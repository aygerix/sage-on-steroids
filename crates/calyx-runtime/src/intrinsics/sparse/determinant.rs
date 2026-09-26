//! Determinants of sparse matrices (text/298).

use super::sparse_arg;
use calyx_flint::gr::Elem;
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::one;
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn determinant(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    if !matches!(a.param("MonteCarloSteps"), Some(Value::Int(_))) {
        return Err(RuntimeError::runtime("Bad type for parameter 'MonteCarloSteps'"));
    }
    let x = sparse_arg(a, 0)?;
    if x.nrows != x.ncols {
        return Err(RuntimeError::runtime("Argument 1 is not square"));
    }
    // The reduction leaves out the zero rows and columns of what remains, so the determinant is
    // zero unless the remainder is all of the unpivoted part.
    let n = x.nrows;
    if let Some(r) = super::structured::integer_reduce(&x) {
        let mut d = if r.remainder.nrows() != n - r.pivots || r.remainder.ncols() != n - r.pivots {
            calyx_flint::Integer::zero()
        } else {
            let tail = r.remainder.det().map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?.to_integer().map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?;
            &r.factor * &tail
        };
        if r.negative { d.neg_assign(); }
        return one(Value::Int(d));
    }
    if let Some(r) = super::structured::word_reduce(&x) {
        let d = if r.remainder.nrows() != n - r.pivots || r.remainder.ncols() != n - r.pivots {
            Elem::zero(&x.info().ctx)
        } else {
            let tail = r.remainder.det().map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?;
            let mut d = Elem::from_word(&x.info().ctx, r.factor).mul(&tail).map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?;
            if r.negative { d = d.neg().map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?; }
            d
        };
        return one(it.elem_to_value(x.ring(), d));
    }
    let d = x.dense().det().map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?;
    one(it.elem_to_value(x.ring(), d))
}

pub(super) fn register(it: &mut Interp) {
    let params = [("MonteCarloSteps", Value::int(0))];
    it.def_params("Determinant", "A::MtrxSprs -> RngElt", &params, "The determinant of A.", determinant);
}
