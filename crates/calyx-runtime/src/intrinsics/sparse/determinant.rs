//! Determinants of sparse matrices (text/298).

use super::sparse_arg;
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
    let d = x.dense().det().map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?;
    one(it.elem_to_value(x.ring(), d))
}

pub(super) fn register(it: &mut Interp) {
    let params = [("MonteCarloSteps", Value::int(0))];
    it.def_params("Determinant", "A::MtrxSprs -> RngElt", &params, "The determinant of A.", determinant);
}
