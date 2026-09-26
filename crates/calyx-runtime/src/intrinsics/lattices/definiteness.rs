//! Testing matrices for definiteness (text/340), over Z and Q so far.

use calyx_flint::gr::Truth;

use super::positive_definite;
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::boolv;
use crate::value::*;

/// A symmetric matrix over Z or Q, argument 1.
fn symmetric_arg(it: &Interp, a: &CallArgs) -> RResult<calyx_flint::mat::Mat> {
    let Value::Mat(m) = &a.args[0] else { unreachable!("a matrix") };
    if !m.ring().is_integers() && !m.ring().is_rationals() {
        return Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", it.type_name_ext(&a.args[0]))));
    }
    if m.m.nrows() != m.m.ncols() {
        return Err(RuntimeError::runtime("Argument 1 is not square"));
    }
    if m.m.transpose().equal(&m.m) != Truth::True {
        return Err(RuntimeError::runtime("Argument 1 is not symmetric"));
    }
    Ok(m.m.clone())
}

fn is_positive_definite(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(positive_definite(&symmetric_arg(it, a)?))
}

pub fn register(it: &mut Interp) {
    it.def("IsPositiveDefinite", "M::Mtrx -> BoolElt", "Whether the symmetric matrix M is positive definite.", is_positive_definite);
}
