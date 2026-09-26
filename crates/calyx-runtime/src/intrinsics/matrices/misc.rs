//! Miscellaneous operations on matrices: the Frobenius image of a matrix
//! over a finite field.

use calyx_flint::Integer;
use calyx_flint::gr::CtxKind;

use super::linalg::{gr, with_types};
use super::{mat_arg, mat_value, vec_value};
use crate::error::RResult;
use crate::intrinsics::one;
use crate::interp::{CallArgs, Interp};
use crate::value::*;

/// `FrobeniusImage(A, e)`: A with each entry x replaced by x^(p^e). The
/// result is a matrix (or vector) over the same field, in the full matrix
/// algebra or space of its shape.
fn frobenius_image(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let degree = match x.m.ctx().kind() {
        CtxKind::FqZech { degree, .. } | CtxKind::FqNmod { degree, .. } | CtxKind::FqPacked { degree, .. } | CtxKind::Fq { degree, .. } => *degree,
        CtxKind::Nmod(_) | CtxKind::FmpzMod(_) if x.info().field => 1,
        _ => return Err(with_types(it, a, "Bad argument types")),
    };
    let k = a.int(1)?.div_rem_euclid(&Integer::from_u64(degree)).expect("a nonzero degree").1.to_u64().expect("a small exponent");
    let mut m = x.m.clone();
    if k > 0 {
        for i in 0..m.nrows() {
            for j in 0..m.ncols() {
                let y = m.entry(i, j).fq_frobenius(k as i64).map_err(gr)?;
                m.set_entry(i, j, &y);
            }
        }
    }
    let ring = x.ring().clone();
    one(if x.is_vector() { vec_value(it, &ring, m)? } else { mat_value(it, &ring, m)? })
}

pub fn register(it: &mut Interp) {
    it.def("FrobeniusImage", "A::Mtrx, e::RngIntElt -> Mtrx", "A with each entry x replaced by x^(p^e), for p the characteristic.", frobenius_image);
}
