//! Changing the coefficient ring of matrices and vectors: coercing the
//! entries (`ChangeRing(A, R)`, `Matrix(R, A)`, `CanChangeRing`) or
//! applying a map to them.
//!
//! `ChangeRing` keeps the shape of A (an algebra, a space or an R-space);
//! `Matrix(R, A)` gives a matrix in the algebra or space of its shape.

use std::rc::Rc;

use calyx_flint::gr::CtxKind;
use calyx_flint::mat::Mat;

use super::{Mtrx, entry_ctx, entry_value, mat_arg, mat_value, parent, set_entry};
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::{boolv, one};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn cannot_coerce() -> RuntimeError {
    RuntimeError::runtime("Cannot coerce element from source coefficent ring into the destination coefficient ring")
}

/// The entries of `x` coerced into `ring` (as by `!`), or None when one
/// does not coerce.
pub(super) fn coerced(it: &mut Interp, x: &Mtrx, ring: &Value) -> RResult<Option<Mat>> {
    if x.ring() == ring {
        return Ok(Some(x.m.clone()));
    }
    let ctx = entry_ctx(it, ring)?;
    if matches!(x.m.ctx().kind(), CtxKind::Integers) {
        // Every ring takes integers as FLINT sets them.
        return Ok(x.m.change_ring(&ctx).ok());
    }
    let mut m = Mat::zero(&ctx, x.m.nrows(), x.m.ncols());
    for i in 0..x.m.nrows() {
        for j in 0..x.m.ncols() {
            let e = entry_value(it, x, i, j);
            if !set_entry(it, ring, &mut m, i, j, &e)? {
                return Ok(None);
            }
        }
    }
    Ok(Some(m))
}

/// A matrix of the shape of `x` (an algebra, space or R-space) over `ring`.
fn shaped(it: &mut Interp, x: &Mtrx, ring: &Value, m: Mat) -> RResult<Value> {
    let p = parent(it, ring, m.nrows(), m.ncols(), x.info().shape)?;
    Ok(Value::Mat(Rc::new(Mtrx { parent: p, m })))
}

fn change_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let ring = a.args[1].clone();
    let m = coerced(it, &x, &ring)?.ok_or_else(cannot_coerce)?;
    one(shaped(it, &x, &ring, m)?)
}

/// `Matrix(R, A)`.
fn matrix_over(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 1)?.clone();
    let ring = a.args[0].clone();
    let m = coerced(it, &x, &ring)?.ok_or_else(cannot_coerce)?;
    one(mat_value(it, &ring, m)?)
}

fn can_change_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let ring = a.args[1].clone();
    match coerced(it, &x, &ring)? {
        Some(m) => Ok(vals![Value::Bool(true), shaped(it, &x, &ring, m)?]),
        None => boolv(false),
    }
}

/// `ChangeRing(A, R, f)` and `ChangeRing(A, f)`: f applied to the entries,
/// giving a matrix over R, the codomain of f.
fn change_ring_map(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let Some(Value::Map(f)) = a.args.last().cloned() else { unreachable!() };
    if &f.domain != x.ring() {
        return Err(RuntimeError::runtime("Domain of map does not equal base ring of argument 1"));
    }
    if a.args.len() == 3 && f.codomain != a.args[1] {
        return Err(RuntimeError::runtime("Codomain of map does not equal argument 2"));
    }
    let ring = f.codomain.clone();
    let mut m = Mat::zero(&entry_ctx(it, &ring)?, x.m.nrows(), x.m.ncols());
    for i in 0..x.m.nrows() {
        for j in 0..x.m.ncols() {
            let e = entry_value(it, &x, i, j);
            let y = it.apply_map(&f, &e)?;
            if !set_entry(it, &ring, &mut m, i, j, &y)? {
                return Err(cannot_coerce());
            }
        }
    }
    one(shaped(it, &x, &ring, m)?)
}

pub fn register(it: &mut Interp) {
    it.def("ChangeRing", "A::Mtrx, R::Rng -> Mtrx", "A with its entries coerced into R.", change_ring);
    it.def("Matrix", "R::Rng, A::Mtrx -> Mtrx", "The matrix over R with the entries of A.", matrix_over);
    it.def("ChangeRing", "A::Mtrx, R::Rng, f::Map -> Mtrx", "A over R with f applied to its entries.", change_ring_map);
    it.def("ChangeRing", "A::Mtrx, f::Map -> Mtrx", "A over the codomain of f with f applied to its entries.", change_ring_map);
    it.def("CanChangeRing", "A::Mtrx, R::Rng -> BoolElt, Mtrx", "Whether the entries of A coerce into R, and A over R.", can_change_ring);
}
