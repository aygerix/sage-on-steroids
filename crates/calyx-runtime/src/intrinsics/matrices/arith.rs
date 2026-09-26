//! Arithmetic of matrices and vectors: sums, products, scalar multiples,
//! powers, comparison and `AddScaledMatrix`.
//!
//! Matrices over different rings meet in a common ring (a matrix over Z
//! plus one over Q is over Q), as do a matrix and a scalar. Vectors are
//! stricter: two vectors must lie in the same R-space.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Elem, GrError, Truth};
use calyx_flint::mat::Mat;
use calyx_syntax::ast::BinOp;

use super::spaces::generic;
use super::{Mtrx, Shape, entry_ctx, entry_value, like, mat_arg, mat_value, over_ring_of, scalar, set_entry, vec_value};
use crate::error::{ErrStyle, ErrorInfo, RResult, RuntimeError};
use crate::intrinsics::{none, one};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn types_error(it: &Interp, msg: &str, a: &Value, b: &Value) -> RuntimeError {
    RuntimeError::runtime(format!("{msg}\nArgument types given: {}, {}", it.type_name_ext(a), it.type_name_ext(b)))
}

fn degrees() -> RuntimeError {
    RuntimeError::runtime("Arguments have incompatible degrees")
}

/// The entries of `a` over the ring `ring` (with its context), or None if
/// they do not coerce.
fn entries_over(it: &mut Interp, a: &Mtrx, ring: &Value) -> RResult<Option<Mat>> {
    if a.ring() == ring {
        return Ok(Some(a.m.clone()));
    }
    let ctx = entry_ctx(it, ring)?;
    let (r, c) = (a.m.nrows(), a.m.ncols());
    let mut m = Mat::zero(&ctx, r, c);
    for i in 0..r {
        for j in 0..c {
            let x = entry_value(it, a, i, j);
            if !set_entry(it, ring, &mut m, i, j, &x)? {
                return Ok(None);
            }
        }
    }
    Ok(Some(m))
}

/// The common ring of two rings, if elements of both coerce into it.
fn meet(it: &mut Interp, r: &Value, s: &Value) -> RResult<Option<Value>> {
    if r == s {
        return Ok(Some(r.clone()));
    }
    it.common_ring(r, s)
}

/// Two matrices over a common ring, with that ring; None if there is none.
pub(super) fn over_common(it: &mut Interp, a: &Mtrx, b: &Mtrx) -> RResult<Option<(Value, Mat, Mat)>> {
    let Some(ring) = meet(it, a.ring(), b.ring())? else { return Ok(None) };
    let (Some(x), Some(y)) = (entries_over(it, a, &ring)?, entries_over(it, b, &ring)?) else { return Ok(None) };
    Ok(Some((ring, x, y)))
}

/// A matrix over `ring` like `a` in shape (a vector if `a` is one).
fn shaped(it: &mut Interp, a: &Mtrx, ring: &Value, m: Mat) -> RResult<Value> {
    if a.ring() == ring && a.m.nrows() == m.nrows() && a.m.ncols() == m.ncols() {
        return Ok(like(a, m));
    }
    if a.is_vector() && m.nrows() == 1 { vec_value(it, ring, m) } else { mat_value(it, ring, m) }
}

fn gr(e: GrError, what: &str) -> RuntimeError {
    crate::rings::gr_error(e, what)
}

/// `A eq B`: None when the values cannot be compared this way.
pub fn equal(it: &mut Interp, a: &Value, b: &Value) -> RResult<bool> {
    match (a, b) {
        (Value::Mat(x), Value::Mat(y)) => {
            if Rc::ptr_eq(&x.parent, &y.parent) {
                return Ok(x.m.equal(&y.m) == Truth::True);
            }
            if x.m.nrows() != y.m.nrows() || x.m.ncols() != y.m.ncols() || x.is_vector() != y.is_vector() {
                return Err(degrees());
            }
            if x.is_vector() && x.ring() != y.ring() {
                return Err(types_error(it, "Bad argument types", a, b));
            }
            match over_common(it, x, y)? {
                Some((_, p, q)) => Ok(p.equal(&q) == Truth::True),
                None => Err(types_error(it, "Bad argument types", a, b)),
            }
        }
        // A matrix of an algebra and a scalar: the scalar matrix.
        (Value::Mat(x), s) | (s, Value::Mat(x)) if x.info().shape == Shape::Algebra => {
            let ring = x.ring().clone();
            match scalar(it, &ring, x.m.ctx(), s)? {
                Some(e) => Ok(x.m.equal(&Mat::scalar(x.m.nrows(), &e)?) == Truth::True),
                None => Err(types_error(it, "Bad argument types", a, b)),
            }
        }
        _ => Err(types_error(it, "Bad argument types", a, b)),
    }
}

/// `-A`.
pub fn negate(a: &Mtrx) -> RResult<Value> {
    Ok(like(a, a.m.neg().map_err(|e| gr(e, "Negation failed"))?))
}

/// A scalar and a matrix over their common ring.
fn scalar_and(it: &mut Interp, a: &Mtrx, s: &Value) -> RResult<Option<(Value, Mat, Elem)>> {
    let sring = it.parent_of(s)?;
    let Some(ring) = meet(it, a.ring(), &sring)? else { return Ok(None) };
    let Some(m) = entries_over(it, a, &ring)? else { return Ok(None) };
    let ctx = m.ctx().clone();
    Ok(scalar(it, &ring, &ctx, s)?.map(|e| (ring, m, e)))
}

/// `a op b` where at least one of a and b is a matrix; None if the
/// operation does not apply.
pub fn binop(it: &mut Interp, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
    use BinOp::*;
    match (op, a, b) {
        (Eq | Ne, _, _) => {
            let e = equal(it, a, b)?;
            Ok(Some(Value::Bool(e == (op == Eq))))
        }
        (Add | Sub, Value::Mat(x), Value::Mat(y)) => {
            let same_shape = x.m.nrows() == y.m.nrows() && x.m.ncols() == y.m.ncols() && x.is_vector() == y.is_vector();
            if !same_shape || (x.is_vector() && x.ring() != y.ring()) {
                return Err(types_error(it, "Bad argument types", a, b));
            }
            let Some((ring, p, q)) = over_common(it, x, y)? else { return Err(types_error(it, "Bad argument types", a, b)) };
            let m = if op == Add { p.add(&q) } else { p.sub(&q) }.map_err(|e| gr(e, "Arithmetic failed"))?;
            if x.is_vector() && !Rc::ptr_eq(&x.parent, &y.parent) && !x.info().same_as(y.info()) {
                // Vectors of different subspaces add in the full space.
                return Ok(Some(Value::Mat(Rc::new(Mtrx { parent: generic(&x.parent), m }))));
            }
            Ok(Some(shaped(it, x, &ring, m)?))
        }
        // A + s and s + A add the scalar matrix s in a matrix algebra.
        (Add | Sub, Value::Mat(x), s) | (Add | Sub, s, Value::Mat(x)) if x.info().shape == Shape::Algebra => {
            let Some((ring, m, e)) = scalar_and(it, x, s)? else { return Err(types_error(it, "Bad argument types", a, b)) };
            let sm = Mat::scalar(m.nrows(), &e)?;
            let r = match (op, matches!(a, Value::Mat(_))) {
                (Add, _) => m.add(&sm),
                (_, true) => m.sub(&sm),
                _ => sm.sub(&m),
            };
            Ok(Some(shaped(it, x, &ring, r.map_err(|e| gr(e, "Arithmetic failed"))?)?))
        }
        (Mul, Value::Mat(x), Value::Mat(y)) => {
            if y.is_vector() {
                return Err(types_error(it, "Arguments are not compatible", a, b));
            }
            if x.m.ncols() != y.m.nrows() {
                return Err(degrees());
            }
            if x.is_vector() && x.ring() != y.ring() {
                return Err(types_error(it, "Bad argument types", a, b));
            }
            let Some((ring, p, q)) = over_common(it, x, y)? else { return Err(types_error(it, "Bad argument types", a, b)) };
            let m = p.mul(&q).map_err(|e| gr(e, "Multiplication failed"))?;
            if x.is_vector() {
                // Of the same degree, the product stays in the full space of
                // the vector (and keeps its inner product).
                if ring == *x.ring() && m.ncols() == x.m.ncols() {
                    return Ok(Some(Value::Mat(Rc::new(Mtrx { parent: generic(&x.parent), m }))));
                }
                return Ok(Some(vec_value(it, &ring, m)?));
            }
            if ring == *x.ring() && m.nrows() == x.m.nrows() && m.ncols() == x.m.ncols() {
                return Ok(Some(like(x, m)));
            }
            Ok(Some(mat_value(it, &ring, m)?))
        }
        (Mul, Value::Mat(x), s) | (Mul, s, Value::Mat(x)) => {
            let Some((ring, m, e)) = scalar_and(it, x, s)? else { return Err(types_error(it, "Bad argument types", a, b)) };
            let r = if matches!(a, Value::Mat(_)) { m.mul_scalar(&e) } else { m.scalar_mul(&e) };
            Ok(Some(shaped(it, x, &ring, r.map_err(|e| gr(e, "Multiplication failed"))?)?))
        }
        (Div, Value::Mat(x), s) if !matches!(s, Value::Mat(_)) => {
            let Some((ring, m, e)) = scalar_and(it, x, s)? else { return Err(types_error(it, "Bad argument types", a, b)) };
            if x.is_vector() && !x.info().field {
                return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a field"));
            }
            let inv = e.inv().map_err(|_| RuntimeError::runtime("Argument 2 is not a unit"))?;
            let r = m.mul_scalar(&inv).map_err(|e| gr(e, "Division failed"))?;
            Ok(Some(shaped(it, x, &ring, r)?))
        }
        (Pow, Value::Mat(x), Value::Int(n)) => Ok(Some(power(it, x, n)?)),
        _ => Ok(None),
    }
}

/// `A^n`, with the inverse for n < 0.
pub fn power(it: &mut Interp, a: &Mtrx, n: &Integer) -> RResult<Value> {
    if a.m.nrows() != a.m.ncols() || a.is_vector() {
        return Err(RuntimeError::runtime("Argument 1 is not square"));
    }
    if n.sign() < 0 {
        let inv = inverse(a).ok_or_else(|| RuntimeError::runtime("Argument 1 is not invertible"))?;
        let m = inv.pow(&-n).map_err(|e| gr(e, "Power failed"))?;
        return over_ring_of(it, a, m);
    }
    let m = a.m.pow(n).map_err(|e| gr(e, "Power failed"))?;
    Ok(like(a, m))
}

/// The inverse of a square matrix over its ring, if it has one.
pub fn inverse(a: &Mtrx) -> Option<Mat> {
    a.m.inv().ok()
}

/// A + s·B for `AddScaledMatrix`, with B of the shape and ring of A and s
/// coerced into the ring: in the parent of A, but a matrix with one row
/// when A is a vector.
fn add_scaled(it: &mut Interp, a: &CallArgs) -> RResult<Value> {
    let (x, y) = (mat_arg(a, 0)?.clone(), mat_arg(a, 2)?.clone());
    if x.m.nrows() != y.m.nrows() {
        return Err(RuntimeError::runtime("Matrices have incompatible numbers of rows"));
    }
    if x.m.ncols() != y.m.ncols() {
        return Err(RuntimeError::runtime("Matrices have incompatible numbers of columns"));
    }
    if x.ring() != y.ring() {
        return Err(RuntimeError::runtime("Arguments have incompatible coefficient rings"));
    }
    let ring = x.ring().clone();
    let Some(s) = scalar(it, &ring, x.m.ctx(), &a.args[1])? else {
        // A failed coercion, reported as Magma's are.
        let msg = match &a.args[1] {
            Value::Rat(_) if ring.is_integers() => "Rational argument is not a whole integer",
            v if it.type_name(v) == "FldFinElt" => "No embedding known into LHS field",
            _ => return Err(RuntimeError::runtime("Bad argument types")),
        };
        return Err(ErrorInfo { style: ErrStyle::Plain, ..ErrorInfo::runtime(msg) }.into());
    };
    let m = x.m.add(&y.m.scalar_mul(&s).map_err(|e| gr(e, "Arithmetic failed"))?).map_err(|e| gr(e, "Arithmetic failed"))?;
    if x.is_vector() { mat_value(it, &ring, m) } else { Ok(like(&x, m)) }
}

fn add_scaled_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(add_scaled(it, a)?)
}

fn add_scaled_matrix_proc(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    a.args[0] = add_scaled(it, a)?;
    none()
}

pub fn register(it: &mut Interp) {
    it.def("AddScaledMatrix", "A::Mtrx, s::RngElt, B::Mtrx -> Mtrx", "A + s*B.", add_scaled_matrix);
    it.def("AddScaledMatrix", "~A::Mtrx, s::RngElt, B::Mtrx", "Set A to A + s*B.", add_scaled_matrix_proc);
}
