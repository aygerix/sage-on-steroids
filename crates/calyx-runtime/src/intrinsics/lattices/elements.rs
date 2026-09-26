//! Lattice elements (text/332): creating them, their operations, and
//! access to their entries and coordinates.

use std::rc::Rc;

use calyx_flint::gr::{Ctx, Elem, Truth};
use calyx_flint::mat::Mat;
use calyx_flint::{Integer, Rational, Real};

use super::{coordinate_lattice, elt, lat, row, row_of, to_q, value_of};
use crate::error::{RResult, RuntimeError};
use crate::ext::ExtElt;
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::matrices::Mtrx;
use crate::intrinsics::{boolv, intv, one};
use crate::value::*;

/// `v div d`: v/d, when it is in the lattice of v.
pub(super) fn exact_div(_it: &mut Interp, x: &ExtElt, d: &Integer) -> RResult<Value> {
    let l = lat(&x.parent);
    if d.is_zero() {
        return Err(RuntimeError::runtime("Division by zero").in_context("div"));
    }
    let entries = row(row_of(x));
    let dq = Rational::from_integer(d);
    if l.ring.is_integers()
        && let Some(j) = entries.iter().position(|c| !c.numerator().is_divisible_by(d))
    {
        return Err(RuntimeError::runtime(format!("Entry {} of argument 1 is not divisible by argument 2", j + 1)).in_context("div"));
    }
    let inv = Elem::from_rational(&Ctx::rationals(), &dq.inv().expect("a nonzero divisor"))?;
    let v = to_q(row_of(x)).mul_scalar(&inv)?;
    if !l.contains(&v) {
        return Err(RuntimeError::runtime("Result is not in the lattice").in_context("div"));
    }
    Ok(elt(&x.parent, v.change_ring(l.ctx())?))
}

/// `v * T` for a square matrix T over the base ring, when the product is
/// in the lattice of v.
pub(super) fn transform(it: &mut Interp, x: &ExtElt, t: &Mtrx, a: &Value, b: &Value) -> RResult<Value> {
    let l = lat(&x.parent);
    let ring = t.ring();
    if !(ring.is_integers() || ring.is_rationals()) || t.m.nrows() != l.degree() || t.m.ncols() != l.degree() {
        return Err(it.bad_types(calyx_syntax::ast::BinOp::Mul, a, b));
    }
    if *ring != l.ring {
        return Err(RuntimeError::runtime("Arguments have incompatible coefficient rings").in_context("*"));
    }
    let v = to_q(row_of(x)).mul(&to_q(&t.m))?;
    if !l.contains(&v) {
        return Err(RuntimeError::runtime("Result is not in the lattice").in_context("*"));
    }
    Ok(elt(&x.parent, v.change_ring(l.ctx())?))
}

fn lattice_arg(a: &CallArgs, i: usize) -> Rc<Struct> {
    match &a.args[i] {
        Value::Struct(st) => st.clone(),
        _ => unreachable!("a lattice"),
    }
}

fn elt_arg(a: &CallArgs, i: usize) -> Rc<ExtElt> {
    match &a.args[i] {
        Value::Ext(x) => x.clone(),
        _ => unreachable!("a lattice element"),
    }
}

/// `L.i`, the i-th basis vector.
fn generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = lattice_arg(a, 0);
    let l = lat(&st);
    let (m, i) = (l.rank(), a.int(1)?);
    match i.to_u64().filter(|&i| i >= 1 && i as usize <= m) {
        Some(i) => one(elt(&st, l.basis.block(i as usize - 1, 0, 1, l.degree()))),
        None => Err(RuntimeError::runtime(format!("Argument 2 ({i}) should be in the range [1 .. {m}]"))),
    }
}

/// `Coordelt(L, C)`: the combination of the basis with the coefficients
/// in C, a sequence or a vector of integers.
fn coordelt(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = lattice_arg(a, 0);
    let l = lat(&st);
    let coeffs: Vec<Value> = match &a.args[1] {
        Value::Seq(s) => s.elems.clone(),
        Value::Mat(m) if m.m.nrows() == 1 => (0..m.m.ncols()).map(|j| crate::intrinsics::matrices::entry_value(it, m, 0, j)).collect(),
        _ => return Err(RuntimeError::runtime("Bad argument types")),
    };
    if coeffs.len() != l.rank() {
        return Err(RuntimeError::runtime(format!("Argument 2 must have length {}", l.rank())));
    }
    let mut c = Vec::with_capacity(coeffs.len());
    for x in &coeffs {
        match x {
            Value::Int(n) => c.push(n.clone()),
            _ => return Err(RuntimeError::runtime("Argument 2 must consist of integers")),
        }
    }
    one(elt(&st, l.element(&c)))
}

fn zero(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = lattice_arg(a, 0);
    let l = lat(&st);
    one(elt(&st, Mat::zero(l.ctx(), 1, l.degree())))
}

fn inner_product(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y) = (elt_arg(a, 0), elt_arg(a, 1));
    if !Rc::ptr_eq(&x.parent, &y.parent) && !lat(&x.parent).compatible(lat(&y.parent)) {
        let (ta, tb) = (it.type_name_ext(&a.args[0]), it.type_name_ext(&a.args[1]));
        return Err(RuntimeError::runtime(format!("Arguments are not compatible\nArgument types given: {ta}, {tb}")));
    }
    let l = lat(&x.parent);
    one(value_of(&l.ring, &l.inner(row_of(&x), row_of(&y))))
}

fn norm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = elt_arg(a, 0);
    let l = lat(&x.parent);
    one(value_of(&l.ring, &l.inner(row_of(&x), row_of(&x))))
}

/// `Length(v)` and `Length(v, K)`: the square root of the norm, in the
/// default real field or in K.
fn length(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = elt_arg(a, 0);
    let l = lat(&x.parent);
    let bits = match a.args.get(1) {
        Some(k) => crate::intrinsics::reals::bits_of(k).expect("a real field"),
        None => crate::intrinsics::reals::default_bits(),
    };
    let n = l.inner(row_of(&x), row_of(&x)).to_rational()?;
    one(Value::real(Real::from_rational(&n, bits).sqrt()))
}

/// The columns (from 1) where v has nonzero entries.
fn support(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = elt_arg(a, 0);
    let cols = (0..row_of(&x).ncols()).filter(|&j| !row_of(&x).entry_is_zero(0, j)).map(|j| Value::int(j as i64 + 1));
    one(Value::Set(Rc::new(SetEnum::new(Some(Value::integers()), cols.collect()))))
}

fn is_zero(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(row_of(&elt_arg(a, 0)).is_zero() == Truth::True)
}

fn eltseq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = elt_arg(a, 0);
    let ring = lat(&x.parent).ring.clone();
    let elems = (0..row_of(&x).ncols()).map(|j| value_of(&ring, &row_of(&x).entry(0, j))).collect();
    one(Value::seq(Some(ring), elems))
}

/// The coordinates of the element argument `i` in the lattice `st`.
fn coords_in(st: &Rc<Struct>, a: &CallArgs, i: usize) -> RResult<Vec<Integer>> {
    let (x, l) = (elt_arg(a, i), lat(st));
    let c = if row_of(&x).ncols() == l.degree() { l.coordinates(row_of(&x)) } else { None };
    c.ok_or_else(|| RuntimeError::runtime(format!("Argument {} is not in argument 1", i + 1)))
}

/// `Coordinates(v)` and `Coordinates(L, v)`.
fn coordinates(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, i) = if a.args.len() == 1 { (elt_arg(a, 0).parent.clone(), 0) } else { (lattice_arg(a, 0), 1) };
    one(Value::int_seq(coords_in(&st, a, i)?))
}

/// `CoordinateVector(v)` and `CoordinateVector(L, v)`: the coordinates
/// as an element of the coordinate lattice.
fn coordinate_vector(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, i) = if a.args.len() == 1 { (elt_arg(a, 0).parent.clone(), 0) } else { (lattice_arg(a, 0), 1) };
    let c = coords_in(&st, a, i)?;
    let cst = coordinate_lattice(&st);
    let v = lat(&cst).element(&c);
    one(elt(&cst, v))
}

fn degree(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(row_of(&elt_arg(a, 0)).ncols() as u64))
}

pub fn register(it: &mut Interp) {
    it.def(".", "L::Lat, i::RngIntElt -> LatElt", "The i-th basis vector of L.", generator);
    for name in ["CoordinatesToElement", "Coordelt"] {
        let doc = "The combination of the basis vectors of L with the integer coefficients C.";
        it.def(name, "L::Lat, C::[RngIntElt] -> LatElt", doc, coordelt);
        it.def(name, "L::Lat, C::Mtrx -> LatElt", doc, coordelt);
    }
    it.def("Zero", "L::Lat -> LatElt", "The zero element of L.", zero);
    it.def("InnerProduct", "v::LatElt, w::LatElt -> RngElt", "The inner product of v and w.", inner_product);
    it.def("Norm", "v::LatElt -> RngElt", "The norm (v, v) of v.", norm);
    it.def("Length", "v::LatElt -> FldReElt", "The square root of the norm of v, in the default real field.", length);
    it.def("Length", "v::LatElt, K::FldRe -> FldReElt", "The square root of the norm of v, in K.", length);
    it.def("Support", "v::LatElt -> SetEnum", "The columns where v has nonzero entries.", support);
    it.def("IsZero", "v::LatElt -> BoolElt", "Whether v is zero.", is_zero);
    for name in ["ElementToSequence", "Eltseq"] {
        it.def(name, "v::LatElt -> SeqEnum", "The entries of v.", eltseq);
    }
    it.def("Coordinates", "v::LatElt -> [RngIntElt]", "The coordinates of v in the basis of its lattice.", coordinates);
    it.def("Coordinates", "L::Lat, v::LatElt -> [RngIntElt]", "The coordinates of v in the basis of L.", coordinates);
    let doc = "The coordinates of v in the basis of its lattice, as an element of the coordinate lattice.";
    it.def("CoordinateVector", "v::LatElt -> LatElt", doc, coordinate_vector);
    let doc = "The coordinates of v in the basis of L, as an element of the coordinate lattice of L.";
    it.def("CoordinateVector", "L::Lat, v::LatElt -> LatElt", doc, coordinate_vector);
    it.def("Degree", "v::LatElt -> RngIntElt", "The degree of the lattice of v.", degree);
}
