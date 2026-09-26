//! Associative algebras given by structure constants (`AlgAss`), as far as
//! `Algebra(Q, Q)` (#53) needs them: printing, the basis elements, `A ! x`,
//! the ring operations, and coercion from and to the base field.
//!
//! An algebra of dimension n over a field K has the basis e_1, ..., e_n,
//! and its elements are rows of n coordinates. Row j of the i-th matrix of
//! structure constants holds the coordinates of e_i e_j, so that x y is the
//! row x times the matrix whose rows are y times each of those matrices.

use std::rc::Rc;

use calyx_flint::gr::{Ctx, Truth};
use calyx_flint::mat::Mat;
use calyx_flint::Integer;
use calyx_syntax::ast::BinOp;

use super::matrices::{entry_ctx, entry_of, set_entry};
use super::{boolv, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::print::Printer;
use crate::value::*;

pub struct AlgAss {
    /// The base field.
    pub ring: Value,
    ctx: Rc<Ctx>,
    /// Row j of `mult[i]` holds the coordinates of e_i e_j.
    mult: Vec<Mat>,
    /// The coordinates of the identity.
    one: Mat,
}

/// An element of an associative algebra: its coordinates, as a row.
pub struct AlgAssElt {
    pub parent: Rc<Struct>,
    pub v: Mat,
}

impl AlgAss {
    pub fn dim(&self) -> usize {
        self.one.ncols()
    }

    /// The matrix of y acting on the right: row i holds e_i y.
    fn right(&self, y: &Mat) -> RResult<Mat> {
        let mut r = Mat::zero(&self.ctx, 0, self.dim());
        for m in &self.mult {
            r = r.concat_vertical(&y.mul(m)?);
        }
        Ok(r)
    }

    fn mul(&self, x: &Mat, y: &Mat) -> RResult<Mat> {
        Ok(x.mul(&self.right(y)?)?)
    }

    /// The inverse of y, or None if y is not a unit: the z with z y = 1.
    fn inverse(&self, y: &Mat) -> RResult<Option<Mat>> {
        Ok(self.right(y)?.transpose().nonsingular_solve(&self.one.transpose())?.map(|z| z.transpose()))
    }

    fn pow(&self, x: &Mat, n: &Integer) -> RResult<Mat> {
        let (mut r, mut b) = (self.one.clone(), x.clone());
        let mut k = n.abs();
        while !k.is_zero() {
            if k.is_odd() {
                r = self.mul(&r, &b)?;
            }
            b = self.mul(&b, &b)?;
            k = k.fdiv_2exp(1);
        }
        Ok(r)
    }

    /// The coordinates of e_i e_j, as a row.
    fn product(&self, i: usize, j: usize) -> Mat {
        self.mult[i].block(j, 0, 1, self.dim())
    }

    fn basis(&self, i: usize) -> Mat {
        let mut v = Mat::zero(&self.ctx, 1, self.dim());
        v.set_si(0, i, 1).expect("1 in the base field");
        v
    }

    /// The c with x = c 1, if x is a multiple of the identity.
    fn scalar(&self, x: &Mat) -> RResult<Option<calyx_flint::gr::Elem>> {
        let Some(j) = (0..self.dim()).find(|&j| !self.one.entry_is_zero(0, j)) else { return Ok(None) };
        let c = x.entry(0, j).mul(&self.one.entry(0, j).inv()?)?;
        Ok((self.one.mul_scalar(&c)?.equal(x) == Truth::True).then_some(c))
    }
}

/// A new algebra over `ring`, with the given structure constants and
/// identity.
pub fn new(it: &mut Interp, ring: &Value, mult: Vec<Mat>, one: Mat) -> RResult<Rc<Struct>> {
    let ctx = entry_ctx(it, ring)?;
    Ok(Struct::new(StructKind::AlgAss(Rc::new(AlgAss { ring: ring.clone(), ctx, mult, one }))))
}

fn alg(st: &Struct) -> &Rc<AlgAss> {
    match &st.kind {
        StructKind::AlgAss(a) => a,
        _ => unreachable!("an associative algebra"),
    }
}

fn elt(st: &Rc<Struct>, v: Mat) -> Value {
    Value::Alg(Rc::new(AlgAssElt { parent: st.clone(), v }))
}

/// The element type of an algebra's elements, as Magma names it in errors.
pub fn elt_type(st: &Struct) -> crate::types::TypeVal {
    use crate::types::{TypeArg, TypeVal, t};
    TypeVal::Ext(t::ALG_ASS_ELT, Rc::from(vec![TypeArg::Type(TypeVal::Cat(alg(st).ring.type_id()))]))
}

/// Whether x and y are different algebras, which Magma does not compare.
pub fn distinct(x: &Struct, y: &Struct) -> bool {
    matches!((&x.kind, &y.kind), (StructKind::AlgAss(a), StructKind::AlgAss(b)) if !Rc::ptr_eq(a, b))
}

pub fn same(x: &AlgAssElt, y: &AlgAssElt) -> bool {
    Rc::ptr_eq(&x.parent, &y.parent) && x.v.equal(&y.v) == Truth::True
}

/// A hash of the coordinates over Q; elements over other fields hash by
/// their algebra alone.
pub fn hash_key(x: &AlgAssElt) -> (usize, Vec<Option<calyx_flint::Rational>>) {
    let coords = (0..x.v.ncols()).map(|j| x.v.entry(0, j).to_rational().ok()).collect();
    (Rc::as_ptr(&x.parent) as usize, coords)
}

pub fn negate(x: &AlgAssElt) -> RResult<Value> {
    Ok(elt(&x.parent, x.v.neg()?))
}

// ----- printing ---------------------------------------------------------------------------------

pub fn fmt_algebra(it: &mut Interp, p: &mut Printer, st: &Struct, indent: usize) -> RResult<()> {
    let a = alg(st);
    p.write(&format!("Associative Algebra of dimension {} with base ring ", a.dim()));
    it.fmt(p, &a.ring.clone(), indent)
}

/// An element prints as its coordinates in parentheses.
pub fn fmt_elt(it: &mut Interp, p: &mut Printer, x: &AlgAssElt, indent: usize) -> RResult<()> {
    let ring = alg(&x.parent).ring.clone();
    p.write("(");
    for j in 0..x.v.ncols() {
        if j > 0 {
            p.write(" ");
        }
        let c = entry_of(it, &ring, &x.v, 0, j);
        it.fmt(p, &c, indent)?;
    }
    p.write(")");
    Ok(())
}

// ----- coercion ---------------------------------------------------------------------------------

/// `A ! x`: an element of A, a sequence of coordinates, or an element of
/// the base field (a multiple of the identity). Only `!` (`strict`)
/// reports sequences of the wrong length.
pub fn coerce(it: &mut Interp, st: &Rc<Struct>, x: &Value, strict: bool) -> RResult<Result<Value, Option<String>>> {
    let a = alg(st).clone();
    match x {
        Value::Alg(e) if Rc::ptr_eq(&e.parent, st) => Ok(Ok(x.clone())),
        Value::Alg(_) => Ok(Err(None)),
        Value::Seq(s) => {
            if s.elems.len() != a.dim() {
                let msg = format!("Sequence argument length ({}) should be {} to be coerced into a matrix or vector", s.elems.len(), a.dim());
                return if strict { Err(RuntimeError::runtime(msg).in_context("!")) } else { Ok(Err(None)) };
            }
            let mut v = Mat::zero(&a.ctx, 1, a.dim());
            for (j, c) in s.elems.iter().enumerate() {
                if !set_entry(it, &a.ring, &mut v, 0, j, c)? {
                    return Ok(Err(None));
                }
            }
            Ok(Ok(elt(st, v)))
        }
        _ => {
            let mut c = Mat::zero(&a.ctx, 1, 1);
            if matches!(x, Value::Mat(_)) || !set_entry(it, &a.ring, &mut c, 0, 0, x)? {
                return Ok(Err(None));
            }
            Ok(Ok(elt(st, a.one.mul_scalar(&c.entry(0, 0))?)))
        }
    }
}

/// `S ! x` for an element x of an algebra and a structure S other than
/// its algebra: a multiple c of the identity goes where c does.
pub fn coerce_out(it: &mut Interp, s: &Value, x: &AlgAssElt) -> RResult<Result<Value, Option<String>>> {
    let a = alg(&x.parent).clone();
    match a.scalar(&x.v)? {
        Some(c) => {
            let c = it.elem_to_value(&a.ring, c);
            it.try_coerce(s, &c)
        }
        None => Ok(Err(None)),
    }
}

// ----- operators --------------------------------------------------------------------------------

fn not_compatible(it: &Interp, op: BinOp, a: &Value, b: &Value) -> RuntimeError {
    let msg = format!("Arguments are not compatible\nArgument types given: {}, {}", it.type_name_ext(a), it.type_name_ext(b));
    RuntimeError::runtime(msg).in_context(op.intrinsic_name())
}

/// Operators with an element of an algebra among the operands. The other
/// operand coerces into the algebra, except for integer exponents.
pub fn binop(it: &mut Interp, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
    use BinOp::*;
    if !matches!(op, Add | Sub | Mul | Div | Pow | Eq | Ne) {
        return Ok(None);
    }
    if let (Value::Alg(x), Value::Int(n)) = (a, b) && op == Pow {
        let alg = alg(&x.parent).clone();
        let base = if n.sign() < 0 {
            match alg.inverse(&x.v)? {
                Some(z) => z,
                None if x.v.is_zero() == Truth::True => return Err(RuntimeError::runtime("Illegal negative power of zero element").in_context("^")),
                None => return Err(RuntimeError::runtime("Element is not invertible").in_context("^")),
            }
        } else {
            x.v.clone()
        };
        return Ok(Some(elt(&x.parent, alg.pow(&base, n)?)));
    }
    if matches!(op, Eq | Ne) {
        let e = compare_eq(it, a, b, true)?.unwrap_or(false);
        return Ok(Some(Value::Bool(e == (op == Eq))));
    }
    if let (Value::Alg(x), Value::Alg(y)) = (a, b) && !Rc::ptr_eq(&x.parent, &y.parent) {
        if op == Mul {
            return Err(RuntimeError::runtime("Arguments have no covering structure").in_context("*"));
        }
        return Err(not_compatible(it, op, a, b));
    }
    let Some((st, x, y)) = operands(it, a, b)? else { return Err(it.bad_types(op, a, b)) };
    let alg = alg(&st).clone();
    let r = match op {
        Add => x.add(&y)?,
        Sub => x.sub(&y)?,
        Mul => alg.mul(&x, &y)?,
        Div => match alg.inverse(&y)? {
            Some(z) => alg.mul(&x, &z)?,
            None => return Err(RuntimeError::runtime("Argument 2 is not a unit").in_context("/")),
        },
        _ => return Err(it.bad_types(op, a, b)),
    };
    Ok(Some(elt(&st, r)))
}

/// The algebra of a and b, one of them an element of it, and the
/// coordinates of both, if the other coerces into it.
fn operands(it: &mut Interp, a: &Value, b: &Value) -> RResult<Option<(Rc<Struct>, Mat, Mat)>> {
    let st = match (a, b) {
        (Value::Alg(x), _) | (_, Value::Alg(x)) => x.parent.clone(),
        _ => unreachable!("an element of an algebra"),
    };
    let mut coords = Vec::with_capacity(2);
    for v in [a, b] {
        match coerce(it, &st, v, false)? {
            Ok(Value::Alg(e)) => coords.push(e.v.clone()),
            _ => return Ok(None),
        }
    }
    let y = coords.pop().expect("two operands");
    let x = coords.pop().expect("two operands");
    Ok(Some((st, x, y)))
}

/// `a eq b` (or `cmpeq`, not `strict`) with an element of an algebra:
/// the other value must coerce into its algebra.
pub fn compare_eq(it: &mut Interp, a: &Value, b: &Value, strict: bool) -> RResult<Option<bool>> {
    match operands(it, a, b)? {
        Some((_, x, y)) => Ok(Some(x.equal(&y) == Truth::True)),
        None if strict => Err(not_compatible(it, BinOp::Eq, a, b)),
        None => Ok(Some(false)),
    }
}

// ----- intrinsics -------------------------------------------------------------------------------

fn alg_arg(a: &CallArgs) -> Rc<Struct> {
    match &a.args[0] {
        Value::Struct(st) => st.clone(),
        _ => unreachable!("an associative algebra"),
    }
}

/// `A.i`, the i-th basis element.
fn generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = alg_arg(a);
    let n = alg(&st).dim();
    let i = a.int(1)?;
    match i.to_u64().filter(|&i| i >= 1 && i as usize <= n) {
        Some(i) => one(elt(&st, alg(&st).basis(i as usize - 1))),
        None => Err(RuntimeError::runtime(format!("Argument 2 ({i}) should be in the range [1 .. {n}]"))),
    }
}

fn one_of(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = alg_arg(a);
    one(elt(&st, alg(&st).one.clone()))
}

fn zero_of(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = alg_arg(a);
    let v = Mat::zero(&alg(&st).ctx, 1, alg(&st).dim());
    one(elt(&st, v))
}

fn basis(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = alg_arg(a);
    let elems = (0..alg(&st).dim()).map(|i| elt(&st, alg(&st).basis(i))).collect();
    one(Value::seq(Some(Value::Struct(st)), elems))
}

fn dimension(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(alg(&alg_arg(a)).dim() as u64))
}

fn base_ring(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(alg(&alg_arg(a)).ring.clone())
}

fn is_commutative(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = alg_arg(a);
    let alg = alg(&st);
    let n = alg.dim();
    boolv((0..n).all(|i| (i + 1..n).all(|j| alg.product(i, j).equal(&alg.product(j, i)) == Truth::True)))
}

/// Whether (e_i e_j) e_k = e_i (e_j e_k) for all i, j and k.
fn is_associative(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = alg_arg(a);
    let alg = alg(&st);
    let n = alg.dim();
    for i in 0..n {
        for j in 0..n {
            let ij = alg.product(i, j);
            for k in 0..n {
                if alg.mul(&ij, &alg.basis(k))?.equal(&alg.mul(&alg.basis(i), &alg.product(j, k))?) != Truth::True {
                    return boolv(false);
                }
            }
        }
    }
    boolv(true)
}

pub fn register(it: &mut Interp) {
    it.def(".", "A::AlgAss, i::RngIntElt -> AlgAssElt", "The i-th basis element of A.", generator);
    it.def("One", "A::AlgAss -> AlgAssElt", "The identity of A.", one_of);
    it.def("Zero", "A::AlgAss -> AlgAssElt", "The zero element of A.", zero_of);
    it.def("Basis", "A::AlgAss -> SeqEnum", "The basis of A.", basis);
    it.def("Dimension", "A::AlgAss -> RngIntElt", "The dimension of A over its base field.", dimension);
    for name in ["BaseRing", "BaseField"] {
        it.def(name, "A::AlgAss -> Rng", "The base field of A.", base_ring);
    }
    it.def("IsCommutative", "A::AlgAss -> BoolElt", "Whether A is commutative.", is_commutative);
    it.def("IsAssociative", "A::AlgAss -> BoolElt", "Whether A is associative.", is_associative);
}
