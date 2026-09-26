//! Associative algebras given by structure constants (`AlgAss`), as far as
//! `Algebra(Q, Q)` (#53) needs them: printing, the basis elements, `A ! x`,
//! the ring operations, and coercion from and to the base field.
//!
//! An algebra of dimension n over a field K has the basis e_1, ..., e_n,
//! and its elements are rows of n coordinates. Row j of the i-th matrix of
//! structure constants holds the coordinates of e_i e_j, so that x y is the
//! row x times the matrix whose rows are y times each of those matrices.

use std::hash::{Hash, Hasher};
use std::rc::Rc;

use calyx_flint::gr::{Ctx, Truth};
use calyx_flint::mat::Mat;
use calyx_flint::Integer;
use calyx_syntax::ast::BinOp;

use super::matrices::{entry_ctx, entry_of, set_entry};
use super::{boolv, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::ext::{self, Coerced, ExtElt, ExtKind};
use crate::interp::{CallArgs, Interp};
use crate::print::Printer;
use crate::types::{TypeArg, TypeId, TypeVal, t};
use crate::value::*;

/// An associative algebra; its elements hold their coordinates, as a row.
pub struct AlgAss {
    /// The base field.
    pub ring: Value,
    ctx: Rc<Ctx>,
    /// Row j of `mult[i]` holds the coordinates of e_i e_j.
    mult: Vec<Mat>,
    /// The coordinates of the identity.
    one: Mat,
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
    Ok(ext::structure(AlgAss { ring: ring.clone(), ctx, mult, one }))
}

fn alg(st: &Struct) -> &AlgAss {
    ext::expect_kind(st)
}

fn elt(st: &Rc<Struct>, v: Mat) -> Value {
    ext::element(st, v)
}

fn coords(x: &ExtElt) -> &Mat {
    x.data()
}

/// The element of an algebra that v is, if it is one.
fn as_elt(v: &Value) -> Option<&ExtElt> {
    match v {
        Value::Ext(x) if ext::kind_of::<AlgAss>(&x.parent).is_some() => Some(x),
        _ => None,
    }
}

/// A hash of the coordinates over Q; elements over other fields hash by
/// their algebra alone.
fn hash_key(x: &ExtElt) -> (usize, Vec<Option<calyx_flint::Rational>>) {
    let v = coords(x);
    let coords = (0..v.ncols()).map(|j| v.entry(0, j).to_rational().ok()).collect();
    (Rc::as_ptr(&x.parent) as usize, coords)
}

fn not_compatible(it: &Interp, op: BinOp, a: &Value, b: &Value) -> RuntimeError {
    let msg = format!("Arguments are not compatible\nArgument types given: {}, {}", it.type_name_ext(a), it.type_name_ext(b));
    RuntimeError::runtime(msg).in_context(op.intrinsic_name())
}

/// The algebra of a and b, one of them an element of it, and the
/// coordinates of both, if the other coerces into it.
fn operands(it: &mut Interp, a: &Value, b: &Value) -> RResult<Option<(Rc<Struct>, Mat, Mat)>> {
    let st = as_elt(a).or(as_elt(b)).expect("an element of an algebra").parent.clone();
    let mut v = Vec::with_capacity(2);
    for x in [a, b] {
        match coerce(it, &st, x, false)? {
            Ok(e) => v.push(coords(as_elt(&e).expect("an element of the algebra")).clone()),
            _ => return Ok(None),
        }
    }
    let y = v.pop().expect("two operands");
    let x = v.pop().expect("two operands");
    Ok(Some((st, x, y)))
}

/// `A ! x`: an element of A, a sequence of coordinates, or an element of
/// the base field (a multiple of the identity). Only `!` (`strict`)
/// reports sequences of the wrong length.
fn coerce(it: &mut Interp, st: &Rc<Struct>, x: &Value, strict: bool) -> RResult<Coerced> {
    let a = alg(st);
    if let Some(e) = as_elt(x) {
        return Ok(if Rc::ptr_eq(&e.parent, st) { Ok(x.clone()) } else { Err(None) });
    }
    match x {
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

impl ExtKind for AlgAss {
    fn struct_type(&self) -> TypeId {
        t::ALG_ASS
    }

    fn elt_type(&self) -> TypeId {
        t::ALG_ASS_ELT
    }

    /// Magma names the base field in the element type in errors.
    fn elt_type_ext(&self) -> TypeVal {
        TypeVal::Ext(t::ALG_ASS_ELT, Rc::from(vec![TypeArg::Type(TypeVal::Cat(self.ring.type_id()))]))
    }

    /// Magma does not compare different algebras.
    fn incomparable(&self, other: &dyn ExtKind) -> Option<&'static str> {
        (other as &dyn std::any::Any).is::<AlgAss>().then_some("Arguments have no covering structure")
    }

    fn fmt_struct(&self, it: &mut Interp, p: &mut Printer, _st: &Struct, indent: usize) -> RResult<()> {
        p.write(&format!("Associative Algebra of dimension {} with base ring ", self.dim()));
        it.fmt(p, &self.ring.clone(), indent)
    }

    fn elt_same(&self, x: &ExtElt, y: &ExtElt) -> bool {
        Rc::ptr_eq(&x.parent, &y.parent) && coords(x).equal(coords(y)) == Truth::True
    }

    fn elt_hash(&self, x: &ExtElt, mut state: &mut dyn Hasher) {
        hash_key(x).hash(&mut state);
    }

    /// An element prints as its coordinates in parentheses.
    fn fmt_elt(&self, it: &mut Interp, p: &mut Printer, x: &ExtElt, indent: usize) -> RResult<()> {
        let v = coords(x);
        p.write("(");
        for j in 0..v.ncols() {
            if j > 0 {
                p.write(" ");
            }
            let c = entry_of(it, &self.ring, v, 0, j);
            it.fmt(p, &c, indent)?;
        }
        p.write(")");
        Ok(())
    }

    fn coerce(&self, it: &mut Interp, st: &Rc<Struct>, x: &Value, strict: bool) -> RResult<Coerced> {
        coerce(it, st, x, strict)
    }

    /// `S ! x` for a structure S other than the algebra of x: a multiple c
    /// of the identity goes where c does.
    fn coerce_out(&self, it: &mut Interp, s: &Value, x: &ExtElt) -> RResult<Coerced> {
        match self.scalar(coords(x))? {
            Some(c) => {
                let c = it.elem_to_value(&self.ring, c);
                it.try_coerce(s, &c)
            }
            None => Ok(Err(None)),
        }
    }

    /// Operators with an element of an algebra among the operands. The
    /// other operand coerces into the algebra, except for integer exponents.
    fn binop(&self, it: &mut Interp, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
        use BinOp::*;
        if !matches!(op, Add | Sub | Mul | Div | Pow | Eq | Ne) {
            return Ok(None);
        }
        if let (Some(x), Value::Int(n)) = (as_elt(a), b) && op == Pow {
            let alg = alg(&x.parent);
            let base = if n.sign() < 0 {
                match alg.inverse(coords(x))? {
                    Some(z) => z,
                    None if coords(x).is_zero() == Truth::True => return Err(RuntimeError::runtime("Illegal negative power of zero element").in_context("^")),
                    None => return Err(RuntimeError::runtime("Element is not invertible").in_context("^")),
                }
            } else {
                coords(x).clone()
            };
            return Ok(Some(elt(&x.parent, alg.pow(&base, n)?)));
        }
        if matches!(op, Eq | Ne) {
            let e = self.compare_eq(it, a, b, true)?.unwrap_or(false);
            return Ok(Some(Value::Bool(e == (op == Eq))));
        }
        if let (Some(x), Some(y)) = (as_elt(a), as_elt(b)) && !Rc::ptr_eq(&x.parent, &y.parent) {
            if op == Mul {
                return Err(RuntimeError::runtime("Arguments have no covering structure").in_context("*"));
            }
            return Err(not_compatible(it, op, a, b));
        }
        let Some((st, x, y)) = operands(it, a, b)? else { return Err(it.bad_types(op, a, b)) };
        let alg = alg(&st);
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

    fn negate(&self, _it: &mut Interp, x: &ExtElt) -> RResult<Option<Value>> {
        Ok(Some(elt(&x.parent, coords(x).neg()?)))
    }

    /// `a eq b` (or `cmpeq`, not `strict`) with an element of an algebra:
    /// the other value must coerce into its algebra.
    fn compare_eq(&self, it: &mut Interp, a: &Value, b: &Value, strict: bool) -> RResult<Option<bool>> {
        match operands(it, a, b)? {
            Some((_, x, y)) => Ok(Some(x.equal(&y) == Truth::True)),
            None if strict => Err(not_compatible(it, BinOp::Eq, a, b)),
            None => Ok(Some(false)),
        }
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
