//! Lattices (#96), as in the Lattices chapter of the handbook: creating
//! lattices, their elements and their properties (text/331–333), and
//! testing matrices for definiteness (text/340), so far.
//!
//! A lattice of rank m and degree n is the Z-span of the m rows of its
//! basis matrix B in Q^n, with the inner product (v, w) = v M wᵀ for a
//! positive definite n by n matrix M. Both are kept over the base ring,
//! the smallest ring holding them: Z when B and M are integral, Q
//! otherwise. An element is a row of n entries over the base ring. Two
//! lattices are compatible, and their elements comparable, when their
//! base rings and inner product matrices are the same.
//!
//! Lattices are structures of an `ExtKind` (`crate::ext`): printing,
//! coercion, operators, equality and hashing are in its implementation
//! below. An element holds its row of entries.

mod creation;
mod definiteness;
mod elements;
mod properties;

use std::cell::OnceCell;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use calyx_flint::gr::{Ctx, CtxKind, Elem, Truth};
use calyx_flint::mat::Mat;
use calyx_flint::{Integer, Rational};
use calyx_syntax::ast::BinOp;

use crate::error::{RResult, RuntimeError};
use crate::ext::{self, Coerced, ExtElt, ExtKind};
use crate::interp::Interp;
use crate::print::{Level, Printer};
use crate::types::{TypeArg, TypeId, TypeVal, t};
use crate::value::*;

pub use creation::positive_definite;

pub struct Lattice {
    /// The base ring, Z or Q.
    pub ring: Value,
    ctx: Rc<Ctx>,
    /// The basis, one vector in each row, over the base ring.
    pub basis: Mat,
    /// The inner product matrix, over the base ring.
    pub ip: Mat,
    /// The Gram matrix B M Bᵀ, once needed.
    gram: OnceCell<Mat>,
    /// For coordinates, once needed: columns of B that are independent,
    /// and the inverse of those columns, over Q.
    coords: OnceCell<(Vec<usize>, Mat)>,
    /// The coordinate lattice, once needed.
    coordinate_lattice: OnceCell<Rc<Struct>>,
}

/// The matrix `m` over Q.
fn to_q(m: &Mat) -> Mat {
    m.change_ring(&Ctx::rationals()).expect("integers and rationals embed in Q")
}

/// The entry of `m` (over Z or Q) as a rational.
fn rational(m: &Mat, i: usize, j: usize) -> Rational {
    match m.ctx().kind() {
        CtxKind::Integers => Rational::from_integer(&m.integer(i, j)),
        _ => m.entry(i, j).to_rational().expect("a rational entry"),
    }
}

/// Whether the entries of `m` (over Z or Q) are integers.
fn integral(m: &Mat) -> bool {
    matches!(m.ctx().kind(), CtxKind::Integers) || (0..m.nrows()).all(|i| (0..m.ncols()).all(|j| rational(m, i, j).is_integral()))
}

/// The least positive d with d m integral, and d m over Z.
fn num_den(m: &Mat) -> (Mat, Integer) {
    let mut d = Integer::one();
    for i in 0..m.nrows() {
        for j in 0..m.ncols() {
            d = d.lcm(&rational(m, i, j).denominator());
        }
    }
    let mut n = Mat::zero(&Ctx::integers(), m.nrows(), m.ncols());
    for i in 0..m.nrows() {
        for j in 0..m.ncols() {
            let x = &rational(m, i, j) * &Rational::from_integer(&d);
            n.set_integer(i, j, &x.numerator()).expect("an integer");
        }
    }
    (n, d)
}

/// Whether `m` is an identity matrix (the empty 0 by 0 one included).
fn is_identity(m: &Mat) -> bool {
    m.nrows() == m.ncols() && (m.nrows() == 0 || m.is_one() == Truth::True)
}

/// The value of an element of Z or Q.
fn value_of(ring: &Value, e: &Elem) -> Value {
    let q = e.to_rational().expect("a rational");
    if ring.is_integers() { Value::Int(q.numerator()) } else { Value::rat(q) }
}

/// The entries of the row `v` as rationals.
fn row(v: &Mat) -> Vec<Rational> {
    (0..v.ncols()).map(|j| rational(v, 0, j)).collect()
}

impl Lattice {
    pub fn rank(&self) -> usize {
        self.basis.nrows()
    }

    pub fn degree(&self) -> usize {
        self.basis.ncols()
    }

    pub fn ctx(&self) -> &Rc<Ctx> {
        &self.ctx
    }

    pub fn gram(&self) -> &Mat {
        self.gram.get_or_init(|| self.basis.mul(&self.ip).and_then(|x| x.mul(&self.basis.transpose())).expect("the Gram matrix"))
    }

    /// v M wᵀ for rows v and w over the base ring.
    pub fn inner(&self, v: &Mat, w: &Mat) -> Elem {
        v.mul(&self.ip).and_then(|x| x.mul(&w.transpose())).expect("an inner product").entry(0, 0)
    }

    pub fn standard_ip(&self) -> bool {
        is_identity(&self.ip)
    }

    /// The coordinates of the row `v` (over Z or Q) in the basis, if `v`
    /// is in the lattice.
    pub fn coordinates(&self, v: &Mat) -> Option<Vec<Integer>> {
        let (cols, inv) = self.coords.get_or_init(|| {
            let (_, pivots) = to_q(&self.basis).rref().expect("an echelon form");
            let sel = to_q(&self.basis).select(&(0..self.rank()).collect::<Vec<_>>(), &pivots);
            (pivots, sel.inv().expect("independent columns"))
        });
        let v = to_q(v);
        let c = v.select(&[0], cols).mul(inv).expect("coordinates");
        let c: Vec<Rational> = row(&c);
        if !c.iter().all(|x| x.is_integral()) {
            return None;
        }
        let ints: Vec<Integer> = c.iter().map(|x| x.numerator()).collect();
        (self.combination(&ints).equal(&v) == Truth::True).then_some(ints)
    }

    /// The combination of the basis vectors with integer coefficients,
    /// over Q.
    fn combination(&self, c: &[Integer]) -> Mat {
        let mut r = Mat::zero(&Ctx::rationals(), 1, c.len());
        for (i, x) in c.iter().enumerate() {
            r.set_integer(0, i, x).expect("an integer");
        }
        r.mul(&to_q(&self.basis)).expect("a combination")
    }

    /// The combination of the basis vectors with integer coefficients.
    pub fn element(&self, c: &[Integer]) -> Mat {
        let mut r = Mat::zero(&self.ctx, 1, c.len());
        for (i, x) in c.iter().enumerate() {
            r.set_integer(0, i, x).expect("an integer");
        }
        r.mul(&self.basis).expect("a combination")
    }

    pub fn contains(&self, v: &Mat) -> bool {
        self.coordinates(v).is_some()
    }

    /// Whether the elements of the two lattices can be compared.
    pub fn compatible(&self, o: &Lattice) -> bool {
        self.ring == o.ring && self.degree() == o.degree() && self.ip.equal(&o.ip) == Truth::True
    }

    /// Whether `o`, a compatible lattice, is a sublattice.
    pub fn contains_lattice(&self, o: &Lattice) -> bool {
        (0..o.rank()).all(|i| self.contains(&o.basis.block(i, 0, 1, o.degree())))
    }
}

/// A new lattice with the basis and inner product matrix given over Z or
/// Q, over the smallest ring holding them.
pub fn new(basis: &Mat, ip: &Mat) -> Rc<Struct> {
    let (ring, ctx) = if integral(basis) && integral(ip) { (Value::integers(), Ctx::integers()) } else { (Value::rationals(), Ctx::rationals()) };
    let over = |m: &Mat| m.change_ring(&ctx).expect("an integral matrix");
    let lat = Lattice {
        ring,
        basis: over(basis),
        ip: over(ip),
        ctx,
        gram: OnceCell::new(),
        coords: OnceCell::new(),
        coordinate_lattice: OnceCell::new(),
    };
    ext::structure(lat)
}

pub fn lat(st: &Struct) -> &Lattice {
    ext::expect_kind(st)
}

/// The lattice `v` is, if it is one.
pub fn lattice_of(v: &Value) -> Option<(&Rc<Struct>, &Lattice)> {
    match v {
        Value::Struct(st) => ext::kind_of::<Lattice>(st).map(|l| (st, l)),
        _ => None,
    }
}

/// The element of a lattice `v` is, if it is one.
pub fn as_elt(v: &Value) -> Option<&ExtElt> {
    match v {
        Value::Ext(x) if ext::kind_of::<Lattice>(&x.parent).is_some() => Some(x),
        _ => None,
    }
}

/// The entries of an element of a lattice, as a row over its base ring.
pub fn row_of(x: &ExtElt) -> &Mat {
    x.data()
}

/// The element of the lattice `st` with the entries `v`.
pub fn elt(st: &Rc<Struct>, v: Mat) -> Value {
    ext::element(st, v)
}

/// The coordinate lattice of `st`: the standard basis, with the Gram
/// matrix of `st` as the inner product matrix.
pub fn coordinate_lattice(st: &Rc<Struct>) -> Rc<Struct> {
    let l = lat(st);
    l.coordinate_lattice.get_or_init(|| new(&Mat::identity(&Ctx::rationals(), l.rank()).expect("an identity"), l.gram())).clone()
}

/// Whether x and y, elements of lattices, are compatible (their
/// lattices are).
fn compatible_elts(x: &ExtElt, y: &ExtElt) -> bool {
    Rc::ptr_eq(&x.parent, &y.parent) || lat(&x.parent).compatible(lat(&y.parent))
}

// ----- printing ---------------------------------------------------------------------------------

/// The factorization of n > 0 as Magma prints it (`2^5 * 3`), and the
/// number of its primes.
fn factored_text(it: &mut Interp, n: &Integer) -> (String, usize) {
    if n.is_one() {
        return ("1".into(), 0);
    }
    let f = it.factor_int(n);
    let text = f.iter().map(|(p, k)| if *k == 1 { p.to_string() } else { format!("{p}^{k}") }).collect::<Vec<_>>().join(" * ");
    (text, f.len())
}

/// A positive rational factored, with a numerator or denominator of
/// several primes in parentheses when both show: `(3 * 5)/2^2`.
fn factored_rational(it: &mut Interp, q: &Rational) -> String {
    let (num, np) = factored_text(it, &q.numerator());
    if q.denominator().is_one() {
        return num;
    }
    let (den, dp) = factored_text(it, &q.denominator());
    let wrap = |s: String, k: usize| if k > 1 { format!("({s})") } else { s };
    format!("{}/{}", wrap(num, np), wrap(den, dp))
}

/// A lattice: its rank and degree, its determinant unless both the basis
/// and the inner product matrix are multiples of the identity, and the
/// basis and inner product matrix, each as an integral matrix and a
/// denominator, where they are not the identity. Briefly (as in maps), a
/// named lattice prints as its name, another as its first line.
fn fmt_lattice(l: &Lattice, it: &mut Interp, p: &mut Printer, st: &Struct, indent: usize) -> RResult<()> {
    if let (Level::Minimal, Some(name)) = (p.level, *st.name.borrow()) {
        p.write(&format!("Lat: {name}"));
        return Ok(());
    }
    let (bn, bd) = num_den(&l.basis);
    let (mn, md) = num_den(&l.ip);
    let (b_id, m_id) = (is_identity(&bn), is_identity(&mn));
    let kind = if b_id && bd.is_one() { "Standard Lattice" } else { "Lattice" };
    p.write(&format!("{kind} of rank {} and degree {}", l.rank(), l.degree()));
    if p.level == Level::Minimal {
        return Ok(());
    }
    if !(b_id && m_id) {
        let det = if l.rank() == 0 { Rational::one() } else { to_q(l.gram()).det()?.to_rational()? };
        p.newline(indent);
        p.write(&format!("Determinant: {det}"));
        if !det.is_one() {
            let text = factored_rational(it, &det);
            p.newline(indent);
            p.write(&format!("Factored Determinant: {text}"));
        }
    }
    let z = Value::integers();
    if !(b_id && bd.is_one()) && l.rank() > 0 {
        p.newline(indent);
        p.write("Basis:");
        p.newline(indent);
        if b_id {
            p.write("[Identity matrix]");
        } else {
            crate::intrinsics::matrices::fmt_rows(it, p, &z, &bn, true, indent)?;
        }
        if !bd.is_one() {
            p.newline(indent);
            p.write(&format!("Basis Denominator: {bd}"));
        }
    }
    if !m_id {
        p.newline(indent);
        p.write("Inner Product Matrix:");
        p.newline(indent);
        crate::intrinsics::matrices::fmt_rows(it, p, &z, &mn, false, indent)?;
    }
    if !md.is_one() {
        p.newline(indent);
        p.write(&format!("Inner Product Denominator: {md}"));
    }
    Ok(())
}


// ----- coercion ---------------------------------------------------------------------------------

const NOT_IN: &str = "Result is not in the given structure";

/// The row of `n` entries over the base ring of `l` given by a sequence or
/// a vector, or the error for `!` (`strict`).
fn entries(it: &mut Interp, l: &Lattice, elems: &[Value], strict: bool) -> RResult<Result<Mat, Option<String>>> {
    let n = l.degree();
    if elems.len() != n {
        let msg = format!("Sequence argument length ({}) should be {n} to be coerced into a matrix or vector", elems.len());
        return if strict { Err(RuntimeError::runtime(msg).in_context("!")) } else { Ok(Err(None)) };
    }
    let mut v = Mat::zero(&l.ctx, 1, n);
    for (j, c) in elems.iter().enumerate() {
        if !crate::intrinsics::matrices::set_entry(it, &l.ring, &mut v, 0, j, c)? {
            let msg = format!("Cannot coerce sequence element {} into the coefficient ring", j + 1);
            return if strict { Err(RuntimeError::runtime(msg).in_context("!")) } else { Ok(Err(None)) };
        }
    }
    Ok(Ok(v))
}

/// `L ! x`: an element of a compatible lattice, a sequence or vector of
/// entries, or 0, when the result is in L. Only `!` (`strict`) reports
/// sequences that do not coerce.
pub fn coerce(it: &mut Interp, st: &Rc<Struct>, x: &Value, strict: bool) -> RResult<Coerced> {
    let l = lat(st);
    if let Some(e) = as_elt(x) {
        if Rc::ptr_eq(&e.parent, st) {
            return Ok(Ok(x.clone()));
        }
        if !lat(&e.parent).compatible(l) {
            return Ok(Err(None));
        }
    }
    let v = match x {
        Value::Ext(e) => row_of(e).clone(),
        Value::Int(n) if n.is_zero() => Mat::zero(&l.ctx, 1, l.degree()),
        Value::Seq(s) => match entries(it, l, &s.elems, strict)? {
            Ok(v) => v,
            Err(e) => return Ok(Err(e)),
        },
        Value::Mat(m) if m.is_vector() => {
            let elems: Vec<Value> = (0..m.m.ncols()).map(|j| crate::intrinsics::matrices::entry_value(it, m, 0, j)).collect();
            match entries(it, l, &elems, strict)? {
                Ok(v) => v,
                Err(e) => return Ok(Err(e)),
            }
        }
        _ => return Ok(Err(None)),
    };
    if l.contains(&v) { Ok(Ok(elt(st, v))) } else { Ok(Err(Some(NOT_IN.into()))) }
}

// ----- operators --------------------------------------------------------------------------------

fn not_compatible(it: &Interp, op: &str, a: &Value, b: &Value) -> RuntimeError {
    let msg = format!("Arguments are not compatible\nArgument types given: {}, {}", it.type_name_ext(a), it.type_name_ext(b));
    RuntimeError::runtime(msg).in_context(op)
}

/// The lattice holding the sum of elements of two compatible lattices:
/// either lattice if it contains the other, else the lattice they
/// generate.
fn covering(x: &ExtElt, y: &ExtElt) -> Rc<Struct> {
    if Rc::ptr_eq(&x.parent, &y.parent) {
        return x.parent.clone();
    }
    let (lx, ly) = (lat(&x.parent), lat(&y.parent));
    if lx.contains_lattice(ly) {
        x.parent.clone()
    } else if ly.contains_lattice(lx) {
        y.parent.clone()
    } else {
        creation::generated(&to_q(&lx.basis).concat_vertical(&to_q(&ly.basis)), &to_q(&lx.ip))
    }
}

/// The scalar s as a rational.
fn rational_scalar(s: &Value) -> Option<Rational> {
    match s {
        Value::Int(n) => Some(Rational::from_integer(n)),
        Value::Rat(q) => Some((**q).clone()),
        _ => None,
    }
}

/// Operators with an element of a lattice among the operands; None for
/// those that do not apply.
fn elt_binop(it: &mut Interp, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
    use BinOp::*;
    let name = op.intrinsic_name();
    let q = Value::rationals();
    let r = match (op, as_elt(a), as_elt(b)) {
        (Eq | Ne, _, _) => return Ok(compare_eq(it, a, b, true)?.map(|e| Value::Bool(e == (op == Eq)))),
        (Add | Sub, Some(x), Some(y)) => {
            if !compatible_elts(x, y) {
                return Err(not_compatible(it, name, a, b));
            }
            let st = covering(x, y);
            let v = if op == Add { row_of(x).add(row_of(y))? } else { row_of(x).sub(row_of(y))? };
            elt(&st, v)
        }
        (Mul, Some(x), None) | (Mul, None, Some(x)) => {
            let other = if as_elt(a).is_some() { b } else { a };
            match other {
                Value::Int(n) => {
                    let c = Elem::from_integer(&lat(&x.parent).ctx, n)?;
                    elt(&x.parent, row_of(x).mul_scalar(&c)?)
                }
                Value::Rat(s) => {
                    let c = Elem::from_rational(&Ctx::rationals(), s)?;
                    let v = to_q(row_of(x)).mul_scalar(&c)?;
                    crate::intrinsics::matrices::vec_value(it, &q, v)?
                }
                Value::Mat(t) if !t.is_vector() && other == b => return elements::transform(it, x, t, a, b).map(Some),
                _ => return Ok(None),
            }
        }
        (Div, Some(x), None) => {
            let Some(s) = rational_scalar(b) else { return Ok(None) };
            let Some(inv) = s.inv() else { return Err(RuntimeError::runtime("Division by zero").in_context("/")) };
            let v = to_q(row_of(x)).mul_scalar(&Elem::from_rational(&Ctx::rationals(), &inv)?)?;
            crate::intrinsics::matrices::vec_value(it, &q, v)?
        }
        (IntDiv, Some(x), None) => match b {
            Value::Int(d) => return elements::exact_div(it, x, d).map(Some),
            _ => return Ok(None),
        },
        (In | Notin, Some(x), None) => match lattice_of(b) {
            Some((st, l)) => {
                if !Rc::ptr_eq(&x.parent, st) && !lat(&x.parent).compatible(l) {
                    return Err(RuntimeError::runtime("Arguments have no covering structure").in_context(name));
                }
                Value::Bool(l.contains(row_of(x)) == (op == In))
            }
            None => return Ok(None),
        },
        _ => return Ok(None),
    };
    Ok(Some(r))
}

/// Operators with a lattice among the operands and no element of one:
/// `eq` and `subset` between compatible lattices.
fn lattice_binop(it: &mut Interp, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
    use BinOp::*;
    let (Some((sa, la)), Some((sb, lb))) = (lattice_of(a), lattice_of(b)) else { return Ok(None) };
    if !matches!(op, Eq | Ne | Subset | Notsubset) {
        return Ok(None);
    }
    if !Rc::ptr_eq(sa, sb) && !la.compatible(lb) {
        return Err(not_compatible(it, op.intrinsic_name(), a, b));
    }
    let r = match op {
        Eq | Ne => (Rc::ptr_eq(sa, sb) || (la.rank() == lb.rank() && la.contains_lattice(lb) && lb.contains_lattice(la))) == (op == Eq),
        _ => lb.contains_lattice(la) == (op == Subset),
    };
    Ok(Some(Value::Bool(r)))
}

/// `a eq b` (or `cmpeq`, not `strict`) with an element of a lattice:
/// equal entries of elements of compatible lattices; another value is
/// first coerced into the lattice.
fn compare_eq(it: &mut Interp, a: &Value, b: &Value, strict: bool) -> RResult<Option<bool>> {
    let incompatible = |it: &Interp| if strict { Err(not_compatible(it, "eq", a, b)) } else { Ok(Some(false)) };
    match (as_elt(a), as_elt(b)) {
        (Some(x), Some(y)) => {
            if compatible_elts(x, y) {
                Ok(Some(row_of(x).equal(row_of(y)) == Truth::True))
            } else {
                incompatible(it)
            }
        }
        (Some(x), None) | (None, Some(x)) => {
            let other = if as_elt(a).is_some() { b } else { a };
            match coerce(it, &x.parent, other, false)? {
                Ok(y) => Ok(Some(row_of(x).equal(row_of(as_elt(&y).expect("an element of the lattice"))) == Truth::True)),
                _ => incompatible(it),
            }
        }
        (None, None) => Ok(None),
    }
}

impl ExtKind for Lattice {
    fn struct_type(&self) -> TypeId {
        t::LAT
    }

    fn elt_type(&self) -> TypeId {
        t::LAT_ELT
    }

    /// Magma names the base ring in the element type in errors.
    fn elt_type_ext(&self) -> TypeVal {
        TypeVal::Ext(t::LAT_ELT, Rc::from(vec![TypeArg::Type(TypeVal::Cat(self.ring.type_id()))]))
    }

    fn fmt_struct(&self, it: &mut Interp, p: &mut Printer, st: &Struct, indent: usize) -> RResult<()> {
        fmt_lattice(self, it, p, st, indent)
    }

    /// Elements are equal when they have the same entries in compatible
    /// lattices.
    fn elt_same(&self, x: &ExtElt, y: &ExtElt) -> bool {
        as_elt_ext(y) && compatible_elts(x, y) && row_of(x).equal(row_of(y)) == Truth::True
    }

    fn elt_hash(&self, x: &ExtElt, mut state: &mut dyn Hasher) {
        row(row_of(x)).hash(&mut state);
    }

    /// An element prints as a vector.
    fn fmt_elt(&self, it: &mut Interp, p: &mut Printer, x: &ExtElt, indent: usize) -> RResult<()> {
        let v = row_of(x);
        if v.ncols() == 0 {
            p.write("()");
            return Ok(());
        }
        crate::intrinsics::matrices::fmt_rows(it, p, &self.ring, v, true, indent)
    }

    /// Elements print one on each line in sequences, as vectors do.
    fn elt_is_simple(&self, _x: &ExtElt) -> bool {
        false
    }

    fn coerce(&self, it: &mut Interp, st: &Rc<Struct>, x: &Value, strict: bool) -> RResult<Coerced> {
        coerce(it, st, x, strict)
    }

    fn binop(&self, it: &mut Interp, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
        elt_binop(it, op, a, b)
    }

    fn struct_binop(&self, it: &mut Interp, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
        lattice_binop(it, op, a, b)
    }

    fn negate(&self, _it: &mut Interp, x: &ExtElt) -> RResult<Option<Value>> {
        Ok(Some(elt(&x.parent, row_of(x).neg()?)))
    }

    fn compare_eq(&self, it: &mut Interp, a: &Value, b: &Value, strict: bool) -> RResult<Option<bool>> {
        compare_eq(it, a, b, strict)
    }
}

/// Whether x is an element of a lattice.
fn as_elt_ext(x: &ExtElt) -> bool {
    ext::kind_of::<Lattice>(&x.parent).is_some()
}

/// Register the intrinsics of the chapter.
pub fn register(it: &mut Interp) {
    creation::register(it);
    elements::register(it);
    properties::register(it);
    definiteness::register(it);
}
