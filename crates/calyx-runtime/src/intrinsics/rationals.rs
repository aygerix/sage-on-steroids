//! The functions of the Rational Field chapter: Q as a number field of
//! degree 1 (bases, invariants, unit, class and automorphism groups,
//! decomposition of primes), and the functions of rational numbers
//! (height, rounding, continued fractions, rational reconstruction,
//! valuations).

use std::cell::RefCell;
use std::rc::Rc;

use calyx_flint::{Integer, Rational};
use calyx_syntax::ast::AggKind;

use super::residue::Res;
use super::{arg_ge, arg_not, arg_prime, boolv, intv, one};
use crate::abgroups::{elt, new_group};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn rat(a: &CallArgs, i: usize) -> &Rational {
    match &a.args[i] {
        Value::Rat(q) => q,
        _ => unreachable!("signature admits only rationals"),
    }
}

/// A sequence of rationals.
fn rat_seq(v: impl IntoIterator<Item = Rational>) -> Value {
    Value::seq(Some(Value::rationals()), v.into_iter().map(Value::rat).collect())
}

fn one_q() -> Value {
    Value::rat(Rational::one())
}

// ----- creation --------------------------------------------------------------

fn integers(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::integers())
}

fn rationals(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::rationals())
}

fn identity(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(one_q())
}

/// 1 or -1 for n = 1, 2; Q has no other roots of unity.
fn root_of_unity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?;
    if n.sign() <= 0 {
        return Err(arg_ge(1, n, 1));
    }
    match n.to_u64() {
        Some(1) => one(one_q()),
        Some(2) => one(Value::rat(Rational::from_i64(-1))),
        Some(k) if k < 1 << 30 => Err(RuntimeError::runtime(format!("{k}-th root of unity not in given field"))),
        _ => Err(RuntimeError::runtime(format!("Argument 1 ({n}) is too large"))),
    }
}

/// A numerator in [-u..u] over a denominator in [1..u], u = |m|.
fn random(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let u = a.int(1)?.abs();
    if u.is_zero() {
        return one(Value::rat(Rational::zero()));
    }
    let n = it.rng.range(&-&u, &u);
    let d = it.rng.range(&Integer::one(), &u);
    one(Value::rat(Rational::new(&n, &d).unwrap()))
}

// ----- Q as a number field ---------------------------------------------------

/// `[ 1 ]`: the bases of Q over itself and over Z.
fn basis(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(rat_seq([Rational::one()]))
}

fn minimal_field_set(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::rationals())
}

fn one_int(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::one())
}

fn signature(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    Ok(vals![Value::int(1), Value::int(0)])
}

/// `x - 1`, whose root 1 generates Q.
fn defining_polynomial(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let px = it.poly_ring(&Value::rationals(), true)?;
    one(it.coerce(&px, &rat_seq([Rational::from_i64(-1), Rational::one()]))?)
}

/// `Q.1`, the generator 1.
fn generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let i = a.int(1)?;
    if !i.is_one() {
        return Err(RuntimeError::runtime(format!("Value for name index ({i}) should be in the range [1..1]")));
    }
    one(one_q())
}

/// The primes of Q over p (or -p): `[ <|p|, 1> ]`.
fn decomposition(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = match &a.args[1] {
        Value::Int(p) if p.abs().is_prime() => Value::Int(p.abs()),
        Value::Int(_) => return Err(super::require(RuntimeError::runtime("Argument 2 must be a prime element."))),
        // The infinite prime (either infinity) is real, unramified.
        _ => Value::Infinity(true),
    };
    one(it.build_aggregate(AggKind::Seq, None, vec![Value::tuple(vec![p, Value::int(1)])], false)?)
}

/// The units {1, -1} of Z as Z/2, with the map that Magma defines by its
/// graph.
struct UnitMap;

fn unit_image(m: &MapObj, x: &Value) -> Option<Value> {
    let (Value::AbElt(e), Value::Struct(st)) = (x, &m.domain) else { return None };
    if !Rc::ptr_eq(&e.group, st) {
        return None;
    }
    Some(Value::rat(Rational::from_i64(if e.coords[0].is_zero() { 1 } else { -1 })))
}

impl NativeMap for UnitMap {
    fn apply(&self, _it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        unit_image(m, x).ok_or_else(|| RuntimeError::runtime("Application of map failed").in_context("map application"))
    }

    fn preimage(&self, _it: &mut Interp, _m: &MapObj, _y: &Value) -> RResult<Value> {
        Err(RuntimeError::runtime("Map has no inverse").in_context("@@"))
    }

    fn graph(&self, m: &MapObj) -> Option<Vec<(Value, Value)>> {
        let Value::Struct(st) = &m.domain else { return None };
        Some([0, 1].iter().map(|&c| (elt(st, vec![Integer::from_u64(c)]), Value::rat(Rational::from_i64(1 - 2 * c as i64)))).collect())
    }
}

/// The unit group of Z, with both results always returned.
fn unit_group(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let group = new_group(vec![Integer::from_u64(2)]);
    let map = Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: Value::Struct(group.clone()), codomain: Value::rationals(), imp: MapImpl::Native(Rc::new(UnitMap)) }));
    Ok(vals![Value::Struct(group), map])
}

fn class_group(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (group, map) = super::abgroups::class_group_of_z();
    super::abgroups::with_map(a, group, map)
}

/// The map from `Sym(1)` onto the automorphisms of Q: every element goes
/// to the identity.
struct AutMap;

impl NativeMap for AutMap {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        if it.try_coerce(&m.domain, x)?.is_err() {
            return Err(RuntimeError::runtime("Element is not in the domain of the map").in_context("map application"));
        }
        let q = Value::rationals();
        Ok(Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: q.clone(), codomain: q, imp: MapImpl::Coercion })))
    }

    fn preimage(&self, _it: &mut Interp, _m: &MapObj, _y: &Value) -> RResult<Value> {
        Err(RuntimeError::runtime("Map has no inverse").in_context("@@"))
    }

    fn rule(&self) -> bool {
        true
    }
}

thread_local! {
    /// The automorphisms of Q and the map onto them from `Sym(1)`, made
    /// once for the group (Magma returns the same objects every time).
    static AUTS: RefCell<Option<(Rc<Struct>, Value, Value)>> = const { RefCell::new(None) };
}

fn automorphism_group(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let g = it.sym_group(1);
    let cached = AUTS.with(|c| c.borrow().as_ref().filter(|(h, _, _)| Rc::ptr_eq(h, &g)).map(|(_, p, f)| (p.clone(), f.clone())));
    let (p, f) = match cached {
        Some(pf) => pf,
        None => {
            let p = Value::structure(StructKind::Automorphisms(Value::rationals()));
            let f = Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: Value::Struct(g.clone()), codomain: p.clone(), imp: MapImpl::Native(Rc::new(AutMap)) }));
            AUTS.with(|c| *c.borrow_mut() = Some((g.clone(), p.clone(), f.clone())));
            (p, f)
        }
    };
    Ok(vals![Value::Struct(g), p, f])
}

/// The map from Q to Q as an algebra or a vector space of dimension 1 over
/// itself, and back. Magma's handbook calls it the map from the algebra or
/// space to Q, but Magma 2.22 gives it the other way round.
struct OverItself;

impl NativeMap for OverItself {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let Ok(q) = it.try_coerce(&Value::rationals(), x)? else {
            return Err(RuntimeError::runtime("Element is not in the domain of the map").in_context("map application"));
        };
        match &m.codomain {
            Value::Struct(st) if matches!(st.kind, StructKind::Matrices(_)) => {
                let mut v = calyx_flint::mat::Mat::zero(&super::matrices::entry_ctx(it, &Value::rationals())?, 1, 1);
                super::matrices::set_entry(it, &Value::rationals(), &mut v, 0, 0, &q)?;
                super::matrices::vec_value(it, &Value::rationals(), v)
            }
            s => it.coerce(s, &q),
        }
    }

    fn preimage(&self, it: &mut Interp, m: &MapObj, y: &Value) -> RResult<Value> {
        // y is first coerced into the codomain, as a sequence [q] can be.
        match it.try_coerce(&m.codomain, y)? {
            Ok(Value::Mat(v)) => Ok(super::matrices::entry_value(it, &v, 0, 0)),
            Ok(a) => it.coerce(&Value::rationals(), &a),
            Err(_) => Err(RuntimeError::runtime("Element is not in the codomain of the map").in_context("@@")),
        }
    }

    fn rule_with_inverse(&self) -> bool {
        true
    }
}

/// The error for a second argument other than Q.
fn check_subfield(a: &CallArgs) -> RResult<()> {
    if a.args[1].is_rationals() {
        return Ok(());
    }
    Err(super::bare(RuntimeError::runtime("Argument 2 must be a subfield of argument 1")))
}

/// `Algebra(Q, Q)`: Q as an associative algebra of dimension 1 over itself,
/// with the map from Q.
fn algebra(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_subfield(a)?;
    let q = Value::rationals();
    let ctx = super::matrices::entry_ctx(it, &q)?;
    let e = calyx_flint::mat::Mat::identity(&ctx, 1)?;
    let alg = Value::Struct(super::algass::new(it, &q, vec![e.clone()], e)?);
    let map = MapObj { kind: MapKind::Map, domain: q, codomain: alg.clone(), imp: MapImpl::Native(Rc::new(OverItself)) };
    Ok(vals![alg, Value::Map(Rc::new(map))])
}

/// `VectorSpace(Q, Q)`: Q as a vector space of dimension 1 over itself,
/// with the map from Q.
fn vector_space(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_subfield(a)?;
    let q = Value::rationals();
    let v = Value::Struct(super::matrices::parent(it, &q, 1, 1, super::matrices::Shape::Tuples)?);
    let map = MapObj { kind: MapKind::Map, domain: q, codomain: v.clone(), imp: MapImpl::Native(Rc::new(OverItself)) };
    Ok(vals![v, Value::Map(Rc::new(map))])
}

/// `hom< Q -> R | >`: r/s goes to r * s^-1 in R, where that makes sense.
struct RationalHom;

impl NativeMap for RationalHom {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let failed = || RuntimeError::runtime("Application of map failed").in_context("map application");
        let Ok(q) = it.try_coerce(&Value::rationals(), x)? else { return Err(failed()) };
        it.try_coerce(&m.codomain, &q)?.map_err(|_| failed())
    }

    fn preimage(&self, _it: &mut Interp, _m: &MapObj, _y: &Value) -> RResult<Value> {
        Err(RuntimeError::runtime("Map has no inverse").in_context("@@"))
    }
}

/// `hom< Q -> R | ... >` with `n` images: the natural map into a ring R,
/// which takes no images.
pub fn rational_hom(codomain: &Value, n: usize) -> RResult<Value> {
    if n != 0 {
        return Err(RuntimeError::runtime("Wrong number of arguments to FldRat homomorphism element constructor (should be 0)"));
    }
    if !matches!(codomain.as_struct(), Some(StructKind::Integers | StructKind::Rationals | StructKind::Reals(_) | StructKind::Ring(_))) {
        return Err(RuntimeError::runtime("Homomorphism has an invalid codomain"));
    }
    Ok(Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: Value::rationals(), codomain: codomain.clone(), imp: MapImpl::Native(Rc::new(RationalHom)) })))
}

// ----- elements --------------------------------------------------------------

fn is_regular(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(!rat(a, 0).is_zero())
}

/// Conjugates, norms and traces of a rational: itself.
fn itself(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(a.args[0].clone())
}

/// `x - q` in the global polynomial ring over Q.
fn minimal_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let q = rat(a, 0).clone();
    let px = it.poly_ring(&Value::rationals(), true)?;
    one(it.coerce(&px, &rat_seq([-&q, Rational::one()]))?)
}

fn eltseq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(rat_seq([rat(a, 0).clone()]))
}

/// The larger of |numerator| and denominator.
fn height(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, d) = match &a.args[0] {
        Value::Int(n) => (n.abs(), Integer::one()),
        _ => (rat(a, 0).numerator().abs(), rat(a, 0).denominator()),
    };
    intv(if n > d { n } else { d })
}

fn qround(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (q, m) = (rat(a, 0), a.int(1)?);
    let r = if a.param_bool("ContFrac")? { qround_cf(q, m)? } else { qround_ceiling(q, m) };
    one(Value::rat(r))
}

/// Magma's quick rounding: Ceiling(q*M)/M (q itself for M = 0).
pub fn qround_ceiling(q: &Rational, m: &Integer) -> Rational {
    if m.is_zero() {
        return q.clone();
    }
    let c = (&q.numerator() * m).cdiv_q(&q.denominator()).unwrap();
    Rational::new(&c, m).unwrap()
}

/// The last convergent of the continued fraction of q with denominator at
/// most M, except that Magma returns a + 1/M for q = a + 1/(M+1).
pub fn qround_cf(q: &Rational, m: &Integer) -> RResult<Rational> {
    if m.is_zero() {
        return Ok(q.clone());
    }
    // p0/q0 and p1/q1 are the convergents before the next one.
    let (mut p0, mut q0, mut p1, mut q1) = (Integer::zero(), Integer::one(), Integer::one(), Integer::zero());
    let (mut n, mut d) = (q.numerator(), q.denominator());
    for k in 0.. {
        let (t, r) = n.fdiv_qr(&d).unwrap();
        let (p2, q2) = (&(&t * &p1) + &p0, &(&t * &q1) + &q0);
        if &q2 > m {
            if k == 1 && r.is_zero() && q2 == m + &Integer::one() {
                return Ok(Rational::new(&(&(m * &p1) + &p0), &(&(m * &q1) + &q0)).unwrap());
            }
            break;
        }
        (p0, q0, p1, q1) = (p1, q1, p2, q2);
        if r.is_zero() {
            break;
        }
        (n, d) = (d, r);
    }
    Rational::new(&p1, &q1).ok_or_else(|| RuntimeError::runtime("Division by zero").in_context("/"))
}

/// The partial quotients of the continued fraction of n/d (d > 0).
pub fn continued_fraction(q: &Rational) -> Vec<Integer> {
    let (mut n, mut d) = (q.numerator(), q.denominator());
    let mut out = Vec::new();
    loop {
        let (t, r) = n.fdiv_qr(&d).unwrap();
        out.push(t);
        if r.is_zero() {
            return out;
        }
        (n, d) = (d, r);
    }
}

/// The partial quotients a1, a2, ... of q = a1 - 1/(a2 - 1/(a3 - ...)),
/// taking ceilings (so a2, a3, ... are at least 2).
pub fn hj_continued_fraction(q: &Rational) -> Vec<Integer> {
    let (mut n, mut d) = (q.numerator(), q.denominator());
    let mut out = Vec::new();
    loop {
        let t = n.cdiv_q(&d).unwrap();
        let r = &(&t * &d) - &n;
        out.push(t);
        if r.is_zero() {
            return out;
        }
        (n, d) = (d, r);
    }
}

/// The value of a non-empty continued fraction c1 + s/(c2 + s/(c3 + ...)),
/// s = 1 for the regular kind and -1 for the Hirzebruch-Jung kind, evaluated
/// from the last quotient; None if a denominator vanishes.
pub fn continued_fraction_value(cs: &[Integer], s: i64) -> Option<Rational> {
    let (last, rest) = cs.split_last()?;
    // The value so far is n/d, kept in lowest terms by the recurrence.
    let (mut n, mut d) = (last.clone(), Integer::one());
    for c in rest.iter().rev() {
        if n.is_zero() {
            return None;
        }
        let t = if s > 0 { &(c * &n) + &d } else { &(c * &n) - &d };
        (n, d) = (t, n);
    }
    Rational::new(&n, &d)
}

fn cf_value(a: &CallArgs, s: i64) -> RResult<Rational> {
    let cs = super::ints::ints_of(&a.args[0])?;
    if cs.is_empty() {
        return Err(arg_not(1, "non-empty"));
    }
    continued_fraction_value(&cs, s).ok_or_else(|| RuntimeError::runtime("Division by zero"))
}

fn cf_intr(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let q = match &a.args[0] {
        Value::Int(n) => Rational::from_integer(n),
        _ => rat(a, 0).clone(),
    };
    // Bound limits the quotients to at least one; as Magma takes it, a
    // negative small integer (below 2^30) is refused and a larger one
    // leaves them unlimited.
    let most = match a.param("Bound") {
        None | Some(Value::Undef) => None,
        Some(Value::Int(b)) => match b.to_i64().filter(|b| b.unsigned_abs() < 1 << 30) {
            Some(b) if b < 0 => return Err(RuntimeError::runtime("Bad value for parameter 'Bound'")),
            b => b.map(|b| b.max(1) as usize),
        },
        Some(_) => return Err(RuntimeError::runtime("Bad type for parameter 'Bound'\nArgument types given: FldRatElt")),
    };
    if !matches!(a.param("Numerators"), None | Some(Value::Undef)) {
        return Err(RuntimeError::runtime("The optional argument 'Numerators' is not supported"));
    }
    let mut cf = continued_fraction(&q);
    cf.truncate(most.unwrap_or(usize::MAX));
    one(Value::int_seq(cf))
}

fn cf_value_intr(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::rat(cf_value(a, 1)?))
}

fn hj_cf_intr(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int_seq(hj_continued_fraction(rat(a, 0))))
}

fn hj_cf_value_intr(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::rat(cf_value(a, -1)?))
}

/// The fraction n/d with |n|, d <= sqrt(m/2) and n = s*d mod m, if there
/// is one (by the half-extended Euclidean algorithm, whose choice Magma
/// shares where 2(sqrt(m/2))^2 = m leaves two).
pub fn rational_reconstruction(s: &Integer, m: &Integer) -> Option<Rational> {
    let bound = m.fdiv_2exp(1).isqrt()?;
    // FLINT's is faster on large moduli, where the answer is unique.
    if m.bits() > 64 && &(&bound * &bound).mul_2exp(1) != m {
        return Rational::reconstruct(s, m, &bound);
    }
    reconstruct_euclid(s, m, &bound)
}

fn reconstruct_euclid(s: &Integer, m: &Integer, bound: &Integer) -> Option<Rational> {
    let (mut r0, mut r1) = (m.clone(), s.div_rem_euclid(m)?.1);
    let (mut t0, mut t1) = (Integer::zero(), Integer::one());
    while &r1 > bound {
        let (q, r) = r0.fdiv_qr(&r1)?;
        let t = &t0 - &(&q * &t1);
        (r0, r1, t0, t1) = (r1, r, t1, t);
    }
    if &t1.abs() > bound || !r1.gcd(&t1).is_one() {
        return None;
    }
    Rational::new(&r1, &t1)
}

fn rational_reconstruction_intr(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (s, m) = match Res::of(&a.args[0]) {
        Some(r) => (r.x, r.m),
        None => {
            let e = crate::rings::small::elt_of(&a.args[0]).expect("a finite field element");
            let f = e.ring().finite_field().expect("a finite field element");
            if f.degree != 1 {
                return Err(RuntimeError::runtime("Field must be prime"));
            }
            (e.residue().unwrap_or_default(), f.p.clone())
        }
    };
    Ok(match rational_reconstruction(&s, &m) {
        Some(q) => vals![Value::Bool(true), Value::rat(q)],
        None => vals![Value::Bool(false), Value::Undef],
    })
}

/// The rational reconstruction of every entry of a matrix or vector over a
/// prime field, or false if one has none.
fn rational_reconstruction_mat(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    use super::matrices::{entry_ctx, entry_value, mat_value, set_entry, vec_value};
    let Value::Mat(m) = a.args[0].clone() else { unreachable!("a matrix") };
    let not_finite = || RuntimeError::runtime("Coefficient ring of argument 1 is not a finite field");
    let p = match m.ring().as_struct() {
        Some(StructKind::Ring(r)) => match r.finite_field() {
            Some(f) if f.degree == 1 => f.p.clone(),
            Some(_) => return Err(RuntimeError::runtime("Coefficient field must be prime")),
            None => return Err(not_finite()),
        },
        _ => return Err(not_finite()),
    };
    let q = Value::rationals();
    let mut out = calyx_flint::mat::Mat::zero(&entry_ctx(it, &q)?, m.m.nrows(), m.m.ncols());
    for i in 0..m.m.nrows() {
        for j in 0..m.m.ncols() {
            let s = crate::rings::small::elt_of(&entry_value(it, &m, i, j)).and_then(|e| e.residue()).unwrap_or_default();
            let Some(r) = rational_reconstruction(&s, &p) else { return Ok(vals![Value::Bool(false), Value::Undef]) };
            set_entry(it, &q, &mut out, i, j, &Value::rat(r))?;
        }
    }
    let r = if m.is_vector() { vec_value(it, &q, out)? } else { mat_value(it, &q, out)? };
    Ok(vals![Value::Bool(true), r])
}

/// The valuation of x at the prime p, and x / p^v when asked for (or
/// always, with `both`).
fn valuation_at(a: &CallArgs, p: &Integer, both: bool) -> RResult<Vals> {
    if p.sign() <= 0 {
        return Err(arg_not(2, "positive"));
    }
    if !p.is_prime() {
        return Err(arg_prime(2, p));
    }
    let x = rat(a, 0);
    let two = a.nresults >= 2 || both;
    if x.is_zero() {
        return Ok(if two { vals![Value::Infinity(true), Value::rat(Rational::zero())] } else { vals![Value::Infinity(true)] });
    }
    let (vn, n) = x.numerator().remove(p);
    let (vd, d) = x.denominator().remove(p);
    let v = Integer::from_i64(vn as i64 - vd as i64);
    if !two {
        return intv(v);
    }
    Ok(vals![Value::Int(v), Value::rat(Rational::new(&n, &d).unwrap())])
}

fn valuation(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = a.int(1)?.clone();
    valuation_at(a, &p, false)
}

/// The valuation at a prime ideal of Z (both values always, as Magma's
/// package intrinsic returns them).
fn valuation_ideal(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = match a.args[1].as_struct() {
        Some(StructKind::IntIdeal(n)) => n.clone(),
        _ => Integer::one(),
    };
    valuation_at(a, &p, true)
}

pub fn register(it: &mut Interp) {
    // creation
    it.def("MaximalOrder", "Q::FldRat -> RngInt", "The maximal order Z of Q.", integers);
    it.def("FieldOfFractions", "Q::FldRat -> FldRat", "The field of fractions of Q, Q itself.", rationals);
    it.def("Identity", "Q::FldRat -> FldRatElt", "The identity 1 of Q.", identity);
    it.def("RootOfUnity", "n::RngIntElt, Q::FldRat -> FldRatElt", "A primitive n-th root of unity in Q (n = 1 or 2).", root_of_unity);
    it.def("Random", "Q::FldRat, m::RngIntElt -> FldRatElt", "A random rational with numerator in [-|m|..|m|] and denominator in [1..|m|].", random);
    it.def(".", "Q::FldRat, i::RngIntElt -> FldRatElt", "The generator 1 of Q.", generator);

    // Q as a number field
    for name in ["IntegralBasis", "Basis", "AbsoluteBasis"] {
        it.def(name, "Q::FldRat -> [FldRatElt]", "The basis [ 1 ] of Q.", basis);
    }
    it.def("MinimalField", "q::FldRatElt -> FldRat", "The least cyclotomic field containing q, the rational field.", minimal_field_set);
    it.def("MinimalField", "S::{FldRatElt} -> FldRat", "The least cyclotomic field containing the elements of S, the rational field.", minimal_field_set);
    it.def("BaseField", "Q::FldRat -> FldRat", "The coefficient field of Q, Q itself.", rationals);
    it.def("UnitGroup", "Q::FldRat -> GrpAb, Map", "The unit group {1, -1} of Z as Z/2, with the map into Q.", unit_group);
    it.def("ClassGroup", "Q::FldRat -> GrpAb, Map", "The trivial class group of Z, with the map onto its ideals.", class_group);
    it.def("AutomorphismGroup", "Q::FldRat -> GrpPerm, PowMapAut, Map", "The trivial group of automorphisms of Q, their parent and the map onto them.", automorphism_group);
    it.def("AutomorphismGroup", "Q::FldRat, R::FldRat -> GrpPerm, PowMapAut, Map", "The trivial group of automorphisms of Q, their parent and the map onto them.", automorphism_group);
    it.def("Algebra", "Q::FldRat, K::Fld -> AlgAss, Map", "Q as an associative algebra over itself (K = Q), with the map from Q.", algebra);
    it.def("VectorSpace", "Q::FldRat, K::Fld -> ModTupFld, Map", "Q as a vector space over itself (K = Q), with the map from Q.", vector_space);
    it.def("Decomposition", "Q::FldRat, p::RngIntElt -> []", "The decomposition [ <p, 1> ] of the prime p in Q.", decomposition);
    it.def("Decomposition", "Q::FldRat, p::Infty -> []", "The decomposition [ <Infinity, 1> ] of the infinite prime in Q.", decomposition);
    for name in ["Conductor", "Degree", "AbsoluteDegree", "Discriminant", "AbsoluteDiscriminant"] {
        it.def(name, "Q::FldRat -> RngIntElt", "1, for Q as a number field.", one_int);
    }
    it.def("DefiningPolynomial", "Q::FldRat -> RngUPolElt", "The polynomial x - 1 over Q.", defining_polynomial);
    it.def("Signature", "Q::FldRat -> RngIntElt, RngIntElt", "The signature 1, 0 of Q.", signature);

    // elements
    it.def("IsRegular", "q::FldRatElt -> BoolElt", "Whether q is not a zero divisor (is non-zero).", is_regular);
    for name in ["ComplexConjugate", "Conjugate", "Norm", "Trace"] {
        it.def(name, "q::FldRatElt -> FldRatElt", "q itself.", itself);
    }
    it.def("MinimalPolynomial", "q::FldRatElt -> RngUPolElt", "The polynomial x - q over Q.", minimal_polynomial);
    for name in ["Eltseq", "ElementToSequence"] {
        it.def(name, "q::FldRatElt -> [FldRatElt]", "The sequence [q].", eltseq);
    }
    it.def("Height", "q::FldRatElt -> RngIntElt", "The larger of the absolute values of the numerator and denominator of q.", height);
    it.def("Height", "n::RngIntElt -> RngIntElt", "The larger of |n| and 1.", height);
    it.def_params(
        "Qround",
        "q::FldRatElt, M::RngIntElt -> FldRatElt",
        &[("ContFrac", Value::Bool(false))],
        "An approximation of q with denominator at most M (a convergent of the continued fraction of q with ContFrac).",
        qround,
    );
    it.def_params(
        "ContinuedFraction",
        "q::FldRatElt -> [RngIntElt]",
        &[("Bound", Value::Undef), ("Numerators", Value::Undef)],
        "The partial quotients of the continued fraction of q, at most Bound of them.",
        cf_intr,
    );
    it.def("ContinuedFraction", "n::RngIntElt -> [RngIntElt]", "The continued fraction [ n ] of n.", cf_intr).package = true;
    it.def("ContinuedFractionValue", "C::[RngIntElt] -> FldRatElt", "The rational with continued fraction C.", cf_value_intr);
    for name in ["HirzebruchJungContinuedFraction", "HJContinuedFraction"] {
        it.def(name, "q::FldRatElt -> [RngIntElt]", "The partial quotients of the Hirzebruch-Jung continued fraction of q.", hj_cf_intr);
    }
    for name in ["HirzebruchJungContinuedFractionValue", "HJContinuedFractionValue"] {
        it.def(name, "C::[RngIntElt] -> FldRatElt", "The rational with Hirzebruch-Jung continued fraction C.", hj_cf_value_intr);
    }
    it.def(
        "RationalReconstruction",
        "s::RngIntResElt -> BoolElt, FldRatElt",
        "Whether some n/d with |n|, d <= Sqrt(m/2) is congruent to s modulo m, and that rational.",
        rational_reconstruction_intr,
    );
    it.def(
        "RationalReconstruction",
        "s::FldFinElt -> BoolElt, FldRatElt",
        "Whether some n/d with |n|, d <= Sqrt(p/2) is congruent to s modulo p, and that rational.",
        rational_reconstruction_intr,
    );
    it.def(
        "RationalReconstruction",
        "M::Mtrx -> BoolElt, Mtrx",
        "Whether every entry of M, over a prime field, has a rational reconstruction, and the matrix of them.",
        rational_reconstruction_mat,
    );
    it.def("Valuation", "x::FldRatElt, p::RngIntElt -> RngIntElt, FldRatElt", "The valuation v of x at the prime p, and x/p^v.", valuation);
    it.def("Valuation", "x::FldRatElt, I::RngInt -> RngIntElt, FldRatElt", "The valuation v of x at the prime ideal I = pZ, and x/p^v.", valuation_ideal);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn z(n: i64) -> Integer {
        Integer::from_i64(n)
    }

    fn q(n: i64, d: i64) -> Rational {
        Rational::new(&z(n), &z(d)).unwrap()
    }

    fn zs(v: &[i64]) -> Vec<Integer> {
        v.iter().map(|&c| z(c)).collect()
    }

    #[test]
    fn continued_fractions_round_trip() {
        for d in 1..=40 {
            for n in -80..=80 {
                let x = q(n, d);
                let cf = continued_fraction(&x);
                assert!(cf[1..].iter().all(|c| c.sign() > 0) && (cf.len() == 1 || cf[cf.len() - 1] > z(1)), "{x}: {cf:?}");
                assert_eq!(continued_fraction_value(&cf, 1), Some(x.clone()));
                let hj = hj_continued_fraction(&x);
                assert!(hj[1..].iter().all(|c| c > &z(1)), "{x}: {hj:?}");
                assert_eq!(continued_fraction_value(&hj, -1), Some(x));
            }
        }
        assert_eq!(continued_fraction(&q(355, 113)), zs(&[3, 7, 16]));
        assert_eq!(continued_fraction(&q(-355, 113)), zs(&[-4, 1, 6, 16]));
        assert_eq!(hj_continued_fraction(&q(10, 7)), zs(&[2, 2, 4]));
        assert_eq!(hj_continued_fraction(&q(-7, 3)), zs(&[-2, 3]));
        assert_eq!(continued_fraction_value(&zs(&[2, -3, 4]), 1), Some(q(18, 11)));
        assert_eq!(continued_fraction_value(&zs(&[1, 0]), 1), None);
        assert_eq!(continued_fraction_value(&zs(&[2, 1, 1]), -1), None);
        assert_eq!(continued_fraction_value(&[], 1), None);
    }

    #[test]
    fn qround_takes_the_last_convergent() {
        let convergents = |x: &Rational| {
            let (mut p0, mut q0, mut p1, mut q1) = (z(0), z(1), z(1), z(0));
            let mut out = Vec::new();
            for a in continued_fraction(x) {
                (p0, q0, p1, q1) = (p1.clone(), q1.clone(), &(&a * &p1) + &p0, &(&a * &q1) + &q0);
                out.push(Rational::new(&p1, &q1).unwrap());
            }
            out
        };
        for m in 1..=12 {
            let mz = z(m);
            for d in 1..=30 {
                for n in -2 * d..=2 * d {
                    let x = q(n, d);
                    let a0 = Rational::from_integer(&x.floor());
                    // The one exception: a0 + 1/M for a0 + 1/(M+1).
                    let want = if x == &a0 + &q(1, m + 1) {
                        &a0 + &q(1, m)
                    } else {
                        convergents(&x).into_iter().filter(|c| c.denominator() <= mz).last().unwrap()
                    };
                    assert_eq!(qround_cf(&x, &mz).unwrap(), want, "Qround({x}, {m} : ContFrac)");
                    let c = qround_ceiling(&x, &mz);
                    assert!(c >= x && &c - &x < q(1, m) && (&c * &Rational::from_integer(&mz)).is_integral(), "Qround({x}, {m})");
                }
            }
        }
        assert_eq!(qround_cf(&q(355, 113), &z(100)).unwrap(), q(22, 7));
        assert_eq!(qround_cf(&q(1, 101), &z(100)).unwrap(), q(1, 100));
        assert_eq!(qround_cf(&q(2, 7), &z(0)).unwrap(), q(2, 7));
        assert_eq!(qround_ceiling(&q(-355, 113), &z(10)), q(-31, 10));
    }

    #[test]
    fn rational_reconstruction_by_brute_force() {
        for m in 1..=150i64 {
            let b = (0..).take_while(|b| 2 * b * b <= m).last().unwrap();
            for s in 0..m {
                // Every n/d in lowest terms with |n|, d <= b and n = s*d mod m.
                let all: Vec<Rational> = (1..=b)
                    .flat_map(|d| (-b..=b).map(move |n| (n, d)))
                    .filter(|&(n, d)| z(n).gcd(&z(d)).is_one() && (n - s * d).rem_euclid(m) == 0)
                    .map(|(n, d)| q(n, d))
                    .collect();
                let got = rational_reconstruction(&z(s), &z(m));
                assert_eq!(got.is_some(), !all.is_empty(), "{s} mod {m}");
                if let Some(r) = got {
                    assert!(all.contains(&r) && (all.len() == 1 || 2 * b * b == m), "{s} mod {m}: {r} from {all:?}");
                }
            }
        }
        // On large moduli FLINT's reconstruction agrees with the Euclidean one.
        let m = &z(1).mul_2exp(100) + &z(277);
        let bound = m.fdiv_2exp(1).isqrt().unwrap();
        for k in 1..=300 {
            let (n, d) = (z(k * 7919 - 1_000_000), z(k * 104729 + 1));
            let s = match d.invmod(&m) {
                Some(i) => &n * &i,
                None => continue,
            };
            let near = &s + &z(k);
            for s in [&s, &near] {
                assert_eq!(Rational::reconstruct(s, &m, &bound), reconstruct_euclid(s, &m, &bound), "{s} mod {m}");
            }
            assert_eq!(rational_reconstruction(&s, &m), Rational::new(&n, &d));
        }
    }
}
