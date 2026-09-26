//! Orders of invertible matrices, found factored:
//!
//! - over a finite field of order q and characteristic p, from the
//!   minimal polynomial: the order of x modulo an irreducible factor f
//!   divides q^deg(f) - 1 (factorized like any such number, with the
//!   Cunningham tables), and a factor with exponent e adds the least power
//!   of p at least e;
//! - over the integers and the rationals, where the order is finite when
//!   the minimal polynomial is a product of distinct cyclotomic
//!   polynomials, the least common multiple of their indices;
//! - over Z/nZ, from the order modulo each prime p of n and the power of p
//!   that lifts it to p^e;
//! - over other rings by multiplying until the identity, which, as in
//!   Magma, goes on until interrupted when the order is infinite.
//!
//! The projective order divides the order, which leaves only its primes to
//! try.
//!
//! Magma returns true as a second value (a third for the projective
//! orders); a call statement prints it only when Proof is false.

use calyx_flint::gr::{Ctx, CtxKind, Elem, Truth};
use calyx_flint::mat::Mat;
use calyx_flint::{Integer, upoly};

use super::linalg::{check_params, gr, modulus, residues};
use super::{Mtrx, entry_of, square};
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::factseq::{self, Fact, fact_int};
use crate::intrinsics::boolv;
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn proof_params() -> [(&'static str, Value); 1] {
    [("Proof", Value::Bool(true))]
}

fn not_invertible() -> RuntimeError {
    RuntimeError::runtime("Argument 1 is not invertible")
}

fn infinite() -> RuntimeError {
    RuntimeError::runtime("Argument 1 has infinite order")
}

/// The rings orders are found over.
enum Kind {
    /// A finite field of order q and characteristic p.
    FiniteField { q: Integer, p: Integer },
    /// The integers or the rationals.
    Rational,
    /// Z/nZ.
    Residue,
    Other,
}

fn kind(x: &Mtrx) -> Kind {
    let ctx = x.m.ctx();
    let p = match ctx.kind() {
        CtxKind::Integers | CtxKind::Rationals => return Kind::Rational,
        CtxKind::Nmod(_) | CtxKind::FmpzMod(_) if !x.info().field => return Kind::Residue,
        CtxKind::Nmod(p) | CtxKind::FqZech { p, .. } | CtxKind::FqNmod { p, .. } | CtxKind::FqPacked { p, .. } => Integer::from_u64(*p),
        CtxKind::FmpzMod(p) | CtxKind::Fq { p, .. } => p.clone(),
        _ => return Kind::Other,
    };
    let q = ctx.fq_order().unwrap_or_else(|| p.clone());
    Kind::FiniteField { q, p }
}

/// The factorization of lcm(a, b) from theirs.
fn lcm(a: &Fact, b: &Fact) -> Fact {
    let mut out: Fact = a.clone();
    for (r, k) in b {
        match out.iter_mut().find(|(s, _)| s == r) {
            Some((_, j)) => *j = (*j).max(*k),
            None => out.push((r.clone(), *k)),
        }
    }
    out.sort();
    out
}

/// The minimal polynomial of a square matrix over a finite field (asking
/// `over_field` first tells FLINT that a large modulus is prime).
fn minimal_polynomial(m: &Mat) -> RResult<Elem> {
    if !m.over_field() {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a finite field"));
    }
    let cs = m.minpoly().map_err(gr)?;
    Elem::poly_from_coeffs(&Ctx::poly(m.ctx()), &cs).map_err(gr)
}

fn is_one(f: &Elem) -> bool {
    f.is_one() == Truth::True
}

/// The powers y^(N/m) for the pairwise coprime m of `ms`, N their product,
/// modulo f: raising y to the product of one half of them gives the powers
/// for the other half.
fn cofactor_powers(y: &Elem, ms: &[Integer], f: &Elem, out: &mut Vec<Elem>) -> RResult<()> {
    if ms.len() <= 1 {
        out.extend(ms.iter().map(|_| y.clone()));
        return Ok(());
    }
    let (l, r) = ms.split_at(ms.len() / 2);
    let product = |xs: &[Integer]| xs.iter().fold(Integer::one(), |a, b| &a * b);
    cofactor_powers(&upoly::powmod(y, &product(r), f).map_err(gr)?, l, f, out)?;
    cofactor_powers(&upoly::powmod(y, &product(l), f).map_err(gr)?, r, f, out)
}

/// The least n dividing N, factored as `multiple`, for which x^n modulo f
/// passes `done` (a test that holds for all multiples of that n): the
/// power of each prime r^k of N in n is the least r^j for which
/// (x^(N/r^k))^(r^j) passes.
fn least_exponent(f: &Elem, multiple: &Fact, done: impl Fn(&Elem) -> bool) -> RResult<Fact> {
    let x = upoly::divrem(&f.ctx().generator().map_err(gr)?, f).map_err(gr)?.1;
    let pps: Vec<Integer> = multiple.iter().map(|(r, k)| r.pow(*k)).collect();
    let mut zs = Vec::with_capacity(pps.len());
    cofactor_powers(&x, &pps, f, &mut zs)?;
    let mut out = Fact::new();
    for ((r, k), mut z) in multiple.iter().zip(zs) {
        let mut j = 0;
        while j < *k && !done(&z) {
            z = upoly::powmod(&z, r, f).map_err(gr)?;
            j += 1;
        }
        if j > 0 {
            out.push((r.clone(), j));
        }
    }
    Ok(out)
}

/// The factored order of x in F[x]/(mu), for a polynomial mu over the
/// finite field F of order q and characteristic p with mu(0) nonzero.
fn field_order(it: &mut Interp, mu: &Elem, q: &Integer, p: &Integer) -> RResult<Fact> {
    let fac = upoly::factor(mu).map_err(gr)?;
    let mut groups: Vec<(u64, Fact)> = Vec::new();
    let (mut order, mut e) = (Fact::new(), 1);
    for (f, k) in &fac.factors {
        e = e.max(*k);
        let d = f.poly_len() as u64 - 1;
        let at = match groups.iter().position(|(c, _)| *c == d) {
            Some(i) => i,
            None => {
                groups.push((d, it.factor_int(&(&q.pow(d) - &Integer::one()))));
                groups.len() - 1
            }
        };
        order = lcm(&order, &least_exponent(f, &groups[at].1, is_one)?);
    }
    // x^(p^j) - c^(p^j) = (x - c)^(p^j) kills the exponents up to p^j.
    let (mut pj, mut j) = (Integer::one(), 0);
    while pj < Integer::from_u64(e) {
        pj = &pj * p;
        j += 1;
    }
    Ok(if j > 0 { lcm(&order, &vec![(p.clone(), j)]) } else { order })
}

/// The factored order of an invertible matrix over a finite field.
fn finite_field_order(it: &mut Interp, m: &Mat, q: &Integer, p: &Integer) -> RResult<Fact> {
    let mu = minimal_polynomial(m)?;
    if mu.poly_coeff(0).is_zero() == Truth::True {
        return Err(not_invertible());
    }
    field_order(it, &mu, q, p)
}

/// The factored order of a matrix over the integers or the rationals, None
/// if it is infinite.
fn rational_order(m: &Mat) -> RResult<Option<Fact>> {
    let cs = m.minpoly().map_err(gr)?;
    if cs[0].is_zero() == Truth::True {
        return Err(not_invertible());
    }
    let mut ints = Vec::with_capacity(cs.len());
    for c in &cs {
        match c.to_rational().map_err(gr)? {
            r if r.denominator().is_one() => ints.push(Elem::from_integer(&Ctx::integers(), &r.numerator()).map_err(gr)?),
            _ => return Ok(None),
        }
    }
    let mu = Elem::poly_from_coeffs(&Ctx::poly(&Ctx::integers()), &ints).map_err(gr)?;
    let mut order = Fact::new();
    for (f, k) in upoly::factor(&mu).map_err(gr)?.factors {
        let n = upoly::cyclotomic_index(&f);
        if k > 1 || n == 0 {
            return Ok(None);
        }
        order = lcm(&order, &factseq::factor(&Integer::from_u64(n)));
    }
    Ok(Some(order))
}

/// The factored order of a matrix over Z/nZ: modulo each prime power p^e
/// of n, the order t modulo p times the least p^j with (A^t)^(p^j) = 1
/// modulo p^e.
fn residue_order(it: &mut Interp, m: &Mat) -> RResult<Fact> {
    let n = modulus(m);
    let mut lift = Mat::zero(&Ctx::integers(), m.nrows(), m.ncols());
    for (i, row) in residues(m).iter().enumerate() {
        for (j, x) in row.iter().enumerate() {
            lift.set_integer(i, j, x).map_err(gr)?;
        }
    }
    let det = lift.det().map_err(gr)?.to_integer().map_err(gr)?;
    if det.fdiv_qr(&n).expect("a nonzero modulus").1.is_zero() {
        return Err(not_invertible());
    }
    if !det.gcd(&n).is_one() {
        return Err(infinite());
    }
    let mut order = Fact::new();
    for (p, e) in factseq::factor(&n) {
        let mp = lift.change_ring(&Ctx::residue_ring(&p)).map_err(gr)?;
        let mut t = finite_field_order(it, &mp, &p, &p)?;
        if e > 1 {
            let mut b = lift.change_ring(&Ctx::residue_ring(&p.pow(e))).map_err(gr)?.pow(&fact_int(&t)).map_err(gr)?;
            let mut j = 0;
            while j < e && b.is_one() != Truth::True {
                b = b.pow(&p).map_err(gr)?;
                j += 1;
            }
            if j > 0 {
                t = factseq::fact_mul(&t, &vec![(p.clone(), j)])?;
            }
        }
        order = lcm(&order, &t);
    }
    Ok(order)
}

/// Whether `d` is not known not to be a unit: a polynomial must be a
/// constant one (FLINT cannot tell for some polynomial rings).
fn may_be_unit(d: &Elem) -> bool {
    let c = match d.ctx().kind() {
        CtxKind::Poly if d.poly_len() != 1 => return false,
        CtxKind::Poly => d.poly_coeff(0),
        CtxKind::MPoly { .. } => match d.mpoly_len() {
            1 => match d.mpoly_term(0) {
                (c, e) if e.iter().all(|&k| k == 0) => c,
                _ => return false,
            },
            _ => return false,
        },
        _ => d.clone(),
    };
    c.is_invertible() != Truth::False
}

/// The order of a matrix over another ring, by multiplying until the
/// identity.
fn order_by_powers(it: &mut Interp, m: &Mat) -> RResult<Integer> {
    if let Ok(d) = m.det() {
        if d.is_zero() == Truth::True {
            return Err(not_invertible());
        }
        if !may_be_unit(&d) {
            return Err(infinite());
        }
    }
    let (mut power, mut k) = (m.clone(), 1u64);
    while power.is_one() != Truth::True {
        it.check_interrupt()?;
        power = power.mul(m).map_err(gr)?;
        k += 1;
    }
    Ok(Integer::from_u64(k))
}

/// The factored order of a square matrix.
fn factored_order(it: &mut Interp, x: &Mtrx) -> RResult<Fact> {
    match kind(x) {
        Kind::FiniteField { q, p } => finite_field_order(it, &x.m, &q, &p),
        Kind::Rational => rational_order(&x.m)?.ok_or_else(infinite),
        Kind::Residue => residue_order(it, &x.m),
        Kind::Other => Ok(factseq::factor(&order_by_powers(it, &x.m)?)),
    }
}

/// The projective order of a matrix over a finite field, factored, and the
/// scalar it gives.
fn projective_order(it: &mut Interp, x: &Mtrx) -> RResult<(Fact, Value)> {
    let Kind::FiniteField { q, p } = kind(x) else {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a finite field"));
    };
    let mu = minimal_polynomial(&x.m)?;
    if mu.poly_coeff(0).is_zero() == Truth::True {
        return Err(not_invertible());
    }
    let mut scalar = Mat::identity(x.m.ctx(), 1).map_err(gr)?;
    let mut order = Fact::new();
    if mu.poly_len() > 1 {
        // Powers of x that are scalars modulo mu are those of the projective
        // order, which divides the order.
        order = least_exponent(&mu, &field_order(it, &mu, &q, &p)?, |z| z.poly_len() <= 1)?;
        let power = upoly::powmod(&mu.ctx().generator().map_err(gr)?, &fact_int(&order), &mu).map_err(gr)?;
        scalar.set_entry(0, 0, &power.poly_coeff(0));
    }
    let s = entry_of(it, x.ring(), &scalar, 0, 0);
    Ok((order, s))
}

/// The values after the order: the scalar of a projective order, then
/// true, which a call statement prints only when Proof is false.
fn with_proved(a: &CallArgs, mut out: Vals) -> RResult<Vals> {
    if a.nresults > out.len() || matches!(a.param("Proof"), Some(Value::Bool(false))) {
        out.push(Value::Bool(true));
    }
    Ok(out)
}

fn order(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &proof_params(), &[])?;
    let x = square(a, 0)?;
    let f = factored_order(it, &x)?;
    with_proved(a, vals![Value::Int(fact_int(&f))])
}

fn factored_order_intrinsic(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &proof_params(), &[])?;
    let x = square(a, 0)?;
    let f = factored_order(it, &x)?;
    with_proved(a, vals![factseq::fact_value(&f)])
}

fn projective_order_intrinsic(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &proof_params(), &[])?;
    let x = square(a, 0)?;
    let (f, s) = projective_order(it, &x)?;
    with_proved(a, vals![Value::Int(fact_int(&f)), s])
}

fn factored_projective_order(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &proof_params(), &[])?;
    let x = square(a, 0)?;
    let (f, s) = projective_order(it, &x)?;
    with_proved(a, vals![factseq::fact_value(&f), s])
}

/// `HasFiniteOrder(A)`: proven over finite fields (always true, as in
/// Magma, even for a singular matrix), Z/nZ (likewise), Z and Q.
fn has_finite_order(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    match kind(&x) {
        Kind::FiniteField { .. } | Kind::Residue => boolv(true),
        Kind::Rational => match rational_order(&x.m) {
            Ok(f) => boolv(f.is_some()),
            Err(_) => boolv(false),
        },
        Kind::Other => Err(RuntimeError::runtime("Argument 1 not known to have finite or infinite order")),
    }
}

pub fn register(it: &mut Interp) {
    it.def("HasFiniteOrder", "A::Mtrx -> BoolElt", "Whether the square matrix A has finite order.", has_finite_order);
    for ty in ["AlgMatElt", "ModMatRngElt"] {
        let (proof, sig) = (proof_params(), |r: &str| format!("A::{ty} -> {r}"));
        it.def_params("Order", &sig("RngIntElt, BoolElt"), &proof, "The order of the invertible matrix A.", order);
        it.def_params("FactoredOrder", &sig("RngIntEltFact, BoolElt"), &proof, "The factored order of the invertible matrix A.", factored_order_intrinsic);
        let doc = "The projective order n of the invertible matrix A over a finite field, and s with A^n = s.";
        it.def_params("ProjectiveOrder", &sig("RngIntElt, RngElt, BoolElt"), &proof, doc, projective_order_intrinsic);
        let doc = "The factored projective order n of the invertible matrix A over a finite field, and s with A^n = s.";
        it.def_params("FactoredProjectiveOrder", &sig("RngIntEltFact, RngElt, BoolElt"), &proof, doc, factored_projective_order);
    }
}
