//! Minimal and characteristic polynomials and eigenvalues: FLINT's
//! characteristic and minimal polynomials as polynomials in the global
//! polynomial ring over the coefficient ring, their factorizations by
//! `Factorization`, the eigenvalues from the roots of the characteristic
//! polynomial, and the eigenspaces as kernels.
//!
//! Over the rationals the characteristic polynomial of a matrix whose
//! minimal polynomial has smaller degree comes from the factors of that
//! (`rational_charpoly`): FLINT's own takes long when the entries are large.

use std::rc::Rc;

use calyx_flint::gr::{Ctx, CtxKind, Elem, Truth};
use calyx_flint::mat::Mat;
use calyx_flint::{Integer, upoly};

use super::linalg::{check_params, gr, kernel_space, with_types};
use super::{Mtrx, scalar, square};
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::one;
use crate::interp::{CallArgs, Interp};
use crate::rings::make_elt;
use crate::sym::Sym;
use crate::value::*;

fn charpoly_params() -> [(&'static str, Value); 2] {
    [("Al", Value::str("Modular")), ("Proof", Value::Bool(true))]
}

const CHARPOLY_ALS: &[&str] = &["Modular", "Hessenberg", "Interpolation", "Trace"];

/// `MinimalPolynomial` takes an `Al` its documentation leaves out; Magma
/// accepts these two.
fn minpoly_params() -> [(&'static str, Value); 2] {
    [("Al", Value::str("Default")), ("Proof", Value::Bool(true))]
}

const MINPOLY_ALS: &[&str] = &["Default", "KellerGehrig"];

fn proof_params() -> [(&'static str, Value); 1] {
    [("Proof", Value::Bool(true))]
}

/// The rings the algorithms of `CharacteristicPolynomial` work over; they
/// all give the same polynomial.
fn algorithm_ring(x: &Mtrx, a: &CallArgs) -> RResult<()> {
    match a.param("Al") {
        Some(Value::Str(s)) if s.as_str() == "Hessenberg" && !x.m.over_field() => Err(RuntimeError::runtime("Coefficient ring must be a field")),
        Some(Value::Str(s)) if s.as_str() == "Interpolation" && !matches!(x.m.ctx().kind(), CtxKind::Integers | CtxKind::Rationals) => {
            Err(RuntimeError::runtime("Coefficient ring must be Z or Q"))
        }
        _ => Ok(()),
    }
}

/// Minimal polynomials are over the integers or an exact field.
fn z_or_exact_field(x: &Mtrx) -> RResult<()> {
    if matches!(x.m.ctx().kind(), CtxKind::Integers) || (x.m.over_field() && !x.m.floating()) {
        return Ok(());
    }
    Err(RuntimeError::runtime("Coefficient ring must be Z or an exact field"))
}

/// The polynomial with coefficients `cs` (constant term first) in the
/// global polynomial ring over the ring of `x`.
pub(super) fn polynomial(it: &mut Interp, x: &Mtrx, cs: &[Elem]) -> RResult<Value> {
    let ring = x.ring().clone();
    let Value::Struct(st) = it.poly_ring(&ring, true)? else { unreachable!("a polynomial ring") };
    let StructKind::Ring(r) = &st.kind else { unreachable!("a polynomial ring") };
    Ok(make_elt(&st, Elem::poly_from_coeffs(&r.ctx, cs).map_err(gr)?))
}

pub(super) fn charpoly(it: &mut Interp, x: &Mtrx) -> RResult<Value> {
    let cs = match x.m.ctx().kind() {
        CtxKind::Rationals => rational_charpoly(&x.m)?,
        _ => None,
    };
    let cs = match cs {
        Some(cs) => cs,
        None => x.m.charpoly().map_err(gr)?,
    };
    polynomial(it, x, &cs)
}

/// Primes just below 2^62, for computing modulo a prime.
pub(super) fn large_primes() -> impl Iterator<Item = Integer> {
    std::iter::successors(Integer::from_u64(1 << 62).previous_prime(), |p| p.previous_prime())
}

/// q(A) for the polynomial q with the coefficients `cs` (the constant term
/// first) over the ring of A, by Horner's rule.
pub(super) fn eval_coeffs(a: &Mat, cs: &[Elem]) -> RResult<Mat> {
    let n = a.nrows();
    let add_scalar = |r: &mut Mat, c: &Elem| -> RResult<()> {
        if c.is_zero() != Truth::True {
            for i in 0..n {
                let x = r.entry(i, i).add(c).map_err(gr)?;
                r.set_entry(i, i, &x);
            }
        }
        Ok(())
    };
    let Some((lead, rest)) = cs.split_last() else { return Ok(Mat::zero(a.ctx(), n, n)) };
    let Some((next, rest)) = rest.split_last() else { return Mat::scalar(n, lead).map_err(gr) };
    let mut r = if lead.is_one() == Truth::True { a.clone() } else { a.mul_scalar(lead).map_err(gr)? };
    add_scalar(&mut r, next)?;
    for c in rest.iter().rev() {
        r = r.mul(a).map_err(gr)?;
        add_scalar(&mut r, c)?;
    }
    Ok(r)
}

/// The multiplicities in the characteristic polynomial of a matrix over the
/// rationals of the irreducible factors q of its minimal polynomial, given
/// with their exponents e there: dim ker q(A)^e / deg q. Modulo a prime the
/// kernels can only be larger, and the true ones add up to n, so they are
/// right when they add up to n; None if no prime tried gives that.
pub(super) fn modular_multiplicities(a: &Mat, factors: &[(Elem, usize)]) -> RResult<Option<Vec<usize>>> {
    let n = a.nrows();
    'primes: for p in large_primes().take(3) {
        let ctx = Ctx::residue_ring(&p);
        let Ok(ap) = a.change_ring(&ctx) else { continue };
        let (mut ms, mut total) = (Vec::with_capacity(factors.len()), 0);
        for (q, e) in factors {
            let Ok(cs) = (0..q.poly_len()).map(|i| Elem::from_other(&ctx, &q.poly_coeff(i))).collect::<Result<Vec<_>, _>>() else { continue 'primes };
            let power = eval_coeffs(&ap, &cs)?.pow(&Integer::from_u64(*e as u64)).map_err(gr)?;
            let dim = n - power.rank().map_err(gr)?;
            total += dim;
            ms.push(dim / (cs.len() - 1));
        }
        if total == n {
            return Ok(Some(ms));
        }
    }
    Ok(None)
}

/// The characteristic polynomial of a matrix over the rationals whose
/// minimal polynomial modulo a prime has degree less than n (so that it is
/// not cyclic, most likely): the product of the factors q^e of the minimal
/// polynomial, each raised to its multiplicity. None to leave it to FLINT.
fn rational_charpoly(m: &Mat) -> RResult<Option<Vec<Elem>>> {
    let n = m.nrows();
    let p = large_primes().next().expect("a prime below 2^62");
    match m.change_ring(&Ctx::residue_ring(&p)) {
        Ok(mp) if mp.minpoly().map_err(gr)?.len() <= n => {}
        _ => return Ok(None),
    }
    let cs = m.minpoly().map_err(gr)?;
    if cs.len() == n + 1 {
        return Ok(Some(cs));
    }
    let px = Ctx::poly(m.ctx());
    let f = Elem::poly_from_coeffs(&px, &cs).map_err(gr)?;
    let factors: Vec<(Elem, usize)> = upoly::factor(&f).map_err(gr)?.factors.into_iter().map(|(q, e)| (q, e as usize)).collect();
    let Some(ms) = modular_multiplicities(m, &factors)? else { return Ok(None) };
    let mut c = Elem::one(&px).map_err(gr)?;
    for ((q, _), k) in factors.iter().zip(ms) {
        c = c.mul(&q.pow_i64(k as i64).map_err(gr)?).map_err(gr)?;
    }
    Ok(Some((0..c.poly_len()).map(|i| c.poly_coeff(i)).collect()))
}

fn minpoly(it: &mut Interp, x: &Mtrx) -> RResult<Value> {
    z_or_exact_field(x)?;
    let cs = x.m.minpoly().map_err(gr)?;
    polynomial(it, x, &cs)
}

pub(super) fn factorization(it: &mut Interp, p: Value) -> RResult<Value> {
    it.call_intrinsic_named(Sym::new("Factorization"), vec![p])
}

fn characteristic_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &charpoly_params(), CHARPOLY_ALS)?;
    let x = square(a, 0)?;
    algorithm_ring(&x, a)?;
    one(charpoly(it, &x)?)
}

fn minimal_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &minpoly_params(), MINPOLY_ALS)?;
    let x = square(a, 0)?;
    one(minpoly(it, &x)?)
}

fn mc_polynomials(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &proof_params(), &[])?;
    let x = square(a, 0)?;
    let m = minpoly(it, &x)?;
    Ok(vals![m, charpoly(it, &x)?])
}

fn factored_characteristic_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &charpoly_params(), CHARPOLY_ALS)?;
    let x = square(a, 0)?;
    algorithm_ring(&x, a)?;
    let ring = x.ring().clone();
    if !matches!(it.call_intrinsic_named(Sym::new("HasPolynomialFactorization"), vec![ring])?, Value::Bool(true)) {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 does not have a polynomial factorization algorithm"));
    }
    let c = charpoly(it, &x)?;
    one(factorization(it, c)?)
}

fn factored_minimal_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &proof_params(), &[])?;
    let x = square(a, 0)?;
    let m = minpoly(it, &x)?;
    one(factorization(it, m)?)
}

fn factored_mc_polynomials(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &proof_params(), &[])?;
    let x = square(a, 0)?;
    let m = minpoly(it, &x)?;
    let c = charpoly(it, &x)?;
    Ok(vals![factorization(it, m)?, factorization(it, c)?])
}

/// `Eigenvalues(A)`: the roots of the characteristic polynomial in the
/// coefficient ring, as a set of pairs <e, k> of an eigenvalue and its
/// multiplicity.
fn eigenvalues(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    if matches!(x.m.ctx().kind(), CtxKind::Nmod(_) | CtxKind::FmpzMod(_)) && !x.m.over_field() {
        return Err(RuntimeError::runtime("Coefficient ring does not have a roots algorithm"));
    }
    let c = charpoly(it, &x)?;
    let Value::Seq(roots) = it.call_intrinsic_named(Sym::new("Roots"), vec![c])? else { unreachable!("a sequence of roots") };
    let pairs = Value::structure(StructKind::Cartesian(vec![x.ring().clone(), Value::integers()]));
    let mut set: VSet = roots
        .elems
        .iter()
        .map(|r| {
            let Value::Tuple(t) = r else { unreachable!("a root and its multiplicity") };
            Value::Tuple(Rc::new(Tuple { elems: t.elems.clone(), parent: Some(pairs.clone()) }))
        })
        .collect();
    sort_value_set(&mut set);
    one(Value::Set(Rc::new(SetEnum::new(Some(pairs), set))))
}

/// `Eigenspace(A, e)`: the kernel of A - e, for e in the coefficient ring.
fn eigenspace(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    let ring = x.ring().clone();
    let Some(e) = scalar(it, &ring, x.m.ctx(), &a.args[1])? else {
        return Err(with_types(it, a, "Arguments are not compatible"));
    };
    let m = x.m.sub(&Mat::scalar(x.m.nrows(), &e).map_err(gr)?).map_err(gr)?;
    one(kernel_space(it, &Mtrx { parent: x.parent.clone(), m })?)
}

pub fn register(it: &mut Interp) {
    // Not for vectors, as in Magma.
    for ty in ["AlgMatElt", "ModMatRngElt"] {
        let (charpoly, minpoly, proof) = (charpoly_params(), minpoly_params(), proof_params());
        let sig = |r: &str| format!("A::{ty} -> {r}");
        it.def_params("CharacteristicPolynomial", &sig("RngUPolElt"), &charpoly, "The characteristic polynomial of A.", characteristic_polynomial);
        it.def_params("MinimalPolynomial", &sig("RngUPolElt"), &minpoly, "The minimal polynomial of A.", minimal_polynomial);
        for name in ["MinimalAndCharacteristicPolynomials", "MCPolynomials"] {
            it.def_params(name, &sig("RngUPolElt, RngUPolElt"), &proof, "The minimal and characteristic polynomials of A.", mc_polynomials);
        }
        let doc = "The factorization of the characteristic polynomial of A.";
        it.def_params("FactoredCharacteristicPolynomial", &sig("[Tup]"), &charpoly, doc, factored_characteristic_polynomial);
        let doc = "The factorization of the minimal polynomial of A.";
        it.def_params("FactoredMinimalPolynomial", &sig("[Tup]"), &proof, doc, factored_minimal_polynomial);
        let doc = "The factorizations of the minimal and characteristic polynomials of A.";
        for name in ["FactoredMinimalAndCharacteristicPolynomials", "FactoredMCPolynomials"] {
            it.def_params(name, &sig("[Tup], [Tup]"), &proof, doc, factored_mc_polynomials);
        }
    }
    it.def("Eigenvalues", "A::Mtrx -> SetEnum", "The eigenvalues of A in its coefficient ring, with their multiplicities.", eigenvalues);
    it.def("Eigenspace", "A::Mtrx, e::RngElt -> ModTupRng", "The eigenspace of A for e, the kernel of A - e.", eigenspace);
}
