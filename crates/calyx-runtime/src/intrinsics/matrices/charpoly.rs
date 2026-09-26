//! Minimal and characteristic polynomials and eigenvalues: FLINT's
//! characteristic and minimal polynomials as polynomials in the global
//! polynomial ring over the coefficient ring, their factorizations by
//! `Factorization`, the eigenvalues from the roots of the characteristic
//! polynomial, and the eigenspaces as kernels.

use std::rc::Rc;

use calyx_flint::gr::{CtxKind, Elem};
use calyx_flint::mat::Mat;

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
fn polynomial(it: &mut Interp, x: &Mtrx, cs: &[Elem]) -> RResult<Value> {
    let ring = x.ring().clone();
    let Value::Struct(st) = it.poly_ring(&ring, true)? else { unreachable!("a polynomial ring") };
    let StructKind::Ring(r) = &st.kind else { unreachable!("a polynomial ring") };
    Ok(make_elt(&st, Elem::poly_from_coeffs(&r.ctx, cs).map_err(gr)?))
}

fn charpoly(it: &mut Interp, x: &Mtrx) -> RResult<Value> {
    let cs = x.m.charpoly().map_err(gr)?;
    polynomial(it, x, &cs)
}

fn minpoly(it: &mut Interp, x: &Mtrx) -> RResult<Value> {
    z_or_exact_field(x)?;
    let cs = x.m.minpoly().map_err(gr)?;
    polynomial(it, x, &cs)
}

fn factorization(it: &mut Interp, p: Value) -> RResult<Value> {
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
