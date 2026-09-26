//! Vector spaces (#78): spaces with an inner product matrix, inner
//! products and norms of vectors, and the basis vectors `V.i`.
//!
//! A full R-space may carry an inner product matrix F (`VectorSpace(K, n,
//! F)`), which its subspaces share; an identity F gives the plain space.
//! The spaces with a form are made once for each ring and matrix, as in
//! Magma, so attributes set on one (the `Involution` of a hermitian form)
//! are seen through all of its handles. Over a field the form is also the
//! attribute `ip_form`.

use std::cell::RefCell;
use std::rc::Rc;

use calyx_flint::gr::{CtxKind, Truth};
use calyx_flint::mat::Mat;

use super::linalg::{gr, with_types};
use super::spaces::generic;
use super::{MatParent, Mtrx, Shape, entry_of, info, mat_value, parent};
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::{arg_ge, one};
use crate::interp::{CallArgs, Interp};
use crate::rings::structure_key;
use crate::sym::Sym;
use crate::types::t;
use crate::value::*;

thread_local! {
    /// The spaces with an inner product matrix made so far, by ring.
    static FORM_SPACES: RefCell<Vec<(String, Rc<Struct>)>> = RefCell::default();
}

/// The full R-space over `ring` with the inner product matrix `f` (square,
/// over the ring): the plain space when `f` is the identity.
pub fn form_space(it: &mut Interp, ring: &Value, f: Mat) -> RResult<Rc<Struct>> {
    let n = f.nrows();
    let plain = parent(it, ring, 1, n, Shape::Tuples)?;
    if f.is_one() == Truth::True {
        return Ok(plain);
    }
    let key = structure_key(ring);
    if let Some(k) = &key {
        let same = |st: &Rc<Struct>| info(st).ncols == n && info(st).form.as_ref().is_some_and(|g| g.equal(&f) == Truth::True);
        if let Some(st) = FORM_SPACES.with(|c| c.borrow().iter().find(|(r, st)| r == k && same(st)).map(|(_, st)| st.clone())) {
            return Ok(st);
        }
    }
    let mp = info(&plain);
    let (field, ctx) = (mp.field, mp.ctx.clone());
    let p = MatParent { ring: ring.clone(), nrows: 1, ncols: n, shape: Shape::Tuples, field, ctx, sub: None, form: Some(f.clone()) };
    let st = Struct::new(StructKind::Matrices(Rc::new(p)));
    if field {
        let v = mat_value(it, ring, f)?;
        st.attrs.borrow_mut().insert(Sym::new("ip_form"), v);
    }
    if let Some(k) = key {
        FORM_SPACES.with(|c| c.borrow_mut().push((k, st.clone())));
    }
    Ok(st)
}

/// The inner product matrix of an R-space (that of its full space), None
/// for the identity.
pub fn inner_product_matrix(st: &Rc<Struct>) -> Option<Mat> {
    info(&generic(st)).form.clone()
}

fn space_arg(a: &CallArgs, i: usize) -> RResult<Rc<Struct>> {
    match &a.args[i] {
        Value::Struct(st) if matches!(st.kind, StructKind::Matrices(_)) => Ok(st.clone()),
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
}

fn vector_arg(a: &CallArgs, i: usize) -> RResult<Rc<Mtrx>> {
    match &a.args[i] {
        Value::Mat(x) if x.is_vector() => Ok(x.clone()),
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
}

/// `VectorSpace(K, n, F)`, `KSpace(K, n, F)` and `RSpace(R, n, F)`: the
/// full space with the inner product matrix F, an n by n matrix over the
/// ring.
fn space_with_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = a.args[0].clone();
    let n = a.int(1)?.clone();
    if n.sign() < 0 {
        return Err(arg_ge(2, &n, 1));
    }
    let Value::Mat(f) = &a.args[2] else { return Err(RuntimeError::runtime("Bad argument types")) };
    if f.is_vector() || n.to_u64() != Some(f.m.nrows() as u64) || f.m.nrows() != f.m.ncols() {
        return Err(RuntimeError::runtime("Arguments have incompatible degrees"));
    }
    if f.ring() != &ring {
        return Err(RuntimeError::runtime("Arguments have incompatible coefficient rings"));
    }
    let m = f.m.clone();
    one(Value::Struct(form_space(it, &ring, m)?))
}

/// `InnerProductMatrix(V)`: the inner product matrix of the full space of V.
fn inner_product_matrix_of(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = space_arg(a, 0)?;
    let mp = info(&st);
    let m = match inner_product_matrix(&st) {
        Some(f) => f,
        None => Mat::identity(&mp.ctx, mp.ncols).map_err(gr)?,
    };
    let ring = mp.ring.clone();
    one(mat_value(it, &ring, m)?)
}

/// u·F·v^tr for the form F of the space of u, with v conjugated over the
/// complex field.
fn inner_product(it: &mut Interp, a: &CallArgs, u: &Mtrx, v: &Mtrx) -> RResult<Value> {
    if u.ring() != v.ring() {
        return Err(with_types(it, a, "Bad argument types"));
    }
    if u.m.ncols() != v.m.ncols() {
        return Err(with_types(it, a, "Arguments are not compatible"));
    }
    let mut w = v.m.clone();
    if matches!(w.ctx().kind(), CtxKind::ComplexFloat(_)) {
        for j in 0..w.ncols() {
            let c = w.entry(0, j).conj().map_err(gr)?;
            w.set_entry(0, j, &c);
        }
    }
    let x = match inner_product_matrix(&u.parent) {
        Some(f) => u.m.mul(&f).map_err(gr)?,
        None => u.m.clone(),
    };
    let r = x.mul(&w.transpose()).map_err(gr)?;
    Ok(entry_of(it, u.ring(), &r, 0, 0))
}

fn inner_product_intrinsic(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (u, v) = (vector_arg(a, 0)?, vector_arg(a, 1)?);
    one(inner_product(it, a, &u, &v)?)
}

fn norm(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let u = vector_arg(a, 0)?;
    one(inner_product(it, a, &u, &u)?)
}

/// `V.i`: the i-th basis vector of V.
fn basis_vector(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = space_arg(a, 0)?;
    let mp = info(&st);
    let d = mp.dimension();
    let i = a.int(1)?;
    let Some(i) = i.to_u64().filter(|&i| i >= 1 && i as usize <= d).map(|i| i as usize - 1) else {
        return Err(RuntimeError::runtime(format!("Argument 2 ({i}) should be in the range [1 .. {d}]")));
    };
    let m = match &mp.sub {
        Some(s) => s.basis.block(i, 0, 1, mp.ncols),
        None => {
            let mut m = Mat::zero(&mp.ctx, 1, mp.ncols);
            m.set_entry(0, i, &calyx_flint::gr::Elem::one(&mp.ctx).map_err(gr)?);
            m
        }
    };
    one(Value::Mat(Rc::new(Mtrx { parent: st.clone(), m })))
}

pub fn register(it: &mut Interp) {
    for name in ["VectorSpace", "KSpace"] {
        it.def(name, "K::Fld, n::RngIntElt, F::Mtrx -> ModTupFld", "The full vector space of degree n over K with the inner product matrix F.", space_with_form);
    }
    it.def("RSpace", "R::Rng, n::RngIntElt, F::Mtrx -> ModTupRng", "The full R-space of degree n with the inner product matrix F.", space_with_form);
    it.def("InnerProductMatrix", "V::ModTupRng -> AlgMatElt", "The inner product matrix of V.", inner_product_matrix_of);
    it.def("InnerProduct", "u::ModTupRngElt, v::ModTupRngElt -> RngElt", "The inner product u·F·v^tr for the inner product matrix F of the space of u.", inner_product_intrinsic);
    it.def("Norm", "u::ModTupRngElt -> RngElt", "The norm u·F·u^tr for the inner product matrix F of the space of u.", norm);
    it.def(".", "V::ModTupRng, i::RngIntElt -> ModTupRngElt", "The i-th basis vector of V.", basis_vector);
    // Hermitian forms keep the involution of the field on the space.
    for name in ["ip_form", "Involution"] {
        it.types.add_attribute(t::MOD_TUP_FLD, Sym::new(name));
    }
}
