//! Standard matrices for alternating, pseudo-alternating, hermitian,
//! quadratic and symmetric forms.  The space operations are below these as
//! their handbook sections are implemented.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Elem, Truth};
use calyx_flint::mat::Mat;

use super::one;
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::matrices::{MatParent, Mtrx, Shape, Sub};
use crate::rings::finite::field_struct;
use crate::rings::props::ring_props;
use crate::sym::Sym;
use crate::value::*;

fn bad() -> RuntimeError {
    RuntimeError::runtime("Bad argument types")
}

fn gr(e: calyx_flint::gr::GrError) -> RuntimeError {
    crate::rings::gr_error(e, "Arithmetic failed")
}

fn dim(a: &CallArgs) -> RResult<usize> {
    let n = a.int_ge(0, 0)?;
    n.to_u64().map(|n| n as usize).ok_or_else(|| RuntimeError::runtime(format!("Argument 1 ({n}) is too large")))
}

/// The explicit ring argument, or the finite field of the given order.
/// Hermitian forms interpret an integer q as GF(q^2).
fn ring_arg(it: &mut Interp, a: &CallArgs, hermitian: bool) -> RResult<(Value, Option<Integer>)> {
    match &a.args[1] {
        Value::Int(q) => {
            if q <= &Integer::one() {
                return Err(RuntimeError::runtime("Argument 2 must be a prime power greater than 1"));
            }
            let order = if hermitian { q * q } else { q.clone() };
            let field = it.call_intrinsic_named(Sym::new("GF"), vec![Value::Int(order)])?;
            Ok((field, hermitian.then(|| q.clone())))
        }
        Value::Struct(_) => Ok((a.args[1].clone(), None)),
        _ => Err(bad()),
    }
}

fn finite_field(ring: &Value) -> RResult<(Integer, Integer)> {
    let p = ring_props(ring).filter(|p| p.field).ok_or_else(bad)?;
    let q = p.cardinality.ok_or_else(bad)?;
    Ok((p.characteristic, q))
}

fn matrix(it: &mut Interp, ring: &Value, m: Mat) -> RResult<Value> {
    crate::intrinsics::matrices::mat_value(it, ring, m)
}

fn matrix_arg(a: &CallArgs, i: usize) -> RResult<Rc<Mtrx>> {
    match &a.args[i] {
        Value::Mat(m) if !m.is_vector() => Ok(m.clone()),
        _ => Err(bad()),
    }
}

fn vector_arg(a: &CallArgs, i: usize) -> RResult<Rc<Mtrx>> {
    match &a.args[i] {
        Value::Mat(v) if v.is_vector() => Ok(v.clone()),
        _ => Err(bad()),
    }
}

fn space_arg(a: &CallArgs, i: usize) -> RResult<Rc<Struct>> {
    match &a.args[i] {
        Value::Struct(st) if crate::intrinsics::matrices::is_rspace(&a.args[i]) => Ok(st.clone()),
        _ => Err(bad()),
    }
}

fn full_space(st: &Rc<Struct>) -> Rc<Struct> {
    crate::intrinsics::matrices::info(st).sub.as_ref().map_or_else(|| st.clone(), |s| s.full.clone())
}

fn space_basis(st: &Rc<Struct>) -> RResult<Mat> {
    let mp = crate::intrinsics::matrices::info(st);
    match &mp.sub {
        Some(s) => Ok(s.basis.clone()),
        None => Mat::identity(&mp.ctx, mp.ncols).map_err(gr),
    }
}

fn space_form(st: &Rc<Struct>) -> RResult<Mat> {
    let mp = crate::intrinsics::matrices::info(st);
    match crate::intrinsics::matrices::inner_product_matrix(st) {
        Some(f) => Ok(f),
        None => Mat::identity(&mp.ctx, mp.ncols).map_err(gr),
    }
}

fn involution(st: &Rc<Struct>) -> Option<Rc<MapObj>> {
    let full = full_space(st);
    let out = match full.attrs.borrow().get(&Sym::new("Involution")) {
        Some(Value::Map(m)) => Some(m.clone()),
        _ => None,
    };
    out
}

fn apply_map_to_matrix(it: &mut Interp, ring: &Value, m: &Mat, map: Option<&Rc<MapObj>>) -> RResult<Mat> {
    let Some(map) = map else { return Ok(m.clone()) };
    let mut out = Mat::zero(m.ctx(), m.nrows(), m.ncols());
    for i in 0..m.nrows() {
        for j in 0..m.ncols() {
            let x = crate::intrinsics::matrices::entry_of(it, ring, m, i, j);
            let y = it.apply_map(map, &x)?;
            if !crate::intrinsics::matrices::set_entry(it, ring, &mut out, i, j, &y)? {
                return Err(RuntimeError::runtime("The involution does not preserve the base field"));
            }
        }
    }
    Ok(out)
}

fn space_with_basis(st: &Rc<Struct>, basis: Mat) -> RResult<Rc<Struct>> {
    let full = full_space(st);
    let mp = crate::intrinsics::matrices::info(&full);
    if basis.nrows() == mp.ncols && basis.equal(&Mat::identity(&mp.ctx, mp.ncols).map_err(gr)?) == Truth::True {
        return Ok(full);
    }
    let (ring, ncols, field, ctx) = (mp.ring.clone(), mp.ncols, mp.field, mp.ctx.clone());
    let sub = Sub { full, basis, echelonized: true };
    Ok(Struct::new(StructKind::Matrices(Rc::new(MatParent {
        ring, nrows: 1, ncols, shape: Shape::Tuples, field, ctx, sub: Some(sub), form: None,
    }))))
}

// ----- inner products (text/316) --------------------------------------------

fn ensure_upper_triangular(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = matrix_arg(a, 0)?;
    if x.m.nrows() != x.m.ncols() {
        return Err(RuntimeError::runtime("Argument 1 is not square"));
    }
    let n = x.m.nrows();
    let mut q = Mat::zero(x.m.ctx(), n, n);
    for i in 0..n {
        q.set_entry(i, i, &x.m.entry(i, i));
        for j in i + 1..n {
            q.set_entry(i, j, &x.m.entry(i, j).add(&x.m.entry(j, i)).map_err(gr)?);
        }
    }
    one(matrix(it, x.ring(), q)?)
}

fn product_matrix(it: &mut Interp, st: &Rc<Struct>, rows: &Mat, conjugate: bool) -> RResult<Mat> {
    let mp = crate::intrinsics::matrices::info(st);
    let right = if conjugate { apply_map_to_matrix(it, &mp.ring, rows, involution(st).as_ref())? } else { rows.clone() };
    rows.mul(&space_form(st)?).map_err(gr)?.mul(&right.transpose()).map_err(gr)
}

fn dot_product(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (u, v) = (vector_arg(a, 0)?, vector_arg(a, 1)?);
    if u.m.ncols() != v.m.ncols() || !Rc::ptr_eq(&full_space(&u.parent), &full_space(&v.parent)) {
        return Err(RuntimeError::runtime("Arguments are not compatible"));
    }
    let st = full_space(&u.parent);
    let mp = crate::intrinsics::matrices::info(&st);
    let right = apply_map_to_matrix(it, &mp.ring, &v.m, involution(&st).as_ref())?;
    let r = u.m.mul(&space_form(&st)?).map_err(gr)?.mul(&right.transpose()).map_err(gr)?;
    one(crate::intrinsics::matrices::entry_of(it, &mp.ring, &r, 0, 0))
}

fn dot_product_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.seq(0)?;
    let Some(Value::Mat(first)) = s.elems.first() else { return Err(RuntimeError::runtime("Illegal null sequence")) };
    if !first.is_vector() {
        return Err(bad());
    }
    let st = full_space(&first.parent);
    let mp = crate::intrinsics::matrices::info(&st);
    let mut rows = Mat::zero(&mp.ctx, s.elems.len(), mp.ncols);
    for (i, v) in s.elems.iter().enumerate() {
        let Value::Mat(v) = v else { return Err(bad()) };
        if !v.is_vector() || !Rc::ptr_eq(&full_space(&v.parent), &st) {
            return Err(RuntimeError::runtime("Sequence elements are not compatible"));
        }
        rows.insert(&v.m, i, 0);
    }
    let products = product_matrix(it, &st, &rows, true)?;
    one(matrix(it, &mp.ring, products)?)
}

fn gram_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = space_arg(a, 0)?;
    let mp = crate::intrinsics::matrices::info(&st);
    let b = space_basis(&st)?;
    let g = b.mul(&space_form(&st)?).map_err(gr)?.mul(&b.transpose()).map_err(gr)?;
    one(matrix(it, &mp.ring, g)?)
}

fn orthogonal_basis(it: &mut Interp, v: &Rc<Struct>, x: &Rc<Struct>, right: bool) -> RResult<Mat> {
    let vf = full_space(v);
    if !Rc::ptr_eq(&vf, &full_space(x)) {
        return Err(RuntimeError::runtime("Arguments are not compatible"));
    }
    let mp = crate::intrinsics::matrices::info(&vf);
    let (bv, bx, f) = (space_basis(v)?, space_basis(x)?, space_form(&vf)?);
    let map = involution(&vf);
    let coeff = if right {
        let sbv = apply_map_to_matrix(it, &mp.ring, &bv, map.as_ref())?;
        let equations = sbv.mul(&f.transpose()).map_err(gr)?.mul(&bx.transpose()).map_err(gr)?;
        apply_map_to_matrix(it, &mp.ring, &equations.left_kernel().map_err(gr)?, map.as_ref())?
    } else {
        let sbx = apply_map_to_matrix(it, &mp.ring, &bx, map.as_ref())?;
        bv.mul(&f).map_err(gr)?.mul(&sbx.transpose()).map_err(gr)?.left_kernel().map_err(gr)?
    };
    coeff.mul(&bv).map_err(gr)
}

fn orthogonal_complement(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (v, x) = (space_arg(a, 0)?, space_arg(a, 1)?);
    let b = orthogonal_basis(it, &v, &x, a.param_bool("Right")?)?;
    one(Value::Struct(space_with_basis(&v, b)?))
}

fn radical(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let v = space_arg(a, 0)?;
    let b = orthogonal_basis(it, &v, &v, a.param_bool("Right")?)?;
    one(Value::Struct(space_with_basis(&v, b)?))
}

fn nondegenerate(it: &mut Interp, st: &Rc<Struct>) -> RResult<bool> {
    let b = space_basis(st)?;
    Ok(product_matrix(it, st, &b, true)?.left_kernel().map_err(gr)?.nrows() == 0)
}

fn is_nondegenerate(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Bool(nondegenerate(it, &space_arg(a, 0)?)?))
}

fn is_degenerate(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Bool(!nondegenerate(it, &space_arg(a, 0)?)?))
}

fn quadratic_form(st: &Rc<Struct>) -> RResult<Rc<Mtrx>> {
    let full = full_space(st);
    let out = match full.attrs.borrow().get(&Sym::new("QuadraticForm")) {
        Some(Value::Mat(q)) => Ok(q.clone()),
        _ => Err(RuntimeError::runtime("The space is not a quadratic space")),
    };
    out
}

fn singular_radical_basis(it: &mut Interp, st: &Rc<Struct>) -> RResult<Mat> {
    let q = quadratic_form(st)?;
    let r = orthogonal_basis(it, st, st, false)?;
    if r.nrows() == 0 {
        return Ok(r);
    }
    let values = r.mul(&q.m).map_err(gr)?.mul(&r.transpose()).map_err(gr)?;
    let mut roots = Mat::zero(r.ctx(), r.nrows(), 1);
    for i in 0..r.nrows() {
        roots.set_entry(i, 0, &values.entry(i, i).sqrt().map_err(gr)?);
    }
    roots.left_kernel().map_err(gr)?.mul(&r).map_err(gr)
}

fn singular_radical(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let v = space_arg(a, 0)?;
    one(Value::Struct(space_with_basis(&v, singular_radical_basis(it, &v)?)?))
}

fn is_nonsingular(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Bool(singular_radical_basis(it, &space_arg(a, 0)?)?.nrows() == 0))
}

fn anti_diagonal(ctx: &Rc<calyx_flint::gr::Ctx>, n: usize, alternating: bool) -> RResult<Mat> {
    let mut m = Mat::zero(ctx, n, n);
    let one = Elem::one(ctx).map_err(gr)?;
    let minus_one = one.neg().map_err(gr)?;
    for i in 0..n {
        m.set_entry(i, n - 1 - i, if alternating && i >= n / 2 { &minus_one } else { &one });
    }
    Ok(m)
}

fn standard_alternating(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = dim(a)?;
    if n % 2 != 0 {
        return Err(RuntimeError::runtime("Argument 1 must be even"));
    }
    let (ring, _) = ring_arg(it, a, false)?;
    let ctx = crate::intrinsics::matrices::entry_ctx(it, &ring)?;
    one(matrix(it, &ring, anti_diagonal(&ctx, n, true)?)?)
}

fn standard_pseudo_alternating(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = dim(a)?;
    let (ring, _) = ring_arg(it, a, false)?;
    let (p, _) = finite_field(&ring)?;
    if p != Integer::from_u64(2) {
        return Err(RuntimeError::runtime("The field must have characteristic 2"));
    }
    let ctx = crate::intrinsics::matrices::entry_ctx(it, &ring)?;
    let mut m = Mat::zero(&ctx, n, n);
    let one_ = Elem::one(&ctx).map_err(gr)?;
    let pairs = n / 2;
    for i in 0..pairs {
        let (j, k) = (2 * i, 2 * i + 1);
        m.set_entry(j, k, &one_);
        m.set_entry(k, j, &one_);
    }
    if n % 2 == 1 {
        m.set_entry(n - 1, n - 1, &one_);
    } else if n != 0 {
        m.set_entry(n - 1, n - 1, &one_);
    }
    one(matrix(it, &ring, m)?)
}

enum Conjugation {
    Finite(Integer),
    Intrinsic,
}

struct ConjugationMap(Conjugation);

impl NativeMap for ConjugationMap {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let x = match it.try_coerce(&m.domain, x)? {
            Ok(x) => x,
            Err(_) => return Err(RuntimeError::runtime("Element is not in the domain of the map").in_context("map application")),
        };
        match &self.0 {
            Conjugation::Finite(q) => {
                let y = it.to_structure_elem(&m.domain, &x, false)?.ok_or_else(bad)?;
                Ok(it.elem_to_value(&m.codomain, y.pow(q).map_err(gr)?))
            }
            Conjugation::Intrinsic => it.call_intrinsic_named(Sym::new("ComplexConjugate"), vec![x]),
        }
    }

    fn preimage(&self, _it: &mut Interp, _m: &MapObj, _y: &Value) -> RResult<Value> {
        Err(RuntimeError::runtime("Map has no inverse").in_context("@@"))
    }

    fn rule(&self) -> bool {
        true
    }

    fn has_inverse(&self) -> bool {
        false
    }
}

fn standard_hermitian(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = dim(a)?;
    let (ring, integer_q) = ring_arg(it, a, true)?;
    let conjugation = match finite_field(&ring) {
        Ok((_, order)) => {
            let q = match integer_q {
                Some(q) => q,
                None => {
                    let q = order.isqrt().unwrap();
                    if &q * &q != order {
                        return Err(RuntimeError::runtime("The field order must be a square"));
                    }
                    q
                }
            };
            Conjugation::Finite(q)
        }
        Err(_) if ring_props(&ring).is_some_and(|p| p.field) => Conjugation::Intrinsic,
        Err(e) => return Err(e),
    };
    let ctx = crate::intrinsics::matrices::entry_ctx(it, &ring)?;
    let form = matrix(it, &ring, anti_diagonal(&ctx, n, false)?)?;
    let map = Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: ring.clone(), codomain: ring, imp: MapImpl::Native(Rc::new(ConjugationMap(conjugation))) }));
    Ok(vals![form, map])
}

fn primitive(it: &mut Interp, ring: &Value) -> RResult<Elem> {
    let st = field_struct(ring).ok_or_else(bad)?;
    it.ff_primitive(st)
}

/// A coefficient c for which x^2 + x + c is irreducible.  In odd
/// characteristic this tests a bounded sequence of powers of a primitive
/// element; in characteristic two a normal element has absolute trace one.
fn anisotropic_coefficient(it: &mut Interp, ring: &Value, p: &Integer) -> RResult<Elem> {
    let ctx = crate::intrinsics::matrices::entry_ctx(it, ring)?;
    if p == &Integer::from_u64(2) {
        let x = it.call_intrinsic_named(Sym::new("NormalElement"), vec![ring.clone()])?;
        return it.to_structure_elem(ring, &x, false)?.ok_or_else(bad);
    }
    let one = Elem::one(&ctx).map_err(gr)?;
    let four = Elem::from_integer(&ctx, &Integer::from_u64(4)).map_err(gr)?;
    let g = primitive(it, ring)?;
    let mut c = one.clone();
    for _ in 0..64 {
        let disc = one.sub(&four.mul(&c).map_err(gr)?).map_err(gr)?;
        if disc.is_square() == Truth::False {
            return Ok(c);
        }
        c = c.mul(&g).map_err(gr)?;
    }
    Err(RuntimeError::runtime("Could not construct an anisotropic plane"))
}

fn variant(a: &CallArgs) -> RResult<&str> {
    match a.param("Variant") {
        Some(Value::Str(s)) if s.as_str() == "Default" || s.as_str() == "Revised" => Ok(s.as_str()),
        Some(Value::Str(s)) => Err(RuntimeError::runtime(format!("Unknown form variant '{s}'"))),
        _ => Err(RuntimeError::runtime("Parameter 'Variant' must be a string")),
    }
}

fn quadratic_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<(Value, Mat)> {
    let n = dim(a)?;
    let (ring, _) = ring_arg(it, a, false)?;
    let (p, _) = finite_field(&ring)?;
    let ctx = crate::intrinsics::matrices::entry_ctx(it, &ring)?;
    let mut q = Mat::zero(&ctx, n, n);
    let one = Elem::one(&ctx).map_err(gr)?;
    for i in 0..(n + 1) / 2 {
        q.set_entry(i, n - 1 - i, &one);
    }
    if !a.param_bool("Minus")? || n == 0 {
        return Ok((ring, q));
    }
    let g = primitive(it, &ring)?;
    if n % 2 == 1 {
        if p != Integer::from_u64(2) {
            q.set_entry(n / 2, n / 2, &g.neg().map_err(gr)?);
        }
        return Ok((ring, q));
    }
    let i = n / 2 - 1;
    if variant(a)? == "Revised" && p != Integer::from_u64(2) {
        let two = Elem::from_integer(&ctx, &Integer::from_u64(2)).map_err(gr)?;
        let half = two.inv().map_err(gr)?;
        let minus_one_square = one.neg().map_err(gr)?.is_square() == Truth::True;
        let c = if minus_one_square { half.mul(&g).map_err(gr)? } else { half.clone() };
        q.set_entry(i, i, &half);
        q.set_entry(i, i + 1, &Elem::zero(&ctx));
        q.set_entry(i + 1, i + 1, &c);
    } else {
        let c = anisotropic_coefficient(it, &ring, &p)?;
        q.set_entry(i, i, &one);
        q.set_entry(i, i + 1, &one);
        q.set_entry(i + 1, i + 1, &c);
    }
    Ok((ring, q))
}

fn standard_quadratic(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (ring, q) = quadratic_matrix(it, a)?;
    one(matrix(it, &ring, q)?)
}

fn standard_symmetric(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (ring, q) = quadratic_matrix(it, a)?;
    let s = q.add(&q.transpose()).map_err(gr)?;
    one(matrix(it, &ring, s)?)
}

pub fn register(it: &mut Interp) {
    it.def("EnsureUpperTriangular", "A::AlgMatElt -> AlgMatElt", "An upper triangular matrix defining the same quadratic form as A.", ensure_upper_triangular);
    it.def("DotProduct", "u::ModTupFldElt, v::ModTupFldElt -> FldElt", "The bilinear or sesquilinear product of u and v in their formed space.", dot_product);
    it.def("DotProductMatrix", "S::SeqEnum -> AlgMatElt", "The matrix of pairwise dot products of the vectors in S.", dot_product_matrix);
    it.def("GramMatrix", "V::ModTupRng -> AlgMatElt", "The Gram matrix on the echelonized basis of V.", gram_matrix);
    let right = [("Right", Value::Bool(false))];
    it.def_params("OrthogonalComplement", "V::ModTupFld, X::ModTupFld -> ModTupFld", &right, "The left or right orthogonal complement of X in V.", orthogonal_complement);
    it.def_params("Radical", "V::ModTupFld -> ModTupFld", &right, "The left or right radical of V.", radical);
    it.def("IsNondegenerate", "V::ModTupFld -> BoolElt", "Whether the form restricted to V is non-degenerate.", is_nondegenerate);
    it.def("IsDegenerate", "V::ModTupFld -> BoolElt", "Whether the form restricted to V is degenerate.", is_degenerate);
    it.def("SingularRadical", "V::ModTupFld -> ModTupFld", "The singular radical of a quadratic space.", singular_radical);
    it.def("IsNonsingular", "V::ModTupFld -> BoolElt", "Whether a quadratic space has zero singular radical.", is_nonsingular);
    it.def("StandardAlternatingForm", "n::RngIntElt, R::Rng -> AlgMatElt", "The standard non-degenerate alternating form of degree n over R.", standard_alternating);
    it.def("StandardAlternatingForm", "n::RngIntElt, q::RngIntElt -> AlgMatElt", "The standard non-degenerate alternating form over GF(q).", standard_alternating);
    it.def("StandardPseudoAlternatingForm", "n::RngIntElt, K::Fld -> AlgMatElt", "The standard pseudo-alternating form of degree n in characteristic two.", standard_pseudo_alternating);
    it.def("StandardPseudoAlternatingForm", "n::RngIntElt, q::RngIntElt -> AlgMatElt", "The standard pseudo-alternating form over GF(q).", standard_pseudo_alternating);
    it.def("StandardHermitianForm", "n::RngIntElt, K::Fld -> AlgMatElt, Map", "The standard hermitian form and its field conjugation.", standard_hermitian);
    it.def("StandardHermitianForm", "n::RngIntElt, q::RngIntElt -> AlgMatElt, Map", "The standard hermitian form over GF(q^2) and its field conjugation.", standard_hermitian);
    let params = [("Minus", Value::Bool(false)), ("Variant", Value::str("Default"))];
    it.def_params("StandardQuadraticForm", "n::RngIntElt, K::Fld -> AlgMatElt", &params, "The standard upper triangular matrix of a quadratic form.", standard_quadratic);
    it.def_params("StandardQuadraticForm", "n::RngIntElt, q::RngIntElt -> AlgMatElt", &params, "The standard upper triangular matrix of a quadratic form over GF(q).", standard_quadratic);
    it.def_params("StandardSymmetricForm", "n::RngIntElt, K::Fld -> AlgMatElt", &params, "The symmetric bilinear form associated to the standard quadratic form.", standard_symmetric);
    it.def_params("StandardSymmetricForm", "n::RngIntElt, q::RngIntElt -> AlgMatElt", &params, "The symmetric bilinear form associated to the standard quadratic form over GF(q).", standard_symmetric);
}
