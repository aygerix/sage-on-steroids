//! Nullspaces, rowspaces and rank of sparse matrices (text/297).

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::Truth;
use calyx_flint::mat::Mat;

use super::{dense_value, sparse_arg};
use crate::error::RResult;
use crate::interp::{CallArgs, Interp};
use crate::value::*;

/// Call the corresponding dense intrinsic, preserving parameters and the
/// requested number of results.  Structured elimination below uses this only
/// after the sparse part has become dense enough to justify conversion.
pub(super) fn dense_call(it: &mut Interp, a: &CallArgs, nresults: usize) -> RResult<Vals> {
    let x = sparse_arg(a, 0)?;
    let mut args = a.args.clone();
    args[0] = dense_value(it, &x)?;
    let refs = vec![false; args.len()];
    Ok(it.call_intrinsic(a.name, &mut args, &refs, a.params.clone(), nresults, false, a.span, None)?.expect("a function intrinsic"))
}

fn nullspace(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = sparse_arg(a, 0)?;
    if structured_rank(&x)?.is_some_and(|r| r == x.nrows) {
        return Ok(vals![subspace(it, x.ring(), x.nrows, Mat::zero(&x.info().ctx, 0, x.nrows))?]);
    }
    dense_call(it, a, 1)
}

fn kernel(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let mut out = nullspace(it, a)?;
    if a.nresults < 2 {
        return Ok(out);
    }
    let space = out[0].clone();
    let Value::Struct(st) = &space else { unreachable!("a kernel space") };
    let mp = crate::intrinsics::matrices::parent_info(&space).expect("a matrix space");
    let codomain = Value::Struct(mp.sub.as_ref().map_or_else(|| st.clone(), |s| s.full.clone()));
    let map = MapObj { kind: MapKind::Map, domain: space, codomain, imp: MapImpl::Coercion };
    out.push(Value::Map(Rc::new(map)));
    Ok(out)
}

fn kernel_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = sparse_arg(a, 0)?;
    if structured_rank(&x)?.is_some_and(|r| r == x.nrows) {
        return Ok(vals![crate::intrinsics::matrices::mat_value(it, x.ring(), Mat::zero(&x.info().ctx, 0, x.nrows))?]);
    }
    dense_call(it, a, 1)
}

fn nullspace_of_transpose(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = sparse_arg(a, 0)?;
    if structured_rank(&x)?.is_some_and(|r| r == x.ncols) {
        return Ok(vals![subspace(it, x.ring(), x.ncols, Mat::zero(&x.info().ctx, 0, x.ncols))?]);
    }
    dense_call(it, a, 1)
}

fn structured_rank(x: &super::SparseMatrix) -> RResult<Option<usize>> {
    if let Some(r) = super::structured::word_reduce(x) {
        return Ok(Some(r.pivots + r.remainder.rank().map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?));
    }
    if let Some(r) = super::structured::integer_reduce(x) {
        return Ok(Some(r.pivots + r.remainder.rank().map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?));
    }
    Ok(None)
}

fn subspace(it: &mut Interp, ring: &Value, degree: usize, basis: Mat) -> RResult<Value> {
    use crate::intrinsics::matrices::{MatParent, Shape, Sub};

    let full = crate::intrinsics::matrices::parent(it, ring, 1, degree, Shape::Tuples)?;
    let full_value = Value::Struct(full.clone());
    let fp = crate::intrinsics::matrices::parent_info(&full_value).expect("an R-space");
    if basis.nrows() == degree && basis.equal(&Mat::identity(&fp.ctx, degree).map_err(|e| crate::rings::gr_error(e, "Identity failed"))?) == Truth::True {
        return Ok(Value::Struct(full));
    }
    let p = MatParent {
        ring: ring.clone(),
        nrows: 1,
        ncols: degree,
        shape: Shape::Tuples,
        field: fp.field,
        ctx: fp.ctx.clone(),
        sub: Some(Sub { full, basis, echelonized: true }),
        form: None,
    };
    Ok(Value::Struct(Struct::new(StructKind::Matrices(Rc::new(p)))))
}

fn rowspace(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = sparse_arg(a, 0)?;
    let ring = x.ring().clone();
    let dense = dense_value(it, &x)?;
    let Value::Mat(m) = dense else { unreachable!() };
    let (e, _) = crate::intrinsics::matrices::echelon(&m, false)?;
    let rows: Vec<usize> = (0..e.nrows()).filter(|&i| (0..e.ncols()).any(|j| !e.entry_is_zero(i, j))).collect();
    let cols: Vec<usize> = (0..e.ncols()).collect();
    let basis = e.select(&rows, &cols);
    Ok(vals![subspace(it, &ring, x.ncols, basis)?])
}

fn rank(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = sparse_arg(a, 0)?;
    if let Some(rank) = structured_rank(&x)? {
        return crate::intrinsics::intv(Integer::from_u64(rank as u64));
    }
    let dense = dense_value(it, &x)?;
    let Value::Mat(m) = dense else { unreachable!() };
    crate::intrinsics::intv(Integer::from_u64(crate::intrinsics::matrices::rank_of(&m)? as u64))
}

pub(super) fn register(it: &mut Interp) {
    it.def("Nullspace", "A::MtrxSprs -> ModTupRng", "The space of vectors v with v*A = 0.", nullspace);
    it.def("Kernel", "A::MtrxSprs -> ModTupRng, Map", "The kernel of A and its inclusion map.", kernel);
    for name in ["NullspaceMatrix", "KernelMatrix"] {
        it.def(name, "A::MtrxSprs -> Mtrx", "A dense basis matrix of the nullspace of A.", kernel_matrix);
    }
    it.def("NullspaceOfTranspose", "A::MtrxSprs -> ModTupRng", "The nullspace of the transpose of A.", nullspace_of_transpose);
    it.def("Rowspace", "A::MtrxSprs -> ModTupRng", "The space generated by the rows of A.", rowspace);
    it.def("Rank", "A::MtrxSprs -> RngIntElt", "The rank of A.", rank);
}
