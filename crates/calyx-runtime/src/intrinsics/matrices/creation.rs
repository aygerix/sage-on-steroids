//! Creation of matrices and vectors: the forms of `Matrix`, structured and
//! random matrices, `Vector`, and the full matrix algebras, matrix spaces
//! and R-spaces with coercion into them.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{CtxKind, Elem};
use calyx_flint::mat::Mat;

use super::{Mtrx, Shape, bad, entry_ctx, entry_value, info, mat_arg, mat_value, parent, set_entry, vec_value};
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::{arg_ge, bare, hidden_inner, one};
use crate::interp::{CallArgs, Interp};
use crate::sym::Sym;
use crate::types::t;
use crate::value::*;

/// Argument i as a dimension (a non-negative integer), numbered `num` in
/// the error.
fn dim(a: &CallArgs, i: usize, num: usize) -> RResult<usize> {
    let n = a.int(i)?;
    match n.to_u64() {
        Some(v) if v < 1 << 32 => Ok(v as usize),
        _ if n.sign() < 0 => Err(arg_ge(num, n, 0)),
        _ => Err(RuntimeError::runtime(format!("Argument {num} ({n}) is too large"))),
    }
}

/// Argument i as a ring (a structure whose elements can be entries).
fn ring_arg(a: &CallArgs, i: usize) -> RResult<Value> {
    match &a.args[i] {
        v @ Value::Struct(_) => Ok(v.clone()),
        _ => Err(bad()),
    }
}

/// The ring of the entries of a sequence: its universe.
fn universe(it: &mut Interp, q: &SeqEnum) -> RResult<Value> {
    match &q.universe {
        Some(u) if it.types.isa(u.type_id(), t::RNG) => Ok(u.clone()),
        Some(_) => Err(bad()),
        None => Err(RuntimeError::runtime("Illegal null sequence")),
    }
}

fn coerce_failed(k: usize) -> RuntimeError {
    RuntimeError::runtime(format!("Cannot coerce sequence element {k} into the coefficient ring"))
}

/// The r by c matrix over `ring` given by `q` in one of the forms of
/// `Matrix(R, m, n, Q)`: the entries in row-major order, the rows as
/// sequences or vectors, or triples `<i, j, x>` for the entries that are
/// not zero.
fn from_seq(it: &mut Interp, ring: &Value, r: usize, c: usize, q: &SeqEnum) -> RResult<Mat> {
    let ctx = entry_ctx(it, ring)?;
    let mut m = Mat::zero(&ctx, r, c);
    match q.elems.first() {
        // The null sequence gives the zero matrix, as an empty list of
        // triples would.
        None if q.universe.is_none() => {}
        None if r * c != 0 => return Err(RuntimeError::runtime(format!("Sequence should have length {}", r * c))),
        None => {}
        Some(Value::Tuple(_)) => {
            for (k, x) in q.elems.iter().enumerate() {
                let Value::Tuple(tp) = x else { return Err(bad()) };
                let [i, j, x] = &tp.elems[..] else { return Err(bad()) };
                let at = |n: usize, v: &Value, hi: usize| -> RResult<usize> {
                    let Value::Int(v) = v else { return Err(bad()) };
                    match v.to_u64() {
                        Some(i) if (1..=hi as u64).contains(&i) => Ok(i as usize - 1),
                        _ => Err(RuntimeError::runtime(format!("Component {n} of sequence entry {} ({v}) is not in range [1 .. {hi}]", k + 1))),
                    }
                };
                let (i, j) = (at(1, i, r)?, at(2, j, c)?);
                if !set_entry(it, ring, &mut m, i, j, x)? {
                    return Err(coerce_failed(k + 1));
                }
            }
        }
        Some(Value::Seq(_) | Value::Mat(_)) => {
            if q.elems.len() != r {
                return Err(RuntimeError::runtime(format!("Sequence should have length {r}")));
            }
            for (i, row) in q.elems.iter().enumerate() {
                let entries: Vec<Value> = match row {
                    Value::Seq(s) if s.elems.len() == c => s.elems.clone(),
                    Value::Mat(v) if v.is_vector() && v.m.ncols() == c => (0..c).map(|j| entry_value(it, v, 0, j)).collect(),
                    Value::Seq(_) | Value::Mat(_) => return Err(bare(RuntimeError::runtime(format!("Element {} of sequence does not have length {c}", i + 1)))),
                    _ => return Err(bad()),
                };
                for (j, x) in entries.iter().enumerate() {
                    if !set_entry(it, ring, &mut m, i, j, x)? {
                        return Err(coerce_failed(i * c + j + 1));
                    }
                }
            }
        }
        Some(_) => {
            if q.elems.len() != r * c {
                return Err(RuntimeError::runtime(format!("Sequence should have length {}", r * c)));
            }
            for (k, x) in q.elems.iter().enumerate() {
                if !set_entry(it, ring, &mut m, k / c, k % c, x)? {
                    return Err(coerce_failed(k + 1));
                }
            }
        }
    }
    Ok(m)
}

/// The ring and number of columns of a sequence of rows (sequences or
/// vectors).
fn rows_shape(it: &mut Interp, q: &SeqEnum) -> RResult<(Value, usize)> {
    match q.elems.first() {
        Some(Value::Seq(s)) => Ok((universe(it, s)?, s.elems.len())),
        Some(Value::Mat(v)) if v.is_vector() => Ok((v.ring().clone(), v.m.ncols())),
        Some(_) => Err(bad()),
        None => Err(RuntimeError::runtime("Illegal null sequence")),
    }
}

/// `Matrix(R, m, n, Q)`.
fn matrix_rmnq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let (r, c) = (dim(a, 1, 1)?, dim(a, 2, 2)?);
    let q = a.seq(3)?.clone();
    let m = from_seq(it, &ring, r, c, &q)?;
    one(mat_value(it, &ring, m)?)
}

/// `Matrix(m, n, Q)`.
fn matrix_mnq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (r, c) = (dim(a, 0, 1)?, dim(a, 1, 2)?);
    let q = a.seq(2)?.clone();
    let ring = match q.elems.first() {
        Some(Value::Seq(_) | Value::Mat(_)) => rows_shape(it, &q)?.0,
        _ => universe(it, &q)?,
    };
    let m = from_seq(it, &ring, r, c, &q)?;
    one(mat_value(it, &ring, m)?)
}

/// `Matrix(R, n, Q)` and `Matrix(n, Q)`: rows of length n.
fn matrix_nq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = a.args.len() - 2;
    let ring = if k == 1 { ring_arg(a, 0)? } else { universe(it, a.seq(1)?)? };
    let c = dim(a, k, k + 1)?;
    let q = a.seq(k + 1)?.clone();
    let len = q.elems.len();
    if c == 0 && len > 0 {
        return Err(RuntimeError::runtime("Sequence should have length 0"));
    }
    if c > 0 && len % c != 0 {
        return Err(RuntimeError::runtime(format!("Sequence length ({len}) is not a multiple of {c}")));
    }
    let r = if c == 0 { 0 } else { len / c };
    let m = from_seq(it, &ring, r, c, &q)?;
    one(mat_value(it, &ring, m)?)
}

/// `Matrix(Q)` and `Matrix(R, Q)`: the rows as sequences or vectors.
fn matrix_rows(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = a.args.len() - 1;
    let q = a.seq(k)?.clone();
    let (ring, c) = match (k, q.elems.first()) {
        (1, Some(Value::Seq(s))) => (ring_arg(a, 0)?, s.elems.len()),
        (1, _) => (ring_arg(a, 0)?, 0),
        (_, Some(Value::Seq(s))) if s.universe.is_none() => return Err(bare(RuntimeError::runtime("Inner sequence must not be null "))),
        (_, Some(Value::Mat(_))) => return one(flattened(it, &q)?),
        _ => rows_shape(it, &q)?,
    };
    let m = from_seq(it, &ring, q.elems.len(), c, &q)?;
    one(mat_value(it, &ring, m)?)
}

/// `Matrix(Q)` for a sequence of vectors or matrices (of one shape): their
/// entries in row-major order as the rows.
fn flattened(it: &mut Interp, q: &SeqEnum) -> RResult<Value> {
    let Some(Value::Mat(first)) = q.elems.first() else { unreachable!() };
    let (r, c) = (first.m.nrows(), first.m.ncols());
    let mut m = Mat::zero(first.m.ctx(), q.elems.len(), r * c);
    for (i, x) in q.elems.iter().enumerate() {
        let Value::Mat(x) = x else { return Err(bad()) };
        for k in 0..x.m.nrows() {
            m.insert(&x.m.block(k, 0, 1, c), i, k * c);
        }
    }
    let ring = first.ring().clone();
    mat_value(it, &ring, m)
}

/// `Matrix(A)`: A in the matrix algebra or space of its shape.
fn matrix_of(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let ring = x.ring().clone();
    one(mat_value(it, &ring, x.m.clone())?)
}

// ----- structured matrices -------------------------------------------------------------

/// A dimension error of the intrinsic `name` that a package intrinsic
/// calls, reported with its name after the hidden traceback.
fn inner(name: &str) -> impl Fn(RuntimeError) -> RuntimeError + '_ {
    move |e| hidden_inner(e.in_context(name))
}

fn zero_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let (r, c) = (dim(a, 1, 1).map_err(inner("Matrix"))?, dim(a, 2, 2).map_err(inner("Matrix"))?);
    let ctx = entry_ctx(it, &ring)?;
    one(mat_value(it, &ring, Mat::zero(&ctx, r, c))?)
}

fn identity_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let n = dim(a, 1, 2).map_err(inner("MatrixRing"))?;
    let ctx = entry_ctx(it, &ring)?;
    let m = Mat::identity(&ctx, n)?;
    one(mat_value(it, &ring, m)?)
}

/// The n by n matrix over `ring` with the entries `diag` on the diagonal.
fn diagonal(it: &mut Interp, ring: &Value, n: usize, diag: &[Value]) -> RResult<Value> {
    let ctx = entry_ctx(it, ring)?;
    let mut m = Mat::zero(&ctx, n, n);
    for (i, x) in diag.iter().enumerate() {
        if !set_entry(it, ring, &mut m, i, i, x)? {
            return Err(coerce_failed(i + 1));
        }
    }
    mat_value(it, ring, m)
}

/// `ScalarMatrix(n, s)` and `ScalarMatrix(R, n, s)`.
fn scalar_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = a.args.len() - 2;
    let s = a.args[k + 1].clone();
    let ring = if k == 1 { ring_arg(a, 0)? } else { it.parent_of(&s)? };
    let n = dim(a, k, k + 1)?;
    one(diagonal(it, &ring, n, &vec![s; n])?)
}

/// `DiagonalMatrix(R, n, Q)`, `DiagonalMatrix(R, Q)` and `DiagonalMatrix(Q)`.
fn diagonal_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = a.args.len() - 1;
    let q = a.seq(k)?.clone();
    let ring = match k {
        0 if q.universe.is_none() => return Err(bare(RuntimeError::runtime("Argument 1 must not be null"))),
        0 => universe(it, &q)?,
        _ => ring_arg(a, 0)?,
    };
    let n = if k == 2 { dim(a, 1, 2)? } else { q.elems.len() };
    if q.elems.len() != n {
        return Err(bare(RuntimeError::runtime(format!("Length of argument 3 is not {n}"))));
    }
    one(diagonal(it, &ring, n, &q.elems)?)
}

/// The n with n(n + 1)/2 = len (or n(n - 1)/2 with `strict`).
fn triangular_size(len: usize, strict: bool) -> RResult<usize> {
    let mut n = 0;
    loop {
        let t = if strict { n * (n + 1) / 2 } else { (n + 1) * (n + 2) / 2 };
        match t.cmp(&len) {
            std::cmp::Ordering::Equal => return Ok(n + 1),
            std::cmp::Ordering::Greater => return Err(RuntimeError::runtime(format!("Length of sequence ({len}) is not a triangular number"))),
            std::cmp::Ordering::Less => n += 1,
        }
    }
}

#[derive(Clone, Copy)]
enum Tri {
    Lower,
    Upper,
    Symmetric,
    Antisymmetric,
}

/// The triangular, symmetric and antisymmetric matrices from the entries
/// of the lower (or upper) triangle in row-major order.
fn triangular(it: &mut Interp, a: &mut CallArgs, kind: Tri) -> RResult<Vals> {
    let k = a.args.len() - 1;
    let q = a.seq(k)?.clone();
    let ring = if k == 1 { ring_arg(a, 0)? } else { universe(it, &q)? };
    if q.elems.is_empty() {
        let ctx = entry_ctx(it, &ring)?;
        return one(mat_value(it, &ring, Mat::zero(&ctx, 0, 0))?);
    }
    let strict = matches!(kind, Tri::Antisymmetric);
    let n = triangular_size(q.elems.len(), strict)?;
    let ctx = entry_ctx(it, &ring)?;
    let mut m = Mat::zero(&ctx, n, n);
    let mut k = 0;
    for i in 0..n {
        let cols: Vec<usize> = match kind {
            Tri::Upper => (i..n).collect(),
            Tri::Antisymmetric => (0..i).collect(),
            _ => (0..=i).collect(),
        };
        for j in cols {
            if !set_entry(it, &ring, &mut m, i, j, &q.elems[k])? {
                return Err(coerce_failed(k + 1));
            }
            k += 1;
            match kind {
                Tri::Symmetric if i != j => {
                    let x = m.entry(i, j);
                    m.set_entry(j, i, &x);
                }
                Tri::Antisymmetric => {
                    let x = m.entry(i, j).neg()?;
                    m.set_entry(j, i, &x);
                }
                _ => {}
            }
        }
    }
    one(mat_value(it, &ring, m)?)
}

fn lower_triangular(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    triangular(it, a, Tri::Lower)
}

fn upper_triangular(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    triangular(it, a, Tri::Upper)
}

fn symmetric(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    triangular(it, a, Tri::Symmetric)
}

fn antisymmetric(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    triangular(it, a, Tri::Antisymmetric)
}

/// The permutation matrix of the images `perm` (from 0): row i has its one
/// in column perm[i].
fn permutation(it: &mut Interp, ring: &Value, perm: &[usize]) -> RResult<Value> {
    let ctx = entry_ctx(it, ring)?;
    let n = perm.len();
    let mut m = Mat::zero(&ctx, n, n);
    let one_ = Elem::one(&ctx)?;
    for (i, &j) in perm.iter().enumerate() {
        m.set_entry(i, j, &one_);
    }
    mat_value(it, ring, m)
}

fn permutation_matrix_seq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let q = a.seq(1)?;
    let n = q.elems.len();
    let mut seen = vec![false; n];
    let mut perm = Vec::with_capacity(n);
    for x in &q.elems {
        let i = match x {
            Value::Int(v) => v.to_u64().filter(|&i| (1..=n as u64).contains(&i)).map(|i| i as usize - 1),
            _ => None,
        };
        match i {
            Some(i) if !seen[i] => {
                seen[i] = true;
                perm.push(i);
            }
            _ => return Err(RuntimeError::runtime(format!("Second argument is not a permutation of [1..{n}]"))),
        }
    }
    one(permutation(it, &ring, &perm)?)
}

fn permutation_matrix_perm(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let Value::Perm(p) = &a.args[1] else { return Err(bad()) };
    let perm: Vec<usize> = p.images.iter().map(|&x| x as usize).collect();
    one(permutation(it, &ring, &perm)?)
}

// ----- random matrices ------------------------------------------------------------------

/// A random element of the finite ring `ring` in its context.
fn random_entry(it: &mut Interp, ring: &Value, m: &mut Mat, i: usize, j: usize) -> RResult<()> {
    match *m.ctx().kind() {
        CtxKind::Nmod(n) => {
            let w = it.rng.below_u64(n);
            m.set_word(i, j, w);
        }
        _ => {
            let x = it.call_intrinsic_named(Sym::new("Random"), vec![ring.clone()])?;
            set_entry(it, ring, m, i, j, &x)?;
        }
    }
    Ok(())
}

fn random_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let (r, c) = (dim(a, 1, 2)?, dim(a, 2, 3)?);
    let finite = crate::rings::props::ring_props(&ring).is_some_and(|p| p.cardinality.is_some());
    if !finite {
        return Err(bare(RuntimeError::runtime("Ring must be finite")));
    }
    let ctx = entry_ctx(it, &ring)?;
    let mut m = Mat::zero(&ctx, r, c);
    for i in 0..r {
        for j in 0..c {
            random_entry(it, &ring, &mut m, i, j)?;
        }
    }
    one(mat_value(it, &ring, m)?)
}

/// A random integer in [-k, k].
fn small_random(it: &mut Interp, k: &Integer) -> Integer {
    it.rng.range(&-k, k)
}

/// The product of l random elementary matrices I + E over the integers,
/// E with one entry in [-k, k] off the diagonal, and with `signs` also
/// random diagonal signs.
fn random_elementary(it: &mut Interp, n: usize, k: &Integer, l: usize, signs: bool) -> RResult<Mat> {
    let ctx = calyx_flint::gr::Ctx::integers();
    let mut m = Mat::identity(&ctx, n)?;
    if n < 2 {
        return Ok(m);
    }
    for _ in 0..l {
        let i = it.rng.below_u64(n as u64) as usize;
        let mut j = it.rng.below_u64(n as u64 - 1) as usize;
        if j >= i {
            j += 1;
        }
        let c = Elem::from_integer(&ctx, &small_random(it, k))?;
        for col in 0..n {
            let x = m.entry(j, col);
            let y = m.entry(i, col).add(&c.mul(&x)?)?;
            m.set_entry(i, col, &y);
        }
    }
    if signs {
        for i in 0..n {
            if it.rng.below_u64(2) == 1 {
                for col in 0..n {
                    let y = m.entry(i, col).neg()?;
                    m.set_entry(i, col, &y);
                }
            }
        }
    }
    Ok(m)
}

fn random_sln_z(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = dim(a, 0, 1)?;
    let (k, l) = (a.int(1)?.clone(), dim(a, 2, 3)?);
    let m = random_elementary(it, n, &k, l, false)?;
    one(mat_value(it, &Value::integers(), m)?)
}

fn random_gln_z(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = dim(a, 0, 1)?;
    let (k, l) = (a.int(1)?.clone(), dim(a, 2, 3)?);
    let m = random_elementary(it, n, &k, l, true)?;
    one(mat_value(it, &Value::integers(), m)?)
}

fn random_unimodular(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = dim(a, 0, 1)?;
    let k = a.int(1)?.clone();
    let m = random_elementary(it, n, &k, 4 * n, true)?;
    one(mat_value(it, &Value::integers(), m)?)
}

fn random_symmetric(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let n = dim(a, 1, 2)?;
    let bound = if a.args.len() == 3 { Some(a.int(2)?.clone()) } else { None };
    let ctx = entry_ctx(it, &ring)?;
    let mut m = Mat::zero(&ctx, n, n);
    for i in 0..n {
        for j in 0..=i {
            match &bound {
                Some(k) => {
                    let x = small_random(it, k);
                    m.set_integer(i, j, &x)?;
                }
                None => random_entry(it, &ring, &mut m, i, j)?,
            }
            let x = m.entry(i, j);
            m.set_entry(j, i, &x);
        }
    }
    one(mat_value(it, &ring, m)?)
}

/// `RandomPositiveDefiniteSymmetricMatrix(n, M)`: B^T B + I for a random B
/// with entries in [-M, M].
fn random_positive_definite(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = dim(a, 0, 1)?;
    let k = a.int(1)?.clone();
    let ctx = calyx_flint::gr::Ctx::integers();
    let mut b = Mat::zero(&ctx, n, n);
    for i in 0..n {
        for j in 0..n {
            let x = small_random(it, &k);
            b.set_integer(i, j, &x)?;
        }
    }
    let m = b.transpose().mul(&b)?.add(&Mat::identity(&ctx, n)?)?;
    one(mat_value(it, &Value::integers(), m)?)
}

/// `RandomSymplecticMatrix(g, m)`: a product of random symplectic
/// transvection-like blocks [I S; 0 I] and [I 0; S I] for symmetric S.
fn random_symplectic(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let g = dim(a, 0, 1)?;
    let k = a.int(1)?.clone();
    let ctx = calyx_flint::gr::Ctx::integers();
    let mut m = Mat::identity(&ctx, 2 * g)?;
    for step in 0..4 {
        let mut s = Mat::zero(&ctx, g, g);
        for i in 0..g {
            for j in 0..=i {
                let x = small_random(it, &k);
                s.set_integer(i, j, &x)?;
                s.set_integer(j, i, &x)?;
            }
        }
        let mut t = Mat::identity(&ctx, 2 * g)?;
        if step % 2 == 0 {
            t.insert(&s, 0, g);
        } else {
            t.insert(&s, g, 0);
        }
        m = m.mul(&t)?;
    }
    one(mat_value(it, &Value::integers(), m)?)
}

// ----- vectors ----------------------------------------------------------------------------

/// The vector over `ring` with the entries of `q`, which must have length n.
fn vector(it: &mut Interp, ring: &Value, n: usize, q: &SeqEnum) -> RResult<Value> {
    if q.elems.len() != n {
        return Err(RuntimeError::runtime(format!("Sequence should have length {n}")));
    }
    let ctx = entry_ctx(it, ring)?;
    let mut m = Mat::zero(&ctx, 1, n);
    for (j, x) in q.elems.iter().enumerate() {
        if !set_entry(it, ring, &mut m, 0, j, x)? {
            return Err(coerce_failed(j + 1));
        }
    }
    vec_value(it, ring, m)
}

/// `Vector(n, Q)`, `Vector(Q)`, `Vector(R, n, Q)` and `Vector(R, Q)`.
fn vector_of(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let q = a.seq(a.args.len() - 1)?.clone();
    let (ring, n) = match a.args.len() {
        1 => (universe(it, &q)?, q.elems.len()),
        2 if matches!(a.args[0], Value::Int(_)) => (universe(it, &q)?, dim(a, 0, 1)?),
        2 => (ring_arg(a, 0)?, q.elems.len()),
        _ => (ring_arg(a, 0)?, dim(a, 1, 2)?),
    };
    one(vector(it, &ring, n, &q)?)
}

// ----- parents ----------------------------------------------------------------------------

fn matrix_algebra(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let n = dim(a, 1, 2)?;
    one(Value::Struct(parent(it, &ring, n, n, Shape::Algebra)?))
}

fn matrix_space(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let (r, c) = (dim(a, 1, 2)?, dim(a, 2, 3)?);
    one(Value::Struct(parent(it, &ring, r, c, Shape::Space)?))
}

/// `KMatrixSpace(K, m, n)`: `RMatrixSpace` for a field.
fn k_matrix_space(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    if !it.types.isa(a.args[0].type_id(), t::FLD) {
        return Err(RuntimeError::runtime("Argument 1 is not a field"));
    }
    matrix_space(it, a)
}

fn rspace(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let n = dim(a, 1, 2)?;
    one(Value::Struct(parent(it, &ring, 1, n, Shape::Tuples)?))
}

/// `P ! x` for a matrix algebra, matrix space or R-space P: a sequence of
/// entries (or rows), a matrix of the same shape, or (in an algebra) a
/// scalar.
pub fn coerce(it: &mut Interp, st: &Rc<Struct>, x: &Value) -> RResult<Result<Value, Option<String>>> {
    let p = info(st);
    let (ring, r, c) = (p.ring.clone(), p.nrows, p.ncols);
    let m = match x {
        Value::Seq(q) => match from_seq(it, &ring, r, c, q) {
            Ok(m) => m,
            Err(e) => return Ok(Err(Some(e.message.clone()))),
        },
        Value::Mat(b) if b.m.nrows() == r && b.m.ncols() == c => {
            if Rc::ptr_eq(&b.parent, st) {
                return Ok(Ok(x.clone()));
            }
            let mut m = Mat::zero(&p.ctx, r, c);
            for i in 0..r {
                for j in 0..c {
                    let e = entry_value(it, b, i, j);
                    if !set_entry(it, &ring, &mut m, i, j, &e)? {
                        return Ok(Err(None));
                    }
                }
            }
            m
        }
        Value::Int(n) if n.is_zero() => Mat::zero(&p.ctx, r, c),
        _ if p.shape == Shape::Algebra && !matches!(x, Value::Mat(_)) => {
            let mut m = Mat::zero(&p.ctx, r, c);
            for i in 0..r {
                if !set_entry(it, &ring, &mut m, i, i, x)? {
                    return Ok(Err(None));
                }
            }
            m
        }
        _ => return Ok(Err(None)),
    };
    Ok(Ok(Value::Mat(Rc::new(Mtrx { parent: st.clone(), m }))))
}

pub fn register(it: &mut Interp) {
    it.def("Matrix", "R::Rng, m::RngIntElt, n::RngIntElt, Q::SeqEnum -> Mtrx", "The m by n matrix over R given by Q.", matrix_rmnq);
    it.def("Matrix", "m::RngIntElt, n::RngIntElt, Q::SeqEnum -> Mtrx", "The m by n matrix given by Q.", matrix_mnq);
    it.def("Matrix", "R::Rng, n::RngIntElt, Q::[RngElt] -> Mtrx", "The matrix over R with rows of length n given by Q.", matrix_nq);
    it.def("Matrix", "n::RngIntElt, Q::[RngElt] -> Mtrx", "The matrix with rows of length n given by Q.", matrix_nq);
    it.def("Matrix", "Q::[Mtrx] -> Mtrx", "The matrix whose rows are the vectors (or the entries of the matrices) in Q.", matrix_rows);
    // Magma writes the forms taking sequences of sequences in its own language.
    it.def("Matrix", "Q::[SeqEnum] -> Mtrx", "The matrix with the rows Q.", matrix_rows).package = true;
    it.def("Matrix", "R::Rng, Q::[SeqEnum] -> Mtrx", "The matrix over R with the rows Q.", matrix_rows).package = true;
    it.def("Matrix", "A::Mtrx -> Mtrx", "A in the matrix algebra or space of its shape.", matrix_of);
    it.def("ZeroMatrix", "R::Rng, m::RngIntElt, n::RngIntElt -> Mtrx", "The m by n zero matrix over R.", zero_matrix).package = true;
    it.def("IdentityMatrix", "R::Rng, n::RngIntElt -> Mtrx", "The n by n identity matrix over R.", identity_matrix).package = true;
    it.def("ScalarMatrix", "n::RngIntElt, s::RngElt -> Mtrx", "The n by n scalar matrix s.", scalar_matrix);
    it.def("ScalarMatrix", "R::Rng, n::RngIntElt, s::RngElt -> Mtrx", "The n by n scalar matrix s over R.", scalar_matrix);
    it.def("DiagonalMatrix", "R::Rng, n::RngIntElt, Q::SeqEnum -> Mtrx", "The n by n diagonal matrix over R with diagonal Q.", diagonal_matrix).package = true;
    it.def("DiagonalMatrix", "R::Rng, Q::SeqEnum -> Mtrx", "The diagonal matrix over R with diagonal Q.", diagonal_matrix).package = true;
    it.def("DiagonalMatrix", "Q::SeqEnum -> Mtrx", "The diagonal matrix with diagonal Q.", diagonal_matrix).package = true;
    for (name, f) in [
        ("LowerTriangularMatrix", lower_triangular as crate::intrinsics::NativeFn),
        ("UpperTriangularMatrix", upper_triangular),
        ("SymmetricMatrix", symmetric),
        ("AntisymmetricMatrix", antisymmetric),
    ] {
        it.def(name, "Q::SeqEnum -> Mtrx", "The matrix given by the entries Q of a triangle.", f);
        it.def(name, "R::Rng, Q::SeqEnum -> Mtrx", "The matrix over R given by the entries Q of a triangle.", f);
    }
    it.def("PermutationMatrix", "R::Rng, Q::[RngIntElt] -> Mtrx", "The permutation matrix over R of Q.", permutation_matrix_seq);
    it.def("PermutationMatrix", "R::Rng, x::GrpPermElt -> Mtrx", "The permutation matrix over R of x.", permutation_matrix_perm);
    // Magma writes the random generators in its own language.
    let random: [(&str, &str, &str, crate::intrinsics::NativeFn); 8] = [
        ("RandomMatrix", "R::Rng, m::RngIntElt, n::RngIntElt -> Mtrx", "A random m by n matrix over the finite ring R.", random_matrix),
        ("RandomUnimodularMatrix", "n::RngIntElt, M::RngIntElt -> Mtrx", "A random n by n integral matrix of determinant 1 or -1.", random_unimodular),
        ("RandomSLnZ", "n::RngIntElt, k::RngIntElt, l::RngIntElt -> AlgMatElt", "A random element of SL(n, Z).", random_sln_z),
        ("RandomGLnZ", "n::RngIntElt, k::RngIntElt, l::RngIntElt -> AlgMatElt", "A random element of GL(n, Z).", random_gln_z),
        ("RandomSymplecticMatrix", "g::RngIntElt, m::RngIntElt -> Mtrx", "A random 2g by 2g integral symplectic matrix.", random_symplectic),
        ("RandomSymmetricMatrix", "R::Rng, n::RngIntElt -> AlgMatElt", "A random n by n symmetric matrix over R.", random_symmetric),
        ("RandomSymmetricMatrix", "R::Rng, n::RngIntElt, M::RngIntElt -> AlgMatElt", "A random symmetric matrix with entries in [-M, M].", random_symmetric),
        ("RandomPositiveDefiniteSymmetricMatrix", "n::RngIntElt, M::RngIntElt -> AlgMatElt", "A random positive definite matrix.", random_positive_definite),
    ];
    for (name, sig, doc, f) in random {
        it.def(name, sig, doc, f).package = true;
    }
    it.def("Vector", "n::RngIntElt, Q::SeqEnum -> ModTupRngElt", "The vector of length n with entries Q.", vector_of);
    it.def("Vector", "Q::SeqEnum -> ModTupRngElt", "The vector with entries Q.", vector_of);
    it.def("Vector", "R::Rng, n::RngIntElt, Q::SeqEnum -> ModTupRngElt", "The vector over R of length n with entries Q.", vector_of);
    it.def("Vector", "R::Rng, Q::SeqEnum -> ModTupRngElt", "The vector over R with entries Q.", vector_of);
    for name in ["MatrixAlgebra", "MatrixRing"] {
        it.def(name, "R::Rng, n::RngIntElt -> AlgMat", "The full matrix algebra of degree n over R.", matrix_algebra);
    }
    it.def("RMatrixSpace", "R::Rng, m::RngIntElt, n::RngIntElt -> ModMatRng", "The full space of m by n matrices over R.", matrix_space);
    it.def("KMatrixSpace", "K::Rng, m::RngIntElt, n::RngIntElt -> ModMatFld", "The full space of m by n matrices over K.", k_matrix_space);
    it.def("RSpace", "R::Rng, n::RngIntElt -> ModTupRng", "The full R-space of degree n.", rspace);
    for name in ["VectorSpace", "KSpace"] {
        it.def(name, "K::Fld, n::RngIntElt -> ModTupFld", "The full vector space of degree n over K.", rspace);
    }
}
