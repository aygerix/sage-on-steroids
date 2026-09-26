//! Linear algebra: the transpose, rank, determinant and trace, minors and
//! the adjoint, echelon and Hermite forms, and the nullspaces and solutions
//! of linear systems V·A = W.
//!
//! Over a field the echelon form comes with Magma's transformation matrix
//! (`Mat::echelon_transform`), which also gives the particular solutions of
//! `Solution` and `IsConsistent`. Over the integers the echelon form is the
//! Hermite form, with a transformation made small by LLL, and kernels are
//! Hermite forms too, though `KernelMatrix` shapes its basis as Magma does
//! (as it does over the rationals). Over Z/nZ for composite n the echelon
//! form is Magma's, made by extended gcds, and kernels are Howell forms.

use std::rc::Rc;

use calyx_flint::gr::{CtxKind, Elem, GrError, Truth};
use calyx_flint::mat::Mat;
use calyx_flint::{Integer, Rational};

use super::spaces::subspace;
use super::{Mtrx, Shape, like, mat_arg, mat_value, over_ring_of, parent, square, vec_value};
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::{boolv, intv, one};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

pub(super) fn gr(e: GrError) -> RuntimeError {
    crate::rings::gr_error(e, "Arithmetic failed")
}

/// The kinds of rings the linear algebra here knows.
#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Field,
    Integers,
    /// The integers modulo a composite.
    Residue,
    Other,
}

fn kind(x: &Mtrx) -> Kind {
    match x.m.ctx().kind() {
        CtxKind::Integers => Kind::Integers,
        _ if x.info().field && x.m.over_field() => Kind::Field,
        CtxKind::Nmod(_) | CtxKind::FmpzMod(_) => Kind::Residue,
        _ => Kind::Other,
    }
}

fn unsupported(what: &str) -> RuntimeError {
    RuntimeError::runtime(format!("{what} of matrices over this ring is not supported"))
}

// ----- transpose, rank, determinant, trace -----------------------------------------

fn transpose(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    one(over_ring_of(it, &x, x.m.transpose())?)
}

/// The rank of a matrix: over a field, the integers, Z/nZ (the number of
/// nonzero rows of the echelon form) or any integral domain FLINT knows.
pub fn rank_of(x: &Mtrx) -> RResult<usize> {
    match kind(x) {
        Kind::Field | Kind::Integers => x.m.rank().map_err(gr),
        Kind::Residue => Ok(echelon_mod(&x.m).2),
        Kind::Other => x.m.rank().map_err(|_| unsupported("The rank")),
    }
}

fn rank(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &proof_params(), &[])?;
    let x = mat_arg(a, 0)?.clone();
    intv(Integer::from_u64(rank_of(&x)? as u64))
}

fn determinant(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &proof_params(), &[])?;
    let x = square(a, 0)?;
    let d = x.m.det().map_err(gr)?;
    one(it.elem_to_value(x.ring(), d))
}

fn trace(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    let t = x.m.trace().map_err(gr)?;
    one(it.elem_to_value(x.ring(), t))
}

/// `TraceOfProduct(A, B)`: the sum of the products A[i, j]·B[j, i].
fn trace_of_product(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y) = (square(a, 0)?, square(a, 1)?);
    if x.m.nrows() != y.m.nrows() {
        return Err(RuntimeError::runtime("Arguments have incompatible degrees"));
    }
    let Some((ring, p, q)) = super::arith::over_common(it, &x, &y)? else {
        return Err(RuntimeError::runtime("Arguments have incompatible coefficient rings"));
    };
    let n = p.nrows();
    let mut t = Elem::zero(p.ctx());
    for i in 0..n {
        for j in 0..n {
            t = t.add(&p.entry(i, j).mul(&q.entry(j, i)).map_err(gr)?).map_err(gr)?;
        }
    }
    one(it.elem_to_value(&ring, t))
}

// ----- minors and the adjoint --------------------------------------------------------

/// The index arguments of `Minor` and `Cofactor`, from 0.
fn row_col(a: &CallArgs, x: &Mtrx) -> RResult<(usize, usize)> {
    let n = x.m.nrows();
    let ix = |k: usize| -> RResult<usize> {
        match &a.args[k] {
            Value::Int(v) => match v.to_u64() {
                Some(i) if (1..=n as u64).contains(&i) => Ok(i as usize - 1),
                _ => Err(RuntimeError::runtime(format!("Argument {} ({v}) should be in the range [1 .. {n}]", k + 1))),
            },
            _ => Err(super::bad()),
        }
    };
    Ok((ix(1)?, ix(2)?))
}

/// The matrix without row i and column j.
fn without(m: &Mat, i: usize, j: usize) -> Mat {
    let (r, c) = (m.nrows(), m.ncols());
    m.select(&(0..r).filter(|&k| k != i).collect::<Vec<_>>(), &(0..c).filter(|&k| k != j).collect::<Vec<_>>())
}

fn minor(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    let (i, j) = row_col(a, &x)?;
    let d = without(&x.m, i, j).det().map_err(gr)?;
    one(it.elem_to_value(x.ring(), d))
}

/// Argument k, a sequence of indices from 1 to n: the indices from 0.
fn indices(a: &CallArgs, k: usize, n: usize) -> RResult<Vec<usize>> {
    let q = a.seq(k)?;
    q.elems
        .iter()
        .map(|v| match v {
            Value::Int(i) => match i.to_u64() {
                Some(i) if (1..=n as u64).contains(&i) => Ok(i as usize - 1),
                _ => Err(RuntimeError::runtime(format!("Argument {} contains an index out of range", k + 1))),
            },
            _ => Err(super::bad()),
        })
        .collect()
}

/// `Minor(M, I, J)`: the determinant of the rows I and columns J of M.
fn minor_seqs(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let (rows, cols) = (indices(a, 1, x.m.nrows())?, indices(a, 2, x.m.ncols())?);
    if rows.len() != cols.len() {
        return Err(RuntimeError::runtime("Arguments 2 and 3 should have the same length"));
    }
    let d = x.m.select(&rows, &cols).det().map_err(gr)?;
    one(it.elem_to_value(x.ring(), d))
}

fn cofactor(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    let (i, j) = row_col(a, &x)?;
    let d = without(&x.m, i, j).det().map_err(gr)?;
    let d = if (i + j) % 2 == 1 { d.neg().map_err(gr)? } else { d };
    one(it.elem_to_value(x.ring(), d))
}

/// The subsets of {0, ..., n-1} of size r, in reverse lexicographic order.
fn subsets(n: usize, r: usize) -> Vec<Vec<usize>> {
    fn go(start: usize, n: usize, r: usize, cur: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if cur.len() == r {
            out.push(cur.clone());
            return;
        }
        for k in start..n {
            cur.push(k);
            go(k + 1, n, r, cur, out);
            cur.pop();
        }
    }
    let mut out = Vec::new();
    go(0, n, r, &mut Vec::new(), &mut out);
    out.reverse();
    out
}

/// The r by r minors of M, the column sets outermost, each set of rows or
/// columns in reverse lexicographic order; if `signed`, the minor on rows I
/// and columns J times (-1)^(ΣI + ΣJ) (for r = n - 1, the entries of the
/// adjoint).
fn minors_of(it: &mut Interp, a: &CallArgs, signed: bool) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let (m, n) = (x.m.nrows(), x.m.ncols());
    let r = match a.args.get(1) {
        Some(Value::Int(r)) => match r.to_u64() {
            Some(r) if r as usize <= m.min(n) => r as usize,
            _ => return Err(RuntimeError::runtime(format!("Argument 2 ({r}) should be in the range [0 .. {}]", m.min(n)))),
        },
        _ => {
            if m != n {
                return Err(RuntimeError::runtime("Argument 1 is not square"));
            }
            m.saturating_sub(1)
        }
    };
    let (rs, cs) = (subsets(m, r), subsets(n, r));
    let mut out = Vec::with_capacity(rs.len() * cs.len());
    for c in &cs {
        for rw in &rs {
            let d = x.m.select(rw, c).det().map_err(gr)?;
            let odd = (rw.iter().sum::<usize>() + c.iter().sum::<usize>()) % 2 == 1;
            let d = if signed && odd { d.neg().map_err(gr)? } else { d };
            out.push(it.elem_to_value(x.ring(), d));
        }
    }
    one(Value::seq(Some(x.ring().clone()), out))
}

fn minors(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    minors_of(it, a, false)
}

fn cofactors(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    minors_of(it, a, true)
}

/// The adjoint (adjugate) of a square matrix: det(A)·A^-1 when A is
/// invertible over a field, and otherwise (-1)^(n+1)·(A^(n-1) + c[n-1]·A^(n-2)
/// + ... + c[1]) from the characteristic polynomial x^n + c[n-1]·x^(n-1) +
/// ... + c[0], by Cayley-Hamilton.
pub fn adjoint_of(m: &Mat) -> RResult<Mat> {
    let n = m.nrows();
    if m.over_field() {
        let d = m.det().map_err(gr)?;
        if d.is_zero() != Truth::True {
            return m.inv().map_err(gr)?.mul_scalar(&d).map_err(gr);
        }
    }
    let c = m.charpoly().map_err(gr)?;
    let mut q = Mat::identity(m.ctx(), n).map_err(gr)?;
    for k in (1..n).rev() {
        q = q.mul(m).map_err(gr)?.add(&Mat::scalar(n, &c[k]).map_err(gr)?).map_err(gr)?;
    }
    if n % 2 == 0 { q.neg().map_err(gr) } else { Ok(q) }
}

fn adjoint(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    let adj = adjoint_of(&x.m)?;
    let ring = x.ring().clone();
    one(mat_value(it, &ring, adj)?)
}

fn is_unit(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    let d = x.m.det().map_err(gr)?;
    boolv(d.is_invertible() == Truth::True)
}

fn is_singular(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    let d = x.m.det().map_err(gr)?;
    boolv(d.is_zero() == Truth::True)
}

// ----- Pfaffians ---------------------------------------------------------------------

fn not_anti_symmetric() -> RuntimeError {
    crate::intrinsics::require(RuntimeError::runtime("Argument must be an anti-symmetric matrix"))
}

/// Whether a matrix is anti-symmetric: square, with M[j, i] = -M[i, j] (so
/// in characteristic 2 any symmetric matrix is).
fn anti_symmetric(m: &Mat) -> RResult<bool> {
    let n = m.nrows();
    if m.ncols() != n {
        return Ok(false);
    }
    for i in 0..n {
        for j in i..n {
            if m.entry(i, j).add(&m.entry(j, i)).map_err(gr)?.is_zero() != Truth::True {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

/// The Pfaffian of an anti-symmetric matrix, from the entries above the
/// diagonal; zero when the size is odd and, as in Magma, when it is 0.
/// Over a field or the integers (`eliminate`) it comes from a fraction-free
/// elimination: pivoting on the entry at (2k, 2k + 1) makes each entry
/// further on the Pfaffian of the principal submatrix on the pivots and
/// its own row and column, divided exactly by the previous pivot, and the
/// last pivot is the Pfaffian. Elsewhere, and over the floating-point
/// reals (whose rounding then follows Magma's), it is the expansion along
/// the first row, with each smaller Pfaffian computed once.
fn pfaffian_of(m: &Mat, eliminate: bool) -> RResult<Elem> {
    let (n, ctx) = (m.nrows(), m.ctx());
    if n == 0 || n % 2 == 1 {
        return Ok(Elem::zero(ctx));
    }
    if !eliminate {
        return pfaffian_expanded(m);
    }
    let mut a: Vec<Vec<Elem>> = (0..n).map(|i| (0..n).map(|j| m.entry(i, j)).collect()).collect();
    // The rows and columns in their current order, and the sign the swaps
    // bringing nonzero pivots into place have made.
    let mut ord: Vec<usize> = (0..n).collect();
    let (mut prev, mut neg) = (Elem::one(ctx).map_err(gr)?, false);
    for k in (0..n).step_by(2) {
        let u = ord[k];
        let Some(j) = (k + 1..n).find(|&j| a[u][ord[j]].is_zero() != Truth::True) else {
            return Ok(Elem::zero(ctx));
        };
        if j != k + 1 {
            ord.swap(k + 1, j);
            neg = !neg;
        }
        let v = ord[k + 1];
        let b = a[u][v].clone();
        if k + 2 == n {
            return if neg { b.neg().map_err(gr) } else { Ok(b) };
        }
        for i in k + 2..n {
            for l in i + 1..n {
                let (p, q) = (ord[i], ord[l]);
                let t = b.mul(&a[p][q]).map_err(gr)?.sub(&a[u][p].mul(&a[v][q]).map_err(gr)?).map_err(gr)?;
                let t = t.add(&a[u][q].mul(&a[v][p]).map_err(gr)?).map_err(gr)?.divexact(&prev).map_err(gr)?;
                a[q][p] = t.neg().map_err(gr)?;
                a[p][q] = t;
            }
        }
        prev = b;
    }
    unreachable!("the last pivot ends the elimination")
}

/// The Pfaffian of an anti-symmetric matrix of even size by expansion along
/// the first row: Pf(S) = Σ ±M[s, t]·Pf(S - {s, t}) over the indices t of
/// S after its first s, the signs alternating from +.
fn pfaffian_expanded(m: &Mat) -> RResult<Elem> {
    // The Pfaffians of the principal submatrices on the index sets s.
    fn pf(m: &Mat, s: u128, memo: &mut std::collections::HashMap<u128, Elem>) -> RResult<Elem> {
        let first = s.trailing_zeros() as usize;
        let rest = s & (s - 1);
        if rest.count_ones() == 1 {
            return Ok(m.entry(first, rest.trailing_zeros() as usize));
        }
        if let Some(x) = memo.get(&s) {
            return Ok(x.clone());
        }
        let (mut sum, mut r, mut plus) = (Elem::zero(m.ctx()), rest, true);
        while r != 0 {
            let t = r.trailing_zeros() as usize;
            r &= r - 1;
            let term = m.entry(first, t).mul(&pf(m, rest & !(1 << t), memo)?).map_err(gr)?;
            sum = if plus { sum.add(&term) } else { sum.sub(&term) }.map_err(gr)?;
            plus = !plus;
        }
        if memo.len() < 1 << 20 {
            memo.insert(s, sum.clone());
        }
        Ok(sum)
    }
    let n = m.nrows();
    if n > 128 {
        return Err(RuntimeError::runtime("The matrix is too large to expand its Pfaffian"));
    }
    pf(m, if n == 128 { u128::MAX } else { (1 << n) - 1 }, &mut std::collections::HashMap::new())
}

/// Whether the Pfaffians over the ring of x come from an elimination.
fn eliminates(x: &Mtrx) -> bool {
    matches!(kind(x), Kind::Field | Kind::Integers) && !x.m.floating()
}

/// `Pfaffian(M)` and `Pfaffian(M, I, J)`, the latter of the rows I and
/// columns J of M.
fn pfaffian(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let m = if a.args.len() > 1 { x.m.select(&indices(a, 1, x.m.nrows())?, &indices(a, 2, x.m.ncols())?) } else { x.m.clone() };
    if !anti_symmetric(&m)? {
        return Err(not_anti_symmetric());
    }
    let pf = pfaffian_of(&m, eliminates(&x))?;
    one(it.elem_to_value(x.ring(), pf))
}

/// `Pfaffians(M, r)`: the Pfaffians of the principal r by r submatrices of
/// M, in the order of `Subsets({1..n}, r)`.
fn pfaffians(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    if !anti_symmetric(&x.m)? {
        return Err(not_anti_symmetric());
    }
    let n = x.m.nrows();
    let r = match &a.args[1] {
        Value::Int(r) => r.to_u64().filter(|&r| (1..=n as u64).contains(&r)),
        _ => None,
    };
    let Some(r) = r else {
        let msg = "Second argument must be positive integer less than or equal to the number of rows of the first";
        return Err(crate::intrinsics::require(RuntimeError::runtime(msg)));
    };
    let all = Value::Set(Rc::new(SetEnum::range(Integer::one(), &Integer::from_u64(n as u64), Integer::one())));
    let sets = it.call_intrinsic_named(crate::sym::Sym::new("Subsets"), vec![all, Value::Int(Integer::from_u64(r))])?;
    let mut sets = it.iter_value(&sets, false)?;
    let eliminate = eliminates(&x);
    let mut out = Vec::new();
    while let Some((_, s)) = sets.next_item() {
        let Value::Set(s) = s else { unreachable!("a set of indices") };
        let mut ix: Vec<usize> = s.iter().map(|v| if let Value::Int(i) = v { i.to_u64().expect("an index") as usize - 1 } else { unreachable!() }).collect();
        ix.sort_unstable();
        let pf = pfaffian_of(&x.m.select(&ix, &ix), eliminate)?;
        out.push(it.elem_to_value(x.ring(), pf));
    }
    one(Value::seq(Some(x.ring().clone()), out))
}

// ----- the integers ------------------------------------------------------------------

/// A basis of the lattice {v in Z^m : v·A = 0} of a matrix over the
/// integers, in Hermite form (which makes it unique).
fn integer_kernel(m: &Mat) -> Mat {
    let (r, ctx) = (m.nrows(), m.ctx().clone());
    let null = m.transpose().nullspace_z();
    match null.ncols() {
        0 => Mat::zero(&ctx, 0, r),
        // One vector: the primitive one.
        1 => {
            let v = null.transpose();
            let g = (0..r).fold(Integer::zero(), |g, j| g.gcd(&v.integer(0, j)));
            let lead = (0..r).map(|j| v.integer(0, j)).find(|x| !x.is_zero()).map_or(1, |x| x.sign());
            let g = if lead < 0 { -&g } else { g };
            let mut k = Mat::zero(&ctx, 1, r);
            for j in 0..r {
                k.set_integer(0, j, &v.integer(0, j).divexact(&g)).expect("an integer");
            }
            k
        }
        d => {
            let (_, u) = m.hnf_transform();
            u.block(r - d, 0, d, r).hnf()
        }
    }
}

/// The basis of the lattice {v in Z^m : v·A = 0} that `KernelMatrix` gives:
/// on the pivot columns of its Hermite form it is lower triangular, with a
/// positive diagonal and each entry left of the diagonal reduced into
/// (-d, 0] for d the diagonal entry of its column. It is the Hermite form
/// with those columns first in reverse order, rows reversed and reduced.
fn integer_kernel_matrix(m: &Mat) -> Mat {
    let h = integer_kernel(m);
    let (k, r) = (h.nrows(), h.ncols());
    if k < 2 {
        return h;
    }
    let pivots: Vec<usize> = (0..k).map(|i| (0..r).find(|&c| !h.entry_is_zero(i, c)).expect("a nonzero row")).collect();
    let mut perm: Vec<usize> = pivots.iter().rev().copied().collect();
    perm.extend((0..r).filter(|c| !pivots.contains(c)));
    let g = h.select(&(0..k).collect::<Vec<_>>(), &perm).hnf();
    let mut at = vec![0; r];
    for (i, &c) in perm.iter().enumerate() {
        at[c] = i;
    }
    let mut b: Vec<Vec<Integer>> = (0..k).rev().map(|i| (0..r).map(|c| g.integer(i, at[c])).collect()).collect();
    for j in (0..k).rev() {
        let d = b[j][pivots[j]].clone();
        for i in j + 1..k {
            let q = b[i][pivots[j]].cdiv_q(&d).expect("a nonzero pivot");
            if !q.is_zero() {
                for c in 0..r {
                    b[i][c] = &b[i][c] - &(&q * &b[j][c]);
                }
            }
        }
    }
    let mut out = Mat::zero(h.ctx(), k, r);
    for (i, row) in b.iter().enumerate() {
        for (c, x) in row.iter().enumerate() {
            out.set_integer(i, c, x).expect("an integer");
        }
    }
    out
}

/// The kernel matrix over the rationals, as Magma gives it: the reduced
/// echelon basis with each row scaled to integers without a common factor.
fn rational_kernel_matrix(m: &Mat) -> RResult<Mat> {
    let (mut e, _) = m.left_kernel().map_err(gr)?.rref().map_err(gr)?;
    for i in 0..e.nrows() {
        let row: Vec<Rational> = (0..e.ncols()).map(|j| e.entry(i, j).to_rational().expect("a rational")).collect();
        let den = Rational::from_integer(&row.iter().fold(Integer::one(), |d, q| d.lcm(&q.denominator())));
        for (j, q) in row.iter().enumerate() {
            e.set_rational(i, j, &(q * &den)).map_err(gr)?;
        }
    }
    Ok(e)
}

/// The rows of the integer matrix `u` less the nearest vectors of the
/// lattice with the LLL-reduced basis `k` (Babai's nearest plane: the
/// multiples of the basis vectors are rounded in turn from the last).
fn reduce_by(u: &mut Mat, k: &Mat) {
    let (d, n) = (k.nrows(), k.ncols());
    if d == 0 || u.nrows() == 0 {
        return;
    }
    // The Gram-Schmidt vectors of k over Q, and their squared lengths.
    let q = |x: &Integer| Rational::from_integer(x);
    let mut gs: Vec<Vec<Rational>> = Vec::with_capacity(d);
    let mut norms: Vec<Rational> = Vec::with_capacity(d);
    for i in 0..d {
        let mut v: Vec<Rational> = (0..n).map(|j| q(&k.integer(i, j))).collect();
        for l in 0..i {
            let dot = (0..n).fold(Rational::zero(), |s, j| &s + &(&q(&k.integer(i, j)) * &gs[l][j]));
            let mu = dot.checked_div(&norms[l]).expect("a nonzero length");
            for j in 0..n {
                v[j] = &v[j] - &(&mu * &gs[l][j]);
            }
        }
        norms.push(v.iter().fold(Rational::zero(), |s, x| &s + &(x * x)));
        gs.push(v);
    }
    for row in 0..u.nrows() {
        let mut x: Vec<Integer> = (0..n).map(|j| u.integer(row, j)).collect();
        for l in (0..d).rev() {
            let dot = (0..n).fold(Rational::zero(), |s, j| &s + &(&q(&x[j]) * &gs[l][j]));
            let c = dot.checked_div(&norms[l]).expect("a nonzero length").round();
            if !c.is_zero() {
                for j in 0..n {
                    x[j] = &x[j] - &(&c * &k.integer(l, j));
                }
            }
        }
        for (j, v) in x.iter().enumerate() {
            u.set_integer(row, j, v).expect("an integer");
        }
    }
}

/// The Hermite form H of an integer matrix, with (if wanted) a unimodular
/// T such that T·A = H whose entries are small: its rows for the zero rows
/// of H are an LLL-reduced basis of the kernel lattice, and the others are
/// reduced by them.
fn hermite(m: &Mat, want_t: bool) -> (Mat, Option<Mat>) {
    if !want_t {
        return (m.hnf(), None);
    }
    let (h, u) = m.hnf_transform();
    let rows = m.nrows();
    let rank = (0..rows).take_while(|&i| (0..h.ncols()).any(|j| !h.entry_is_zero(i, j))).count();
    let mut kern = u.block(rank, 0, rows - rank, rows);
    if rows > rank {
        let mut unused = Mat::identity(m.ctx(), rows - rank).expect("an identity");
        kern.lll_transform(&mut unused);
    }
    let mut top = u.block(0, 0, rank, rows);
    reduce_by(&mut top, &kern);
    let mut t = Mat::zero(m.ctx(), rows, rows);
    t.insert(&top, 0, 0);
    t.insert(&kern, rank, 0);
    (h, Some(t))
}

// ----- the integers modulo a composite -------------------------------------------------

/// The modulus n of a matrix over Z/nZ.
fn modulus(m: &Mat) -> Integer {
    match m.ctx().kind() {
        CtxKind::Nmod(n) => Integer::from_u64(*n),
        CtxKind::FmpzMod(n) => n.clone(),
        _ => unreachable!("a matrix over a residue ring"),
    }
}

/// The residues in [0, n) of the entries of a matrix over Z/nZ, by rows.
fn residues(m: &Mat) -> Vec<Vec<Integer>> {
    (0..m.nrows()).map(|i| (0..m.ncols()).map(|j| m.entry(i, j).to_integer().expect("a residue")).collect()).collect()
}

/// The matrix over the ring of `like` with the given rows of residues.
fn from_residues(like: &Mat, rows: &[Vec<Integer>], ncols: usize) -> Mat {
    let mut m = Mat::zero(like.ctx(), rows.len(), ncols);
    for (i, row) in rows.iter().enumerate() {
        for (j, x) in row.iter().enumerate() {
            m.set_integer(i, j, x).expect("a residue");
        }
    }
    m
}

fn modn(x: &Integer, n: &Integer) -> Integer {
    x.fdiv_qr(n).expect("a nonzero modulus").1
}

/// The residue of least absolute value (n/2 rather than -n/2).
fn balanced(x: &Integer, n: &Integer) -> Integer {
    if &(x + x) <= n { x.clone() } else { x - n }
}

/// A unit u of Z/nZ with u·p the divisor gcd(p, n) of n: the inverse of
/// p/g for p of least absolute value, moved by multiples of n/g until it is
/// a unit.
fn normalizer(p: &Integer, n: &Integer) -> Integer {
    let g = p.gcd(n);
    let (base, step) = (balanced(p, n).divexact(&g), n.divexact(&g));
    for k in 0u64.. {
        for s in [1i64, -1] {
            let c = &base + &(&step * &Integer::from_i64(s * k as i64));
            if let Some(u) = c.invmod(n) {
                return u;
            }
        }
    }
    unreachable!("a unit in each class modulo n/g")
}

/// Rows k and i of both `w` and `t` become a·(row k) + b·(row i) and
/// c·(row k) + d·(row i), modulo n.
fn mix(w: &mut [Vec<Integer>], t: &mut [Vec<Integer>], k: usize, i: usize, [a, b, c, d]: [&Integer; 4], n: &Integer) {
    for rows in [w, t] {
        for j in 0..rows[k].len() {
            let (x, y) = (rows[k][j].clone(), rows[i][j].clone());
            rows[k][j] = modn(&(&(a * &x) + &(b * &y)), n);
            rows[i][j] = modn(&(&(c * &x) + &(d * &y)), n);
        }
    }
}

/// Magma's echelon form of a matrix over Z/nZ, n composite, with T such
/// that T·A = E, and its rank (the number of nonzero rows). The rows are
/// taken in turn and reduced by the pivots found so far, in the order
/// found: an entry that is a multiple of the pivot is cleared with the
/// pivot row, and any other is merged into it by the unimodular step of
/// the extended gcd of the two (as residues of least absolute value). A
/// row left nonzero gives a new pivot, scaled by a unit to a divisor of n;
/// a zero row changes places with the last row not yet taken. Last the
/// entries above each pivot are reduced below it and the rows sorted by
/// their pivots. Unlike the Howell form this keeps to the rows of A.
fn echelon_mod(a: &Mat) -> (Mat, Mat, usize) {
    let (m, c, n) = (a.nrows(), a.ncols(), modulus(a));
    let (zero, one) = (Integer::zero(), Integer::one());
    let mut w = residues(a);
    let mut t: Vec<Vec<Integer>> = (0..m).map(|i| (0..m).map(|j| if i == j { one.clone() } else { zero.clone() }).collect()).collect();
    let mut piv: Vec<(usize, usize)> = Vec::new();
    let (mut i, mut last) = (0, m);
    while i < last {
        for &(col, k) in &piv {
            let (e, p) = (w[i][col].clone(), w[k][col].clone());
            if e.is_zero() {
                continue;
            }
            let (q, r) = e.fdiv_qr(&p).expect("a nonzero pivot");
            if r.is_zero() {
                mix(&mut w, &mut t, k, i, [&one, &zero, &-&q, &one], &n);
                continue;
            }
            let (p, e) = (balanced(&p, &n), balanced(&e, &n));
            let (g, s, v) = p.xgcd(&e);
            mix(&mut w, &mut t, k, i, [&s, &v, &-&e.divexact(&g), &p.divexact(&g)], &n);
        }
        match (0..c).find(|&j| !w[i][j].is_zero()) {
            Some(j) => {
                let u = normalizer(&w[i][j], &n);
                mix(&mut w, &mut t, i, i, [&u, &zero, &u, &zero], &n);
                piv.push((j, i));
                i += 1;
            }
            None => {
                last -= 1;
                w.swap(i, last);
                t.swap(i, last);
            }
        }
    }
    for &(col, k) in &piv {
        let p = w[k][col].clone();
        for &(col2, k2) in &piv {
            if col2 < col {
                let q = w[k2][col].fdiv_qr(&p).expect("a nonzero pivot").0;
                if !q.is_zero() {
                    mix(&mut w, &mut t, k, k2, [&one, &zero, &-&q, &one], &n);
                }
            }
        }
    }
    let mut sorted = piv.clone();
    sorted.sort();
    let mut order: Vec<usize> = sorted.iter().map(|&(_, k)| k).collect();
    order.extend((0..m).filter(|r| !piv.iter().any(|&(_, k)| k == *r)));
    let e: Vec<Vec<Integer>> = order.iter().map(|&r| w[r].clone()).collect();
    let tt: Vec<Vec<Integer>> = order.iter().map(|&r| t[r].clone()).collect();
    (from_residues(a, &e, c), from_residues(a, &tt, m), piv.len())
}

/// The kernel {v : v·A = 0} of a matrix over Z/nZ in Howell form, as Magma
/// echelonizes it: the Hermite form, reduced modulo n, of the lattice of
/// integer vectors v with v·A ≡ 0 (mod n). That lattice is the second
/// block of the rows of the Hermite form of [A | I; n·I | 0] that are zero
/// in the first.
fn kernel_mod(a: &Mat) -> Mat {
    let (m, c, n) = (a.nrows(), a.ncols(), modulus(a));
    let z = calyx_flint::gr::Ctx::integers();
    let mut g = Mat::zero(&z, m + c, c + m);
    for (i, row) in residues(a).iter().enumerate() {
        for (j, x) in row.iter().enumerate() {
            g.set_integer(i, j, x).expect("an integer");
        }
        g.set_integer(i, c + i, &Integer::one()).expect("an integer");
    }
    for j in 0..c {
        g.set_integer(m + j, j, &n).expect("an integer");
    }
    let h = g.hnf();
    let rows: Vec<Vec<Integer>> = (0..m + c)
        .filter(|&i| (0..c).all(|j| h.entry_is_zero(i, j)))
        .map(|i| (0..m).map(|j| modn(&h.integer(i, c + j), &n)).collect::<Vec<_>>())
        .filter(|r| r.iter().any(|x| !x.is_zero()))
        .collect();
    from_residues(a, &rows, m)
}

/// Solutions of V·A = W over Z/nZ: W written in the rows of the echelon
/// form of A, and V the same combination of the rows of its transformation;
/// failing that (the echelon form need not be a Howell form), a solution of
/// V·A + Z·n = W over the integers.
fn solve_mod(a: &Mat, w: &Mat) -> RResult<Option<Mat>> {
    let (m, c, n) = (a.nrows(), a.ncols(), modulus(a));
    let (e, t, r) = echelon_mod(a);
    let (ev, wv) = (residues(&e), residues(w));
    let pivots: Vec<usize> = (0..r).map(|i| (0..c).find(|&j| !ev[i][j].is_zero()).expect("a pivot")).collect();
    let mut coeffs = Vec::with_capacity(wv.len());
    'rows: for row in &wv {
        let mut rest = row.clone();
        let mut cs = Vec::with_capacity(r);
        for (i, &p) in pivots.iter().enumerate() {
            let (q, rem) = rest[p].fdiv_qr(&ev[i][p]).expect("a nonzero pivot");
            if !rem.is_zero() {
                break 'rows;
            }
            for j in 0..c {
                rest[j] = modn(&(&rest[j] - &(&q * &ev[i][j])), &n);
            }
            cs.push(q);
        }
        if rest.iter().any(|x| !x.is_zero()) {
            break;
        }
        coeffs.push(cs);
    }
    if coeffs.len() == wv.len() {
        let cm = from_residues(a, &coeffs, r);
        return Ok(Some(cm.mul(&t.block(0, 0, r, m)).map_err(gr)?));
    }
    let z = calyx_flint::gr::Ctx::integers();
    let mut lifted = Mat::zero(&z, m + c, c);
    for (i, row) in residues(a).iter().enumerate() {
        for (j, x) in row.iter().enumerate() {
            lifted.set_integer(i, j, x).expect("an integer");
        }
    }
    for j in 0..c {
        lifted.set_integer(m + j, j, &n).expect("an integer");
    }
    let rhs = from_residues(&Mat::zero(&z, 0, 0), &wv, c);
    let Some(v) = solve_integer(&lifted, &rhs)? else { return Ok(None) };
    let rows: Vec<Vec<Integer>> = (0..v.nrows()).map(|i| (0..m).map(|j| modn(&v.integer(i, j), &n)).collect()).collect();
    Ok(Some(from_residues(a, &rows, m)))
}

// ----- echelon forms -------------------------------------------------------------------

/// The reduced echelon form E of a matrix over a field, Magma's
/// transformation T with T·A = E, and the pivot columns P. When A has full
/// row rank T is unique, the inverse of the columns P of A, and FLINT's
/// elimination gives both. Otherwise T follows Magma's own elimination
/// (`Mat::echelon_transform`), as it does over the floating-point reals.
/// When the first r = rank rows are independent, that elimination takes
/// them as the pivot rows, whose part of T is the inverse B of their
/// columns P; the other rows reduce to zero in the order r + 1, n, n - 1,
/// ..., r + 2 (counting from 1), and T has them from its last row up, the
/// row for row o with 1 in place o and -A[o, P]·B in the first r places.
fn field_echelon(m: &Mat) -> RResult<(Mat, Mat, Vec<usize>)> {
    let n = m.nrows();
    if !m.floating() {
        if n == m.ncols() {
            if let Ok(t) = m.inv() {
                return Ok((Mat::identity(m.ctx(), n).map_err(gr)?, t, (0..n).collect()));
            }
        }
        let (e, pivots) = m.rref().map_err(gr)?;
        let r = pivots.len();
        if let Ok(b) = m.select(&(0..r).collect::<Vec<_>>(), &pivots).inv() {
            let rest: Vec<usize> = (r + 1..n).chain((r < n).then_some(r)).collect();
            let mut t = Mat::zero(m.ctx(), n, n);
            t.insert(&b, 0, 0);
            if r < n {
                t.insert(&m.select(&rest, &pivots).mul(&b).and_then(|l| l.neg()).map_err(gr)?, r, 0);
                for (k, &o) in rest.iter().enumerate() {
                    t.set_si(r + k, o, 1).map_err(gr)?;
                }
            }
            return Ok((e, t, pivots));
        }
    }
    let ech = m.echelon_transform().map_err(gr)?;
    Ok((ech.e, ech.t, ech.pivots))
}

/// The echelon form of a matrix, as `EchelonForm` gives it, with the
/// transformation T (T·A = E) if wanted.
pub fn echelon(x: &Mtrx, want_t: bool) -> RResult<(Mat, Option<Mat>)> {
    match kind(x) {
        Kind::Field if want_t => {
            let (e, t, _) = field_echelon(&x.m)?;
            Ok((e, Some(t)))
        }
        Kind::Field => Ok((x.m.rref().map_err(gr)?.0, None)),
        Kind::Integers => Ok(hermite(&x.m, want_t)),
        Kind::Residue => {
            let (e, t, _) = echelon_mod(&x.m);
            Ok((e, want_t.then_some(t)))
        }
        Kind::Other => Err(unsupported("The echelon form")),
    }
}

fn echelon_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let (e, t) = echelon(&x, a.nresults >= 2)?;
    let e = like(&x, e);
    match t {
        Some(t) => {
            let ring = x.ring().clone();
            Ok(vals![e, mat_value(it, &ring, t)?])
        }
        None => one(e),
    }
}

fn hermite_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &hermite_params(), &["Classical", "Default", "Modular"])?;
    let x = mat_arg(a, 0)?.clone();
    if kind(&x) != Kind::Integers {
        return Err(unsupported("The Hermite form"));
    }
    let (h, t) = hermite(&x.m, a.nresults >= 2);
    let h = like(&x, h);
    match t {
        Some(t) => {
            let ring = x.ring().clone();
            Ok(vals![h, mat_value(it, &ring, t)?])
        }
        None => one(h),
    }
}

// ----- nullspaces ------------------------------------------------------------------

/// A basis of the left kernel {v : v·A = 0}, as `KernelMatrix` gives it:
/// Magma's from the echelon form of the transpose over a field, and over
/// the integers and rationals the Hermite form of the integral kernel.
fn kernel_matrix_of(x: &Mtrx) -> RResult<Mat> {
    match (kind(x), x.m.ctx().kind()) {
        (_, CtxKind::Rationals) => rational_kernel_matrix(&x.m),
        (Kind::Field, _) => x.m.left_kernel().map_err(gr),
        (Kind::Integers, _) => Ok(integer_kernel_matrix(&x.m)),
        (Kind::Residue, _) => Ok(kernel_mod(&x.m)),
        (Kind::Other, _) => Err(unsupported("The kernel")),
    }
}

/// The echelonized basis of the left kernel: the reduced echelon form over
/// a field, the Hermite form over the integers.
fn kernel_basis(x: &Mtrx) -> RResult<Mat> {
    match kind(x) {
        Kind::Field => Ok(x.m.left_kernel().map_err(gr)?.rref().map_err(gr)?.0),
        Kind::Integers => Ok(integer_kernel(&x.m)),
        _ => kernel_matrix_of(x),
    }
}

/// The kernel of a matrix with m rows, as a subspace of R^m.
pub(super) fn kernel_space(it: &mut Interp, x: &Mtrx) -> RResult<Value> {
    let basis = kernel_basis(x)?;
    let ring = x.ring().clone();
    let full = parent(it, &ring, 1, x.m.nrows(), Shape::Tuples)?;
    Ok(Value::Struct(subspace(&full, basis)?))
}

fn kernel(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &kernel_params(), KERNEL_ALS)?;
    let x = mat_arg(a, 0)?.clone();
    one(kernel_space(it, &x)?)
}

fn kernel_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_params(it, a, &kernel_params(), KERNEL_ALS)?;
    let x = mat_arg(a, 0)?.clone();
    let k = kernel_matrix_of(&x)?;
    let ring = x.ring().clone();
    one(mat_value(it, &ring, k)?)
}

fn nullspace_of_transpose(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let t = Mtrx { parent: x.parent.clone(), m: x.m.transpose() };
    one(kernel_space(it, &t)?)
}

// ----- solutions of linear systems -----------------------------------------------------

/// The reduced echelon form of the system V·A = W over a field, transposed
/// and with the rows of A last first: the matrix with the columns of A
/// reversed and then those of W, and its pivots. Its pivot columns stand
/// for the rows of A independent of the rows below them, and the columns
/// after them hold the solutions that use only those rows. None if some row
/// of W has no solution.
fn reduced_system(a: &Mat, w: &Mat) -> RResult<Option<(Mat, Vec<usize>)>> {
    let (m, n) = (a.nrows(), a.ncols());
    let mut b = Mat::zero(a.ctx(), n, m + w.nrows());
    b.insert(&a.select(&(0..m).rev().collect::<Vec<_>>(), &(0..n).collect::<Vec<_>>()).transpose(), 0, 0);
    b.insert(&w.transpose(), 0, m);
    let (e, pivots) = b.rref().map_err(gr)?;
    Ok(if pivots.iter().any(|&p| p >= m) { None } else { Some((e, pivots)) })
}

/// Magma's solutions of V·A = W over the rationals: for each row of W, the
/// one that uses only the rows of A independent of the rows below them.
fn solve_rational(a: &Mat, w: &Mat) -> RResult<Option<Mat>> {
    let (m, s) = (a.nrows(), w.nrows());
    let Some((e, pivots)) = reduced_system(a, w)? else { return Ok(None) };
    let mut v = Mat::zero(a.ctx(), s, m);
    for (r, &p) in pivots.iter().enumerate() {
        for i in 0..s {
            v.set_entry(i, m - 1 - p, &e.entry(r, m + i));
        }
    }
    Ok(Some(v))
}

/// Magma's solutions of V·A = W over the integers. The rational solution
/// above is taken when it is integral. Otherwise the coefficients of the
/// other rows of A (free in the reduced system) are chosen to make it so:
/// in the lattice of their integral choices (a coset of it), the one
/// reduced by its Hermite basis from the last row of A back, to residues
/// in (-d/2, d/2]. The Hermite form of one integer matrix gives both the
/// coset and the basis.
fn solve_integer(a: &Mat, w: &Mat) -> RResult<Option<Mat>> {
    let q = calyx_flint::gr::Ctx::rationals();
    let (m, s) = (a.nrows(), w.nrows());
    let Some((e, pivots)) = reduced_system(&a.change_ring(&q).map_err(gr)?, &w.change_ring(&q).map_err(gr)?)? else { return Ok(None) };
    let rat = |i: usize, j: usize| e.entry(i, j).to_rational().expect("a rational");
    // The free columns, first the one for the last row of A.
    let free: Vec<usize> = (0..m).filter(|c| !pivots.contains(c)).collect();
    let (r, k) = (pivots.len(), free.len());
    let mut den = Integer::one();
    for i in 0..r {
        for c in free.iter().copied().chain(m..m + s) {
            den = den.lcm(&rat(i, c).denominator());
        }
    }
    let scaled = |x: &Rational| (x * &Rational::from_integer(&den)).numerator();
    // The pivot values must become integers: y·(D·C) + D·z = D·t, for the
    // coefficients C of the free rows, their choices y and any z. The rows
    // (D·C_f, e_f) and (D·e_p, 0) span the pairs (y·D·C + D·z, y).
    let z = calyx_flint::gr::Ctx::integers();
    let mut g = Mat::zero(&z, r + k, r + k);
    for (j, &c) in free.iter().enumerate() {
        for i in 0..r {
            g.set_integer(j, i, &scaled(&rat(i, c))).map_err(gr)?;
        }
        g.set_integer(j, r + j, &Integer::one()).map_err(gr)?;
    }
    for i in 0..r {
        g.set_integer(k + i, i, &den).map_err(gr)?;
    }
    let h = g.hnf();
    let mut v = Mat::zero(&z, s, m);
    for l in 0..s {
        let mut u: Vec<Integer> = (0..r).map(|i| scaled(&rat(i, m + l))).chain((0..k).map(|_| Integer::zero())).collect();
        let sub = |u: &mut Vec<Integer>, row: usize, q: &Integer| {
            for (j, x) in u.iter_mut().enumerate() {
                *x = &*x - &(q * &h.integer(row, j));
            }
        };
        // Clearing the pivot part leaves (0, -y) for some choice y.
        for i in 0..r {
            match u[i].div_rem_euclid(&h.integer(i, i)) {
                Some((q, rem)) if rem.is_zero() => sub(&mut u, i, &q),
                _ => return Ok(None),
            }
        }
        for x in u.iter_mut() {
            *x = -&*x;
        }
        for j in r..r + k {
            let d = h.integer(j, j);
            let (mut q, rem) = u[j].div_rem_euclid(&d).expect("a nonzero pivot");
            if &rem + &rem > d {
                q = &q + &Integer::one();
            }
            sub(&mut u, j, &q);
        }
        for (j, &c) in free.iter().enumerate() {
            v.set_integer(l, m - 1 - c, &u[r + j]).map_err(gr)?;
        }
        for (i, &p) in pivots.iter().enumerate() {
            let mut x = rat(i, m + l);
            for (j, &c) in free.iter().enumerate() {
                x = &x - &(&rat(i, c) * &Rational::from_integer(&u[r + j]));
            }
            v.set_integer(l, m - 1 - p, &x.numerator()).map_err(gr)?;
        }
    }
    Ok(Some(v))
}

/// Magma's solutions of V·A = W for a sequence of vectors over the integers
/// or the rationals, which come from the Hermite form H = T·A of A (its
/// denominators cleared, and W scaled to match): each row of W is written
/// as X·H down the pivots of H, and V = X·T. Over the integers X must be
/// integral.
fn solve_hermite(a: &Mat, w: &Mat) -> RResult<Option<Mat>> {
    let (m, n, s) = (a.nrows(), a.ncols(), w.nrows());
    let integral = matches!(a.ctx().kind(), CtxKind::Integers);
    let q = |x: &Mat, i: usize, j: usize| {
        if integral { Rational::from_integer(&x.integer(i, j)) } else { x.entry(i, j).to_rational().expect("a rational") }
    };
    let den = (0..m).flat_map(|i| (0..n).map(move |j| (i, j))).fold(Integer::one(), |d, (i, j)| d.lcm(&q(a, i, j).denominator()));
    let dq = Rational::from_integer(&den);
    let mut ai = Mat::zero(&calyx_flint::gr::Ctx::integers(), m, n);
    for i in 0..m {
        for j in 0..n {
            ai.set_integer(i, j, &(&q(a, i, j) * &dq).numerator()).map_err(gr)?;
        }
    }
    let (h, t) = hermite(&ai, true);
    let t = t.expect("a transformation");
    let pivots: Vec<usize> = (0..m).map_while(|i| (0..n).find(|&j| !h.entry_is_zero(i, j))).collect();
    let hq = |k: usize, j: usize| Rational::from_integer(&h.integer(k, j));
    let mut v = Mat::zero(a.ctx(), s, m);
    for l in 0..s {
        let target: Vec<Rational> = (0..n).map(|j| &q(w, l, j) * &dq).collect();
        let mut x: Vec<Rational> = Vec::with_capacity(pivots.len());
        for (i, &p) in pivots.iter().enumerate() {
            let y = x.iter().enumerate().fold(target[p].clone(), |y, (k, xk)| &y - &(xk * &hq(k, p)));
            x.push(y.checked_div(&hq(i, p)).expect("a nonzero pivot"));
        }
        let consistent = (0..n).all(|j| x.iter().enumerate().fold(Rational::zero(), |y, (k, xk)| &y + &(xk * &hq(k, j))) == target[j]);
        if !consistent || (integral && x.iter().any(|xk| !xk.denominator().is_one())) {
            return Ok(None);
        }
        for c in 0..m {
            let y = x.iter().enumerate().fold(Rational::zero(), |y, (k, xk)| &y + &(xk * &Rational::from_integer(&t.integer(k, c))));
            if integral { v.set_integer(l, c, &y.numerator()) } else { v.set_rational(l, c, &y) }.map_err(gr)?;
        }
    }
    Ok(Some(v))
}

/// Solutions V of V·A = W for the rows of `w`: None if some row has none.
/// Over a finite field W is written in the rows of the echelon form of A
/// and V the same combination of the rows of Magma's transformation. For a
/// sequence of vectors (`seq`) over the integers or the rationals Magma
/// solves through the Hermite form instead.
fn solve(x: &Mtrx, w: &Mat, seq: bool) -> RResult<Option<Mat>> {
    let (m, s) = (x.m.nrows(), w.nrows());
    match kind(x) {
        _ if seq && matches!(x.m.ctx().kind(), CtxKind::Integers | CtxKind::Rationals) => solve_hermite(&x.m, w),
        Kind::Field if matches!(x.m.ctx().kind(), CtxKind::Rationals) => solve_rational(&x.m, w),
        Kind::Field => {
            // A square system with an invertible A has just the one solution.
            if m == x.m.ncols() && !x.m.floating() {
                if let Some(v) = x.m.transpose().nonsingular_solve(&w.transpose()).map_err(gr)? {
                    return Ok(Some(v.transpose()));
                }
            }
            let (e, t, pivots) = field_echelon(&x.m)?;
            let r = pivots.len();
            let c = w.select(&(0..s).collect::<Vec<_>>(), &pivots);
            let top = e.block(0, 0, r, e.ncols());
            if c.mul(&top).map_err(gr)?.equal(w) != Truth::True {
                return Ok(None);
            }
            Ok(Some(c.mul(&t.block(0, 0, r, m)).map_err(gr)?))
        }
        Kind::Integers => solve_integer(&x.m, w),
        Kind::Residue => solve_mod(&x.m, w),
        Kind::Other => Err(unsupported("Solving systems")),
    }
}

/// The right-hand side of `Solution` and `IsConsistent`: the rows of a
/// matrix or vector, or a sequence of vectors; and whether it was a
/// sequence.
fn rhs(it: &mut Interp, x: &Mtrx, v: &Value) -> RResult<(Mat, bool)> {
    let n = x.m.ncols();
    let check = |y: &Mtrx| -> RResult<()> {
        if y.ring() != x.ring() {
            return Err(RuntimeError::runtime("Arguments have incompatible coefficient rings"));
        }
        if y.m.ncols() != n {
            return Err(RuntimeError::runtime("Arguments have incompatible degrees"));
        }
        Ok(())
    };
    match v {
        Value::Mat(y) => {
            check(y)?;
            Ok((y.m.clone(), false))
        }
        Value::Seq(q) => {
            let mut w = Mat::zero(x.m.ctx(), q.elems.len(), n);
            for (i, e) in q.elems.iter().enumerate() {
                let Value::Mat(y) = e else { return Err(super::bad()) };
                check(y)?;
                w.insert(&y.m, i, 0);
            }
            let _ = it;
            Ok((w, true))
        }
        _ => Err(super::bad()),
    }
}

/// The solutions as the caller wants them: a vector for a vector, a
/// matrix for a matrix, a sequence of vectors for a sequence.
fn solution_value(it: &mut Interp, x: &Mtrx, w: &Value, v: Mat, seq: bool) -> RResult<Value> {
    let ring = x.ring().clone();
    let m = v.ncols();
    if seq {
        let u = Value::Struct(parent(it, &ring, 1, m, Shape::Tuples)?);
        let rows = (0..v.nrows()).map(|i| vec_value(it, &ring, v.block(i, 0, 1, m))).collect::<RResult<Vec<_>>>()?;
        return Ok(Value::seq(Some(u), rows));
    }
    match w {
        Value::Mat(y) if y.is_vector() => vec_value(it, &ring, v),
        _ => mat_value(it, &ring, v),
    }
}

fn solution(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let w = a.args[1].clone();
    let (rows, seq) = rhs(it, &x, &w)?;
    let Some(v) = solve(&x, &rows, seq)? else {
        if !seq {
            return Err(RuntimeError::runtime("No solution exists"));
        }
        // The first vector without one.
        let n = rows.ncols();
        for i in 0..rows.nrows() {
            if solve(&x, &rows.block(i, 0, 1, n), true)?.is_none() {
                return Err(RuntimeError::runtime(format!("No solution exists for vector number {}", i + 1)));
            }
        }
        unreachable!("some vector has no solution")
    };
    let v = solution_value(it, &x, &w, v, seq)?;
    if a.nresults < 2 {
        return one(v);
    }
    Ok(vals![v, kernel_space(it, &x)?])
}

/// `IsConsistent`: for an element of a matrix algebra or a sequence of
/// vectors Magma's gives the nullspace as well, which a print statement
/// then shows.
fn is_consistent(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let w = a.args[1].clone();
    let (rows, seq) = rhs(it, &x, &w)?;
    // Without a solution, `b, V := IsConsistent(A, W)` leaves V unassigned.
    let Some(v) = solve(&x, &rows, seq)? else { return Ok(vals![Value::Bool(false), Value::Undef, Value::Undef]) };
    let v = solution_value(it, &x, &w, v, seq)?;
    if a.nresults < 3 && x.info().shape != Shape::Algebra && !seq {
        return Ok(vals![Value::Bool(true), v]);
    }
    Ok(vals![Value::Bool(true), v, kernel_space(it, &x)?])
}

// ----- parameters ------------------------------------------------------------------

/// The parameters of `Determinant` (and the first two of `Rank`), which the
/// exact algorithms here have no use for.
fn proof_params() -> [(&'static str, Value); 4] {
    [("MonteCarloLevel", Value::int(0)), ("Proof", Value::Bool(true)), ("pAdic", Value::Bool(true)), ("Divisor", Value::int(0))]
}

fn hermite_params() -> [(&'static str, Value); 4] {
    [("Al", Value::str("Default")), ("Optimize", Value::Bool(true)), ("Integral", Value::Bool(true)), ("InitialSort", Value::Bool(false))]
}

/// `Kernel`, `KernelMatrix` and `NullspaceMatrix` take an `Al` among
/// `KERNEL_ALS`; every one of them gives the same basis in Magma.
fn kernel_params() -> [(&'static str, Value); 1] {
    [("Al", Value::str("Default"))]
}

const KERNEL_ALS: &[&str] = &["Default", "Hermite", "LLL", "Modular"];

/// Magma's errors for a parameter whose value does not have the type of its
/// default, or for an `Al` that is not one of `als`.
pub(super) fn check_params(it: &Interp, a: &CallArgs, params: &[(&str, Value)], als: &[&str]) -> RResult<()> {
    for (p, default) in params {
        match a.param(p) {
            Some(v) if std::mem::discriminant(v) != std::mem::discriminant(default) => return Err(with_types(it, a, &format!("Bad type for parameter '{p}'"))),
            Some(Value::Str(s)) if !als.contains(&s.as_str()) => return Err(with_types(it, a, &format!("Bad value for parameter '{p}' ({})", s.as_str()))),
            _ => {}
        }
    }
    Ok(())
}

/// Magma's error `msg` followed by the types of the arguments.
pub(super) fn with_types(it: &Interp, a: &CallArgs, msg: &str) -> RuntimeError {
    let types: Vec<String> = a.args.iter().map(|v| it.type_name_ext(v)).collect();
    RuntimeError::runtime(format!("{msg}\nArgument types given: {}", types.join(", ")))
}

pub fn register(it: &mut Interp) {
    for ty in ["AlgMatElt", "ModMatRngElt"] {
        it.def("Transpose", &format!("A::{ty} -> Mtrx"), "The transpose of A.", transpose);
    }
    it.def_params("Rank", "A::Mtrx -> RngIntElt", &proof_params()[..2], "The rank of A.", rank);
    it.def_params("Determinant", "A::Mtrx -> RngElt", &proof_params(), "The determinant of A.", determinant);
    it.def("Trace", "A::Mtrx -> RngElt", "The trace of A.", trace);
    it.def("TraceOfProduct", "A::Mtrx, B::Mtrx -> RngElt", "The trace of A*B.", trace_of_product);
    // Magma writes the minors, cofactors and Pfaffians in its own language.
    let package: [(&str, &str, &str, crate::intrinsics::NativeFn); 9] = [
        ("Minor", "M::Mtrx, i::RngIntElt, j::RngIntElt -> RngElt", "The minor of M without row i and column j.", minor),
        ("Minor", "M::Mtrx, I::[RngIntElt], J::[RngIntElt] -> RngElt", "The minor of M with rows I and columns J.", minor_seqs),
        ("Minors", "M::Mtrx, r::RngIntElt -> SeqEnum", "The r by r minors of M.", minors),
        ("Cofactor", "M::Mtrx, i::RngIntElt, j::RngIntElt -> RngElt", "The cofactor of M at (i, j).", cofactor),
        ("Cofactors", "M::Mtrx -> SeqEnum", "The cofactors of M.", cofactors),
        ("Cofactors", "M::Mtrx, r::RngIntElt -> SeqEnum", "The r by r cofactors of M.", cofactors),
        ("Pfaffian", "M::Mtrx -> RngElt", "The Pfaffian of the anti-symmetric matrix M.", pfaffian),
        ("Pfaffian", "M::Mtrx, I::[RngIntElt], J::[RngIntElt] -> RngElt", "The Pfaffian of the rows I and columns J of M.", pfaffian),
        ("Pfaffians", "M::Mtrx, r::RngIntElt -> SeqEnum", "The Pfaffians of the principal r by r submatrices of M.", pfaffians),
    ];
    for (name, sig, doc, f) in package {
        it.def(name, sig, doc, f).package = true;
    }
    it.def("Adjoint", "A::Mtrx -> AlgMatElt", "The adjoint of A.", adjoint);
    it.def("IsUnit", "A::Mtrx -> BoolElt", "Whether A is invertible.", is_unit);
    it.def("IsSingular", "A::Mtrx -> BoolElt", "Whether the determinant of A is zero.", is_singular);
    it.def("EchelonForm", "A::Mtrx -> Mtrx, AlgMatElt", "The reduced echelon form E of A and T with T*A = E.", echelon_form);
    it.def_params("HermiteForm", "A::Mtrx -> Mtrx, AlgMatElt", &hermite_params(), "The Hermite form H of A and T with T*A = H.", hermite_form);
    it.def("Nullspace", "A::Mtrx -> ModTupRng", "The space of vectors v with v*A = 0.", kernel);
    it.def_params("Kernel", "A::Mtrx -> ModTupRng", &kernel_params(), "The space of vectors v with v*A = 0.", kernel);
    for name in ["NullspaceMatrix", "KernelMatrix"] {
        it.def_params(name, "A::Mtrx -> Mtrx", &kernel_params(), "A basis of the nullspace of A as the rows of a matrix.", kernel_matrix);
    }
    it.def("NullspaceOfTranspose", "A::Mtrx -> ModTupRng", "The nullspace of the transpose of A.", nullspace_of_transpose);
    it.def("IsConsistent", "A::Mtrx, W::Mtrx -> BoolElt, Mtrx, ModTupRng", "Whether V*A = W has a solution; a solution and the nullspace.", is_consistent);
    it.def(
        "IsConsistent",
        "A::Mtrx, Q::[ModTupRngElt] -> BoolElt, SeqEnum, ModTupRng",
        "Whether V*A = Q[i] has solutions; solutions and the nullspace.",
        is_consistent,
    );
    it.def("Solution", "A::Mtrx, W::Mtrx -> Mtrx, ModTupRng", "A solution of V*A = W and the nullspace of A.", solution);
    it.def("Solution", "A::Mtrx, Q::[ModTupRngElt] -> SeqEnum, ModTupRng", "Solutions of V*A = Q[i] and the nullspace of A.", solution);
}
