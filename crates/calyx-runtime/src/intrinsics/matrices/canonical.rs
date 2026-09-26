//! Canonical forms (text/280): the Smith form and elementary divisors of a
//! matrix over a Euclidean ring, the saturation of an integer matrix, the
//! Hessenberg form, the rational, primary rational and Jordan forms of a
//! square matrix over a field with their lists of factors, similarity, and
//! the Frobenius form of an alternating integer matrix.
//!
//! The forms and the lists are Magma's. The transformations are valid but
//! our own, save that over a field SmithForm's P and Q are Magma's. The
//! saturation is given by its Hermite form, where Magma gives another basis.
//!
//! The forms over a field come from the primary decomposition: the
//! irreducible factors q of the minimal polynomial, in the order of
//! `Factorization`, and the sizes k of the blocks q^k for each, which the
//! exponents of q in the minimal and characteristic polynomials settle but
//! for a few cases, where the ranks of the powers of q(A) do. The
//! transformations need a generator for each block: from a cyclic vector
//! when the two polynomials are the same, as they usually are, and
//! otherwise chosen from the kernels of the powers of q(A).

use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::{Integer, Nmod};
use calyx_flint::gr::{Ctx, CtxKind, Elem, Truth};
use calyx_flint::mat::Mat;

use super::change::coerced;
use super::charpoly::{charpoly, eval_coeffs, factorization, large_primes, modular_multiplicities, polynomial};
use super::linalg::{field_echelon, gr, modulus, normalizer, residues, with_types};
use super::{Mtrx, Shape, entry_of, like, mat_arg, mat_value, parent, square};
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::{bare, boolv, hidden_inner, one};
use crate::interp::{CallArgs, Interp};
use crate::rings::make_elt;
use crate::value::*;

// ----- Smith forms ---------------------------------------------------------------------

/// The Euclidean rings with a Smith form here.
#[derive(Clone, Copy, PartialEq)]
enum Euclid {
    Integers,
    Field,
    /// The integers modulo a composite.
    Residue,
    /// Polynomials over a field.
    Poly,
}

fn euclid(x: &Mtrx) -> RResult<Euclid> {
    let ctx = x.m.ctx();
    Ok(match ctx.kind() {
        CtxKind::Integers => Euclid::Integers,
        _ if x.m.over_field() => Euclid::Field,
        CtxKind::Nmod(_) | CtxKind::FmpzMod(_) => Euclid::Residue,
        CtxKind::Poly if ctx.base().is_some_and(|b| b.is_field() == Truth::True) => Euclid::Poly,
        _ => return Err(RuntimeError::runtime("Argument 1 has no Smith algorithm")),
    })
}

/// The Smith form S of A, with P and Q such that P·A·Q = S if wanted.
fn smith(x: &Mtrx, want: bool) -> RResult<(Mat, Option<(Mat, Mat)>)> {
    let m = &x.m;
    match euclid(x)? {
        Euclid::Integers if want => {
            let (s, p, q) = smith_integers(m)?;
            Ok((s, Some((p, q))))
        }
        Euclid::Integers => Ok((integer_smith(m)?, None)),
        Euclid::Field => smith_field(m, want),
        Euclid::Residue => smith_mod(m, want),
        Euclid::Poly => smith_euclid(m, want),
    }
}

/// The Smith form of a matrix over the integers: from `integer_divisors`,
/// or FLINT's when that gives up.
fn integer_smith(a: &Mat) -> RResult<Mat> {
    let Some(ds) = integer_divisors(a)? else { return Ok(a.snf()) };
    let mut s = Mat::zero(a.ctx(), a.nrows(), a.ncols());
    for (i, d) in ds.iter().enumerate() {
        s.set_integer(i, i, d).map_err(gr)?;
    }
    Ok(s)
}

/// The nonzero elementary divisors of a matrix over the integers, or None
/// to leave them to FLINT (which takes Hermite forms in turn, slow when the
/// determinant is large). The content of A is taken out first. Of rank r,
/// A has a nonsingular r by r minor on r rows and columns independent
/// modulo a prime; unless it is square of full rank, the gcd of that and a
/// few other such minors is a multiple of the product of the divisors, and
/// they are the Smith form modulo it (`modular_divisors`). A rank below
/// both sizes is certified by `rank_at_most`.
fn integer_divisors(a: &Mat) -> RResult<Option<Vec<Integer>>> {
    let (m, n) = (a.nrows(), a.ncols());
    let c = a.content();
    if c.is_zero() {
        return Ok(Some(Vec::new()));
    }
    let a = if c.is_one() { a.clone() } else { a.divexact_scalar(&c) };
    let p = large_primes().next().expect("a prime below 2^62");
    let ap = a.change_ring(&Ctx::residue_ring(&p)).map_err(gr)?;
    let (_, cols) = ap.rref().map_err(gr)?;
    let r = cols.len();
    let ds = if r == m && r == n {
        square_divisors(&a)?
    } else {
        let (_, rows) = ap.transpose().rref().map_err(gr)?;
        if r < m && r < n && !rank_at_most(&a, &rows, &cols)? {
            return Ok(None);
        }
        modular_divisors(&a, r, &minors_gcd(&a, &rows, &cols)?)?
    };
    Ok(ds.map(|ds| ds.iter().map(|x| x * &c).collect()))
}

/// The elementary divisors of a nonsingular square matrix over the integers,
/// or None to leave them to FLINT. FLINT's divisor s of the determinant d
/// (see `det_with_divisor`) divides the last one, so the others divide d/s:
/// they are the Smith form modulo d/s, and the last is d over their
/// product. Most often s = d and the others are 1.
fn square_divisors(a: &Mat) -> RResult<Option<Vec<Integer>>> {
    let n = a.nrows();
    let (d, s) = a.det_with_divisor();
    if d.is_zero() {
        return Ok(None);
    }
    let Some(mut ds) = modular_divisors(a, n - 1, &d.divexact(&s))? else { return Ok(None) };
    let product = ds.iter().fold(Integer::one(), |x, y| &x * y);
    ds.push(d.divexact(&product));
    Ok(Some(ds))
}

/// The first k entries of the Smith form of a matrix over the integers,
/// given a multiple g of their product: the Smith form modulo g, one prime
/// power of g at a time, where a prime modulo which the matrix keeps rank k
/// divides none of them. None when g has a large factor.
fn modular_divisors(a: &Mat, k: usize, g: &Integer) -> RResult<Option<Vec<Integer>>> {
    let mut ds = vec![Integer::one(); k];
    let Some(factors) = factor_small(g, 62) else { return Ok(None) };
    for (p, e) in factors {
        let (Some(p), Some(q)) = (p.to_u64(), p.pow(e).to_u64()) else { return Ok(None) };
        if q >= 1 << 62 {
            return Ok(None);
        }
        if a.change_ring(&Ctx::residue_ring(&Integer::from_u64(p))).map_err(gr)?.rank().map_err(gr)? >= k {
            continue;
        }
        for (x, v) in ds.iter_mut().zip(local_smith(a, p, e as u32, Nmod::new(q), k)) {
            *x = &*x * &Integer::from_u64(p.pow(v));
        }
    }
    Ok(Some(ds))
}

/// Whether a matrix over the integers has rank at most the number of its
/// independent columns `cols`, given as many independent rows `rows`: the
/// other columns are combinations of those if the solution X of
/// A[rows, cols]·X = A[rows, others] gives them on every row.
fn rank_at_most(a: &Mat, rows: &[usize], cols: &[usize]) -> RResult<bool> {
    let (m, n) = (a.nrows(), a.ncols());
    let all: Vec<usize> = (0..m).collect();
    let others: Vec<usize> = (0..n).filter(|j| !cols.contains(j)).collect();
    let Some((x, den)) = a.select(rows, cols).solve_den(&a.select(rows, &others)) else { return Ok(false) };
    let lhs = a.select(&all, cols).mul(&x).map_err(gr)?;
    Ok((0..m).all(|i| others.iter().enumerate().all(|(j, &c)| lhs.integer(i, j) == &a.integer(i, c) * &den)))
}

/// The gcd of the minor of `a` on `rows` and `cols` (as many, and not 0)
/// and a few others of that size on random rows and columns.
fn minors_gcd(a: &Mat, rows: &[usize], cols: &[usize]) -> RResult<Integer> {
    let r = rows.len();
    let minor = |rs: &[usize], cs: &[usize]| -> RResult<Integer> { Ok(a.select(rs, cs).det().map_err(gr)?.to_integer().map_err(gr)?.abs()) };
    let mut g = minor(rows, cols)?;
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut pick = |n: usize| {
        let mut all: Vec<usize> = (0..n).collect();
        for i in 0..r {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            all.swap(i, i + (state % (n - i) as u64) as usize);
        }
        let mut s = all[..r].to_vec();
        s.sort_unstable();
        s
    };
    for _ in 0..3 {
        if g.is_one() {
            break;
        }
        let (rs, cs) = (pick(a.nrows()), pick(a.ncols()));
        g = g.gcd(&minor(&rs, &cs)?);
    }
    Ok(g)
}

/// The p-adic valuations (at most e) of the first k entries of the Smith
/// form of a matrix over the integers, by elimination modulo q = p^e with
/// pivots of least valuation (which leaves the rest of the pivot's row to
/// column operations that change nothing else).
fn local_smith(a: &Mat, p: u64, e: u32, q: Nmod, k: usize) -> Vec<u32> {
    let (rows, n) = (a.nrows(), a.ncols());
    let mut m: Vec<u64> = (0..rows * n).map(|x| q.reduce_integer(&a.integer(x / n, x % n))).collect();
    let val = |mut x: u64| {
        if x == 0 {
            return e;
        }
        let mut v = 0;
        while x.is_multiple_of(p) {
            x /= p;
            v += 1;
        }
        v
    };
    let mut out = Vec::with_capacity(k);
    for t in 0..k {
        let mut best = (e, t, t);
        'search: for i in t..rows {
            for j in t..n {
                let v = val(m[i * n + j]);
                if v < best.0 {
                    best = (v, i, j);
                    if v == 0 {
                        break 'search;
                    }
                }
            }
        }
        let (v, i, j) = best;
        if v == e {
            out.resize(k, e);
            break;
        }
        out.push(v);
        if i != t {
            for c in 0..n {
                m.swap(t * n + c, i * n + c);
            }
        }
        if j != t {
            for r in 0..rows {
                m.swap(r * n + t, r * n + j);
            }
        }
        let pv = p.pow(v);
        let inv = q.inv(m[t * n + t] / pv).expect("a unit");
        for r in t + 1..rows {
            let x = m[r * n + t];
            if x == 0 {
                continue;
            }
            let f = q.mul(x / pv, inv);
            for c in t..n {
                m[r * n + c] = q.sub(m[r * n + c], q.mul(f, m[t * n + c]));
            }
        }
    }
    out
}

/// The factorization of a positive g: trial division below 2^16, then what
/// is left if it is a probable prime or has at most `bits` bits (by
/// `Factorization`'s methods); None when a larger composite is left.
fn factor_small(g: &Integer, bits: u64) -> Option<Vec<(Integer, u64)>> {
    let mut g = g.clone();
    let mut out = Vec::new();
    let mut p = Integer::from_i64(2);
    while !g.is_one() && p.bits() <= 16 {
        if (&p * &p) > g {
            break;
        }
        let (k, rest) = g.remove(&p);
        if k > 0 {
            out.push((p.clone(), k));
            g = rest;
        }
        p = p.next_prime();
    }
    if g.is_one() || (&p * &p) > g || g.is_probable_prime() {
        out.extend((!g.is_one()).then_some((g, 1)));
        return Some(out);
    }
    if g.bits() > bits {
        return None;
    }
    out.extend(crate::intrinsics::factseq::factor(&g));
    Some(out)
}

/// The Smith form S of a matrix A over the integers with unimodular U and V
/// such that U·A·V = S. FLINT's alternating Hermite forms are slow unless A
/// is square of full rank r, so otherwise A is first cut down to r by r by
/// Hermite transforms of matrices of full column rank (which FLINT does
/// quickly): of r independent columns, giving U2·A = [R 0]^t, and of R^t,
/// giving R·V1 = [C 0].
fn smith_integers(a: &Mat) -> RResult<(Mat, Mat, Mat)> {
    let (m, n) = (a.nrows(), a.ncols());
    // Columns independent modulo a prime are independent; if there are fewer
    // than the rank, U2·A shows it and FLINT takes over.
    let p = large_primes().next().expect("a prime below 2^62");
    let (_, cols) = a.change_ring(&Ctx::residue_ring(&p)).map_err(gr)?.rref().map_err(gr)?;
    let r = cols.len();
    let zero_below = |x: &Mat| (r..x.nrows()).all(|i| (0..x.ncols()).all(|j| x.entry_is_zero(i, j)));
    if r == m && r == n || !zero_below(a) && r == 0 {
        return Ok(a.snf_transform());
    }
    if r == 0 {
        let one = |k| Mat::identity(a.ctx(), k).map_err(gr);
        return Ok((a.clone(), one(m)?, one(n)?));
    }
    let (_, u2) = a.select(&(0..m).collect::<Vec<_>>(), &cols).hnf_transform();
    let ua = u2.mul(a).map_err(gr)?;
    if !zero_below(&ua) {
        return Ok(a.snf_transform());
    }
    let (h3, u3) = ua.block(0, 0, r, n).transpose().hnf_transform();
    let v1 = u3.transpose();
    let (d, u4, v4) = h3.block(0, 0, r, r).transpose().snf_transform();
    let mut s = Mat::zero(a.ctx(), m, n);
    for i in 0..r {
        s.set_integer(i, i, &d.integer(i, i)).map_err(gr)?;
    }
    let u = u4.mul(&u2.block(0, 0, r, m)).map_err(gr)?.concat_vertical(&u2.block(r, 0, m - r, m));
    let v = v1.block(0, 0, n, r).mul(&v4).map_err(gr)?.concat_horizontal(&v1.block(0, r, n, n - r));
    Ok((s, u, v))
}

/// Over a field, as many 1s as the rank, with Magma's P and Q: the
/// transformation of the echelon form E of A, and the transpose of that of
/// the echelon form of the transpose of E.
fn smith_field(m: &Mat, want: bool) -> RResult<(Mat, Option<(Mat, Mat)>)> {
    let (rank, pq) = if want {
        let (e, p, pivots) = field_echelon(m)?;
        let (_, q, _) = field_echelon(&e.transpose())?;
        (pivots.len(), Some((p, q.transpose())))
    } else {
        (m.rank().map_err(gr)?, None)
    };
    let mut s = Mat::zero(m.ctx(), m.nrows(), m.ncols());
    let one = Elem::one(m.ctx()).map_err(gr)?;
    for i in 0..rank {
        s.set_entry(i, i, &one);
    }
    Ok((s, pq))
}

/// Over Z/nZ, n composite: the Smith form of the residues as integers, each
/// entry d of its diagonal taken to the divisor gcd(d, n) of n by a unit
/// in its column of Q.
fn smith_mod(m: &Mat, want: bool) -> RResult<(Mat, Option<(Mat, Mat)>)> {
    let (rows, cols, n) = (m.nrows(), m.ncols(), modulus(m));
    let mut lift = Mat::zero(&Ctx::integers(), rows, cols);
    for (i, row) in residues(m).iter().enumerate() {
        for (j, x) in row.iter().enumerate() {
            lift.set_integer(i, j, x).map_err(gr)?;
        }
    }
    let (s, pq) = if want {
        let (s, p, q) = lift.snf_transform();
        (s, Some((p, q)))
    } else {
        (lift.snf(), None)
    };
    let mut out = Mat::zero(m.ctx(), rows, cols);
    let mut units = Vec::with_capacity(rows.min(cols));
    for i in 0..rows.min(cols) {
        let d = s.integer(i, i).fdiv_qr(&n).expect("a nonzero modulus").1;
        out.set_integer(i, i, &d.gcd(&n)).map_err(gr)?;
        units.push(normalizer(&d, &n));
    }
    let Some((p, q)) = pq else { return Ok((out, None)) };
    let mut q = q.change_ring(m.ctx()).map_err(gr)?;
    for (j, u) in units.iter().enumerate() {
        let u = Elem::from_integer(m.ctx(), u).map_err(gr)?;
        for r in 0..cols {
            let x = q.entry(r, j).mul(&u).map_err(gr)?;
            q.set_entry(r, j, &x);
        }
    }
    Ok((out, Some((p.change_ring(m.ctx()).map_err(gr)?, q))))
}

/// Column j of `m` minus c times column k.
fn submul_col(m: &mut Mat, j: usize, k: usize, c: &Elem) -> RResult<()> {
    for r in 0..m.nrows() {
        if !m.entry_is_zero(r, k) {
            let x = m.entry(r, j).sub(&c.mul(&m.entry(r, k)).map_err(gr)?).map_err(gr)?;
            m.set_entry(r, j, &x);
        }
    }
    Ok(())
}

/// Whether the polynomial g divides f (g nonzero, over a field).
fn poly_divides(g: &Elem, f: &Elem) -> RResult<bool> {
    Ok(f.poly_divrem(g).map_err(gr)?.1.poly_len() == 0)
}

/// Over K[x], by division with remainder: the pivot is an entry of least
/// degree, moved to the diagonal, and the rest of its row and column are
/// reduced by it; while that leaves remainders, or an entry below and right
/// of it that it does not divide (whose row is then added to its own), a
/// new pivot is taken. The pivots are made monic.
fn smith_euclid(m: &Mat, want: bool) -> RResult<(Mat, Option<(Mat, Mat)>)> {
    let (rows, cols, ctx) = (m.nrows(), m.ncols(), m.ctx().clone());
    let mut w = m.clone();
    let (mut p, mut q) = (Mat::identity(&ctx, rows).map_err(gr)?, Mat::identity(&ctx, cols).map_err(gr)?);
    let minus_one = Elem::from_i64(&ctx, -1).map_err(gr)?;
    'diagonal: for t in 0..rows.min(cols) {
        loop {
            let mut least: Option<(usize, usize, usize)> = None;
            for i in t..rows {
                for j in t..cols {
                    let len = w.entry(i, j).poly_len();
                    if len > 0 && least.is_none_or(|(l, _, _)| len < l) {
                        least = Some((len, i, j));
                    }
                }
            }
            let Some((len, i, j)) = least else { break 'diagonal };
            w.swap_rows(t, i);
            p.swap_rows(t, i);
            w.swap_cols(t, j);
            q.swap_cols(t, j);
            let pivot = w.entry(t, t);
            let mut clean = true;
            for i in t + 1..rows {
                if !w.entry_is_zero(i, t) {
                    let (quo, rem) = w.entry(i, t).poly_divrem(&pivot).map_err(gr)?;
                    w.submul_row(i, t, &quo).map_err(gr)?;
                    p.submul_row(i, t, &quo).map_err(gr)?;
                    clean &= rem.poly_len() == 0;
                }
            }
            for j in t + 1..cols {
                if !w.entry_is_zero(t, j) {
                    let (quo, rem) = w.entry(t, j).poly_divrem(&pivot).map_err(gr)?;
                    submul_col(&mut w, j, t, &quo)?;
                    submul_col(&mut q, j, t, &quo)?;
                    clean &= rem.poly_len() == 0;
                }
            }
            if !clean {
                continue;
            }
            let mut split = None;
            'rest: for i in t + 1..rows {
                for j in t + 1..cols {
                    if !poly_divides(&pivot, &w.entry(i, j))? {
                        split = Some(i);
                        break 'rest;
                    }
                }
            }
            if let Some(i) = split {
                w.submul_row(t, i, &minus_one).map_err(gr)?;
                p.submul_row(t, i, &minus_one).map_err(gr)?;
                continue;
            }
            let lead = pivot.poly_coeff(len - 1).inv().map_err(gr)?;
            let lead = Elem::poly_from_coeffs(&ctx, &[lead]).map_err(gr)?;
            w.scale_row(t, &lead).map_err(gr)?;
            p.scale_row(t, &lead).map_err(gr)?;
            break;
        }
    }
    Ok((w, want.then_some((p, q))))
}

fn smith_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let (s, pq) = smith(&x, a.nresults != 1)?;
    let s = like(&x, s);
    let Some((p, q)) = pq else { return one(s) };
    let ring = x.ring().clone();
    Ok(vals![s, mat_value(it, &ring, p)?, mat_value(it, &ring, q)?])
}

fn elementary_divisors(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let (s, _) = smith(&x, false)?;
    let ring = x.ring().clone();
    let ds = (0..s.nrows().min(s.ncols())).filter(|&i| !s.entry_is_zero(i, i)).map(|i| entry_of(it, &ring, &s, i, i)).collect();
    one(Value::seq(Some(ring), ds))
}

// ----- saturation and the Hessenberg form ------------------------------------------------

/// A matrix over the rationals with each row scaled to integers, over the
/// integers.
fn integral_rows(m: &Mat) -> RResult<Mat> {
    let mut out = Mat::zero(&Ctx::integers(), m.nrows(), m.ncols());
    for i in 0..m.nrows() {
        let row: Vec<_> = (0..m.ncols()).map(|j| m.entry(i, j).to_rational().expect("a rational")).collect();
        let den = row.iter().fold(Integer::one(), |d, q| d.lcm(&q.denominator()));
        for (j, q) in row.iter().enumerate() {
            out.set_integer(i, j, &(&q.numerator() * &den.divexact(&q.denominator()))).map_err(gr)?;
        }
    }
    Ok(out)
}

/// `Saturation(A)`: the integer vectors with a nonzero multiple in the row
/// lattice of A, those orthogonal to the kernel {v : A·v = 0}, as the rows
/// of a matrix in Hermite form.
fn saturation(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let m = match x.m.ctx().kind() {
        CtxKind::Integers => x.m.clone(),
        CtxKind::Rationals => integral_rows(&x.m)?,
        _ => return Err(RuntimeError::runtime("Coefficient ring must be Z")),
    };
    one(mat_value(it, &Value::integers(), saturated(&m)?)?)
}

/// The saturation of the row lattice of `m` over the integers, in Hermite
/// form: a basis of the lattice saturated at each prime of the gcd of a few
/// maximal minors of m (`p_saturate`), since the index is the product of
/// the elementary divisors, which divides each; or when that gcd keeps a
/// large factor not known to be prime, the lattice orthogonal to the
/// kernel.
fn saturated(m: &Mat) -> RResult<Mat> {
    let n = m.ncols();
    // Rows independent modulo a prime are independent; when they are not
    // all, the nonzero rows of the Hermite form are a basis. (Only some of
    // the rows would span a lattice of larger index, with primes too large
    // to find.)
    let p = large_primes().next().expect("a prime below 2^62");
    let mp = m.change_ring(&Ctx::residue_ring(&p)).map_err(gr)?;
    let (_, cols) = mp.rref().map_err(gr)?;
    if cols.len() == n {
        return Mat::identity(m.ctx(), n).map_err(gr);
    }
    let (mut h, rows) = if cols.len() == m.nrows() {
        (m.clone(), (0..m.nrows()).collect())
    } else {
        let h = m.hnf();
        let r = (0..h.nrows()).take_while(|&i| (0..n).any(|j| !h.entry_is_zero(i, j))).count();
        if r > cols.len() {
            return orthogonal_saturation(&h.block(0, 0, r, n));
        }
        (h.block(0, 0, r, n), mp.transpose().rref().map_err(gr)?.1)
    };
    if h.nrows() == 0 {
        return Ok(Mat::zero(m.ctx(), 0, n));
    }
    let Some(primes) = index_primes(m, &rows, &cols)? else { return orthogonal_saturation(&h) };
    for p in &primes {
        p_saturate(&mut h, p)?;
    }
    Ok(h.hnf())
}

/// The primes that can divide the index of the row lattice of `m`, of rank
/// r, in its saturation (the product of its elementary divisors): those of
/// the gcd of its r by r minors on `rows` and `cols` (not 0) and on a few
/// random sets of rows and columns. None when the gcd keeps a large factor
/// not known to be prime.
fn index_primes(m: &Mat, rows: &[usize], cols: &[usize]) -> RResult<Option<Vec<Integer>>> {
    let g = minors_gcd(m, rows, cols)?;
    Ok(factor_small(&g, 128).map(|f| f.into_iter().map(|(p, _)| p).collect()))
}

/// Saturate the row lattice of `h` (independent rows) at the prime p: while
/// a combination w·h of the rows is divisible by p, with w = -1 at a place
/// f (from the reduced echelon form of h^t modulo p, as for a left kernel),
/// row f gives way to w·h / p.
fn p_saturate(h: &mut Mat, p: &Integer) -> RResult<()> {
    let ctx = Ctx::residue_ring(p);
    let (r, n) = (h.nrows(), h.ncols());
    loop {
        let (e, pivots) = h.change_ring(&ctx).map_err(gr)?.transpose().rref().map_err(gr)?;
        let free: Vec<usize> = (0..r).filter(|j| !pivots.contains(j)).collect();
        if free.is_empty() {
            return Ok(());
        }
        let mut w = Mat::zero(h.ctx(), free.len(), r);
        for (s, &f) in free.iter().enumerate() {
            w.set_integer(s, f, &Integer::from_i64(-1)).map_err(gr)?;
            for (i, &c) in pivots.iter().enumerate() {
                w.set_integer(s, c, &e.entry(i, f).to_integer().map_err(gr)?).map_err(gr)?;
            }
        }
        let q = w.mul(h).map_err(gr)?;
        for (s, &f) in free.iter().enumerate() {
            for j in 0..n {
                h.set_integer(f, j, &q.integer(s, j).divexact(p)).map_err(gr)?;
            }
        }
    }
}

/// The saturation of the row lattice of `h` (independent rows) as the
/// lattice orthogonal to a basis of the kernel {v : h·v = 0}, which the
/// Hermite transform of h^t gives.
fn orthogonal_saturation(h: &Mat) -> RResult<Mat> {
    let (r, n) = (h.nrows(), h.ncols());
    let (_, u) = h.transpose().hnf_transform();
    let (_, u) = u.block(r, 0, n - r, n).transpose().hnf_transform();
    Ok(u.block(n - r, 0, r, n).hnf())
}

/// `HessenbergForm(A)`: zero above the superdiagonal, the transpose of
/// FLINT's upper Hessenberg form of the transpose.
fn hessenberg_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    if !x.m.over_field() {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a field"));
    }
    let h = x.m.transpose().hessenberg().map_err(gr)?.transpose();
    let ring = x.ring().clone();
    one(mat_value(it, &ring, h)?)
}

// ----- the primary decomposition ---------------------------------------------------------

fn exact_field(x: &Mtrx) -> RResult<()> {
    if x.m.over_field() && !x.m.floating() {
        return Ok(());
    }
    Err(RuntimeError::runtime("Coefficient ring of argument 1 is not an exact field"))
}

/// Argument 1 as a square matrix over an exact field, the ring checked
/// first.
fn field_square(a: &CallArgs) -> RResult<Rc<Mtrx>> {
    exact_field(mat_arg(a, 0)?)?;
    square(a, 0)
}

/// An irreducible factor q of the minimal polynomial, with the sizes k of
/// its blocks q^k in increasing order.
struct Prime {
    q: Elem,
    sizes: Vec<usize>,
}

impl Prime {
    fn degree(&self) -> usize {
        self.q.poly_len() - 1
    }
}

/// The primary decomposition of a matrix: its primes in the order of
/// `Factorization`, which are polynomials of the global polynomial ring
/// over its ring.
struct Primary {
    ring: Rc<Struct>,
    primes: Vec<Prime>,
}

fn primary(it: &mut Interp, x: &Mtrx) -> RResult<Primary> {
    let n = x.m.nrows();
    let base = x.ring().clone();
    let Value::Struct(ring) = it.poly_ring(&base, true)? else { unreachable!("a polynomial ring") };
    let cs = x.m.minpoly().map_err(gr)?;
    if cs.len() == 1 {
        return Ok(Primary { ring, primes: Vec::new() });
    }
    let f = polynomial(it, x, &cs)?;
    let Value::Seq(fs) = factorization(it, f)? else { unreachable!("a factorization") };
    let factors: Vec<(Elem, usize)> = fs
        .elems
        .iter()
        .map(|t| match t {
            Value::Tuple(t) => match (&t.elems[0], &t.elems[1]) {
                (Value::Elt(q), Value::Int(e)) => (q.x.clone(), e.to_u64().expect("an exponent") as usize),
                _ => unreachable!("a factor and its exponent"),
            },
            _ => unreachable!("a factor and its exponent"),
        })
        .collect();
    let ms = if cs.len() == n + 1 { factors.iter().map(|&(_, e)| e).collect() } else { multiplicities(it, x, &factors)? };
    let mut primes = Vec::with_capacity(factors.len());
    for ((q, e), m) in factors.into_iter().zip(ms) {
        primes.push(Prime { sizes: block_sizes(&x.m, &q, e, m)?, q });
    }
    Ok(Primary { ring, primes })
}

/// The multiplicities of the factors q^e of the minimal polynomial in the
/// characteristic polynomial: modularly over the rationals, else by
/// dividing the characteristic polynomial.
fn multiplicities(it: &mut Interp, x: &Mtrx, factors: &[(Elem, usize)]) -> RResult<Vec<usize>> {
    if matches!(x.m.ctx().kind(), CtxKind::Rationals)
        && let Some(ms) = modular_multiplicities(&x.m, factors)?
    {
        return Ok(ms);
    }
    let Value::Elt(c) = charpoly(it, x)? else { unreachable!("a polynomial") };
    let mut ms = Vec::with_capacity(factors.len());
    for (q, _) in factors {
        let (mut c, mut m) = (c.x.clone(), 0);
        loop {
            let (quo, rem) = c.poly_divrem(q).map_err(gr)?;
            if rem.poly_len() > 0 {
                break;
            }
            (c, m) = (quo, m + 1);
        }
        ms.push(m);
    }
    Ok(ms)
}

/// The sizes of the blocks for q, whose exponent in the minimal polynomial
/// is e and multiplicity in the characteristic polynomial m: one block when
/// m = e, all of size 1 when e = 1, 1 and e when m = e + 1, and otherwise
/// from d_k = dim ker q(A)^k, since (d_k - d_(k-1)) / deg q blocks have size
/// at least k.
fn block_sizes(a: &Mat, q: &Elem, e: usize, m: usize) -> RResult<Vec<usize>> {
    if m == e {
        return Ok(vec![e]);
    }
    if e == 1 {
        return Ok(vec![1; m]);
    }
    if m == e + 1 {
        return Ok(vec![1, e]);
    }
    let (n, d) = (a.nrows(), q.poly_len() - 1);
    let nq = eval(a, q)?;
    let mut dims = vec![0];
    let mut power = nq.clone();
    for k in 1..e {
        if k > 1 {
            power = power.mul(&nq).map_err(gr)?;
        }
        dims.push(n - power.rank().map_err(gr)?);
    }
    dims.push(m * d);
    let at_least: Vec<usize> = dims.windows(2).map(|w| (w[1] - w[0]) / d).collect();
    let mut sizes = Vec::with_capacity(m);
    for k in 1..=e {
        let exactly = at_least[k - 1] - at_least.get(k).copied().unwrap_or(0);
        sizes.extend(std::iter::repeat_n(k, exactly));
    }
    Ok(sizes)
}

/// q(A).
fn eval(a: &Mat, q: &Elem) -> RResult<Mat> {
    let cs: Vec<Elem> = (0..q.poly_len()).map(|i| q.poly_coeff(i)).collect();
    eval_coeffs(a, &cs)
}

/// v·q(A) for a row vector v and a monic q, by Horner's rule.
fn eval_at(v: &Mat, a: &Mat, q: &Elem) -> RResult<Mat> {
    let mut w = v.clone();
    for i in (0..q.poly_len() - 1).rev() {
        w = w.mul(a).map_err(gr)?;
        let c = q.poly_coeff(i);
        if c.is_zero() != Truth::True {
            w.submul_row_of(0, v, 0, &c.neg().map_err(gr)?).map_err(gr)?;
        }
    }
    Ok(w)
}

impl Primary {
    fn poly(&self, f: Elem) -> Value {
        make_elt(&self.ring, f)
    }

    fn universe(&self) -> Value {
        Value::Struct(self.ring.clone())
    }

    /// The blocks, as the prime and the size of each.
    fn blocks(&self) -> impl Iterator<Item = (&Prime, usize)> {
        self.primes.iter().flat_map(|p| p.sizes.iter().map(move |&k| (p, k)))
    }

    /// The number of invariant factors: the most blocks of any prime.
    fn count(&self) -> usize {
        self.primes.iter().map(|p| p.sizes.len()).max().unwrap_or(0)
    }

    /// The index of the block of prime p in invariant factor j, if any: the
    /// last invariant factor takes the largest block of every prime, the
    /// one before it the next largest, and so on.
    fn block_of(&self, p: &Prime, j: usize) -> Option<usize> {
        (j + p.sizes.len()).checked_sub(self.count())
    }

    /// The invariant factors, each dividing the next.
    fn invariant_factors(&self) -> RResult<Vec<Elem>> {
        let Some(first) = self.primes.first() else { return Ok(Vec::new()) };
        let one = Elem::one(first.q.ctx()).map_err(gr)?;
        let mut fs = Vec::with_capacity(self.count());
        for j in 0..self.count() {
            let mut f = one.clone();
            for p in &self.primes {
                if let Some(l) = self.block_of(p, j) {
                    f = f.mul(&p.q.pow_i64(p.sizes[l] as i64).map_err(gr)?).map_err(gr)?;
                }
            }
            fs.push(f);
        }
        Ok(fs)
    }

    fn invariant_factor_seq(&self) -> RResult<Value> {
        let fs = self.invariant_factors()?.into_iter().map(|f| self.poly(f)).collect();
        Ok(Value::seq(Some(self.universe()), fs))
    }

    /// The primary invariant factors: a pair <q, k> for each block.
    fn primary_seq(&self) -> Value {
        let pairs = Value::structure(StructKind::Cartesian(vec![self.universe(), Value::integers()]));
        let elems = self
            .blocks()
            .map(|(p, k)| Value::Tuple(Rc::new(Tuple { elems: vec![self.poly(p.q.clone()), Value::int(k as i64)], parent: Some(pairs.clone()) })))
            .collect();
        Value::seq(Some(pairs), elems)
    }

    fn same(&self, o: &Primary) -> bool {
        self.primes.len() == o.primes.len() && self.primes.iter().zip(&o.primes).all(|(p, q)| p.sizes == q.sizes && p.q.equal(&q.q) == Truth::True)
    }
}

// ----- the forms --------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq)]
enum Form {
    Rational,
    Primary,
    Jordan,
}

/// Put the companion matrix of the monic f at (at, at): 1s above the
/// diagonal and the negated coefficients of f in the last row.
fn companion(m: &mut Mat, at: usize, f: &Elem) -> RResult<usize> {
    let d = f.poly_len() - 1;
    for i in 1..d {
        m.set_si(at + i - 1, at + i, 1).map_err(gr)?;
    }
    for j in 0..d {
        m.set_entry(at + d - 1, at + j, &f.poly_coeff(j).neg().map_err(gr)?);
    }
    Ok(d)
}

/// The rational form (the companion matrices of the invariant factors), the
/// primary rational form (those of the q^k) or the Jordan form (for each
/// q^k, k companion matrices of q, each joined to the next by a 1 in its
/// last row).
fn form_matrix(a: &Mat, p: &Primary, which: Form) -> RResult<Mat> {
    let n = a.nrows();
    let mut m = Mat::zero(a.ctx(), n, n);
    let mut at = 0;
    match which {
        Form::Rational => {
            for f in p.invariant_factors()? {
                at += companion(&mut m, at, &f)?;
            }
        }
        Form::Primary => {
            for (pr, k) in p.blocks() {
                at += companion(&mut m, at, &pr.q.pow_i64(k as i64).map_err(gr)?)?;
            }
        }
        Form::Jordan => {
            for (pr, k) in p.blocks() {
                for l in 0..k {
                    let d = companion(&mut m, at, &pr.q)?;
                    if l + 1 < k {
                        m.set_si(at + d - 1, at + d, 1).map_err(gr)?;
                    }
                    at += d;
                }
            }
        }
    }
    debug_assert_eq!(at, n);
    Ok(m)
}

/// The rows v·A^i for i < len.
fn krylov(a: &Mat, v: &Mat, len: usize) -> RResult<Mat> {
    let mut k = Mat::zero(a.ctx(), len, a.ncols());
    let mut w = v.clone();
    for i in 0..len {
        if i > 0 {
            w = w.mul(a).map_err(gr)?;
        }
        k.insert(&w, i, 0);
    }
    Ok(k)
}

/// Whether a square matrix is invertible; over the rationals by its rank
/// modulo a prime, which can only be smaller: a no may be wrong.
fn invertible(k: &Mat) -> RResult<bool> {
    let n = k.nrows();
    if matches!(k.ctx().kind(), CtxKind::Rationals) {
        let p = large_primes().next().expect("a prime below 2^62");
        return Ok(k.change_ring(&Ctx::residue_ring(&p)).is_ok_and(|kp| kp.rank().is_ok_and(|r| r == n)));
    }
    Ok(k.rank().map_err(gr)? == n)
}

/// The Krylov matrix (the rows v·A^i, i < n) of a cyclic vector v of A, if
/// one is found among the first unit vector, the vector of 1s and a few
/// pseudo-random ones.
fn cyclic_krylov(a: &Mat) -> RResult<Option<Mat>> {
    let n = a.nrows();
    let mut seed = 0x9E37_79B9_7F4A_7C15u64;
    for attempt in 0..6 {
        let mut v = Mat::zero(a.ctx(), 1, n);
        for j in 0..n {
            let c = match attempt {
                0 => (j == 0) as i64,
                1 => 1,
                _ => {
                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    (seed >> 59) as i64 - 16
                }
            };
            v.set_si(0, j, c).map_err(gr)?;
        }
        let k = krylov(a, &v, n)?;
        if invertible(&k)? {
            return Ok(Some(k));
        }
    }
    Ok(None)
}

/// A subspace, by a basis in which each vector is zero at the pivots of the
/// ones before it and 1 at its own.
struct Span {
    rows: Vec<(Mat, usize)>,
}

impl Span {
    fn of(m: &Mat) -> RResult<Span> {
        if m.nrows() == 0 {
            return Ok(Span { rows: Vec::new() });
        }
        let (e, pivots) = m.rref().map_err(gr)?;
        Ok(Span { rows: pivots.iter().enumerate().map(|(i, &c)| (e.block(i, 0, 1, e.ncols()), c)).collect() })
    }

    /// v less its part in the span, and the first place where that is not
    /// zero (none when v is in the span).
    fn reduce(&self, v: &Mat) -> RResult<(Mat, Option<usize>)> {
        let mut w = v.clone();
        for (r, c) in &self.rows {
            if !w.entry_is_zero(0, *c) {
                let x = w.entry(0, *c);
                w.submul_row_of(0, r, 0, &x).map_err(gr)?;
            }
        }
        let first = (0..w.ncols()).find(|&j| !w.entry_is_zero(0, j));
        Ok((w, first))
    }

    fn contains(&self, v: &Mat) -> RResult<bool> {
        Ok(self.reduce(v)?.1.is_none())
    }

    /// Add the vectors v·A^i for i < d.
    fn add_orbit(&mut self, v: &Mat, a: &Mat, d: usize) -> RResult<()> {
        let mut h = v.clone();
        for i in 0..d {
            if i > 0 {
                h = h.mul(a).map_err(gr)?;
            }
            if let (mut w, Some(c)) = self.reduce(&h)? {
                let inv = w.entry(0, c).inv().map_err(gr)?;
                w.scale_row(0, &inv).map_err(gr)?;
                self.rows.push((w, c));
            }
        }
        Ok(())
    }
}

/// Generators for the blocks of the prime p, in the order of its sizes:
/// from the largest size down, vectors of a basis of ker N^k (N = q(A))
/// outside the span of ker N^(k-1) and of the vectors at that level of the
/// chains already taken (h·A^i for h = g·N^(s-k) and i < deg q).
fn prime_generators(a: &Mat, p: &Prime) -> RResult<Vec<Mat>> {
    let (n, d, top) = (a.nrows(), p.degree(), *p.sizes.last().expect("a block"));
    let nq = eval(a, &p.q)?;
    let mut kernels = vec![Mat::zero(a.ctx(), 0, n)];
    let mut power = nq.clone();
    for k in 1..=top {
        if k > 1 {
            power = power.mul(&nq).map_err(gr)?;
        }
        kernels.push(power.left_kernel().and_then(|k| k.rref()).map_err(gr)?.0);
    }
    let mut chosen: Vec<(Mat, usize)> = Vec::with_capacity(p.sizes.len());
    for k in (1..=top).rev() {
        let mut wanted = p.sizes.iter().filter(|&&s| s == k).count();
        if wanted == 0 {
            continue;
        }
        let mut span = Span::of(&kernels[k - 1])?;
        for (g, s) in &chosen {
            let mut h = g.clone();
            for _ in k..*s {
                h = eval_at(&h, a, &p.q)?;
            }
            span.add_orbit(&h, a, d)?;
        }
        for i in 0..kernels[k].nrows() {
            if wanted == 0 {
                break;
            }
            let b = kernels[k].block(i, 0, 1, n);
            if !span.contains(&b)? {
                span.add_orbit(&b, a, d)?;
                chosen.push((b, k));
                wanted -= 1;
            }
        }
        debug_assert_eq!(wanted, 0, "a generator for each block");
    }
    chosen.sort_by_key(|&(_, k)| k);
    Ok(chosen.into_iter().map(|(g, _)| g).collect())
}

/// Generators for the blocks of every prime: from a cyclic vector v when
/// every prime has one block (v·f(A)/q^e(A) for the prime q, where f is the
/// minimal polynomial), unless none is found; otherwise prime by prime.
fn generators(a: &Mat, p: &Primary, krylov: Option<&Mat>) -> RResult<Vec<Vec<Mat>>> {
    let Some(k) = krylov else { return p.primes.iter().map(|pr| prime_generators(a, pr)).collect() };
    let powers: Vec<Elem> = p.primes.iter().map(|pr| pr.q.pow_i64(pr.sizes[0] as i64).map_err(gr)).collect::<RResult<_>>()?;
    let f = powers.iter().try_fold(Elem::one(powers[0].ctx()).map_err(gr)?, |f, g| f.mul(g).map_err(gr))?;
    let mut gens = Vec::with_capacity(powers.len());
    for g in &powers {
        let h = f.poly_divrem(g).map_err(gr)?.0;
        let mut c = Mat::zero(a.ctx(), 1, a.nrows());
        for j in 0..h.poly_len() {
            c.set_entry(0, j, &h.poly_coeff(j));
        }
        gens.push(vec![c.mul(k).map_err(gr)?]);
    }
    Ok(gens)
}

/// T with T·A·T^-1 = F for the form F: its rows are bases of the cyclic
/// subspaces of the blocks of F. For the rational form, those of the sums
/// of the generators of the blocks of each invariant factor; for the
/// primary rational form, g·A^i for the generator g of a block q^k and
/// i < k·deg q; for the Jordan form, g·q(A)^l·A^i for l < k and i < deg q.
fn transformation(a: &Mat, p: &Primary, which: Form) -> RResult<Mat> {
    let n = a.nrows();
    let cyclic = n > 0 && p.primes.iter().all(|pr| pr.sizes.len() == 1);
    let k = if cyclic { cyclic_krylov(a)? } else { None };
    if let (Some(k), Form::Rational) = (&k, which) {
        return Ok(k.clone());
    }
    let gens = generators(a, p, k.as_ref())?;
    let mut t = Mat::zero(a.ctx(), n, n);
    let mut row = 0;
    match which {
        Form::Rational => {
            for j in 0..p.count() {
                let (mut v, mut len) = (Mat::zero(a.ctx(), 1, n), 0);
                for (pr, gs) in p.primes.iter().zip(&gens) {
                    if let Some(l) = p.block_of(pr, j) {
                        v = v.add(&gs[l]).map_err(gr)?;
                        len += pr.sizes[l] * pr.degree();
                    }
                }
                t.insert(&krylov(a, &v, len)?, row, 0);
                row += len;
            }
        }
        Form::Primary => {
            for (pr, gs) in p.primes.iter().zip(&gens) {
                for (g, &k) in gs.iter().zip(&pr.sizes) {
                    let len = k * pr.degree();
                    t.insert(&krylov(a, g, len)?, row, 0);
                    row += len;
                }
            }
        }
        Form::Jordan => {
            for (pr, gs) in p.primes.iter().zip(&gens) {
                for (g, &k) in gs.iter().zip(&pr.sizes) {
                    let mut h = g.clone();
                    for l in 0..k {
                        if l > 0 {
                            h = eval_at(&h, a, &pr.q)?;
                        }
                        t.insert(&krylov(a, &h, pr.degree())?, row, 0);
                        row += pr.degree();
                    }
                }
            }
        }
    }
    debug_assert_eq!(row, n);
    Ok(t)
}

/// `RationalForm`, `PrimaryRationalForm` and `JordanForm`: the form, T with
/// T·A·T^-1 = F, and the list of factors. A statement prints all three of
/// `PrimaryRationalForm` but only the form of the others.
fn canonical_form(it: &mut Interp, a: &CallArgs, which: Form) -> RResult<Vals> {
    let x = field_square(a)?;
    let p = primary(it, &x)?;
    let ring = x.ring().clone();
    let f = mat_value(it, &ring, form_matrix(&x.m, &p, which)?)?;
    let all = if which == Form::Primary { a.nresults != 1 } else { a.nresults >= 2 };
    if !all {
        return one(f);
    }
    let t = mat_value(it, &ring, transformation(&x.m, &p, which)?)?;
    let list = if which == Form::Rational { p.invariant_factor_seq()? } else { p.primary_seq() };
    Ok(vals![f, t, list])
}

fn rational_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    canonical_form(it, a, Form::Rational)
}

fn primary_rational_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    canonical_form(it, a, Form::Primary)
}

fn jordan_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    canonical_form(it, a, Form::Jordan)
}

fn invariant_factors(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = field_square(a)?;
    one(primary(it, &x)?.invariant_factor_seq()?)
}

fn primary_invariant_factors(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = field_square(a)?;
    one(primary(it, &x)?.primary_seq())
}

/// `IsSimilar(A, B)`: whether A and B have the same invariant factors, over
/// the ring of A if B coerces into it and else over that of B; and if so T
/// with T·A·T^-1 = B, from the transformations to their rational form.
fn is_similar(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y) = (mat_arg(a, 0)?.clone(), mat_arg(a, 1)?.clone());
    exact_field(&x)?;
    if x.type_id() != y.type_id() {
        return Err(with_types(it, a, "Bad argument types"));
    }
    let x = square(a, 0)?;
    let n = x.m.nrows();
    if y.m.nrows() != n || y.m.ncols() != n {
        return Err(with_types(it, a, "Arguments are not compatible"));
    }
    let (ring, xm, ym) = match coerced(it, &y, x.ring())? {
        Some(ym) => (x.ring().clone(), x.m.clone(), ym),
        None => match coerced(it, &x, y.ring())? {
            Some(xm) => (y.ring().clone(), xm, y.m.clone()),
            None => return Err(with_types(it, a, "Arguments are not compatible")),
        },
    };
    let algebra = parent(it, &ring, n, n, Shape::Algebra)?;
    let (x, y) = (Mtrx { parent: algebra.clone(), m: xm }, Mtrx { parent: algebra, m: ym });
    exact_field(&x).map_err(|_| with_types(it, a, "Arguments are not compatible"))?;
    let (px, py) = (primary(it, &x)?, primary(it, &y)?);
    if !px.same(&py) {
        return Ok(vals![Value::Bool(false), Value::Undef]);
    }
    if a.nresults < 2 {
        return boolv(true);
    }
    let tx = transformation(&x.m, &px, Form::Rational)?;
    let ty = transformation(&y.m, &py, Form::Rational)?;
    let t = ty.inv().map_err(gr)?.mul(&tx).map_err(gr)?;
    Ok(vals![Value::Bool(true), mat_value(it, &ring, t)?])
}

// ----- the Frobenius form of an alternating matrix ------------------------------------------

/// The basis of `b` of the Frobenius form of the alternating form with the
/// Gram matrix `g`, and the diagonal D: pairs e, f are taken in turn, the
/// pair of least nonzero pairing (the first in row-major order, ordered so
/// that it is positive), and the other vectors are made orthogonal to both
/// by b - [<b, f>/g]·e + [<b, e>/g]·f for g = <e, f> (floor division),
/// starting over whenever that leaves a remainder. The pairs are sorted by
/// their pairings, and the basis is e_1, ..., e_n, f_1, ..., f_n.
fn frobenius_alternating(g: &Mat) -> (Vec<Vec<Integer>>, Vec<Integer>) {
    let n = g.nrows();
    let mut gram: Vec<Vec<Integer>> = (0..n).map(|i| (0..n).map(|j| g.integer(i, j)).collect()).collect();
    let mut basis: Vec<Vec<Integer>> = (0..n).map(|i| (0..n).map(|j| Integer::from_i64((i == j) as i64)).collect()).collect();
    // b_k + c·b_j, with the Gram matrix kept up to date.
    let add = |basis: &mut Vec<Vec<Integer>>, gram: &mut Vec<Vec<Integer>>, k: usize, j: usize, c: &Integer| {
        if c.is_zero() {
            return;
        }
        for l in 0..n {
            basis[k][l] = &basis[k][l] + &(c * &basis[j][l]);
            gram[k][l] = &gram[k][l] + &(c * &gram[j][l]);
        }
        for row in gram.iter_mut() {
            row[k] = &row[k] + &(c * &row[j]);
        }
    };
    let mut rest: Vec<usize> = (0..n).collect();
    let (mut es, mut fs, mut ds) = (Vec::new(), Vec::new(), Vec::new());
    while !rest.is_empty() {
        'pair: loop {
            let mut least: Option<(usize, usize)> = None;
            for (a, &i) in rest.iter().enumerate() {
                for &j in &rest[a + 1..] {
                    if !gram[i][j].is_zero() && least.is_none_or(|(s, t)| gram[i][j].cmp_abs(&gram[s][t]) == Ordering::Less) {
                        least = Some((i, j));
                    }
                }
            }
            let (i, j) = least.expect("a non-singular form");
            let (e, f) = if gram[i][j].sign() > 0 { (i, j) } else { (j, i) };
            let d = gram[e][f].clone();
            for &k in &rest {
                if k == e || k == f {
                    continue;
                }
                let (qf, rf) = gram[k][f].fdiv_qr(&d).expect("a nonzero pairing");
                let (qe, re) = gram[k][e].fdiv_qr(&d).expect("a nonzero pairing");
                add(&mut basis, &mut gram, k, e, &-&qf);
                add(&mut basis, &mut gram, k, f, &qe);
                if !rf.is_zero() || !re.is_zero() {
                    continue 'pair;
                }
            }
            es.push(e);
            fs.push(f);
            ds.push(d);
            rest.retain(|&k| k != e && k != f);
            break;
        }
    }
    let mut order: Vec<usize> = (0..ds.len()).collect();
    order.sort_by(|&i, &j| ds[i].cmp(&ds[j]));
    let rows = order.iter().map(|&i| es[i]).chain(order.iter().map(|&i| fs[i]));
    (rows.map(|k| basis[k].clone()).collect(), order.iter().map(|&i| ds[i].clone()).collect())
}

/// `FrobeniusFormAlternating(A)`: for a non-singular alternating integer
/// matrix A, F = [0 D; -D 0] with D diagonal and positive, and B with
/// B·A·B^t = F. The errors are raised in Magma's package code, unnamed.
fn frobenius_form_alternating(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let error = |msg: &str| Err(bare(RuntimeError::runtime(msg)));
    match x.m.ctx().kind() {
        CtxKind::Integers => {}
        CtxKind::Rationals => return error("The argument must have integer entries"),
        _ => {
            let t = it.type_name(x.ring());
            return Err(hidden_inner(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {t}, RngInt"))));
        }
    }
    let (m, n) = (&x.m, x.m.nrows());
    if n == 0 {
        return error("The argument must have more than 0 rows");
    }
    if n % 2 == 1 {
        return error("The argument must have an even number of rows");
    }
    let alternating = (0..n).all(|i| m.entry_is_zero(i, i) && (i + 1..n).all(|j| m.integer(i, j) == -&m.integer(j, i)));
    if !alternating {
        return error("The argument must be an alternating matrix");
    }
    if m.det().map_err(gr)?.is_zero() == Truth::True {
        return error("The matrix must be non-singular");
    }
    let (basis, ds) = frobenius_alternating(m);
    let h = n / 2;
    let mut f = Mat::zero(m.ctx(), n, n);
    for (i, d) in ds.iter().enumerate() {
        f.set_integer(i, h + i, d).map_err(gr)?;
        f.set_integer(h + i, i, &-d).map_err(gr)?;
    }
    let mut b = Mat::zero(m.ctx(), n, n);
    for (i, row) in basis.iter().enumerate() {
        for (j, v) in row.iter().enumerate() {
            b.set_integer(i, j, v).map_err(gr)?;
        }
    }
    if a.nresults == 1 {
        return one(like(&x, f));
    }
    Ok(vals![like(&x, f), like(&x, b)])
}

pub fn register(it: &mut Interp) {
    it.def("SmithForm", "A::Mtrx -> Mtrx, AlgMatElt, AlgMatElt", "The Smith form S of A and unimodular P and Q with P*A*Q = S.", smith_form);
    it.def("ElementaryDivisors", "A::Mtrx -> [RngElt]", "The nonzero entries of the diagonal of the Smith form of A.", elementary_divisors);
    it.def("Saturation", "A::Mtrx -> Mtrx", "A basis of the integer vectors with a nonzero multiple in the row lattice of A.", saturation);
    it.def("HessenbergForm", "A::Mtrx -> AlgMatElt", "A Hessenberg form of A, zero above the superdiagonal.", hessenberg_form);
    it.def("InvariantFactors", "A::Mtrx -> [RngUPolElt]", "The invariant factors of A, each dividing the next.", invariant_factors);
    it.def("PrimaryInvariantFactors", "A::Mtrx -> [Tup]", "The primary invariant factors <q, k> of A.", primary_invariant_factors);
    let doc = "The rational form F of A, T with T*A*T^-1 = F and the invariant factors.";
    it.def("RationalForm", "A::Mtrx -> AlgMatElt, AlgMatElt, [RngUPolElt]", doc, rational_form);
    let doc = "The primary rational form F of A, T with T*A*T^-1 = F and the primary invariant factors.";
    it.def("PrimaryRationalForm", "A::Mtrx -> AlgMatElt, AlgMatElt, [Tup]", doc, primary_rational_form);
    let doc = "The Jordan form F of A, T with T*A*T^-1 = F and the primary invariant factors.";
    it.def("JordanForm", "A::Mtrx -> AlgMatElt, AlgMatElt, [Tup]", doc, jordan_form);
    it.def("IsSimilar", "A::Mtrx, B::Mtrx -> BoolElt, AlgMatElt", "Whether A and B are similar, and T with T*A*T^-1 = B.", is_similar);
    let doc = "The Frobenius form F of the alternating matrix A and B with B*A*Transpose(B) = F.";
    it.def("FrobeniusFormAlternating", "A::AlgMatElt -> AlgMatElt, AlgMatElt", doc, frobenius_form_alternating).package = true;
}
