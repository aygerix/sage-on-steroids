//! Numerical linear algebra over the real and complex fields.
//!
//! All computations use FLINT's arbitrary-precision floating-point elements
//! with guard bits. Decompositions use Householder transformations; the SVD
//! uses one-sided Jacobi rotations, and eigenvalues use FLINT's shifted QR
//! iteration.

use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::gr::{Ctx, CtxKind, Elem, GrError};
use calyx_flint::mat::Mat;
use calyx_flint::{Integer, Real};

use super::linalg::gr;
use super::{Mtrx, Shape, mat_arg, mat_value, parent, square, vec_value};
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::{intv, one};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

const GUARD_BITS: u64 = 32;

fn bad() -> RuntimeError {
    RuntimeError::runtime("Bad argument types")
}

fn bool_param(a: &CallArgs, name: &str) -> RResult<bool> {
    match a.param(name) {
        Some(Value::Bool(v)) => Ok(*v),
        _ => Err(bad()),
    }
}

fn kind(m: &Mtrx) -> RResult<(u64, bool)> {
    match m.m.ctx().kind() {
        CtxKind::RealFloat(p) => Ok((*p, false)),
        CtxKind::ComplexFloat(p) => Ok((*p, true)),
        _ => Err(RuntimeError::runtime("Numerical linear algebra requires a matrix over a real or complex field")),
    }
}

fn work(m: &Mtrx) -> RResult<(Mat, u64, bool)> {
    let (bits, complex) = kind(m)?;
    let ctx = if complex { Ctx::complex_float(bits + GUARD_BITS) } else { Ctx::real_float(bits + GUARD_BITS) };
    Ok((m.m.change_ring(&ctx).map_err(gr)?, bits, complex))
}

fn work_svd(m: &Mtrx) -> RResult<(Mat, u64, bool)> {
    let (bits, complex) = kind(m)?;
    let work_bits = bits.saturating_mul(2).saturating_add(GUARD_BITS);
    let ctx = if complex { Ctx::complex_float(work_bits) } else { Ctx::real_float(work_bits) };
    Ok((m.m.change_ring(&ctx).map_err(gr)?, bits, complex))
}

fn round(m: &Mat, ctx: &Rc<Ctx>) -> RResult<Mat> {
    m.change_ring(ctx).map_err(gr)
}

fn adjoint(a: &Mat) -> RResult<Mat> {
    let mut b = Mat::zero(a.ctx(), a.ncols(), a.nrows());
    for i in 0..a.nrows() {
        for j in 0..a.ncols() {
            b.set_entry(j, i, &a.entry(i, j).conj().map_err(gr)?);
        }
    }
    Ok(b)
}

fn abs_real(x: &Elem) -> Real {
    match x.ctx().kind() {
        CtxKind::RealFloat(_) => x.to_real().unwrap().abs(),
        CtxKind::ComplexFloat(_) => {
            let (re, im) = x.to_complex_parts().unwrap();
            re.sqr().add(&im.sqr()).sqrt()
        }
        _ => unreachable!(),
    }
}

fn real_elem(ctx: &Rc<Ctx>, x: &Real) -> Result<Elem, GrError> {
    Elem::from_real(ctx, x)
}

fn unit_roundoff(bits: u64) -> Real {
    Real::from_i64(1, bits).mul_2exp(8 - bits as i64)
}

fn dot_cols(a: &Mat, p: usize, q: usize) -> RResult<Elem> {
    let mut s = Elem::new(a.ctx());
    for i in 0..a.nrows() {
        s = s.add(&a.entry(i, p).conj().map_err(gr)?.mul(&a.entry(i, q)).map_err(gr)?).map_err(gr)?;
    }
    Ok(s)
}

fn norm_col(a: &Mat, j: usize) -> RResult<Real> {
    Ok(abs_real(&dot_cols(a, j, j)?).sqrt())
}

/// The vector and scalar of H = I - beta v v*, with Hx a multiple of e1.
fn reflector(x: Vec<Elem>) -> RResult<Option<(Vec<Elem>, Elem)>> {
    if x.is_empty() {
        return Ok(None);
    }
    let ctx = x[0].ctx().clone();
    let mut n2 = Elem::new(&ctx);
    for z in &x {
        n2 = n2.add(&z.conj().map_err(gr)?.mul(z).map_err(gr)?).map_err(gr)?;
    }
    let norm = abs_real(&n2).sqrt();
    if norm.is_zero() {
        return Ok(None);
    }
    let a0 = abs_real(&x[0]);
    let phase = if a0.is_zero() {
        Elem::one(&ctx).map_err(gr)?
    } else {
        x[0].div(&real_elem(&ctx, &a0).map_err(gr)?).map_err(gr)?
    };
    let alpha = phase.mul(&real_elem(&ctx, &norm).map_err(gr)?).map_err(gr)?.neg().map_err(gr)?;
    let mut v = x;
    v[0] = v[0].sub(&alpha).map_err(gr)?;
    let mut d = Elem::new(&ctx);
    for z in &v {
        d = d.add(&z.conj().map_err(gr)?.mul(z).map_err(gr)?).map_err(gr)?;
    }
    if abs_real(&d).is_zero() {
        return Ok(None);
    }
    let two = Elem::from_integer(&ctx, &Integer::from_u64(2)).map_err(gr)?;
    Ok(Some((v, two.div(&d).map_err(gr)?)))
}

fn apply_left(a: &mut Mat, start: usize, v: &[Elem], beta: &Elem) -> RResult<()> {
    for j in 0..a.ncols() {
        let mut s = Elem::new(a.ctx());
        for k in 0..v.len() {
            s = s.add(&v[k].conj().map_err(gr)?.mul(&a.entry(start + k, j)).map_err(gr)?).map_err(gr)?;
        }
        s = beta.mul(&s).map_err(gr)?;
        for k in 0..v.len() {
            a.set_entry(start + k, j, &a.entry(start + k, j).sub(&v[k].mul(&s).map_err(gr)?).map_err(gr)?);
        }
    }
    Ok(())
}

fn apply_right(a: &mut Mat, start: usize, v: &[Elem], beta: &Elem) -> RResult<()> {
    for i in 0..a.nrows() {
        let mut s = Elem::new(a.ctx());
        for k in 0..v.len() {
            s = s.add(&a.entry(i, start + k).mul(&v[k]).map_err(gr)?).map_err(gr)?;
        }
        s = s.mul(beta).map_err(gr)?;
        for k in 0..v.len() {
            let t = s.mul(&v[k].conj().map_err(gr)?).map_err(gr)?;
            a.set_entry(i, start + k, &a.entry(i, start + k).sub(&t).map_err(gr)?);
        }
    }
    Ok(())
}

/// A = Q R, with square Q, by Householder transformations.
fn qr(a: &Mat) -> RResult<(Mat, Mat)> {
    let (m, n) = (a.nrows(), a.ncols());
    let mut r = a.clone();
    let mut left = Mat::identity(a.ctx(), m).map_err(gr)?;
    for k in 0..m.min(n) {
        let x = (k..m).map(|i| r.entry(i, k)).collect();
        if let Some((v, beta)) = reflector(x)? {
            apply_left(&mut r, k, &v, &beta)?;
            apply_left(&mut left, k, &v, &beta)?;
        }
    }
    Ok((adjoint(&left)?, r))
}

/// Scale the last factor pair without changing RQ, making det(Q) one.
fn normalize_rq(r: &mut Mat, q: &mut Mat) -> RResult<()> {
    let n = q.nrows();
    if n == 0 {
        return Ok(());
    }
    let d = q.det().map_err(gr)?;
    if abs_real(&d).is_zero() {
        return Ok(());
    }
    let c = d.inv().map_err(gr)?;
    for j in 0..n {
        q.set_entry(n - 1, j, &q.entry(n - 1, j).mul(&c).map_err(gr)?);
    }
    for i in 0..r.nrows() {
        r.set_entry(i, n - 1, &r.entry(i, n - 1).mul(&d).map_err(gr)?);
    }
    Ok(())
}

fn rq_mat(a: &Mat) -> RResult<(Mat, Mat)> {
    let (q0, r0) = qr(&adjoint(a)?)?;
    let (mut r, mut q) = (adjoint(&r0)?, adjoint(&q0)?);
    normalize_rq(&mut r, &mut q)?;
    Ok((r, q))
}

fn rq_decomposition(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let (w, _, _) = work(&x)?;
    let (r, q) = rq_mat(&w)?;
    Ok(vals![mat_value(it, x.ring(), round(&r, x.m.ctx())?)?, mat_value(it, x.ring(), round(&q, x.m.ctx())?)?])
}

fn ql_decomposition(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let (w, _, _) = work(&x)?;
    let (r, q) = rq_mat(&adjoint(&w)?)?;
    let (q, l) = (adjoint(&q)?, adjoint(&r)?);
    Ok(vals![mat_value(it, x.ring(), round(&q, x.m.ctx())?)?, mat_value(it, x.ring(), round(&l, x.m.ctx())?)?])
}

struct Svd {
    s: Mat,
    u: Mat,
    v: Mat,
    sigma: Vec<Real>,
}

fn rotate_cols(a: &mut Mat, p: usize, q: usize, c: &Elem, s: &Elem, phase: &Elem) -> RResult<()> {
    let sp = s.mul(phase).map_err(gr)?;
    let sc = s.mul(&phase.conj().map_err(gr)?).map_err(gr)?;
    for i in 0..a.nrows() {
        let (x, y) = (a.entry(i, p), a.entry(i, q));
        a.set_entry(i, p, &c.mul(&x).map_err(gr)?.add(&sc.mul(&y).map_err(gr)?).map_err(gr)?);
        a.set_entry(i, q, &c.mul(&y).map_err(gr)?.sub(&sp.mul(&x).map_err(gr)?).map_err(gr)?);
    }
    Ok(())
}

/// SVD for a matrix with at least as many rows as columns.
fn svd_tall(a: &Mat) -> RResult<Svd> {
    let (m, n) = (a.nrows(), a.ncols());
    let bits = match a.ctx().kind() { CtxKind::RealFloat(p) | CtxKind::ComplexFloat(p) => *p, _ => unreachable!() };
    let tol = unit_roundoff(bits);
    let mut b = a.clone();
    let mut q = Mat::identity(a.ctx(), n).map_err(gr)?;
    let max_sweeps = (12usize).max(8 * n.max(1));
    for _ in 0..max_sweeps {
        let mut changed = false;
        for p in 0..n {
            for j in p + 1..n {
                let alpha = abs_real(&dot_cols(&b, p, p)?);
                let beta = abs_real(&dot_cols(&b, j, j)?);
                let gamma_e = dot_cols(&b, p, j)?;
                let gamma = abs_real(&gamma_e);
                if gamma.is_zero() || gamma.cmp_magma(&tol.mul(&alpha.mul(&beta).sqrt())) != Ordering::Greater {
                    continue;
                }
                let tau = beta.sub(&alpha).div(&gamma.mul_i64(2)).unwrap();
                let t = if tau.is_zero() {
                    Real::from_i64(1, bits)
                } else {
                    let den = tau.abs().add(&Real::from_i64(1, bits).add(&tau.sqr()).sqrt());
                    Real::from_i64(-(tau.sign() as i64), bits).div(&den).unwrap()
                };
                let c = Real::from_i64(1, bits).div(&Real::from_i64(1, bits).add(&t.sqr()).sqrt()).unwrap();
                let s = c.mul(&t);
                let phase = gamma_e.div(&real_elem(a.ctx(), &gamma).map_err(gr)?).map_err(gr)?;
                let (ce, se) = (real_elem(a.ctx(), &c).map_err(gr)?, real_elem(a.ctx(), &s).map_err(gr)?);
                rotate_cols(&mut b, p, j, &ce, &se, &phase)?;
                rotate_cols(&mut q, p, j, &ce, &se, &phase)?;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut sigma: Vec<Real> = (0..n).map(|j| norm_col(&b, j)).collect::<RResult<_>>()?;
    for i in 0..n {
        let Some(j) = (i..n).max_by(|&p, &q0| sigma[p].cmp_magma(&sigma[q0])) else { continue };
        if i != j {
            sigma.swap(i, j);
            b.swap_cols(i, j);
            q.swap_cols(i, j);
        }
    }
    let cutoff = sigma.first().map_or_else(|| Real::zero(bits), |x| x.mul(&tol));
    let rank = sigma.iter().take_while(|x| x.cmp_magma(&cutoff) == Ordering::Greater).count();
    let mut pmat = Mat::zero(a.ctx(), m, m);
    for j in 0..rank {
        let d = real_elem(a.ctx(), &sigma[j]).map_err(gr)?;
        for i in 0..m {
            pmat.set_entry(i, j, &b.entry(i, j).div(&d).map_err(gr)?);
        }
    }
    let one = Elem::one(a.ctx()).map_err(gr)?;
    let mut col = rank;
    for seed in 0..m {
        if col == m { break; }
        let mut z = vec![Elem::new(a.ctx()); m];
        z[seed] = one.clone();
        for _ in 0..2 {
            for j in 0..col {
                let mut d = Elem::new(a.ctx());
                for i in 0..m {
                    d = d.add(&pmat.entry(i, j).conj().map_err(gr)?.mul(&z[i]).map_err(gr)?).map_err(gr)?;
                }
                for i in 0..m {
                    z[i] = z[i].sub(&pmat.entry(i, j).mul(&d).map_err(gr)?).map_err(gr)?;
                }
            }
        }
        let mut d = Elem::new(a.ctx());
        for x in &z { d = d.add(&x.conj().map_err(gr)?.mul(x).map_err(gr)?).map_err(gr)?; }
        let norm = abs_real(&d).sqrt();
        if norm.cmp_magma(&tol) != Ordering::Greater { continue; }
        let ne = real_elem(a.ctx(), &norm).map_err(gr)?;
        for i in 0..m { pmat.set_entry(i, col, &z[i].div(&ne).map_err(gr)?); }
        col += 1;
    }
    let mut s = Mat::zero(a.ctx(), m, n);
    for i in 0..rank {
        s.set_entry(i, i, &real_elem(a.ctx(), &sigma[i]).map_err(gr)?);
    }
    Ok(Svd { s, u: adjoint(&pmat)?, v: adjoint(&q)?, sigma })
}

/// SVD through the Hermitian Gram matrix and FLINT's shifted QR eigensolver.
/// This is substantially faster than Jacobi for moderate and large matrices;
/// the extra guard bits offset the precision lost by squaring the condition
/// number. Small matrices stay on Jacobi, which handles clustered zero
/// singular values especially well.
fn svd_eigen_tall(a: &Mat) -> RResult<Svd> {
    let (m, n) = (a.nrows(), a.ncols());
    let (bits, real) = match a.ctx().kind() {
        CtxKind::RealFloat(p) => (*p, true),
        CtxKind::ComplexFloat(p) => (*p, false),
        _ => unreachable!(),
    };
    let cctx = Ctx::complex_float(bits);
    let ac = a.change_ring(&cctx).map_err(gr)?;
    let gram = adjoint(&ac)?.mul(&ac).map_err(gr)?;
    let (es, mut q) = gram.approx_eigen().map_err(gr)?;
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by(|&i, &j| {
        let (xi, _) = es[i].to_complex_parts().unwrap();
        let (xj, _) = es[j].to_complex_parts().unwrap();
        xj.cmp_magma(&xi)
    });
    q = q.select(&(0..n).collect::<Vec<_>>(), &order);
    let zero = Real::zero(bits);
    let sigma: Vec<Real> = order.iter().map(|&i| {
        let (x, _) = es[i].to_complex_parts().unwrap();
        if x.sign() > 0 { x.sqrt() } else { zero.clone() }
    }).collect();
    let tol = unit_roundoff(bits);
    // Fix arbitrary eigenvector phases, then reorthogonalize (also within
    // repeated eigenspaces, where the eigensolver's vectors are non-unique).
    for j in 0..n {
        let pivot = (0..n).max_by(|&r, &s| abs_real(&q.entry(r, j)).cmp_magma(&abs_real(&q.entry(s, j))));
        if let Some(r) = pivot {
            let z = q.entry(r, j);
            let az = abs_real(&z);
            if !az.is_zero() {
                let phase = z.div(&real_elem(&cctx, &az).map_err(gr)?).map_err(gr)?.conj().map_err(gr)?;
                for i in 0..n { q.set_entry(i, j, &q.entry(i, j).mul(&phase).map_err(gr)?); }
            }
        }
        for _ in 0..2 {
            for k in 0..j {
                let d = dot_cols(&q, k, j)?;
                for i in 0..n { q.set_entry(i, j, &q.entry(i, j).sub(&q.entry(i, k).mul(&d).map_err(gr)?).map_err(gr)?); }
            }
        }
        let d = norm_col(&q, j)?;
        if d.cmp_magma(&tol) == Ordering::Greater {
            let de = real_elem(&cctx, &d).map_err(gr)?;
            for i in 0..n { q.set_entry(i, j, &q.entry(i, j).div(&de).map_err(gr)?); }
        }
    }
    let b = ac.mul(&q).map_err(gr)?;
    let cutoff = sigma.first().map_or_else(|| Real::zero(bits), |x| x.mul(&tol));
    let rank = sigma.iter().take_while(|x| x.cmp_magma(&cutoff) == Ordering::Greater).count();
    let mut pmat = Mat::zero(&cctx, m, m);
    for j in 0..rank {
        let d = real_elem(&cctx, &sigma[j]).map_err(gr)?;
        for i in 0..m { pmat.set_entry(i, j, &b.entry(i, j).div(&d).map_err(gr)?); }
    }
    let one = Elem::one(&cctx).map_err(gr)?;
    let mut col = rank;
    for seed in 0..m {
        if col == m { break; }
        let mut z = vec![Elem::new(&cctx); m];
        z[seed] = one.clone();
        for _ in 0..2 {
            for j in 0..col {
                let mut d = Elem::new(&cctx);
                for i in 0..m { d = d.add(&pmat.entry(i, j).conj().map_err(gr)?.mul(&z[i]).map_err(gr)?).map_err(gr)?; }
                for i in 0..m { z[i] = z[i].sub(&pmat.entry(i, j).mul(&d).map_err(gr)?).map_err(gr)?; }
            }
        }
        let mut d = Elem::new(&cctx);
        for x in &z { d = d.add(&x.conj().map_err(gr)?.mul(x).map_err(gr)?).map_err(gr)?; }
        let norm = abs_real(&d).sqrt();
        if norm.cmp_magma(&tol) != Ordering::Greater { continue; }
        let ne = real_elem(&cctx, &norm).map_err(gr)?;
        for i in 0..m { pmat.set_entry(i, col, &z[i].div(&ne).map_err(gr)?); }
        col += 1;
    }
    let mut s = Mat::zero(&cctx, m, n);
    for i in 0..rank { s.set_entry(i, i, &real_elem(&cctx, &sigma[i]).map_err(gr)?); }
    let mut z = Svd { s, u: adjoint(&pmat)?, v: adjoint(&q)?, sigma };
    if real {
        let to_real = |x: &Mat| -> RResult<Mat> {
            let mut y = Mat::zero(a.ctx(), x.nrows(), x.ncols());
            for i in 0..x.nrows() {
                for j in 0..x.ncols() {
                    let (re, _) = x.entry(i, j).to_complex_parts().unwrap();
                    y.set_entry(i, j, &real_elem(a.ctx(), &re).map_err(gr)?);
                }
            }
            Ok(y)
        };
        z.s = to_real(&z.s)?;
        z.u = to_real(&z.u)?;
        z.v = to_real(&z.v)?;
    }
    Ok(z)
}

fn svd(a: &Mat) -> RResult<Svd> {
    if a.nrows() >= a.ncols() {
        if a.ncols() >= 16 { svd_eigen_tall(a) } else { svd_tall(a) }
    } else {
        let ah = adjoint(a)?;
        let t = if ah.ncols() >= 16 { svd_eigen_tall(&ah)? } else { svd_tall(&ah)? };
        Ok(Svd { s: adjoint(&t.s)?, u: t.v, v: t.u, sigma: t.sigma })
    }
}

fn svd_jacobi(a: &Mat) -> RResult<Svd> {
    if a.nrows() >= a.ncols() {
        svd_tall(a)
    } else {
        let t = svd_tall(&adjoint(a)?)?;
        Ok(Svd { s: adjoint(&t.s)?, u: t.v, v: t.u, sigma: t.sigma })
    }
}

fn epsilon(a: &CallArgs, bits: u64, dimension: usize, sigma: &[Real]) -> RResult<Real> {
    match a.param("Epsilon") {
        Some(Value::Undef) | None => {
            Ok(sigma.first().map_or_else(|| Real::zero(bits), |x| x.mul(&unit_roundoff(bits)).mul_integer(&Integer::from_u64(dimension as u64))))
        }
        Some(Value::Real(x)) => Ok(x.x.round_to(bits).abs()),
        _ => Err(bad()),
    }
}

fn numerical_rank_of(a: &CallArgs, bits: u64, matrix: &Mat, sigma: &[Real]) -> RResult<usize> {
    let e = epsilon(a, bits, matrix.nrows().max(matrix.ncols()), sigma)?;
    Ok(sigma.iter().filter(|x| x.cmp_magma(&e) == Ordering::Greater).count())
}

fn numerical_inverse(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    if x.m.nrows() == 0 { return Err(RuntimeError::runtime("Argument 1 has degree zero")); }
    let (w, bits, _) = work_svd(&x)?;
    let z = svd_jacobi(&w)?;
    if numerical_rank_of(a, bits, &w, &z.sigma)? != w.nrows() {
        return Err(RuntimeError::runtime("Matrix is numerically singular"));
    }
    let p = pseudoinverse_of(&z, w.nrows())?;
    one(mat_value(it, x.ring(), round(&p, x.m.ctx())?)?)
}

fn numerical_rank(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let (w, bits, _) = work_svd(&x)?;
    let z = svd_jacobi(&w)?;
    intv(Integer::from_u64(numerical_rank_of(a, bits, &w, &z.sigma)? as u64))
}

fn kernel_of(z: &Svd, rank: usize) -> Mat {
    z.u.block(rank, 0, z.u.nrows() - rank, z.u.ncols())
}

fn image_of(z: &Svd, rank: usize) -> Mat {
    z.v.block(0, 0, rank, z.v.ncols())
}

fn numerical_kernel(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let (w, bits, _) = work_svd(&x)?;
    let z = svd_jacobi(&w)?;
    let rank = numerical_rank_of(a, bits, &w, &z.sigma)?;
    one(mat_value(it, x.ring(), round(&kernel_of(&z, rank), x.m.ctx())?)?)
}

fn numerical_image(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let (w, bits, _) = work_svd(&x)?;
    let z = svd_jacobi(&w)?;
    let rank = numerical_rank_of(a, bits, &w, &z.sigma)?;
    one(mat_value(it, x.ring(), round(&image_of(&z, rank), x.m.ctx())?)?)
}

fn pseudoinverse_of(z: &Svd, rank: usize) -> RResult<Mat> {
    let mut sp = Mat::zero(z.s.ctx(), z.s.ncols(), z.s.nrows());
    for i in 0..rank.min(z.sigma.len()) {
        let d = real_elem(z.s.ctx(), &z.sigma[i]).map_err(gr)?;
        sp.set_entry(i, i, &d.inv().map_err(gr)?);
    }
    adjoint(&z.v)?.mul(&sp).map_err(gr)?.mul(&z.u).map_err(gr)
}

fn numerical_pseudoinverse(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let (w, bits, _) = work_svd(&x)?;
    let z = svd_jacobi(&w)?;
    let rank = numerical_rank_of(a, bits, &w, &z.sigma)?;
    one(mat_value(it, x.ring(), round(&pseudoinverse_of(&z, rank)?, x.m.ctx())?)?)
}

fn solve_numerically(_it: &mut Interp, a: &mut CallArgs) -> RResult<(Rc<Mtrx>, Rc<Mtrx>, Mat, Mat, bool)> {
    let x = mat_arg(a, 0)?.clone();
    let y = mat_arg(a, 1)?.clone();
    kind(&x)?;
    if y.m.ncols() != x.m.ncols() || y.ring() != x.ring() {
        return Err(RuntimeError::runtime("Arguments have incompatible dimensions or coefficient rings"));
    }
    let (w, bits, _) = work_svd(&x)?;
    let yw = y.m.change_ring(w.ctx()).map_err(gr)?;
    let z = svd_jacobi(&w)?;
    let dimension = w.nrows().max(w.ncols());
    let rank = numerical_rank_of(a, bits, &w, &z.sigma)?;
    let p = pseudoinverse_of(&z, rank)?;
    let v = yw.mul(&p).map_err(gr)?;
    let residual = v.mul(&w).map_err(gr)?.sub(&yw).map_err(gr)?;
    let e = epsilon(a, bits, dimension, &z.sigma)?;
    let consistent = (0..residual.nrows()).all(|i| (0..residual.ncols()).all(|j| abs_real(&residual.entry(i, j)).cmp_magma(&e) != Ordering::Greater));
    Ok((x, y, v, kernel_of(&z, rank), consistent))
}

fn solution_value(it: &mut Interp, x: &Mtrx, y: &Mtrx, v: Mat) -> RResult<Value> {
    let v = round(&v, x.m.ctx())?;
    if y.is_vector() { vec_value(it, x.ring(), v) } else { mat_value(it, x.ring(), v) }
}

fn numerical_solution(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y, v, k, yes) = solve_numerically(it, a)?;
    if !yes { return Err(RuntimeError::runtime("No solution exists")); }
    let v = solution_value(it, &x, &y, v)?;
    if a.nresults < 2 { return one(v); }
    Ok(vals![v, mat_value(it, x.ring(), round(&k, x.m.ctx())?)?])
}

fn numerical_is_consistent(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y, v, k, yes) = solve_numerically(it, a)?;
    if !yes { return Ok(vals![Value::Bool(false), Value::Undef, Value::Undef]); }
    Ok(vals![Value::Bool(true), solution_value(it, &x, &y, v)?, mat_value(it, x.ring(), round(&k, x.m.ctx())?)?])
}

fn hessenberg(a: &Mat) -> RResult<(Mat, Mat)> {
    let n = a.nrows();
    let mut h = a.clone();
    let mut q = Mat::identity(a.ctx(), n).map_err(gr)?;
    for k in 0..n.saturating_sub(2) {
        let x = (k + 1..n).map(|i| h.entry(i, k)).collect();
        if let Some((v, beta)) = reflector(x)? {
            apply_left(&mut h, k + 1, &v, &beta)?;
            apply_right(&mut h, k + 1, &v, &beta)?;
            apply_left(&mut q, k + 1, &v, &beta)?;
        }
    }
    Ok((h, q))
}

fn numerical_hessenberg_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    let (w, _, _) = work(&x)?;
    let (h, q) = hessenberg(&w)?;
    Ok(vals![mat_value(it, x.ring(), round(&h, x.m.ctx())?)?, mat_value(it, x.ring(), round(&q, x.m.ctx())?)?])
}

fn shift_of(a: &Mat, active: usize, complex: bool, bits: u64) -> Elem {
    let d = a.entry(active - 1, active - 1);
    if complex || active < 2 { return d; }
    let ar = a.entry(active - 2, active - 2).to_real().unwrap();
    let br = a.entry(active - 2, active - 1).to_real().unwrap();
    let cr = a.entry(active - 1, active - 2).to_real().unwrap();
    let dr = d.to_real().unwrap();
    let disc = ar.sub(&dr).sqr().add(&br.mul(&cr).mul_i64(4));
    let mu = if disc.sign() < 0 {
        ar.add(&dr).div_i64(2)
    } else {
        let root = disc.sqrt();
        let x = ar.add(&dr).add(&root).div_i64(2);
        let y = ar.add(&dr).sub(&root).div_i64(2);
        if x.sub(&dr).abs().cmp_magma(&y.sub(&dr).abs()) == Ordering::Less { x } else { y }
    };
    real_elem(a.ctx(), &mu.round_to(bits)).unwrap()
}

fn schur(a: &Mat, complex: bool) -> RResult<(Mat, Mat)> {
    let (mut s, mut t) = hessenberg(a)?;
    let n = a.nrows();
    let bits = match a.ctx().kind() { CtxKind::RealFloat(p) | CtxKind::ComplexFloat(p) => *p, _ => unreachable!() };
    let tol = unit_roundoff(bits);
    let mut active = n;
    let mut iterations = 0usize;
    let limit = 100 * n.max(1) * n.max(1);
    while active > 1 && iterations < limit {
        let sub = abs_real(&s.entry(active - 1, active - 2));
        let scale = abs_real(&s.entry(active - 2, active - 2)).add(&abs_real(&s.entry(active - 1, active - 1))).add_i64(1);
        if sub.cmp_magma(&tol.mul(&scale)) != Ordering::Greater {
            s.set_entry(active - 1, active - 2, &Elem::new(a.ctx()));
            active -= 1;
            continue;
        }
        if !complex && (active == 2 || abs_real(&s.entry(active - 2, active - 3)).cmp_magma(&tol) != Ordering::Greater) {
            active = active.saturating_sub(2);
            continue;
        }
        let mu = shift_of(&s, active, complex, bits);
        let mut block = s.block(0, 0, active, active);
        for i in 0..active { block.set_entry(i, i, &block.entry(i, i).sub(&mu).map_err(gr)?); }
        let (q, _) = qr(&block)?;
        let mut g = Mat::identity(a.ctx(), n).map_err(gr)?;
        g.insert(&q, 0, 0);
        let gh = adjoint(&g)?;
        // Updating the full matrices also carries the coupling to already
        // deflated blocks and keeps the stated transformation identity.
        s = gh.mul(&s).map_err(gr)?.mul(&g).map_err(gr)?;
        t = gh.mul(&t).map_err(gr)?;
        iterations += 1;
    }
    Ok((s, t))
}

fn numerical_schur_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let _ = bool_param(a, "Transform")?;
    let x = square(a, 0)?;
    let (w, _, complex) = work(&x)?;
    let (s, q) = schur(&w, complex)?;
    Ok(vals![mat_value(it, x.ring(), round(&s, x.m.ctx())?)?, mat_value(it, x.ring(), round(&q, x.m.ctx())?)?])
}

fn eigenvalue_values(it: &mut Interp, a: &mut CallArgs) -> RResult<(Value, Vec<Value>, bool)> {
    let _ = bool_param(a, "Balance")?;
    let x = square(a, 0)?;
    let (bits, input_complex) = kind(&x)?;
    let ctx = Ctx::complex_float(bits + GUARD_BITS);
    let w = x.m.change_ring(&ctx).map_err(gr)?;
    let (mut es, _) = w.approx_eigen().map_err(gr)?;
    es.sort_by(|x, y| {
        let (xr, xi) = x.to_complex_parts().unwrap();
        let (yr, yi) = y.to_complex_parts().unwrap();
        xr.cmp_magma(&yr).then_with(|| xi.cmp_magma(&yi))
    });
    let small = unit_roundoff(bits + GUARD_BITS);
    let field = it.complex_field(bits);
    let values = es.into_iter().map(|e| {
        let (re, mut im) = e.to_complex_parts().unwrap();
        if !input_complex && im.abs().cmp_magma(&small.mul(&re.abs().add_i64(1))) != Ordering::Greater { im = Real::zero(im.prec()); }
        Value::complex(re.round_to(bits), im.round_to(bits))
    }).collect();
    Ok((field, values, input_complex))
}

fn eigenvalues(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (field, values, _) = eigenvalue_values(it, a)?;
    one(Value::seq(Some(field), values))
}

/// The backwards-compatible `Eigenvalues` form: approximate real roots only
/// for a real matrix, and pairs with multiplicities in an unordered set.
fn eigenvalues_compat(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, values, input_complex) = eigenvalue_values(it, a)?;
    let mut groups: Vec<(Value, usize)> = Vec::new();
    for e in values {
        if !input_complex && matches!(&e, Value::Complex(z) if !z.im.is_zero()) {
            continue;
        }
        if let Some((_, n)) = groups.iter_mut().find(|(x, _)| *x == e) {
            *n += 1;
        } else {
            groups.push((e, 1));
        }
    }
    let elems: VSet = groups.into_iter().map(|(e, n)| Value::tuple(vec![e, Value::int(n as i64)])).collect();
    one(Value::Set(Rc::new(SetEnum::new(None, elems))))
}

fn numerical_eigenvectors(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    let (bits, _) = kind(&x)?;
    let Value::Complex(e) = &a.args[1] else { return Err(bad()) };
    let ctx = Ctx::complex_float(bits + GUARD_BITS);
    let mut w = x.m.change_ring(&ctx).map_err(gr)?;
    let ee = Elem::from_complex_parts(&ctx, &e.re.round_to(bits + GUARD_BITS), &e.im.round_to(bits + GUARD_BITS)).map_err(gr)?;
    for i in 0..w.nrows() { w.set_entry(i, i, &w.entry(i, i).sub(&ee).map_err(gr)?); }
    let z = svd(&w)?;
    let base = z.sigma.first().map_or_else(|| unit_roundoff(bits + GUARD_BITS), |s| s.mul(&unit_roundoff(bits + GUARD_BITS)));
    let mut rank = z.sigma.iter().filter(|s| s.cmp_magma(&base) == Ordering::Greater).count();
    if rank == w.nrows() && rank > 0 { rank -= 1; }
    let k = round(&kernel_of(&z, rank), &Ctx::complex_float(bits)).map_err(|e| e)?;
    let ring = it.complex_field(bits);
    let universe = Value::Struct(parent(it, &ring, 1, w.nrows(), Shape::Tuples)?);
    let mut rows = Vec::new();
    for i in 0..k.nrows() { rows.push(vec_value(it, &ring, k.block(i, 0, 1, k.ncols()))?); }
    one(Value::seq(Some(universe), rows))
}

fn numerical_bidiagonal_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    // A diagonal matrix is also upper and lower bidiagonal. Reusing the SVD
    // gives a stable form in both rectangular orientations.
    numerical_svd(it, a)
}

fn numerical_svd(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?.clone();
    let (w, _, _) = work(&x)?;
    let z = svd(&w)?;
    Ok(vals![
        mat_value(it, x.ring(), round(&z.s, x.m.ctx())?)?,
        mat_value(it, x.ring(), round(&z.u, x.m.ctx())?)?,
        mat_value(it, x.ring(), round(&z.v, x.m.ctx())?)?,
    ])
}

fn eps_params() -> [(&'static str, Value); 1] {
    [("Epsilon", Value::Undef)]
}

fn register_for(it: &mut Interp, ty: &str) {
    let m = format!("Mtrx[{ty}]");
    let eps = eps_params();
    for name in ["NumericalInverse", "Inverse"] {
        it.def_params(name, &format!("A::{m} -> AlgMatElt"), &eps, "The numerical inverse of A.", numerical_inverse);
    }
    for name in ["NumericalRank", "Rank"] {
        it.def_params(name, &format!("A::{m} -> RngIntElt"), &eps, "The numerical rank of A.", numerical_rank);
    }
    for name in ["NumericalKernel", "Kernel"] {
        it.def_params(name, &format!("A::{m} -> Mtrx"), &eps, "An orthonormal row basis of the numerical kernel of A.", numerical_kernel);
    }
    for name in ["NumericalImage", "Image"] {
        it.def_params(name, &format!("A::{m} -> Mtrx"), &eps, "An orthonormal row basis of the numerical image of A.", numerical_image);
    }
    for name in ["NumericalSolution", "Solution"] {
        it.def_params(name, &format!("A::{m}, W::{m} -> Mtrx, Mtrx"), &eps, "A numerical solution V of V*A = W, and the kernel.", numerical_solution);
    }
    for name in ["NumericalIsConsistent", "IsConsistent"] {
        it.def_params(name, &format!("A::{m}, W::{m} -> BoolElt, Mtrx, Mtrx"), &eps, "Whether V*A = W is numerically consistent, with a solution and the kernel.", numerical_is_consistent);
    }
    for name in ["NumericalPseudoinverse", "Pseudoinverse"] {
        it.def_params(name, &format!("A::{m} -> Mtrx"), &eps, "The numerical Moore-Penrose pseudoinverse of A.", numerical_pseudoinverse);
    }
    for name in ["NumericalHessenbergForm", "HessenbergForm"] {
        it.def(name, &format!("A::{m} -> Mtrx, Mtrx"), "A Hessenberg form H = Q*A*Q^* and Q.", numerical_hessenberg_form);
    }
    for name in ["NumericalSchurForm", "SchurForm"] {
        it.def_params(name, &format!("A::{m} -> Mtrx, Mtrx"), &[("Transform", Value::Bool(true))], "A Schur form S = Q*A*Q^* and Q.", numerical_schur_form);
    }
    it.def_params("NumericalEigenvalues", &format!("A::{m} -> SeqEnum"), &[("Balance", Value::Bool(true))], "Numerical approximations to the eigenvalues of A.", eigenvalues);
    it.def_params("Eigenvalues", &format!("A::{m} -> SetEnum"), &[("Balance", Value::Bool(true))], "Numerical eigenvalues and their multiplicities.", eigenvalues_compat);
    for name in ["NumericalBidiagonalForm", "BidiagonalForm"] {
        it.def(name, &format!("A::{m} -> Mtrx, Mtrx, Mtrx"), "A bidiagonal form B = U*A*V^* and U, V.", numerical_bidiagonal_form);
    }
    for name in ["NumericalSingularValueDecomposition", "SingularValueDecomposition"] {
        it.def(name, &format!("A::{m} -> Mtrx, Mtrx, Mtrx"), "The singular value decomposition S = U*A*V^*.", numerical_svd);
    }
}

pub fn register(it: &mut Interp) {
    for ty in ["FldRe", "FldCom"] {
        register_for(it, ty);
    }
    it.def("RQDecomposition", "A::Mtrx[FldRe] -> Mtrx, AlgMatElt", "The RQ decomposition A = R*Q.", rq_decomposition);
    it.def("RQDecomposition", "A::Mtrx[FldCom] -> Mtrx, AlgMatElt", "The RQ decomposition A = R*Q.", rq_decomposition);
    it.def("QLDecomposition", "A::Mtrx[FldRe] -> AlgMatElt, Mtrx", "The QL decomposition A = Q*L.", ql_decomposition);
    it.def("QLDecomposition", "A::Mtrx[FldCom] -> AlgMatElt, Mtrx", "The QL decomposition A = Q*L.", ql_decomposition);
    it.def("NumericalEigenvectors", "A::Mtrx, e::FldComElt -> SeqEnum", "Numerical row eigenvectors of A for e.", numerical_eigenvectors);
    it.def("Eigenvectors", "A::Mtrx[FldRe], e::FldComElt -> SeqEnum", "Numerical row eigenvectors of A for e.", numerical_eigenvectors);
    it.def("Eigenvectors", "A::Mtrx[FldCom], e::FldComElt -> SeqEnum", "Numerical row eigenvectors of A for e.", numerical_eigenvectors);
}
