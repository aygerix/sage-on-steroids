//! Matrix methods on the kernels, for the gr contexts of fields with Zech
//! logarithms (see `install`): products of matrices, whose rows are sums of
//! row updates, and for large matrices over odd characteristic products
//! through GF(p).

use std::ffi::c_int;

use flint3_sys as sys;

use super::{GrCtx, Opd, SUCCESS, SmallFq, ext, words, words_mut};

type Mat = sys::gr_mat_struct;

/// FLINT's status for arguments an operation is not defined for.
const DOMAIN: c_int = 1;

/// Row i of a matrix, as words.
unsafe fn row<'a>(m: *const Mat, i: usize) -> &'a [u64] {
    unsafe { words((*m).entries.cast::<u64>().add(i * (*m).stride as usize).cast(), (*m).c as usize) }
}

unsafe fn row_mut<'a>(m: *mut Mat, i: usize) -> &'a mut [u64] {
    unsafe { words_mut((*m).entries.cast::<u64>().add(i * (*m).stride as usize).cast(), (*m).c as usize) }
}

/// C = A B. Each row of C sums the rows of B scaled by the entries of the
/// row of A. B becomes operands first, as both factors do in products
/// through GF(p), so C may be A or B.
pub(super) unsafe extern "C" fn mat_mul(c: *mut Mat, a: *const Mat, b: *const Mat, ctx: GrCtx) -> c_int {
    unsafe {
        let e = &*ext(ctx);
        let (r, m, n) = ((*a).r as usize, (*a).c as usize, (*b).c as usize);
        if (*b).r as usize != m || (*c).r as usize != r || (*c).c as usize != n {
            return DOMAIN;
        }
        let k = &e.k;
        let (from, to) = e.cut.mat_mul;
        let size = r.min(m).min(n);
        // FLINT's product would go by Kronecker substitution, which the
        // kernels beat.
        let ks = 5 * r.min(n) > 8 * k.n + 29;
        if size < from.max(1) && !ks {
            return (e.mat_mul)(c, a, b, ctx);
        }
        if size > to {
            return mat_mul_p(k, c, a, b);
        }
        let bs: Vec<Opd> = (0..m).map(|t| k.opd_from_logs(row(b, t))).collect();
        for i in 0..r {
            let mut acc = k.acc(n);
            for (t, &x) in row(a, i).iter().enumerate() {
                k.addmul(&mut acc, 0, x, &bs[t], 0..n);
            }
            k.to_logs(&mut acc, row_mut(c, i));
        }
        SUCCESS
    }
}

/// A matrix over GF(p), freed when dropped.
struct PMat(sys::nmod_mat_struct);

impl PMat {
    /// A zero matrix.
    fn new(r: usize, c: usize, p: u64) -> PMat {
        let mut m = sys::nmod_mat_struct::default();
        unsafe { sys::nmod_mat_init(&mut m, r as sys::slong, c as sys::slong, p as sys::ulong) };
        PMat(m)
    }

    fn at(&self, i: usize, j: usize) -> *mut u64 {
        unsafe { self.0.entries.cast::<u64>().add(i * self.0.stride as usize + j) }
    }
}

impl Drop for PMat {
    fn drop(&mut self) {
        unsafe { sys::nmod_mat_clear(&mut self.0) };
    }
}

/// C = A B through GF(p): with A = Σ A_u x^u and B = Σ B_v x^v for
/// matrices A_u and B_v over GF(p), which FLINT multiplies fast, C is the
/// product of the two polynomials reduced by x^t = g^t.
unsafe fn mat_mul_p(k: &SmallFq, c: *mut Mat, a: *const Mat, b: *const Mat) -> c_int {
    unsafe {
        let (r, n) = ((*a).r as usize, (*b).c as usize);
        let (pa, pb) = (planes(k, a), planes(k, b));
        let mut pc = karatsuba(&pa.iter().collect::<Vec<_>>(), &pb.iter().collect::<Vec<_>>(), (r, n, k.p));
        let (low, high) = pc.split_at_mut(k.n);
        for (t, h) in (k.n..).zip(high.iter()) {
            let mut v = k.eval[t] as u64;
            for l in low.iter_mut() {
                let (q, d) = k.div.divrem(v);
                if d != 0 {
                    let l: *mut _ = &mut l.0;
                    sys::nmod_mat_scalar_addmul_ui(l, l, &h.0, d as sys::ulong);
                }
                v = q;
            }
        }
        let logs = k.logs();
        for i in 0..r {
            for (j, x) in row_mut(c, i).iter_mut().enumerate() {
                *x = logs.get(low.iter().rev().fold(0, |v, l| v * k.p + *l.at(i, j)) as usize);
            }
        }
        SUCCESS
    }
}

/// The coordinates of the entries of m: plane u holds those of x^u.
unsafe fn planes(k: &SmallFq, m: *const Mat) -> Vec<PMat> {
    unsafe {
        let (r, c) = ((*m).r as usize, (*m).c as usize);
        let ps: Vec<PMat> = (0..k.n).map(|_| PMat::new(r, c, k.p)).collect();
        for i in 0..r {
            for (j, &x) in row(m, i).iter().enumerate() {
                let mut v = k.eval[x as usize] as u64;
                for pl in &ps {
                    let (q, d) = k.div.divrem(v);
                    *pl.at(i, j) = d;
                    v = q;
                }
            }
        }
        ps
    }
}

/// The coefficients of Σ a_u x^u · Σ b_v x^v, for a and b of the same
/// length, by Karatsuba's method: three products of halves make one of
/// wholes. The products are r × c.
fn karatsuba(a: &[&PMat], b: &[&PMat], (r, c, p): (usize, usize, u64)) -> Vec<PMat> {
    let n = a.len();
    if n == 1 {
        let mut t = PMat::new(r, c, p);
        unsafe { sys::nmod_mat_mul(&mut t.0, &a[0].0, &b[0].0) };
        return vec![t];
    }
    let h = n.div_ceil(2);
    let (a0, a1) = a.split_at(h);
    let (b0, b1) = b.split_at(h);
    let sum = |x0: &[&PMat], x1: &[&PMat]| -> Vec<PMat> {
        x1.iter()
            .zip(x0)
            .map(|(y, x)| {
                let mut s = PMat::new(x.0.r as usize, x.0.c as usize, p);
                unsafe { sys::nmod_mat_add(&mut s.0, &x.0, &y.0) };
                s
            })
            .collect()
    };
    let (sa, sb) = (sum(a0, a1), sum(b0, b1));
    // The halves' sums, the lower half alone where the upper is shorter.
    let sa: Vec<&PMat> = sa.iter().chain(a0[n - h..].iter().copied()).collect();
    let sb: Vec<&PMat> = sb.iter().chain(b0[n - h..].iter().copied()).collect();
    let mut mid = karatsuba(&sa, &sb, (r, c, p));
    let lo = karatsuba(a0, b0, (r, c, p));
    let hi = karatsuba(a1, b1, (r, c, p));
    for (i, m) in mid.iter_mut().enumerate() {
        unsafe {
            let m: *mut _ = &mut m.0;
            sys::nmod_mat_sub(m, m, &lo[i].0);
            if let Some(x) = hi.get(i) {
                sys::nmod_mat_sub(m, m, &x.0);
            }
        }
    }
    // lo, a zero, hi; then mid added at x^h.
    let mut out = lo;
    out.push(PMat::new(r, c, p));
    out.extend(hi);
    for (o, m) in out[h..].iter_mut().zip(&mid) {
        let o: *mut _ = &mut o.0;
        unsafe { sys::nmod_mat_add(o, o, &m.0) };
    }
    out
}

#[cfg(test)]
mod tests {
    use super::super::tests::{Lcg, fields, row as rand_row, set_cutoffs};
    use super::super::{Cutoffs, SmallFq};
    use super::*;
    use crate::gr::Ctx;

    unsafe extern "C" {
        fn fq_zech_mat_mul(c: *mut Mat, a: *const Mat, b: *const Mat, ctx: *const sys::fq_zech_ctx_struct);
    }

    /// An r × c matrix of the field of `ctx` with the given words, row by row.
    fn mat_of(ctx: &Ctx, r: usize, c: usize, w: &[u64]) -> Mat {
        let mut m = Mat::default();
        unsafe {
            sys::gr_mat_init(&mut m, r as sys::slong, c as sys::slong, ctx.ptr());
            for i in 0..r {
                row_mut(&mut m, i).copy_from_slice(&w[i * c..(i + 1) * c]);
            }
        }
        m
    }

    fn words_of(m: &Mat) -> Vec<u64> {
        (0..m.r as usize).flat_map(|i| unsafe { row(m, i) }.to_vec()).collect()
    }

    fn clear(ctx: &Ctx, mut m: Mat) {
        unsafe { sys::gr_mat_clear(&mut m, ctx.ptr()) };
    }

    fn zech(ctx: &Ctx) -> *const sys::fq_zech_ctx_struct {
        unsafe { std::ptr::read_unaligned((*ctx.ptr()).data.as_ptr() as *const *const sys::fq_zech_ctx_struct) }
    }

    /// The kernels at every size, and products through GF(p) at every size.
    const EVERYWHERE: (usize, usize) = (1, usize::MAX);
    const THROUGH_P: (usize, usize) = (1, 0);

    fn with_mat_mul(cut: Cutoffs, mat_mul: (usize, usize)) -> Cutoffs {
        Cutoffs { mat_mul, ..cut }
    }

    #[test]
    fn products_agree_with_flint() {
        let mut rng = Lcg(0x3a7_5eed);
        for (p, n) in [(2u64, 1u64), (2, 8), (2, 16), (3, 4), (5, 3), (7, 2), (7, 5), (13, 5), (31, 3), (1021, 2), (3, 12)] {
            let (ours, flint) = fields(p, n);
            let k = SmallFq::of(&ours).unwrap();
            let measured = k.cutoffs();
            for (r, m, c) in [(1, 1, 1), (2, 3, 4), (5, 1, 7), (7, 9, 1), (16, 16, 16), (33, 17, 65), (64, 100, 31), (130, 70, 90)] {
                let (x, y) = (rand_row(k, r * m, &mut rng), rand_row(k, m * c, &mut rng));
                let want = {
                    let (a, b, mut out) = (mat_of(&flint, r, m, &x), mat_of(&flint, m, c, &y), mat_of(&flint, r, c, &vec![0; r * c]));
                    unsafe { fq_zech_mat_mul(&mut out, &a, &b, zech(&flint)) };
                    let w = words_of(&out);
                    [a, b, out].into_iter().for_each(|m| clear(&flint, m));
                    w
                };
                let modes = [EVERYWHERE, THROUGH_P].map(|m| with_mat_mul(measured, m));
                for (cut, cuts) in [(measured, "measured"), (modes[0], "everywhere"), (modes[1], "through GF(p)")] {
                    set_cutoffs(&ours, cut);
                    let what = format!("GF({p}^{n}), {r} × {m} by {m} × {c}, cutoffs {cuts}");
                    let (a, b) = (mat_of(&ours, r, m, &x), mat_of(&ours, m, c, &y));
                    let mut out = mat_of(&ours, r, c, &vec![0; r * c]);
                    assert_eq!(unsafe { sys::gr_mat_mul(&mut out, &a, &b, ours.ptr()) }, SUCCESS, "{what}");
                    assert_eq!(words_of(&out), want, "{what}");
                    // In place of either factor, when the shapes allow.
                    if m == c {
                        let mut a2 = mat_of(&ours, r, m, &x);
                        let a2p: *mut Mat = &mut a2;
                        assert_eq!(unsafe { sys::gr_mat_mul(a2p, a2p, &b, ours.ptr()) }, SUCCESS, "{what}");
                        assert_eq!(words_of(&a2), want, "{what}, in place of A");
                        clear(&ours, a2);
                    }
                    if r == m {
                        let mut b2 = mat_of(&ours, m, c, &y);
                        let b2p: *mut Mat = &mut b2;
                        assert_eq!(unsafe { sys::gr_mat_mul(b2p, &a, b2p, ours.ptr()) }, SUCCESS, "{what}");
                        assert_eq!(words_of(&b2), want, "{what}, in place of B");
                        clear(&ours, b2);
                    }
                    [a, b, out].into_iter().for_each(|m| clear(&ours, m));
                }
            }
            // A square, in place.
            let x = rand_row(k, 20 * 20, &mut rng);
            let mut want = mat_of(&flint, 20, 20, &vec![0; 400]);
            let fa = mat_of(&flint, 20, 20, &x);
            unsafe { fq_zech_mat_mul(&mut want, &fa, &fa, zech(&flint)) };
            for mode in [EVERYWHERE, THROUGH_P] {
                set_cutoffs(&ours, with_mat_mul(measured, mode));
                let mut a = mat_of(&ours, 20, 20, &x);
                let ap: *mut Mat = &mut a;
                assert_eq!(unsafe { sys::gr_mat_mul(ap, ap, ap, ours.ptr()) }, SUCCESS);
                assert_eq!(words_of(&a), words_of(&want), "GF({p}^{n}), a square in place");
                clear(&ours, a);
            }
            [fa, want].into_iter().for_each(|m| clear(&flint, m));
        }
    }

    /// Windows, whose rows are further apart than their lengths, and shapes
    /// that do not match.
    #[test]
    fn products_of_windows() {
        let mut rng = Lcg(0x3a7_0001);
        let (ours, flint) = fields(3, 5);
        let k = SmallFq::of(&ours).unwrap();
        let (x, y) = (rand_row(k, 30 * 40, &mut rng), rand_row(k, 40 * 50, &mut rng));
        for mode in [EVERYWHERE, THROUGH_P] {
            set_cutoffs(&ours, with_mat_mul(k.cutoffs(), mode));
            windows(&ours, &flint, &x, &y);
        }
    }

    fn windows(ours: &Ctx, flint: &Ctx, x: &[u64], y: &[u64]) {
        let (big_a, big_b) = (mat_of(ours, 30, 40, x), mat_of(ours, 40, 50, y));
        let (fa, fb) = (mat_of(flint, 30, 40, x), mat_of(flint, 40, 50, y));
        let mut big_c = mat_of(ours, 30, 50, &[0; 1500]);
        let mut fc = mat_of(flint, 30, 50, &[0; 1500]);
        unsafe {
            let (mut a, mut b, mut c) = (Mat::default(), Mat::default(), Mat::default());
            let (mut ga, mut gb, mut gc) = (Mat::default(), Mat::default(), Mat::default());
            sys::gr_mat_window_init(&mut a, &big_a, 3, 5, 20, 35, ours.ptr());
            sys::gr_mat_window_init(&mut b, &big_b, 7, 2, 37, 40, ours.ptr());
            // The products write through these windows.
            sys::gr_mat_window_init(&mut c, &mut big_c as *mut Mat, 1, 4, 18, 42, ours.ptr());
            sys::gr_mat_window_init(&mut ga, &fa, 3, 5, 20, 35, flint.ptr());
            sys::gr_mat_window_init(&mut gb, &fb, 7, 2, 37, 40, flint.ptr());
            sys::gr_mat_window_init(&mut gc, &mut fc as *mut Mat, 1, 4, 18, 42, flint.ptr());
            assert_eq!(sys::gr_mat_mul(&mut c, &a, &b, ours.ptr()), SUCCESS);
            fq_zech_mat_mul(&mut gc, &ga, &gb, zech(flint));
            // The product and everything around it.
            assert_eq!(words_of(&big_c), words_of(&fc));
            // Shapes that do not match.
            assert_eq!(sys::gr_mat_mul(&mut c, &b, &a, ours.ptr()), DOMAIN);
            for w in [&mut a, &mut b, &mut c] {
                sys::gr_mat_window_clear(w, ours.ptr());
            }
            for w in [&mut ga, &mut gb, &mut gc] {
                sys::gr_mat_window_clear(w, flint.ptr());
            }
        }
        [big_a, big_b, big_c].into_iter().for_each(|m| clear(ours, m));
        [fa, fb, fc].into_iter().for_each(|m| clear(flint, m));
    }
}
