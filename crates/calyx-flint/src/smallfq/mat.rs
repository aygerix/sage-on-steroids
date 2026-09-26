//! Matrix methods on the kernels, for the gr contexts of fields with Zech
//! logarithms (see `install`): products of matrices, whose rows are sums of
//! row updates, and for large matrices over odd characteristic products
//! through GF(p); and elimination (LU decomposition, triangular solves,
//! the reduction of a row by others), whose rows are accumulated into
//! until they are final.

use std::ffi::c_int;

use flint3_sys as sys;

use super::{Acc, GrCtx, Opd, SUCCESS, SmallFq, ext, words, words_mut};

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

/// LU = P A, as FLINT's classical elimination makes it: the pivot of each
/// column is its first nonzero entry on or below the current row, the
/// multiplier of pivot k in row j is stored at (j, k), and U sits right of
/// the multipliers. The rows are read into sums first, so LU may be A.
/// With `rank_check`, the rank is 0 once a column has no pivot.
pub(super) unsafe extern "C" fn lu(rank: *mut sys::slong, perm: *mut sys::slong, lu: *mut Mat, a: *const Mat, rank_check: c_int, ctx: GrCtx) -> c_int {
    unsafe {
        let e = &*ext(ctx);
        let (m, n) = ((*a).r as usize, (*a).c as usize);
        if m.min(n) < e.cut.lu.max(1) {
            return (e.lu)(rank, perm, lu, a, rank_check, ctx);
        }
        let k = &e.k;
        let zero = k.zero();
        let p = std::slice::from_raw_parts_mut(perm, m);
        for (i, x) in p.iter_mut().enumerate() {
            *x = i as sys::slong;
        }
        let mut rows: Vec<Acc> = (0..m).map(|i| k.acc_from_logs(row(a, i))).collect();
        // The multipliers of each row, in the order of the pivots.
        let mut left: Vec<Vec<u64>> = vec![Vec::new(); m];
        let mut buf = vec![0; n];
        let (mut r, mut row, mut col) = (0, 0, 0);
        let mut deficient = false;
        while row < m && col < n {
            let Some(j) = (row..m).find(|&j| k.entry(&mut rows[j], col) != zero) else {
                if rank_check != 0 {
                    deficient = true;
                    break;
                }
                col += 1;
                continue;
            };
            r += 1;
            if j != row {
                rows.swap(j, row);
                left.swap(j, row);
                p.swap(j, row);
            }
            let d = k.entry(&mut rows[row], col);
            k.to_logs(&mut rows[row], &mut buf);
            put_row(k, lu, row, &left[row], col, &buf);
            let pivot = k.opd_from_logs(&buf[col + 1..]);
            for j in row + 1..m {
                let x = k.entry(&mut rows[j], col);
                let f = k.div(x, d).unwrap();
                k.addmul(&mut rows[j], col + 1, k.neg(f), &pivot, 0..n - col - 1);
                left[j].push(f);
            }
            row += 1;
            col += 1;
        }
        // The rows below, zero from their multipliers up to the column the
        // elimination stopped at.
        for j in row..m {
            k.to_logs(&mut rows[j], &mut buf);
            put_row(k, lu, j, &left[j], col, &buf);
        }
        *rank = if deficient { 0 } else { r as sys::slong };
        SUCCESS
    }
}

/// Row i of LU: the multipliers, zeros up to column `from`, and the sums'
/// entries from there.
unsafe fn put_row(k: &SmallFq, lu: *mut Mat, i: usize, left: &[u64], from: usize, sums: &[u64]) {
    let out = unsafe { row_mut(lu, i) };
    out[..left.len()].copy_from_slice(left);
    out[left.len()..from].fill(k.zero());
    out[from..].copy_from_slice(&sums[from..]);
}

/// X = L^-1 B for L lower triangular, with ones on the diagonal if `unit`.
pub(super) unsafe extern "C" fn solve_tril(x: *mut Mat, l: *const Mat, b: *const Mat, unit: c_int, ctx: GrCtx) -> c_int {
    unsafe { solve(x, l, b, unit, ctx, false) }
}

/// X = U^-1 B for U upper triangular, with ones on the diagonal if `unit`.
pub(super) unsafe extern "C" fn solve_triu(x: *mut Mat, u: *const Mat, b: *const Mat, unit: c_int, ctx: GrCtx) -> c_int {
    unsafe { solve(x, u, b, unit, ctx, true) }
}

/// Substitution row by row, forward or back: row i of X is row i of B less
/// the rows of X already found, scaled by row i of T, over T's diagonal
/// entry. Each row of B is read before row i of X is written, so X may be
/// B. A zero on the diagonal is FLINT's domain error.
unsafe fn solve(x: *mut Mat, t: *const Mat, b: *const Mat, unit: c_int, ctx: GrCtx, upper: bool) -> c_int {
    unsafe {
        let e = &*ext(ctx);
        let (n, m) = ((*t).r as usize, (*b).c as usize);
        if (*t).c as usize != n || (*b).r as usize != n || (*x).r as usize != n || (*x).c as usize != m {
            return DOMAIN;
        }
        if n.min(m) < e.cut.solve.max(1) {
            return if upper { (e.solve_triu)(x, t, b, unit, ctx) } else { (e.solve_tril)(x, t, b, unit, ctx) };
        }
        let k = &e.k;
        let mut inv = vec![0; n];
        if unit == 0 {
            for (i, v) in inv.iter_mut().enumerate() {
                let Some(y) = k.inv(row(t, i)[i]) else { return DOMAIN };
                *v = y;
            }
        }
        let mut xs: Vec<Option<Opd>> = (0..n).map(|_| None).collect();
        let mut buf = vec![0; m];
        for s in 0..n {
            let i = if upper { n - 1 - s } else { s };
            let mut acc = k.acc_from_logs(row(b, i));
            let found = if upper { i + 1..n } else { 0..i };
            let ti = row(t, i);
            for j in found {
                k.addmul(&mut acc, 0, k.neg(ti[j]), xs[j].as_ref().unwrap(), 0..m);
            }
            k.to_logs(&mut acc, &mut buf);
            if unit == 0 {
                for y in buf.iter_mut() {
                    *y = k.mul(*y, inv[i]);
                }
            }
            row_mut(x, i).copy_from_slice(&buf);
            xs[i] = Some(k.opd_from_logs(&buf));
        }
        SUCCESS
    }
}

/// The first row from `start` up to `end` with a nonzero entry in the
/// column, as FLINT's generic search finds it.
pub(super) unsafe extern "C" fn find_pivot(pivot: *mut sys::slong, mat: *mut Mat, start: sys::slong, end: sys::slong, column: sys::slong, ctx: GrCtx) -> c_int {
    unsafe {
        let zero = (*ext(ctx)).k.zero();
        for i in start..end {
            if row(mat, i as usize)[column as usize] != zero {
                *pivot = i;
                return SUCCESS;
            }
        }
        DOMAIN
    }
}

/// Reduce row m of A by the rows already reduced, as FLINT's generic method
/// does: for each column i left to right where row m is nonzero, subtract
/// the multiple of row P[i] (entries i + 1 up to L[P[i]]) that clears it;
/// at the first such column without a row, scale the entries up to L[m] to
/// make it one, record row m as its row and report the column (-1 when
/// there is none).
pub(super) unsafe extern "C" fn reduce_row(
    column: *mut sys::slong,
    a: *mut Mat,
    perm: *mut sys::slong,
    len: *mut sys::slong,
    m: sys::slong,
    ctx: GrCtx,
) -> c_int {
    unsafe {
        let e = &*ext(ctx);
        let n = (*a).c as usize;
        if n < e.cut.reduce_row.max(1) {
            return (e.reduce_row)(column, a, perm, len, m, ctx);
        }
        let k = &e.k;
        let zero = k.zero();
        let mu = m as usize;
        let p = std::slice::from_raw_parts_mut(perm, n);
        *column = -1;
        let mut acc = k.acc_from_logs(row(a, mu));
        // The columns cleared, and the one made one with its scale.
        let mut cleared = Vec::new();
        let mut unit = None;
        for (i, pi) in p.iter_mut().enumerate() {
            let x = k.entry(&mut acc, i);
            if x == zero {
                continue;
            }
            if *pi != -1 {
                let r = *pi as usize;
                let end = *len.add(r) as usize;
                if end > i + 1 {
                    let b = k.opd_from_logs(&row(a, r)[i + 1..end]);
                    k.addmul(&mut acc, i + 1, k.neg(x), &b, 0..end - i - 1);
                }
                cleared.push(i);
            } else {
                unit = Some((i, k.inv(x).unwrap()));
                *pi = m;
                *column = i as sys::slong;
                break;
            }
        }
        let out = row_mut(a, mu);
        k.to_logs(&mut acc, out);
        for i in cleared {
            out[i] = zero;
        }
        if let Some((i, h)) = unit {
            out[i] = 0;
            let end = *len.add(mu) as usize;
            for y in out.iter_mut().take(end).skip(i + 1) {
                *y = k.mul(*y, h);
            }
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
    use super::super::tests::{Lcg, fields, row as rand_row, set_cutoffs, word};
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

    /// The kernels everywhere, matrices and polynomials alike.
    const EVERYWHERE_ALL: Cutoffs = super::super::tests::EVERYWHERE;

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

    const FIELDS: [(u64, u64); 9] = [(2, 1), (2, 8), (3, 4), (5, 3), (7, 2), (7, 5), (31, 3), (1021, 2), (3, 12)];

    /// An r × c matrix: at random, or of low rank (rows that are multiples
    /// of earlier ones), or with a zero column and a zero row, or sparse.
    fn matrix(k: &SmallFq, r: usize, c: usize, rng: &mut Lcg) -> Vec<u64> {
        let mut w = rand_row(k, r * c, rng);
        match rng.below(4) {
            0 => {}
            1 => {
                for i in 1..r {
                    if rng.below(2) == 0 {
                        let (s, f) = (rng.below(i), word(k, rng));
                        for j in 0..c {
                            w[i * c + j] = k.mul(w[s * c + j], f);
                        }
                    }
                }
            }
            2 => {
                let j0 = rng.below(c);
                for i in 0..r {
                    w[i * c + j0] = k.zero();
                }
                let i0 = rng.below(r);
                w[i0 * c..(i0 + 1) * c].fill(k.zero());
            }
            _ => w.iter_mut().filter(|_| rng.below(3) != 0).for_each(|x| *x = k.zero()),
        }
        w
    }

    /// The rank, permutation and words of an LU decomposition, into LU or
    /// in place of A.
    fn lu_of(ctx: &Ctx, r: usize, c: usize, w: &[u64], rank_check: c_int, in_place: bool, flint_classical: bool) -> (c_int, i64, Vec<i64>, Vec<u64>) {
        let mut a = mat_of(ctx, r, c, w);
        let mut out = mat_of(ctx, r, c, &vec![0; r * c]);
        let (mut rank, mut perm) = (0, vec![0; r]);
        let lu_fn = if flint_classical { sys::gr_mat_lu_classical } else { sys::gr_mat_lu };
        let st = unsafe {
            if in_place {
                let ap: *mut Mat = &mut a;
                lu_fn(&mut rank, perm.as_mut_ptr(), ap, ap, rank_check, ctx.ptr())
            } else {
                lu_fn(&mut rank, perm.as_mut_ptr(), &mut out, &a, rank_check, ctx.ptr())
            }
        };
        let got = words_of(if in_place { &a } else { &out });
        [a, out].into_iter().for_each(|m| clear(ctx, m));
        (st, rank, perm, got)
    }

    /// LU decompositions word for word as FLINT's classical elimination
    /// makes them, with and without the rank check, and in place.
    #[test]
    fn lu_agrees_with_flint() {
        let mut rng = Lcg(0x10_5eed);
        for (p, n) in FIELDS {
            let (ours, flint) = fields(p, n);
            let k = SmallFq::of(&ours).unwrap();
            let measured = k.cutoffs();
            for (r, c) in [(1, 1), (1, 5), (5, 1), (2, 2), (3, 7), (7, 3), (6, 6), (16, 16), (20, 33), (33, 20), (40, 40)] {
                for _ in 0..4 {
                    let w = matrix(k, r, c, &mut rng);
                    for rank_check in [0, 1] {
                        let want = lu_of(&flint, r, c, &w, rank_check, false, true);
                        for (cut, cuts) in [(measured, "measured"), (EVERYWHERE_ALL, "everywhere")] {
                            set_cutoffs(&ours, cut);
                            for in_place in [false, true] {
                                let what = format!("GF({p}^{n}), {r} × {c}, rank check {rank_check}, cutoffs {cuts}, in place {in_place}");
                                let got = lu_of(&ours, r, c, &w, rank_check, in_place, false);
                                // A failed rank check leaves a partial decomposition, which
                                // FLINT's recursive algorithm (below the cutoffs) leaves
                                // otherwise, and which callers do not read.
                                if rank_check == 1 && want.1 == 0 {
                                    assert_eq!((got.0, got.1), (want.0, want.1), "{what}");
                                } else {
                                    assert_eq!(got, want, "{what}");
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Everything calyx computes by elimination, against FLINT's own field:
    /// determinants, ranks, echelon forms, inverses, solutions and minimal
    /// polynomials.
    #[test]
    fn elimination_agrees_with_flint() {
        let mut rng = Lcg(0x11_5eed);
        for (p, n) in FIELDS {
            let (ours, flint) = fields(p, n);
            let k = SmallFq::of(&ours).unwrap();
            let measured = k.cutoffs();
            for (r, c) in [(1, 1), (2, 2), (4, 4), (5, 5), (3, 8), (8, 3), (12, 12), (24, 24), (9, 30)] {
                for _ in 0..4 {
                    let w = matrix(k, r, c, &mut rng);
                    let rhs = rand_row(k, r * 3, &mut rng);
                    let want = everything(&flint, r, c, &w, &rhs);
                    for (cut, cuts) in [(measured, "measured"), (EVERYWHERE_ALL, "everywhere")] {
                        set_cutoffs(&ours, cut);
                        assert_eq!(everything(&ours, r, c, &w, &rhs), want, "GF({p}^{n}), {r} × {c}, cutoffs {cuts}");
                    }
                }
            }
        }
    }

    /// Statuses and words: rank, echelon form, and for square matrices the
    /// determinant, inverse, solution for three right-hand columns and
    /// minimal polynomial.
    fn everything(ctx: &Ctx, r: usize, c: usize, w: &[u64], rhs: &[u64]) -> Vec<(c_int, Vec<u64>)> {
        let a = mat_of(ctx, r, c, w);
        let mut out = Vec::new();
        unsafe {
            let mut rank = 0;
            out.push((sys::gr_mat_rank(&mut rank, &a, ctx.ptr()), vec![rank as u64]));
            let mut e = mat_of(ctx, r, c, &vec![0; r * c]);
            out.push((sys::gr_mat_rref(&mut rank, &mut e, &a, ctx.ptr()), words_of(&e)));
            out.push((0, vec![rank as u64]));
            clear(ctx, e);
            if r == c {
                let mut d = 0u64;
                out.push((sys::gr_mat_det((&mut d as *mut u64).cast(), &a, ctx.ptr()), vec![d]));
                let mut inv = mat_of(ctx, r, r, &vec![0; r * r]);
                let st = sys::gr_mat_inv(&mut inv, &a, ctx.ptr());
                out.push((st, if st == SUCCESS { words_of(&inv) } else { Vec::new() }));
                clear(ctx, inv);
                let b = mat_of(ctx, r, 3, rhs);
                let mut x = mat_of(ctx, r, 3, &vec![0; r * 3]);
                let st = sys::gr_mat_nonsingular_solve(&mut x, &a, &b, ctx.ptr());
                out.push((st, if st == SUCCESS { words_of(&x) } else { Vec::new() }));
                [b, x].into_iter().for_each(|m| clear(ctx, m));
                let mut f = sys::gr_poly_struct::default();
                sys::gr_poly_init(&mut f, ctx.ptr());
                let st = sys::gr_mat_minpoly_field(&mut f, &a, ctx.ptr());
                out.push((st, words(f.coeffs, f.length as usize).to_vec()));
                sys::gr_poly_clear(&mut f, ctx.ptr());
            }
        }
        clear(ctx, a);
        out
    }

    /// Triangular solves against FLINT's classical ones: lower and upper,
    /// with and without ones on the diagonal, in place, and with a zero on
    /// the diagonal.
    #[test]
    fn solves_agree_with_flint() {
        let mut rng = Lcg(0x12_5eed);
        for (p, n) in FIELDS {
            let (ours, flint) = fields(p, n);
            let k = SmallFq::of(&ours).unwrap();
            let measured = k.cutoffs();
            for (d, m) in [(1, 1), (1, 4), (4, 1), (3, 3), (10, 7), (7, 10), (33, 33), (64, 70)] {
                for upper in [false, true] {
                    for unit in [0, 1] {
                        let mut t = rand_row(k, d * d, &mut rng);
                        for i in 0..d {
                            for j in 0..d {
                                if (j > i && !upper) || (j < i && upper) {
                                    t[i * d + j] = k.zero();
                                }
                            }
                            // Nonzero diagonal entries, one of them zero now and then.
                            t[i * d + i] = rng.next() % k.qm1;
                        }
                        if rng.below(4) == 0 {
                            let i = rng.below(d);
                            t[i * d + i] = k.zero();
                        }
                        let b = rand_row(k, d * m, &mut rng);
                        let want = solved(&flint, d, m, &t, &b, unit, upper, false, true);
                        for (cut, cuts) in [(measured, "measured"), (EVERYWHERE_ALL, "everywhere")] {
                            set_cutoffs(&ours, cut);
                            for in_place in [false, true] {
                                let what = format!("GF({p}^{n}), order {d}, {m} columns, upper {upper}, unit {unit}, cutoffs {cuts}, in place {in_place}");
                                let got = solved(&ours, d, m, &t, &b, unit, upper, in_place, false);
                                // FLINT leaves a partial solution behind a zero on the diagonal.
                                if want.0 == SUCCESS {
                                    assert_eq!(got, want, "{what}");
                                } else {
                                    assert_eq!(got.0, want.0, "{what}");
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn solved(ctx: &Ctx, d: usize, m: usize, t: &[u64], b: &[u64], unit: c_int, upper: bool, in_place: bool, flint_classical: bool) -> (c_int, Vec<u64>) {
        let tm = mat_of(ctx, d, d, t);
        let mut bm = mat_of(ctx, d, m, b);
        let mut x = mat_of(ctx, d, m, &vec![0; d * m]);
        let f = match (upper, flint_classical) {
            (false, false) => sys::gr_mat_nonsingular_solve_tril,
            (true, false) => sys::gr_mat_nonsingular_solve_triu,
            (false, true) => sys::gr_mat_nonsingular_solve_tril_classical,
            (true, true) => sys::gr_mat_nonsingular_solve_triu_classical,
        };
        let st = unsafe {
            if in_place {
                let bp: *mut Mat = &mut bm;
                f(bp, &tm, bp, unit, ctx.ptr())
            } else {
                f(&mut x, &tm, &bm, unit, ctx.ptr())
            }
        };
        let got = words_of(if in_place { &bm } else { &x });
        [tm, bm, x].into_iter().for_each(|m| clear(ctx, m));
        (st, got)
    }

    /// Reductions of rows, one after another as in FLINT's minimal
    /// polynomials, against FLINT's generic method: rows of random lengths,
    /// with entries past their lengths.
    #[test]
    fn reductions_agree_with_flint() {
        let mut rng = Lcg(0x13_5eed);
        for (p, n) in FIELDS {
            let (ours, flint) = fields(p, n);
            let k = SmallFq::of(&ours).unwrap();
            for (rows, c) in [(1, 1), (3, 5), (8, 8), (20, 41), (40, 12)] {
                let w = matrix(k, rows, c, &mut rng);
                let len: Vec<i64> = (0..rows).map(|_| 1 + rng.below(c) as i64).collect();
                for cut in [k.cutoffs(), EVERYWHERE_ALL] {
                    set_cutoffs(&ours, cut);
                    let (mut a, mut fa) = (mat_of(&ours, rows, c, &w), mat_of(&flint, rows, c, &w));
                    let (mut pa, mut pf) = (vec![-1i64; c], vec![-1i64; c]);
                    let (mut la, mut lf) = (len.clone(), len.clone());
                    for m in 0..rows {
                        let (mut ca, mut cf) = (0, 0);
                        let sa = unsafe { sys::gr_mat_reduce_row(&mut ca, &mut a, pa.as_mut_ptr(), la.as_mut_ptr(), m as i64, ours.ptr()) };
                        let sf = unsafe { sys::gr_mat_reduce_row_generic(&mut cf, &mut fa, pf.as_mut_ptr(), lf.as_mut_ptr(), m as i64, flint.ptr()) };
                        let what = format!("GF({p}^{n}), {rows} × {c}, row {m}");
                        assert_eq!((sa, ca, &pa, words_of(&a)), (sf, cf, &pf, words_of(&fa)), "{what}");
                    }
                    clear(&ours, a);
                    clear(&flint, fa);
                }
            }
        }
    }

    /// Pivot searches against FLINT's generic one, empty ranges included.
    #[test]
    fn pivots_agree_with_flint() {
        let mut rng = Lcg(0x14_5eed);
        for (p, n) in FIELDS {
            let (ours, flint) = fields(p, n);
            let k = SmallFq::of(&ours).unwrap();
            let (r, c) = (12, 5);
            let mut w = rand_row(k, r * c, &mut rng);
            w.iter_mut().filter(|_| rng.below(4) != 0).for_each(|x| *x = k.zero());
            let (mut a, mut fa) = (mat_of(&ours, r, c, &w), mat_of(&flint, r, c, &w));
            for col in 0..c {
                for start in 0..=r {
                    for end in [start.saturating_sub(1), start, start + 1, r] {
                        let end = end.min(r);
                        let (mut i, mut j) = (-7, -7);
                        let s = unsafe { sys::gr_mat_find_nonzero_pivot(&mut i, &mut a, start as i64, end as i64, col as i64, ours.ptr()) };
                        let t = unsafe { sys::gr_mat_find_nonzero_pivot_generic(&mut j, &mut fa, start as i64, end as i64, col as i64, flint.ptr()) };
                        assert_eq!((s, i), (t, j), "GF({p}^{n}), column {col}, rows {start}..{end}");
                    }
                }
            }
            clear(&ours, a);
            clear(&flint, fa);
        }
    }
}
