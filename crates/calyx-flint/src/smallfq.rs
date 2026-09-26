//! Kernels for finite fields with Zech logarithms (q up to 2^20): row
//! updates r += c·b over whole rows of field elements, for the classical
//! polynomial algorithms here and for matrices.
//!
//! FLINT keeps an element of such a field as its logarithm to the base of
//! the generator g (the root of the modulus, which is primitive in these
//! fields), q - 1 standing for zero. A product is then a sum of logarithms,
//! but a sum is a lookup in the table of Zech logarithms, and a row update
//! is a chain of dependent lookups. Rows here are kept in one of three
//! forms, fixed per field by measurement:
//!
//! - odd p and degree n up to 4: the coordinates in the power basis of g,
//!   in n planes of 32-bit lanes. c·b is b times the n×n matrix of
//!   multiplication by c, and sums are reduced modulo p only before they
//!   could overflow;
//! - odd p and larger n: the coordinates of each entry packed into the
//!   lanes of a word. c·b is a lookup of g^(log c + log b) in a table of
//!   such words, and a sum is an addition of words, reduced before a lane
//!   could overflow;
//! - p = 2: the coordinates as bits. Carry-less products are added up and
//!   reduced modulo the modulus once.
//!
//! Callers see logarithms (FLINT's words), `Acc`s (rows being accumulated
//! into) and `Opd`s (reduced rows, the operands of updates). The tables are
//! built on the first call, not with the field.
//!
//! Every field with Zech logarithms that calyx makes carries its kernels in
//! its gr context, which has its own copy of FLINT's method table (see
//! `install`). Polynomial products, division and gcds run on the kernels
//! over a middle range of lengths (`Cutoffs`), on FLINT's classical
//! algorithms below it and on its fast ones above. In the lanes form gcds
//! keep FLINT's algorithms, over the kernels' products and division.
//! Products of matrices run on the kernels from small sizes on, and for
//! large matrices over odd characteristic through FLINT's products over
//! GF(p) (`mat`).

use std::ffi::{c_int, c_void};
use std::ops::Range;
use std::sync::OnceLock;

use flint3_sys as sys;

use crate::fq::Zech;
use crate::gr::{Ctx, CtxKind};

type GrCtx = *mut sys::gr_ctx_struct;

unsafe extern "C" {
    /// FLINT's classical product over fq_zech, truncated to n terms (at most
    /// la + lb - 1), best with the shorter factor first.
    fn _fq_zech_poly_mullow_classical(r: *mut c_void, a: *const c_void, la: sys::slong, b: *const c_void, lb: sys::slong, n: sys::slong, ctx: *const c_void);
}

const SUCCESS: c_int = 0;
const TAB_SIZE: usize = sys::gr_method_GR_METHOD_TAB_SIZE as usize;

/// Where the polynomial methods take the kernels, by form, as measured in
/// the lab against FLINT's fq_zech algorithms. Products and division
/// convert their operands, which costs about as much as a few row updates,
/// so they take the kernels from a short operand and an area (the product
/// of the lengths) on; below, FLINT's classical algorithms win. Above the
/// upper bounds FLINT's fast algorithms win, which rest on products by
/// Kronecker substitution.
#[derive(Clone, Copy)]
struct Cutoffs {
    /// Products: from a shorter factor of length `mullow.0` and an area of
    /// `mullow.1`, up to a shorter factor of length `mullow.2`.
    mullow: (usize, usize, usize),
    /// Division: from a quotient of length `divrem.0`, a divisor of length
    /// `divrem.1` and an area of `divrem.2`, up to the last length
    /// `divrem.3` of the shorter of the two.
    divrem: (usize, usize, usize, usize),
    /// Gcds, and gcds with cofactors, by the length of the shorter
    /// polynomial: FLINT's Euclid below the first, the kernels' up to the
    /// second, FLINT's half-gcd above.
    gcd: (usize, usize),
    xgcd: (usize, usize),
    /// Products of matrices, by the least of their dimensions: FLINT's
    /// classical product below the first, the kernels up to the second, and
    /// products through GF(p) above. The kernels also take the products
    /// FLINT would make by Kronecker substitution.
    mat_mul: (usize, usize),
}

impl SmallFq {
    fn cutoffs(&self) -> Cutoffs {
        let n = self.n;
        // Over GF(p) FLINT's products pack several entries into a word, and
        // from about 400 on go by Strassen's method.
        let via_p = if n <= 8 { 560 } else { usize::MAX };
        match self.form() {
            Form::Bits => Cutoffs {
                mullow: (2, if n <= 4 { 96 } else { 64 }, 256 * n),
                divrem: (2, 3, 24, 640 * n),
                gcd: (6, 8192),
                xgcd: (6, 768 * n),
                mat_mul: (1, usize::MAX),
            },
            Form::Planes => Cutoffs {
                mullow: (n + 1, 64 * (n + 1), if n == 1 { 512 } else { 3072 / n }),
                divrem: (n + 1, (8 * (n - 1)).max(8), 72 * n, if n == 1 { 1536 } else { 9216 / n }),
                gcd: (if n <= 2 { 16 } else { 16 * (n - 1) }, 8192),
                xgcd: (if n <= 2 { 12 } else { 24 }, 8192),
                mat_mul: (
                    match n {
                        1 | 2 => 8,
                        3 => 10,
                        _ => 13,
                    },
                    via_p,
                ),
            },
            Form::Lanes => Cutoffs {
                mullow: ((n + 1).max(3), 40 * n + 64, if n == 1 { 128 } else { 512 }),
                divrem: (n + 2, if n == 1 { 6 } else { 8 }, 64 * n, if n == 1 { 384 } else { 1536 }),
                // FLINT's Euclid, on these methods, beats the kernels' own:
                // they would convert every remainder.
                gcd: (
                    usize::MAX,
                    match n {
                        1 => 768,
                        // Half-gcd rests on products, slower with larger tables.
                        7 | 8 if self.qm1 >= 1 << 18 => 1536,
                        2..=8 => 448,
                        9 | 10 => 1024,
                        _ => 8192,
                    },
                ),
                xgcd: (
                    usize::MAX,
                    match n {
                        1..=6 => 128,
                        7 | 8 => 192,
                        9 | 10 => 256,
                        _ => 8192,
                    },
                ),
                mat_mul: (if n <= 8 { 8 } else { 10 }, via_p),
            },
        }
    }
}

/// fq_zech's cutoffs for half-gcd: below the first it recurses no further,
/// below the second Euclid's algorithm finishes a gcd.
const HGCD_INNER: sys::slong = 35;
const HGCD_OUTER: sys::slong = 96;

/// `$go!(n)` for the degree n from 1 to 4, as a constant.
macro_rules! by_degree {
    ($n:expr, $go:ident) => {
        match $n {
            1 => $go!(1),
            2 => $go!(2),
            3 => $go!(3),
            4 => $go!(4),
            _ => unreachable!("planes are for degrees up to 4"),
        }
    };
}

/// The kernels of one field with Zech logarithms.
pub struct SmallFq {
    p: u64,
    /// The degree.
    n: usize,
    /// q - 1: the order of g, and FLINT's word for zero.
    qm1: u64,
    zech: Zech,
    /// FLINT's table of the powers of g: the coordinates of g^k are the
    /// base-p digits of eval[k], and eval[q - 1] = 0. The field's context
    /// owns it, and outlives this.
    eval: &'static [sys::ulong],
    div: Div,
    /// The coefficients of the modulus below x^n.
    modulus: Vec<u64>,
    tabs: OnceLock<Tabs>,
}

/// A row being accumulated into: its sums are kept unreduced, in the form
/// of its field.
pub struct Acc {
    len: usize,
    /// Planes: plane u of the coordinates at u·stride.
    h: Vec<u32>,
    stride: usize,
    /// Lanes and bits: a word per entry.
    w: Vec<u64>,
    /// The addmuls since the sums were last reduced.
    pending: usize,
}

/// A reduced row, the operand of row updates.
pub struct Opd {
    len: usize,
    /// Planes: the n planes of the coordinates, one after the other. Lanes:
    /// the logarithms, with 2(q - 1) for zero. Bits: the coordinates.
    h: Vec<u32>,
}

impl Acc {
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl Opd {
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl SmallFq {
    /// The kernels of the field of `ctx`, when it has Zech logarithms.
    pub fn of(ctx: &Ctx) -> Option<&SmallFq> {
        let CtxKind::FqZech { .. } = ctx.kind() else { return None };
        let e = unsafe { ext(ctx.ptr()) };
        // The extension lives as long as the context.
        (!e.is_null()).then(|| unsafe { &(*e).k })
    }

    /// The kernels of the fq_zech context `z`, which must outlive them.
    unsafe fn new(z: *const sys::fq_zech_ctx_struct) -> SmallFq {
        let zc = unsafe { &*z };
        let f = unsafe { &(*zc.fq_nmod_ctx).modulus[0] };
        let n = f.length as usize - 1;
        let q = zc.qm1 as usize + 1;
        SmallFq {
            p: zc.p as u64,
            n,
            qm1: zc.qm1 as u64,
            zech: unsafe { Zech::from_raw(z) },
            eval: unsafe { std::slice::from_raw_parts(zc.eval_table, q) },
            div: Div::new(zc.p as u64),
            modulus: (0..n).map(|i| unsafe { *f.coeffs.add(i) } as u64).collect(),
            tabs: OnceLock::new(),
        }
    }

    fn tabs(&self) -> &Tabs {
        self.tabs.get_or_init(|| self.build(self.form() == Form::Planes))
    }

    fn logs(&self) -> &Logs {
        match self.tabs() {
            Tabs::Planes(t) => &t.logs,
            Tabs::Lanes(t) => &t.logs,
            Tabs::Bits(t) => &t.logs,
        }
    }

    /// The form of the field's rows: bits for p = 2, planes for degrees up
    /// to 4 when they hold a product, lanes otherwise.
    fn form(&self) -> Form {
        match self.p {
            2 => Form::Bits,
            _ if self.n <= 4 && self.planes_slack() >= 1 => Form::Planes,
            _ => Form::Lanes,
        }
    }

    /// The addmuls a reduced row in planes takes before a lane could pass
    /// 2^32: each adds at most n (p - 1)^2.
    fn planes_slack(&self) -> u64 {
        let pm1 = self.p - 1;
        (u32::MAX as u64 - pm1) / (self.n as u64 * pm1 * pm1)
    }

    // ----- scalars, as logarithms -------------------------------------------------

    /// The word of zero, q - 1.
    pub fn zero(&self) -> u64 {
        self.qm1
    }

    pub fn mul(&self, x: u64, y: u64) -> u64 {
        self.zech.mul(x, y)
    }

    pub fn add(&self, x: u64, y: u64) -> u64 {
        self.zech.add(x, y)
    }

    pub fn neg(&self, x: u64) -> u64 {
        self.zech.neg(x)
    }

    /// 1/x, unless x is zero.
    pub fn inv(&self, x: u64) -> Option<u64> {
        self.zech.inv(x)
    }

    /// x/y, unless y is zero.
    pub fn div(&self, x: u64, y: u64) -> Option<u64> {
        self.zech.div(x, y)
    }

    // ----- rows ---------------------------------------------------------------------

    /// A row of `len` zeros to accumulate into.
    pub fn acc(&self, len: usize) -> Acc {
        let (h, w) = match self.tabs() {
            Tabs::Planes(_) => (vec![0; self.n * len], Vec::new()),
            _ => (Vec::new(), vec![0; len]),
        };
        Acc { len, h, stride: len, w, pending: 0 }
    }

    /// The row with the given entries.
    pub fn acc_from_logs(&self, xs: &[u64]) -> Acc {
        let (h, w) = match self.tabs() {
            Tabs::Planes(_) => (self.planes_of(xs), Vec::new()),
            Tabs::Lanes(t) => (Vec::new(), xs.iter().map(|&x| t.anti[x as usize]).collect()),
            Tabs::Bits(_) => (Vec::new(), xs.iter().map(|&x| self.eval[x as usize] as u64).collect()),
        };
        Acc { len: xs.len(), h, stride: xs.len(), w, pending: 0 }
    }

    /// The operand with the given entries.
    pub fn opd_from_logs(&self, xs: &[u64]) -> Opd {
        let h = match self.tabs() {
            Tabs::Planes(_) => self.planes_of(xs),
            Tabs::Lanes(_) => {
                let (zero, z) = (self.qm1, 2 * self.qm1);
                xs.iter().map(|&x| (if x == zero { z } else { x }) as u32).collect()
            }
            Tabs::Bits(_) => xs.iter().map(|&x| self.eval[x as usize] as u32).collect(),
        };
        Opd { len: xs.len(), h }
    }

    /// The first `out.len()` entries of the row.
    pub fn to_logs(&self, acc: &mut Acc, out: &mut [u64]) {
        let len = out.len();
        assert!(len <= acc.len, "more entries than the row has");
        match self.tabs() {
            Tabs::Planes(t) => {
                self.planes_reduce(t, acc, 0..len);
                for (j, o) in out.iter_mut().enumerate() {
                    let v = (0..self.n).rev().fold(0, |v, u| v * self.p + acc.h[u * acc.stride + j] as u64);
                    *o = t.logs.get(v as usize);
                }
            }
            Tabs::Lanes(t) => {
                for (o, x) in out.iter_mut().zip(&mut acc.w) {
                    *x = t.reduce(*x);
                    *o = t.logs.get(t.value(*x));
                }
            }
            Tabs::Bits(t) => {
                for (o, x) in out.iter_mut().zip(&mut acc.w) {
                    *x = t.reduce(*x);
                    *o = t.logs.get(*x as usize);
                }
            }
        }
    }

    /// The row as an operand.
    pub fn to_opd(&self, acc: &mut Acc) -> Opd {
        self.opd_prefix(acc, acc.len)
    }

    /// acc[off + j] += c·b[j] for j in `cols`, c a logarithm. The sums are
    /// reduced first when they could otherwise overflow.
    pub fn addmul(&self, acc: &mut Acc, off: usize, c: u64, b: &Opd, cols: Range<usize>) {
        assert!(cols.start <= cols.end && cols.end <= b.len && off + cols.end <= acc.len, "columns outside the rows");
        if c == self.qm1 || cols.is_empty() {
            return;
        }
        let dst = off + cols.start..off + cols.end;
        match self.tabs() {
            Tabs::Planes(t) => {
                if acc.pending == t.slack {
                    self.planes_reduce(t, acc, 0..acc.len);
                    acc.pending = 0;
                }
                acc.pending += 1;
                macro_rules! go {
                    ($n:literal) => {
                        self.planes_addmul::<$n>(t, acc, dst, c, b, cols)
                    };
                }
                by_degree!(self.n, go)
            }
            Tabs::Lanes(t) => {
                if acc.pending == t.slack {
                    for x in &mut acc.w[..acc.len] {
                        *x = t.reduce(*x);
                    }
                    acc.pending = 0;
                }
                acc.pending += 1;
                lanes_addmul(&t.anti, &mut acc.w[dst], c as u32, &b.h[cols], self.qm1 as u32);
            }
            Tabs::Bits(t) => bits_addmul(t.clmul, &mut acc.w[dst], self.eval[c as usize] as u64, &b.h[cols]),
        }
    }

    /// The logarithm of entry i, which is reduced (the others are not).
    pub fn entry(&self, acc: &mut Acc, i: usize) -> u64 {
        assert!(i < acc.len, "an entry outside the row");
        match self.tabs() {
            Tabs::Planes(t) => {
                let (p, s) = (self.p as u32, acc.stride);
                let mut v = 0;
                for u in (0..self.n).rev() {
                    let x = barrett(acc.h[u * s + i], p, t.minv);
                    acc.h[u * s + i] = x;
                    v = v * self.p + x as u64;
                }
                t.logs.get(v as usize)
            }
            Tabs::Lanes(t) => {
                let x = t.reduce(acc.w[i]);
                acc.w[i] = x;
                t.logs.get(t.value(x))
            }
            Tabs::Bits(t) => {
                let x = t.reduce(acc.w[i]);
                acc.w[i] = x;
                t.logs.get(x as usize)
            }
        }
    }

    /// Σ a[j] b[j], as a logarithm.
    pub fn dot(&self, a: &Opd, b: &Opd) -> u64 {
        assert_eq!(a.len, b.len, "operands of different lengths");
        match self.tabs() {
            Tabs::Planes(t) => {
                macro_rules! go {
                    ($n:literal) => {
                        self.planes_dot::<$n>(t, a, b)
                    };
                }
                by_degree!(self.n, go)
            }
            Tabs::Lanes(t) => {
                let qm1 = self.qm1 as u32;
                let mut s = 0u64;
                for (x, y) in a.h.chunks(t.slack).zip(b.h.chunks(t.slack)) {
                    s = t.reduce(s.wrapping_add(lanes_dot(&t.anti, x, y, qm1)));
                }
                t.logs.get(t.value(s))
            }
            Tabs::Bits(t) => t.logs.get(t.reduce(bits_dot(t.clmul, &a.h, &b.h)) as usize),
        }
    }

    /// b := c·b, c a logarithm.
    pub fn scale(&self, b: &mut Opd, c: u64) {
        match self.tabs() {
            Tabs::Planes(t) => {
                let mut acc = self.acc(b.len);
                self.addmul(&mut acc, 0, c, b, 0..b.len);
                self.planes_reduce(t, &mut acc, 0..b.len);
                b.h = acc.h;
            }
            Tabs::Lanes(_) => {
                let (qm1, z) = (self.qm1 as u32, 2 * self.qm1 as u32);
                if c == self.qm1 {
                    b.h.fill(z);
                } else {
                    for y in &mut b.h {
                        let e = *y + c as u32;
                        *y = if *y == z { z } else { e.min(e.wrapping_sub(qm1)) };
                    }
                }
            }
            Tabs::Bits(t) => {
                let c = self.eval[c as usize] as u64;
                for y in &mut b.h {
                    *y = t.reduce(clmul(t.clmul, c, *y as u64)) as u32;
                }
            }
        }
    }

    /// The first `len` entries of the row as an operand.
    fn opd_prefix(&self, acc: &mut Acc, len: usize) -> Opd {
        let mut o = Opd { len: 0, h: Vec::new() };
        self.opd_prefix_into(acc, len, &mut o);
        o
    }

    /// The same into `o`, whose memory is reused.
    fn opd_prefix_into(&self, acc: &mut Acc, len: usize, o: &mut Opd) {
        assert!(len <= acc.len, "more entries than the row has");
        o.len = len;
        o.h.clear();
        match self.tabs() {
            Tabs::Planes(t) => {
                self.planes_reduce(t, acc, 0..len);
                for plane in acc.h.chunks_exact(acc.stride.max(1)).take(self.n) {
                    o.h.extend_from_slice(&plane[..len]);
                }
            }
            Tabs::Lanes(t) => {
                let (zero, z) = (self.qm1, 2 * self.qm1);
                o.h.extend(acc.w[..len].iter_mut().map(|x| {
                    *x = t.reduce(*x);
                    let l = t.logs.get(t.value(*x));
                    (if l == zero { z } else { l }) as u32
                }));
            }
            Tabs::Bits(t) => o.h.extend(acc.w[..len].iter_mut().map(|x| {
                *x = t.reduce(*x);
                *x as u32
            })),
        }
    }

    /// The tables of one form: planes when asked for and they can hold a
    /// product (they then take at least one addmul between reductions).
    fn build(&self, planes: bool) -> Tabs {
        let logs = Logs::new(self.eval, self.qm1);
        if self.p == 2 {
            return Tabs::Bits(Bits::new(self, logs));
        }
        let slack = self.planes_slack();
        if planes && self.n <= 4 && slack >= 1 {
            let minv = ((1u64 << 32) / self.p) as u32;
            return Tabs::Planes(Planes { logs, minv, slack: slack as usize, avx2: avx2() });
        }
        Tabs::Lanes(Lanes::new(self, logs))
    }
}

// ----- the forms -------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum Form {
    Planes,
    Lanes,
    Bits,
}

enum Tabs {
    Planes(Planes),
    Lanes(Lanes),
    Bits(Bits),
}

/// The logarithms of the elements (q - 1 for zero), indexed by the base-p
/// value of their coordinates, in the narrowest integers that hold them.
enum Logs {
    U8(Box<[u8]>),
    U16(Box<[u16]>),
    U32(Box<[u32]>),
}

impl Logs {
    /// The inverse of FLINT's table of the powers of g.
    fn new(eval: &[sys::ulong], qm1: u64) -> Logs {
        macro_rules! inverse {
            ($t:ty) => {{
                let mut lg = vec![qm1 as $t; qm1 as usize + 1];
                for (k, &v) in eval[..qm1 as usize].iter().enumerate() {
                    lg[v as usize] = k as $t;
                }
                lg.into_boxed_slice()
            }};
        }
        match qm1 {
            0..=0xff => Logs::U8(inverse!(u8)),
            0x100..=0xffff => Logs::U16(inverse!(u16)),
            _ => Logs::U32(inverse!(u32)),
        }
    }

    #[inline(always)]
    fn get(&self, v: usize) -> u64 {
        match self {
            Logs::U8(t) => t[v] as u64,
            Logs::U16(t) => t[v] as u64,
            Logs::U32(t) => t[v] as u64,
        }
    }
}

/// Exact division of numbers below 2^32 by d: the quotient is the high
/// word of m v for m = ⌈2^64 / d⌉ (Lemire, Kaser and Kurz).
#[derive(Clone, Copy)]
struct Div {
    d: u64,
    m: u64,
}

impl Div {
    fn new(d: u64) -> Div {
        Div { d, m: u64::MAX / d + 1 }
    }

    #[inline(always)]
    fn divrem(self, v: u64) -> (u64, u64) {
        let q = ((self.m as u128 * v as u128) >> 64) as u64;
        (q, v - q * self.d)
    }
}

fn avx2() -> bool {
    #[cfg(target_arch = "x86_64")]
    return std::is_x86_feature_detected!("avx2");
    #[allow(unreachable_code)]
    false
}

// ----- coordinates in planes -------------------------------------------------------

struct Planes {
    logs: Logs,
    /// floor(2^32 / p), for Barrett's reduction.
    minv: u32,
    /// The addmuls a reduced row takes before a lane could pass 2^32: each
    /// adds at most n (p - 1)^2.
    slack: usize,
    #[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
    avx2: bool,
}

/// x mod p for x below 2^32 by Barrett's method: the estimated quotient is
/// short by at most one, which the minimum takes off without a branch.
#[inline(always)]
fn barrett(x: u32, p: u32, minv: u32) -> u32 {
    let t = x.wrapping_sub((((x as u64) * (minv as u64)) >> 32) as u32 * p);
    t.min(t.wrapping_sub(p))
}

#[inline(always)]
fn barrett_lanes(r: &mut [u32], p: u32, minv: u32) {
    for x in r.iter_mut() {
        *x = barrett(*x, p, minv);
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn barrett_lanes_avx2(r: &mut [u32], p: u32, minv: u32) {
    barrett_lanes(r, p, minv)
}

/// r_u += Σ_v m[u][v] b_v lane by lane, unreduced: b times the matrix m of
/// multiplication by an element. Eight lanes at a time, which stay in
/// vector registers.
#[inline(always)]
fn planes_addmul_k<const N: usize>(m: &[[u32; N]; N], b: &[&[u32]; N], r: &mut [&mut [u32]; N]) {
    let len = b[0].len();
    assert!(b.iter().all(|x| x.len() == len) && r.iter().all(|x| x.len() == len));
    let whole = len / 8 * 8;
    for i in (0..whole).step_by(8) {
        let bv: [[u32; 8]; N] = std::array::from_fn(|v| b[v][i..i + 8].try_into().unwrap());
        for u in 0..N {
            let mut s: [u32; 8] = r[u][i..i + 8].try_into().unwrap();
            for v in 0..N {
                for x in 0..8 {
                    s[x] = s[x].wrapping_add(m[u][v].wrapping_mul(bv[v][x]));
                }
            }
            r[u][i..i + 8].copy_from_slice(&s);
        }
    }
    for i in whole..len {
        for u in 0..N {
            let mut s = r[u][i];
            for v in 0..N {
                s = s.wrapping_add(m[u][v].wrapping_mul(b[v][i]));
            }
            r[u][i] = s;
        }
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn planes_addmul_avx2<const N: usize>(m: &[[u32; N]; N], b: &[&[u32]; N], r: &mut [&mut [u32]; N]) {
    planes_addmul_k::<N>(m, b, r)
}

/// s[t] += the coefficient of x^t in Σ_j a_j(x) b_j(x), the a_j and b_j
/// being the columns of the planes (t < 2N - 1). Each lane of the partial
/// sums takes one in eight of the columns, so the caller passes at most
/// eight times the planes' slack.
#[inline(always)]
fn planes_dot_k<const N: usize>(a: &[&[u32]; N], b: &[&[u32]; N], s: &mut [u64; 7]) {
    let len = a[0].len();
    assert!(a.iter().chain(b).all(|x| x.len() == len));
    let whole = len / 8 * 8;
    let mut acc = [[0u32; 8]; 7];
    for i in (0..whole).step_by(8) {
        let av: [[u32; 8]; N] = std::array::from_fn(|j| a[j][i..i + 8].try_into().unwrap());
        let bv: [[u32; 8]; N] = std::array::from_fn(|k| b[k][i..i + 8].try_into().unwrap());
        for j in 0..N {
            for k in 0..N {
                for x in 0..8 {
                    acc[j + k][x] = acc[j + k][x].wrapping_add(av[j][x].wrapping_mul(bv[k][x]));
                }
            }
        }
    }
    for t in 0..2 * N - 1 {
        s[t] += acc[t].iter().map(|&x| x as u64).sum::<u64>();
    }
    for i in whole..len {
        for j in 0..N {
            for k in 0..N {
                s[j + k] += a[j][i] as u64 * b[k][i] as u64;
            }
        }
    }
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn planes_dot_avx2<const N: usize>(a: &[&[u32]; N], b: &[&[u32]; N], s: &mut [u64; 7]) {
    planes_dot_k::<N>(a, b, s)
}

impl SmallFq {
    /// The coordinates of the elements with the given logarithms, in planes.
    fn planes_of(&self, xs: &[u64]) -> Vec<u32> {
        let len = xs.len();
        let mut h = vec![0; self.n * len];
        for (j, &x) in xs.iter().enumerate() {
            let mut v = self.eval[x as usize] as u64;
            for u in 0..self.n {
                let (q, r) = self.div.divrem(v);
                h[u * len + j] = r as u32;
                v = q;
            }
        }
        h
    }

    /// The matrix of multiplication by g^c: column v holds the coordinates
    /// of g^(c + v).
    fn mul_matrix<const N: usize>(&self, c: u64) -> [[u32; N]; N] {
        let mut m = [[0; N]; N];
        for v in 0..N {
            let e = c + v as u64;
            let mut x = self.eval[e.min(e.wrapping_sub(self.qm1)) as usize] as u64;
            for row in m.iter_mut() {
                let (q, r) = self.div.divrem(x);
                row[v] = r as u32;
                x = q;
            }
        }
        m
    }

    fn planes_addmul<const N: usize>(&self, t: &Planes, acc: &mut Acc, dst: Range<usize>, c: u64, b: &Opd, cols: Range<usize>) {
        let m = self.mul_matrix::<N>(c);
        let bs: [&[u32]; N] = std::array::from_fn(|v| &b.h[v * b.len..][cols.clone()]);
        let mut planes = acc.h.chunks_exact_mut(acc.stride);
        let mut rs: [&mut [u32]; N] = std::array::from_fn(|_| &mut planes.next().unwrap()[dst.clone()]);
        #[cfg(target_arch = "x86_64")]
        if t.avx2 {
            return unsafe { planes_addmul_avx2::<N>(&m, &bs, &mut rs) };
        }
        let _ = t;
        planes_addmul_k::<N>(&m, &bs, &mut rs)
    }

    /// Reduce the lanes of `cols` in every plane.
    fn planes_reduce(&self, t: &Planes, acc: &mut Acc, cols: Range<usize>) {
        if cols.is_empty() {
            return;
        }
        let p = self.p as u32;
        for plane in acc.h.chunks_exact_mut(acc.stride).take(self.n) {
            #[cfg(target_arch = "x86_64")]
            if t.avx2 {
                unsafe { barrett_lanes_avx2(&mut plane[cols.clone()], p, t.minv) };
                continue;
            }
            barrett_lanes(&mut plane[cols.clone()], p, t.minv);
        }
    }

    fn planes_dot<const N: usize>(&self, t: &Planes, a: &Opd, b: &Opd) -> u64 {
        let mut s = [0u64; 7];
        let chunk = 8 * t.slack;
        for start in (0..a.len).step_by(chunk.max(1)) {
            let cols = start..(start + chunk).min(a.len);
            let x: [&[u32]; N] = std::array::from_fn(|v| &a.h[v * a.len..][cols.clone()]);
            let y: [&[u32]; N] = std::array::from_fn(|v| &b.h[v * b.len..][cols.clone()]);
            #[cfg(target_arch = "x86_64")]
            if t.avx2 {
                unsafe { planes_dot_avx2::<N>(&x, &y, &mut s) };
                continue;
            }
            planes_dot_k::<N>(&x, &y, &mut s);
        }
        // The sum of s_t x^t modulo the modulus: x^t is g^t.
        let p = self.p;
        let mut c = [0u64; N];
        for (t, &st) in s.iter().enumerate().take(2 * N - 1) {
            let st = st % p;
            if t < N {
                c[t] = (c[t] + st) % p;
                continue;
            }
            let mut v = self.eval[t] as u64;
            for cu in c.iter_mut() {
                let (q, r) = self.div.divrem(v);
                *cu = (*cu + st * r) % p;
                v = q;
            }
        }
        t.logs.get(c.iter().rev().fold(0, |v, &cu| v * p + cu) as usize)
    }
}

// ----- coordinates in the lanes of a word -------------------------------------------

struct Lanes {
    logs: Logs,
    /// anti[k] holds the coordinates of g^k, `bits` bits a lane with the
    /// constant term lowest; anti[q - 1] = 0.
    anti: Box<[u64]>,
    /// v mod p for lane values v below 2^bits, when bits is at most 16
    /// (else `div`).
    residue: Box<[u8]>,
    bits: u32,
    n: usize,
    p: u64,
    div: Div,
    /// The addmuls a reduced row takes: each adds at most p - 1 to a lane.
    slack: usize,
}

impl Lanes {
    fn new(k: &SmallFq, logs: Logs) -> Lanes {
        let (p, n) = (k.p, k.n);
        let bits = (64 / n as u32).min(32);
        let slack = ((1u64 << bits) - 1) / (p - 1) - 1;
        assert!(slack >= 1, "lanes too narrow for GF({p}^{n})");
        // The lanes of the digits of v, from tables for the low h digits and
        // the rest.
        let h = n.div_ceil(2);
        let lanes = |mut v: u64, digits: usize| -> u64 {
            (0..digits).fold(0, |w, l| {
                let (q, r) = k.div.divrem(v);
                v = q;
                w | r << (bits * l as u32)
            })
        };
        let ph = p.pow(h as u32);
        let lo: Vec<u64> = (0..ph).map(|v| lanes(v, h)).collect();
        let hi: Vec<u64> = (0..p.pow((n - h) as u32)).map(|v| lanes(v, n - h) << (bits * h as u32)).collect();
        let dh = Div::new(ph);
        let anti = k
            .eval
            .iter()
            .map(|&v| {
                let (a, b) = dh.divrem(v as u64);
                hi[a as usize] | lo[b as usize]
            })
            .collect();
        let residue = if bits <= 16 { (0..1u64 << bits).map(|v| (v % p) as u8).collect() } else { Box::default() };
        Lanes { logs, anti, residue, bits, n, p, div: k.div, slack: slack as usize }
    }

    /// The lanes of x modulo p.
    #[inline(always)]
    fn reduce(&self, x: u64) -> u64 {
        let mask = (1u64 << self.bits) - 1;
        let mut r = 0;
        for l in 0..self.n {
            let s = self.bits * l as u32;
            let v = x >> s & mask;
            let c = if self.residue.is_empty() { self.div.divrem(v).1 } else { self.residue[v as usize] as u64 };
            r |= c << s;
        }
        r
    }

    /// The base-p value of reduced lanes.
    #[inline(always)]
    fn value(&self, x: u64) -> usize {
        let mask = (1u64 << self.bits) - 1;
        (0..self.n).rev().fold(0, |v, l| v * self.p + (x >> (self.bits * l as u32) & mask)) as usize
    }
}

/// The index into the antilogarithms of g^c g^y for words c and y of
/// operands (below 2(q - 1), which stands for zero): c + y modulo q - 1, or
/// q - 1 (where anti is zero) if either is zero. Written with minima, which
/// compile to vector code without branches.
#[inline(always)]
fn anti_index(c: u32, y: u32, qm1: u32) -> u32 {
    let e = c + y;
    e.min(e.wrapping_sub(qm1)).min(qm1)
}

/// r[j] += anti[c + b[j]]: the indices first, 64 at a time in vector code,
/// then the lookups.
#[inline(always)]
fn lanes_addmul(anti: &[u64], r: &mut [u64], c: u32, b: &[u32], qm1: u32) {
    let mut idx = [0u32; 64];
    for (rc, bc) in r.chunks_mut(64).zip(b.chunks(64)) {
        for (i, &y) in idx.iter_mut().zip(bc) {
            *i = anti_index(c, y, qm1);
        }
        for (x, &i) in rc.iter_mut().zip(&idx) {
            // anti has q entries and the index is at most q - 1.
            *x = x.wrapping_add(unsafe { *anti.get_unchecked(i as usize) });
        }
    }
}

/// Σ anti[a[j] + b[j]], unreduced (the caller keeps within the slack).
#[inline(always)]
fn lanes_dot(anti: &[u64], a: &[u32], b: &[u32], qm1: u32) -> u64 {
    let mut idx = [0u32; 64];
    let mut s = 0u64;
    for (ac, bc) in a.chunks(64).zip(b.chunks(64)) {
        for ((i, &x), &y) in idx.iter_mut().zip(ac).zip(bc) {
            *i = anti_index(x, y, qm1);
        }
        for &i in &idx[..ac.len()] {
            s = s.wrapping_add(unsafe { *anti.get_unchecked(i as usize) });
        }
    }
    s
}

// ----- coordinates as bits (p = 2) ---------------------------------------------------

struct Bits {
    logs: Logs,
    /// red[j][v] = v x^(n + 8j) modulo the modulus: products, of degree
    /// below 2n - 1, are reduced a byte of their high part at a time.
    red: Box<[[u32; 256]; 3]>,
    n: u32,
    /// Whether the processor multiplies without carries.
    clmul: bool,
}

impl Bits {
    fn new(k: &SmallFq, logs: Logs) -> Bits {
        let n = k.n as u32;
        let f = k.modulus.iter().enumerate().fold(1u64 << n, |f, (i, &c)| f | (c & 1) << i);
        let slow = |mut x: u64| {
            for t in (n..64).rev() {
                if x >> t & 1 == 1 {
                    x ^= f << (t - n);
                }
            }
            x as u32
        };
        let red = Box::new(std::array::from_fn(|j| std::array::from_fn(|v| slow((v as u64) << (n + 8 * j as u32)))));
        Bits { logs, red, n, clmul: has_clmul() }
    }

    #[inline(always)]
    fn reduce(&self, x: u64) -> u64 {
        let h = x >> self.n;
        let r = self.red[0][(h & 255) as usize] ^ self.red[1][(h >> 8 & 255) as usize] ^ self.red[2][(h >> 16 & 255) as usize];
        (x & ((1 << self.n) - 1)) ^ r as u64
    }
}

fn has_clmul() -> bool {
    #[cfg(target_arch = "x86_64")]
    return std::is_x86_feature_detected!("pclmulqdq");
    #[cfg(target_arch = "aarch64")]
    return std::arch::is_aarch64_feature_detected!("aes");
    #[allow(unreachable_code)]
    false
}

/// The carry-less product of x and y below 2^20, in software: the bits of
/// each split by their position modulo 4, so that the ordinary products of
/// the parts, of at most five bits each, carry only into the three bits
/// above each position they fill.
#[inline(always)]
fn clmul_soft(x: u64, y: u64) -> u64 {
    const M: [u64; 4] = [0x1111_1111_1111_1111, 0x2222_2222_2222_2222, 0x4444_4444_4444_4444, 0x8888_8888_8888_8888];
    let xs = M.map(|m| x & m);
    let ys = M.map(|m| y & m);
    let mut r = 0;
    for (k, m) in M.iter().enumerate() {
        let z = (0..4).fold(0u64, |z, i| z ^ xs[i].wrapping_mul(ys[(k + 4 - i) % 4]));
        r |= z & m;
    }
    r
}

#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn clmul_hw(x: u64, y: u64) -> u64 {
    use std::arch::x86_64::*;
    #[allow(unused_unsafe)]
    unsafe {
        _mm_cvtsi128_si64(_mm_clmulepi64_si128(_mm_cvtsi64_si128(x as i64), _mm_cvtsi64_si128(y as i64), 0)) as u64
    }
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn clmul_hw(x: u64, y: u64) -> u64 {
    #[allow(unused_unsafe)]
    let r = unsafe { std::arch::aarch64::vmull_p64(x, y) };
    r as u64
}

/// `$body` with `$mul` the carry-less product: the processor's in a
/// function compiled for it when `$hw`, else the one in software.
macro_rules! with_clmul {
    ($hw:expr, $mul:ident, fn $f:ident($($a:ident: $t:ty),*) -> $r:ty $body:block) => {{
        #[inline(always)]
        fn $f($($a: $t,)* $mul: impl Fn(u64, u64) -> u64) -> $r $body
        #[cfg(target_arch = "x86_64")]
        if $hw {
            #[target_feature(enable = "pclmulqdq")]
            unsafe fn compiled($($a: $t),*) -> $r {
                $f($($a,)* clmul_hw)
            }
            return unsafe { compiled($($a),*) };
        }
        #[cfg(target_arch = "aarch64")]
        if $hw {
            #[target_feature(enable = "aes")]
            unsafe fn compiled($($a: $t),*) -> $r {
                $f($($a,)* clmul_hw)
            }
            return unsafe { compiled($($a),*) };
        }
        $f($($a,)* clmul_soft)
    }};
}

fn clmul(hw: bool, x: u64, y: u64) -> u64 {
    with_clmul!(hw, mul, fn go(x: u64, y: u64) -> u64 { mul(x, y) })
}

/// r[j] ^= c·b[j], unreduced.
fn bits_addmul(hw: bool, r: &mut [u64], c: u64, b: &[u32]) {
    with_clmul!(hw, mul, fn go(r: &mut [u64], c: u64, b: &[u32]) -> () {
        for (x, &y) in r.iter_mut().zip(b) {
            *x ^= mul(c, y as u64);
        }
    })
}

/// Σ a[j] b[j], unreduced.
fn bits_dot(hw: bool, a: &[u32], b: &[u32]) -> u64 {
    with_clmul!(hw, mul, fn go(a: &[u32], b: &[u32]) -> u64 {
        a.iter().zip(b).fold(0, |s, (&x, &y)| s ^ mul(x as u64, y as u64))
    })
}

// ----- the classical polynomial algorithms ------------------------------------------

impl SmallFq {
    /// The product of the polynomials a and b, both nonzero, modulo x^n:
    /// rows of the longer factor scaled by the terms of the shorter.
    fn mullow(&self, a: &[u64], b: &[u64], n: usize) -> Acc {
        let (a, b) = if a.len() <= b.len() { (a, b) } else { (b, a) };
        let b = self.opd_from_logs(&b[..b.len().min(n)]);
        let mut acc = self.acc(n);
        for (i, &c) in a.iter().enumerate().take(n) {
            self.addmul(&mut acc, i, c, &b, 0..b.len.min(n - i));
        }
        acc
    }

    /// Divide the polynomial in the first `la` entries of acc by the one
    /// with leading coefficient 1/linv and lower coefficients bo, leaving
    /// the remainder in the first bo.len entries. The coefficients of the
    /// quotient go to `quo` from the top, with their indices.
    fn divide(&self, acc: &mut Acc, la: usize, bo: &Opd, linv: u64, mut quo: impl FnMut(usize, u64)) {
        let lb = bo.len + 1;
        for i in (0..=la - lb).rev() {
            let t = self.entry(acc, i + lb - 1);
            let c = if t == self.qm1 { t } else { self.zech.mul(t, linv) };
            quo(i, c);
            self.addmul(acc, i, self.zech.neg(c), bo, 0..bo.len);
        }
    }

    /// The length of the polynomial in the first `len` entries of acc
    /// without its zero leading terms.
    fn top(&self, acc: &mut Acc, mut len: usize) -> usize {
        while len > 0 && self.entry(acc, len - 1) == self.qm1 {
            len -= 1;
        }
        len
    }

    /// The divisor in the first `len` entries of acc (normalised), for
    /// `divide`: its lower coefficients, into `o`, and the inverse of its
    /// leading one.
    fn divisor(&self, acc: &mut Acc, len: usize, o: &mut Opd) -> u64 {
        let linv = self.zech.inv(self.entry(acc, len - 1)).expect("a normalised divisor");
        self.opd_prefix_into(acc, len - 1, o);
        linv
    }

    /// The last nonzero remainder of Euclid's algorithm on the polynomials
    /// in r0 and r1, of lengths l0 >= l1 >= 1 (r1 normalised), with its
    /// length.
    fn euclid(&self, mut r0: Acc, mut l0: usize, mut r1: Acc, mut l1: usize) -> (Acc, usize) {
        let mut o = Opd { len: 0, h: Vec::new() };
        loop {
            let linv = self.divisor(&mut r1, l1, &mut o);
            self.divide(&mut r0, l0, &o, linv, |_, _| {});
            let l2 = self.top(&mut r0, l1 - 1);
            if l2 == 0 {
                return (r1, l1);
            }
            (r0, r1, l0, l1) = (r1, r0, l1, l2);
        }
    }

    /// Euclid's algorithm with cofactors on a and b (la >= lb >= 2, b
    /// normalised): the last nonzero remainder g = s a + t b and the
    /// cofactors, as rows with their lengths. The cofactors are those of
    /// FLINT's `_gr_poly_xgcd_euclidean`: B and (0, 1) when b divides a,
    /// else the unique ones of least degree.
    fn xgcd(&self, a: &[u64], b: &[u64]) -> [(Acc, usize); 3] {
        let (la, lb) = (a.len(), b.len());
        let one = |len: usize| {
            let mut v = vec![self.qm1; len];
            v[0] = 0;
            self.acc_from_logs(&v)
        };
        let (mut r0, mut r1, mut l0, mut l1) = (self.acc_from_logs(a), self.acc_from_logs(b), la, lb);
        // The cofactors of r0 and r1: (1, 0) and (0, 1).
        let (mut s0, mut s1, mut ls0, mut ls1) = (one(lb), self.acc(lb), 1, 0);
        let (mut t0, mut t1, mut lt0, mut lt1) = (self.acc(la), one(la), 0, 1);
        let mut quo = Vec::new();
        let [mut o, mut os, mut ot] = std::array::from_fn(|_| Opd { len: 0, h: Vec::new() });
        loop {
            let linv = self.divisor(&mut r1, l1, &mut o);
            quo.clear();
            self.divide(&mut r0, l0, &o, linv, |i, c| {
                if c != self.qm1 {
                    quo.push((i, c))
                }
            });
            let l2 = self.top(&mut r0, l1 - 1);
            if l2 == 0 {
                return [(r1, l1), (s1, ls1), (t1, lt1)];
            }
            let lq = l0 - l1 + 1;
            ls0 = self.submul(&mut s0, ls0, &quo, &mut s1, ls1, lq, &mut os);
            lt0 = self.submul(&mut t0, lt0, &quo, &mut t1, lt1, lq, &mut ot);
            (r0, r1, l0, l1) = (r1, r0, l1, l2);
            (s0, s1, ls0, ls1) = (s1, s0, ls1, ls0);
            (t0, t1, lt0, lt1) = (t1, t0, lt1, lt0);
        }
    }

    /// x0 -= q x1 for the quotient with the given terms and length lq, x0
    /// and x1 of lengths l0 and l1 (x1 through the operand o): the new
    /// length of x0.
    #[allow(clippy::too_many_arguments)]
    fn submul(&self, x0: &mut Acc, l0: usize, quo: &[(usize, u64)], x1: &mut Acc, l1: usize, lq: usize, o: &mut Opd) -> usize {
        if l1 == 0 {
            return l0;
        }
        self.opd_prefix_into(x1, l1, o);
        for &(i, c) in quo {
            self.addmul(x0, i, self.zech.neg(c), o, 0..l1);
        }
        self.top(x0, l0.max(lq + l1 - 1))
    }
}

// ----- the gr context ----------------------------------------------------------------

mod mat;

type Clear = unsafe extern "C" fn(GrCtx);
type Mullow = unsafe extern "C" fn(*mut c_void, *const c_void, sys::slong, *const c_void, sys::slong, sys::slong, GrCtx) -> c_int;
type Divrem = unsafe extern "C" fn(*mut c_void, *mut c_void, *const c_void, sys::slong, *const c_void, sys::slong, GrCtx) -> c_int;
type MatMul = unsafe extern "C" fn(*mut sys::gr_mat_struct, *const sys::gr_mat_struct, *const sys::gr_mat_struct, GrCtx) -> c_int;

/// What a field with Zech logarithms made by calyx adds to its gr context,
/// at data word 1: its own copy of FLINT's method table, FLINT's methods
/// that the copy replaces, and the kernels.
struct Ext {
    methods: [sys::gr_funcptr; TAB_SIZE],
    clear: Clear,
    mullow: Mullow,
    divrem: Divrem,
    mat_mul: MatMul,
    cut: Cutoffs,
    k: SmallFq,
}

/// The fq_zech context of a gr context of a field with Zech logarithms, at
/// data word 0.
unsafe fn fq_zech(ctx: GrCtx) -> *const sys::fq_zech_ctx_struct {
    unsafe { std::ptr::read_unaligned((*ctx).data.as_ptr() as *const *const sys::fq_zech_ctx_struct) }
}

/// The extension of a gr context of a field with Zech logarithms (null for
/// one made by FLINT alone).
unsafe fn ext(ctx: GrCtx) -> *mut Ext {
    unsafe { std::ptr::read_unaligned((*ctx).data.as_ptr().add(8) as *const *mut Ext) }
}

/// Give `c`, the gr context of a field with Zech logarithms just made by
/// FLINT (and zeroed before), its extension: the context's methods become
/// FLINT's, with the kernels in place of polynomial products, division,
/// gcds and products of matrices, and with a clear that frees the extension
/// too.
pub(crate) unsafe fn install(c: GrCtx) {
    unsafe {
        let z = fq_zech(c);
        let flint = std::slice::from_raw_parts((*c).methods, TAB_SIZE);
        let method = |i: sys::gr_method| flint[i as usize].expect("FLINT's methods for fq_zech");
        let k = SmallFq::new(z);
        let mut e = Box::new(Ext {
            methods: flint.try_into().unwrap(),
            clear: std::mem::transmute::<unsafe extern "C" fn() -> c_int, Clear>(method(sys::gr_method_GR_METHOD_CTX_CLEAR)),
            mullow: std::mem::transmute::<unsafe extern "C" fn() -> c_int, Mullow>(method(sys::gr_method_GR_METHOD_POLY_MULLOW)),
            divrem: std::mem::transmute::<unsafe extern "C" fn() -> c_int, Divrem>(method(sys::gr_method_GR_METHOD_POLY_DIVREM)),
            mat_mul: std::mem::transmute::<unsafe extern "C" fn() -> c_int, MatMul>(method(sys::gr_method_GR_METHOD_MAT_MUL)),
            cut: k.cutoffs(),
            k,
        });
        let ours: [(sys::gr_method, *const ()); 6] = [
            (sys::gr_method_GR_METHOD_CTX_CLEAR, ctx_clear as *const ()),
            (sys::gr_method_GR_METHOD_POLY_MULLOW, poly_mullow as *const ()),
            (sys::gr_method_GR_METHOD_POLY_DIVREM, poly_divrem as *const ()),
            (sys::gr_method_GR_METHOD_POLY_GCD, poly_gcd as *const ()),
            (sys::gr_method_GR_METHOD_POLY_XGCD, poly_xgcd as *const ()),
            (sys::gr_method_GR_METHOD_MAT_MUL, mat::mat_mul as *const ()),
        ];
        for (i, f) in ours {
            e.methods[i as usize] = Some(std::mem::transmute::<*const (), unsafe extern "C" fn() -> c_int>(f));
        }
        let e = Box::into_raw(e);
        std::ptr::write_unaligned((*c).data.as_mut_ptr().add(8) as *mut *mut Ext, e);
        (*c).methods = (*e).methods.as_mut_ptr();
    }
}

/// The words of a vector of `len` elements (a word each). FLINT may pass
/// null for an empty one, such as the remainder of a division by a constant.
unsafe fn words<'a>(x: *const c_void, len: usize) -> &'a [u64] {
    if len == 0 {
        return &[];
    }
    unsafe { std::slice::from_raw_parts(x as *const u64, len) }
}

unsafe fn words_mut<'a>(x: *mut c_void, len: usize) -> &'a mut [u64] {
    if len == 0 {
        return &mut [];
    }
    unsafe { std::slice::from_raw_parts_mut(x as *mut u64, len) }
}

// The methods. Each reads its operands into rows before it writes, so that
// outputs may overlap inputs as FLINT allows (the remainder of a division
// may be its dividend).

unsafe extern "C" fn ctx_clear(ctx: GrCtx) {
    unsafe {
        let e = Box::from_raw(ext(ctx));
        // FLINT's own, which frees the fq_zech context with its tables.
        (e.clear)(ctx);
    }
}

unsafe extern "C" fn poly_mullow(res: *mut c_void, a: *const c_void, la: sys::slong, b: *const c_void, lb: sys::slong, n: sys::slong, ctx: GrCtx) -> c_int {
    unsafe {
        let e = &*ext(ctx);
        let (short, long) = (la.min(lb) as usize, la.max(lb) as usize);
        let (from, area, to) = e.cut.mullow;
        if n < 1 || short < 1 || short > to {
            return (e.mullow)(res, a, la, b, lb, n, ctx);
        }
        if short < from || short * long < area {
            // FLINT's own choice would take Kronecker substitution for long
            // results, even with a short factor.
            let ((x, lx), (y, ly)) = if la <= lb { ((a, la), (b, lb)) } else { ((b, lb), (a, la)) };
            _fq_zech_poly_mullow_classical(res, x, lx, y, ly, n, fq_zech(ctx).cast());
            return SUCCESS;
        }
        let mut acc = e.k.mullow(words(a, la as usize), words(b, lb as usize), n as usize);
        e.k.to_logs(&mut acc, words_mut(res, n as usize));
        SUCCESS
    }
}

unsafe extern "C" fn poly_divrem(q: *mut c_void, r: *mut c_void, a: *const c_void, la: sys::slong, b: *const c_void, lb: sys::slong, ctx: GrCtx) -> c_int {
    unsafe {
        let e = &*ext(ctx);
        if lb < 1 || la < lb || *(b as *const u64).add(lb as usize - 1) == e.k.qm1 {
            return (e.divrem)(q, r, a, la, b, lb, ctx);
        }
        let (la, lb) = (la as usize, lb as usize);
        let lq = la - lb + 1;
        let (quotient, divisor, area, to) = e.cut.divrem;
        if lb.min(lq) > to {
            return (e.divrem)(q, r, a, la as sys::slong, b, lb as sys::slong, ctx);
        }
        if lq < quotient || lb < divisor || lq * lb < area {
            return sys::_gr_poly_divrem_basecase(q, r, a, la as sys::slong, b, lb as sys::slong, ctx);
        }
        let mut acc = e.k.acc_from_logs(words(a, la));
        let mut d = e.k.acc_from_logs(words(b, lb));
        let mut o = Opd { len: 0, h: Vec::new() };
        let linv = e.k.divisor(&mut d, lb, &mut o);
        let quo = words_mut(q, lq);
        e.k.divide(&mut acc, la, &o, linv, |i, c| quo[i] = c);
        e.k.to_logs(&mut acc, words_mut(r, lb - 1));
        SUCCESS
    }
}

/// A gcd, not made monic (`gr_poly_gcd` does that), of a and b of lengths
/// la >= lb >= 1: the last nonzero remainder, as FLINT's Euclid finds it.
unsafe extern "C" fn poly_gcd(g: *mut c_void, lg: *mut sys::slong, a: *const c_void, la: sys::slong, b: *const c_void, lb: sys::slong, ctx: GrCtx) -> c_int {
    unsafe {
        let e = &*ext(ctx);
        let (lo, hi) = e.cut.gcd;
        if lb as usize > hi {
            return sys::_gr_poly_gcd_hgcd(g, lg, a, la, b, lb, HGCD_INNER, HGCD_OUTER, ctx);
        }
        if (lb as usize) < lo.max(2) {
            return sys::_gr_poly_gcd_euclidean(g, lg, a, la, b, lb, ctx);
        }
        let (la, lb) = (la as usize, lb as usize);
        let (r0, r1) = (e.k.acc_from_logs(words(a, la)), e.k.acc_from_logs(words(b, lb)));
        let (mut r, len) = e.k.euclid(r0, la, r1, lb);
        e.k.to_logs(&mut r, words_mut(g, len));
        *lg = len as sys::slong;
        SUCCESS
    }
}

/// The same with cofactors, g = s a + t b; s and t are written out to the
/// lengths lb - 1 and la - 1, zero above their degrees.
unsafe extern "C" fn poly_xgcd(
    lg: *mut sys::slong,
    g: *mut c_void,
    s: *mut c_void,
    t: *mut c_void,
    a: *const c_void,
    la: sys::slong,
    b: *const c_void,
    lb: sys::slong,
    ctx: GrCtx,
) -> c_int {
    unsafe {
        let e = &*ext(ctx);
        let (lo, hi) = e.cut.xgcd;
        if lb as usize > hi {
            return sys::_gr_poly_xgcd_hgcd(lg, g, s, t, a, la, b, lb, HGCD_INNER, HGCD_OUTER, ctx);
        }
        if (lb as usize) < lo.max(2) {
            return sys::_gr_poly_xgcd_euclidean(lg, g, s, t, a, la, b, lb, ctx);
        }
        let k = &e.k;
        let (la, lb) = (la as usize, lb as usize);
        let [(mut gr, len), (mut sr, ls), (mut tr, lt)] = k.xgcd(words(a, la), words(b, lb));
        for (acc, used, out) in [(&mut gr, len, words_mut(g, lb)), (&mut sr, ls, words_mut(s, lb - 1)), (&mut tr, lt, words_mut(t, la - 1))] {
            out.fill(k.qm1);
            k.to_logs(acc, &mut out[..used]);
        }
        *lg = len as sys::slong;
        SUCCESS
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Integer;
    use crate::gr::{Elem, conway_polynomial};
    use std::ffi::c_char;
    use std::rc::Rc;

    unsafe extern "C" {
        fn gr_ctx_init_fq_zech_modulus_nmod_poly(ctx: GrCtx, modulus: *const sys::nmod_poly_struct, var: *const c_char) -> c_int;
        fn fq_zech_poly_gcd(r: *mut c_void, a: *const c_void, b: *const c_void, ctx: *const c_void);
        fn fq_zech_poly_xgcd(g: *mut c_void, s: *mut c_void, t: *mut c_void, a: *const c_void, b: *const c_void, ctx: *const c_void);
        fn fq_zech_poly_divrem(q: *mut c_void, r: *mut c_void, a: *const c_void, b: *const c_void, ctx: *const c_void);
    }

    pub(super) struct Lcg(pub(super) u64);

    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            self.0 ^ self.0 >> 29
        }

        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    /// GF(p^n) with Zech logarithms defined by the Conway polynomial (or x -
    /// g for g primitive, for large p): calyx's field, with the kernels, and
    /// FLINT's own, with FLINT's methods.
    pub(super) fn fields(p: u64, n: u64) -> (Rc<Ctx>, Rc<Ctx>) {
        let c = conway_polynomial(p, n).unwrap_or_else(|| match (p, n) {
            (65521, 1) => vec![Integer::from_u64(p - 17), Integer::one()],
            (1048573, 1) => vec![Integer::from_u64(p - 2), Integer::one()],
            _ => panic!("no modulus for GF({p}^{n})"),
        });
        let ours = Ctx::finite_field(&Integer::from_u64(p), &c, true).unwrap();
        let flint = Ctx::try_build(CtxKind::FqZech { p, degree: n }, None, |g| unsafe {
            let mut poly = sys::nmod_poly_struct::default();
            sys::nmod_poly_init(&mut poly, p as sys::ulong);
            for (i, x) in c.iter().enumerate() {
                sys::nmod_poly_set_coeff_ui(&mut poly, i as sys::slong, x.to_u64().unwrap() as sys::ulong);
            }
            let var = std::ffi::CString::new("a").unwrap();
            let st = gr_ctx_init_fq_zech_modulus_nmod_poly(g, &poly, var.as_ptr());
            sys::nmod_poly_clear(&mut poly);
            st
        })
        .unwrap();
        (ours, flint)
    }

    fn zech_ctx(ctx: &Ctx) -> *const sys::fq_zech_ctx_struct {
        unsafe { std::ptr::read_unaligned((*ctx.ptr()).data.as_ptr() as *const *const sys::fq_zech_ctx_struct) }
    }

    /// The kernels of a field in the given form: planes, if they can be, or
    /// lanes for odd p.
    fn kernels_in(ctx: &Ctx, planes: bool) -> SmallFq {
        let k = unsafe { SmallFq::new(zech_ctx(ctx)) };
        assert!(k.tabs.set(k.build(planes)).is_ok());
        k
    }

    fn slack(k: &SmallFq) -> usize {
        match k.tabs() {
            Tabs::Planes(t) => t.slack,
            Tabs::Lanes(t) => t.slack,
            Tabs::Bits(_) => usize::MAX,
        }
    }

    /// Random words of a field, zero one time in five.
    fn word(k: &SmallFq, rng: &mut Lcg) -> u64 {
        if rng.below(5) == 0 { k.qm1 } else { rng.next() % k.qm1 }
    }

    pub(super) fn row(k: &SmallFq, len: usize, rng: &mut Lcg) -> Vec<u64> {
        (0..len).map(|_| word(k, rng)).collect()
    }

    /// The entries of an operand, through an update of a row of zeros.
    fn opd_logs(k: &SmallFq, o: &Opd) -> Vec<u64> {
        let mut acc = k.acc(o.len);
        k.addmul(&mut acc, 0, 0, o, 0..o.len);
        let mut out = vec![0; o.len];
        k.to_logs(&mut acc, &mut out);
        out
    }

    /// Every kernel against the field's arithmetic on logarithms.
    fn check_kernels(k: &SmallFq, rng: &mut Lcg) {
        for len in [1, 2, 7, 8, 9, 31, 64, 65, 130] {
            let xs = row(k, len, rng);
            let mut out = vec![0; len];
            k.to_logs(&mut k.acc_from_logs(&xs), &mut out);
            assert_eq!(out, xs);
            assert_eq!(opd_logs(k, &k.to_opd(&mut k.acc_from_logs(&xs))), xs);
            assert_eq!(opd_logs(k, &k.opd_from_logs(&xs)), xs);
            // Updates, past the slack where it is small.
            let (mut acc, mut want) = (k.acc_from_logs(&xs), xs.clone());
            let rounds = if slack(k) < 3000 { 3 * slack(k) + 5 } else { 60 };
            for _ in 0..rounds {
                let bl = 1 + rng.below(len);
                let b = row(k, bl, rng);
                let from = rng.below(bl);
                let to = from + rng.below(bl - from + 1);
                let off = rng.below(len - to + 1);
                let c = word(k, rng);
                k.addmul(&mut acc, off, c, &k.opd_from_logs(&b), from..to);
                for j in from..to {
                    want[off + j] = k.add(want[off + j], k.mul(c, b[j]));
                }
            }
            let i = rng.below(len);
            assert_eq!(k.entry(&mut acc, i), want[i]);
            k.to_logs(&mut acc, &mut out);
            assert_eq!(out, want, "{len}");
            // Dot products, of rows long enough to pass the slack.
            let dl = if slack(k) < 3000 { 8 * slack(k) + len } else { len };
            let (a, b) = (row(k, dl, rng), row(k, dl, rng));
            let d = a.iter().zip(&b).fold(k.qm1, |s, (&x, &y)| k.add(s, k.mul(x, y)));
            assert_eq!(k.dot(&k.opd_from_logs(&a), &k.opd_from_logs(&b)), d);
            for c in [word(k, rng), 0, k.qm1] {
                let mut o = k.opd_from_logs(&xs);
                k.scale(&mut o, c);
                assert_eq!(opd_logs(k, &o), xs.iter().map(|&x| k.mul(c, x)).collect::<Vec<_>>());
            }
        }
    }

    #[test]
    fn kernels_agree_with_zech_arithmetic() {
        let mut rng = Lcg(0x5eed_0000_f00d);
        let cases: [(u64, u64); 26] = [
            (2, 1),
            (2, 2),
            (2, 5),
            (2, 8),
            (2, 11),
            (2, 17),
            (3, 1),
            (3, 2),
            (3, 4),
            (3, 5),
            (3, 7),
            (3, 12),
            (5, 3),
            (5, 6),
            (7, 2),
            (7, 4),
            (7, 5),
            (13, 5),
            (31, 3),
            (31, 4),
            (101, 3),
            (257, 2),
            (1021, 2),
            (65521, 1),
            (1048573, 1),
            (11, 4),
        ];
        for (p, n) in cases {
            let (ours, _) = fields(p, n);
            let natural = SmallFq::of(&ours).unwrap();
            assert_eq!(natural.p, p);
            for planes in [true, false] {
                let k = kernels_in(&ours, planes);
                let want = match (p, planes && n <= 4) {
                    (2, _) => "bits",
                    (_, true) if (p - 1) * (p - 1) * n + (p - 1) <= u32::MAX as u64 => "planes",
                    _ => "lanes",
                };
                let got = match k.tabs() {
                    Tabs::Planes(_) => "planes",
                    Tabs::Lanes(_) => "lanes",
                    Tabs::Bits(_) => "bits",
                };
                assert_eq!(got, want, "GF({p}^{n})");
                check_kernels(&k, &mut rng);
            }
        }
    }

    /// The words of a polynomial over a field with Zech logarithms.
    fn words_of(f: &Elem) -> Vec<u64> {
        let p = unsafe { &*(f.as_ptr() as *const sys::gr_poly_struct) };
        if p.length == 0 {
            return Vec::new();
        }
        unsafe { std::slice::from_raw_parts(p.coeffs as *const u64, p.length as usize) }.to_vec()
    }

    fn poly_of(px: &Rc<Ctx>, words: &[u64]) -> Elem {
        let mut f = Elem::new(px);
        let base = px.base().unwrap().ptr();
        unsafe {
            let p = f.as_mut_ptr() as *mut sys::gr_poly_struct;
            sys::gr_poly_fit_length(p, words.len() as sys::slong, base);
            std::ptr::copy_nonoverlapping(words.as_ptr(), (*p).coeffs as *mut u64, words.len());
            sys::_gr_poly_set_length(p, words.len() as sys::slong, base);
            sys::_gr_poly_normalise(p, base);
        }
        f
    }

    /// A polynomial of length `len` with a nonzero leading coefficient.
    fn rand_poly(k: &SmallFq, len: usize, rng: &mut Lcg) -> Vec<u64> {
        let mut w = row(k, len, rng);
        if let Some(top) = w.last_mut() {
            *top = rng.next() % k.qm1;
        }
        w
    }

    /// FLINT's fq_zech function on the fq_zech context of `ctx`, with fresh
    /// polynomials for the results (as words).
    fn fq_zech_results<const R: usize>(ctx: &Rc<Ctx>, f: impl FnOnce([*mut c_void; R], *const c_void)) -> [Vec<u64>; R] {
        let px = Ctx::poly(ctx);
        let mut out: [Elem; R] = std::array::from_fn(|_| Elem::new(&px));
        let ptrs = std::array::from_fn(|i| out[i].as_mut_ptr());
        f(ptrs, zech_ctx(ctx).cast());
        out.map(|e| words_of(&e))
    }

    #[test]
    fn polynomials_agree_with_flint() {
        let mut rng = Lcg(0xfeed_beef_1234);
        for (p, n) in [(2u64, 1u64), (2, 4), (2, 9), (2, 16), (3, 2), (3, 4), (3, 6), (5, 3), (7, 5), (13, 2), (31, 4), (101, 3), (1021, 2)] {
            let (ours, flint) = fields(p, n);
            let k = SmallFq::of(&ours).unwrap();
            let (px, fx) = (Ctx::poly(&ours), Ctx::poly(&flint));
            let lens = [(1, 1), (2, 1), (2, 2), (3, 2), (7, 3), (20, 20), (41, 17), (64, 9), (100, 99), (140, 97), (97, 95), (230, 120), (450, 401), (700, 60)];
            for ((cut, cuts), (la, lb)) in cutoff_sets(k).into_iter().flat_map(|c| lens.map(|l| (c, l))) {
                set_cutoffs(&ours, cut);
                let (a, b) = (rand_poly(k, la, &mut rng), rand_poly(k, lb, &mut rng));
                let (fa, fb, ga, gb) = (poly_of(&px, &a), poly_of(&px, &b), poly_of(&fx, &a), poly_of(&fx, &b));
                let what = format!("GF({p}^{n}), lengths {la} and {lb}, cutoffs {cuts}");
                // Products, whole and truncated.
                assert_eq!(words_of(&fa.mul(&fb).unwrap()), words_of(&ga.mul(&gb).unwrap()), "{what}");
                assert_eq!(words_of(&fa.mul(&fa).unwrap()), words_of(&ga.mul(&ga).unwrap()), "{what}");
                for m in [1, la.min(lb), la + lb - 2] {
                    let (mut r, mut s) = (Elem::new(&px), Elem::new(&fx));
                    unsafe {
                        assert_eq!(sys::gr_poly_mullow(r.as_mut_ptr().cast(), fa.as_ptr().cast(), fb.as_ptr().cast(), m as sys::slong, ours.ptr()), 0);
                        assert_eq!(sys::gr_poly_mullow(s.as_mut_ptr().cast(), ga.as_ptr().cast(), gb.as_ptr().cast(), m as sys::slong, flint.ptr()), 0);
                    }
                    assert_eq!(words_of(&r), words_of(&s), "{what}, mullow {m}");
                }
                // Division, against gr on FLINT's context and FLINT's fq_zech.
                let (q, r) = crate::upoly::divrem(&fa, &fb).unwrap();
                let (fq, fr) = crate::upoly::divrem(&ga, &gb).unwrap();
                assert_eq!((words_of(&q), words_of(&r)), (words_of(&fq), words_of(&fr)), "{what}");
                let [tq, tr] = fq_zech_results(&flint, |[q, r], c| unsafe { fq_zech_poly_divrem(q, r, ga.as_ptr(), gb.as_ptr(), c) });
                assert_eq!((words_of(&q), words_of(&r)), (tq, tr), "{what}");
                // The remainder in place of the dividend.
                let mut x = fa.clone();
                let mut qq = Elem::new(&px);
                unsafe { assert_eq!(sys::gr_poly_divrem(qq.as_mut_ptr().cast(), x.as_mut_ptr().cast(), x.as_ptr().cast(), fb.as_ptr().cast(), ours.ptr()), 0) };
                assert_eq!((words_of(&qq), words_of(&x)), (words_of(&q), words_of(&r)), "{what}");
                // Gcds, of coprime polynomials and with a common factor.
                let h = rand_poly(k, 1 + rng.below(lb.min(30)), &mut rng);
                let (fh, gh) = (poly_of(&px, &h), poly_of(&fx, &h));
                for (x, y, u, v) in [(&fa, &fb, &ga, &gb), (&fa.mul(&fh).unwrap(), &fb.mul(&fh).unwrap(), &ga.mul(&gh).unwrap(), &gb.mul(&gh).unwrap())] {
                    let d = crate::upoly::gcd(x, y).unwrap();
                    assert_eq!(words_of(&d), words_of(&crate::upoly::gcd(u, v).unwrap()), "{what}");
                    let [td] = fq_zech_results(&flint, |[d], c| unsafe { fq_zech_poly_gcd(d, u.as_ptr(), v.as_ptr(), c) });
                    assert_eq!(words_of(&d), td, "{what}");
                    let (d, s, t) = crate::upoly::xgcd(x, y).unwrap();
                    let (fd, fs, ft) = crate::upoly::xgcd(u, v).unwrap();
                    assert_eq!([words_of(&d), words_of(&s), words_of(&t)], [words_of(&fd), words_of(&fs), words_of(&ft)], "{what}");
                    let [td, ts, tt] = fq_zech_results(&flint, |[d, s, t], c| unsafe { fq_zech_poly_xgcd(d, s, t, u.as_ptr(), v.as_ptr(), c) });
                    if crate::upoly::divrem(u, v).unwrap().1.poly_len() > 0 && crate::upoly::divrem(v, u).unwrap().1.poly_len() > 0 {
                        assert_eq!([words_of(&d), words_of(&s), words_of(&t)], [td, ts, tt], "{what}");
                    }
                }
                // Powers modulo b.
                if lb > 1 {
                    for e in [Integer::from_u64(0), Integer::from_u64(2), Integer::from_u64(12345), Integer::from_u64(p).pow(n + 3)] {
                        let r = crate::upoly::powmod(&fa, &e, &fb).unwrap();
                        assert_eq!(words_of(&r), words_of(&crate::upoly::powmod(&ga, &e, &gb).unwrap()), "{what}, e = {e:?}");
                    }
                }
            }
        }
    }

    /// The raw methods, to FLINT's contracts: gcds not made monic, and
    /// cofactors zero past their lengths, where a division is exact too.
    #[test]
    fn methods_keep_flint_contracts() {
        let mut rng = Lcg(0x0dd_ba11);
        for (p, n) in [(2u64, 6u64), (3, 3), (7, 5)] {
            let (ours, flint) = fields(p, n);
            let k = SmallFq::of(&ours).unwrap();
            let lens = [(2, 2), (5, 5), (9, 4), (30, 29), (60, 7), (61, 60), (90, 45)];
            for ((cut, cuts), (la, lb)) in cutoff_sets(k).into_iter().flat_map(|c| lens.map(|l| (c, l))) {
                set_cutoffs(&ours, cut);
                let (a, b0) = (rand_poly(k, la, &mut rng), rand_poly(k, lb, &mut rng));
                // b divides a when la = lb and a is a multiple of b.
                let b = if la == lb { a.iter().map(|&x| k.mul(x, 5 % k.qm1)).collect() } else { b0 };
                let mut outs = Vec::new();
                for ctx in [ours.ptr(), flint.ptr()] {
                    let (mut gg, mut s, mut t) = (vec![7u64; lb], vec![7u64; lb - 1], vec![7u64; la - 1]);
                    let mut lg = 0;
                    let method = unsafe { std::mem::transmute::<unsafe extern "C" fn() -> c_int, XgcdOp>((*(*ctx).methods.add(sys::gr_method_GR_METHOD_POLY_XGCD as usize)).unwrap()) };
                    let st = unsafe { method(&mut lg, gg.as_mut_ptr().cast(), s.as_mut_ptr().cast(), t.as_mut_ptr().cast(), a.as_ptr().cast(), la as sys::slong, b.as_ptr().cast(), lb as sys::slong, ctx) };
                    let (mut g2, mut lg2) = (vec![7u64; lb], 0);
                    let gcd = unsafe { std::mem::transmute::<unsafe extern "C" fn() -> c_int, GcdOp>((*(*ctx).methods.add(sys::gr_method_GR_METHOD_POLY_GCD as usize)).unwrap()) };
                    let st2 = unsafe { gcd(g2.as_mut_ptr().cast(), &mut lg2, a.as_ptr().cast(), la as sys::slong, b.as_ptr().cast(), lb as sys::slong, ctx) };
                    outs.push((st, lg, gg[..lg as usize].to_vec(), s, t, st2, lg2, g2[..lg2 as usize].to_vec()));
                }
                assert_eq!(outs[0], outs[1], "GF({p}^{n}), lengths {la} and {lb}, cutoffs {cuts}");
            }
        }
    }

    /// The kernels at every length, and in a window only, so that FLINT's
    /// algorithms on either side of it take their turns: with the measured
    /// cutoffs, the three sets the tests run with.
    const EVERYWHERE: Cutoffs =
        Cutoffs { mullow: (1, 1, usize::MAX), divrem: (1, 1, 1, usize::MAX), gcd: (2, usize::MAX), xgcd: (2, usize::MAX), mat_mul: (1, usize::MAX) };
    const WINDOW: Cutoffs = Cutoffs { mullow: (4, 64, 40), divrem: (4, 8, 64, 40), gcd: (8, 40), xgcd: (8, 40), mat_mul: (4, 40) };

    fn cutoff_sets(k: &SmallFq) -> [(Cutoffs, &'static str); 3] {
        [(k.cutoffs(), "measured"), (EVERYWHERE, "everywhere"), (WINDOW, "window")]
    }

    pub(super) fn set_cutoffs(ctx: &Ctx, cut: Cutoffs) {
        unsafe { (*ext(ctx.ptr())).cut = cut };
    }

    type XgcdOp = unsafe extern "C" fn(*mut sys::slong, *mut c_void, *mut c_void, *mut c_void, *const c_void, sys::slong, *const c_void, sys::slong, GrCtx) -> c_int;
    type GcdOp = unsafe extern "C" fn(*mut c_void, *mut sys::slong, *const c_void, sys::slong, *const c_void, sys::slong, GrCtx) -> c_int;

    #[test]
    fn kernels_of_contexts() {
        let (ours, flint) = fields(3, 5);
        assert!(SmallFq::of(&ours).is_some() && SmallFq::of(&flint).is_none());
        let packed = Ctx::finite_field(&Integer::from_u64(3), &conway_polynomial(3, 5).unwrap(), false).unwrap();
        assert!(SmallFq::of(&packed).is_none() && SmallFq::of(&Ctx::integers()).is_none());
    }

    /// The largest resident size of the process so far, in bytes.
    fn max_rss() -> u64 {
        let mut u: libc::rusage = unsafe { std::mem::zeroed() };
        unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut u) };
        let v = u.ru_maxrss as u64;
        if cfg!(target_os = "macos") { v } else { v * 1024 }
    }

    /// Fields made and dropped in a loop keep memory flat: the context's
    /// clear frees the kernels and FLINT's clear, which it calls, frees the
    /// tables. Run alone in a child process, where no other test's memory
    /// counts.
    #[test]
    fn contexts_free_their_tables() {
        const CHILD: &str = "CALYX_SMALLFQ_LEAK_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let st = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "smallfq::tests::contexts_free_their_tables", "--test-threads=1"])
                .env(CHILD, "1")
                .status()
                .unwrap();
            assert!(st.success());
            return;
        }
        // 2^16 elements: FLINT's tables take 1 MB, the kernels' 128 KB.
        let c = conway_polynomial(2, 16).unwrap();
        let cycle = || {
            let f = Ctx::finite_field(&Integer::from_u64(2), &c, true).unwrap();
            let k = SmallFq::of(&f).unwrap();
            assert_eq!(k.dot(&k.opd_from_logs(&[3]), &k.opd_from_logs(&[5])), 8);
        };
        for _ in 0..20 {
            cycle();
        }
        let before = max_rss();
        for _ in 0..300 {
            cycle();
        }
        let grown = max_rss() - before;
        eprintln!("resident size {before} bytes, grown by {grown}");
        assert!(before > 0 && grown < 16 << 20, "grown by {grown} bytes");
    }
}
