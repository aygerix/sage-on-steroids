//! Arithmetic in GF(p^n) = F_p[x]/(f) for odd primes p below 2^16, with the
//! n coordinates of an element in 8-bit lanes (p below 2^8, n up to 64) or
//! 16-bit ones (n up to 32), so that an element fits in 64 bytes and the
//! packed field contexts (see `packed`) keep it inline.
//!
//! Products sum in the narrowest lanes their bound allows (16 bits for
//! GF(3^40), 32 for GF(251^10)), a chunk of coefficients of the result at a
//! time in a vector, then reduce modulo f by the rows x^(n+k) modulo f, with
//! one reduction modulo p per coefficient. Inverses and norms (resultants
//! with f) come from Euclid's algorithm, the Frobenius from its matrix, and
//! traces from those of the powers of x.
//!
//! Chunks of 16-bit sums (`Chunk`) are vector registers used through
//! intrinsics, as the compiler vectorizes the plain loops poorly: 8 lanes
//! with SSE2 or NEON, 16 with AVX2 where the processor has it (chosen at run
//! time). Wider sums are arrays of 8.

use std::array;
use std::cell::OnceCell;

/// A coordinate, below p.
pub trait Lane: Copy + Eq + Default + std::fmt::Debug + 'static {
    fn get(self) -> u32;
    fn of(x: u32) -> Self;
    /// self - y modulo p, for self and y below p, in the lane's own width
    /// (which the compiler vectorizes well, unlike widened sums).
    fn sub_mod(self, y: Self, p: Self) -> Self;
    /// self + y modulo p, as self - (p - y).
    fn add_mod(self, y: Self, p: Self) -> Self;
}

impl Lane for u8 {
    #[inline(always)]
    fn get(self) -> u32 {
        self as u32
    }

    #[inline(always)]
    fn of(x: u32) -> u8 {
        x as u8
    }

    #[inline(always)]
    fn sub_mod(self, y: u8, p: u8) -> u8 {
        let (r, borrow) = self.overflowing_sub(y);
        if borrow { r.wrapping_add(p) } else { r }
    }

    #[inline(always)]
    fn add_mod(self, y: u8, p: u8) -> u8 {
        self.sub_mod(p - y, p)
    }
}

impl Lane for u16 {
    #[inline(always)]
    fn get(self) -> u32 {
        self as u32
    }

    #[inline(always)]
    fn of(x: u32) -> u16 {
        x as u16
    }

    #[inline(always)]
    fn sub_mod(self, y: u16, p: u16) -> u16 {
        let (r, borrow) = self.overflowing_sub(y);
        if borrow { r.wrapping_add(p) } else { r }
    }

    #[inline(always)]
    fn add_mod(self, y: u16, p: u16) -> u16 {
        self.sub_mod(p - y, p)
    }
}

/// Reduction modulo an odd p below 2^16 by Barrett's method, of words and
/// of 32- and 16-bit values. The quotient estimates are short by at most 1.
#[derive(Clone, Copy, Debug)]
struct Barrett {
    p: u64,
    /// floor(2^64 / p), floor(2^32 / p) and floor(2^16 / p), none exact as
    /// p is odd.
    m64: u64,
    m32: u32,
    m16: u16,
}

impl Barrett {
    fn new(p: u64) -> Barrett {
        Barrett { p, m64: u64::MAX / p, m32: ((1 << 32) / p) as u32, m16: ((1 << 16) / p) as u16 }
    }

    #[inline(always)]
    fn word(self, x: u64) -> u64 {
        let r = x - ((x as u128 * self.m64 as u128) >> 64) as u64 * self.p;
        if r >= self.p { r - self.p } else { r }
    }

    #[inline(always)]
    fn half(self, x: u32) -> u32 {
        let p = self.p as u32;
        let r = x - ((x as u64 * self.m32 as u64) >> 32) as u32 * p;
        if r >= p { r - p } else { r }
    }

    #[inline(always)]
    fn short(self, x: u16) -> u16 {
        let p = self.p as u16;
        let r = x - ((x as u32 * self.m16 as u32) >> 16) as u16 * p;
        if r >= p { r - p } else { r }
    }
}

/// A lane for sums of products, as narrow as their bound allows so that
/// more of them fit in a vector.
trait Acc: Copy + Default + Eq + std::fmt::Debug + std::ops::Add<Output = Self> + std::ops::Mul<Output = Self> + 'static {
    fn of(x: u32) -> Self;
    fn get(self) -> u32;
    /// The value modulo p.
    fn modp(self, b: Barrett) -> Self;
    /// The weights of the terms near the diagonal in `square`: row d has 0
    /// below lane d, 1 at it and 2 above.
    fn weights() -> &'static [[Self; 16]; 16];
}

/// The rows of `Acc::weights`.
macro_rules! weights {
    ($t:ty) => {{
        const W: [[$t; 16]; 16] = {
            let mut w = [[0; 16]; 16];
            let mut d = 0;
            while d < 16 {
                let mut l = d;
                while l < 16 {
                    w[d][l] = if l == d { 1 } else { 2 };
                    l += 1;
                }
                d += 1;
            }
            w
        };
        &W
    }};
}

impl Acc for u16 {
    #[inline(always)]
    fn of(x: u32) -> u16 {
        x as u16
    }

    #[inline(always)]
    fn get(self) -> u32 {
        self as u32
    }

    #[inline(always)]
    fn modp(self, b: Barrett) -> u16 {
        b.short(self)
    }

    fn weights() -> &'static [[u16; 16]; 16] {
        weights!(u16)
    }
}

impl Acc for u32 {
    #[inline(always)]
    fn of(x: u32) -> u32 {
        x
    }

    #[inline(always)]
    fn get(self) -> u32 {
        self
    }

    #[inline(always)]
    fn modp(self, b: Barrett) -> u32 {
        b.half(self)
    }

    fn weights() -> &'static [[u32; 16]; 16] {
        weights!(u32)
    }
}

impl Acc for u64 {
    #[inline(always)]
    fn of(x: u32) -> u64 {
        x as u64
    }

    #[inline(always)]
    fn get(self) -> u32 {
        self as u32
    }

    #[inline(always)]
    fn modp(self, b: Barrett) -> u64 {
        b.word(self)
    }

    fn weights() -> &'static [[u64; 16]; 16] {
        weights!(u64)
    }
}

/// Lanes of sums, the unit the kernels work in: 8, or 16 with AVX2.
trait Chunk: Copy {
    type A: Acc;
    /// The number of lanes.
    const W: usize;
    /// A multiplier of all lanes, as `mla` takes it: copies of it in a
    /// vector, or a lane.
    type S: Copy;
    fn zero() -> Self;
    fn scalar(x: u32) -> Self::S;
    /// The first W lanes of s.
    fn load(s: &[Self::A]) -> Self;
    /// Into the first W lanes of s.
    fn store(self, s: &mut [Self::A]);
    /// The products lane by lane.
    fn mul(self, y: Self) -> Self;
    /// self + x y.
    fn mla(self, x: Self::S, y: Self) -> Self;
    /// What `modp` needs of p, made once per call of a kernel so that it
    /// stays in registers.
    type R: Copy;
    fn reducer(b: Barrett) -> Self::R;
    /// Each lane modulo p, as `Acc::modp`.
    fn modp(self, r: Self::R) -> Self;
}

impl<A: Acc> Chunk for [A; 8] {
    type A = A;
    type S = A;
    const W: usize = 8;

    #[inline(always)]
    fn zero() -> [A; 8] {
        [A::default(); 8]
    }

    #[inline(always)]
    fn scalar(x: u32) -> A {
        A::of(x)
    }

    #[inline(always)]
    fn load(s: &[A]) -> [A; 8] {
        s[..8].try_into().unwrap()
    }

    #[inline(always)]
    fn store(self, s: &mut [A]) {
        s[..8].copy_from_slice(&self);
    }

    #[inline(always)]
    fn mul(self, y: [A; 8]) -> [A; 8] {
        array::from_fn(|i| self[i] * y[i])
    }

    #[inline(always)]
    fn mla(self, x: A, y: [A; 8]) -> [A; 8] {
        array::from_fn(|i| self[i] + x * y[i])
    }

    type R = Barrett;

    #[inline(always)]
    fn reducer(b: Barrett) -> Barrett {
        b
    }

    #[inline(always)]
    fn modp(self, b: Barrett) -> [A; 8] {
        self.map(|x| x.modp(b))
    }
}

/// 16-bit sums in an SSE2 register. The intrinsics are safe to call on
/// every x86-64 processor, as SSE2 is part of the architecture.
#[cfg(target_arch = "x86_64")]
mod simd {
    use std::arch::x86_64::*;

    use super::{Barrett, Chunk};

    #[derive(Clone, Copy)]
    pub struct U16x8(__m128i);

    impl Chunk for U16x8 {
        type A = u16;
        type S = U16x8;
        const W: usize = 8;

        #[inline(always)]
        fn zero() -> U16x8 {
            U16x8(unsafe { _mm_setzero_si128() })
        }

        #[inline(always)]
        fn scalar(x: u32) -> U16x8 {
            U16x8(unsafe { _mm_set1_epi16(x as i16) })
        }

        #[inline(always)]
        fn load(s: &[u16]) -> U16x8 {
            let s = &s[..8];
            // SAFETY: s has 8 lanes, and the load may be unaligned.
            U16x8(unsafe { _mm_loadu_si128(s.as_ptr().cast()) })
        }

        #[inline(always)]
        fn store(self, s: &mut [u16]) {
            let s = &mut s[..8];
            // SAFETY: as for `load`.
            unsafe { _mm_storeu_si128(s.as_mut_ptr().cast(), self.0) }
        }

        #[inline(always)]
        fn mul(self, y: U16x8) -> U16x8 {
            U16x8(unsafe { _mm_mullo_epi16(self.0, y.0) })
        }

        #[inline(always)]
        fn mla(self, x: U16x8, y: U16x8) -> U16x8 {
            U16x8(unsafe { _mm_add_epi16(self.0, _mm_mullo_epi16(x.0, y.0)) })
        }

        /// Copies of p and floor(2^16 / p).
        type R = (__m128i, __m128i);

        #[inline(always)]
        fn reducer(b: Barrett) -> (__m128i, __m128i) {
            unsafe { (_mm_set1_epi16(b.p as i16), _mm_set1_epi16(b.m16 as i16)) }
        }

        /// `Barrett::short` lane by lane. SSE2 has no unsigned minimum of
        /// 16-bit lanes for the last step, min(r, r - p): it is r less the
        /// saturated difference of r and r - p.
        #[inline(always)]
        fn modp(self, (p, m): (__m128i, __m128i)) -> U16x8 {
            unsafe {
                let r = _mm_sub_epi16(self.0, _mm_mullo_epi16(mulhi(self.0, m), p));
                U16x8(_mm_sub_epi16(r, _mm_subs_epu16(r, _mm_sub_epi16(r, p))))
            }
        }
    }

    /// The high halves of the products of the lanes, as `_mm_mulhi_epu16`
    /// but written out: that intrinsic is generic code, which the optimizer
    /// may turn into four times as many instructions on 32-bit lanes.
    #[inline(always)]
    fn mulhi(x: __m128i, m: __m128i) -> __m128i {
        let mut r = x;
        // SAFETY: an SSE2 instruction on registers.
        unsafe { std::arch::asm!("pmulhuw {r}, {m}", r = inout(xmm_reg) r, m = in(xmm_reg) m, options(pure, nomem, nostack, preserves_flags)) };
        r
    }

    /// 16-bit sums in an AVX2 register. Its intrinsics need a processor
    /// with AVX2: the kernels use it only in functions compiled for AVX2,
    /// which run only where `FpLanes::avx2` is set.
    #[derive(Clone, Copy)]
    pub struct U16x16(__m256i);

    impl Chunk for U16x16 {
        type A = u16;
        type S = U16x16;
        const W: usize = 16;

        #[inline(always)]
        fn zero() -> U16x16 {
            U16x16(unsafe { _mm256_setzero_si256() })
        }

        #[inline(always)]
        fn scalar(x: u32) -> U16x16 {
            U16x16(unsafe { _mm256_set1_epi16(x as i16) })
        }

        #[inline(always)]
        fn load(s: &[u16]) -> U16x16 {
            let s = &s[..16];
            // SAFETY: s has 16 lanes, and the load may be unaligned.
            U16x16(unsafe { _mm256_loadu_si256(s.as_ptr().cast()) })
        }

        #[inline(always)]
        fn store(self, s: &mut [u16]) {
            let s = &mut s[..16];
            // SAFETY: as for `load`.
            unsafe { _mm256_storeu_si256(s.as_mut_ptr().cast(), self.0) }
        }

        #[inline(always)]
        fn mul(self, y: U16x16) -> U16x16 {
            U16x16(unsafe { _mm256_mullo_epi16(self.0, y.0) })
        }

        #[inline(always)]
        fn mla(self, x: U16x16, y: U16x16) -> U16x16 {
            U16x16(unsafe { _mm256_add_epi16(self.0, _mm256_mullo_epi16(x.0, y.0)) })
        }

        /// Copies of p and floor(2^16 / p).
        type R = (__m256i, __m256i);

        #[inline(always)]
        fn reducer(b: Barrett) -> (__m256i, __m256i) {
            unsafe { (_mm256_set1_epi16(b.p as i16), _mm256_set1_epi16(b.m16 as i16)) }
        }

        /// `Barrett::short` lane by lane.
        #[inline(always)]
        fn modp(self, (p, m): (__m256i, __m256i)) -> U16x16 {
            unsafe {
                let r = _mm256_sub_epi16(self.0, _mm256_mullo_epi16(mulhi256(self.0, m), p));
                U16x16(_mm256_min_epu16(r, _mm256_sub_epi16(r, p)))
            }
        }
    }

    /// `mulhi` for AVX2.
    #[inline]
    #[target_feature(enable = "avx2")]
    fn mulhi256(x: __m256i, m: __m256i) -> __m256i {
        let r;
        // SAFETY: an AVX2 instruction on registers.
        unsafe {
            std::arch::asm!("vpmulhuw {r}, {x}, {m}", r = lateout(ymm_reg) r, x = in(ymm_reg) x, m = in(ymm_reg) m,
                options(pure, nomem, nostack, preserves_flags))
        };
        r
    }
}

/// 16-bit sums in a NEON register. The intrinsics are safe to call on
/// every AArch64 processor, as NEON is part of the architecture.
#[cfg(target_arch = "aarch64")]
mod simd {
    use std::arch::aarch64::*;

    use super::{Barrett, Chunk};

    #[derive(Clone, Copy)]
    pub struct U16x8(uint16x8_t);

    impl Chunk for U16x8 {
        type A = u16;
        type S = U16x8;
        const W: usize = 8;

        #[inline(always)]
        fn zero() -> U16x8 {
            U16x8(unsafe { vdupq_n_u16(0) })
        }

        #[inline(always)]
        fn scalar(x: u32) -> U16x8 {
            U16x8(unsafe { vdupq_n_u16(x as u16) })
        }

        #[inline(always)]
        fn load(s: &[u16]) -> U16x8 {
            let s = &s[..8];
            // SAFETY: s has 8 lanes.
            U16x8(unsafe { vld1q_u16(s.as_ptr()) })
        }

        #[inline(always)]
        fn store(self, s: &mut [u16]) {
            let s = &mut s[..8];
            // SAFETY: as for `load`.
            unsafe { vst1q_u16(s.as_mut_ptr(), self.0) }
        }

        #[inline(always)]
        fn mul(self, y: U16x8) -> U16x8 {
            U16x8(unsafe { vmulq_u16(self.0, y.0) })
        }

        #[inline(always)]
        fn mla(self, x: U16x8, y: U16x8) -> U16x8 {
            U16x8(unsafe { vmlaq_u16(self.0, x.0, y.0) })
        }

        /// Copies of p and floor(2^16 / p).
        type R = (uint16x8_t, uint16x8_t);

        #[inline(always)]
        fn reducer(b: Barrett) -> (uint16x8_t, uint16x8_t) {
            unsafe { (vdupq_n_u16(b.p as u16), vdupq_n_u16(b.m16)) }
        }

        /// `Barrett::short` lane by lane, the high halves of the products
        /// by floor(2^16 / p) taken from widening products.
        #[inline(always)]
        fn modp(self, (p, m): (uint16x8_t, uint16x8_t)) -> U16x8 {
            unsafe {
                let x = self.0;
                let (lo, hi) = (vmull_u16(vget_low_u16(x), vget_low_u16(m)), vmull_high_u16(x, m));
                let q = vuzp2q_u16(vreinterpretq_u16_u32(lo), vreinterpretq_u16_u32(hi));
                let r = vmlsq_u16(x, q, p);
                U16x8(vminq_u16(r, vsubq_u16(r, p)))
            }
        }
    }
}

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
type C16 = simd::U16x8;
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
type C16 = [u16; 8];
type C32 = [u32; 8];
type C64 = [u64; 8];

/// The rows of coefficients products are reduced and mapped by, in the
/// lanes products sum in: the narrowest that holds their sums (below 2n
/// p^2), so that more of them fit in a vector.
#[derive(Clone, Debug)]
enum Rows<const N: usize> {
    W16(Tables<u16, N>),
    W32(Tables<u32, N>),
    W64(Tables<u64, N>),
}

#[derive(Clone, Debug)]
struct Tables<A, const N: usize> {
    /// x^(n+k) modulo f for k below n - 1, which reduce products.
    red: Vec<[A; N]>,
    /// x^(p i) modulo f for i below n: the rows of the Frobenius.
    frob: Vec<[A; N]>,
}

impl<A: Acc, const N: usize> Tables<A, N> {
    fn new(red: &[[u32; N]], frob: &[[u32; N]]) -> Tables<A, N> {
        let widen = |rows: &[[u32; N]]| rows.iter().map(|r| r.map(A::of)).collect();
        Tables { red: widen(red), frob: widen(frob) }
    }
}

impl<const N: usize> Rows<N> {
    /// The rows in the lanes for sums below 2n p^2.
    fn new(p: u64, n: usize, red: &[[u32; N]], frob: &[[u32; N]]) -> Rows<N> {
        match 2 * n as u64 * (p - 1) * (p - 1) + p {
            0..0x1_0000 => Rows::W16(Tables::new(red, frob)),
            0x1_0000..0x1_0000_0000 => Rows::W32(Tables::new(red, frob)),
            _ => Rows::W64(Tables::new(red, frob)),
        }
    }
}

/// The zeros in front of the polynomials in Euclid's algorithm, so that
/// shifted reads below them find zeros: a chunk's worth.
const PAD: usize = 16;

/// GF(p^n) for an odd prime p below 2^16, its elements `[T; N]` with n
/// coordinates (constant term first) and zeros after.
#[derive(Clone, Debug)]
pub struct FpLanes<T: Lane, const N: usize> {
    b: Barrett,
    n: usize,
    /// Whether the kernels with 16-bit sums run in AVX2 registers: the
    /// processor has it, and N is a multiple of 16 (always so for such
    /// sums, which need p below 2^8).
    #[cfg(target_arch = "x86_64")]
    avx2: bool,
    /// The coefficients of f below x^n, and their negatives (x^n modulo f).
    f: [u32; N],
    fneg: [u32; N],
    rows: Rows<N>,
    /// The inverses modulo p, by residue (0 at 0), made when first needed.
    inv: OnceCell<Vec<T>>,
    /// Tr(x^i) for i below n.
    tr: [u32; N],
}

/// The degree of the polynomial x (-1 for 0), from `top` down.
fn degree_of<A: Acc>(x: &[A], top: isize) -> isize {
    let mut d = top;
    while d >= 0 && x[d as usize] == A::default() {
        d -= 1;
    }
    d
}

impl<T: Lane, const N: usize> FpLanes<T, N> {
    /// The field for a monic irreducible f of degree n, 1 <= n <= N, given
    /// by its coefficients below x^n.
    pub fn new(p: u64, f: &[u64]) -> FpLanes<T, N> {
        let n = f.len();
        assert!(p % 2 == 1 && p > 2 && p >> (8 * std::mem::size_of::<T>()) == 0 && (1..=N).contains(&n));
        let fr: [u32; N] = array::from_fn(|i| if i < n { (f[i] % p) as u32 } else { 0 });
        let fneg: [u32; N] = array::from_fn(|i| ((p - fr[i] as u64) % p) as u32);
        let mut rows = Vec::with_capacity(n - 1);
        let mut r = fneg;
        for _ in 1..n {
            rows.push(r);
            let top = r[n - 1] as u64;
            r = array::from_fn(|i| if i < n { ((if i > 0 { r[i - 1] as u64 } else { 0 } + top * fneg[i] as u64) % p) as u32 } else { 0 });
        }
        let mut k: FpLanes<T, N> = FpLanes {
            b: Barrett::new(p),
            n,
            #[cfg(target_arch = "x86_64")]
            avx2: N % 16 == 0 && is_x86_feature_detected!("avx2"),
            f: fr,
            fneg,
            rows: Rows::new(p, n, &rows, &[]),
            inv: OnceCell::new(),
            tr: [0; N],
        };
        // Newton's identities for the power sums of the roots of f: s_0 = n,
        // s_j = -(j f_(n-j) + the sum over 0 < i < j of f_(n-i) s_(j-i)).
        let mut s = vec![n as u64 % p; n];
        for j in 1..n {
            let t = (1..j).fold(j as u64 % p * k.f[n - j] as u64 % p, |t, i| (t + k.f[n - i] as u64 * s[j - i]) % p);
            s[j] = (p - t) % p;
        }
        for (t, &v) in k.tr.iter_mut().zip(&s) {
            *t = v as u32;
        }
        let (xp, mut row, mut frob) = (k.pow(&k.generator(), &[p]), k.scalar(1), Vec::with_capacity(n));
        for _ in 0..n {
            frob.push(array::from_fn(|i| row[i].get()));
            row = k.mul(&row, &xp);
        }
        k.rows = Rows::new(p, n, &rows, &frob);
        k
    }

    fn zero(&self) -> [T; N] {
        [T::default(); N]
    }

    /// The table of inverses modulo p: 1/i = -(p div i)/(p mod i).
    fn inverses(&self) -> &[T] {
        self.inv.get_or_init(|| {
            let p = self.b.p as u32;
            let mut inv = vec![T::default(); p as usize];
            inv[1] = T::of(1);
            for i in 2..p {
                inv[i as usize] = T::of((p - p / i) * inv[(p % i) as usize].get() % p);
            }
            inv
        })
    }

    /// The element c of the prime field.
    pub fn scalar(&self, c: u64) -> [T; N] {
        let mut r = self.zero();
        r[0] = T::of((c % self.b.p) as u32);
        r
    }

    /// The root of f.
    pub fn generator(&self) -> [T; N] {
        let mut r = self.zero();
        if self.n == 1 {
            r[0] = T::of(self.fneg[0]);
        } else {
            r[1] = T::of(1);
        }
        r
    }

    pub fn add(&self, a: &[T; N], b: &[T; N]) -> [T; N] {
        let p = T::of(self.b.p as u32);
        array::from_fn(|i| a[i].add_mod(b[i], p))
    }

    pub fn sub(&self, a: &[T; N], b: &[T; N]) -> [T; N] {
        let p = T::of(self.b.p as u32);
        array::from_fn(|i| a[i].sub_mod(b[i], p))
    }

    pub fn neg(&self, a: &[T; N]) -> [T; N] {
        let p = T::of(self.b.p as u32);
        array::from_fn(|i| T::default().sub_mod(a[i], p))
    }

    /// a*c for c below p.
    pub fn mul_scalar(&self, a: &[T; N], c: u64) -> [T; N] {
        let c = (c % self.b.p) as u32;
        array::from_fn(|i| T::of(self.b.half(a[i].get() * c)))
    }

    /// The 2n - 1 coefficients of a b (sums below n p^2), a chunk at a time:
    /// each sums its terms in a vector and is stored once.
    #[inline(always)]
    fn product<C: Chunk>(&self, a: &[T; N], b: &[T; N]) -> [[C::A; 2]; N] {
        let n = self.n;
        // b between N zeros on each side, for shifted reads past its ends.
        let mut bp = [[C::A::default(); 3]; N];
        let bp = bp.as_flattened_mut();
        for (x, y) in bp[N..2 * N].iter_mut().zip(b) {
            *x = C::A::of(y.get());
        }
        let xs: [C::S; N] = array::from_fn(|i| C::scalar(a[i].get()));
        let mut acc = [[C::A::default(); 2]; N];
        let out = acc.as_flattened_mut();
        for c in (0..2 * n - 1).step_by(C::W) {
            let mut s = C::zero();
            for i in (c + 1).saturating_sub(n)..n.min(c + C::W) {
                s = s.mla(xs[i], C::load(&bp[N + c - i..]));
            }
            s.store(&mut out[c..]);
        }
        acc
    }

    /// The element with the coefficients of a product: those of degree n and
    /// more taken modulo p and replaced by their multiples of the rows (the
    /// sums stay below 2n p^2), then all modulo p.
    #[inline(always)]
    fn reduce<C: Chunk>(&self, acc: &[[C::A; 2]; N], red: &[[C::A; N]]) -> [T; N] {
        let (n, c, r) = (self.n, acc.as_flattened(), C::reducer(self.b));
        let mut h = [C::A::default(); N];
        for k in (0..n - 1).step_by(C::W) {
            C::load(&c[n + k..]).modp(r).store(&mut h[k..]);
        }
        let mut hs = [C::scalar(0); N];
        for (x, y) in hs.iter_mut().zip(&h[..n - 1]) {
            *x = C::scalar(y.get());
        }
        let mut lo = [C::A::default(); N];
        lo[..n].copy_from_slice(&c[..n]);
        for j in (0..n).step_by(C::W) {
            let s = red.iter().zip(&hs).fold(C::load(&lo[j..]), |s, (row, &h)| s.mla(h, C::load(&row[j..])));
            s.modp(r).store(&mut lo[j..]);
        }
        array::from_fn(|i| if i < n { T::of(lo[i].get()) } else { T::default() })
    }

    /// The 2n - 1 coefficients of a^2 as `product` finds them, with each
    /// product of two different coefficients once, doubled: a chunk at c
    /// takes the terms a_i a_(k-i) with 2i < c in full, and those with 2i
    /// from c to c + W - 1 weighted lane by lane (2 below the diagonal, 1 on
    /// it).
    #[inline(always)]
    fn square<C: Chunk>(&self, a: &[T; N]) -> [[C::A; 2]; N] {
        let n = self.n;
        let mut ap = [[C::A::default(); 3]; N];
        let ap = ap.as_flattened_mut();
        for (x, y) in ap[N..2 * N].iter_mut().zip(a) {
            *x = C::A::of(y.get());
        }
        let xs: [C::S; N] = array::from_fn(|i| C::scalar(a[i].get()));
        let (x2s, w): ([C::S; N], _) = (array::from_fn(|i| C::scalar(2 * a[i].get())), C::A::weights());
        let mut acc = [[C::A::default(); 2]; N];
        let out = acc.as_flattened_mut();
        for c in (0..2 * n - 1).step_by(C::W) {
            let (mut s, lo) = (C::zero(), (c + 1).saturating_sub(n));
            for i in lo..(c / 2).min(n) {
                s = s.mla(x2s[i], C::load(&ap[N + c - i..]));
            }
            for i in (c / 2).max(lo)..(c / 2 + C::W / 2).min(n) {
                s = s.mla(xs[i], C::load(&ap[N + c - i..]).mul(C::load(&w[2 * i - c])));
            }
            s.store(&mut out[c..]);
        }
        acc
    }

    pub fn mul(&self, a: &[T; N], b: &[T; N]) -> [T; N] {
        match &self.rows {
            // SAFETY: `avx2` is set only where the processor has AVX2.
            #[cfg(target_arch = "x86_64")]
            Rows::W16(t) if self.avx2 => unsafe { self.mul_avx2(a, b, &t.red) },
            Rows::W16(t) => self.reduce::<C16>(&self.product::<C16>(a, b), &t.red),
            Rows::W32(t) => self.reduce::<C32>(&self.product::<C32>(a, b), &t.red),
            Rows::W64(t) => self.reduce::<C64>(&self.product::<C64>(a, b), &t.red),
        }
    }

    pub fn sqr(&self, a: &[T; N]) -> [T; N] {
        match &self.rows {
            // SAFETY: as for `mul`.
            #[cfg(target_arch = "x86_64")]
            Rows::W16(t) if self.avx2 => unsafe { self.sqr_avx2(a, &t.red) },
            Rows::W16(t) => self.reduce::<C16>(&self.square::<C16>(a), &t.red),
            Rows::W32(t) => self.reduce::<C32>(&self.square::<C32>(a), &t.red),
            Rows::W64(t) => self.reduce::<C64>(&self.square::<C64>(a), &t.red),
        }
    }

    /// The element c_0 + c_1 x + ... modulo f, for at most 2n - 1
    /// coefficients c_i below p (a product, as Kronecker substitution finds
    /// it).
    pub fn reduce_coeffs(&self, c: &[u64]) -> [T; N] {
        fn spread<C: Chunk, const N: usize>(c: &[u64]) -> [[C::A; 2]; N] {
            let mut acc = [[C::A::default(); 2]; N];
            for (x, &y) in acc.as_flattened_mut().iter_mut().zip(c) {
                *x = C::A::of(y as u32);
            }
            acc
        }
        match &self.rows {
            Rows::W16(t) => self.reduce::<C16>(&spread::<C16, N>(c), &t.red),
            Rows::W32(t) => self.reduce::<C32>(&spread::<C32, N>(c), &t.red),
            Rows::W64(t) => self.reduce::<C64>(&spread::<C64, N>(c), &t.red),
        }
    }

    /// u_i + t v_(i-j) modulo p for i from j to top, over whole aligned
    /// chunks (the other lanes add zeros: v is 0 above its degree and PAD
    /// zeros lead it). The sums stay below p^2.
    #[inline(always)]
    fn shift_axpy<C: Chunk>(&self, u: &mut [C::A], t: u32, v: &[C::A], j: usize, top: usize) {
        let (t, r, k) = (C::scalar(t), C::reducer(self.b), C::W - 1);
        for i in ((j & !k)..(top + C::W) & !k).step_by(C::W) {
            C::load(&u[PAD + i..]).mla(t, C::load(&v[PAD + i - j..])).modp(r).store(&mut u[PAD + i..]);
        }
    }

    /// c u_i + t v_i modulo p for i up to top, over whole chunks (v is 0
    /// above its degree). The sums stay below 2p^2.
    #[inline(always)]
    fn scale_axpy<C: Chunk>(&self, u: &mut [C::A], c: u32, t: u32, v: &[C::A], top: usize) {
        let (c, t, r) = (C::scalar(c), C::scalar(t), C::reducer(self.b));
        for i in (0..(top + C::W) & !(C::W - 1)).step_by(C::W) {
            C::zero().mla(c, C::load(&u[PAD + i..])).mla(t, C::load(&v[PAD + i..])).modp(r).store(&mut u[PAD + i..]);
        }
    }

    /// c u_i + t v_(i-j) + s v_(i-j+1) modulo p for i up to top (j >= 1):
    /// c u_i alone below the chunk of j - 1, where v does not reach, and
    /// all three above it (PAD zeros lead v). The sums stay below 3p^2.
    #[inline(always)]
    fn scale_axpy2<C: Chunk>(&self, u: &mut [C::A], c: u32, t: u32, s: u32, v: &[C::A], j: usize, top: usize) {
        let (c, t, s, k, r) = (C::scalar(c), C::scalar(t), C::scalar(s), C::W - 1, C::reducer(self.b));
        let lo = (j - 1) & !k;
        for i in (0..lo).step_by(C::W) {
            C::zero().mla(c, C::load(&u[PAD + i..])).modp(r).store(&mut u[PAD + i..]);
        }
        for i in (lo..(top + C::W) & !k).step_by(C::W) {
            let x = C::zero().mla(c, C::load(&u[PAD + i..])).mla(t, C::load(&v[PAD + i - j..]));
            x.mla(s, C::load(&v[PAD + i + 1 - j..])).modp(r).store(&mut u[PAD + i..]);
        }
    }

    /// The inverse of a unit, by the extended Euclidean algorithm on a and
    /// f, two leading terms at a time, in the narrowest lanes 3p^2 fits.
    pub fn inv(&self, a: &[T; N]) -> Option<[T; N]> {
        match self.b.p {
            // SAFETY: as for `mul`.
            #[cfg(target_arch = "x86_64")]
            ..=139 if self.avx2 => unsafe { self.inv_avx2(a) },
            ..=139 => self.inv_with::<C16>(a),
            ..=37813 => self.inv_with::<C32>(a),
            _ => self.inv_with::<C64>(a),
        }
    }

    #[inline(always)]
    fn inv_with<C: Chunk>(&self, a: &[T; N]) -> Option<[T; N]> {
        let (n, p) = (self.n, self.b.p as u32);
        // Remainders u and v with cofactors: gu a = u and gv a = v modulo f.
        // With deg gu + deg v <= n and deg gv + deg u <= n throughout, all
        // have degree at most n. Coefficient i is at PAD + i.
        let (mut r, mut g) = ([[[C::A::default(); 4]; N]; 2], [[[C::A::default(); 4]; N]; 2]);
        let ([u, v], [gu, gv]) = (&mut r, &mut g);
        let (mut u, mut v, mut gu, mut gv) = (u.as_flattened_mut(), v.as_flattened_mut(), gu.as_flattened_mut(), gv.as_flattened_mut());
        for i in 0..n {
            (u[PAD + i], v[PAD + i]) = (C::A::of(a[i].get()), C::A::of(self.f[i]));
        }
        (v[PAD + n], gu[PAD]) = (C::A::of(1), C::A::of(1));
        let (mut du, mut dv, mut eu, mut ev) = (degree_of(&u[PAD..], n as isize - 1), n as isize, 0, -1);
        if du < 0 {
            return None;
        }
        // Each step takes the leading terms of u by a multiple of v, with u
        // (and gu) scaled by a power of lc(v) instead of dividing by it, so
        // that no inverse lies on the path from one step to the next. Once
        // v is not zero, neither is gv. `tops` has the two leading
        // coefficients of u and of v when the last step found them.
        let mut tops = None;
        loop {
            if du < dv {
                (u, v, gu, gv) = (v, u, gv, gu);
                (du, dv, eu, ev) = (dv, du, ev, eu);
                tops = tops.map(|(x, y)| (y, x));
            }
            if du == 0 {
                break;
            }
            if dv < 0 {
                return None;
            }
            let (j, d, e) = ((du - dv) as usize, du as usize, dv as usize);
            let top = |x: &[C::A], d: usize| (x[PAD + d].get(), x[PAD + d - 1].get());
            let ((ud, u1), (vd, v1)) = tops.take().unwrap_or_else(|| (top(u, d), top(v, e)));
            if j == 0 {
                // u lc(v) - lc(u) v.
                let t = p - ud;
                self.scale_axpy::<C>(u, vd, t, v, d);
                self.scale_axpy::<C>(gu, vd, t, gv, eu.max(ev) as usize);
                eu = eu.max(ev);
                du = degree_of(&u[PAD..], du - 1);
                continue;
            }
            // u lc(v)^2 - (lc(v) lc(u) x^j + (lc(v) u1 - lc(u) v1) x^(j-1)) v,
            // with u1 and v1 the coefficients below the leading ones (v1 is
            // a leading zero if dv = 0).
            let c = self.b.half(vd * vd);
            let t = p - self.b.half(vd * ud);
            let s = self.b.word(ud as u64 * v1 as u64 + vd as u64 * (p - u1) as u64) as u32;
            // The usual step has j = 1 and leaves a remainder of degree dv
            // - 1: its two leading coefficients, found here before u is
            // overwritten, let the next step start before the vectors are
            // stored. At i = d - 2, v_i is v1.
            let lead = (j == 1).then(|| {
                let r = |i: usize, vi: u32| {
                    let x = c as u64 * u[i].get() as u64 + t as u64 * v[i - 1].get() as u64 + s as u64 * vi as u64;
                    self.b.word(x) as u32
                };
                (r(PAD + d - 2, v1), r(PAD + d - 3, v[PAD + d - 3].get()))
            });
            self.scale_axpy2::<C>(u, c, t, s, v, j, d);
            self.scale_axpy2::<C>(gu, c, t, s, gv, j, eu.max(ev + j as isize) as usize);
            eu = eu.max(ev + j as isize);
            match lead {
                Some((r2, r3)) if r2 != 0 => (du, tops) = (du - 2, Some(((r2, r3), (vd, v1)))),
                _ => du = degree_of(&u[PAD..], du - 2),
            }
        }
        let inv = self.inverses();
        // gu/u, and x^n replaced by its remainder if gu reached degree n.
        let s = C::A::of(inv[u[PAD].get() as usize].get());
        let top = (gu[PAD + n] * s).modp(self.b).get();
        Some(array::from_fn(|i| if i < n { T::of(self.b.half((gu[PAD + i] * s).modp(self.b).get() + top * self.fneg[i])) } else { T::default() }))
    }

    /// b^e modulo p.
    fn pow_mod(&self, b: u32, mut e: u64) -> u64 {
        let (p, mut b, mut r) = (self.b.p, b as u64, 1);
        while e > 0 {
            if e & 1 == 1 {
                r = r * b % p;
            }
            (b, e) = (b * b % p, e >> 1);
        }
        r
    }

    /// The norm to F_p: the resultant of f and a, by Euclid's algorithm with
    /// Res(A, B) = (-1)^(deg A deg B) lc(B)^(deg A - deg R) Res(B, R) for R
    /// = A mod B, and Res(A, c) = c^deg A for a constant c.
    pub fn norm(&self, a: &[T; N]) -> u64 {
        #[cfg(target_arch = "x86_64")]
        if self.b.p < 256 && self.avx2 {
            // SAFETY: as for `mul`.
            return unsafe { self.norm_avx2(a) };
        }
        if self.b.p < 256 { self.norm_with::<C16>(a) } else { self.norm_with::<C32>(a) }
    }

    #[inline(always)]
    fn norm_with<C: Chunk>(&self, a: &[T; N]) -> u64 {
        let (n, p, inv) = (self.n, self.b.p as u32, self.inverses());
        let mut r = [[[C::A::default(); 4]; N]; 2];
        let [x, y] = &mut r;
        let (mut x, mut y) = (x.as_flattened_mut(), y.as_flattened_mut());
        for i in 0..n {
            (x[PAD + i], y[PAD + i]) = (C::A::of(self.f[i]), C::A::of(a[i].get()));
        }
        x[PAD + n] = C::A::of(1);
        let (mut dx, mut dy, mut res) = (n as isize, degree_of(&y[PAD..], n as isize - 1), 1);
        loop {
            if dy < 0 {
                return 0;
            }
            let lc = y[PAD + dy as usize].get();
            if dy == 0 {
                return res * self.pow_mod(lc, dx as u64) % p as u64;
            }
            let (d, li) = (dx, inv[lc as usize].get());
            while dx >= dy {
                let t = p - self.b.half(x[PAD + dx as usize].get() * li);
                self.shift_axpy::<C>(x, t, y, (dx - dy) as usize, dx as usize);
                dx = degree_of(&x[PAD..], dx - 1);
            }
            if dx < 0 {
                return 0;
            }
            if d * dy % 2 == 1 {
                res = (p as u64 - res) % p as u64;
            }
            res = res * self.pow_mod(lc, (d - dx) as u64) % p as u64;
            (x, y, dx, dy) = (y, x, dy, dx);
        }
    }

    /// a^e for the exponent with the given words (least significant first),
    /// by sliding windows of up to 4 bits over the odd powers a, a^3, ...,
    /// a^15 once e has more than 16 bits.
    pub fn pow(&self, a: &[T; N], e: &[u64]) -> [T; N] {
        let Some(top) = e.iter().rposition(|&x| x != 0) else { return self.scalar(1) };
        let bits = 64 * top + 64 - e[top].leading_zeros() as usize;
        let bit = |i: usize| (e[i / 64] >> (i % 64) & 1) as usize;
        if bits <= 16 {
            return (0..bits - 1).rev().fold(*a, |r, i| if bit(i) == 1 { self.mul(&self.sqr(&r), a) } else { self.sqr(&r) });
        }
        let a2 = self.sqr(a);
        let mut odd = [*a; 8];
        for i in 1..8 {
            odd[i] = self.mul(&odd[i - 1], &a2);
        }
        // The top bit is set, so the first window starts the result.
        let (mut r, mut i) = (None, bits as isize - 1);
        while i >= 0 {
            if bit(i as usize) == 0 {
                r = r.map(|x| self.sqr(&x));
                i -= 1;
                continue;
            }
            let mut j = (i - 3).max(0);
            while bit(j as usize) == 0 {
                j += 1;
            }
            let w = (j..=i).rev().fold(0, |w, t| w << 1 | bit(t as usize));
            r = Some(match r {
                None => odd[w >> 1],
                Some(x) => self.mul(&(j..=i).fold(x, |x, _| self.sqr(&x)), &odd[w >> 1]),
            });
            i = j - 1;
        }
        r.unwrap()
    }

    /// a^p, from the rows of the Frobenius (the sums stay below n p^2).
    #[inline(always)]
    fn frobenius_with<C: Chunk>(&self, a: &[T; N], frob: &[[C::A; N]]) -> [T; N] {
        let n = self.n;
        let (xs, r): ([C::S; N], _) = (array::from_fn(|i| C::scalar(a[i].get())), C::reducer(self.b));
        let mut out = [C::A::default(); N];
        for j in (0..n).step_by(C::W) {
            let s = frob.iter().zip(&xs).fold(C::zero(), |s, (row, &x)| s.mla(x, C::load(&row[j..])));
            s.modp(r).store(&mut out[j..]);
        }
        array::from_fn(|i| if i < n { T::of(out[i].get()) } else { T::default() })
    }

    /// a^(p^k).
    pub fn frobenius(&self, a: &[T; N], k: u64) -> [T; N] {
        (0..k % self.n as u64).fold(*a, |x, _| match &self.rows {
            // SAFETY: as for `mul`.
            #[cfg(target_arch = "x86_64")]
            Rows::W16(t) if self.avx2 => unsafe { self.frobenius_avx2(&x, &t.frob) },
            Rows::W16(t) => self.frobenius_with::<C16>(&x, &t.frob),
            Rows::W32(t) => self.frobenius_with::<C32>(&x, &t.frob),
            Rows::W64(t) => self.frobenius_with::<C64>(&x, &t.frob),
        })
    }

    /// The trace to F_p.
    pub fn trace(&self, a: &[T; N]) -> u64 {
        self.b.word(a[..self.n].iter().zip(&self.tr).map(|(x, &t)| x.get() as u64 * t as u64).sum())
    }

    /// The n coordinates.
    pub fn coords(&self, a: &[T; N]) -> Vec<u64> {
        a[..self.n].iter().map(|x| x.get() as u64).collect()
    }

    /// The element with the given coordinates (missing ones are zero).
    pub fn from_coords(&self, c: &[u64]) -> [T; N] {
        let mut r = self.zero();
        for (x, &v) in r.iter_mut().zip(c).take(self.n) {
            *x = T::of((v % self.b.p) as u32);
        }
        r
    }
}

/// The kernels with 16-bit sums compiled for AVX2, as `FpLanes::avx2`
/// chooses at run time.
#[cfg(target_arch = "x86_64")]
impl<T: Lane, const N: usize> FpLanes<T, N> {
    #[target_feature(enable = "avx2")]
    fn mul_avx2(&self, a: &[T; N], b: &[T; N], red: &[[u16; N]]) -> [T; N] {
        self.reduce::<simd::U16x16>(&self.product::<simd::U16x16>(a, b), red)
    }

    #[target_feature(enable = "avx2")]
    fn sqr_avx2(&self, a: &[T; N], red: &[[u16; N]]) -> [T; N] {
        self.reduce::<simd::U16x16>(&self.square::<simd::U16x16>(a), red)
    }

    #[target_feature(enable = "avx2")]
    fn inv_avx2(&self, a: &[T; N]) -> Option<[T; N]> {
        self.inv_with::<simd::U16x16>(a)
    }

    #[target_feature(enable = "avx2")]
    fn norm_avx2(&self, a: &[T; N]) -> u64 {
        self.norm_with::<simd::U16x16>(a)
    }

    #[target_feature(enable = "avx2")]
    fn frobenius_avx2(&self, a: &[T; N], frob: &[[u16; N]]) -> [T; N] {
        self.frobenius_with::<simd::U16x16>(a, frob)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Integer;
    use crate::gr::{conway_polynomial, is_irreducible_mod_p};

    struct Lcg(u64);

    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            self.0 ^ self.0 >> 29
        }
    }

    /// a*b modulo f (its coefficients below x^n) and p, the slow way.
    fn mulmod_naive(p: u64, f: &[u64], a: &[u64], b: &[u64]) -> Vec<u64> {
        let n = f.len();
        let mut c = vec![0u64; 2 * n];
        for i in 0..n {
            for j in 0..n {
                c[i + j] = (c[i + j] + a[i] * b[j]) % p;
            }
        }
        for k in (n..2 * n).rev() {
            let t = std::mem::take(&mut c[k]);
            for i in 0..n {
                c[k - n + i] = (c[k - n + i] + t * (p - f[i])) % p;
            }
        }
        c.truncate(n);
        c
    }

    /// The coefficients below x^n of a monic irreducible polynomial of
    /// degree n over F_p: Conway's if known, else a random one.
    fn modulus(p: u64, n: usize, rng: &mut Lcg) -> Vec<u64> {
        if let Some(c) = conway_polynomial(p, n as u64) {
            return c[..n].iter().map(|x| x.to_u64().unwrap()).collect();
        }
        for _ in 0..100 * n {
            let f: Vec<u64> = (0..n).map(|_| rng.next() % p).collect();
            let ints: Vec<Integer> = f.iter().chain(&[1]).map(|&c| Integer::from_u64(c)).collect();
            if is_irreducible_mod_p(&Integer::from_u64(p), &ints) {
                return f;
            }
        }
        panic!("no irreducible of degree {n} over F_{p}");
    }

    /// The checks below for each set of kernels the processor has.
    fn lanes_agree<T: Lane, const N: usize>(p: u64, f: &[u64], rng: &mut Lcg) {
        let k = FpLanes::<T, N>::new(p, f);
        #[cfg(target_arch = "x86_64")]
        if k.avx2 {
            agree(&FpLanes { avx2: false, ..k.clone() }, p, f, rng);
        }
        agree(&k, p, f, rng);
    }

    fn agree<T: Lane, const N: usize>(k: &FpLanes<T, N>, p: u64, f: &[u64], rng: &mut Lcg) {
        let n = f.len();
        let q = Integer::from_u64(p).pow(n as u64);
        let qm1 = &q - &Integer::one();
        let (e_unit, e_norm) = (qm1.to_limbs(), qm1.divexact(&Integer::from_u64(p - 1)).to_limbs());
        let (zero, one) = (k.zero(), k.scalar(1));
        let rand = |rng: &mut Lcg| -> Vec<u64> { (0..n).map(|_| rng.next() % p).collect() };
        for i in 0..20 {
            let (ca, cb) = (rand(rng), if i == 0 { vec![0; n] } else { rand(rng) });
            let (a, b) = (k.from_coords(&ca), k.from_coords(&cb));
            assert_eq!(k.coords(&a), ca);
            assert_eq!(k.coords(&k.mul(&a, &b)), mulmod_naive(p, f, &ca, &cb), "{p} {n}");
            assert_eq!(k.sqr(&a), k.mul(&a, &a));
            assert_eq!(k.add(&k.sub(&a, &b), &b), a);
            assert_eq!(k.add(&a, &k.neg(&a)), zero);
            let c = rng.next() % p;
            assert_eq!(k.mul_scalar(&a, c), k.mul(&a, &k.scalar(c)));
            if a != zero {
                assert_eq!(k.mul(&a, &k.inv(&a).unwrap()), one);
                assert_eq!(k.pow(&a, &e_unit), one);
            }
            assert_eq!(k.scalar(k.norm(&a)), k.pow(&a, &e_norm));
            assert_eq!(k.norm(&k.mul(&a, &b)), k.norm(&a) * k.norm(&b) % p);
            for j in [0, 1, 2, n as u64 - 1, n as u64 + 1] {
                assert_eq!(k.frobenius(&a, j), k.pow(&a, &Integer::from_u64(p).pow(j % n as u64).to_limbs()));
            }
            let conjugates = (0..n as u64).fold(zero, |s, j| k.add(&s, &k.frobenius(&a, j)));
            assert_eq!(conjugates, k.scalar(k.trace(&a)));
        }
        assert_eq!((k.inv(&zero), k.norm(&zero)), (None, 0));
        let x = k.generator();
        let fx = (0..n).fold(k.pow(&x, &[n as u64]), |s, i| k.add(&s, &k.mul_scalar(&k.pow(&x, &[i as u64]), f[i])));
        assert_eq!(fx, zero);
    }

    fn check(p: u64, n: usize, rng: &mut Lcg) {
        let f = modulus(p, n, rng);
        match (p < 256, n) {
            (true, 1..=16) => lanes_agree::<u8, 16>(p, &f, rng),
            (true, 17..=32) => lanes_agree::<u8, 32>(p, &f, rng),
            (true, _) => lanes_agree::<u8, 64>(p, &f, rng),
            (false, 1..=8) => lanes_agree::<u16, 8>(p, &f, rng),
            (false, 9..=16) => lanes_agree::<u16, 16>(p, &f, rng),
            (false, _) => lanes_agree::<u16, 32>(p, &f, rng),
        }
    }

    #[test]
    fn lanes_agree_with_naive_arithmetic() {
        let mut rng = Lcg(0x243f_6a88_85a3_08d3);
        for n in [1, 2, 3, 13, 16, 17, 32, 40, 64] {
            check(3, n, &mut rng);
        }
        for (p, n) in [(5, 7), (7, 30), (7, 33), (13, 47), (127, 2), (137, 20), (139, 3), (149, 4), (181, 3), (251, 5), (251, 64)] {
            check(p, n, &mut rng);
        }
        for (p, n) in [(257, 1), (257, 2), (257, 32), (1009, 9), (32003, 16), (65521, 2), (65521, 8), (65521, 17), (65521, 32)] {
            check(p, n, &mut rng);
        }
    }
}
