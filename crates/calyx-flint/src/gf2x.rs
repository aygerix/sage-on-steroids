//! Polynomials over GF(2) packed into words (bit i of word w is the
//! coefficient of x^(64w + i)) and multiplied without carries: the kernels
//! of the searches for irreducible polynomials over GF(2), and of the
//! fields GF(2^n) with n up to 512 (`Gf2Field` in a word, `Gf2Words` in up
//! to eight).
//!
//! The moduli of the searches are sparse, x^n plus terms of low degree or
//! few terms, so reduction multiplies the part above x^n by the low terms
//! only; the fields reduce by Barrett's method. Products of words use the
//! processor's carry-less multiplication when it has one (checked at run
//! time), else a table in software.

/// Carry-less products of words, as (low word, high word).
trait Clmul {
    fn mul(a: u64, b: u64) -> (u64, u64);
    fn sqr(a: u64) -> (u64, u64);
}

/// In software, four bits at a time.
struct Soft;

impl Clmul for Soft {
    #[inline(always)]
    fn mul(a: u64, b: u64) -> (u64, u64) {
        let mut t = [0u128; 16];
        for i in 1..16 {
            t[i] = if i % 2 == 0 { t[i / 2] << 1 } else { t[i - 1] ^ a as u128 };
        }
        let r = (0..16).rev().fold(0u128, |r, k| r << 4 ^ t[(b >> (4 * k) & 15) as usize]);
        (r as u64, (r >> 64) as u64)
    }

    #[inline(always)]
    fn sqr(a: u64) -> (u64, u64) {
        (spread(a & 0xffff_ffff), spread(a >> 32))
    }
}

/// Interleave the bits of a 32-bit word with zeros (its square).
#[inline(always)]
fn spread(x: u64) -> u64 {
    let x = (x | x << 16) & 0x0000_ffff_0000_ffff;
    let x = (x | x << 8) & 0x00ff_00ff_00ff_00ff;
    let x = (x | x << 4) & 0x0f0f_0f0f_0f0f_0f0f;
    let x = (x | x << 2) & 0x3333_3333_3333_3333;
    (x | x << 1) & 0x5555_5555_5555_5555
}

/// With the processor's instruction; only reached from functions compiled
/// for it (see `dispatch`).
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
struct Hw;

#[cfg(target_arch = "x86_64")]
impl Clmul for Hw {
    #[inline(always)]
    fn mul(a: u64, b: u64) -> (u64, u64) {
        use std::arch::x86_64::*;
        #[allow(unused_unsafe)]
        unsafe {
            let r = _mm_clmulepi64_si128(_mm_cvtsi64_si128(a as i64), _mm_cvtsi64_si128(b as i64), 0);
            (_mm_cvtsi128_si64(r) as u64, _mm_cvtsi128_si64(_mm_unpackhi_epi64(r, r)) as u64)
        }
    }

    #[inline(always)]
    fn sqr(a: u64) -> (u64, u64) {
        Hw::mul(a, a)
    }
}

#[cfg(target_arch = "aarch64")]
impl Clmul for Hw {
    #[inline(always)]
    fn mul(a: u64, b: u64) -> (u64, u64) {
        #[allow(unused_unsafe)]
        let r = unsafe { std::arch::aarch64::vmull_p64(a, b) };
        (r as u64, (r >> 64) as u64)
    }

    #[inline(always)]
    fn sqr(a: u64) -> (u64, u64) {
        Hw::mul(a, a)
    }
}

/// `$f::<Hw>(args)` compiled for carry-less multiplication when the
/// processor has it, else `$f::<Soft>(args)`.
macro_rules! dispatch {
    ($f:ident($($a:ident: $t:ty),*) -> $r:ty) => {{
        #[cfg(target_arch = "x86_64")]
        if std::is_x86_feature_detected!("pclmulqdq") {
            #[target_feature(enable = "pclmulqdq")]
            unsafe fn hw($($a: $t),*) -> $r {
                $f::<Hw>($($a),*)
            }
            return unsafe { hw($($a),*) };
        }
        #[cfg(target_arch = "aarch64")]
        if std::arch::is_aarch64_feature_detected!("aes") {
            #[target_feature(enable = "aes")]
            unsafe fn hw($($a: $t),*) -> $r {
                $f::<Hw>($($a),*)
            }
            return unsafe { hw($($a),*) };
        }
        $f::<Soft>($($a),*)
    }};
}

/// The terms of a modulus below its leading term x^n.
enum Low {
    /// All of degree below 64, as the bits of a word.
    Word(u64),
    /// Their exponents.
    Terms(Vec<usize>),
}

/// A monic modulus x^n + (low terms) with its scratch space.
struct Modulus {
    n: usize,
    /// Words in a residue.
    w: usize,
    low: Low,
    /// Scratch: a product (2w + 1 words) and the part above x^n.
    s: Vec<u64>,
    h: Vec<u64>,
}

impl Modulus {
    fn new(n: usize, low: &[usize]) -> Modulus {
        let w = n.div_ceil(64);
        let low = if low.iter().all(|&e| e < 64) {
            Low::Word(low.iter().fold(0, |g, &e| g ^ 1 << e))
        } else {
            Low::Terms(low.to_vec())
        };
        Modulus { n, w, low, s: vec![0; 2 * w + 1], h: vec![0; 2 * w + 1] }
    }

    /// The modulus itself, in n + 1 bits.
    fn full(&self) -> Vec<u64> {
        let mut f = vec![0u64; (self.n + 1).div_ceil(64)];
        f[self.n / 64] |= 1 << (self.n % 64);
        match &self.low {
            Low::Word(g) => f[0] ^= g,
            Low::Terms(es) => es.iter().for_each(|&e| f[e / 64] ^= 1 << (e % 64)),
        }
        f
    }

    /// Reduce the product in `s` modulo x^n + low; the residue is left in
    /// the first w words.
    #[inline(always)]
    fn reduce<C: Clmul>(&mut self) {
        let (nw, nb) = (self.n / 64, self.n % 64);
        let (s, h) = (&mut self.s, &mut self.h);
        loop {
            let Some(top) = s.iter().rposition(|&x| x != 0) else { return };
            if top * 64 + 63 - (s[top].leading_zeros() as usize) < self.n {
                return;
            }
            // h = s / x^n, and s mod x^n.
            let hl = top - nw + 1;
            for i in 0..hl {
                h[i] = if nb == 0 { s[nw + i] } else { s[nw + i] >> nb | s.get(nw + i + 1).map_or(0, |&x| x << (64 - nb)) };
            }
            if nb == 0 {
                s[nw..=top].fill(0);
            } else {
                s[nw] &= (1 << nb) - 1;
                s[nw + 1..=top].fill(0);
            }
            match &self.low {
                Low::Word(g) => {
                    for i in 0..hl {
                        let (lo, hi) = C::mul(h[i], *g);
                        s[i] ^= lo;
                        s[i + 1] ^= hi;
                    }
                }
                Low::Terms(es) => {
                    for &e in es {
                        xor_shl(s, &h[..hl], e);
                    }
                }
            }
        }
    }

    /// a^2 mod the modulus, into a.
    #[inline(always)]
    fn sqr_mod<C: Clmul>(&mut self, a: &mut [u64]) {
        for (i, &x) in a.iter().enumerate() {
            (self.s[2 * i], self.s[2 * i + 1]) = C::sqr(x);
        }
        self.s[2 * self.w] = 0;
        self.reduce::<C>();
        a.copy_from_slice(&self.s[..self.w]);
    }

    /// a*b mod the modulus, into a.
    #[inline(always)]
    fn mul_mod<C: Clmul>(&mut self, a: &mut [u64], b: &[u64]) {
        self.s.fill(0);
        for (i, &x) in a.iter().enumerate().filter(|(_, x)| **x != 0) {
            for (j, &y) in b.iter().enumerate() {
                let (lo, hi) = C::mul(x, y);
                self.s[i + j] ^= lo;
                self.s[i + j + 1] ^= hi;
            }
        }
        self.reduce::<C>();
        a.copy_from_slice(&self.s[..self.w]);
    }
}

/// dst ^= src * x^e.
#[inline(always)]
fn xor_shl(dst: &mut [u64], src: &[u64], e: usize) {
    let (ws, bs) = (e / 64, e % 64);
    for (i, &x) in src.iter().enumerate() {
        dst[i + ws] ^= x << bs;
        if bs > 0 {
            dst[i + ws + 1] ^= x >> (64 - bs);
        }
    }
}

/// The degree of a (at most `hint`), if a is not zero.
#[inline(always)]
fn degree(a: &[u64], hint: usize) -> Option<usize> {
    (0..=(hint / 64).min(a.len() - 1)).rev().find(|&i| a[i] != 0).map(|i| i * 64 + 63 - a[i].leading_zeros() as usize)
}

/// Whether gcd(a, b) = 1; clobbers both.
fn gcd_is_one(a: &mut [u64], b: &mut [u64]) -> bool {
    let (mut a, mut b) = (a, b);
    let mut da = degree(a, usize::MAX);
    let mut db = degree(b, usize::MAX);
    loop {
        let Some(n) = db else { return da == Some(0) };
        if n == 0 {
            return true;
        }
        while let Some(m) = da.filter(|&m| m >= n) {
            // a -= b * x^(m - n), over the words of b.
            let (ws, bs) = ((m - n) / 64, (m - n) % 64);
            for i in 0..=n / 64 {
                a[i + ws] ^= b[i] << bs;
                if bs > 0 && i + ws + 1 < a.len() {
                    a[i + ws + 1] ^= b[i] >> (64 - bs);
                }
            }
            da = if m == 0 { None } else { degree(a, m - 1) };
        }
        std::mem::swap(&mut a, &mut b);
        std::mem::swap(&mut da, &mut db);
    }
}

/// Steps of Ben-Or's test before `irreducible` turns to Rabin's.
const BEN_OR_STEPS: usize = 64;

/// Whether the modulus is irreducible, given that it has no factor of
/// degree at most `skip`.
///
/// Ben-Or's test first finds the factors of degree up to 64 (so that most
/// reducible polynomials go quickly), taking the gcds with the products of
/// the x^(2^i) - x at i = 2^k; then, for large n, Rabin's test needs only
/// squarings: x^(2^n) = x, and no factor in common with x^(2^(n/r)) - x
/// for the primes r dividing n.
#[inline(always)]
fn irreducible<C: Clmul>(m: &mut Modulus, skip: usize) -> bool {
    let (n, w) = (m.n, m.w);
    if n <= 1 {
        return n == 1;
    }
    let f = m.full();
    let mut x = vec![0u64; w];
    x[0] = 2;
    let mut h = x.clone();
    let mut acc = vec![0u64; w];
    acc[0] = 1;
    let (mut ga, mut gb) = (vec![0u64; f.len().max(w)], vec![0u64; f.len().max(w)]);
    // Whether gcd(f, a) = 1.
    let mut coprime = |a: &[u64]| {
        ga.fill(0);
        ga[..f.len()].copy_from_slice(&f);
        gb.fill(0);
        gb[..w].copy_from_slice(a);
        gcd_is_one(&mut ga, &mut gb)
    };
    let bound = (n / 2).min(BEN_OR_STEPS);
    let mut t = vec![0u64; w];
    for i in 1..=bound {
        m.sqr_mod::<C>(&mut h);
        if i > skip {
            t.copy_from_slice(&h);
            t[0] ^= 2;
            m.mul_mod::<C>(&mut acc, &t);
            if (i.is_power_of_two() || i == bound) && !coprime(&acc) {
                return false;
            }
            if i.is_power_of_two() {
                acc.fill(0);
                acc[0] = 1;
            }
        }
    }
    if bound == n / 2 {
        return true;
    }
    let checks: Vec<usize> = (2..=n).filter(|&r| n % r == 0 && (2..r).take_while(|d| d * d <= r).all(|d| r % d != 0)).map(|r| n / r).filter(|&c| c > bound).collect();
    for i in bound + 1..=n {
        m.sqr_mod::<C>(&mut h);
        if checks.contains(&i) {
            t.copy_from_slice(&h);
            t[0] ^= 2;
            if !coprime(&t) {
                return false;
            }
        }
    }
    h == x
}

#[inline(always)]
fn is_irreducible_with<C: Clmul>(n: usize, low: &[usize]) -> bool {
    irreducible::<C>(&mut Modulus::new(n, low), 0)
}

/// Whether x^n + (the sum of x^e over `low`, distinct and below n) is
/// irreducible over GF(2).
pub fn is_irreducible_sparse(n: usize, low: &[usize]) -> bool {
    dispatch!(is_irreducible_with(n: usize, low: &[usize]) -> bool)
}

/// The product of polynomials of degree below 32.
fn mul_small(a: u64, b: u64) -> u64 {
    (0..32).filter(|i| b >> i & 1 == 1).fold(0, |r, i| r ^ a << i)
}

/// a mod h, for h not zero.
fn rem_small(mut a: u64, h: u64) -> u64 {
    let dh = 63 - h.leading_zeros();
    while a != 0 && 63 - a.leading_zeros() >= dh {
        a ^= h << (63 - a.leading_zeros() - dh);
    }
    a
}

/// x^e mod h, for h of degree below 32.
fn xpow_small(e: usize, h: u64) -> u64 {
    let mut r = rem_small(1, h);
    for i in (0..usize::BITS - e.leading_zeros()).rev() {
        r = rem_small(mul_small(r, r), h);
        if e >> i & 1 == 1 {
            r = rem_small(r << 1, h);
        }
    }
    r
}

/// The irreducible polynomials of degree 1 to d (d below 32), as bits.
fn small_irreducibles(d: u32) -> Vec<u64> {
    let mut irr: Vec<u64> = Vec::new();
    for h in 2u64..1 << (d + 1) {
        let dh = 63 - h.leading_zeros();
        if irr.iter().take_while(|&&g| 2 * (63 - g.leading_zeros()) <= dh).all(|&g| rem_small(h, g) != 0) {
            irr.push(h);
        }
    }
    irr
}

#[inline(always)]
fn least_low_term_with<C: Clmul>(n: usize) -> Option<u64> {
    if n == 1 {
        return Some(1);
    }
    // x^n + g has the factor h exactly when g = x^n mod h; sieve blocks of
    // candidates by the irreducible h of degree at most 8 and n/2.
    const K: u32 = 12;
    let dmax = (n / 2).min(8) as u32;
    let hs: Vec<(u64, u32, u64)> = small_irreducibles(dmax).into_iter().map(|h| (h, 63 - h.leading_zeros(), xpow_small(n, h))).collect();
    let limit: u128 = 1 << n.min(64);
    let mut bad = vec![false; 1 << K];
    let mut m = Modulus::new(n, &[]);
    let mut base = 0u128;
    while base < limit {
        bad.fill(false);
        for &(h, dh, r) in &hs {
            // The low parts L of candidates base + L with L = r + (base mod h)
            // modulo h, in Gray-code order.
            let mut l = r ^ rem_small(base as u64, h);
            bad[l as usize] = true;
            for k in 1u64..1 << (K - dh) {
                l ^= h << k.trailing_zeros();
                bad[l as usize] = true;
            }
        }
        let size = (limit - base).min(1 << K) as u64;
        for l in (1..size).step_by(2).filter(|&l| !bad[l as usize]) {
            let g = base as u64 + l;
            m.low = Low::Word(g);
            if irreducible::<C>(&mut m, dmax as usize) {
                return Some(g);
            }
        }
        base += 1 << K;
    }
    None
}

/// The least g, as bits, with x^n + g irreducible over GF(2) and g of
/// degree below 64 and n (so with constant term 1, for n above 1).
pub fn least_low_term(n: usize) -> Option<u64> {
    dispatch!(least_low_term_with(n: usize) -> Option<u64>)
}

/// Whether the processor multiplies words without carries.
fn has_clmul() -> bool {
    #[cfg(target_arch = "x86_64")]
    return std::is_x86_feature_detected!("pclmulqdq");
    #[cfg(target_arch = "aarch64")]
    return std::arch::is_aarch64_feature_detected!("aes");
    #[allow(unreachable_code)]
    false
}

/// GF(2)[x]/(f) for f of degree n from 1 to 64 (GF(2^n) when f is
/// irreducible): elements are the bits of their coordinates in the power
/// basis. Products are reduced by Barrett's method, whose quotient is exact
/// for polynomials: three carry-less products in all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Gf2Field {
    n: u32,
    /// f - x^n, and floor(x^(2n) / f) - x^n, both of degree below n.
    g: u64,
    mu: u64,
    hw: bool,
}

/// `$k.$f::<Hw>(args)` compiled for carry-less multiplication when the
/// field found the processor has it, else `$k.$f::<Soft>(args)`.
macro_rules! field_dispatch {
    ($k:ident.$f:ident($($a:ident: $t:ty),*) -> $r:ty) => {{
        #[cfg(target_arch = "x86_64")]
        if $k.hw {
            #[target_feature(enable = "pclmulqdq")]
            unsafe fn hw(k: &Gf2Field, $($a: $t),*) -> $r {
                k.$f::<Hw>($($a),*)
            }
            return unsafe { hw($k, $($a),*) };
        }
        #[cfg(target_arch = "aarch64")]
        if $k.hw {
            #[target_feature(enable = "aes")]
            unsafe fn hw(k: &Gf2Field, $($a: $t),*) -> $r {
                k.$f::<Hw>($($a),*)
            }
            return unsafe { hw($k, $($a),*) };
        }
        $k.$f::<Soft>($($a),*)
    }};
}

impl Gf2Field {
    /// The ring for f = x^n + g (g as bits, of degree below n).
    pub fn new(n: u32, g: u64) -> Gf2Field {
        assert!((1..=64).contains(&n) && (n == 64 || g >> n == 0), "a modulus of degree 1 to 64");
        // floor(x^(2n) / f) = x^n + floor(x^n g / f).
        let f = 1u128 << n | g as u128;
        let mut r = (g as u128) << n;
        let mut mu = 0u64;
        while r != 0 && 127 - r.leading_zeros() >= n {
            let s = 127 - r.leading_zeros() - n;
            r ^= f << s;
            mu |= 1 << s;
        }
        Gf2Field { n, g, mu, hw: has_clmul() }
    }

    pub fn degree(&self) -> u32 {
        self.n
    }

    /// The terms of the modulus below x^n, as bits.
    pub fn modulus_low(&self) -> u64 {
        self.g
    }

    /// p mod f, for p of degree below 2n - 1.
    #[inline(always)]
    fn reduce<C: Clmul>(&self, p: u128) -> u64 {
        let a = (p >> self.n) as u64;
        let (tl, th) = C::mul(a, self.mu);
        let q = a ^ (((th as u128) << 64 | tl as u128) >> self.n) as u64;
        let (rl, rh) = C::mul(q, self.g);
        (p ^ (q as u128) << self.n ^ ((rh as u128) << 64 | rl as u128)) as u64
    }

    #[inline(always)]
    fn mul_with<C: Clmul>(&self, a: u64, b: u64) -> u64 {
        let (lo, hi) = C::mul(a, b);
        self.reduce::<C>((hi as u128) << 64 | lo as u128)
    }

    #[inline(always)]
    fn pow_with<C: Clmul>(&self, a: u64, e: u64) -> u64 {
        let mut r = 1u64;
        for i in (0..64 - e.leading_zeros()).rev() {
            let (lo, hi) = C::sqr(r);
            r = self.reduce::<C>((hi as u128) << 64 | lo as u128);
            if e >> i & 1 == 1 {
                r = self.mul_with::<C>(r, a);
            }
        }
        r
    }

    /// a*b.
    pub fn mul(&self, a: u64, b: u64) -> u64 {
        field_dispatch!(self.mul_with(a: u64, b: u64) -> u64)
    }

    /// a^e.
    pub fn pow(&self, a: u64, e: u64) -> u64 {
        field_dispatch!(self.pow_with(a: u64, e: u64) -> u64)
    }

    /// The inverse of a non-zero element of a field: a^(2^n - 2).
    pub fn inv(&self, a: u64) -> u64 {
        self.pow(a, (u64::MAX >> (64 - self.n)) - 1)
    }
}

/// GF(2)[x]/(f) for f of degree n with 64(W - 1) < n <= 64W and W from 1 to
/// 8 (GF(2^n) when f is irreducible): elements are W words of bits.
/// Products are reduced by Barrett's method as in `Gf2Field`, and inverses
/// found by the extended Euclidean algorithm on shifts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gf2Words<const W: usize> {
    n: u32,
    /// f - x^n and floor(x^(2n) / f) - x^n, both of degree below n; g lies
    /// in its first gw words.
    g: [u64; W],
    mu: [u64; W],
    gw: usize,
    hw: bool,
}

/// `$k.$f::<Hw>(args)` for a `Gf2Words`, as `field_dispatch` does for a
/// `Gf2Field`.
macro_rules! words_dispatch {
    ($k:ident.$f:ident($($a:ident: $t:ty),*) -> $r:ty) => {{
        #[cfg(target_arch = "x86_64")]
        if $k.hw {
            #[target_feature(enable = "pclmulqdq")]
            unsafe fn hw<const W: usize>(k: &Gf2Words<W>, $($a: $t),*) -> $r {
                k.$f::<Hw>($($a),*)
            }
            return unsafe { hw($k, $($a),*) };
        }
        #[cfg(target_arch = "aarch64")]
        if $k.hw {
            #[target_feature(enable = "aes")]
            unsafe fn hw<const W: usize>(k: &Gf2Words<W>, $($a: $t),*) -> $r {
                k.$f::<Hw>($($a),*)
            }
            return unsafe { hw($k, $($a),*) };
        }
        $k.$f::<Soft>($($a),*)
    }};
}

/// Words for a product of two elements of `Gf2Words` (2W), and one more
/// read by the shifts.
const PRODUCT: usize = 17;

impl<const W: usize> Gf2Words<W> {
    /// The ring for f = x^n + g, with g given by its words (of degree below
    /// n).
    pub fn new(n: u32, g: &[u64]) -> Gf2Words<W> {
        let nu = n as usize;
        assert!((1..=8).contains(&W) && nu > 64 * (W - 1) && nu <= 64 * W && g.len() <= W, "a modulus of degree 64(W - 1) + 1 to 64W");
        let mut gs = [0u64; W];
        gs[..g.len()].copy_from_slice(g);
        assert!(nu == 64 * W || gs[W - 1] >> (nu % 64) == 0, "g of degree below n");
        // floor(x^(2n) / f) = x^n + floor(x^n g / f), by long division.
        let mut r = vec![0u64; 2 * W + 1];
        xor_shl(&mut r, &gs, nu);
        let mut mu = [0u64; W];
        for i in (nu..2 * nu).rev() {
            if r[i / 64] >> (i % 64) & 1 == 1 {
                r[i / 64] ^= 1 << (i % 64);
                xor_shl(&mut r, &gs, i - nu);
                mu[(i - nu) / 64] |= 1 << ((i - nu) % 64);
            }
        }
        let gw = gs.iter().rposition(|&x| x != 0).map_or(0, |i| i + 1);
        Gf2Words { n, g: gs, mu, gw, hw: has_clmul() }
    }

    pub fn degree(&self) -> u32 {
        self.n
    }

    /// The terms of the modulus below x^n, as bits.
    pub fn modulus_low(&self) -> &[u64; W] {
        &self.g
    }

    /// p mod f, for p of degree below 2n - 1.
    #[inline(always)]
    fn reduce<C: Clmul>(&self, p: &[u64; PRODUCT]) -> [u64; W] {
        let (s, b) = (self.n as usize / 64, self.n % 64);
        let shr = |t: &[u64; PRODUCT], i: usize| if b == 0 { t[i + s] } else { t[i + s] >> b | t[i + s + 1] << (64 - b) };
        // a = floor(p / x^n), and the quotient q = a + floor(a mu / x^n).
        let mut a = [0u64; W];
        for (i, x) in a.iter_mut().enumerate() {
            *x = shr(p, i);
        }
        let mut t = [0u64; PRODUCT];
        for i in 0..W {
            for j in 0..W {
                let (lo, hi) = C::mul(a[i], self.mu[j]);
                t[i + j] ^= lo;
                t[i + j + 1] ^= hi;
            }
        }
        let (mut q, mut r) = (a, [0u64; W]);
        for i in 0..W {
            q[i] ^= shr(&t, i);
            r[i] = p[i];
        }
        // p - q f = p + q g modulo x^n.
        for j in 0..self.gw {
            for i in 0..W - j {
                let (lo, hi) = C::mul(q[i], self.g[j]);
                r[i + j] ^= lo;
                if i + j + 1 < W {
                    r[i + j + 1] ^= hi;
                }
            }
        }
        if b != 0 {
            r[W - 1] &= (1 << b) - 1;
        }
        r
    }

    #[inline(always)]
    fn mul_with<C: Clmul>(&self, a: &[u64; W], b: &[u64; W]) -> [u64; W] {
        let mut p = [0u64; PRODUCT];
        for i in 0..W {
            for j in 0..W {
                let (lo, hi) = C::mul(a[i], b[j]);
                p[i + j] ^= lo;
                p[i + j + 1] ^= hi;
            }
        }
        self.reduce::<C>(&p)
    }

    #[inline(always)]
    fn sqr_with<C: Clmul>(&self, a: &[u64; W]) -> [u64; W] {
        let mut p = [0u64; PRODUCT];
        for i in 0..W {
            (p[2 * i], p[2 * i + 1]) = C::sqr(a[i]);
        }
        self.reduce::<C>(&p)
    }

    #[inline(always)]
    fn pow_with<C: Clmul>(&self, a: &[u64; W], e: &[u64]) -> [u64; W] {
        let Some(top) = e.iter().rposition(|&x| x != 0) else {
            let mut one = [0u64; W];
            one[0] = 1;
            return one;
        };
        let mut r = *a;
        for i in (0..64 * top + 63 - e[top].leading_zeros() as usize).rev() {
            r = self.sqr_with::<C>(&r);
            if e[i / 64] >> (i % 64) & 1 == 1 {
                r = self.mul_with::<C>(&r, a);
            }
        }
        r
    }

    #[inline(always)]
    fn sqr_n_with<C: Clmul>(&self, a: &[u64; W], k: u64) -> [u64; W] {
        let mut r = *a;
        for _ in 0..k {
            r = self.sqr_with::<C>(&r);
        }
        r
    }

    #[inline(always)]
    fn trace_with<C: Clmul>(&self, a: &[u64; W]) -> u64 {
        let (mut t, mut s) = (*a, *a);
        for _ in 1..self.n {
            t = self.sqr_with::<C>(&t);
            for i in 0..W {
                s[i] ^= t[i];
            }
        }
        s[0] & 1
    }

    /// a*b.
    pub fn mul(&self, a: &[u64; W], b: &[u64; W]) -> [u64; W] {
        words_dispatch!(self.mul_with(a: &[u64; W], b: &[u64; W]) -> [u64; W])
    }

    /// a^2.
    pub fn sqr(&self, a: &[u64; W]) -> [u64; W] {
        words_dispatch!(self.sqr_with(a: &[u64; W]) -> [u64; W])
    }

    /// The element c_0 + c_1 x + ... modulo f, for at most 2n - 1 bits c_i
    /// (a product, as Kronecker substitution finds it).
    pub fn reduce_coeffs(&self, c: &[u64]) -> [u64; W] {
        let mut bits = [0u64; PRODUCT];
        for (i, &x) in c.iter().enumerate() {
            bits[i / 64] |= (x & 1) << (i % 64);
        }
        let p = &bits;
        words_dispatch!(self.reduce(p: &[u64; PRODUCT]) -> [u64; W])
    }

    /// a^e for the exponent with the given words (least significant first).
    pub fn pow(&self, a: &[u64; W], e: &[u64]) -> [u64; W] {
        words_dispatch!(self.pow_with(a: &[u64; W], e: &[u64]) -> [u64; W])
    }

    /// a^(2^k).
    pub fn sqr_n(&self, a: &[u64; W], k: u64) -> [u64; W] {
        words_dispatch!(self.sqr_n_with(a: &[u64; W], k: u64) -> [u64; W])
    }

    /// The absolute trace, the sum of the a^(2^i) for i below n (in a
    /// field, 0 or 1).
    pub fn trace(&self, a: &[u64; W]) -> u64 {
        words_dispatch!(self.trace_with(a: &[u64; W]) -> u64)
    }

    /// The inverse of a, if it is a unit. The extended Euclidean algorithm
    /// on shifts keeps u = g1 a and v = g2 a modulo f, from (a, f) until u =
    /// 1; the degrees of g1 and g2 stay at most n, so W + 1 words hold them.
    pub fn inv(&self, a: &[u64; W]) -> Option<[u64; W]> {
        let n = self.n as usize;
        let (mut u, mut v, mut g1, mut g2) = ([0u64; 9], [0u64; 9], [0u64; 9], [0u64; 9]);
        u[..W].copy_from_slice(a);
        v[..W].copy_from_slice(&self.g);
        v[n / 64] |= 1 << (n % 64);
        g1[0] = 1;
        let (mut du, mut dv) = (degree(&u[..=W], n)?, n);
        while du > 0 {
            if du < dv {
                std::mem::swap(&mut u, &mut v);
                std::mem::swap(&mut g1, &mut g2);
                std::mem::swap(&mut du, &mut dv);
            }
            xor_shl_within(&mut u, &v, du - dv, W + 1);
            xor_shl_within(&mut g1, &g2, du - dv, W + 1);
            du = degree(&u[..=W], du)?;
        }
        if g1[n / 64] >> (n % 64) & 1 == 1 {
            g1[n / 64] ^= 1 << (n % 64);
            for i in 0..W {
                g1[i] ^= self.g[i];
            }
        }
        let mut r = [0u64; W];
        r.copy_from_slice(&g1[..W]);
        Some(r)
    }
}

/// dst ^= src * x^e over the first w words, dropping what goes past them.
#[inline(always)]
fn xor_shl_within(dst: &mut [u64; 9], src: &[u64; 9], e: usize, w: usize) {
    let (ws, bs) = (e / 64, e % 64);
    for i in (ws..w).rev() {
        let hi = if bs > 0 && i > ws { src[i - ws - 1] >> (64 - bs) } else { 0 };
        dst[i] ^= src[i - ws] << bs | hi;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn products_agree() {
        let mut seed = 0x1234_5678_9abc_def0u64;
        for _ in 0..1000 {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let a = seed;
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let b = seed;
            let naive = (0..64).filter(|i| b >> i & 1 == 1).fold(0u128, |r, i| r ^ (a as u128) << i);
            assert_eq!(Soft::mul(a, b), (naive as u64, (naive >> 64) as u64));
            let sq = (0..64).filter(|i| a >> i & 1 == 1).fold(0u128, |r, i| r ^ 1u128 << (2 * i));
            assert_eq!(Soft::sqr(a), (sq as u64, (sq >> 64) as u64));
            #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
            assert_eq!(Hw::mul(a, b), Soft::mul(a, b));
        }
    }

    /// Irreducibility by trial division by every polynomial of degree at
    /// most n/2, for n below 32.
    fn irreducible_naive(f: u64) -> bool {
        let n = 63 - f.leading_zeros();
        n >= 1 && (2u64..1 << (n / 2 + 1)).all(|h| rem_small(f, h) != 0)
    }

    #[test]
    fn ben_or_agrees_with_trial_division() {
        for n in 1..=14usize {
            for g in 0u64..1 << n {
                let low: Vec<usize> = (0..n).filter(|i| g >> i & 1 == 1).collect();
                let f = 1 << n | g;
                assert_eq!(is_irreducible_with::<Soft>(n, &low), irreducible_naive(f), "{f:b}");
                assert_eq!(is_irreducible_sparse(n, &low), irreducible_naive(f), "{f:b}");
            }
        }
    }

    #[test]
    fn low_terms_agree_with_the_naive_search() {
        for n in 1..=200usize {
            let naive = (1u64..).find(|&g| is_irreducible_with::<Soft>(n, &(0..64).filter(|i| g >> i & 1 == 1).collect::<Vec<_>>()));
            assert_eq!(least_low_term(n), naive, "{n}");
            assert_eq!(least_low_term_with::<Soft>(n), naive, "{n}");
        }
    }

    /// FLINT's test of x^n + g over GF(2).
    fn flint_irreducible(n: usize, low: &[usize]) -> bool {
        let mut cs = vec![crate::Integer::zero(); n + 1];
        for &e in low.iter().chain([n].iter()) {
            cs[e] = crate::Integer::one();
        }
        crate::gr::is_irreducible_mod_p(&crate::Integer::from_u64(2), &cs)
    }

    fn bits(g: u64) -> Vec<usize> {
        (0..64).filter(|i| g >> i & 1 == 1).collect()
    }

    #[test]
    fn large_degrees_agree_with_flint() {
        // Every candidate up to the least one, past Ben-Or's steps.
        for n in [129usize, 150, 200, 255, 256, 300, 311, 400, 509] {
            let g0 = least_low_term(n).unwrap();
            for g in (1..=g0).step_by(2) {
                assert_eq!(is_irreducible_sparse(n, &bits(g)), flint_irreducible(n, &bits(g)), "{n} {g}");
            }
            assert!(flint_irreducible(n, &bits(g0)));
        }
    }

    /// a*b mod f by shifts, for f = x^n + g.
    fn mulmod_naive(a: u64, b: u64, n: u32, g: u64) -> u64 {
        let mut p = 0u128;
        for i in 0..64 {
            if b >> i & 1 == 1 {
                p ^= (a as u128) << i;
            }
        }
        let f = 1u128 << n | g as u128;
        for i in (n..128).rev() {
            if p >> i & 1 == 1 {
                p ^= f << (i - n);
            }
        }
        p as u64
    }

    #[test]
    fn field_products_agree() {
        let mut seed = 0x0123_4567_89ab_cdefu64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            seed
        };
        for n in 1..=64u32 {
            let mask = u64::MAX >> (64 - n);
            let g = next() & mask >> 1 | 1;
            let k = Gf2Field::new(n, g);
            let soft = Gf2Field { hw: false, ..k };
            for _ in 0..200 {
                let (a, b) = (next() & mask, next() & mask);
                let want = mulmod_naive(a, b, n, g);
                assert_eq!(k.mul(a, b), want, "{n} {g:x} {a:x} {b:x}");
                assert_eq!(soft.mul(a, b), want);
            }
        }
        // GF(2^64) with x^64 + x^4 + x^3 + x + 1: inverses and Fermat.
        let k = Gf2Field::new(64, 0b11011);
        for a in [1u64, 2, 3, 0xdead_beef, u64::MAX] {
            assert_eq!(k.mul(a, k.inv(a)), 1);
            assert_eq!(k.pow(a, u64::MAX), 1);
        }
        let k = Gf2Field::new(40, least_low_term(40).unwrap());
        assert_eq!(k.pow(2, (1 << 40) - 1), 1);
    }

    #[test]
    fn sparse_moduli_with_high_terms() {
        // x^127 + x + 1 and x^127 + x^63 + 1 are primitive trinomials, and
        // x^127 + x^64 + 1 is the reverse of the second.
        assert!(is_irreducible_sparse(127, &[1, 0]));
        assert!(is_irreducible_sparse(127, &[63, 0]));
        assert!(is_irreducible_sparse(127, &[64, 0]));
        assert!(!is_irreducible_sparse(127, &[2, 0]));
        // A polynomial and its reverse, with terms above and below x^64.
        for (n, low) in [(128usize, vec![127usize, 0]), (130, vec![100, 3, 0]), (200, vec![150, 77, 1, 0])] {
            let words: Vec<usize> = low.iter().map(|&e| n - e).filter(|&e| e < n).chain([0]).collect();
            assert_eq!(is_irreducible_sparse(n, &low), is_irreducible_sparse(n, &words), "{n} {low:?}");
        }
    }

    struct Lcg(u64);

    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            self.0 ^ self.0 >> 29
        }

        /// A polynomial of degree below n, in w words.
        fn below(&mut self, n: usize, w: usize) -> Vec<u64> {
            (0..w).map(|i| if 64 * (i + 1) <= n { self.next() } else if 64 * i < n { self.next() & ((1 << (n % 64)) - 1) } else { 0 }).collect()
        }
    }

    /// a*b mod f by shifts, for f = x^n + g.
    fn mulmod_words_naive(a: &[u64], b: &[u64], n: usize, g: &[u64]) -> Vec<u64> {
        let w = n.div_ceil(64);
        let mut p = vec![0u64; 2 * w + 1];
        for i in 0..64 * w {
            if b[i / 64] >> (i % 64) & 1 == 1 {
                xor_shl(&mut p, a, i);
            }
        }
        for i in (n..2 * n).rev() {
            if p[i / 64] >> (i % 64) & 1 == 1 {
                p[i / 64] ^= 1 << (i % 64);
                xor_shl(&mut p, g, i - n);
            }
        }
        p.truncate(w);
        p
    }

    /// Products against the naive ones, with and without the processor's
    /// instruction; and, when f is irreducible, inverses, Fermat's little
    /// theorem, the Frobenius map and traces.
    fn words_agree<const W: usize>(n: usize, g: &[u64], rng: &mut Lcg) {
        let g = &(0..W).map(|i| g.get(i).copied().unwrap_or(0)).collect::<Vec<_>>();
        let k = Gf2Words::<W>::new(n as u32, g);
        let soft = Gf2Words { hw: false, ..k.clone() };
        let field = flint_irreducible(n, &(0..n).filter(|&i| g[i / 64] >> (i % 64) & 1 == 1).collect::<Vec<_>>());
        let mut one = [0u64; W];
        one[0] = 1;
        let qm1: Vec<u64> = (0..W).map(|i| if 64 * (i + 1) <= n { u64::MAX } else { (1 << (n % 64)) - 1 }).collect();
        for _ in 0..40 {
            let a: [u64; W] = rng.below(n, W).try_into().unwrap();
            let b: [u64; W] = rng.below(n, W).try_into().unwrap();
            let want = mulmod_words_naive(&a, &b, n, g);
            assert_eq!(k.mul(&a, &b).to_vec(), want, "{n} {g:x?}");
            assert_eq!(soft.mul(&a, &b).to_vec(), want);
            assert_eq!(k.sqr(&a), k.mul(&a, &a));
            assert_eq!(soft.sqr(&a), k.sqr(&a));
            assert_eq!(k.pow(&a, &[5]), k.mul(&k.sqr(&k.sqr(&a)), &a));
            if field && a != [0; W] {
                let i = k.inv(&a).unwrap();
                assert_eq!(k.mul(&a, &i), one, "{n} {a:x?}");
                assert_eq!(k.pow(&a, &qm1), one);
                assert_eq!(k.sqr_n(&a, n as u64), a);
                let t = (1..n as u64).fold(a, |s, j| {
                    let c = k.sqr_n(&a, j);
                    std::array::from_fn(|i| s[i] ^ c[i])
                });
                assert!(t == [0; W] || t == one);
                assert_eq!(k.trace(&a), t[0]);
            }
        }
        if field {
            assert_eq!(k.inv(&[0; W]), None);
        }
    }

    /// x^n + g irreducible with g of degree n - 1 and many terms.
    fn dense_irreducible(n: usize, rng: &mut Lcg) -> Vec<u64> {
        for _ in 0..20 * n {
            let mut g = rng.below(n, n.div_ceil(64));
            g[0] |= 1;
            g[(n - 1) / 64] |= 1 << ((n - 1) % 64);
            if flint_irreducible(n, &(0..n).filter(|&i| g[i / 64] >> (i % 64) & 1 == 1).collect::<Vec<_>>()) {
                return g;
            }
        }
        panic!("no irreducible of degree {n}");
    }

    #[test]
    fn word_fields_agree() {
        let mut rng = Lcg(0x5eed_0f_f1e1d5);
        macro_rules! check {
            ($w:literal: $($n:expr),*) => {
                for n in [$($n),*] {
                    let sparse = [least_low_term(n).unwrap()];
                    words_agree::<$w>(n, &sparse, &mut rng);
                    let dense = dense_irreducible(n, &mut rng);
                    words_agree::<$w>(n, &dense, &mut rng);
                    // Reducible: products only.
                    let any = rng.below(n, $w);
                    words_agree::<$w>(n, &any, &mut rng);
                }
            };
        }
        check!(1: 2, 3, 31, 63, 64);
        check!(2: 65, 100, 127, 128);
        check!(3: 129, 150, 192);
        check!(4: 193, 256);
        check!(5: 300);
        check!(6: 333);
        check!(7: 400);
        check!(8: 449, 512);
    }
}
