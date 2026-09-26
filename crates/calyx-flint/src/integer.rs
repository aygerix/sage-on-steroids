use std::cmp::Ordering;
use std::ffi::CString;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops;

use flint3_sys as sys;

/// An arbitrary-precision integer backed by FLINT's `fmpz`.
///
/// Small values are stored inline in the machine word, so cloning and
/// arithmetic on small integers never allocates.
pub struct Integer {
    raw: sys::fmpz,
}

/// The factorization of a nonzero integer: `sign * prod p_i^e_i`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Factorization {
    pub sign: i32,
    pub factors: Vec<(Integer, u64)>,
}

impl Integer {
    /// Pointer to the underlying FLINT value (for other wrappers in this crate).
    pub(crate) fn raw_ptr(&self) -> *const sys::fmpz {
        &self.raw
    }

    pub(crate) fn raw_mut_ptr(&mut self) -> *mut sys::fmpz {
        &mut self.raw
    }

    #[inline]
    pub const fn zero() -> Self {
        Integer { raw: 0 }
    }

    #[inline]
    pub fn one() -> Self {
        Integer::from_i64(1)
    }

    #[inline]
    pub fn from_i64(v: i64) -> Self {
        if v.unsigned_abs() <= COEFF_MAX {
            return Integer { raw: v as sys::fmpz };
        }
        let mut z = Integer::zero();
        unsafe { sys::fmpz_set_si(&mut z.raw, v as sys::slong) };
        z
    }

    #[inline]
    pub fn from_u64(v: u64) -> Self {
        if v <= COEFF_MAX {
            return Integer { raw: v as sys::fmpz };
        }
        let mut z = Integer::zero();
        unsafe { sys::fmpz_set_ui(&mut z.raw, v as sys::ulong) };
        z
    }

    pub fn from_i128(v: i128) -> Self {
        let neg = v < 0;
        let m = v.unsigned_abs();
        let limbs = [m as u64, (m >> 64) as u64];
        Integer::from_limbs(&limbs, neg)
    }

    /// Build an integer from little-endian 64-bit limbs of its absolute value.
    pub fn from_limbs(limbs: &[u64], negative: bool) -> Self {
        let mut z = Integer::zero();
        if !limbs.is_empty() {
            let v: Vec<sys::ulong> = limbs.iter().map(|&l| l as sys::ulong).collect();
            unsafe { sys::fmpz_set_ui_array(&mut z.raw, v.as_ptr(), v.len() as sys::slong) };
        }
        if negative {
            z.neg_assign();
        }
        z
    }

    /// Little-endian 64-bit limbs of the absolute value (empty for zero).
    pub fn to_limbs(&self) -> Vec<u64> {
        if self.is_zero() {
            return Vec::new();
        }
        let a = self.abs();
        let n = a.bits().div_ceil(64) as usize;
        let mut out: Vec<sys::ulong> = vec![0; n];
        unsafe { sys::fmpz_get_ui_array(out.as_mut_ptr(), n as sys::slong, &a.raw) };
        out.into_iter().map(|l| l as u64).collect()
    }

    /// Parse an integer in the given radix (2..=36). Accepts a leading `-`.
    pub fn parse_radix(s: &str, radix: u32) -> Option<Self> {
        let t = s.trim();
        if t.is_empty() || !(2..=36).contains(&radix) {
            return None;
        }
        let (neg, digits) = match t.as_bytes()[0] {
            b'-' => (true, &t[1..]),
            b'+' => (false, &t[1..]),
            _ => (false, t),
        };
        if digits.is_empty() || !digits.chars().all(|c| c.is_digit(radix)) {
            return None;
        }
        let c = CString::new(digits).ok()?;
        let mut z = Integer::zero();
        let rc = unsafe { sys::fmpz_set_str(&mut z.raw, c.as_ptr(), radix as i32) };
        if rc != 0 {
            return None;
        }
        if neg {
            z.neg_assign();
        }
        Some(z)
    }

    pub fn parse(s: &str) -> Option<Self> {
        Integer::parse_radix(s, 10)
    }

    pub fn to_string_radix(&self, radix: u32) -> String {
        assert!((2..=36).contains(&radix));
        if let Some(v) = self.to_i64() {
            if radix == 10 {
                return v.to_string();
            }
        }
        unsafe { crate::take_flint_string(sys::fmpz_get_str(std::ptr::null_mut(), radix as i32, &self.raw)) }
    }

    #[inline]
    pub fn as_raw(&self) -> *const sys::fmpz {
        &self.raw
    }

    #[inline]
    pub fn as_raw_mut(&mut self) -> *mut sys::fmpz {
        &mut self.raw
    }

    #[inline]
    pub fn to_i64(&self) -> Option<i64> {
        if let Some(v) = self.to_i64_fast() {
            return Some(v);
        }
        if unsafe { sys::fmpz_fits_si(&self.raw) } != 0 {
            Some(unsafe { sys::fmpz_get_si(&self.raw) } as i64)
        } else {
            None
        }
    }

    pub fn to_u64(&self) -> Option<u64> {
        if let Some(v) = self.to_i64_fast() {
            return (v >= 0).then_some(v as u64);
        }
        if self.sign() >= 0 && unsafe { sys::fmpz_abs_fits_ui(&self.raw) } != 0 {
            Some(unsafe { sys::fmpz_get_ui(&self.raw) } as u64)
        } else {
            None
        }
    }

    pub fn to_i128(&self) -> Option<i128> {
        if self.bits() > 127 {
            return None;
        }
        let limbs = self.to_limbs();
        let mut m: u128 = 0;
        for (i, l) in limbs.iter().enumerate() {
            m |= (*l as u128) << (64 * i);
        }
        let v = m as i128;
        Some(if self.sign() < 0 { -v } else { v })
    }

    pub fn to_f64(&self) -> f64 {
        unsafe { sys::fmpz_get_d(&self.raw) }
    }

    /// Returns the integer nearest to `d` (truncating toward zero), or `None`
    /// if `d` is not finite.
    pub fn from_f64(d: f64) -> Option<Self> {
        if !d.is_finite() {
            return None;
        }
        let mut z = Integer::zero();
        unsafe { sys::fmpz_set_d(&mut z.raw, d.trunc()) };
        Some(z)
    }

    #[inline]
    pub fn sign(&self) -> i32 {
        match self.to_i64_fast() {
            Some(v) => v.signum() as i32,
            None => unsafe { sys::fmpz_sgn(&self.raw) },
        }
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        self.raw == 0
    }

    #[inline]
    pub fn is_one(&self) -> bool {
        self.raw == 1
    }

    pub fn is_even(&self) -> bool {
        unsafe { sys::fmpz_is_even(&self.raw) != 0 }
    }

    pub fn is_odd(&self) -> bool {
        !self.is_even()
    }

    /// Number of bits in the absolute value (0 for zero).
    pub fn bits(&self) -> u64 {
        unsafe { sys::fmpz_bits(&self.raw) as u64 }
    }

    pub fn abs(&self) -> Self {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_abs(&mut z.raw, &self.raw) };
        z
    }

    pub fn neg_assign(&mut self) {
        unsafe { sys::fmpz_neg(&mut self.raw, &self.raw) };
    }

    pub fn cmp_abs(&self, other: &Integer) -> Ordering {
        unsafe { sys::fmpz_cmpabs(&self.raw, &other.raw) }.cmp(&0)
    }

    pub fn pow(&self, exp: u64) -> Self {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_pow_ui(&mut z.raw, &self.raw, exp as sys::ulong) };
        z
    }

    /// Euclidean division: `self = q*d + r` with `0 <= r < |d|`.
    /// Returns `None` if `d` is zero.
    pub fn div_rem_euclid(&self, d: &Integer) -> Option<(Integer, Integer)> {
        if d.is_zero() {
            return None;
        }
        let mut q = Integer::zero();
        let mut r = Integer::zero();
        unsafe { sys::fmpz_fdiv_qr(&mut q.raw, &mut r.raw, &self.raw, &d.raw) };
        // Floor division gives r with the sign of d; fix up for negative d.
        if r.sign() < 0 {
            r = &r - d;
            q = &q + &Integer::one();
        }
        Some((q, r))
    }

    /// Floor division `(q, r)` with `r` having the sign of `d`.
    pub fn fdiv_qr(&self, d: &Integer) -> Option<(Integer, Integer)> {
        if d.is_zero() {
            return None;
        }
        if let Some((a, b)) = self.both_small(d) {
            let (mut q, mut r) = (a / b, a % b);
            if r != 0 && (r < 0) != (b < 0) {
                q -= 1;
                r += b;
            }
            return Some((Integer::from_i64(q), Integer::from_i64(r)));
        }
        let mut q = Integer::zero();
        let mut r = Integer::zero();
        unsafe { sys::fmpz_fdiv_qr(&mut q.raw, &mut r.raw, &self.raw, &d.raw) };
        Some((q, r))
    }

    /// Truncating division `(q, r)` with `r` having the sign of `self`.
    pub fn tdiv_qr(&self, d: &Integer) -> Option<(Integer, Integer)> {
        if d.is_zero() {
            return None;
        }
        let mut q = Integer::zero();
        let mut r = Integer::zero();
        unsafe { sys::fmpz_tdiv_qr(&mut q.raw, &mut r.raw, &self.raw, &d.raw) };
        Some((q, r))
    }

    pub fn cdiv_q(&self, d: &Integer) -> Option<Integer> {
        if d.is_zero() {
            return None;
        }
        let mut q = Integer::zero();
        unsafe { sys::fmpz_cdiv_q(&mut q.raw, &self.raw, &d.raw) };
        Some(q)
    }

    /// Exact division; the caller guarantees `d` divides `self`.
    pub fn divexact(&self, d: &Integer) -> Integer {
        assert!(!d.is_zero(), "divexact by zero");
        let mut q = Integer::zero();
        unsafe { sys::fmpz_divexact(&mut q.raw, &self.raw, &d.raw) };
        q
    }

    /// Whether `d` divides `self` (0 divides only 0).
    pub fn is_divisible_by(&self, d: &Integer) -> bool {
        if d.is_zero() {
            return self.is_zero();
        }
        unsafe { sys::fmpz_divisible(&self.raw, &d.raw) != 0 }
    }

    pub fn gcd(&self, other: &Integer) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_gcd(&mut z.raw, &self.raw, &other.raw) };
        z
    }

    pub fn lcm(&self, other: &Integer) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_lcm(&mut z.raw, &self.raw, &other.raw) };
        z
    }

    /// Extended gcd: returns `(g, s, t)` with `g = s*self + t*other`, `g >= 0`.
    pub fn xgcd(&self, other: &Integer) -> (Integer, Integer, Integer) {
        let mut g = Integer::zero();
        let mut s = Integer::zero();
        let mut t = Integer::zero();
        unsafe { sys::fmpz_xgcd_canonical_bezout(&mut g.raw, &mut s.raw, &mut t.raw, &self.raw, &other.raw) };
        (g, s, t)
    }

    /// `self^e mod m` for `m > 0`. Negative exponents require an inverse.
    pub fn powm(&self, e: &Integer, m: &Integer) -> Option<Integer> {
        if m.sign() <= 0 {
            return None;
        }
        if e.sign() < 0 {
            let inv = self.invmod(m)?;
            return inv.powm(&e.abs(), m);
        }
        let mut z = Integer::zero();
        unsafe { sys::fmpz_powm(&mut z.raw, &self.raw, &e.raw, &m.raw) };
        Some(z)
    }

    /// Inverse of `self` modulo `m`, in `[0, |m|)`, if it exists.
    pub fn invmod(&self, m: &Integer) -> Option<Integer> {
        if m.is_zero() {
            return None;
        }
        let m = m.abs();
        if m.is_one() {
            return Some(Integer::zero());
        }
        let mut z = Integer::zero();
        let ok = unsafe { sys::fmpz_invmod(&mut z.raw, &self.raw, &m.raw) };
        if ok != 0 { Some(z) } else { None }
    }

    /// Kronecker symbol `(self / n)`.
    pub fn kronecker(&self, n: &Integer) -> i32 {
        unsafe { sys::fmpz_kronecker(&self.raw, &n.raw) }
    }

    /// Proven primality. Negative numbers are prime if their absolute value is.
    pub fn is_prime(&self) -> bool {
        let a = self.abs();
        if a.bits() < 2 {
            return false;
        }
        unsafe { sys::fmpz_is_prime(&a.raw) == 1 }
    }

    /// Probable primality (BPSW); no known counterexamples.
    pub fn is_probable_prime(&self) -> bool {
        let a = self.abs();
        if a.bits() < 2 {
            return false;
        }
        unsafe { sys::fmpz_is_probabprime(&a.raw) != 0 }
    }

    /// The smallest (proven) prime strictly greater than `self`.
    pub fn next_prime(&self) -> Integer {
        if self.to_i64().is_some_and(|v| v < 2) {
            return Integer::from_i64(2);
        }
        let mut z = Integer::zero();
        unsafe { sys::fmpz_nextprime(&mut z.raw, &self.raw, 1) };
        z
    }

    /// The largest prime strictly less than `self`, if any.
    pub fn previous_prime(&self) -> Option<Integer> {
        if self.to_i64().is_some_and(|v| v <= 2) {
            return None;
        }
        if self.to_i64() == Some(3) {
            return Some(Integer::from_i64(2));
        }
        let two = Integer::from_i64(2);
        let mut c = self - &Integer::one();
        if c.is_even() {
            c = &c - &Integer::one();
        }
        loop {
            if c.is_prime() {
                return Some(c);
            }
            c = &c - &two;
        }
    }

    /// Factorization of a nonzero integer. Returns `None` for zero.
    pub fn factor(&self) -> Option<Factorization> {
        if self.is_zero() {
            return None;
        }
        unsafe {
            let mut f: sys::fmpz_factor_struct = std::mem::zeroed();
            sys::fmpz_factor_init(&mut f);
            sys::fmpz_factor(&mut f, &self.raw);
            let mut factors = Vec::with_capacity(f.num as usize);
            for i in 0..f.num as usize {
                let mut p = Integer::zero();
                sys::fmpz_set(&mut p.raw, f.p.add(i));
                factors.push((p, *f.exp.add(i) as u64));
            }
            let sign = f.sign;
            sys::fmpz_factor_clear(&mut f);
            // FLINT may list a prime more than once (p^2 and p from
            // different splits), so equal primes are merged.
            factors.sort_by(|a, b| a.0.cmp(&b.0));
            factors.dedup_by(|b, a| {
                let same = a.0 == b.0;
                if same {
                    a.1 += b.1;
                }
                same
            });
            Some(Factorization { sign, factors })
        }
    }

    /// Floor of the square root; `None` for negative input.
    pub fn isqrt(&self) -> Option<Integer> {
        if self.sign() < 0 {
            return None;
        }
        let mut z = Integer::zero();
        unsafe { sys::fmpz_sqrt(&mut z.raw, &self.raw) };
        Some(z)
    }

    pub fn is_square(&self) -> bool {
        unsafe { sys::fmpz_is_square(&self.raw) != 0 }
    }

    /// Truncated `n`-th root and whether it is exact. `None` if no real root.
    pub fn root(&self, n: u64) -> Option<(Integer, bool)> {
        if n == 0 || (self.sign() < 0 && n % 2 == 0) {
            return None;
        }
        let mut z = Integer::zero();
        let exact = unsafe { sys::fmpz_root(&mut z.raw, &self.raw, n as sys::slong) };
        Some((z, exact != 0))
    }

    /// Returns `(b, e)` with `self = b^e` and `e > 1` maximal, if such exist.
    pub fn perfect_power(&self) -> Option<(Integer, u64)> {
        let mut b = Integer::zero();
        let e = unsafe { sys::fmpz_is_perfect_power(&mut b.raw, &self.raw) };
        if e <= 1 {
            return None;
        }
        // FLINT's root may itself be a power: 2^1001 comes as (2^143)^7.
        let mut e = e as u64;
        while b.cmp_abs(&Integer::one()) == Ordering::Greater {
            let mut r = Integer::zero();
            let k = unsafe { sys::fmpz_is_perfect_power(&mut r.raw, &b.raw) };
            if k <= 1 {
                break;
            }
            (b, e) = (r, e * k as u64);
        }
        Some((b, e))
    }

    /// Removes all factors `p` (|p| > 1) from `self`.
    /// Returns the multiplicity and the cofactor.
    pub fn remove(&self, p: &Integer) -> (u64, Integer) {
        if self.is_zero() || p.cmp_abs(&Integer::one()) != Ordering::Greater {
            return (0, self.clone());
        }
        let mut rest = Integer::zero();
        let v = unsafe { sys::fmpz_remove(&mut rest.raw, &self.raw, &p.raw) };
        (v as u64, rest)
    }

    pub fn factorial(n: u64) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_fac_ui(&mut z.raw, n as sys::ulong) };
        z
    }

    pub fn binomial_u64(n: u64, k: u64) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_bin_uiui(&mut z.raw, n as sys::ulong, k as sys::ulong) };
        z
    }

    /// The rising factorial self (self + 1) ... (self + k - 1), by binary
    /// splitting.
    pub fn rising_factorial(&self, k: u64) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_rfac_ui(&mut z.raw, &self.raw, k as sys::ulong) };
        z
    }

    pub fn fibonacci(n: u64) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_fib_ui(&mut z.raw, n as sys::ulong) };
        z
    }

    pub fn euler_phi(&self) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_euler_phi(&mut z.raw, &self.raw) };
        z
    }

    pub fn moebius_mu(&self) -> i32 {
        unsafe { sys::fmpz_moebius_mu(&self.raw) }
    }

    pub fn divisor_sigma(&self, k: u64) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_divisor_sigma(&mut z.raw, k as sys::ulong, &self.raw) };
        z
    }

    /// `floor(log_b(self))` for `self >= 1`, `b >= 2`.
    pub fn ilog(&self, b: u64) -> Option<u64> {
        if self.sign() <= 0 || b < 2 {
            return None;
        }
        Some(unsafe { sys::fmpz_flog_ui(&self.raw, b as sys::ulong) } as u64)
    }

    pub fn mul_2exp(&self, e: u64) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_mul_2exp(&mut z.raw, &self.raw, e as sys::ulong) };
        z
    }

    /// Floor division by `2^e`.
    pub fn fdiv_2exp(&self, e: u64) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_fdiv_q_2exp(&mut z.raw, &self.raw, e as sys::ulong) };
        z
    }

    pub fn bitand(&self, o: &Integer) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_and(&mut z.raw, &self.raw, &o.raw) };
        z
    }

    pub fn bitor(&self, o: &Integer) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_or(&mut z.raw, &self.raw, &o.raw) };
        z
    }

    pub fn bitxor(&self, o: &Integer) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_xor(&mut z.raw, &self.raw, &o.raw) };
        z
    }

    pub fn bitnot(&self) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_complement(&mut z.raw, &self.raw) };
        z
    }

    /// Whether `self` is a strong probable prime to base `a` (`self` odd,
    /// greater than `a`).
    pub fn is_strong_probable_prime(&self, a: &Integer) -> bool {
        unsafe { sys::fmpz_is_strong_probabprime(&self.raw, &a.raw) != 0 }
    }

    /// The number of partitions of `n`.
    pub fn partitions(n: u64) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::arith_number_of_partitions(&mut z.raw, n as sys::ulong) };
        z
    }

    /// The (signed) Stirling number of the first kind `s(n, k)`.
    pub fn stirling1(n: u64, k: u64) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::arith_stirling_number_1(&mut z.raw, n as sys::ulong, k as sys::ulong) };
        z
    }

    /// The Stirling number of the second kind `S(n, k)`.
    pub fn stirling2(n: u64, k: u64) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::arith_stirling_number_2(&mut z.raw, n as sys::ulong, k as sys::ulong) };
        z
    }

    /// The `n`-th Bell number.
    pub fn bell(n: u64) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::arith_bell_number(&mut z.raw, n as sys::ulong) };
        z
    }

    /// The prime factors (with exponents) found by FLINT's self-initialising
    /// quadratic sieve, for `self > 1`.
    pub fn qsieve(&self) -> Vec<(Integer, u64)> {
        unsafe {
            let mut f: sys::fmpz_factor_struct = std::mem::zeroed();
            sys::fmpz_factor_init(&mut f);
            sys::qsieve_factor(&mut f, &self.raw);
            let mut out = Vec::with_capacity(f.num as usize);
            for i in 0..f.num as usize {
                let mut p = Integer::zero();
                sys::fmpz_set(&mut p.raw, f.p.add(i));
                out.push((p, *f.exp.add(i) as u64));
            }
            sys::fmpz_factor_clear(&mut f);
            out
        }
    }

    /// A proper factor of `self` (odd, composite and not a perfect power)
    /// found by FLINT's ECM with `curves` curves chosen from `seed` and the
    /// stage bounds `b1 < b2`, if they find one.
    pub fn ecm(&self, curves: u64, b1: u64, b2: u64, seed: u64) -> Option<Integer> {
        let mut f = Integer::zero();
        let found = unsafe {
            let mut state = sys::flint_rand_struct { __gmp_state: std::ptr::null_mut(), __randval: seed, __randval2: seed ^ 0x9e37_79b9_7f4a_7c15 };
            let r = sys::fmpz_factor_ecm(&mut f.raw, curves as sys::ulong, b1 as sys::ulong, b2 as sys::ulong, &mut state, &self.raw);
            if !state.__gmp_state.is_null() {
                sys::_flint_rand_clear_gmp_state(&mut state);
            }
            r
        };
        (found != 0 && !f.is_zero() && !f.is_one() && f != *self).then_some(f)
    }

    /// The residue `self mod m` for `m > 0`, as a machine word.
    pub fn mod_u64(&self, m: u64) -> u64 {
        assert!(m > 0);
        unsafe { sys::fmpz_fdiv_ui(&self.raw, m as sys::ulong) as u64 }
    }

    /// A hash of the value, stable across representations.
    pub fn hash_u64(&self) -> u64 {
        match self.to_i64() {
            Some(v) => mix64(v as u64),
            None => {
                const M61: u64 = (1u64 << 61) - 1;
                let r = self.mod_u64(M61);
                mix64(r ^ ((self.sign() as i64 as u64) << 62) ^ self.bits().rotate_left(32))
            }
        }
    }
}

#[inline]
fn mix64(mut x: u64) -> u64 {
    x ^= x >> 33;
    x = x.wrapping_mul(0xff51afd7ed558ccd);
    x ^= x >> 33;
    x = x.wrapping_mul(0xc4ceb9fe1a85ec53);
    x ^= x >> 33;
    x
}

impl Drop for Integer {
    #[inline]
    fn drop(&mut self) {
        // Small values live inline; only big values own an mpz.
        if self.to_i64_fast().is_none() {
            unsafe { sys::fmpz_clear(&mut self.raw) };
        }
    }
}

/// The largest absolute value FLINT stores inline in the word.
const COEFF_MAX: u64 = (1 << 62) - 1;

impl Integer {
    /// FLINT marks heap-allocated values by setting the two top bits of the
    /// word to `01`; anything else is an inline small integer.
    #[inline]
    fn to_i64_fast(&self) -> Option<i64> {
        let v = self.raw as i64;
        if ((v as u64) >> 62) == 1 { None } else { Some(v) }
    }

    /// Both values, if both are inline.
    #[inline]
    fn both_small(&self, other: &Integer) -> Option<(i64, i64)> {
        Some((self.to_i64_fast()?, other.to_i64_fast()?))
    }

    /// An inline value, if `v` is small enough to be one.
    #[inline]
    fn small(v: i128) -> Option<Integer> {
        (v.unsigned_abs() <= COEFF_MAX as u128).then(|| Integer { raw: v as i64 as sys::fmpz })
    }
}

impl Clone for Integer {
    #[inline]
    fn clone(&self) -> Self {
        if let Some(v) = self.to_i64_fast() {
            return Integer { raw: v as sys::fmpz };
        }
        let mut z = Integer::zero();
        unsafe { sys::fmpz_set(&mut z.raw, &self.raw) };
        z
    }
}

impl Default for Integer {
    fn default() -> Self {
        Integer::zero()
    }
}

impl PartialEq for Integer {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if let Some((a, b)) = self.both_small(other) {
            return a == b;
        }
        unsafe { sys::fmpz_equal(&self.raw, &other.raw) != 0 }
    }
}

impl Eq for Integer {}

impl PartialOrd for Integer {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Integer {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        if let Some((a, b)) = self.both_small(other) {
            return a.cmp(&b);
        }
        unsafe { sys::fmpz_cmp(&self.raw, &other.raw) }.cmp(&0)
    }
}

impl Hash for Integer {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash_u64());
    }
}

impl fmt::Display for Integer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad_integral(self.sign() >= 0, "", self.abs().to_string_radix(10).as_str())
    }
}

impl fmt::Debug for Integer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_radix(10))
    }
}

impl From<i64> for Integer {
    fn from(v: i64) -> Self {
        Integer::from_i64(v)
    }
}

impl From<i32> for Integer {
    fn from(v: i32) -> Self {
        Integer::from_i64(v as i64)
    }
}

impl From<u64> for Integer {
    fn from(v: u64) -> Self {
        Integer::from_u64(v)
    }
}

impl From<usize> for Integer {
    fn from(v: usize) -> Self {
        Integer::from_u64(v as u64)
    }
}

macro_rules! binop {
    ($trait:ident, $method:ident, $ffi:ident, $small:ident) => {
        impl ops::$trait<&Integer> for &Integer {
            type Output = Integer;
            #[inline]
            fn $method(self, rhs: &Integer) -> Integer {
                if let Some(z) = self.both_small(rhs).and_then(|(a, b)| Integer::small((a as i128).$small(b as i128))) {
                    return z;
                }
                let mut z = Integer::zero();
                unsafe { sys::$ffi(&mut z.raw, &self.raw, &rhs.raw) };
                z
            }
        }
        impl ops::$trait<Integer> for Integer {
            type Output = Integer;
            #[inline]
            fn $method(self, rhs: Integer) -> Integer {
                (&self).$method(&rhs)
            }
        }
        impl ops::$trait<&Integer> for Integer {
            type Output = Integer;
            #[inline]
            fn $method(self, rhs: &Integer) -> Integer {
                (&self).$method(rhs)
            }
        }
        impl ops::$trait<i64> for &Integer {
            type Output = Integer;
            #[inline]
            fn $method(self, rhs: i64) -> Integer {
                self.$method(&Integer::from_i64(rhs))
            }
        }
    };
}

binop!(Add, add, fmpz_add, wrapping_add);
binop!(Sub, sub, fmpz_sub, wrapping_sub);
binop!(Mul, mul, fmpz_mul, wrapping_mul);

impl ops::Neg for &Integer {
    type Output = Integer;
    fn neg(self) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_neg(&mut z.raw, &self.raw) };
        z
    }
}

impl ops::Neg for Integer {
    type Output = Integer;
    fn neg(mut self) -> Integer {
        self.neg_assign();
        self
    }
}

// An inline result replaces an inline value directly; a small `self` owns
// nothing that would need clearing.
impl ops::AddAssign<&Integer> for Integer {
    #[inline]
    fn add_assign(&mut self, rhs: &Integer) {
        if let Some(z) = self.both_small(rhs).and_then(|(a, b)| Integer::small(a as i128 + b as i128)) {
            self.raw = z.raw;
            return;
        }
        unsafe { sys::fmpz_add(&mut self.raw, &self.raw, &rhs.raw) };
    }
}

impl ops::SubAssign<&Integer> for Integer {
    #[inline]
    fn sub_assign(&mut self, rhs: &Integer) {
        if let Some(z) = self.both_small(rhs).and_then(|(a, b)| Integer::small(a as i128 - b as i128)) {
            self.raw = z.raw;
            return;
        }
        unsafe { sys::fmpz_sub(&mut self.raw, &self.raw, &rhs.raw) };
    }
}

impl ops::MulAssign<&Integer> for Integer {
    #[inline]
    fn mul_assign(&mut self, rhs: &Integer) {
        if let Some(z) = self.both_small(rhs).and_then(|(a, b)| Integer::small(a as i128 * b as i128)) {
            self.raw = z.raw;
            return;
        }
        unsafe { sys::fmpz_mul(&mut self.raw, &self.raw, &rhs.raw) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn z(s: &str) -> Integer {
        Integer::parse(s).unwrap()
    }

    #[test]
    fn arithmetic_and_printing() {
        let a = z("123456789012345678901234567890");
        let b = Integer::from_i64(-42);
        assert_eq!((&a * &b).to_string(), "-5185185138518518513851851851380");
        assert_eq!((&a + &b).to_string(), "123456789012345678901234567848");
        assert_eq!(Integer::from_i64(2).pow(100).to_string(), "1267650600228229401496703205376");
        assert_eq!(z("-17").to_string_radix(16), "-11");
        assert!(Integer::parse("12x").is_none());
    }

    #[test]
    fn euclidean_division() {
        let cases = [(7, 2, 3, 1), (-7, 2, -4, 1), (7, -2, -3, 1), (-7, -2, 4, 1)];
        for (a, b, q, r) in cases {
            let (qq, rr) = Integer::from_i64(a).div_rem_euclid(&Integer::from_i64(b)).unwrap();
            assert_eq!((qq.to_i64().unwrap(), rr.to_i64().unwrap()), (q, r), "{a} / {b}");
        }
    }

    #[test]
    fn number_theory() {
        assert!(z("1000000007").is_prime());
        assert!(!z("1000000008").is_prime());
        let f = Integer::from_i64(-360).factor().unwrap();
        assert_eq!(f.sign, -1);
        let got: Vec<(i64, u64)> = f.factors.iter().map(|(p, e)| (p.to_i64().unwrap(), *e)).collect();
        assert_eq!(got, vec![(2, 3), (3, 2), (5, 1)]);
        assert_eq!(Integer::from_i64(100).next_prime().to_i64(), Some(101));
        assert_eq!(Integer::from_i64(100).previous_prime().unwrap().to_i64(), Some(97));
        let (g, s, t) = Integer::from_i64(12).xgcd(&Integer::from_i64(15));
        assert_eq!(g.to_i64(), Some(3));
        assert_eq!((&(&s * 12) + &(&t * 15)).to_i64(), Some(3));
    }

    #[test]
    fn small_value_fast_paths_agree_with_flint() {
        let edge: i128 = 1 << 62;
        let mut xs: Vec<i128> = vec![0, 1, -1, 2, -3, 7, 1 << 31, 1 << 32, edge - 2, edge - 1, edge, edge + 1, 1 << 63, (1 << 63) - 1];
        xs.extend(xs.clone().iter().map(|x| -x));
        for &a in &xs {
            let za = Integer::from_i128(a);
            assert_eq!(za.to_i128(), Some(a));
            assert_eq!(za.sign(), a.signum() as i32);
            if let Ok(v) = i64::try_from(a) {
                assert_eq!(Integer::from_i64(v), za);
                assert_eq!(za.to_i64(), Some(v));
            }
            for &b in &xs {
                let zb = Integer::from_i128(b);
                assert_eq!(za == zb, a == b);
                assert_eq!(za.cmp(&zb), a.cmp(&b));
                assert_eq!((&za + &zb).to_i128(), Some(a + b), "{a} + {b}");
                assert_eq!((&za - &zb).to_i128(), Some(a - b), "{a} - {b}");
                let p = Integer::from_i128(a * b);
                assert_eq!(&za * &zb, p, "{a} * {b}");
                let (mut s, mut d, mut m) = (za.clone(), za.clone(), za.clone());
                s += &zb;
                d -= &zb;
                m *= &zb;
                assert_eq!((s.to_i128(), d.to_i128()), (Some(a + b), Some(a - b)));
                assert_eq!(m, p);
                if b != 0 {
                    // Floor division: a = q b + r with r of the sign of b.
                    let (q, r) = za.fdiv_qr(&zb).unwrap();
                    let (q, r) = (q.to_i128().unwrap(), r.to_i128().unwrap());
                    assert!(a == q * b + r && r.abs() < b.abs() && (r == 0 || (r < 0) == (b < 0)), "{a} fdiv {b}");
                }
            }
        }
    }

    #[test]
    fn big_values_round_trip() {
        let big = Integer::from_i64(3).pow(200);
        let limbs = big.to_limbs();
        assert_eq!(Integer::from_limbs(&limbs, true), -big.clone());
        assert_eq!(big.clone().hash_u64(), big.hash_u64());
        assert_eq!(Integer::from_i128(-(1i128 << 100)).to_i128(), Some(-(1i128 << 100)));
    }
}
