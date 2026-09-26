//! Integer factorization: `Factorization` and the individual methods
//! (trial division, Pollard rho, SQUFOF, p - 1, p + 1, ECM, the quadratic
//! sieve), coprime bases, partial factorizations and Cunningham numbers.

use std::collections::HashMap;

use calyx_flint::Integer;

use super::factseq::{Fact, fact_value, factor, flint_factor};
use super::numtheory::{each_prime, modp, modsqrt, primes_up_to};
use super::{arg_not, arg_range, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::random::Rng;
use crate::value::*;

pub(crate) mod arith;
pub mod cunningham;
mod ecm;
mod pm1;
mod siqs;
mod stage1;
mod stage2;

fn int(v: i64) -> Integer {
    Integer::from_i64(v)
}

/// A factorization sequence and the composites left unfactored.
fn fact_and_rest(f: &Fact, rest: Vec<Integer>) -> Vals {
    vals![fact_value(f), Value::int_seq(rest)]
}

fn sorted_fact(mut f: Fact) -> Fact {
    f.sort_by(|a, b| a.0.cmp(&b.0));
    let mut out: Fact = Vec::with_capacity(f.len());
    for (p, e) in f {
        match out.last_mut() {
            Some((q, k)) if *q == p => *k += e,
            _ => out.push((p, e)),
        }
    }
    out
}

fn param_int(a: &CallArgs, name: &str) -> Option<Integer> {
    match a.param(name) {
        Some(Value::Int(n)) => Some(n.clone()),
        _ => None,
    }
}

// ----- Factorization ------------------------------------------------------------------

/// Whether the factors must be proven prime (the parameter Proof).
fn proof(a: &CallArgs) -> bool {
    !matches!(a.param("Proof"), Some(Value::Bool(false)))
}

/// Split `n` with one method until every part is prime or the method
/// gives up. `method` returns a proper divisor of a composite, if it finds
/// one. Powers of 2 and 3 and perfect powers are taken out first. The parts
/// left are listed with their multiplicities, as in Magma.
fn split_with(n: &Integer, proof: bool, method: &mut dyn FnMut(&Integer) -> Option<Integer>) -> (Fact, Vec<Integer>) {
    let mut fact = Fact::new();
    let mut rest = Vec::new();
    let mut stack = vec![(n.abs(), 1u64)];
    while let Some((m, e)) = stack.pop() {
        if m.is_one() {
            continue;
        }
        if if proof { m.is_prime() } else { m.is_probable_prime() } {
            fact.push((m, e));
            continue;
        }
        let mut m = m;
        let mut found_small = false;
        for p in [int(2), int(3)] {
            let (k, r) = m.remove(&p);
            if k > 0 {
                fact.push((p, k * e));
                m = r;
                found_small = true;
            }
        }
        if found_small {
            stack.push((m, e));
            continue;
        }
        if let Some((b, k)) = m.perfect_power() {
            stack.push((b, e * k));
            continue;
        }
        match method(&m) {
            Some(d) if !d.is_one() && d != m => {
                let q = m.divexact(&d);
                stack.push((d, e));
                stack.push((q, e));
            }
            _ => rest.extend(std::iter::repeat_n(m, e as usize)),
        }
    }
    rest.sort();
    (sorted_fact(fact), rest)
}

fn factorization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.clone();
    if n.is_zero() {
        return Err(arg_not(1, "non-zero"));
    }
    let sign = Value::int(n.sign() as i64);
    // Negative limits count as not given, as in Magma.
    let given = |name: &str| param_int(a, name).filter(|b| b.sign() >= 0).map(|b| b.to_u64().unwrap_or(u64::MAX));
    let mut stages = Stages {
        trial: given("TrialDivisionLimit").unwrap_or(10000),
        squfof: given("SQUFOFLimit").unwrap_or(24),
        rho: given("PollardRhoLimit").unwrap_or(8191),
        ecm: given("ECMLimit"),
        mpqs: given("MPQSLimit"),
        proof: proof(a),
        b1: None,
    };
    let (fact, rest) = stages.factor(&n, &mut it.rng, &mut it.stored_factors);
    // The sign and the unfactored part are returned only when asked for;
    // the latter stays unassigned when the factorization is complete.
    let mut out: Vals = vals![fact_value(&fact), sign, if rest.is_empty() { Value::Undef } else { Value::int_seq(rest) }];
    out.truncate(a.nresults.max(1));
    Ok(out)
}

impl Interp {
    /// The factorization of |n| (non-zero) as Factorization finds it by
    /// default, storing the primes that ECM and MPQS split off, as Magma's
    /// functions that factorize their arguments do.
    pub fn factor_int(&mut self, n: &Integer) -> Fact {
        Stages::default().factor(n, &mut self.rng, &mut self.stored_factors).0
    }
}

/// The factorization of |n| (non-zero) as Factorization finds it by
/// default, for callers without an interpreter.
pub fn factor_default(n: &Integer) -> Fact {
    Stages::default().factor(n, &mut Rng::new(1), &mut Vec::new()).0
}

/// The stages of Factorization, with their limits.
struct Stages {
    /// The bound on the primes for trial division.
    trial: u64,
    /// The most digits for SQUFOF.
    squfof: u64,
    /// The iterations of Pollard rho.
    rho: u64,
    /// The curves of ECM (by default as many as the size warrants).
    ecm: Option<u64>,
    /// The most digits for MPQS (by default no limit).
    mpqs: Option<u64>,
    /// Whether the factors must be proven prime.
    proof: bool,
    /// The B1 that ECM has reached on the number being factored.
    b1: Option<u64>,
}

impl Default for Stages {
    fn default() -> Stages {
        Stages { trial: 10000, squfof: 24, rho: 8191, ecm: None, mpqs: None, proof: true, b1: None }
    }
}

impl Stages {
    /// The factorization of |n| (non-zero), and the composites left, which
    /// only both ECMLimit and MPQSLimit can leave. The primes that ECM and
    /// MPQS split off are stored for later calls. When |n| is b^k - 1 or
    /// b^k + 1, its cyclotomic factors come first, with the Cunningham tables.
    fn factor(&mut self, n: &Integer, rng: &mut Rng, stored: &mut Vec<Integer>) -> (Fact, Vec<Integer>) {
        let m = n.abs();
        if m.bits() > 64 {
            for (x, plus) in [(&m + 1, false), (&m - 1, true)] {
                let Some((b, k)) = x.perfect_power() else { continue };
                let proof = self.proof;
                let prime = |p: &Integer| if proof { p.is_prime() } else { p.is_probable_prime() };
                let mut rest = Vec::new();
                let f = cunningham::factor_power(&b, k, plus, &prime, &mut |c| {
                    let (f, r) = self.factor_general(c, rng, stored);
                    rest.extend(r);
                    f
                });
                rest.sort();
                return (sorted_fact(f), rest);
            }
        }
        self.factor_general(&m, rng, stored)
    }

    /// The factorization of |n| (non-zero) by the stages alone.
    fn factor_general(&mut self, n: &Integer, rng: &mut Rng, stored: &mut Vec<Integer>) -> (Fact, Vec<Integer>) {
        let mut m = n.abs();
        let mut fact = Fact::new();
        if self.ecm.is_none() && self.mpqs.is_none() && self.squfof >= 20 && m.bits() <= 64 {
            // The stages would end with SQUFOF: FLINT's word methods are faster.
            fact.extend(flint_factor(&m));
            m = Integer::one();
        }
        let (f, r) = trial_division(&m, self.trial);
        fact.extend(f);
        let proof = self.proof;
        let (f, rest) = split_with(&r, proof, &mut |x: &Integer| {
            let (d, by_ecm_or_mpqs) = self.split(x, rng, stored)?;
            // As in Magma, the factor found is stored with the cofactor left
            // once its powers are divided out, those of them that are prime
            // or powers of a prime (which is stored).
            if by_ecm_or_mpqs {
                for y in [d.clone(), x.remove(&d).1] {
                    let y = y.perfect_power().map_or(y, |(b, _)| b);
                    if !y.is_one() && !stored.contains(&y) && if proof { y.is_prime() } else { y.is_probable_prime() } {
                        stored.push(y);
                    }
                }
            }
            Some(d)
        });
        fact.extend(f);
        (sorted_fact(fact), rest)
    }

    /// A proper divisor of the composite m (prime to 6 and not a perfect
    /// power) from the first stage that finds one: SQUFOF, Pollard rho, the
    /// stored factors, ECM and MPQS. Unless both ECM and MPQS are bounded,
    /// whatever it takes follows: ECM without end when MPQS may not be used,
    /// or else FLINT's factorization. With the divisor comes whether ECM or
    /// MPQS found it.
    fn split(&mut self, m: &Integer, rng: &mut Rng, stored: &[Integer]) -> Option<(Integer, bool)> {
        let digits = m.to_string().len() as u64;
        if digits <= self.squfof && m.bits() <= 125 {
            if let Some(d) = squfof(m, 200_000) {
                return Some((d, false));
            }
        }
        if let Some(d) = pollard_rho(m, &int(1), &int(1), self.rho) {
            return Some((d, false));
        }
        // The stored factors are tried before ECM and MPQS.
        if let Some(p) = stored.iter().find(|p| p.bits() <= m.bits() && m.is_divisible_by(p)) {
            return Some((p.clone(), false));
        }
        // MPQS is not used below 26 digits.
        let mpqs = digits > 25 && self.mpqs.is_none_or(|l| digits <= l);
        let complete = self.ecm.is_none() || self.mpqs.is_none();
        match self.ecm {
            // Without a limit on the curves when MPQS follows, B1 grows by its
            // square root a curve and carries over to the cofactors, as in
            // Magma, while the curves cost less than sieving.
            None if mpqs => {
                let bound = ecm_bound(digits);
                let b1 = self.b1.get_or_insert((bound / 4).clamp(100, 2000));
                while *b1 <= bound {
                    if let Some(d) = ecm::curve(m, *b1, b1.saturating_mul(100), 6 + rng.below_u64(1 << 62)) {
                        return Some((d, true));
                    }
                    *b1 += b1.isqrt();
                }
            }
            // Otherwise B1 grows from 500 by 100 a curve: over the curves
            // given, without end when MPQS may not be used, or to 600 over
            // the 2 curves Magma gives numbers of up to 25 digits.
            _ => {
                let (curves, top) = match self.ecm {
                    Some(c) => (c, None),
                    None if digits > 25 => (u64::MAX, None),
                    None => (2, Some(600)),
                };
                for i in 0..curves {
                    let b1 = match top {
                        Some(t) => 500 + (t - 500) * i / (curves - 1).max(1),
                        None => 500u64.saturating_add(i.saturating_mul(100)),
                    };
                    if let Some(d) = ecm::curve(m, b1, b1.saturating_mul(100), 6 + rng.below_u64(1 << 62)) {
                        return Some((d, true));
                    }
                }
            }
        }
        if mpqs {
            if let Some(d) = siqs::siqs(m) {
                return Some((d, true));
            }
        }
        if complete {
            return flint_factor(m).first().map(|(p, _)| (p.clone(), false));
        }
        None
    }
}

/// The largest B1 for ECM on a composite of the given size before MPQS:
/// past it, sieving costs less than more curves. It grows tenfold every 15
/// digits, from 8000 at 60 digits.
fn ecm_bound(digits: u64) -> u64 {
    (8000.0 * 10f64.powf((digits as f64 - 60.0) / 15.0)).min(1e18) as u64
}

fn store_factor(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ps = match &a.args[0] {
        Value::Int(n) => vec![n.clone()],
        v => super::ints::ints_of(v)?,
    };
    for p in &ps {
        if p.sign() <= 0 {
            return Err(arg_not(1, "positive"));
        }
        if !p.is_prime() {
            return Err(super::arg_prime(1, p));
        }
    }
    for p in ps {
        if !it.stored_factors.contains(&p) {
            it.stored_factors.push(p);
        }
    }
    Ok(Vals::new())
}

fn get_stored_factors(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int_seq(it.stored_factors.clone()))
}

fn clear_stored_factors(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    it.stored_factors.clear();
    Ok(Vals::new())
}

// ----- trial division ---------------------------------------------------------------------

/// The primes below 2^16, for trial division.
fn small_primes() -> &'static [u64] {
    static PRIMES: std::sync::OnceLock<Vec<u64>> = std::sync::OnceLock::new();
    PRIMES.get_or_init(|| primes_up_to(1 << 16))
}

/// The primes up to `bound` dividing `n`, and the part of |n| left.
fn trial_division(n: &Integer, bound: u64) -> (Fact, Integer) {
    let mut m = n.abs();
    let mut fact = Fact::new();
    let limit = bound.min(1 << 32);
    let mut word = m.to_u64();
    // One prime: whether to go on.
    let mut step = |p: u64| {
        if m.is_one() {
            return false;
        }
        if word.is_some_and(|w| p as u128 * p as u128 > w as u128) {
            // What is left is prime; keep it only if it is within the bound.
            if m <= Integer::from_u64(bound) {
                fact.push((std::mem::replace(&mut m, Integer::one()), 1));
            }
            return false;
        }
        if m.mod_u64(p) == 0 {
            let pi = Integer::from_u64(p);
            let (k, r) = m.remove(&pi);
            fact.push((pi, k));
            m = r;
            word = m.to_u64();
        }
        true
    };
    let small = small_primes();
    if small.iter().take_while(|&&p| p <= limit).all(|&p| step(p)) && limit > 1 << 16 {
        each_prime((1 << 16) + 1, limit, &mut step);
    }
    (fact, m)
}

fn trial_division_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.clone();
    if n.is_zero() {
        return Err(arg_not(1, "non-zero"));
    }
    let bound = if a.args.len() > 1 {
        let b = a.int(1)?;
        if b.sign() <= 0 {
            return Err(RuntimeError::runtime("Argument 2 must be greater than 0"));
        }
        b.to_u64().unwrap_or(u64::MAX)
    } else {
        10000
    };
    let (f, r) = trial_division(&n, bound);
    Ok(vals![fact_value(&f), Value::Int(r)])
}

// ----- Pollard rho --------------------------------------------------------------------------

/// Brent's variant of Pollard's rho with x -> x^2 + c from x = s, for at
/// most `k` iterations.
fn pollard_rho(n: &Integer, c: &Integer, s: &Integer, k: u64) -> Option<Integer> {
    let f = |x: &Integer| modp(&(&(x * x) + c), n);
    let (mut y, mut r, mut q) = (modp(s, n), 1u64, Integer::one());
    let mut x = y.clone();
    let mut ys = y.clone();
    let mut g = Integer::one();
    let mut iters = 0u64;
    let batch = 32u64;
    while g.is_one() {
        x = y.clone();
        for _ in 0..r {
            y = f(&y);
        }
        let mut done = 0u64;
        while done < r && g.is_one() {
            ys = y.clone();
            for _ in 0..batch.min(r - done) {
                y = f(&y);
                q = modp(&(&q * &(&x - &y).abs()), n);
                iters += 1;
            }
            g = q.gcd(n);
            done += batch;
            if iters >= k && g.is_one() {
                return None;
            }
        }
        r *= 2;
    }
    if g == *n {
        // Step back one iteration at a time.
        loop {
            ys = f(&ys);
            g = (&x - &ys).abs().gcd(n);
            if !g.is_one() {
                break;
            }
        }
    }
    if g == *n { None } else { Some(g) }
}

fn pollard_rho_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.clone();
    if n <= Integer::one() {
        return Err(RuntimeError::runtime("Argument 1 must be greater than 1"));
    }
    let (c, s, k) = if a.args.len() == 4 { (a.int(1)?.clone(), a.int(2)?.clone(), a.int(3)?.to_u64().unwrap_or(0)) } else { (int(1), int(1), 8191) };
    let (f, r) = split_with(&n, proof(a), &mut |m: &Integer| pollard_rho(m, &c, &s, k));
    Ok(fact_and_rest(&f, r))
}

// ----- SQUFOF ----------------------------------------------------------------------------------

/// Shanks's square form factorization, with small multipliers.
fn squfof(n: &Integer, limit: u64) -> Option<Integer> {
    if n.is_square() {
        return n.isqrt();
    }
    for k in [1i64, 3, 5, 7, 11, 15, 21, 33, 35, 55, 77, 105, 165, 231, 385, 1155] {
        let kn = n * &int(k);
        let p = match kn.to_i128() {
            Some(x) if x < 1 << 125 => squfof_word(x, limit).map(Integer::from_i128),
            _ => squfof_big(&kn, limit),
        };
        let Some(p) = p else { continue };
        let f = n.gcd(&p);
        if !f.is_one() && f != *n {
            return Some(f);
        }
    }
    None
}

/// The P at which SQUFOF on kn finds its symmetry point, from a square form
/// met within `limit` steps.
fn squfof_big(kn: &Integer, limit: u64) -> Option<Integer> {
    let p0 = kn.isqrt()?;
    let (mut qprev, mut q) = (Integer::one(), kn - &(&p0 * &p0));
    if q.is_zero() {
        return None;
    }
    let mut p = p0.clone();
    let mut found = false;
    for i in 1..=limit {
        let b = (&p0 + &p).fdiv_qr(&q)?.0;
        let pn = &(&b * &q) - &p;
        let qn = &qprev + &(&b * &(&p - &pn));
        qprev = q;
        q = qn;
        p = pn;
        // q is now Q_(i+1), which must be a square with even index.
        if i % 2 == 1 && q.is_square() {
            found = true;
            break;
        }
    }
    if !found {
        return None;
    }
    let r = q.isqrt()?;
    let b = (&p0 - &p).fdiv_qr(&r)?.0;
    p = &(&b * &r) + &p;
    qprev = r;
    q = (kn - &(&p * &p)).divexact(&qprev);
    if q.is_zero() {
        return None;
    }
    for _ in 0..limit {
        let b = (&p0 + &p).fdiv_qr(&q)?.0;
        let pn = &(&b * &q) - &p;
        let qn = &qprev + &(&b * &(&p - &pn));
        if pn == p {
            break;
        }
        qprev = q;
        q = qn;
        p = pn;
    }
    Some(p)
}

/// squfof_big in machine words, for kn < 2^125: P stays below sqrt(kn) and
/// Q below 2 sqrt(kn), so the quotients are taken in 64 bits.
fn squfof_word(kn: i128, limit: u64) -> Option<i128> {
    let p0 = isqrt_i128(kn);
    let mut q = kn - p0 * p0;
    if q == 0 {
        return None;
    }
    let (mut p, mut qprev) = (p0, 1i128);
    let mut found = false;
    for i in 1..=limit {
        let b = ((p0 + p) as u64 / q as u64) as i128;
        let pn = b * q - p;
        let qn = qprev + b * (p - pn);
        qprev = q;
        q = qn;
        p = pn;
        if i % 2 == 1 && square_root_u64(q as u64).is_some() {
            found = true;
            break;
        }
    }
    if !found {
        return None;
    }
    let r = square_root_u64(q as u64)? as i128;
    p += (p0 - p) / r * r;
    qprev = r;
    q = (kn - p * p) / qprev;
    if q == 0 {
        return None;
    }
    for _ in 0..limit {
        let b = ((p0 + p) as u64 / q as u64) as i128;
        let pn = b * q - p;
        let qn = qprev + b * (p - pn);
        if pn == p {
            break;
        }
        qprev = q;
        q = qn;
        p = pn;
    }
    Some(p)
}

/// The floor of the square root of x >= 0.
fn isqrt_i128(x: i128) -> i128 {
    let mut r = (x as f64).sqrt() as i128;
    if r > 0 {
        r = (r + x / r) / 2;
    }
    while r * r > x {
        r -= 1;
    }
    while (r + 1) * (r + 1) <= x {
        r += 1;
    }
    r
}

/// The square root of q if q is a square.
fn square_root_u64(q: u64) -> Option<u64> {
    // The squares modulo 64 first.
    const SQUARES: u64 = {
        let (mut m, mut r) = (0u64, 0);
        while r < 64 {
            m |= 1 << (r * r % 64);
            r += 1;
        }
        m
    };
    if SQUARES >> (q & 63) & 1 == 0 {
        return None;
    }
    let r = (q as f64).sqrt() as u64;
    (r.saturating_sub(1)..=r + 1).find(|&x| x.checked_mul(x) == Some(q))
}

fn squfof_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.clone();
    if n <= Integer::one() {
        return Err(RuntimeError::runtime("Argument 1 must be greater than 1"));
    }
    if n.bits() > 126 {
        return Err(RuntimeError::runtime(format!("Argument 1 ({n}) is too large")));
    }
    let limit = if a.args.len() > 1 { a.int(1)?.to_u64().unwrap_or(0) } else { 200_000 };
    let (f, r) = split_with(&n, proof(a), &mut |m: &Integer| squfof(m, limit));
    Ok(fact_and_rest(&f, r))
}

// ----- p - 1, p + 1 and ECM ------------------------------------------------------------------------

/// The factors of B1^1.4248 that give the default B2 of each method, as
/// measured in Magma.
const PM1_B2: f64 = 0.14;
const PP1_B2: f64 = 1.0;
const ECM_B2: f64 = 3.3;

/// The largest B1 and B2 taken: no run with larger ones would end.
const MAX_B1: u64 = 1 << 52;
const MAX_B2: u64 = 1 << 62;

/// Magma's default B2 for B1, with the method's factor.
fn default_b2(b1: u64, scale: f64) -> u64 {
    (scale * (b1 as f64).powf(1.424828748)).min(MAX_B2 as f64) as u64
}

/// The arguments and parameters of pMinus1, pPlus1 and ECM.
struct Stages2 {
    n: Integer,
    b1: u64,
    /// B2 (by default Magma's, from the method's factor): below B1 it skips
    /// stage 2.
    b2: u64,
    k: u64,
    x0: Option<Integer>,
    sigma: Option<Integer>,
}

/// The arguments and parameters of pMinus1, pPlus1 and ECM, checked in
/// Magma's order: the parameters' types, k, Sigma, then the arguments.
fn stage_args(a: &CallArgs, scale: f64, ecm: bool) -> RResult<Stages2> {
    let param = |p: &str| match a.param(p) {
        None | Some(Value::Undef) => Ok(None),
        Some(Value::Int(x)) => Ok(Some(x.clone())),
        Some(_) => Err(RuntimeError::runtime(format!("Bad type for parameter '{p}'\nArgument types given: RngIntElt, RngIntElt"))),
    };
    let (x0, b2, k, sigma) = (param("x0")?, param("B2")?, param("k")?, param("Sigma")?);
    let k = match k {
        None => 2,
        Some(k) if k.sign() > 0 => k.to_u64().unwrap_or(u64::MAX),
        Some(_) => return Err(RuntimeError::runtime("Bad value for parameter 'k'")),
    };
    match &sigma {
        Some(s) if s.sign() <= 0 => return Err(RuntimeError::runtime("Bad value for parameter 'Sigma'")),
        Some(_) if !ecm => return Err(RuntimeError::runtime("Sigma parameter only allowed for ECM")),
        _ => {}
    }
    let n = a.int(0)?.clone();
    if n <= Integer::one() {
        return Err(RuntimeError::runtime("Argument 1 should be greater than 1"));
    }
    let b1 = a.int(1)?;
    if *b1 <= Integer::one() {
        return Err(RuntimeError::runtime("Argument 2 should be greater than 1"));
    }
    let b1 = b1.to_u64().map_or(MAX_B1, |b| b.min(MAX_B1));
    let b2 = match b2 {
        None => default_b2(b1, scale),
        Some(b) if b.sign() <= 0 => 0,
        Some(b) => b.to_u64().map_or(MAX_B2, |b| b.min(MAX_B2)),
    };
    Ok(Stages2 { n, b1, b2, k, x0, sigma })
}

/// A random x0 or sigma, as Magma chooses them.
fn random_start(it: &mut Interp) -> Integer {
    Integer::from_u64(6 + it.rng.below_u64((1 << 32) - 6))
}

/// The factor a method finds on n > 1: it is not run on even n, which has
/// the factor 2 but for n = 2.
fn run_odd(n: &Integer, method: impl FnOnce() -> Option<Integer>) -> Option<Integer> {
    match n.is_even() {
        true => (n.bits() > 2).then(|| int(2)),
        false => method(),
    }
}

/// The x0 that the methods start from: as Magma passes it on, a negative
/// x0 gains 2^64 once, as a machine word would.
fn start_value(x0: &Integer) -> Integer {
    match x0.sign() < 0 {
        true => x0 + &Integer::one().mul_2exp(64),
        false => x0.clone(),
    }
}

/// The factor found and the x0 or sigma it came from, or 0 alone (the
/// second value is left unassigned).
fn found(d: Option<Integer>, start: Integer) -> RResult<Vals> {
    match d {
        Some(d) => Ok(vals![Value::Int(d), Value::Int(start)]),
        None => Ok(vals![Value::Int(Integer::zero()), Value::Undef]),
    }
}

fn p_minus_1_fn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = stage_args(a, PM1_B2, false)?;
    let x0 = s.x0.unwrap_or_else(|| random_start(it));
    found(run_odd(&s.n, || pm1::p_minus_1(&s.n, s.b1, s.b2, s.k, &start_value(&x0))), x0)
}

fn p_plus_1_fn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = stage_args(a, PP1_B2, false)?;
    let x0 = s.x0.unwrap_or_else(|| random_start(it));
    found(run_odd(&s.n, || pm1::p_plus_1(&s.n, s.b1, s.b2, s.k, &start_value(&x0))), x0)
}

/// Suyama's curve for sigma: u = sigma^2 - 5, v = 4 sigma,
/// A + 2 = (v - u)^3 (3u + v) / (4 u^3 v), starting point (u^3 : v^3).
/// Returns (a24 numerator, a24 denominator, x0 numerator, x0 denominator).
fn suyama(sigma: &Integer) -> (Integer, Integer, Integer, Integer) {
    let u = &(sigma * sigma) - &int(5);
    let v = sigma * &int(4);
    let vu = &v - &u;
    let num = &(&(&vu * &vu) * &vu) * &(&(&u * &int(3)) + &v);
    let den = &(&(&(&u * &u) * &u) * &v) * &int(16);
    (num, den, &(&u * &u) * &u, &(&v * &v) * &v)
}

fn ecm_fn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = stage_args(a, ECM_B2, true)?;
    let sigma = s.sigma.unwrap_or_else(|| random_start(it));
    let x0 = s.x0.as_ref().map(start_value);
    found(run_odd(&s.n, || ecm::run(&s.n, s.b1, s.b2, s.k, &sigma, x0.as_ref())), sigma)
}

/// Magma's package code runs ECM on a random curve for each B1 from L to U,
/// B1 growing by its square root, and returns 0 and 0 when none succeeds.
fn ecm_steps(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.clone();
    let (mut b1, hi) = (a.int(1)?.clone(), a.int(2)?.clone());
    let inner = |msg: &str| {
        let mut e = super::hidden_inner(RuntimeError::runtime(msg));
        e.context = Some("ECM".into());
        e
    };
    while b1 <= hi {
        if n <= Integer::one() {
            return Err(inner("Argument 1 should be greater than 1"));
        }
        if b1 <= Integer::one() {
            return Err(inner("Argument 2 should be greater than 1"));
        }
        let b = b1.to_u64().map_or(MAX_B1, |b| b.min(MAX_B1));
        let sigma = random_start(it);
        if let Some(d) = run_odd(&n, || ecm::run(&n, b, default_b2(b, ECM_B2), 2, &sigma, None)) {
            return Ok(vals![Value::Int(d), Value::Int(sigma)]);
        }
        b1 = &b1 + &Integer::from_u64(b.isqrt());
    }
    Ok(vals![Value::int(0), Value::int(0)])
}

fn mpqs(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.clone();
    if n <= Integer::one() {
        return Err(RuntimeError::runtime("Argument 1 must be greater than 1"));
    }
    let (f, r) = split_with(&n, proof(a), &mut qs_split);
    Ok(fact_and_rest(&f, r))
}

/// A proper divisor of the composite m by the quadratic sieve (FLINT's word
/// methods below 64 bits, where the sieve has no room).
fn qs_split(m: &Integer) -> Option<Integer> {
    if m.bits() <= 64 {
        return factor(m).first().map(|(p, _)| p.clone());
    }
    siqs::siqs(m)
}

// ----- ECM curve orders ---------------------------------------------------------------------------------

/// Affine points on y^2 = x^3 + a2 x^2 + a4 x over GF(p); `None` is the
/// point at infinity.
type Pt = Option<(Integer, Integer)>;

struct Curve {
    p: Integer,
    a2: Integer,
    a4: Integer,
}

impl Curve {
    fn add(&self, s: &Pt, t: &Pt) -> Pt {
        let p = &self.p;
        let (Some((x1, y1)), Some((x2, y2))) = (s, t) else {
            return if s.is_none() { t.clone() } else { s.clone() };
        };
        let lam = if x1 == x2 {
            if modp(&(y1 + y2), p).is_zero() {
                return None;
            }
            let num = &(&(&(&(x1 * x1) * &int(3)) + &(&(&self.a2 * x1) * &int(2))) + &self.a4);
            modp(&(num * &modp(&(y1 * &int(2)), p).invmod(p)?), p)
        } else {
            modp(&(&(y2 - y1) * &modp(&(x2 - x1), p).invmod(p)?), p)
        };
        let x3 = modp(&(&(&(&(&lam * &lam) - &self.a2) - x1) - x2), p);
        let y3 = modp(&(&(&lam * &(x1 - &x3)) - y1), p);
        Some((x3, y3))
    }

    fn mul(&self, s: &Pt, k: &Integer) -> Pt {
        let mut r: Pt = None;
        let mut base = s.clone();
        let mut k = k.clone();
        while !k.is_zero() {
            if k.is_odd() {
                r = self.add(&r, &base);
            }
            base = self.add(&base, &base);
            k = k.fdiv_2exp(1);
        }
        r
    }

    fn rhs(&self, x: &Integer) -> Integer {
        modp(&(&(&(&(x * x) * x) + &(&(&self.a2 * x) * x)) + &(&self.a4 * x)), &self.p)
    }

    fn random_point(&self, rng: &mut crate::random::Rng) -> Pt {
        loop {
            let x = rng.below(&self.p);
            let r = self.rhs(&x);
            if r.is_zero() {
                return Some((x, r));
            }
            if r.kronecker(&self.p) == 1 {
                return Some((x, modsqrt(&r, &self.p)?));
            }
        }
    }

    /// The number of points over GF(p).
    fn order(&self, rng: &mut crate::random::Rng) -> Integer {
        let p = &self.p;
        if p.to_u64().is_some_and(|p| p < 5000) {
            let mut n = p + 1;
            let mut x = Integer::zero();
            while x < *p {
                n = &n + &Integer::from_i64(self.rhs(&x).kronecker(p) as i64);
                x = &x + 1;
            }
            return n;
        }
        // The order lies in [p + 1 - 2 sqrt p, p + 1 + 2 sqrt p]; find the
        // multiples of the orders of random points there.
        let s = &(p.isqrt().unwrap() * &int(2)) + 2;
        let (lo, hi) = (&(p + 1) - &s, &(p + 1) + &s);
        let width = &hi - &lo;
        let m = &width.isqrt().unwrap() + 1;
        let mut lcm = Integer::one();
        for _ in 0..64 {
            let pt = self.random_point(rng);
            let mut baby: std::collections::HashMap<Integer, Vec<(u64, Integer)>> = std::collections::HashMap::new();
            let mut q: Pt = None;
            let mm = m.to_u64().unwrap();
            for j in 0..=mm {
                if let Some((x, y)) = &q {
                    baby.entry(x.clone()).or_default().push((j, y.clone()));
                }
                q = self.add(&q, &pt);
            }
            let giant = self.mul(&pt, &m);
            let mut r = self.mul(&pt, &lo);
            let mut base = lo.clone();
            let mut cands = Vec::new();
            while base <= &hi + &m {
                match &r {
                    None => cands.push(base.clone()),
                    Some((x, y)) => {
                        for (j, yj) in baby.get(x).into_iter().flatten() {
                            let j = Integer::from_u64(*j);
                            cands.push(if yj == y { &base - &j } else { &base + &j });
                        }
                    }
                }
                r = self.add(&r, &giant);
                base = &base + &m;
            }
            // The order of this point divides every candidate that kills it.
            let Some(nn) = cands.into_iter().find(|c| c.sign() > 0 && self.mul(&pt, c).is_none()) else {
                continue;
            };
            let mut ord = nn;
            for (q, _) in factor(&ord) {
                while ord.is_divisible_by(&q) && self.mul(&pt, &ord.divexact(&q)).is_none() {
                    ord = ord.divexact(&q);
                }
            }
            lcm = lcm.lcm(&ord);
            let first = lo.cdiv_q(&lcm).unwrap();
            let first = &first * &lcm;
            if &first + &lcm > hi {
                return first;
            }
        }
        // Fall back on counting (small p only reach here).
        let mut n = p + 1;
        let mut x = Integer::zero();
        while x < *p {
            n = &n + &Integer::from_i64(self.rhs(&x).kronecker(p) as i64);
            x = &x + 1;
        }
        n
    }
}

/// The curve ECM uses modulo the prime p for sigma: Suyama's Montgomery
/// curve b y^2 = x^3 + A x^2 + x through (x0, 1), in the form
/// y^2 = x^3 + bA x^2 + b^2 x. Where it degenerates, Magma's package code
/// fails in a division or in EllipticCurve.
fn ecm_curve_mod(p: &Integer, sigma: &Integer) -> RResult<Curve> {
    let fails = |msg: &str, name: &str| {
        let mut e = super::hidden(RuntimeError::runtime(msg));
        e.context = Some(name.into());
        e
    };
    let (num, den, xn, xd) = suyama(sigma);
    let inv = modp(&den, p).invmod(p).ok_or_else(|| fails("Division by zero", "/"))?;
    let a = modp(&(&(&(&num * &inv) * &int(4)) - &int(2)), p);
    let x0 = modp(&(&xn * &modp(&xd, p).invmod(p).ok_or_else(|| fails("Division by zero", "/"))?), p);
    let b = modp(&(&(&(&(&x0 * &x0) * &x0) + &(&(&a * &x0) * &x0)) + &x0), p);
    let disc = modp(&(&(&b * &b) * &(&(&a * &a) - &int(4))), p);
    if disc.is_zero() {
        return Err(fails("Curve is singular", "EllipticCurve"));
    }
    Ok(Curve { p: p.clone(), a2: modp(&(&b * &a), p), a4: modp(&(&b * &b), p) })
}

fn ecm_order_of(it: &mut Interp, a: &CallArgs) -> RResult<Integer> {
    let (p, s) = (a.int(0)?.clone(), a.int(1)?.clone());
    if p.sign() <= 0 || !p.is_prime() {
        return Err(super::require(RuntimeError::runtime("First argument must be a positive prime")));
    }
    let c = ecm_curve_mod(&p, &s)?;
    Ok(c.order(&mut it.rng))
}

fn ecm_order(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(ecm_order_of(it, a)?)
}

fn ecm_factored_order(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(fact_value(&factor(&ecm_order_of(it, a)?)))
}

// ----- coprime bases and partial factorizations ------------------------------------------------------

/// The natural coprime base of the integers (ignoring signs, 0 and 1),
/// with the exponent of each base element in their product.
pub fn coprime_basis(s: &[Integer]) -> Fact {
    let mut base: Vec<Integer> = s.iter().map(|x| x.abs()).filter(|x| !x.is_zero() && !x.is_one()).collect();
    base.sort();
    base.dedup();
    'outer: loop {
        for i in 0..base.len() {
            for j in i + 1..base.len() {
                let g = base[i].gcd(&base[j]);
                if !g.is_one() {
                    let (a, b) = (base[i].divexact(&g), base[j].divexact(&g));
                    base.remove(j);
                    base.remove(i);
                    base.extend([g, a, b].into_iter().filter(|x| !x.is_one()));
                    base.sort();
                    base.dedup();
                    continue 'outer;
                }
            }
        }
        break;
    }
    base.into_iter()
        .map(|b| {
            let e = s.iter().filter(|x| !x.is_zero()).map(|x| x.remove(&b).0).sum();
            (b, e)
        })
        .collect()
}

fn coprime_basis_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(fact_value(&coprime_basis(&super::ints::ints_of(&a.args[0])?)))
}

/// Primary bucket counts of Magma's hash tables for sets, beyond the
/// initial 11.
const SET_TABLE_SIZES: [u64; 69] = [
    17, 19, 29, 37, 43, 53, 67, 89, 127, 157, 211, 277, 373, 491, 653, 877, 1153, 1543, 2039, 2711, 3607, 4793, 6379, 8501, 11279, 15013, 19949, 26539, 35291,
    46933, 62417, 83009, 110419, 146833, 195311, 259733, 345451, 459443, 611057, 812699, 1080899, 1437577, 1911977, 2542919, 3382103, 4498177, 5982577,
    7956821, 10582571, 14074807, 18719483, 24896917, 33112897, 44040163, 58573399, 77902631, 103610489, 137801941, 183276589, 243757873, 324197953, 431183287,
    574911079, 766548109, 1022064149, 1362752201, 1817002973, 2422670633, 3230227519,
];

fn set_table_size(required: u64) -> u64 {
    if required < 12 { 11 } else { SET_TABLE_SIZES.iter().copied().find(|&b| b >= required).unwrap_or(required) }
}

/// The order in which Magma iterates `Subsets({1..n}, 1)`, as 0-based
/// positions.
///
/// The singletons sit in a chained hash table with `set_table_size(n)`
/// primary buckets B and max(floor(6B/5), B + 1) - B collision nodes; {i}
/// hashes to 1 xor (27 i (i + 11) + 7) mod 2^32. When a collision finds no
/// free node, the table grows to `set_table_size(floor(3B/2))` buckets and
/// takes the old elements in their iteration order before retrying.
/// Iteration visits the buckets in turn, each followed by its chain.
fn singleton_order(n: usize) -> Vec<usize> {
    fn insert(buckets: &mut Vec<Vec<usize>>, collisions: &mut usize, i: usize) {
        let x = i as u32;
        let hash = 1 ^ 27u32.wrapping_mul(x).wrapping_mul(x.wrapping_add(11)).wrapping_add(7);
        loop {
            let b = buckets.len();
            let chain = &mut buckets[hash as usize % b];
            if chain.is_empty() {
                chain.push(i);
                return;
            }
            if *collisions < (b * 6 / 5).max(b + 1) - b {
                chain.push(i);
                *collisions += 1;
                return;
            }
            let old = buckets.concat();
            *buckets = vec![Vec::new(); set_table_size((b + b / 2) as u64) as usize];
            *collisions = 0;
            for y in old {
                insert(buckets, collisions, y);
            }
        }
    }
    let mut buckets = vec![Vec::new(); set_table_size(n as u64) as usize];
    let mut collisions = 0;
    for i in 1..=n {
        insert(&mut buckets, &mut collisions, i);
    }
    buckets.concat().into_iter().map(|i| i - 1).collect()
}

/// Square factors and pairwise coprime cofactors of each integer, using
/// only gcds and exact divisions: Lemma 2.5 of Cremona and Rusin,
/// "Efficient solution of rational conics", Math. Comp. 72 (2003).
///
/// Each subset I of the positions carries a value c_I, starting from
/// c_{i} = |a_i| with the singletons in `singleton_order`. Each sweep visits
/// the pairs I, J of subsets known when it starts; if d = gcd(c_I, c_J) > 1,
/// c_I and c_J are divided by d, c of the symmetric difference (added at the
/// end if new) is multiplied by d, and <d, 2> joins the square part of each
/// position in both I and J. Sweeps repeat until nothing changes. The
/// cofactors of position i are the values c_I > 1 with i in I, in subset
/// order.
fn partial_factorization(s: &[Integer]) -> Vec<(Fact, Fact)> {
    let n = s.len();
    let words = n.div_ceil(64);
    let has = |w: &[u64], k: usize| w[k / 64] >> (k % 64) & 1 == 1;
    let mut supports: Vec<Vec<u64>> = Vec::new();
    let mut values: Vec<Integer> = Vec::new();
    for i in singleton_order(n) {
        let mut w = vec![0u64; words];
        w[i / 64] |= 1 << (i % 64);
        supports.push(w);
        values.push(s[i].abs());
    }
    let mut index: HashMap<Vec<u64>, usize> = supports.iter().cloned().zip(0..).collect();
    let mut f: Vec<Fact> = vec![Fact::new(); n];
    loop {
        let mut changed = false;
        let m = supports.len();
        for i in 0..m {
            for j in i + 1..m {
                if values[i].is_one() {
                    break;
                }
                let d = values[i].gcd(&values[j]);
                if d.is_one() {
                    continue;
                }
                values[i] = values[i].divexact(&d);
                values[j] = values[j].divexact(&d);
                let x: Vec<u64> = supports[i].iter().zip(&supports[j]).map(|(a, b)| a ^ b).collect();
                match index.get(&x) {
                    Some(&k) => values[k] = &values[k] * &d,
                    None => {
                        index.insert(x.clone(), supports.len());
                        supports.push(x);
                        values.push(d.clone());
                    }
                }
                for k in (0..n).filter(|&k| has(&supports[i], k) && has(&supports[j], k)) {
                    match f[k].iter_mut().find(|(y, _)| *y == d) {
                        Some((_, e)) => *e += 2,
                        None => f[k].push((d.clone(), 2)),
                    }
                }
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    f.into_iter()
        .enumerate()
        .map(|(k, fk)| {
            let g = supports.iter().zip(&values).filter(|(w, c)| has(w, k) && !c.is_one()).map(|(_, c)| (c.clone(), 1)).collect();
            (fk, g)
        })
        .collect()
}

fn partial_factorization_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = super::ints::ints_of(&a.args[0])?;
    if s.iter().any(|x| x.is_zero()) {
        return Err(RuntimeError::runtime("The integers must be non-zero"));
    }
    let out: Vec<Value> = partial_factorization(&s)
        .into_iter()
        .map(|(f, g)| Value::seq(None, vec![fact_value(&f), fact_value(&g)]))
        .collect();
    one(Value::seq(None, out))
}

// ----- Cunningham numbers ---------------------------------------------------------------------------------

fn cunningham(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (b, k, c) = (a.int(0)?.clone(), a.int(1)?.clone(), a.int(2)?.clone());
    if b < int(2) || b > int(1073741823) {
        return Err(arg_range(1, &b, 2, 1073741823));
    }
    if k < int(1) || k > int(10000) {
        return Err(arg_range(2, &k, 1, 10000));
    }
    if c != int(1) && c != int(-1) {
        return Err(RuntimeError::runtime("Argument 3 should be -1 or +1"));
    }
    // The primes are only probable primes, as in Magma.
    let mut stages = Stages { proof: false, ..Stages::default() };
    let (mut rng, mut stored) = (Rng::new(1), Vec::new());
    let f = cunningham::factor_power(&b, k.to_u64().unwrap(), c.sign() > 0, &|p| p.is_probable_prime(), &mut |m| {
        stages.factor_general(m, &mut rng, &mut stored).0
    });
    one(fact_value(&sorted_fact(f)))
}

pub fn register(it: &mut Interp) {
    let params = [
        ("Proof", Value::Bool(true)),
        ("Bases", Value::int(20)),
        ("TrialDivisionLimit", Value::int(10000)),
        ("SQUFOFLimit", Value::int(24)),
        ("PollardRhoLimit", Value::int(8191)),
        ("ECMLimit", Value::Undef),
        ("MPQSLimit", Value::Undef),
    ];
    for name in ["Factorization", "Factorisation"] {
        it.def_params(
            name,
            "n::RngIntElt -> RngIntEltFact, RngIntElt, SeqEnum",
            &params,
            "The prime factorization of |n|, the sign of n, and any composites left unfactored.",
            factorization,
        );
    }
    it.def("StoreFactor", "n::RngIntElt", "Store the prime n for Factorization to try first.", store_factor);
    it.def("StoreFactor", "S::[RngIntElt]", "Store the primes in S for Factorization to try first.", store_factor);
    it.def("StoreFactor", "S::{RngIntElt}", "Store the primes in S for Factorization to try first.", store_factor);
    it.def("GetStoredFactors", "-> [RngIntElt]", "The stored factors.", get_stored_factors);
    it.def("ClearStoredFactors", "", "Clear the stored factors.", clear_stored_factors);
    let pb = [("Proof", Value::Bool(true)), ("Bases", Value::int(20))];
    it.def_params(
        "TrialDivision",
        "n::RngIntElt -> RngIntEltFact, RngIntElt",
        &pb,
        "The factorization of the part of |n| made of primes up to 10000, and the rest of |n|.",
        trial_division_fn,
    );
    it.def_params(
        "TrialDivision",
        "n::RngIntElt, B::RngIntElt -> RngIntEltFact, RngIntElt",
        &pb,
        "The factorization of the part of |n| made of primes up to B, and the rest of |n|.",
        trial_division_fn,
    );
    it.def_params(
        "PollardRho",
        "n::RngIntElt -> RngIntEltFact, [RngIntElt]",
        &pb,
        "Factor n by Pollard's rho method: the factorization found and the composites left.",
        pollard_rho_fn,
    );
    it.def_params(
        "PollardRho",
        "n::RngIntElt, c::RngIntElt, s::RngIntElt, k::RngIntElt -> RngIntEltFact, [RngIntElt]",
        &pb,
        "Factor n by Pollard's rho method iterating x^2 + c k times from s.",
        pollard_rho_fn,
    );
    it.def_params("SQUFOF", "n::RngIntElt -> RngIntEltFact, [RngIntElt]", &pb, "Factor n by Shanks's square form factorization.", squfof_fn);
    it.def_params(
        "SQUFOF",
        "n::RngIntElt, k::RngIntElt -> RngIntEltFact, [RngIntElt]",
        &pb,
        "Factor n by Shanks's square form factorization with at most k iterations.",
        squfof_fn,
    );
    let pm = [("x0", Value::Undef), ("B2", Value::Undef), ("k", Value::Undef), ("Sigma", Value::Undef)];
    it.def_params(
        "pMinus1",
        "n::RngIntElt, B1::RngIntElt -> RngIntElt, RngIntElt",
        &pm,
        "A factor of n found by Pollard's p - 1 method, and its x0; or 0.",
        p_minus_1_fn,
    );
    it.def_params("pPlus1", "n::RngIntElt, B1::RngIntElt -> RngIntElt", &pm, "A factor of n found by Williams's p + 1 method, or 0.", p_plus_1_fn);
    it.def_params(
        "ECM",
        "n::RngIntElt, B1::RngIntElt -> RngIntElt, RngIntElt",
        &[("Sigma", Value::Undef), ("x0", Value::Undef), ("B2", Value::Undef), ("k", Value::Undef)],
        "A factor of n found by one elliptic curve (Suyama's parametrization), and its sigma; or 0.",
        ecm_fn,
    );
    it.def(
        "ECMSteps",
        "n::RngIntElt, L::RngIntElt, U::RngIntElt -> RngIntElt, RngIntElt",
        "A factor of n found by ECM with B1 growing from L to U, and its sigma; or 0.",
        ecm_steps,
    )
    .package = true;
    it.def_params("MPQS", "n::RngIntElt -> RngIntEltFact, [RngIntElt]", &pb, "Factor n by the quadratic sieve.", mpqs);
    it.def("ECMOrder", "p::RngIntElt, s::RngIntElt -> RngIntElt", "The order of the ECM curve for sigma = s modulo the prime p.", ecm_order);
    it.def(
        "ECMFactoredOrder",
        "p::RngIntElt, s::RngIntElt -> RngIntEltFact",
        "The factored order of the ECM curve for sigma = s modulo the prime p.",
        ecm_factored_order,
    );
    it.def("CoprimeBasis", "S::[RngIntElt] -> RngIntEltFact", "A factorization sequence of pairwise coprime bases for the product of S.", coprime_basis_fn);
    it.def("CoprimeBasis", "S::{RngIntElt} -> RngIntEltFact", "A factorization sequence of pairwise coprime bases for the product of S.", coprime_basis_fn);
    it.def(
        "PartialFactorization",
        "S::[RngIntElt] -> [RngIntEltFact]",
        "Square factors and coprime cofactors of the integers in S, found with gcds only.",
        partial_factorization_fn,
    );
    it.def("Cunningham", "b::RngIntElt, k::RngIntElt, c::RngIntElt -> RngIntEltFact", "The factorization of b^k + c for c = 1 or -1.", cunningham);
}

#[cfg(test)]
mod tests {
    use super::super::factseq::fact_int;
    use super::*;

    #[test]
    fn squfof_in_words_matches_big_integers() {
        let mut x = 0x1234_5678_9abc_def1u64;
        for bits in [20u32, 40, 60, 80, 100, 120] {
            for _ in 0..20 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let n = if bits < 64 { Integer::from_u64((x >> (64 - bits)) | 1) } else { &(&Integer::from_u64(x | 1) * &int(2).pow((bits - 64) as u64)) + &int(1) };
                for k in [1i64, 3, 1155] {
                    let kn = &n * &int(k);
                    let Some(w) = kn.to_i128().filter(|&v| v < 1 << 125) else { continue };
                    assert_eq!(squfof_word(w, 5000).map(Integer::from_i128), squfof_big(&kn, 5000), "{n} * {k}");
                }
            }
        }
    }

    #[test]
    fn stages_respect_the_limits() {
        let (p, q) = (int(100000000000031), int(300000000000089));
        let n = &p * &q;
        let mut rng = crate::random::Rng::new(1);
        // Both ECM and MPQS bounded: nothing splits a 29-digit semiprime.
        let mut bounded = Stages { ecm: Some(0), mpqs: Some(0), ..Stages::default() };
        assert_eq!(split_with(&n, true, &mut |x: &Integer| bounded.split(x, &mut rng, &[]).map(|r| r.0)), (Fact::new(), vec![n.clone()]));
        assert_eq!(split_with(&n.pow(2), true, &mut |x: &Integer| bounded.split(x, &mut rng, &[]).map(|r| r.0)).1, vec![n.clone(), n.clone()]);
        // A stored factor splits it all the same.
        let stored = [int(1000003), q.clone()];
        assert_eq!(split_with(&n, true, &mut |x: &Integer| bounded.split(x, &mut rng, &stored).map(|r| r.0)), (vec![(p.clone(), 1), (q.clone(), 1)], vec![]));
        // Either one unbounded: the factorization is complete.
        for (ecm, mpqs) in [(None, Some(0)), (Some(0), None), (None, None)] {
            let mut stages = Stages { ecm, mpqs, ..Stages::default() };
            let (f, rest) = split_with(&n, true, &mut |x: &Integer| stages.split(x, &mut rng, &[]).map(|r| r.0));
            assert_eq!(f, vec![(p.clone(), 1), (q.clone(), 1)]);
            assert!(rest.is_empty());
        }
        // SQUFOF alone splits 24 digits.
        let m = &int(300000000077) * &int(700000000009);
        let mut squfof_only = Stages { rho: 0, ecm: Some(0), mpqs: Some(0), ..Stages::default() };
        assert!(split_with(&m, true, &mut |x: &Integer| squfof_only.split(x, &mut rng, &[]).map(|r| r.0)).1.is_empty());
    }

    /// A xorshift generator, so that the cases are the same on every run.
    fn next(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }

    /// A random factorization: up to four primes, of 2 to `bits` bits, with
    /// exponents up to 3.
    fn random_fact(s: &mut u64, bits: u32) -> Fact {
        let mut f = Fact::new();
        for _ in 0..next(s) % 5 {
            let b = 2 + next(s) as u32 % (bits - 1);
            f = super::super::factseq::fact_mul(&f, &vec![(Integer::from_u64(next(s) >> (64 - b)).next_prime(), 1 + next(s) % 3)]).unwrap();
        }
        f
    }

    #[test]
    fn trial_division_splits_off_the_primes_up_to_the_bound() {
        let mut s = 0x9e37_79b9_7f4a_7c15;
        for i in 0..600 {
            let f = random_fact(&mut s, [8, 14, 20, 40][i % 4]);
            let n = &fact_int(&f) * &int([1, -1][i % 2]);
            let bound = [1u64, 2, 3, 10, 97, 100, 1000, 10000, 70000][i % 9];
            let (g, r) = trial_division(&n, bound);
            assert_eq!(&fact_int(&g) * &r, n.abs(), "TrialDivision({n}, {bound})");
            let small: Fact = f.iter().filter(|(p, _)| p.to_u64().is_some_and(|p| p <= bound)).cloned().collect();
            assert_eq!(g, small, "TrialDivision({n}, {bound})");
        }
    }

    #[test]
    fn the_stages_factor_completely() {
        let mut stages = Stages::default();
        let mut rng = crate::random::Rng::new(7);
        let mut s = 0x2545_f491_4f6c_dd1d;
        for i in 0..150 {
            let f = random_fact(&mut s, [16, 24, 32, 48][i % 4]);
            let n = fact_int(&f);
            let (g, rest) = split_with(&n, true, &mut |x: &Integer| stages.split(x, &mut rng, &[]).map(|r| r.0));
            assert!(rest.is_empty() && g == f, "Factorization({n})");
        }
    }

    #[test]
    fn coprime_bases_are_coprime_and_generate() {
        let mut s = 0x0123_4567_89ab_cdef;
        for i in 0..400 {
            // Products of a few shared factors, so that the elements meet.
            let shared: Vec<Integer> = (0..4).map(|_| int(2 + (next(&mut s) % 60) as i64)).collect();
            let xs: Vec<Integer> = (0..1 + i % 5).map(|_| (0..3).fold(int(1), |x, _| &x * &shared[next(&mut s) as usize % 4])).collect();
            let basis = coprime_basis(&xs);
            for (j, (b, _)) in basis.iter().enumerate() {
                assert!(*b > int(1) && basis[j + 1..].iter().all(|(c, _)| b.gcd(c).is_one()), "CoprimeBasis({xs:?})");
            }
            for x in &xs {
                let rest = basis.iter().fold(x.clone(), |x, (b, _)| x.remove(b).1);
                assert!(rest.is_one(), "CoprimeBasis({xs:?}) leaves {rest} of {x}");
            }
        }
    }

    #[test]
    fn partial_factorizations_multiply_back() {
        let mut s = 0x1357_9bdf_2468_ace0;
        for i in 0..300 {
            let shared: Vec<Integer> = (0..5).map(|_| Integer::from_u64(next(&mut s) >> 40).next_prime()).collect();
            let xs: Vec<Integer> = (0..1 + i % 6).map(|_| (0..1 + next(&mut s) % 4).fold(int(1), |x, _| &x * &shared[next(&mut s) as usize % 5])).collect();
            let pf = partial_factorization(&xs);
            let mut cofactors: Vec<Integer> = Vec::new();
            for (x, (squares, rest)) in xs.iter().zip(&pf) {
                assert!(squares.iter().all(|(_, e)| e % 2 == 0), "PartialFactorization({xs:?})");
                assert_eq!(&fact_int(squares) * &fact_int(rest), x.abs(), "PartialFactorization({xs:?})");
                cofactors.extend(rest.iter().map(|(c, _)| c.clone()));
            }
            cofactors.sort();
            cofactors.dedup();
            for (j, c) in cofactors.iter().enumerate() {
                assert!(cofactors[j + 1..].iter().all(|d| c.gcd(d).is_one()), "PartialFactorization({xs:?})");
            }
        }
    }

    #[test]
    fn cyclotomic_values_multiply_to_powers_less_one() {
        for b in 2..=12u64 {
            let b = Integer::from_u64(b);
            for k in 1..=40u64 {
                let product = super::super::factseq::divisors_of(&factor(&Integer::from_u64(k)))
                    .iter()
                    .fold(int(1), |t, d| &t * &cunningham::cyclotomic_value(d.to_u64().unwrap(), &b));
                assert_eq!(product, &b.pow(k) - &int(1), "{b}^{k} - 1");
            }
        }
    }
}
