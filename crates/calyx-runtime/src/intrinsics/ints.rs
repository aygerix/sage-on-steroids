//! Integer and rational number intrinsics (FLINT-backed): arithmetic of
//! elements, gcds, digits, predicates and random integers.

use std::rc::Rc;

use calyx_flint::{Integer, Rational};

use super::numtheory::{prime_test, proof};
use super::{arg_ge, arg_not, boolv, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn int_arg(a: &CallArgs, i: usize) -> RResult<Integer> {
    match &a.args[i] {
        Value::Int(n) => Ok(n.clone()),
        Value::Rat(q) if q.is_integral() => Ok(q.numerator()),
        other => Err(RuntimeError::runtime(format!("Argument {} must be an integer (got {})", i + 1, crate::value_kind(other)))),
    }
}

fn rat_arg(a: &CallArgs, i: usize) -> RResult<Rational> {
    match &a.args[i] {
        Value::Int(n) => Ok(Rational::from_integer(n)),
        Value::Rat(q) => Ok((**q).clone()),
        other => Err(RuntimeError::runtime(format!("Argument {} must be rational (got {})", i + 1, crate::value_kind(other)))),
    }
}

fn int_seq(v: Vec<Integer>) -> Value {
    Value::int_seq(v)
}

/// A factorization as a sequence of `<p, e>` tuples.
pub fn factorization_value(factors: &[(Integer, u64)]) -> Value {
    super::factseq::fact_value(factors)
}

/// The integers of a sequence or set argument.
pub fn ints_of(v: &Value) -> RResult<Vec<Integer>> {
    let elems: Vec<Value> = match v {
        Value::Seq(s) => s.elems.clone(),
        Value::Set(s) => s.iter().collect(),
        _ => return Err(RuntimeError::runtime("Bad argument types")),
    };
    elems
        .into_iter()
        .map(|e| match e {
            Value::Int(n) => Ok(n),
            _ => Err(RuntimeError::runtime("Bad argument types")),
        })
        .collect()
}

fn abs(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(match &a.args[0] {
        Value::Int(n) => Value::Int(n.abs()),
        Value::Rat(q) => Value::rat(q.abs()),
        Value::Real(r) => Value::Real(Rc::new(RealV { x: r.x.abs(), fixed: r.fixed })),
        _ => unreachable!(),
    })
}

fn sign(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = match &a.args[0] {
        Value::Int(n) => n.sign(),
        Value::Rat(q) => q.sign(),
        Value::Real(r) => r.x.sign(),
        _ => unreachable!(),
    };
    one(Value::int(s as i64))
}

fn is_zero(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(match &a.args[0] {
        Value::Int(n) => n.is_zero(),
        Value::Rat(q) => q.is_zero(),
        Value::Real(r) => r.x.is_zero(),
        _ => false,
    })
}

fn is_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(match &a.args[0] {
        Value::Int(n) => n.is_one(),
        Value::Rat(q) => q.is_one(),
        _ => false,
    })
}

fn is_minus_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(match &a.args[0] {
        Value::Int(n) => n.to_i64() == Some(-1),
        Value::Rat(q) => q.is_integral() && q.numerator().to_i64() == Some(-1),
        _ => false,
    })
}

fn is_even(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(a.int(0)?.is_even())
}

fn is_odd(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(a.int(0)?.is_odd())
}

fn is_regular(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(!a.int(0)?.is_zero())
}

fn is_single_precision(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(a.int(0)?.abs() < Integer::from_i64(1 << 30))
}

/// The ring-theoretic functions that are the identity (or absolute value)
/// on the integers.
fn identity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(a.args[0].clone())
}

fn minimal_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.clone();
    let px = it.poly_ring(&Value::integers(), true)?;
    one(it.coerce(&px, &Value::int_seq([-n, Integer::one()]))?)
}

fn eltseq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(int_seq(vec![a.int(0)?.clone()]))
}

// ----- division -----------------------------------------------------------------

fn quotrem(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (q, r) = a.int(0)?.fdiv_qr(a.int(1)?).ok_or_else(|| RuntimeError::runtime("Division by zero"))?;
    Ok(vals![Value::Int(q), Value::Int(r)])
}

fn exact_quotient(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, d) = (a.int(0)?, a.int(1)?);
    if d.is_zero() {
        return Err(RuntimeError::runtime("Division by zero"));
    }
    if !n.is_divisible_by(d) {
        return Err(RuntimeError::runtime("Argument 1 is not exactly divisible by argument 2"));
    }
    intv(n.divexact(d))
}

fn is_divisible_by(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, d) = (a.int(0)?, a.int(1)?);
    if d.is_zero() {
        return Err(RuntimeError::runtime("Division by zero"));
    }
    let yes = n.is_divisible_by(d);
    // The quotient is returned only when asked for.
    if a.nresults < 2 {
        return boolv(yes);
    }
    Ok(vals![Value::Bool(yes), if yes { Value::Int(n.divexact(d)) } else { Value::Undef }])
}

/// Argument 2 as a shift: small (below 2^30 in absolute value, whatever the
/// number shifted) and non-negative, as Magma requires.
fn shift_arg(a: &CallArgs) -> RResult<u64> {
    let b = a.int(1)?;
    if b.abs() >= Integer::from_u64(1 << 30) {
        return Err(RuntimeError::runtime(format!("Argument 2 ({b}) is too large")));
    }
    a.small_ge(1, 0)
}

fn shift_left(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let b = shift_arg(a)?;
    intv(a.int(0)?.mul_2exp(b))
}

fn shift_right(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let b = shift_arg(a)?;
    intv(a.int(0)?.fdiv_2exp(b))
}

fn mod_by_power_of_2(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let b = shift_arg(a)?;
    let n = a.int(0)?;
    intv(n - &n.fdiv_2exp(b).mul_2exp(b))
}

fn bitwise_not(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(a.int(0)?.bitnot())
}

fn bitwise_and(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(a.int(0)?.bitand(a.int(1)?))
}

fn bitwise_or(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(a.int(0)?.bitor(a.int(1)?))
}

fn bitwise_xor(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(a.int(0)?.bitxor(a.int(1)?))
}

// ----- gcd and lcm ----------------------------------------------------------------

fn gcd(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y) = (rat_arg(a, 0)?, rat_arg(a, 1)?);
    if x.is_integral() && y.is_integral() {
        return intv(x.numerator().gcd(&y.numerator()));
    }
    // gcd of rationals: gcd of numerators over lcm of denominators.
    let n = x.numerator().gcd(&y.numerator());
    let d = x.denominator().lcm(&y.denominator());
    one(Value::rat(Rational::new(&n, &d).unwrap()))
}

fn null_seq() -> RuntimeError {
    RuntimeError::runtime("Illegal null set/sequence")
}

fn gcd_seq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = ints_of(&a.args[0])?;
    if s.is_empty() {
        return Err(null_seq());
    }
    intv(s.iter().fold(Integer::zero(), |g, n| g.gcd(n)))
}

fn lcm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(int_arg(a, 0)?.lcm(&int_arg(a, 1)?))
}

fn lcm_seq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = ints_of(&a.args[0])?;
    if s.is_empty() {
        return Err(null_seq());
    }
    intv(s.iter().fold(Integer::one(), |l, n| l.lcm(n)))
}

fn xgcd(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (g, s, t) = a.int(0)?.xgcd(a.int(1)?);
    Ok(vals![Value::Int(g), Value::Int(s), Value::Int(t)])
}

/// `x / y` rounded to the nearest integer (halves upwards).
fn round_div(x: &Integer, y: &Integer) -> Integer {
    let two = Integer::from_i64(2);
    let (q, _) = (&(&two * x) + y).fdiv_qr(&(&two * y)).unwrap();
    q
}

/// The extended gcd of a sequence: the gcd and small multipliers, found by
/// lattice reduction of the identity basis weighted by the integers
/// (Havas, Majewski and Matthews).
pub fn xgcd_seq_of(a: &[Integer]) -> (Integer, Vec<Integer>) {
    let m = a.len();
    if a.iter().all(|x| x.is_zero()) {
        return (Integer::zero(), vec![Integer::zero(); m]);
    }
    let mut a = a.to_vec();
    let mut b: Vec<Vec<Integer>> = (0..m).map(|i| (0..m).map(|j| Integer::from_i64((i == j) as i64)).collect()).collect();
    let mut lam = vec![vec![Integer::zero(); m]; m];
    let mut d = vec![Integer::one(); m + 1];
    // Indices below are 1-based as in the published algorithm.
    let reduce = |k: usize, i: usize, a: &mut Vec<Integer>, b: &mut Vec<Vec<Integer>>, lam: &mut Vec<Vec<Integer>>, d: &Vec<Integer>| {
        let q = if !a[i - 1].is_zero() {
            round_div(&a[k - 1], &a[i - 1])
        } else if &Integer::from_i64(2) * &lam[k - 1][i - 1].abs() > d[i] {
            round_div(&lam[k - 1][i - 1], &d[i])
        } else {
            Integer::zero()
        };
        if !q.is_zero() {
            let bi = b[i - 1].clone();
            for (x, y) in b[k - 1].iter_mut().zip(&bi) {
                *x = &*x - &(&q * y);
            }
            a[k - 1] = &a[k - 1] - &(&q * &a[i - 1]);
            lam[k - 1][i - 1] = &lam[k - 1][i - 1] - &(&q * &d[i]);
            for j in 1..i {
                lam[k - 1][j - 1] = &lam[k - 1][j - 1] - &(&q * &lam[i - 1][j - 1]);
            }
        }
    };
    let mut k = 2;
    while k <= m {
        reduce(k, k - 1, &mut a, &mut b, &mut lam, &d);
        let swap = !a[k - 2].is_zero()
            || (a[k - 1].is_zero()
                && &Integer::from_i64(4) * &(&(&d[k - 2] * &d[k]) + &(&lam[k - 1][k - 2] * &lam[k - 1][k - 2]))
                    < &Integer::from_i64(3) * &(&d[k - 1] * &d[k - 1]));
        if swap {
            a.swap(k - 1, k - 2);
            b.swap(k - 1, k - 2);
            for j in 1..k - 1 {
                let t = lam[k - 1][j - 1].clone();
                lam[k - 1][j - 1] = std::mem::replace(&mut lam[k - 2][j - 1], t);
            }
            let l = lam[k - 1][k - 2].clone();
            let bb = (&(&d[k - 2] * &d[k]) + &(&l * &l)).divexact(&d[k - 1]);
            for i in k + 1..=m {
                let t = lam[i - 1][k - 1].clone();
                lam[i - 1][k - 1] = (&(&d[k] * &lam[i - 1][k - 2]) - &(&l * &t)).divexact(&d[k - 1]);
                lam[i - 1][k - 2] = (&(&bb * &t) + &(&l * &lam[i - 1][k - 1])).divexact(&d[k]);
            }
            d[k - 1] = bb;
            if k > 2 {
                k -= 1;
            }
        } else {
            for i in (1..=k - 2).rev() {
                reduce(k, i, &mut a, &mut b, &mut lam, &d);
            }
            k += 1;
        }
    }
    let mut g = a[m - 1].clone();
    let mut x = b[m - 1].clone();
    if g.sign() < 0 {
        g = -g;
        x = x.into_iter().map(|v| -v).collect();
    }
    (g, x)
}

fn xgcd_seq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = ints_of(&a.args[0])?;
    let (g, x) = xgcd_seq_of(&s);
    Ok(vals![Value::Int(g), int_seq(x)])
}

// ----- roots, powers and logarithms ---------------------------------------------

fn isqrt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match a.int(0)?.isqrt() {
        Some(r) => intv(r),
        None => Err(arg_not(1, "non-negative")),
    }
}

fn iroot(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int_ge(0, 1)?;
    let k = a.small_ge(1, 2)?;
    intv(n.root(k).unwrap().0)
}

fn is_square(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match &a.args[0] {
        Value::Int(n) => {
            if n.sign() >= 0 && n.is_square() {
                Ok(vals![Value::Bool(true), Value::Int(n.isqrt().unwrap())])
            } else {
                Ok(vals![Value::Bool(false), Value::Undef])
            }
        }
        Value::Rat(q) => {
            let (n, d) = (q.numerator(), q.denominator());
            if n.sign() >= 0 && n.is_square() && d.is_square() {
                Ok(vals![Value::Bool(true), Value::rat(Rational::new(&n.isqrt().unwrap(), &d.isqrt().unwrap()).unwrap())])
            } else {
                Ok(vals![Value::Bool(false), Value::Undef])
            }
        }
        _ => unreachable!(),
    }
}

fn is_power(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    if a.args.len() == 2 {
        let n = a.int(0)?.clone();
        let no = Ok(vals![Value::Bool(false), Value::Undef]);
        let k = a.int(1)?;
        if k.sign() <= 0 {
            return no;
        }
        let Some(k) = k.to_u64() else { return no };
        if n.sign() < 0 && k % 2 == 0 {
            return no;
        }
        return match n.abs().root(k) {
            Some((r, true)) => Ok(vals![Value::Bool(true), Value::Int(if n.sign() < 0 { -r } else { r })]),
            _ => no,
        };
    }
    let n = a.int_ge(0, 2)?;
    match n.perfect_power() {
        Some((b, e)) => Ok(vals![Value::Bool(true), Value::Int(b), Value::Int(Integer::from_u64(e))]),
        None => Ok(vals![Value::Bool(false), Value::Undef, Value::Undef]),
    }
}

fn is_squarefree(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?;
    if n.is_zero() {
        return Err(arg_not(1, "non-zero"));
    }
    boolv(it.factor_int(n).iter().all(|(_, e)| *e == 1))
}

fn squarefree_factorization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?;
    if n.is_zero() {
        return Err(arg_not(1, "non-zero"));
    }
    let (x, y) = super::factseq::squarefree_split(&it.factor_int(n));
    let x = super::factseq::fact_int(&x);
    Ok(vals![Value::Int(if n.sign() < 0 { -x } else { x }), Value::Int(super::factseq::fact_int(&y))])
}

fn valuation(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, p) = (a.int(0)?.clone(), a.int(1)?.clone());
    valuation_of(&n, &p, a.nresults)
}

/// The valuation v of n at the prime p, and n/p^v when `nresults` asks for
/// it (Infinity and 0 for n = 0).
pub(super) fn valuation_of(n: &Integer, p: &Integer, nresults: usize) -> RResult<Vals> {
    if p.sign() <= 0 {
        return Err(arg_not(2, "positive"));
    }
    if !p.is_prime() {
        return Err(super::arg_prime(2, p));
    }
    let (v, rest) = match n.is_zero() {
        true => (Value::Infinity(true), Integer::zero()),
        false => {
            let (v, rest) = n.remove(p);
            (Value::Int(Integer::from_u64(v)), rest)
        }
    };
    if nresults < 2 {
        return Ok(vals![v]);
    }
    Ok(vals![v, Value::Int(rest)])
}

fn ilog(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let b = a.int_ge(0, 2)?;
    let n = a.int_ge(1, 1)?;
    // Count the divisions by b that stay above 1.
    if let Some(b) = b.to_u64() {
        return intv(Integer::from_u64(n.ilog(b).unwrap()));
    }
    let mut k = 0u64;
    let mut p = b.clone();
    while p <= n {
        p = &p * &b;
        k += 1;
    }
    intv(Integer::from_u64(k))
}

fn ilog2(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int_ge(0, 1)?;
    intv(Integer::from_u64(n.bits() - 1))
}

// ----- digits -------------------------------------------------------------------

fn intseq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int_ge(0, 0)?;
    let b = if a.args.len() > 1 { a.int_ge(1, 2)? } else { Integer::from_i64(10) };
    let mut digits = Vec::new();
    let mut m = n;
    while !m.is_zero() {
        let (q, r) = m.fdiv_qr(&b).unwrap();
        digits.push(r);
        m = q;
    }
    if a.args.len() > 2 {
        // Pad with zeros to length k; a smaller k is ignored.
        let k = a.int(2)?.to_u64().unwrap_or(0) as usize;
        if digits.len() < k {
            digits.resize(k, Integer::zero());
        }
    }
    one(int_seq(digits))
}

fn seqint(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.seq(0)?.clone();
    let b = if a.args.len() > 1 { a.int_ge(1, 2)? } else { Integer::from_i64(10) };
    let mut n = Integer::zero();
    for (i, v) in s.elems.iter().enumerate().rev() {
        let Value::Int(d) = v else {
            return Err(RuntimeError::runtime("Bad argument types"));
        };
        if d.sign() < 0 || *d >= b {
            return Err(RuntimeError::runtime(format!("Sequence digit {} should be >= 0 and < {b}", i + 1)));
        }
        n = &(&n * &b) + d;
    }
    intv(n)
}

// ----- maxima -------------------------------------------------------------------

/// Maximum and Minimum of two values are not defined on ring elements, even
/// where `lt` is.
fn check_max_args(it: &Interp, x: &Value, y: &Value) -> RResult<()> {
    if matches!(x, Value::Elt(_) | Value::Small(..)) || matches!(y, Value::Elt(_) | Value::Small(..)) {
        return Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}, {}", it.type_name_ext(x), it.type_name_ext(y))));
    }
    Ok(())
}

fn max2(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y) = (a.args[0].clone(), a.args[1].clone());
    check_max_args(it, &x, &y)?;
    let o = it.compare_for_sort(&x, &y)?;
    let r = if o == std::cmp::Ordering::Less { y.clone() } else { x.clone() };
    one(in_common_structure(it, &x, &y, r)?)
}

/// `r` (one of x and y) in the structure containing both, as Maximum and
/// Minimum return it (so `Max(1.5, 2)` is a real).
fn in_common_structure(it: &mut Interp, x: &Value, y: &Value, r: Value) -> RResult<Value> {
    let (px, py) = (it.parent_of(x)?, it.parent_of(y)?);
    match it.common_universe(&px, &py) {
        Some(u) => Ok(it.try_coerce(&u, &r)?.unwrap_or(r)),
        None => Ok(r),
    }
}

fn min2(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y) = (a.args[0].clone(), a.args[1].clone());
    check_max_args(it, &x, &y)?;
    let o = it.compare_for_sort(&x, &y)?;
    let r = if o == std::cmp::Ordering::Greater { y.clone() } else { x.clone() };
    one(in_common_structure(it, &x, &y, r)?)
}

// ----- rationals ----------------------------------------------------------------

fn numerator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(rat_arg(a, 0)?.numerator())
}

fn denominator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(rat_arg(a, 0)?.denominator())
}

fn floor(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(match &a.args[0] {
        Value::Int(n) => n.clone(),
        Value::Rat(q) => q.floor(),
        Value::Real(r) => r.x.floor(),
        _ => unreachable!(),
    })
}

fn ceiling(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(match &a.args[0] {
        Value::Int(n) => n.clone(),
        Value::Rat(q) => q.ceil(),
        Value::Real(r) => r.x.ceil(),
        _ => unreachable!(),
    })
}

fn round(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(match &a.args[0] {
        Value::Int(n) => n.clone(),
        Value::Rat(q) => q.round(),
        Value::Real(r) => r.x.round(),
        _ => unreachable!(),
    })
}

fn truncate(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(match &a.args[0] {
        Value::Int(n) => n.clone(),
        Value::Rat(q) => q.trunc(),
        Value::Real(r) => r.x.trunc(),
        _ => unreachable!(),
    })
}

fn is_integral(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(match &a.args[0] {
        Value::Int(_) => true,
        Value::Rat(q) => q.is_integral(),
        _ => false,
    })
}

// ----- random integers -------------------------------------------------------------

fn random_range(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (lo, hi) = (a.int(0)?.clone(), a.int(1)?.clone());
    if lo > hi {
        return Err(RuntimeError::runtime(format!("Argument 2 ({hi}) should be >= argument 1 ({lo})")));
    }
    intv(it.rng.range(&lo, &hi))
}

fn random_upto(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let hi = a.int_ge(0, 0)?;
    intv(it.rng.range(&Integer::zero(), &hi))
}

/// A random integer with `n` bits (below 2^n).
fn random_bits_of(it: &mut Interp, n: u64) -> Integer {
    if n == 0 {
        return Integer::zero();
    }
    it.rng.below(&Integer::one().mul_2exp(n))
}

fn random_bits(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?;
    if n.sign() < 0 {
        // Magma numbers this argument 0.
        return Err(arg_ge(0, n, 0));
    }
    let n = a.small_ge(0, 0)?;
    intv(random_bits_of(it, n))
}

fn random_prime(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let proof = proof(it, a)?;
    // n is small and non-negative (positive with a congruence).
    let n = a.int_ge(0, if a.args.len() == 1 { 0 } else { 1 })?;
    let n = n.to_u64().filter(|&n| n < 1 << 30).ok_or_else(|| super::arg_le(1, &n, (1 << 30) - 1))?;
    let bound = Integer::one().mul_2exp(n);
    if a.args.len() == 1 {
        // There are no primes below 2^0 or 2^1.
        if n < 2 {
            return intv(Integer::zero());
        }
        loop {
            let p = it.rng.below(&bound);
            if prime_test(&p, proof) {
                return intv(p);
            }
        }
    }
    let (r, m, tries) = (a.int(1)?.clone(), a.int(2)?.clone(), a.int(3)?.clone());
    if r >= m || m.sign() <= 0 || r.sign() < 0 {
        return Err(RuntimeError::runtime("a must be less than b"));
    }
    let tries = tries.to_u64().unwrap_or(0);
    // Primes below 2^n congruent to r mod m: r + m*k with k < (2^n - r)/m.
    let count = (&bound - &r).cdiv_q(&m).unwrap_or_else(Integer::zero);
    if count.sign() > 0 {
        for _ in 0..tries {
            let p = &r + &(&m * &it.rng.below(&count));
            if prime_test(&p, proof) {
                return Ok(vals![Value::Bool(true), Value::Int(p)]);
            }
        }
    }
    Ok(vals![Value::Bool(false), Value::Undef])
}

fn random_consecutive_bits(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.clone();
    if n.sign() <= 0 {
        return Err(arg_ge(1, &n, 0));
    }
    let n = a.small_ge(0, 1)?;
    let lo = a.int(1)?.clone();
    let hi = a.int(2)?.clone();
    if lo.sign() < 0 || lo > hi {
        return Err(super::arg_range(2, &lo, 0, &hi));
    }
    let (lo, hi) = (lo.to_u64().unwrap_or(0), hi.to_u64().unwrap_or(u64::MAX).min(n));
    // Runs of ones and zeros, alternating from a random start, each of a
    // random length in [lo .. hi].
    let mut bit = it.rng.below_u64(2) == 1;
    let mut x = Integer::zero();
    let mut len = 0u64;
    while len < n {
        let run = (lo + it.rng.below_u64(hi - lo + 1)).max(1).min(n - len);
        if bit {
            let ones = &Integer::one().mul_2exp(run) - &Integer::one();
            x = &x + &ones.mul_2exp(len);
        }
        len += run;
        bit = !bit;
    }
    intv(x)
}

fn integers(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::integers())
}

fn identity_z(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::one())
}

fn field_of_fractions(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::rationals())
}

fn signature(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    Ok(vals![Value::int(1), Value::int(0)])
}

pub fn register(it: &mut Interp) {
    it.def("RingOfIntegers", "-> RngInt", "The ring of integers.", integers);
    for name in ["IntegerRing", "Integers", "RingOfIntegers"] {
        it.def(name, "Q::FldRat -> RngInt", "The ring of integers of the rational field.", integers);
    }
    it.def("Identity", "Z::RngInt -> RngIntElt", "The identity 1 of Z.", identity_z);
    it.def("FieldOfFractions", "Z::RngInt -> FldRat", "The field of fractions of Z, the rational field.", field_of_fractions);
    it.def("Signature", "Z::RngInt -> RngIntElt, RngIntElt", "The signature 1, 0 of Z as an order of the rationals.", signature);
    for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
        it.def("Abs", &format!("x::{t} -> {t}"), "The absolute value of x.", abs);
        it.def("AbsoluteValue", &format!("x::{t} -> {t}"), "The absolute value of x.", abs);
        it.def("Sign", &format!("x::{t} -> RngIntElt"), "The sign of x (-1, 0 or 1).", sign);
        it.def("IsZero", &format!("x::{t} -> BoolElt"), "Whether x is zero.", is_zero);
        it.def("Floor", &format!("x::{t} -> RngIntElt"), "The largest integer not exceeding x.", floor);
        it.def("Ceiling", &format!("x::{t} -> RngIntElt"), "The smallest integer not less than x.", ceiling);
        it.def("Round", &format!("x::{t} -> RngIntElt"), "The integer nearest to x (halves away from zero).", round);
        it.def("Truncate", &format!("x::{t} -> RngIntElt"), "The integer part of x.", truncate);
    }
    for t in ["RngIntElt", "FldRatElt"] {
        it.def("IsOne", &format!("x::{t} -> BoolElt"), "Whether x is one.", is_one);
        it.def("IsMinusOne", &format!("x::{t} -> BoolElt"), "Whether x is minus one.", is_minus_one);
        it.def("Numerator", &format!("x::{t} -> RngIntElt"), "The numerator of x.", numerator);
        it.def("Denominator", &format!("x::{t} -> RngIntElt"), "The denominator of x.", denominator);
        it.def("IsSquare", &format!("x::{t} -> BoolElt, {t}"), "Whether x is a square, and a square root.", is_square);
        it.def("IsIntegral", &format!("x::{t} -> BoolElt"), "Whether x is an integer.", is_integral);
    }
    it.def("IsEven", "n::RngIntElt -> BoolElt", "Whether n is even.", is_even);
    it.def("IsOdd", "n::RngIntElt -> BoolElt", "Whether n is odd.", is_odd);
    it.def("IsRegular", "n::RngIntElt -> BoolElt", "Whether n is not a zero divisor (is non-zero).", is_regular);
    it.def("IsSinglePrecision", "n::RngIntElt -> BoolElt", "Whether |n| < 2^30.", is_single_precision);
    for name in ["ComplexConjugate", "Conjugate", "Norm", "Trace"] {
        it.def(name, "n::RngIntElt -> RngIntElt", "n itself (the integers are their own conjugates, norms and traces).", identity);
    }
    it.def("EuclideanNorm", "n::RngIntElt -> RngIntElt", "The Euclidean norm |n| of n.", abs);
    it.def("MinimalPolynomial", "n::RngIntElt -> RngUPolElt", "The minimal polynomial x - n of n over the integers.", minimal_polynomial);
    for name in ["Eltseq", "ElementToSequence"] {
        it.def(name, "n::RngIntElt -> [RngIntElt]", "The sequence [n].", eltseq);
    }

    it.def(
        "Quotrem",
        "a::RngIntElt, b::RngIntElt -> RngIntElt, RngIntElt",
        "The quotient q = a div b and remainder r = a mod b (with the sign of b).",
        quotrem,
    );
    it.def("ExactQuotient", "a::RngIntElt, b::RngIntElt -> RngIntElt", "The quotient a/b, where b divides a.", exact_quotient);
    it.def("IsDivisibleBy", "n::RngIntElt, d::RngIntElt -> BoolElt, RngIntElt", "Whether d divides n, and the quotient.", is_divisible_by);
    it.def("ShiftLeft", "n::RngIntElt, b::RngIntElt -> RngIntElt", "n * 2^b.", shift_left);
    it.def("ShiftRight", "n::RngIntElt, b::RngIntElt -> RngIntElt", "n div 2^b.", shift_right);
    it.def("ModByPowerOf2", "n::RngIntElt, b::RngIntElt -> RngIntElt", "n mod 2^b.", mod_by_power_of_2);
    it.def("BitwiseNot", "n::RngIntElt -> RngIntElt", "The bitwise complement of n (two's complement).", bitwise_not);
    it.def("BitwiseAnd", "m::RngIntElt, n::RngIntElt -> RngIntElt", "The bitwise and of m and n (two's complement).", bitwise_and);
    it.def("BitwiseOr", "m::RngIntElt, n::RngIntElt -> RngIntElt", "The bitwise or of m and n (two's complement).", bitwise_or);
    it.def("BitwiseXor", "m::RngIntElt, n::RngIntElt -> RngIntElt", "The bitwise exclusive or of m and n (two's complement).", bitwise_xor);

    for name in ["Gcd", "GCD", "GreatestCommonDivisor"] {
        it.def(name, "x::RngIntElt, y::RngIntElt -> RngIntElt", "The greatest common divisor of x and y.", gcd);
        it.def(name, "x::FldRatElt, y::FldRatElt -> FldRatElt", "The greatest common divisor of x and y.", gcd);
        it.def(name, "x::RngIntElt, y::FldRatElt -> FldRatElt", "The greatest common divisor of x and y.", gcd);
        it.def(name, "x::FldRatElt, y::RngIntElt -> FldRatElt", "The greatest common divisor of x and y.", gcd);
        it.def(name, "S::[RngIntElt] -> RngIntElt", "The greatest common divisor of the integers in S.", gcd_seq);
        it.def(name, "S::{RngIntElt} -> RngIntElt", "The greatest common divisor of the integers in S.", gcd_seq);
    }
    for name in ["Lcm", "LCM", "LeastCommonMultiple"] {
        it.def(name, "x::RngIntElt, y::RngIntElt -> RngIntElt", "The least common multiple of x and y.", lcm);
        it.def(name, "S::[RngIntElt] -> RngIntElt", "The least common multiple of the integers in S.", lcm_seq);
        it.def(name, "S::{RngIntElt} -> RngIntElt", "The least common multiple of the integers in S.", lcm_seq);
    }
    for name in ["Xgcd", "XGCD", "ExtendedGreatestCommonDivisor"] {
        it.def(name, "x::RngIntElt, y::RngIntElt -> RngIntElt, RngIntElt, RngIntElt", "The gcd d of x and y, with a and b such that d = a*x + b*y.", xgcd);
        it.def(name, "S::[RngIntElt] -> RngIntElt, [RngIntElt]", "The gcd g of the integers in S and small multipliers X with g = &+[X[i]*S[i]].", xgcd_seq);
    }

    it.def("Isqrt", "n::RngIntElt -> RngIntElt", "The integer part of the square root of n.", isqrt);
    it.def("Iroot", "n::RngIntElt, k::RngIntElt -> RngIntElt", "The integer part of the k-th root of n.", iroot);
    it.def("IsPower", "n::RngIntElt -> BoolElt, RngIntElt, RngIntElt", "Whether n is a perfect power b^e with e > 1, and b and e (e largest).", is_power);
    it.def("IsPower", "n::RngIntElt, k::RngIntElt -> BoolElt, RngIntElt", "Whether n is a k-th power, and a k-th root.", is_power);
    it.def("IsSquarefree", "n::RngIntElt -> BoolElt", "Whether n is not divisible by the square of a prime.", is_squarefree);
    it.def(
        "SquarefreeFactorization",
        "n::RngIntElt -> RngIntElt, RngIntElt",
        "Integers x (squarefree, with the sign of n) and y > 0 with n = x*y^2.",
        squarefree_factorization,
    );
    it.def("Valuation", "n::RngIntElt, p::RngIntElt -> RngIntElt, RngIntElt", "The largest k with p^k dividing n, and n/p^k.", valuation);
    it.def("Ilog", "b::RngIntElt, n::RngIntElt -> RngIntElt", "The integer part of the logarithm of n to base b.", ilog);
    it.def("Ilog2", "n::RngIntElt -> RngIntElt", "The integer part of the base 2 logarithm of n.", ilog2);

    for name in ["Intseq", "IntegerToSequence"] {
        it.def(name, "n::RngIntElt -> [RngIntElt]", "The decimal digits of n, least significant first.", intseq);
        it.def(name, "n::RngIntElt, b::RngIntElt -> [RngIntElt]", "The base b digits of n, least significant first.", intseq);
        it.def(name, "n::RngIntElt, b::RngIntElt, k::RngIntElt -> [RngIntElt]", "The base b digits of n, padded with zeros to length k.", intseq);
    }
    for name in ["Seqint", "SequenceToInteger"] {
        it.def(name, "s::[RngIntElt] -> RngIntElt", "The integer with decimal digits s (least significant first).", seqint);
        it.def(name, "s::[RngIntElt], b::RngIntElt -> RngIntElt", "The integer with base b digits s (least significant first).", seqint);
    }

    it.def("Max", "x::., y::. -> .", "The larger of x and y.", max2);
    it.def("Min", "x::., y::. -> .", "The smaller of x and y.", min2);
    it.def("Maximum", "x::., y::. -> .", "The larger of x and y.", max2);
    it.def("Minimum", "x::., y::. -> .", "The smaller of x and y.", min2);

    it.def("Random", "a::RngIntElt, b::RngIntElt -> RngIntElt", "A random integer in the interval [a, b].", random_range);
    it.def("Random", "b::RngIntElt -> RngIntElt", "A random integer in the interval [0, b].", random_upto);
    it.def("RandomBits", "n::RngIntElt -> RngIntElt", "A random integer m with 0 <= m < 2^n.", random_bits);
    it.def_params("RandomPrime", "n::RngIntElt -> RngIntElt", &[("Proof", Value::Bool(true))], "A random prime below 2^n.", random_prime);
    it.def_params(
        "RandomPrime",
        "n::RngIntElt, a::RngIntElt, b::RngIntElt, x::RngIntElt -> BoolElt, RngIntElt",
        &[("Proof", Value::Bool(true))],
        "Try x times to find a random prime below 2^n congruent to a modulo b.",
        random_prime,
    );
    it.def(
        "RandomConsecutiveBits",
        "n::RngIntElt, a::RngIntElt, b::RngIntElt -> RngIntElt",
        "A random integer below 2^n whose binary expansion consists of runs of zeros and ones of lengths in [a .. b].",
        random_consecutive_bits,
    );
}

// ----- modular helpers shared with residue class rings --------------------------

/// Euler's totient of a positive integer.
pub fn totient(m: &Integer) -> Integer {
    super::factseq::phi(&super::factseq::factor(m))
}

/// The multiplicative order of `x` modulo `m > 1`, or 0 if `x` is not a
/// unit modulo `m`.
pub fn modorder(x: &Integer, m: &Integer) -> Integer {
    if m.is_one() {
        return Integer::one();
    }
    let x = x.div_rem_euclid(m).unwrap().1;
    if !x.gcd(m).is_one() {
        return Integer::zero();
    }
    let mut order = totient(m);
    for (p, e) in &super::factseq::factor(&order) {
        for _ in 0..*e {
            let cand = order.div_rem_euclid(p).unwrap().0;
            if x.powm(&cand, m).is_some_and(|r| r.is_one()) {
                order = cand;
            } else {
                break;
            }
        }
    }
    order
}

/// The least primitive root modulo `m`, if the unit group is cyclic.
pub fn primitive_root(m: &Integer) -> Option<Integer> {
    if m.sign() <= 0 {
        return None;
    }
    if m.is_one() {
        return Some(Integer::zero());
    }
    let two = Integer::from_i64(2);
    if *m == two {
        return Some(Integer::one());
    }
    if *m == Integer::from_i64(4) {
        return Some(Integer::from_i64(3));
    }
    // m must be p^k or 2p^k for an odd prime p.
    let odd = if m.div_rem_euclid(&two).unwrap().1.is_zero() { m.div_rem_euclid(&two).unwrap().0 } else { m.clone() };
    let f = super::factseq::factor(&odd);
    if f.len() != 1 || f[0].0 == two {
        return None;
    }
    let phi = totient(m);
    let primes: Vec<Integer> = super::factseq::factor(&phi).into_iter().map(|(p, _)| p).collect();
    let mut g = two.clone();
    while &g < m {
        if g.gcd(m).is_one() && primes.iter().all(|p| !g.powm(&phi.div_rem_euclid(p).unwrap().0, m).is_some_and(|r| r.is_one())) {
            return Some(g);
        }
        g = &g + &Integer::one();
    }
    None
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use super::*;

    /// A xorshift generator, so that the cases are the same on every run.
    fn next(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }

    /// A random integer of at most `bits` bits, of either sign.
    fn random_int(s: &mut u64, bits: u64) -> Integer {
        let mut x = Integer::zero();
        for _ in 0..bits.div_ceil(64) {
            x = &x.mul_2exp(64) + &Integer::from_u64(next(s));
        }
        let x = x.fdiv_2exp(64 * bits.div_ceil(64) - bits);
        if next(s) % 2 == 0 { -x } else { x }
    }

    #[test]
    fn xgcd_is_a_bezout_identity() {
        let mut s = 0x9e37_79b9_7f4a_7c15;
        for i in 0..3000 {
            let bits = [3, 8, 30, 64, 100, 300][i % 6];
            let c = random_int(&mut s, [1, 1, 5, 40][i % 4]);
            let (a, b) = (&random_int(&mut s, bits) * &c, &random_int(&mut s, bits) * &c);
            let (g, x, y) = a.xgcd(&b);
            assert_eq!(g, a.gcd(&b), "Xgcd({a}, {b})");
            assert_eq!(&(&a * &x) + &(&b * &y), g, "Xgcd({a}, {b})");
            if !a.is_zero() && !b.is_zero() {
                assert!(x.cmp_abs(&b.divexact(&g)) != Ordering::Greater && y.cmp_abs(&a.divexact(&g)) != Ordering::Greater, "Xgcd({a}, {b})");
            }
        }
    }

    #[test]
    fn xgcd_of_a_sequence_is_a_bezout_identity() {
        let mut s = 0x2545_f491_4f6c_dd1d;
        for i in 0..1000 {
            let c = random_int(&mut s, [1, 3, 20][i % 3]);
            let a: Vec<Integer> = (0..1 + i % 8).map(|j| if (i + j) % 7 == 0 { Integer::zero() } else { &random_int(&mut s, [4, 20, 70][i % 3]) * &c }).collect();
            let (g, x) = xgcd_seq_of(&a);
            assert_eq!(g, a.iter().fold(Integer::zero(), |g, v| g.gcd(v)), "Xgcd({a:?})");
            assert_eq!(x.len(), a.len());
            assert_eq!(a.iter().zip(&x).fold(Integer::zero(), |t, (v, m)| &t + &(v * m)), g, "Xgcd({a:?})");
        }
    }
}
