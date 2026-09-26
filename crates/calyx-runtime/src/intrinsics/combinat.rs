//! Combinatorial functions of the integers.

use calyx_flint::Integer;

use super::{arg_not, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn binomial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, k) = (a.int(0)?.clone(), a.int(1)?.clone());
    if k.sign() < 0 {
        return intv(Integer::zero());
    }
    // As Magma does: C(n, k) = (-1)^k C(k - n - 1, k) for n < 0, and
    // C(m, k) = C(m, m - k). Results of more than 2^32 bits are refused.
    let m = if n.sign() < 0 { &(&k - &n) - 1 } else { n.clone() };
    if k > m {
        return intv(Integer::zero());
    }
    let j = std::cmp::min(k.clone(), &m - &k);
    let big = || RuntimeError::runtime("Binomial computation is too big");
    let j = j.to_u64().filter(|&j| j < 1 << 32 && j * m.bits() <= 1 << 32).ok_or_else(big)?;
    let c = (&(&m - &Integer::from_u64(j)) + 1).rising_factorial(j).divexact(&Integer::factorial(j));
    intv(if n.sign() < 0 && k.is_odd() { -c } else { c })
}

fn multinomial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int_ge(0, 0)?;
    let parts = super::ints::ints_of(&a.args[1])?;
    if parts.is_empty() {
        return Err(RuntimeError::runtime("Argument 2 has length 0: should be >= 2"));
    }
    if let Some(r) = parts.iter().find(|r| r.sign() < 0 || **r > n) {
        return Err(RuntimeError::runtime(format!("Bad multinomial argument {r}")));
    }
    if parts.iter().fold(Integer::zero(), |s, r| &s + r) != n {
        return Err(RuntimeError::runtime("Sum of elements of argument 2 does not equal argument 1"));
    }
    let small = |x: &Integer| x.to_u64().filter(|&v| v < 100_000_000).ok_or_else(|| RuntimeError::runtime("Argument is too large"));
    let mut r = Integer::factorial(small(&n)?);
    for p in &parts {
        r = r.divexact(&Integer::factorial(small(p)?));
    }
    intv(r)
}

fn factorial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.small_ge(0, 0)?;
    if n >= 100_000_000 {
        return Err(RuntimeError::runtime("Argument 1 is too large"));
    }
    intv(Integer::factorial(n))
}

fn is_factorial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.clone();
    let no = Ok(vals![Value::Bool(false), Value::Undef]);
    if n.sign() <= 0 {
        return no;
    }
    let mut m = n;
    let mut k = 1u64;
    // Divide by 2, 3, ... while the quotient stays whole.
    loop {
        if m.is_one() {
            return Ok(vals![Value::Bool(true), Value::Int(Integer::from_u64(k.max(1)))]);
        }
        let d = Integer::from_u64(k + 1);
        if !m.is_divisible_by(&d) {
            return no;
        }
        m = m.divexact(&d);
        k += 1;
    }
}

/// The most integers that a list of partitions may hold, their parts and
/// one for each: about 2.5 GB, which Partitions(74) nears.
const MOST_PARTS: u64 = 1 << 27;

/// Calls `f` with the partitions of `n` into parts from `parts` (decreasing),
/// each with its parts in decreasing order, in reverse lexicographic order.
/// `k` restricts the number of parts. False, having stopped, if they would
/// hold more than MOST_PARTS integers.
fn each_partition(n: u64, parts: &[u64], k: Option<u64>, f: &mut dyn FnMut(&[u64])) -> bool {
    // g[j] is the gcd of parts[j..], which divides whatever they add up to.
    let mut g = vec![0; parts.len() + 1];
    for j in (0..parts.len()).rev() {
        g[j] = gcd(parts[j], g[j + 1]);
    }
    let least = parts.last().copied().unwrap_or(0);
    let mut held = 0u64;
    // A depth-first search without recursion, as a partition may have n
    // parts: cur holds the parts so far, at[i] the index of cur[i] in parts,
    // and the next part comes from parts[from..].
    let (mut cur, mut at, mut rest, mut from) = (Vec::new(), Vec::<u32>::new(), n, 0);
    loop {
        let len = cur.len() as u64;
        let next = match k {
            _ if rest == 0 => None,
            Some(k) if len == k => None,
            _ => {
                // With k parts, the parts left must make up the rest: none
                // may be above what the least ones leave, nor all below the
                // rest's share.
                let left = k.map_or(0, |k| k - len);
                let top = if k.is_some() { rest.checked_sub((left - 1) * least) } else { Some(rest) };
                top.and_then(|top| {
                    let first = from + parts[from..].partition_point(|&p| p > top);
                    (first..parts.len()).take_while(|&j| k.is_none() || parts[j] * left >= rest).find(|&j| (rest - parts[j]) % g[j] == 0)
                })
            }
        };
        if let Some(j) = next {
            if len >= MOST_PARTS {
                return false;
            }
            cur.push(parts[j]);
            at.push(j as u32);
            rest -= parts[j];
            from = j;
            continue;
        }
        if rest == 0 && k.is_none_or(|k| len == k) {
            held += len + 1;
            if held > MOST_PARTS {
                return false;
            }
            f(&cur);
        }
        let Some(j) = at.pop() else { break };
        rest += cur.pop().unwrap_or(0);
        from = j as usize + 1;
    }
    true
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// The partitions as Magma gives them (`count` of them, if known), or
/// Magma's error for an n that is too large when they would hold more than
/// MOST_PARTS integers.
fn partitions_value(n: &Integer, parts: &[u64], k: Option<u64>, count: usize) -> RResult<Vals> {
    let mut elems = Vec::with_capacity(count);
    let small = n.to_u64().filter(|&m| m < 1 << 30).ok_or_else(|| too_large(n))?;
    let mut push = |p: &[u64]| elems.push(Value::int_seq(p.iter().map(|&x| Integer::from_u64(x))));
    // A partition has at least n/max(parts) parts.
    if parts.first().is_some_and(|&p| small / p >= MOST_PARTS) || !each_partition(small, parts, k, &mut push) {
        return Err(too_large(n));
    }
    one(Value::seq(Some(Value::structure(StructKind::PowerSeq(Some(Value::integers())))), elems))
}

fn too_large(n: &Integer) -> RuntimeError {
    RuntimeError::runtime(format!("Argument 1 ({n}) is too large"))
}

/// The number of partitions of n, and the integers they hold, their parts
/// and one for each (for n up to 350, where it fits): the parts k number
/// p(n - k) + p(n - 2k) + ....
fn partitions_size(n: usize) -> (u64, u64) {
    let mut p = vec![0u64; n + 1];
    p[0] = 1;
    for k in 1..=n {
        for i in k..=n {
            p[i] += p[i - k];
        }
    }
    (p[n], p[n] + (1..=n).map(|k| (1..=n / k).map(|j| p[n - j * k]).sum::<u64>()).sum::<u64>())
}

fn partitions(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.clone();
    if n.sign() < 0 {
        return Err(arg_not(1, "non-negative"));
    }
    // Refused at once when too many.
    let m = n.to_u64().filter(|&m| m < 200).ok_or_else(|| too_large(&n))?;
    let (count, size) = partitions_size(m as usize);
    if size > MOST_PARTS {
        return Err(too_large(&n));
    }
    let parts: Vec<u64> = (1..=m).rev().collect();
    partitions_value(&n, &parts, None, count as usize)
}

fn number_of_partitions(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.small_ge(0, 0)?;
    intv(Integer::partitions(n))
}

fn restricted_partitions(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.clone();
    if n.sign() < 0 {
        return Err(arg_not(1, "positive"));
    }
    if n >= Integer::from_u64(1 << 30) {
        return Err(too_large(&n));
    }
    let k = match a.args.len() {
        3 => {
            let k = a.int(1)?;
            let bad = || RuntimeError::runtime(format!("Argument 2 ({k}) is not small and non-negative"));
            Some(k.to_u64().filter(|&k| k < 1 << 30).ok_or_else(bad)?)
        }
        _ => None,
    };
    let bad = || RuntimeError::runtime("Set elements must be positive single integers");
    let mut parts = Vec::new();
    for m in super::ints::ints_of(&a.args[a.args.len() - 1])? {
        parts.push(m.to_u64().filter(|&m| m > 0 && m < 1 << 30).ok_or_else(bad)?);
    }
    parts.sort_by(|a, b| b.cmp(a));
    partitions_value(&n, &parts, k, 0)
}

fn stirling_first(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, k) = (a.small_ge(0, 0)?, a.small_ge(1, 0)?);
    intv(Integer::stirling1(n, k))
}

fn stirling_second(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, k) = (a.small_ge(0, 0)?, a.small_ge(1, 0)?);
    intv(Integer::stirling2(n, k))
}

fn bell(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.small_ge(0, 0).map_err(super::bare)?;
    intv(Integer::bell(n))
}

/// F_n for any integer n (F_(-n) = (-1)^(n+1) F_n).
fn fibonacci_any(n: i64) -> Integer {
    let f = Integer::fibonacci(n.unsigned_abs());
    if n < 0 && n % 2 == 0 { -f } else { f }
}

/// The n-th term of the sequence with G_0 = g0, G_1 = g1 and
/// G_n = G_(n-1) + G_(n-2), for any integer n: g0 F_(n-1) + g1 F_n.
fn generalized_fibonacci(g0: &Integer, g1: &Integer, n: i64) -> Integer {
    &(g0 * &fibonacci_any(n - 1)) + &(g1 * &fibonacci_any(n))
}

fn fibonacci(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(fibonacci_any(a.small(0)?))
}

fn lucas(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.small(0)?;
    let m = n.unsigned_abs();
    let l = if m == 0 { Integer::from_i64(2) } else { &Integer::fibonacci(m - 1) + &Integer::fibonacci(m + 1) };
    intv(if n < 0 && m % 2 == 1 { -l } else { l })
}

fn generalized_fibonacci_number(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.small(2)?;
    intv(generalized_fibonacci(a.int(0)?, a.int(1)?, n))
}

pub fn register(it: &mut Interp) {
    it.def("Binomial", "n::RngIntElt, r::RngIntElt -> RngIntElt", "The binomial coefficient n choose r.", binomial);
    it.def("Multinomial", "n::RngIntElt, Q::[RngIntElt] -> RngIntElt", "The multinomial coefficient n choose Q[1], ..., Q[k].", multinomial);
    it.def("Factorial", "n::RngIntElt -> RngIntElt", "n factorial.", factorial);
    it.def("IsFactorial", "n::RngIntElt -> BoolElt, RngIntElt", "Whether n = k! for some k, and k.", is_factorial);
    it.def("Partitions", "n::RngIntElt -> [[RngIntElt]]", "The partitions of n, each in decreasing order.", partitions);
    it.def("NumberOfPartitions", "n::RngIntElt -> RngIntElt", "The number of partitions of n.", number_of_partitions);
    it.def("RestrictedPartitions", "n::RngIntElt, M::{RngIntElt} -> [[RngIntElt]]", "The partitions of n into parts from M.", restricted_partitions);
    it.def(
        "RestrictedPartitions",
        "n::RngIntElt, k::RngIntElt, M::{RngIntElt} -> [[RngIntElt]]",
        "The partitions of n into k parts from M.",
        restricted_partitions,
    );
    it.def("StirlingFirst", "n::RngIntElt, k::RngIntElt -> RngIntElt", "The (signed) Stirling number of the first kind s(n, k).", stirling_first);
    it.def("StirlingSecond", "n::RngIntElt, k::RngIntElt -> RngIntElt", "The Stirling number of the second kind S(n, k).", stirling_second);
    it.def("Bell", "n::RngIntElt -> RngIntElt", "The n-th Bell number.", bell);
    it.def("Fibonacci", "n::RngIntElt -> RngIntElt", "The n-th Fibonacci number.", fibonacci);
    it.def("Lucas", "n::RngIntElt -> RngIntElt", "The n-th Lucas number.", lucas);
    it.def(
        "GeneralizedFibonacciNumber",
        "g0::RngIntElt, g1::RngIntElt, n::RngIntElt -> RngIntElt",
        "The n-th term of the Fibonacci recursion started at g0, g1.",
        generalized_fibonacci_number,
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    fn partitions_of(n: u64, parts: &[u64], k: Option<u64>) -> Vec<Vec<u64>> {
        let mut out = Vec::new();
        assert!(each_partition(n, parts, k, &mut |p| out.push(p.to_vec())));
        out
    }

    /// The partitions by plain recursion, in the same order.
    fn reference(n: u64, parts: &[u64], k: Option<u64>, cur: &mut Vec<u64>, out: &mut Vec<Vec<u64>>) {
        if n == 0 && k.is_none_or(|k| cur.len() as u64 == k) {
            out.push(cur.clone());
        }
        for (i, &p) in parts.iter().enumerate() {
            if p <= n && k.is_none_or(|k| (cur.len() as u64) < k) {
                cur.push(p);
                reference(n - p, &parts[i..], k, cur, out);
                cur.pop();
            }
        }
    }

    #[test]
    fn partitions_are_complete_and_ordered() {
        for n in 0..=25u64 {
            let parts: Vec<u64> = (1..=n).rev().collect();
            let ps = partitions_of(n, &parts, None);
            assert_eq!(Integer::from_u64(ps.len() as u64), Integer::partitions(n), "#Partitions({n})");
            assert!(ps.iter().all(|p| p.iter().sum::<u64>() == n && p.windows(2).all(|w| w[0] >= w[1])), "Partitions({n})");
            assert!(ps.windows(2).all(|w| w[0] > w[1]), "Partitions({n}) in reverse lexicographic order");
            for k in 0..=n + 1 {
                let want: Vec<Vec<u64>> = ps.iter().filter(|p| p.len() as u64 == k).cloned().collect();
                assert_eq!(partitions_of(n, &parts, Some(k)), want, "Partitions({n}, {k})");
            }
        }
        // Parts from a set: the coefficients of 1/((1 - x^7)(1 - x^5)(1 - x^3)).
        let parts = [7u64, 5, 3];
        let mut ways = [0usize; 61];
        ways[0] = 1;
        for p in parts {
            for i in p as usize..=60 {
                ways[i] += ways[i - p as usize];
            }
        }
        for n in 0..=60 {
            assert_eq!(partitions_of(n, &parts, None).len(), ways[n as usize], "RestrictedPartitions({n}, {{3, 5, 7}})");
        }
        // Sets whose parts share factors, with and without the number of parts.
        for parts in [vec![15u64, 10, 6], vec![6, 4], vec![9, 4, 1], vec![2], vec![]] {
            for n in 0..=40 {
                for k in [None, Some(0), Some(1), Some(2), Some(3), Some(5), Some(8)] {
                    let mut want = Vec::new();
                    reference(n, &parts, k, &mut Vec::new(), &mut want);
                    assert_eq!(partitions_of(n, &parts, k), want, "RestrictedPartitions({n}, {k:?}, {parts:?})");
                }
            }
        }
        // A partition may have more parts than recursion could take.
        assert_eq!(partitions_of(1_000_000, &[1], None).iter().map(Vec::len).collect::<Vec<_>>(), [1_000_000]);
        assert_eq!(partitions_of(1_000_000, &[3, 2], Some(10)), Vec::<Vec<u64>>::new());
        // The sizes of the lists of partitions: Partitions(74) is the last to fit.
        assert_eq!(partitions_size(60), (966467, 15959618));
        assert!(partitions_size(74).1 <= MOST_PARTS && partitions_size(75).1 > MOST_PARTS);
    }

    #[test]
    fn fibonacci_numbers_follow_the_recurrence_both_ways() {
        let int = Integer::from_i64;
        assert_eq!([-2, -1, 0, 1, 2].map(fibonacci_any), [-1, 1, 0, 1, 1].map(int));
        let (g0, g1) = (int(3), int(-7));
        assert_eq!((generalized_fibonacci(&g0, &g1, 0), generalized_fibonacci(&g0, &g1, 1)), (g0.clone(), g1.clone()));
        for n in -80..=80 {
            assert_eq!(fibonacci_any(n + 2), &fibonacci_any(n + 1) + &fibonacci_any(n), "Fibonacci({n})");
            assert_eq!(generalized_fibonacci(&g0, &g1, n + 2), &generalized_fibonacci(&g0, &g1, n + 1) + &generalized_fibonacci(&g0, &g1, n), "G({n})");
        }
    }
}
