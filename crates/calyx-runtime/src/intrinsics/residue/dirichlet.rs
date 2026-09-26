//! Dirichlet characters (`GrpDrch`, `GrpDrchElt`), with values in the
//! integers, the rationals or a finite field.
//!
//! A group of characters modulo N takes its values in the powers of a root
//! of unity z of order r in its base ring. The units of Z/NZ are generated
//! by Magma's unit generators g_i, of orders n_i, and a character is given
//! by exponents e_i in Z/n_i (its `Eltseq`): its value at g_i is
//! z^(e_i r / n_i), so that e_i is a multiple of n_i / d_i, d_i being
//! gcd(n_i, r). The group is the product of the cyclic groups of orders d_i.
//!
//! Between groups, a character is carried by the angles e_i / n_i of its
//! values at the unit generators, which the generators of different moduli
//! share prime by prime. This identifies the roots of unity of groups over
//! the same ring (Magma's are powers of the primitive element), and -1
//! with -1 between the integers, the rationals and finite fields.

use std::cell::RefCell;
use std::rc::Rc;

use calyx_flint::{Integer, Rational};
use calyx_syntax::ast::BinOp;
use rustc_hash::FxHashMap;

use super::super::dlog::{log_mod_prime, log_one_units};
use super::super::{arg_ge, boolv, hidden_inner, intv, none, one, require};
use super::Res;
use crate::abgroups::{elt as ab_elt, new_group};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::rings::finite::field_of;
use crate::sym::Sym;
use crate::value::*;

/// The largest modulus: products of residues fit 128 bits.
const MAX_MODULUS: u64 = 1 << 62;

/// Odd prime powers up to this keep a table of logarithms.
const LOG_TABLE: u64 = 1 << 20;

/// Roots of unity of orders up to this keep a table of their powers.
const POWERS: u64 = 1 << 16;

/// Groups with more elements than this are not listed.
const MAX_ELEMENTS: u64 = 1 << 24;

const BAD_RING: &str = "Argument 2 must be of type RngInt, FldRat, FldCyc, FldFin, FldQuad, or FldNum.";

/// One prime power p^k exactly dividing the modulus, with the index of its
/// first unit generator.
struct Part {
    p: u64,
    k: u32,
    pk: u64,
    first: usize,
    /// Odd p: the generator modulo p^k and the factorisation of p - 1.
    odd: Option<(u64, Vec<(Integer, u64)>)>,
}

/// A group of Dirichlet characters modulo N with values in the powers of
/// `zeta`, of order r, in `ring`.
pub struct DrchGroup {
    pub modulus: u64,
    pub ring: Value,
    pub zeta: Value,
    pub r: u64,
    parts: Vec<Part>,
    /// Magma's unit generators, in [0, N), and their orders n_i.
    gens: Vec<u64>,
    orders: Vec<u64>,
    /// d_i = gcd(n_i, r): the orders of the cyclic factors of the group.
    sizes: Vec<u64>,
    names: RefCell<Vec<String>>,
    /// zeta^0, ..., zeta^(r-1), made on first use.
    powers: RefCell<Option<Rc<Vec<Value>>>>,
    /// The abstract group, made on first use: Magma returns the same one
    /// each time (and so the name it was assigned to).
    abelian: RefCell<Option<Rc<Struct>>>,
}

/// A character: its exponents e_i in Z/n_i.
pub struct DrchElt {
    pub group: Rc<Struct>,
    pub exps: Vec<u64>,
}

// ----- arithmetic on words ---------------------------------------------------

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn lcm(a: u64, b: u64) -> u64 {
    a / gcd(a, b) * b
}

fn mulmod(a: u64, b: u64, m: u64) -> u64 {
    (a as u128 * b as u128 % m as u128) as u64
}

fn powmod(mut a: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1 % m;
    a %= m;
    while e > 0 {
        if e & 1 == 1 {
            r = mulmod(r, a, m);
        }
        a = mulmod(a, a, m);
        e >>= 1;
    }
    r
}

/// The inverse of a modulo m, for a coprime to m.
fn invmod(a: u64, m: u64) -> u64 {
    let (mut r0, mut r1) = (m as i128, (a % m) as i128);
    let (mut s0, mut s1) = (0i128, 1i128);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (s0, s1) = (s1, s0 - q * s1);
    }
    s0.rem_euclid(m as i128) as u64
}

/// The exponent of p in n.
fn valuation(mut n: u64, p: u64) -> u32 {
    let mut v = 0;
    while n % p == 0 {
        n /= p;
        v += 1;
    }
    v
}

// ----- the unit group of Z/NZ ------------------------------------------------

/// Magma's generators of the units modulo n, as for `UnitGroup`: for each
/// prime power in turn, -1 and 5 for 2^k (only -1 for 4, none for 2), and
/// for odd p^k the least primitive root g modulo p (g + p if g^(p-1) = 1
/// mod p^2), each lifted to 1 modulo the other prime powers.
fn unit_parts(n: u64) -> (Vec<Part>, Vec<u64>, Vec<u64>) {
    let (mut parts, mut gens, mut orders) = (Vec::new(), Vec::new(), Vec::new());
    let factors = if n > 1 { Integer::from_u64(n).factor().map(|f| f.factors).unwrap_or_default() } else { Vec::new() };
    let mut factors: Vec<(u64, u32)> = factors.iter().map(|(p, k)| (p.to_u64().unwrap(), *k as u32)).collect();
    factors.sort_unstable();
    for (p, k) in factors {
        let pk = p.pow(k);
        let first = gens.len();
        let mut local = Vec::new();
        let mut odd = None;
        if p == 2 {
            if k >= 2 {
                local.push((pk - 1, 2));
            }
            if k >= 3 {
                local.push((5, 1 << (k - 2)));
            }
        } else {
            let pm1 = Integer::from_u64(p - 1).factor().map(|f| f.factors).unwrap_or_default();
            let primes: Vec<u64> = pm1.iter().map(|(q, _)| q.to_u64().unwrap()).collect();
            let mut g = (2..p).find(|&g| primes.iter().all(|&q| powmod(g, (p - 1) / q, p) != 1)).unwrap_or(1);
            if k >= 2 && powmod(g, p - 1, p * p) == 1 {
                g += p;
            }
            local.push((g, (p - 1) * (pk / p)));
            odd = Some((g, pm1));
        }
        let co = n / pk;
        let inv = invmod(co, pk);
        for (g, order) in local {
            gens.push(1 + co * mulmod(g - 1, inv, pk));
            orders.push(order);
        }
        parts.push(Part { p, k, pk, first, odd });
    }
    (parts, gens, orders)
}

thread_local! {
    /// Logarithms modulo odd prime powers p^k up to `LOG_TABLE` to the base
    /// of the unit generator, by p^k (u32::MAX for non-units).
    static LOG_TABLES: RefCell<FxHashMap<u64, Rc<Vec<u32>>>> = RefCell::default();
}

fn log_table(pk: u64, g: u64, phi: u64) -> Rc<Vec<u32>> {
    LOG_TABLES.with(|c| {
        if let Some(t) = c.borrow().get(&pk) {
            return t.clone();
        }
        let mut t = vec![u32::MAX; pk as usize];
        let mut y = 1;
        for a in 0..phi {
            t[y as usize] = a as u32;
            y = y * g % pk;
        }
        let t = Rc::new(t);
        c.borrow_mut().insert(pk, t.clone());
        t
    })
}

/// log_5(y) modulo 2^(k-2), for y = 1 mod 4 and k >= 3: 5^(2^i) is
/// 1 + 2^(i+2) modulo 2^(i+3), which clears the bits of y one at a time.
fn log5(y: u64, k: u32) -> u64 {
    let m = 1u64 << k;
    let (mut inv, mut t, mut b) = (invmod(5, m), y % m, 0);
    for i in 0..k - 2 {
        if (t >> (i + 2)) & 1 == 1 {
            b |= 1 << i;
            t = mulmod(t, inv, m);
        }
        inv = mulmod(inv, inv, m);
    }
    b
}

/// The logarithm of the unit y modulo the odd prime power of `part`.
fn log_odd(part: &Part, g: u64, pm1: &[(Integer, u64)], y: u64) -> Option<u64> {
    if part.pk <= LOG_TABLE {
        let t = log_table(part.pk, g, (part.p - 1) * (part.pk / part.p));
        let a = t[y as usize];
        return (a != u32::MAX).then_some(a as u64);
    }
    let (p, gi, yi) = (Integer::from_u64(part.p), Integer::from_u64(g), Integer::from_u64(y));
    let x1 = log_mod_prime(&yi, &gi, &p, pm1)?;
    if part.k == 1 {
        return x1.to_u64();
    }
    // The p-part of the logarithm from the units 1 mod p.
    let (n, pk, pe) = (Integer::from_u64(part.p - 1), Integer::from_u64(part.pk), Integer::from_u64(part.pk / part.p));
    let x2 = log_one_units(&yi.powm(&n, &pk)?, &gi.powm(&n, &pk)?, &p, part.k as u64)?;
    let t = (&(&x2 - &x1) * &n.invmod(&pe)?).div_rem_euclid(&pe)?.1;
    (&x1 + &(&n * &t)).to_u64()
}

/// Where a generator sits in the unit group, shared between moduli: the
/// prime, and for 2 whether it is 5 rather than -1.
fn keys(parts: &[Part]) -> Vec<(u64, bool)> {
    let mut out = Vec::new();
    for part in parts {
        match part.odd {
            Some(_) => out.push((part.p, false)),
            None => {
                if part.k >= 2 {
                    out.push((2, false));
                }
                if part.k >= 3 {
                    out.push((2, true));
                }
            }
        }
    }
    out
}

// ----- groups and characters -------------------------------------------------

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Integers,
    Rationals,
    Finite,
}

fn ring_kind(r: &Value) -> Option<Kind> {
    match r {
        Value::Struct(s) => match &s.kind {
            StructKind::Integers => Some(Kind::Integers),
            StructKind::Rationals => Some(Kind::Rationals),
            _ if field_of(s).is_some() => Some(Kind::Finite),
            _ => None,
        },
        _ => None,
    }
}

fn char_zero(r: &Value) -> bool {
    matches!(ring_kind(r), Some(Kind::Integers | Kind::Rationals))
}

fn char_two(r: &Value) -> bool {
    matches!(r, Value::Struct(s) if field_of(s).is_some_and(|(_, f)| f.p.to_u64() == Some(2)))
}

/// Whether a finite field r is a subfield of the finite field s.
fn subfield(r: &Value, s: &Value) -> bool {
    match (r, s) {
        (Value::Struct(a), Value::Struct(b)) => match (field_of(a), field_of(b)) {
            (Some((_, f)), Some((_, g))) => f.p == g.p && g.degree % f.degree == 0,
            _ => false,
        },
        _ => false,
    }
}

/// Whether the values of characters over r lie in s: the integers and the
/// rationals go anywhere, and finite fields into their overfields.
fn values_in(r: &Value, s: &Value) -> bool {
    r == s || char_zero(r) || subfield(r, s)
}

/// Whether characters over r and s can be compared: their rings have a
/// covering structure.
fn comparable(r: &Value, s: &Value) -> bool {
    r == s || matches!(ring_kind(r), Some(Kind::Integers)) || matches!(ring_kind(s), Some(Kind::Integers)) || subfield(r, s) || subfield(s, r)
}

/// The exponents of chi as a character over the ring r: in characteristic
/// 2 the values ±1 of characters over the integers are all 1.
fn exps_over(chi: &DrchElt, r: &Value) -> Vec<u64> {
    if char_zero(&chi.group().ring) && char_two(r) { vec![0; chi.exps.len()] } else { chi.exps.clone() }
}

fn make_group(n: u64, ring: Value, zeta: Value, r: u64) -> Rc<Struct> {
    Struct::new(StructKind::DrchGroup(Rc::new(DrchGroup::new(n, ring, zeta, r))))
}

/// Magma's group of characters modulo n over the ring: values ±1 over the
/// integers and the rationals, and over GF(q) the powers of the primitive
/// element of order gcd(q - 1, exponent of (Z/n)^*).
fn natural_group(it: &mut Interp, n: u64, ring: &Value) -> RResult<Rc<Struct>> {
    let (zeta, r) = match ring_kind(ring) {
        Some(Kind::Integers) => (Value::int(-1), 2),
        Some(Kind::Rationals) => (Value::rat(Rational::from_i64(-1)), 2),
        Some(Kind::Finite) => {
            let Value::Struct(st) = ring else { unreachable!() };
            let (_, f) = field_of(st).unwrap();
            let q1 = &f.p.pow(f.degree) - &Integer::one();
            let exponent = unit_parts(n).2.iter().fold(1, |a, &o| lcm(a, o));
            let r = Integer::from_u64(exponent).gcd(&q1).to_u64().unwrap();
            let pe = it.call_intrinsic_named(Sym::new("PrimitiveElement"), vec![ring.clone()])?;
            (it.binop(BinOp::Pow, pe, Value::Int(q1.divexact(&Integer::from_u64(r))))?, r)
        }
        None => return Err(require(RuntimeError::runtime(BAD_RING))),
    };
    Ok(make_group(n, ring.clone(), zeta, r))
}

fn modulus_arg(a: &CallArgs, i: usize) -> RResult<u64> {
    let n = a.int(i)?;
    if n.sign() <= 0 {
        return Err(require(arg_ge(i + 1, n, 1)));
    }
    n.to_u64().filter(|&n| n < MAX_MODULUS).ok_or_else(|| RuntimeError::runtime(format!("Argument {} ({n}) is too large", i + 1)))
}

pub fn group_of(st: &Struct) -> &DrchGroup {
    match &st.kind {
        StructKind::DrchGroup(g) => g,
        _ => unreachable!("a group of Dirichlet characters"),
    }
}

fn group_arg(a: &CallArgs, i: usize) -> Rc<Struct> {
    match &a.args[i] {
        Value::Struct(s) => s.clone(),
        _ => unreachable!(),
    }
}

fn elt_arg(a: &CallArgs, i: usize) -> Rc<DrchElt> {
    match &a.args[i] {
        Value::Drch(x) => x.clone(),
        _ => unreachable!(),
    }
}

fn elt(st: &Rc<Struct>, exps: Vec<u64>) -> Value {
    Value::Drch(Rc::new(DrchElt { group: st.clone(), exps }))
}

impl DrchGroup {
    fn new(n: u64, ring: Value, zeta: Value, r: u64) -> DrchGroup {
        let (parts, gens, orders) = unit_parts(n);
        let sizes = orders.iter().map(|&o| gcd(o, r)).collect();
        let (names, powers, abelian) = (RefCell::default(), RefCell::default(), RefCell::default());
        DrchGroup { modulus: n, ring, zeta, r, parts, gens, orders, sizes, names, powers, abelian }
    }

    fn ngens(&self) -> usize {
        self.gens.len()
    }

    /// n_i / d_i, the exponent of the i-th generator of the group.
    fn step(&self, i: usize) -> u64 {
        self.orders[i] / self.sizes[i]
    }

    fn order(&self) -> u64 {
        self.sizes.iter().product()
    }

    /// The character with exponents k_i (n_i / d_i) for coordinates k_i.
    fn from_coords(&self, st: &Rc<Struct>, coords: impl Iterator<Item = u64>) -> Value {
        elt(st, coords.enumerate().map(|(i, k)| k % self.sizes[i] * self.step(i) % self.orders[i]).collect())
    }

    /// The power of zeta at the i-th generator for the exponent e: e r / n_i
    /// modulo r.
    fn weight(&self, i: usize, e: u64) -> u64 {
        if self.r == 0 {
            return 0;
        }
        let d = self.sizes[i];
        ((e / self.step(i)) as u128 * (self.r / d) as u128 % self.r as u128) as u64
    }

    /// The logarithms of the unit x (in [0, N)) to the unit generators.
    fn logs(&self, x: u64) -> Option<Vec<u64>> {
        let mut out = vec![0; self.ngens()];
        for part in &self.parts {
            let y = x % part.pk;
            match &part.odd {
                None if part.k >= 2 => {
                    let minus = y % 4 == 3;
                    out[part.first] = minus as u64;
                    if part.k >= 3 {
                        out[part.first + 1] = log5(if minus { part.pk - y } else { y }, part.k);
                    }
                }
                None => {}
                Some((g, pm1)) => out[part.first] = log_odd(part, *g, pm1, y)?,
            }
        }
        Some(out)
    }

    fn powers_table(&self, it: &mut Interp) -> RResult<Rc<Vec<Value>>> {
        if let Some(t) = &*self.powers.borrow() {
            return Ok(t.clone());
        }
        let mut t = Vec::with_capacity(self.r.max(1) as usize);
        let mut x = it.coerce(&self.ring, &Value::int(1))?;
        for _ in 0..self.r.max(1) {
            t.push(x.clone());
            x = it.binop(BinOp::Mul, x, self.zeta.clone())?;
        }
        let t = Rc::new(t);
        *self.powers.borrow_mut() = Some(t.clone());
        Ok(t)
    }

    /// zeta^j, for j in [0, r).
    fn power(&self, it: &mut Interp, j: u64) -> RResult<Value> {
        if self.r <= POWERS {
            return Ok(self.powers_table(it)?[j as usize].clone());
        }
        it.binop(BinOp::Pow, self.zeta.clone(), Value::Int(Integer::from_u64(j)))
    }
}

/// Whether two groups are the same: the same modulus, ring and root of unity.
pub fn same_group(a: &DrchGroup, b: &DrchGroup) -> bool {
    a.modulus == b.modulus && a.r == b.r && a.ring == b.ring && a.zeta == b.zeta
}

/// Whether a and b are different groups of characters: Magma finds no
/// common universe for them, even when they are equal (as the groups of
/// two calls of `DirichletGroup(N)` are).
pub fn distinct_groups(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Struct(x), Value::Struct(y)) => matches!((&x.kind, &y.kind), (StructKind::DrchGroup(_), StructKind::DrchGroup(_))) && !Rc::ptr_eq(x, y),
        _ => false,
    }
}

impl DrchElt {
    pub fn group(&self) -> &DrchGroup {
        group_of(&self.group)
    }

    pub fn modulus(&self) -> u64 {
        self.group().modulus
    }

    fn order(&self) -> u64 {
        let g = self.group();
        self.exps.iter().zip(&g.orders).fold(1, |a, (&e, &n)| lcm(a, n / gcd(e, n)))
    }

    /// The least modulus the character factors through, prime by prime.
    fn conductor(&self) -> u64 {
        let g = self.group();
        let (e, n) = (&self.exps, &g.orders);
        let mut c = 1;
        for part in &g.parts {
            let f = part.first;
            match part.odd {
                Some(_) => {
                    let o = n[f] / gcd(e[f], n[f]);
                    if o > 1 {
                        c *= part.p.pow(1 + valuation(o, part.p));
                    }
                }
                None if part.k >= 2 => {
                    let five = if part.k >= 3 { n[f + 1] / gcd(e[f + 1], n[f + 1]) } else { 1 };
                    if five > 1 {
                        c *= 1 << (2 + five.trailing_zeros());
                    } else if e[f] == 1 {
                        c *= 4;
                    }
                }
                None => {}
            }
        }
        c
    }

    /// Whether the character is odd, from its exponents: -1 is the half
    /// power of each odd generator, and -1 itself for the power of 2.
    fn odd_sign(&self) -> bool {
        let g = self.group();
        g.parts.iter().filter(|p| p.odd.is_some() || p.k >= 2).map(|p| self.exps[p.first]).sum::<u64>() % 2 == 1
    }

    /// j with chi(x) = zeta^j, for a unit x in [0, N).
    fn index_at(&self, x: u64) -> Option<u64> {
        let g = self.group();
        let logs = g.logs(x)?;
        let r = g.r.max(1) as u128;
        let mut j = 0u128;
        for (i, l) in logs.iter().enumerate() {
            j = (j + *l as u128 * g.weight(i, self.exps[i]) as u128) % r;
        }
        Some(if g.r == 0 { 0 } else { j as u64 })
    }
}

/// `x eq y`: the same modulus and values.
pub fn equal(a: &DrchElt, b: &DrchElt) -> bool {
    if Rc::ptr_eq(&a.group, &b.group) {
        return a.exps == b.exps;
    }
    let (g, h) = (a.group(), b.group());
    g.modulus == h.modulus && comparable(&g.ring, &h.ring) && exps_over(a, &h.ring) == exps_over(b, &g.ring)
}

/// The exponents in the group t of the character chi, whose conductor
/// divides the modulus of t, or `None` if its values are not in the group.
fn transfer(chi: &DrchElt, t: &DrchGroup) -> Option<Vec<u64>> {
    let s = chi.group();
    let mut out = vec![0; t.ngens()];
    // Over the integers and the rationals the values are ±1, which are the
    // same in characteristic 2.
    if char_zero(&s.ring) && char_two(&t.ring) {
        return Some(out);
    }
    let (ks, kt) = (keys(&s.parts), keys(&t.parts));
    for (i, key) in kt.iter().enumerate() {
        if let Some(j) = ks.iter().position(|k| k == key) {
            let e = chi.exps[j] as u128 * t.orders[i] as u128;
            if e % s.orders[j] as u128 != 0 {
                return None;
            }
            out[i] = (e / s.orders[j] as u128) as u64 % t.orders[i];
        }
    }
    if ks.iter().enumerate().any(|(j, key)| chi.exps[j] != 0 && !kt.contains(key)) {
        return None;
    }
    out.iter().enumerate().all(|(i, &e)| e % t.step(i) == 0).then_some(out)
}

/// How Magma prints a character: 1, a Kronecker character by its
/// discriminant, or a product of powers of the generators of its group.
pub fn format(x: &DrchElt) -> String {
    match x.order() {
        1 => "1".to_string(),
        2 => format!("Kronecker character {}{}", if x.odd_sign() { "-" } else { "" }, x.conductor()),
        _ => {
            let g = x.group();
            let names = g.names.borrow();
            let mut out = Vec::new();
            for (i, &e) in x.exps.iter().enumerate() {
                let k = e / g.step(i);
                if k == 0 {
                    continue;
                }
                let name = names.get(i).cloned().unwrap_or_else(|| format!("$.{}", i + 1));
                out.push(if k == 1 { name } else { format!("{name}^{k}") });
            }
            out.join("*")
        }
    }
}

/// `G ! x`: a character of another group whose conductor divides the
/// modulus, a sequence of exponents (as `Eltseq`), or 1.
pub fn coerce(_it: &mut Interp, st: &Rc<Struct>, x: &Value) -> RResult<Result<Value, Option<String>>> {
    let g = group_of(st);
    let invalid = || Ok(Err(Some("Invalid coercion.".to_string())));
    match x {
        Value::Drch(chi) => {
            if Rc::ptr_eq(&chi.group, st) {
                return Ok(Ok(x.clone()));
            }
            if g.modulus % chi.conductor() != 0 {
                return Ok(Err(Some("Invalid coercion: The given character has too large conductor".to_string())));
            }
            if !values_in(&chi.group().ring, &g.ring) {
                return Ok(Err(Some("Invalid coercion: The values of the character are not in the coefficient ring of the group".to_string())));
            }
            match transfer(chi, g) {
                Some(e) => Ok(Ok(elt(st, e))),
                None => invalid(),
            }
        }
        Value::Seq(q) => {
            if q.elems.len() != g.ngens() || !q.elems.iter().all(|v| matches!(v, Value::Int(_))) {
                return invalid();
            }
            let mut exps = Vec::with_capacity(g.ngens());
            for (i, v) in q.elems.iter().enumerate() {
                let Value::Int(c) = v else { unreachable!() };
                let e = c.mod_u64(g.orders[i]);
                if e % g.step(i) != 0 {
                    return Ok(Err(Some("Invalid coercion: The sequence does not define a valid Dirichlet character (over the given base ring).".to_string())));
                }
                exps.push(e);
            }
            Ok(Ok(elt(st, exps)))
        }
        Value::Int(n) if n.is_one() => Ok(Ok(elt(st, vec![0; g.ngens()]))),
        _ => invalid(),
    }
}

// ----- creation --------------------------------------------------------------

fn dirichlet_group(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = modulus_arg(a, 0)?;
    let ring = if a.args.len() > 1 { a.args[1].clone() } else { Value::rationals() };
    one(Value::Struct(natural_group(it, n, &ring)?))
}

/// `DirichletGroup(N, R, z, r)`: values in the powers of z, with z^r = 1.
fn dirichlet_group_root(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = modulus_arg(a, 0)?;
    let (ring, z) = (a.args[1].clone(), a.args[2].clone());
    if ring_kind(&ring).is_none() {
        return Err(require(RuntimeError::runtime(BAD_RING)));
    }
    if it.parent_of(&z)? != ring {
        return Err(require(RuntimeError::runtime("Argument 3 must lie in argument 2.")));
    }
    let r = a.int(3)?;
    let r = r.to_u64().ok_or_else(|| require(arg_ge(4, r, 0)))?;
    let power = it.binop(BinOp::Pow, z.clone(), Value::Int(Integer::from_u64(r)))?;
    if !matches!(it.binop(BinOp::Eq, power, Value::int(1))?, Value::Bool(true)) {
        return Err(require(RuntimeError::runtime("Argument 3 must have order equal to argument 4.")));
    }
    one(Value::Struct(make_group(n, ring, z, r)))
}

/// `BaseExtend(G, R)` maps the root of unity of G into R; `BaseExtend(G,
/// R, z)` takes z in its place.
fn base_extend(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = group_arg(a, 0);
    let g = group_of(&st);
    let ring = a.args[1].clone();
    if ring_kind(&ring).is_none() {
        return Err(require(RuntimeError::runtime(BAD_RING)));
    }
    let z = match a.args.get(2) {
        Some(z) => {
            if it.parent_of(z)? != ring {
                return Err(require(RuntimeError::runtime("Argument 3 must lie in argument 2.")));
            }
            z.clone()
        }
        None => it.coerce(&ring, &g.zeta).map_err(|e| {
            let mut e = hidden_inner(e);
            e.context = Some("!".into());
            e
        })?,
    };
    one(Value::Struct(make_group(g.modulus, ring, z, g.r)))
}

fn assign_names(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = group_arg(a, 0);
    let Value::Seq(s) = &a.args[1] else { unreachable!() };
    let k = group_of(&st).ngens();
    if s.elems.len() != k {
        return Err(require(RuntimeError::runtime(format!("Argument 2 must have length {k}"))));
    }
    let name = |v: &Value| if let Value::Str(t) = v { t.as_str().to_string() } else { String::new() };
    *group_of(&st).names.borrow_mut() = s.elems.iter().map(name).collect();
    none()
}

/// Unlike most structures, the group gives the reason a coercion fails.
fn is_coercible(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match it.try_coerce(&a.args[0], &a.args[1])? {
        Ok(v) => Ok(vals![Value::Bool(true), v]),
        Err(reason) => Ok(vals![Value::Bool(false), Value::str(reason.as_deref().unwrap_or("Invalid coercion."))]),
    }
}

// ----- elements --------------------------------------------------------------

/// The characters of the group, the first coordinate running fastest.
fn all_elements(st: &Rc<Struct>) -> RResult<Vec<Value>> {
    let g = group_of(st);
    let total = g.order();
    if total > MAX_ELEMENTS {
        return Err(RuntimeError::runtime("The group is too large to list its elements"));
    }
    let mut out = Vec::with_capacity(total as usize);
    let mut coords = vec![0u64; g.ngens()];
    for _ in 0..total {
        out.push(g.from_coords(st, coords.iter().copied()));
        for (c, &d) in coords.iter_mut().zip(&g.sizes) {
            *c += 1;
            if *c < d {
                break;
            }
            *c = 0;
        }
    }
    Ok(out)
}

fn elements(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = group_arg(a, 0);
    one(Value::seq(Some(Value::Struct(st.clone())), all_elements(&st)?))
}

fn random(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = group_arg(a, 0);
    let g = group_of(&st);
    let coords: Vec<u64> = g.sizes.iter().map(|&d| it.rng.below_u64(d)).collect();
    one(g.from_coords(&st, coords.into_iter()))
}

/// `G.i`: the i-th generator, or the identity for i = 0.
fn generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = group_arg(a, 0);
    let g = group_of(&st);
    let i = a.int(1)?;
    if i.sign() < 0 {
        return Err(require(RuntimeError::runtime("Argument 2 must be nonnegative")));
    }
    let k = g.ngens();
    let i = i.to_u64().filter(|&i| i <= k as u64).ok_or_else(|| require(RuntimeError::runtime(format!("Argument 2 can be at most {k}"))))? as usize;
    one(g.from_coords(&st, (1..=k).map(|j| (j == i) as u64)))
}

fn generators(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = group_arg(a, 0);
    let g = group_of(&st);
    let k = g.ngens();
    let gens = (1..=k).map(|i| g.from_coords(&st, (1..=k).map(|j| (j == i) as u64))).collect();
    one(Value::seq(Some(Value::Struct(st.clone())), gens))
}

/// The fundamental discriminant of the quadratic field of sqrt(D), 1 for
/// squares and 0.
fn fundamental_discriminant(d: &Integer) -> Integer {
    if d.is_zero() {
        return Integer::one();
    }
    let mut core = Integer::from_i64(d.sign() as i64);
    for (p, e) in d.abs().factor().map(|f| f.factors).unwrap_or_default() {
        if e % 2 == 1 {
            core = &core * &p;
        }
    }
    if core.mod_u64(4) == 1 { core } else { &core * &Integer::from_u64(4) }
}

/// `KroneckerCharacter(D[, R])`: n -> (d/n) for the fundamental
/// discriminant d of D, modulo |d|, over the integers by default.
fn kronecker_character(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let d = fundamental_discriminant(a.int(0)?);
    let n = d.abs().to_u64().filter(|&n| n < MAX_MODULUS).ok_or_else(|| RuntimeError::runtime("Argument 1 is too large"))?;
    let ring = if a.args.len() > 1 { a.args[1].clone() } else { Value::integers() };
    let st = natural_group(it, n, &ring)?;
    let g = group_of(&st);
    let two = char_two(&g.ring);
    let exps = g.gens.iter().zip(&g.orders).map(|(&x, &o)| if d.kronecker(&Integer::from_u64(x)) < 0 && !two { o / 2 } else { 0 }).collect();
    one(elt(&st, exps))
}

// ----- attributes ------------------------------------------------------------

fn base_ring(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(group_of(&group_arg(a, 0)).ring.clone())
}

fn modulus(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(group_of(&group_arg(a, 0)).modulus))
}

fn group_order(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(group_of(&group_arg(a, 0)).order()))
}

fn exponent(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(group_of(&group_arg(a, 0)).sizes.iter().fold(1, |a, &d| lcm(a, d))))
}

fn ngens(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(group_of(&group_arg(a, 0)).ngens() as u64))
}

fn unit_generators(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int_seq(group_of(&group_arg(a, 0)).gens.iter().map(|&g| Integer::from_u64(g))))
}

/// Over the rationals every class is a single character, and Magma returns
/// a sequence of characters as it is (repetitions included).
fn galois_representatives(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = match &a.args[0] {
        Value::Struct(st) => group_of(st).ring.clone(),
        Value::Seq(s) => match (&s.universe, s.elems.first()) {
            (Some(Value::Struct(st)), _) => group_of(st).ring.clone(),
            (_, Some(Value::Drch(x))) => x.group().ring.clone(),
            _ => Value::rationals(),
        },
        _ => unreachable!(),
    };
    if !matches!(ring_kind(&ring), Some(Kind::Rationals)) {
        return Err(require(RuntimeError::runtime("The base ring of argument 1 must be a number field.")));
    }
    match &a.args[0] {
        Value::Struct(st) => one(Value::seq(Some(a.args[0].clone()), all_elements(st)?)),
        s => one(s.clone()),
    }
}

/// The map from the abstract group onto the characters.
struct AbMap {
    group: Rc<Struct>,
}

impl NativeMap for AbMap {
    fn apply(&self, _it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        match (x, &m.domain) {
            (Value::AbElt(e), Value::Struct(st)) if Rc::ptr_eq(&e.group, st) => {
                let g = group_of(&self.group);
                let coords = e.coords.iter().zip(&g.sizes).map(|(c, &d)| c.mod_u64(d));
                Ok(g.from_coords(&self.group, coords))
            }
            _ => Err(RuntimeError::runtime("Application of map failed").in_context("map application")),
        }
    }

    fn preimage(&self, it: &mut Interp, m: &MapObj, y: &Value) -> RResult<Value> {
        let chi = match it.try_coerce(&m.codomain, y)? {
            Ok(Value::Drch(chi)) => chi,
            _ => return Err(RuntimeError::runtime("Argument is not in the codomain of the map").in_context("@@")),
        };
        let g = group_of(&self.group);
        let Value::Struct(domain) = &m.domain else { unreachable!() };
        Ok(ab_elt(domain, chi.exps.iter().enumerate().map(|(i, &e)| Integer::from_u64(e / g.step(i))).collect()))
    }

    fn rule_with_inverse(&self) -> bool {
        true
    }
}

fn abelian_group(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = group_arg(a, 0);
    let g = group_of(&st);
    let abstract_group = g.abelian.borrow_mut().get_or_insert_with(|| new_group(g.sizes.iter().map(|&d| Integer::from_u64(d)).collect())).clone();
    let map = Value::Map(Rc::new(MapObj {
        kind: MapKind::Map,
        domain: Value::Struct(abstract_group.clone()),
        codomain: Value::Struct(st.clone()),
        imp: MapImpl::Native(Rc::new(AbMap { group: st })),
    }));
    // A statement printing the call shows both.
    Ok(vals![Value::Struct(abstract_group), map])
}

fn elt_base_ring(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(elt_arg(a, 0).group().ring.clone())
}

fn elt_modulus(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(elt_arg(a, 0).modulus()))
}

fn conductor(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(elt_arg(a, 0).conductor()))
}

fn eltseq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int_seq(elt_arg(a, 0).exps.iter().map(|&e| Integer::from_u64(e))))
}

fn elt_order(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(elt_arg(a, 0).order()))
}

fn is_trivial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(elt_arg(a, 0).exps.iter().all(|&e| e == 0))
}

fn is_primitive(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = elt_arg(a, 0);
    boolv(x.conductor() == x.modulus())
}

/// The character modulo the conductor with the same values on units.
fn primitive_character(x: &DrchElt) -> Value {
    let g = x.group();
    let st = make_group(x.conductor(), g.ring.clone(), g.zeta.clone(), g.r);
    let exps = transfer(x, group_of(&st)).expect("a character modulo its conductor");
    elt(&st, exps)
}

fn associated_primitive_character(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(primitive_character(&elt_arg(a, 0)))
}

/// The components of a character at the prime powers of its modulus.
fn components(x: &DrchElt) -> Vec<Value> {
    let g = x.group();
    let mut out = Vec::with_capacity(g.parts.len());
    for (i, part) in g.parts.iter().enumerate() {
        let end = g.parts.get(i + 1).map_or(g.ngens(), |q| q.first);
        let st = make_group(part.pk, g.ring.clone(), g.zeta.clone(), g.r);
        out.push(elt(&st, x.exps[part.first..end].to_vec()));
    }
    out
}

fn decomposition(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::list(components(&elt_arg(a, 0))))
}

/// The value at -1 compared with `s` (1 or -1) in the base ring.
fn value_at_minus_one_is(it: &mut Interp, x: &DrchElt, s: i64) -> RResult<bool> {
    let n = x.modulus();
    let v = evaluate(it, x, &Integer::from_u64(n - 1))?;
    Ok(matches!(it.binop(BinOp::Eq, v, Value::int(s))?, Value::Bool(true)))
}

fn is_even(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(value_at_minus_one_is(it, &elt_arg(a, 0), 1)?)
}

fn is_odd(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(value_at_minus_one_is(it, &elt_arg(a, 0), -1)?)
}

fn is_totally_even(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    for c in components(&elt_arg(a, 0)) {
        let Value::Drch(c) = c else { unreachable!() };
        if !value_at_minus_one_is(it, &c, 1)? {
            return boolv(false);
        }
    }
    boolv(true)
}

/// The character over the least subring of its base ring: itself over the
/// rationals and the prime fields.
fn minimal_base_ring_character(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = elt_arg(a, 0);
    let ring = &x.group().ring;
    let prime_field = matches!(ring, Value::Struct(s) if field_of(s).is_some_and(|(_, f)| f.degree == 1));
    if !(prime_field || matches!(ring_kind(ring), Some(Kind::Rationals))) {
        return Err(require(RuntimeError::runtime("The base ring of argument 1 must be the Q, F_p, or cyclotomic.")));
    }
    one(a.args[0].clone())
}

// ----- evaluation ------------------------------------------------------------

/// chi(-1), ±1 by the parity of the exponents, as Magma takes it even when
/// the root of unity of the group has a smaller order than it was given.
fn value_at_minus_one(it: &mut Interp, chi: &DrchElt) -> RResult<Value> {
    it.coerce(&chi.group().ring, &Value::int(if chi.odd_sign() { -1 } else { 1 }))
}

/// chi(n): 0 unless n is a unit modulo N.
fn evaluate(it: &mut Interp, chi: &DrchElt, n: &Integer) -> RResult<Value> {
    let g = chi.group();
    let x = n.mod_u64(g.modulus);
    if gcd(x, g.modulus) != 1 {
        return it.coerce(&g.ring, &Value::int(0));
    }
    if g.modulus > 2 && x == g.modulus - 1 {
        return value_at_minus_one(it, chi);
    }
    let j = chi.index_at(x).ok_or_else(|| RuntimeError::runtime("Discrete logarithm is too hard"))?;
    g.power(it, j)
}

/// The integer an argument of `Evaluate` stands for: an integer, or the
/// representative of a residue.
fn integer_arg(a: &CallArgs, i: usize) -> Integer {
    match &a.args[i] {
        Value::Int(n) => n.clone(),
        v => Res::of(v).expect("a residue").x,
    }
}

fn evaluate_int(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = integer_arg(a, 1);
    one(evaluate(it, &elt_arg(a, 0), &n)?)
}

/// `n @ chi`, which `chi(n)` stands for.
fn image(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = integer_arg(a, 0);
    one(evaluate(it, &elt_arg(a, 1), &n)?)
}

/// [chi(1), ..., chi(N)], running through the units as products of powers
/// of the generators, the first power fastest.
fn value_list(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let chi = elt_arg(a, 0);
    let g = chi.group();
    let n = g.modulus;
    let zero = it.coerce(&g.ring, &Value::int(0))?;
    let mut out = vec![zero; n as usize];
    let w: Vec<u64> = (0..g.ngens()).map(|i| g.weight(i, chi.exps[i])).collect();
    let r = g.r.max(1);
    let table = if g.r <= POWERS { Some(g.powers_table(it)?) } else { None };
    let mut digits = vec![0u64; g.ngens()];
    let (mut u, mut j) = (1 % n, 0u64);
    'units: loop {
        // Residue x goes at position x - 1, and 0 last.
        out[((u + n - 1) % n) as usize] = match &table {
            Some(t) => t[j as usize].clone(),
            None => g.power(it, j)?,
        };
        let mut i = 0;
        loop {
            if i == digits.len() {
                break 'units;
            }
            digits[i] += 1;
            u = mulmod(u, g.gens[i], n);
            j = ((j as u128 + w[i] as u128) % r as u128) as u64;
            if digits[i] < g.orders[i] {
                break;
            }
            digits[i] = 0;
            i += 1;
        }
    }
    if n > 2 {
        out[n as usize - 2] = value_at_minus_one(it, &chi)?;
    }
    one(Value::seq(Some(g.ring.clone()), out))
}

fn values_on_unit_generators(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let chi = elt_arg(a, 0);
    let g = chi.group();
    let mut out = Vec::with_capacity(g.ngens());
    for i in 0..g.ngens() {
        out.push(g.power(it, g.weight(i, chi.exps[i]))?);
    }
    one(Value::seq(Some(g.ring.clone()), out))
}

/// The order of r, assuming r^n = 1: n with each prime removed while the
/// power stays 1.
fn order_of_root_of_unity(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (r, n) = (a.args[0].clone(), a.int(1)?.abs());
    let Some(f) = n.factor() else {
        let mut e = hidden_inner(RuntimeError::runtime("Argument 1 is not non-zero"));
        e.context = Some("PrimeDivisors".into());
        return Err(e);
    };
    let mut m = n;
    for (p, _) in f.factors {
        while let Some((q, rem)) = m.div_rem_euclid(&p) {
            if !rem.is_zero() {
                break;
            }
            let power = it.binop(BinOp::Pow, r.clone(), Value::Int(q.clone()))?;
            if !matches!(it.binop(BinOp::Eq, power, Value::int(1))?, Value::Bool(true)) {
                break;
            }
            m = q;
        }
    }
    intv(m)
}

// ----- arithmetic ------------------------------------------------------------

/// x y^s for s = 1 or -1, in the group modulo the lcm of the moduli.
fn combine(it: &mut Interp, x: &Rc<DrchElt>, y: &Rc<DrchElt>, s: i64) -> RResult<Value> {
    let (g, h) = (x.group(), y.group());
    let add = |a: &[u64], b: &[u64], orders: &[u64]| -> Vec<u64> {
        a.iter().zip(b).zip(orders).map(|((&a, &b), &n)| if s > 0 { (a + b) % n } else { (a + n - b) % n }).collect()
    };
    if Rc::ptr_eq(&x.group, &y.group) || same_group(g, h) {
        return Ok(elt(&x.group, add(&x.exps, &y.exps, &g.orders)));
    }
    let ring = if g.ring == h.ring {
        g.ring.clone()
    } else if char_zero(&g.ring) && char_zero(&h.ring) {
        if matches!(ring_kind(&g.ring), Some(Kind::Rationals)) { g.ring.clone() } else { h.ring.clone() }
    } else {
        // The quotient fails in the product it calls.
        let e = RuntimeError::runtime("The base rings of the arguments must be the integers, rationals, or cyclotomic fields.");
        return Err(if s > 0 { require(e) } else { hidden_inner(e) });
    };
    let n = lcm(g.modulus, h.modulus);
    if n >= MAX_MODULUS {
        return Err(RuntimeError::runtime("The modulus of the product is too large"));
    }
    let st = natural_group(it, n, &ring)?;
    let t = group_of(&st);
    let (Some(a), Some(b)) = (transfer(x, t), transfer(y, t)) else {
        return Err(RuntimeError::runtime("The values of the characters do not lie in a common group"));
    };
    let exps = add(&a, &b, &t.orders);
    Ok(elt(&st, exps))
}

fn mul(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(combine(it, &elt_arg(a, 0), &elt_arg(a, 1), 1)?)
}

fn div(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(combine(it, &elt_arg(a, 0), &elt_arg(a, 1), -1)?)
}

fn power(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = elt_arg(a, 0);
    let k = a.int(1)?;
    let g = x.group();
    let exps = x.exps.iter().zip(&g.orders).map(|(&e, &n)| mulmod(e, k.mod_u64(n), n)).collect();
    one(elt(&x.group, exps))
}

/// Magma's package code fails on an exponent that is not an integer.
fn power_other(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    Err(hidden_inner(RuntimeError::runtime(format!("Bad argument types\nArgument types given: FldRatElt, {}", it.type_name(&a.args[1])))))
}

/// The square root of a character of odd order whose value at each
/// generator is -zeta^((m+1)/2) for its value zeta there, of order m: the
/// root of order 2m (just zeta^((m+1)/2) in characteristic 2).
fn sqrt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = elt_arg(a, 0);
    if x.order() % 2 == 0 {
        return Err(require(RuntimeError::runtime("Argument 1 must have odd order.")));
    }
    let g = x.group();
    let two = char_two(&g.ring);
    let mut exps = Vec::with_capacity(g.ngens());
    for (i, (&e, &n)) in x.exps.iter().zip(&g.orders).enumerate() {
        let m = n / gcd(e, n);
        let mut s = mulmod(e, (m + 1) / 2, n);
        if !two {
            s = (s + n / 2) % n;
        }
        if s % g.step(i) != 0 {
            return Err(RuntimeError::runtime("The square root does not lie in the group"));
        }
        exps.push(s);
    }
    one(elt(&x.group, exps))
}

pub fn register(it: &mut Interp) {
    const G: &str = "GrpDrch";
    const E: &str = "GrpDrchElt";
    it.def("DirichletGroup", &format!("N::RngIntElt -> {G}"), "The group of Dirichlet characters modulo N with values in the rationals.", dirichlet_group).package = true;
    it.def("DirichletGroup", &format!("N::RngIntElt, R::Rng -> {G}"), "The group of Dirichlet characters modulo N with values in R (the integers, the rationals or a finite field).", dirichlet_group).package = true;
    it.def("DirichletGroup", &format!("N::RngIntElt, R::Rng, z::RngElt, r::RngIntElt -> {G}"), "The group of Dirichlet characters modulo N with values in the powers of z, a root of unity of order r in R.", dirichlet_group_root).package = true;
    it.def("BaseExtend", &format!("G::{G}, R::Rng -> {G}"), "The characters of G with values in R.", base_extend);
    it.def("BaseExtend", &format!("G::{G}, R::Rng, z::RngElt -> {G}"), "The characters of G with values in R, the root of unity of G becoming z.", base_extend);
    it.def("AssignNames", &format!("~G::{G}, S::[MonStgElt]"), "Assign names to the generators of G.", assign_names);
    it.def("IsCoercible", &format!("G::{G}, x::. -> BoolElt, ."), "Whether x can be coerced into G, and the result or the reason it cannot.", is_coercible);

    it.def("Elements", &format!("G::{G} -> [{E}]"), "The characters in G.", elements);
    it.def("Random", &format!("G::{G} -> {E}"), "A random character in G.", random);
    it.def(".", &format!("G::{G}, i::RngIntElt -> {E}"), "The i-th generator of G (the identity for i = 0).", generator);
    for sig in ["D::RngIntElt", "D::RngIntElt, R::Rng"] {
        it.def("KroneckerCharacter", &format!("{sig} -> {E}"), "The character n -> (d/n) for the fundamental discriminant d of D (over the integers, or R).", kronecker_character);
    }

    it.def("BaseRing", &format!("G::{G} -> Rng"), "The ring the characters of G take values in.", base_ring);
    it.def("Modulus", &format!("G::{G} -> RngIntElt"), "The modulus of the characters of G.", modulus);
    it.def("Order", &format!("G::{G} -> RngIntElt"), "The order of G.", group_order);
    it.def("#", &format!("G::{G} -> RngIntElt"), "The order of G.", group_order);
    it.def("Exponent", &format!("G::{G} -> RngIntElt"), "The exponent of G.", exponent);
    for name in ["NumberOfGenerators", "Ngens"] {
        it.def(name, &format!("G::{G} -> RngIntElt"), "The number of generators of G (one for each unit generator).", ngens);
    }
    it.def("Generators", &format!("G::{G} -> [{E}]"), "The generators of G.", generators);
    it.def("UnitGenerators", &format!("G::{G} -> [RngIntElt]"), "Magma's generators of the units modulo the modulus of G.", unit_generators);
    it.def("GaloisConjugacyRepresentatives", &format!("G::{G} -> [{E}]"), "One character of G from each Galois conjugacy class.", galois_representatives);
    it.def("GaloisConjugacyRepresentatives", &format!("S::[{E}] -> [{E}]"), "One character from each Galois conjugacy class of the characters in S.", galois_representatives);
    it.def("AbelianGroup", &format!("G::{G} -> GrpAb, Map"), "An abelian group isomorphic to G, with the map onto G.", abelian_group);

    it.def("BaseRing", &format!("x::{E} -> Rng"), "The ring x takes values in.", elt_base_ring);
    it.def("Modulus", &format!("x::{E} -> RngIntElt"), "The modulus of x.", elt_modulus);
    it.def("Conductor", &format!("x::{E} -> RngIntElt"), "The conductor of x.", conductor);
    for name in ["Eltseq", "ElementToSequence"] {
        it.def(name, &format!("x::{E} -> [RngIntElt]"), "The exponents of x on the unit generators.", eltseq);
    }
    it.def("Order", &format!("x::{E} -> RngIntElt"), "The order of x.", elt_order);
    it.def("IsTrivial", &format!("x::{E} -> BoolElt"), "Whether x is the trivial character.", is_trivial);
    it.def("IsPrimitive", &format!("x::{E} -> BoolElt"), "Whether the conductor of x is its modulus.", is_primitive);
    it.def("AssociatedPrimitiveCharacter", &format!("x::{E} -> {E}"), "The primitive character modulo the conductor of x with the same values on units.", associated_primitive_character);
    it.def("IsEven", &format!("x::{E} -> BoolElt"), "Whether x(-1) = 1.", is_even);
    it.def("IsOdd", &format!("x::{E} -> BoolElt"), "Whether x(-1) = -1.", is_odd);
    it.def("IsTotallyEven", &format!("x::{E} -> BoolElt"), "Whether the components of x at the prime powers of its modulus are all even.", is_totally_even);
    it.def("Decomposition", &format!("x::{E} -> List"), "The components of x at the prime powers of its modulus.", decomposition);
    it.def("MinimalBaseRingCharacter", &format!("x::{E} -> {E}"), "The character x over the least subring of its base ring.", minimal_base_ring_character);

    for n in ["RngIntElt", "RngIntResElt"] {
        it.def("Evaluate", &format!("x::{E}, n::{n} -> RngElt"), "The value of x at n.", evaluate_int);
        it.def("@", &format!("n::{n}, x::{E} -> RngElt"), "The value of x at n.", image);
    }
    it.def("ValueList", &format!("x::{E} -> [RngElt]"), "The values of x at 1, ..., N for its modulus N.", value_list);
    it.def("ValuesOnUnitGenerators", &format!("x::{E} -> [RngElt]"), "The values of x at the unit generators of its group.", values_on_unit_generators);
    it.def("OrderOfRootOfUnity", "r::RngElt, n::RngIntElt -> RngIntElt", "The least m with r^m = 1, for r with r^n = 1.", order_of_root_of_unity);

    it.def("*", &format!("x::{E}, y::{E} -> {E}"), "The product of x and y.", mul);
    it.def("/", &format!("x::{E}, y::{E} -> {E}"), "The quotient of x by y.", div);
    it.def("^", &format!("x::{E}, n::RngIntElt -> {E}"), "The n-th power of x.", power);
    it.def("^", &format!("x::{E}, n::. -> {E}"), "An error: the exponent must be an integer.", power_other);
    it.def("Sqrt", &format!("x::{E} -> {E}"), "A square root of x, of odd order.", sqrt);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A group over the integers with the unit structure of n.
    fn group(n: u64) -> DrchGroup {
        DrchGroup::new(n, Value::integers(), Value::int(-1), 2)
    }

    #[test]
    fn unit_generators_as_magma() {
        let cases: &[(u64, &[u64])] = &[
            (1, &[]),
            (2, &[]),
            (4, &[3]),
            (8, &[7, 5]),
            (9, &[2]),
            (16, &[15, 5]),
            (24, &[7, 13, 17]),
            (35, &[22, 31]),
            (40, &[31, 21, 17]),
            (100, &[51, 77]),
            (105, &[71, 22, 31]),
            (1078, &[199, 981]),
        ];
        for &(n, gens) in cases {
            assert_eq!(unit_parts(n).1, gens, "modulus {n}");
        }
    }

    /// The product of the generators to the powers of the logarithms is x.
    fn check_logs(n: u64, xs: impl Iterator<Item = u64>) {
        let g = group(n);
        for x in xs.filter(|&x| gcd(x, n) == 1) {
            let logs = g.logs(x).unwrap();
            let y = g.gens.iter().zip(&logs).fold(1 % n, |y, (&b, &e)| mulmod(y, powmod(b, e, n), n));
            assert_eq!(y, x % n, "modulus {n}");
            assert!(logs.iter().zip(&g.orders).all(|(l, o)| l < o));
        }
    }

    #[test]
    fn logarithms() {
        for n in [1, 2, 3, 4, 8, 12, 45, 64, 105, 243, 1000, 1078, 4096] {
            check_logs(n, 0..n);
        }
        // Prime powers beyond the tables, and a large power of 2.
        let step = |n: u64| (1..200).map(move |i| i * (n / 211) + 1);
        for n in [1048583, 3u64.pow(13), 2 * 1048583 * 9, 1 << 40, (1 << 20) * 1048583] {
            check_logs(n, step(n));
        }
    }
}
