//! Real fields and their elements (MPFR numbers), with `complex`: the Real
//! and Complex Fields chapter.
//!
//! A real field is determined by its precision in bits, `⌈p·log2(10)⌉` for
//! `p` decimal digits, and every real carries its precision. Arithmetic
//! mixing precisions first rounds the more precise operand to the smaller
//! precision, as Magma does; integers and rationals are first rounded into
//! the field of the other operand.

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::{Integer, Real, bits_for_digits};
use calyx_syntax::ast::{AggKind, BinOp};
use rustc_hash::FxHashMap;

use super::{hidden, hidden_inner, one, package_frame};
use crate::error::{ErrKind, ErrStyle, ErrorInfo, RResult, RuntimeError, TraceFrame};
use crate::interp::{CallArgs, Interp};
use crate::ops::div_by_zero;
use crate::print::Level;
use crate::value::*;

mod relations;

/// The precision of the default real field at startup.
pub const DEFAULT_DIGITS: u32 = 30;

thread_local! {
    /// The precision in bits of the default real field (the parent of real
    /// literals, `RealField()`, ...).
    static DEFAULT_BITS: Cell<u64> = const { Cell::new(100) };
    /// Real literals by source text (the constant's address) and precision.
    static LITERALS: RefCell<FxHashMap<(usize, u64), (Rc<Text>, Value)>> = RefCell::default();
}

pub fn default_bits() -> u64 {
    DEFAULT_BITS.with(|b| b.get())
}

pub fn set_default_bits(bits: u64) {
    DEFAULT_BITS.with(|b| b.set(bits));
}

/// A real literal such as `1.5`, `2e-3` or `1.5p10` (precision 10) in the
/// default real field.
pub fn real_literal(s: &Rc<Text>) -> RResult<Value> {
    let bits = default_bits();
    let key = (Rc::as_ptr(s) as usize, bits);
    if let Some(v) = LITERALS.with(|m| m.borrow().get(&key).map(|e| e.1.clone())) {
        return Ok(v);
    }
    let (num, bits) = match s.find(['p', 'P']) {
        Some(i) => {
            let d: u64 = s[i + 1..].parse().map_err(|_| RuntimeError::runtime(format!("Bad real literal '{s}'")))?;
            (&s[..i], bits_for_digits(d))
        }
        None => (s.as_str(), bits),
    };
    let x = Real::parse(num, bits).ok_or_else(|| RuntimeError::runtime(format!("Bad real literal '{s}'")))?;
    let v = Value::real(x);
    LITERALS.with(|m| {
        let mut m = m.borrow_mut();
        if m.len() > 4096 {
            m.clear();
        }
        m.insert(key, (s.clone(), v.clone()));
    });
    Ok(v)
}

/// Format a real with a fixed number of decimals (for `%.No`).
pub fn format_with_digits(v: &Value, decimals: usize) -> Option<String> {
    match v {
        Value::Real(r) => Some(r.x.format_decimals(decimals, r.x.digits())),
        _ => None,
    }
}

/// A real as Magma prints it; at the Magma level followed by `p` and the
/// precision.
pub fn format_real(r: &RealV, level: Level) -> String {
    if let Some(d) = r.fixed {
        return r.x.to_string_fixed(d as usize);
    }
    let d = r.x.digits();
    let s = r.x.format(d);
    if level == Level::Magma { format!("{s}p{d}") } else { s }
}

/// An integer, rational or real as a real of the given precision.
pub fn to_real(v: &Value, bits: u64) -> Option<Real> {
    Some(match v {
        Value::Int(i) => Real::from_integer(i, bits),
        Value::Rat(q) => Real::from_rational(q, bits),
        Value::Real(r) if r.x.prec() == bits => r.x.clone(),
        Value::Real(r) => r.x.round_to(bits),
        _ => return None,
    })
}

/// A real with the precision of its argument (or the default precision for
/// integers and rationals).
pub fn real_arg(v: &Value) -> Option<Real> {
    match v {
        Value::Real(r) => Some(r.x.clone()),
        _ => to_real(v, default_bits()),
    }
}

fn bad_types(it: &Interp, a: &CallArgs) -> RuntimeError {
    let types: Vec<String> = a.args.iter().map(|v| it.type_name_ext(v)).collect();
    RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", types.join(", ")))
}

/// An integer, rational, real, or a complex number whose imaginary part is
/// zero, as a real of the given precision.
fn to_real_if_real(v: &Value, bits: u64) -> Option<Real> {
    match v {
        Value::Complex(c) if c.im.is_zero() => Some(c.re.round_to(bits)),
        Value::Complex(_) => None,
        _ => to_real(v, bits),
    }
}

/// When a real binary intrinsic is given a complex argument, Magma coerces
/// both arguments into the default real field before calling it.
fn coerce_complex_real_args(it: &Interp, a: &mut CallArgs, arctan: bool) -> RResult<bool> {
    if !a.args.iter().any(|v| matches!(v, Value::Complex(_))) {
        return Ok(false);
    }
    let bits = default_bits();
    let Some(v): Option<Vec<Real>> = a.args.iter().map(|x| to_real_if_real(x, bits)).collect() else {
        if arctan {
            return Err(RuntimeError::runtime("Bad argument types\nArgument types given: FldComElt, FldComElt"));
        }
        return Err(bad_types(it, a));
    };
    a.args = v.into_iter().map(Value::real).collect();
    Ok(true)
}

/// The precision in bits of a real or complex number.
pub fn prec_of(v: &Value) -> Option<u64> {
    match v {
        Value::Real(r) => Some(r.x.prec()),
        Value::Complex(c) => Some(c.prec()),
        _ => None,
    }
}

/// 0 for integers and rationals, 1 for reals, 2 for complex numbers.
fn num_kind(v: &Value) -> Option<u8> {
    match v {
        Value::Int(_) | Value::Rat(_) => Some(0),
        Value::Real(_) => Some(1),
        Value::Complex(_) => Some(2),
        _ => None,
    }
}

/// The precision of an operation on `a` and `b`, at least one of which is
/// real or complex: the smaller precision.
fn common_bits(a: &Value, b: &Value) -> u64 {
    match (prec_of(a), prec_of(b)) {
        (Some(x), Some(y)) => x.min(y),
        (Some(x), None) | (None, Some(x)) => x,
        _ => default_bits(),
    }
}

/// Results computed from timings are timings, unless the other operand is
/// a real of lower precision (as in Magma, whose field of timings has 52
/// bits).
fn fixed_of(a: &Value, b: &Value) -> Option<u32> {
    let timing = |v: &Value| matches!(v, Value::Real(r) if r.fixed.is_some());
    let lower = |v: &Value| matches!(v, Value::Real(r) if r.fixed.is_none() && r.x.prec() <= TIMING_BITS);
    (timing(a) && !lower(b) || timing(b) && !lower(a)).then_some(TIMING_DECIMALS)
}

/// Binary operators with a real or complex operand and the other an
/// integer, rational, real or complex number; `None` for other operands.
pub fn num_binop(op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
    let (Some(ka), Some(kb)) = (num_kind(a), num_kind(b)) else { return Ok(None) };
    if ka == 0 && kb == 0 {
        return Ok(None);
    }
    let bits = common_bits(a, b);
    if ka == 2 || kb == 2 {
        return super::complex::complex_binop(op, a, b, bits);
    }
    use BinOp::*;
    Ok(Some(match op {
        Add | Sub | Mul | Div => {
            let (x, y) = (to_real(a, bits).unwrap(), to_real(b, bits).unwrap());
            let r = match op {
                Add => x.add(&y),
                Sub => x.sub(&y),
                Mul => x.mul(&y),
                _ => x.div(&y).ok_or_else(|| div_by_zero().in_context("/"))?,
            };
            Value::Real(Rc::new(RealV { x: r, fixed: fixed_of(a, b) }))
        }
        Pow => return real_pow(a, b, bits).map(Some),
        Eq | Cmpeq => Value::Bool(num_eq(a, b).unwrap_or(false)),
        Ne | Cmpne => Value::Bool(!num_eq(a, b).unwrap_or(false)),
        Lt | Le | Gt | Ge => {
            let o = num_cmp(a, b).unwrap_or(Ordering::Equal);
            Value::Bool(match op {
                Lt => o.is_lt(),
                Le => o.is_le(),
                Gt => o.is_gt(),
                _ => o.is_ge(),
            })
        }
        _ => return Ok(None),
    }))
}

/// An integer exponent of a real or complex number: `|e| < 2^30`.
pub fn small_exponent(e: &Integer) -> RResult<i64> {
    e.to_i64().filter(|k| k.unsigned_abs() < 1 << 30).ok_or_else(|| RuntimeError::runtime(format!("Argument 2 ({e}) is too large")).in_context("^"))
}

/// `a^b` with a real operand and no complex one.
fn real_pow(a: &Value, b: &Value, bits: u64) -> RResult<Value> {
    let r = match (a, b) {
        (Value::Real(x), Value::Int(e)) => {
            let e = small_exponent(e)?;
            if x.x.is_zero() && e < 0 {
                return Err(RuntimeError::runtime("Illegal negative power of zero element").in_context("^"));
            }
            return Ok(Value::Real(Rc::new(RealV { x: x.x.pow_i64(e), fixed: x.fixed })));
        }
        _ => to_real(a, bits).unwrap().pow(&to_real(b, bits).unwrap()),
    };
    Ok(Value::real(r))
}

/// Equality of numbers at least one of which is real or complex (after
/// rounding to the smaller precision; NaN equals everything, as with
/// MPFR's comparison).
pub fn num_eq(a: &Value, b: &Value) -> Option<bool> {
    let (ka, kb) = (num_kind(a)?, num_kind(b)?);
    if ka == 0 && kb == 0 {
        return None;
    }
    let bits = common_bits(a, b);
    if ka == 2 || kb == 2 {
        let (x, y) = (super::complex::to_complex(a, bits)?, super::complex::to_complex(b, bits)?);
        return Some(x.re.cmp_magma(&y.re) == Ordering::Equal && x.im.cmp_magma(&y.im) == Ordering::Equal);
    }
    Some(to_real(a, bits)?.cmp_magma(&to_real(b, bits)?) == Ordering::Equal)
}

/// The order of real numbers (with integers and rationals).
pub fn num_cmp(a: &Value, b: &Value) -> Option<Ordering> {
    let (ka, kb) = (num_kind(a)?, num_kind(b)?);
    if ka == 2 || kb == 2 || (ka == 0 && kb == 0) {
        return None;
    }
    let bits = common_bits(a, b);
    Some(to_real(a, bits)?.cmp_magma(&to_real(b, bits)?))
}

/// `secs` rounded to the precision of timings, so that the time since a
/// timing taken earlier is not negative.
pub fn timing_seconds(secs: f64) -> f64 {
    Real::from_f64(secs, TIMING_BITS).to_f64()
}

/// A timing of `secs` seconds.
pub fn timing_value(secs: f64) -> Value {
    timing_real(Real::from_f64(secs, TIMING_BITS))
}

/// `x` in the field of timings.
pub fn timing_real(x: Real) -> Value {
    Value::Real(Rc::new(RealV { x: x.round_to(TIMING_BITS), fixed: Some(TIMING_DECIMALS) }))
}

/// `y`, a function of the real `x`, in the field of timings if `x` is a
/// timing.
fn same_field(x: &Value, y: Real) -> Value {
    match x {
        Value::Real(r) if r.fixed.is_some() => timing_real(y),
        _ => Value::real(y),
    }
}

// ----- real fields -------------------------------------------------------------

/// The precision in bits of `RealField(p)` or `ComplexField(p)`, with the
/// `Bits` parameter.
pub fn field_bits(a: &CallArgs, i: usize) -> RResult<u64> {
    let p = a.int(i)?;
    if a.param_bool("Bits")? {
        if *p < Integer::from_i64(2) {
            return Err(super::arg_ge(i + 1, p, 2));
        }
        return p.to_u64().filter(|&b| b < 1 << 40).ok_or_else(|| RuntimeError::runtime("Precision is too large"));
    }
    if p.sign() <= 0 {
        return Err(super::arg_not(i + 1, "positive"));
    }
    p.to_u64().filter(|&d| d < 1 << 38).map(bits_for_digits).ok_or_else(|| RuntimeError::runtime("Precision is too large"))
}

fn real_field(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = match a.args.first() {
        None => default_bits(),
        Some(v @ Value::Struct(_)) => bits_of(v).unwrap(),
        Some(_) => field_bits(a, 0)?,
    };
    one(Value::reals(bits))
}

fn get_default_real_field(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::reals(default_bits()))
}

fn set_default_real_field(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    set_default_bits(bits_of(&a.args[0]).unwrap());
    super::none()
}

fn identity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = bits_of(&a.args[0]).unwrap();
    let x = Real::from_i64(1, bits);
    one(if matches!(a.args[0], Value::Struct(ref s) if matches!(s.kind, StructKind::Reals(_))) { Value::real(x) } else { Value::complex(x, Real::zero(bits)) })
}

/// The precision in bits of a real or complex field or number, or of the
/// universe of a sequence of them.
pub fn bits_of(v: &Value) -> Option<u64> {
    match v {
        Value::Real(r) => Some(r.x.prec()),
        Value::Complex(c) => Some(c.prec()),
        Value::Struct(s) => match &s.kind {
            StructKind::Reals(b) => Some(*b),
            StructKind::Ring(r) => match r.kind {
                crate::rings::RingKind::Complex(b) => Some(b),
                _ => None,
            },
            _ => None,
        },
        Value::Seq(s) => s.universe.as_ref().and_then(bits_of),
        _ => None,
    }
}

fn precision(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = bits_of(&a.args[0]).ok_or_else(|| RuntimeError::runtime("Bad argument types"))?;
    one(Value::int(calyx_flint::digits_for_bits(bits) as i64))
}

fn bit_precision(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(bits_of(&a.args[0]).unwrap() as i64))
}

/// `ChangePrecision(x, n)`: x in the field of precision n.
fn change_precision(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(1)?;
    if n.sign() <= 0 {
        return Err(super::arg_not(1, "positive").in_context("RealField"));
    }
    let bits = n.to_u64().filter(|&d| d < 1 << 38).map(bits_for_digits).ok_or_else(|| RuntimeError::runtime("Precision is too large"))?;
    one(match &a.args[0] {
        Value::Complex(c) => super::complex::cv(c.round_to(bits)),
        v => Value::real(to_real(v, bits).unwrap()),
    })
}

fn mantissa_exponent(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = prec_of(&a.args[0]).unwrap();
    let x = to_real_if_real(&a.args[0], bits).ok_or_else(|| bad_types(it, a))?;
    if !x.is_regular() {
        return Ok(vals![Value::int(0), Value::Infinity(false)]);
    }
    let (m, e) = x.mantissa_exponent();
    Ok(vals![Value::Int(m), Value::int(e)])
}

fn complex_real_rounding(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Complex(c) = &a.args[0] else { unreachable!() };
    if !c.im.is_zero() {
        return Err(bad_types(it, a));
    }
    one(Value::Int(if &*a.name.as_rc() == "Floor" { c.re.floor() } else { c.re.ceil() }))
}

/// Argument `i` as a real number, with integers and rationals in the
/// default field.
fn real_at(a: &CallArgs, i: usize) -> Real {
    real_arg(&a.args[i]).unwrap()
}

fn sqrt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = real_at(a, 0);
    if x.sign() < 0 {
        let z = Real::zero(x.prec());
        return one(Value::complex(z, x.neg().sqrt()));
    }
    one(same_field(&a.args[0], x.sqrt()))
}

/// The real n-th root (NaN for n < 1); even roots of negative integers
/// and rationals are complex.
fn root(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = real_at(a, 0);
    let n = a.int(1)?;
    let Some(k) = n.to_u64().filter(|&k| k > 0) else { return one(Value::real(Real::nan(x.prec()))) };
    if k % 2 == 0 && x.sign() < 0 {
        if !matches!(a.args[0], Value::Real(_)) {
            let c = super::complex::magma_root(&calyx_flint::Complex::from_real(x), n);
            return one(super::complex::cv(c));
        }
        return Err(RuntimeError::runtime("Illegal even root of negative number"));
    }
    one(Value::real(x.root(k)))
}

fn real_part(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::real(real_at(a, 0)))
}

fn imaginary_part(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::real(Real::zero(real_at(a, 0).prec())))
}

/// The argument of a real: 0, or pi for negative numbers.
fn arg(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = real_at(a, 0);
    one(Value::real(Real::zero(x.prec()).binary(&x, calyx_flint::mpfr::mpfr_atan2)))
}

fn abs(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::real(real_at(a, 0).abs()))
}

fn conjugate(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(a.args[0].clone())
}

fn is_integral(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    super::boolv(real_at(a, 0).is_integer())
}

fn constant(a: &CallArgs, f: calyx_flint::mpfr::Constant) -> RResult<Vals> {
    let bits = bits_of(&a.args[0]).unwrap();
    let x = Real::constant(f, bits);
    one(match &a.args[0] {
        Value::Struct(s) if matches!(s.kind, StructKind::Reals(_)) => Value::real(x),
        _ => Value::complex(x, Real::zero(bits)),
    })
}

fn pi(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    constant(a, calyx_flint::mpfr::mpfr_const_pi)
}

fn euler_gamma(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    constant(a, calyx_flint::mpfr::mpfr_const_euler)
}

fn catalan(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    constant(a, calyx_flint::mpfr::mpfr_const_catalan)
}

/// `|x - y|` for real or complex numbers.
fn distance_between(x: &Value, y: &Value) -> RResult<Value> {
    Ok(match num_binop(BinOp::Sub, x, y)? {
        Some(Value::Real(r)) => Value::real(r.x.abs()),
        Some(Value::Complex(c)) => Value::real(c.abs()),
        _ => return Err(RuntimeError::runtime("Bad argument types")),
    })
}

/// Whether a distance is below the bound `Max` (none by default).
fn below(d: &Value, max: &Value) -> bool {
    match max {
        Value::Infinity(pos) => *pos,
        _ => num_cmp(d, max).is_some_and(|o| o.is_lt()),
    }
}

/// `Distance(x, L)`: the least distance from x to an element of L, and the
/// index of such an element (`Max` and 0 if every distance is at least
/// `Max`).
fn distance(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = a.args[0].clone();
    let Value::Seq(l) = &a.args[1] else { unreachable!() };
    if l.elems.is_empty() {
        return Err(RuntimeError::runtime("Array must be nonempty").in_context(""));
    }
    let max = a.param("Max").cloned().unwrap_or(Value::Infinity(true));
    let mut best = (max.clone(), 0);
    for (i, y) in l.elems.iter().enumerate() {
        let d = distance_between(&x, y)?;
        if below(&d, &best.0) {
            best = (d, i + 1);
        }
    }
    if best.1 == 0 && matches!(best.0, Value::Infinity(_)) {
        best.0 = Value::int(0);
    }
    Ok(vals![best.0, Value::int(best.1 as i64)])
}

/// `Diameter(L)`: the least distance between distinct elements of L (0, or
/// `Max`, if there is none below `Max`).
fn diameter(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Seq(l) = &a.args[0] else { unreachable!() };
    let l = l.clone();
    let max = a.param("Max").cloned().unwrap_or(Value::Infinity(true));
    let mut best = max;
    for (i, x) in l.elems.iter().enumerate() {
        for y in &l.elems[i + 1..] {
            let d = distance_between(x, y)?;
            if !matches!(&d, Value::Real(r) if r.x.is_zero()) && below(&d, &best) {
                best = d;
            }
        }
    }
    one(if matches!(best, Value::Infinity(_)) { Value::int(0) } else { best })
}

// ----- transcendental functions ------------------------------------------------

/// The error for an argument outside the domain of a real function.
type Domain = fn(&Real) -> Option<&'static str>;

/// A real function as Magma computes it: MPFR's function (of `1/x` for
/// `recip`), after a check of the domain; for `finite`, a value that is
/// not finite (a pole, an overflow, or NaN) is an error.
struct RealFn {
    f: calyx_flint::mpfr::Unary,
    recip: bool,
    domain: Domain,
    finite: bool,
}

/// The real functions with their Magma names, and their descriptions.
pub const REAL_FUNCTIONS: [(&str, &str); 27] = [
    ("Exp", "The exponential of x."),
    ("Log", "The natural logarithm of x > 0."),
    ("Dilog", "The dilogarithm of x (its real part for x > 1)."),
    ("Sin", "The sine of x."),
    ("Cos", "The cosine of x."),
    ("Tan", "The tangent of x."),
    ("Cot", "The cotangent of x."),
    ("Sec", "The secant of x."),
    ("Cosec", "The cosecant of x."),
    ("Arcsin", "The inverse sine of x, in [-pi/2, pi/2]."),
    ("Arccos", "The inverse cosine of x, in [0, pi]."),
    ("Arctan", "The inverse tangent of x, in (-pi/2, pi/2)."),
    ("Arccot", "The inverse cotangent of x, the inverse tangent of 1/x."),
    ("Arcsec", "The inverse secant of x, the inverse cosine of 1/x."),
    ("Arccosec", "The inverse cosecant of x, the inverse sine of 1/x."),
    ("Sinh", "The hyperbolic sine of x."),
    ("Cosh", "The hyperbolic cosine of x."),
    ("Tanh", "The hyperbolic tangent of x."),
    ("Coth", "The hyperbolic cotangent of x."),
    ("Sech", "The hyperbolic secant of x."),
    ("Cosech", "The hyperbolic cosecant of x."),
    ("Argsinh", "The inverse hyperbolic sine of x."),
    ("Argcosh", "The inverse hyperbolic cosine of x >= 1."),
    ("Argtanh", "The inverse hyperbolic tangent of x, |x| < 1."),
    ("Argsech", "The inverse hyperbolic secant of x, the inverse hyperbolic cosine of 1/x."),
    ("Argcosech", "The inverse hyperbolic cosecant of x, the inverse hyperbolic sine of 1/x."),
    ("Argcoth", "The inverse hyperbolic cotangent of x, the inverse hyperbolic tangent of 1/x."),
];

fn cmp_one(x: &Real) -> Ordering {
    x.cmp_magma(&Real::from_i64(1, 2))
}

fn abs_cmp_one(x: &Real) -> Ordering {
    x.cmp_abs(&Real::from_i64(1, 2))
}

fn real_fn(name: &str) -> RealFn {
    use calyx_flint::mpfr::*;
    let any: Domain = |_| None;
    let (f, recip, domain, finite): (Unary, bool, Domain, bool) = match name {
        "Exp" => (mpfr_exp, false, any, false),
        "Log" => (mpfr_log, false, |x| (x.is_zero() || x.sign() < 0).then_some("Argument 1 is not positive"), false),
        "Dilog" => (mpfr_li2, false, any, false),
        "Sin" => (mpfr_sin, false, any, true),
        "Cos" => (mpfr_cos, false, any, true),
        "Tan" => (mpfr_tan, false, any, true),
        "Cot" => (mpfr_cot, false, any, true),
        "Sec" => (mpfr_sec, false, any, true),
        "Cosec" => (mpfr_csc, false, any, true),
        "Arcsin" | "Arccos" => {
            let f: Unary = if name == "Arcsin" { mpfr_asin } else { mpfr_acos };
            (f, false, |x| abs_cmp_one(x).is_gt().then_some("Argument must have absolute value <= 1"), true)
        }
        "Arctan" => (mpfr_atan, false, any, true),
        "Arccot" => (mpfr_atan, true, any, false),
        "Arcsec" | "Arccosec" => {
            let f: Unary = if name == "Arcsec" { mpfr_acos } else { mpfr_asin };
            (f, true, |x| abs_cmp_one(x).is_lt().then_some("Argument must have absolute value >= 1"), false)
        }
        "Sinh" => (mpfr_sinh, false, any, true),
        "Cosh" => (mpfr_cosh, false, any, true),
        "Tanh" => (mpfr_tanh, false, any, true),
        "Coth" => (mpfr_coth, false, |x| x.is_zero().then_some("Argument 1 is not non-zero"), true),
        "Sech" => (mpfr_sech, false, any, true),
        "Cosech" => (mpfr_csch, false, |x| x.is_zero().then_some("Argument 1 is not non-zero"), true),
        "Argsinh" => (mpfr_asinh, false, any, true),
        "Argcosh" => (mpfr_acosh, false, |x| cmp_one(x).is_lt().then_some("Argument must be at least 1"), true),
        "Argtanh" => (mpfr_atanh, false, |x| (x.is_nan() || !abs_cmp_one(x).is_lt()).then_some("Argument must have absolute value < 1"), true),
        "Argsech" => (
            mpfr_acosh,
            true,
            |x| {
                if x.is_zero() || x.sign() < 0 {
                    Some("Argument must be positive")
                } else {
                    cmp_one(x).is_gt().then_some("Argument must be no more than 1")
                }
            },
            false,
        ),
        "Argcosech" => (mpfr_asinh, true, |x| x.is_zero().then_some("Argument 1 is not non-zero"), false),
        "Argcoth" => (mpfr_atanh, true, |x| (x.is_nan() || !abs_cmp_one(x).is_gt()).then_some("Argument must have absolute value > 1"), false),
        _ => unreachable!("{name}"),
    };
    RealFn { f, recip, domain, finite }
}

/// The real functions of `REAL_FUNCTIONS`, by the name called.
fn real_function(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let spec = real_fn(&a.name.as_rc());
    let x = real_at(a, 0);
    if let Some(msg) = (spec.domain)(&x) {
        return Err(RuntimeError::runtime(msg));
    }
    let x = if spec.recip { Real::from_i64(1, x.prec()).binary(&x, calyx_flint::mpfr::mpfr_div) } else { x };
    let y = x.unary(spec.f);
    if spec.finite && !y.is_finite() {
        return Err(RuntimeError::runtime("Function not defined for this argument"));
    }
    one(same_field(&a.args[0], y))
}

fn sincos(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (s, c) = real_at(a, 0).sin_cos();
    Ok(vals![Value::real(s), Value::real(c)])
}

/// The precision of a function of two real arguments: the smaller
/// precision; the default one if neither is real.
fn common_real_bits(a: &CallArgs) -> u64 {
    let (x, y) = (prec_of(&a.args[0]), prec_of(&a.args[1]));
    x.zip(y).map(|(x, y)| x.min(y)).or(x).or(y).unwrap_or_else(default_bits)
}

/// The precision of Arctan(x, y): that of the first real argument, or the
/// default precision if both arguments are exact.
fn first_real_bits(a: &CallArgs) -> u64 {
    a.args.iter().find_map(|v| match v { Value::Real(r) => Some(r.x.prec()), _ => None }).unwrap_or_else(default_bits)
}

/// `Log(b, x)`: the logarithm of x to the base b, the quotient of the two
/// logarithms, in the field of b and x if they are the same, else in the
/// default real field.
fn log_base(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    coerce_complex_real_args(it, a, false)?;
    let bits = shared_bits(&a.args);
    let (b, x) = (to_real(&a.args[0], bits).unwrap(), to_real(&a.args[1], bits).unwrap());
    if b.sign() <= 0 {
        return Err(super::arg_not(1, "positive"));
    }
    if x.sign() <= 0 {
        return Err(super::arg_not(2, "positive"));
    }
    if cmp_one(&b).is_eq() {
        return Err(RuntimeError::runtime("Base for logarithm should not be 1"));
    }
    let log = |v: &Real| v.unary(calyx_flint::mpfr::mpfr_log);
    one(Value::real(log(&x).div(&log(&b)).unwrap()))
}

/// `Arctan(x, y)`: the angle of the point (x, y), in (-pi, pi]. Magma
/// computes it with PARI, whose zeros have no sign: `Arctan(-1, -0)` is pi.
fn arctan2(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let complex = coerce_complex_real_args(it, a, true)?;
    let bits = if complex { default_bits() } else { first_real_bits(a) };
    let unsigned = |v: &Value| to_real(v, bits).map(|r| if r.is_zero() { Real::zero(bits) } else { r }).unwrap();
    let (x, y) = (unsigned(&a.args[0]), unsigned(&a.args[1]));
    if x.is_zero() && y.is_zero() {
        return Err(RuntimeError::runtime("Arguments cannot both be zero"));
    }
    one(Value::real(y.binary(&x, calyx_flint::mpfr::mpfr_atan2)))
}

// ----- gamma, Bessel and associated functions ------------------------------------------------

/// Magma's errors at the poles of the gamma function on the real line: 0
/// (of either sign) and the negative integers.
fn real_pole(x: &Real) -> RResult<()> {
    if x.is_zero() {
        return Err(RuntimeError::runtime("Argument must be non zero"));
    }
    if x.sign() < 0 && x.is_integer() {
        return Err(RuntimeError::runtime("Argument must not be a negative integer"));
    }
    Ok(())
}

/// `Gamma(x)`, `LogGamma(x)` and `Psi(x)` (also `LogDerivative(x)`) of a
/// real or complex number, integers and rationals in the default field.
/// The real Gamma and LogGamma are MPFR's, and an error where their value
/// is not finite (so where Gamma is negative for LogGamma). The complex
/// LogGamma is the principal branch, log(Gamma(x)).
fn gamma_function(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let name = a.name.as_rc();
    if let Value::Complex(z) = &a.args[0] {
        if z.im.is_zero() && (z.re.is_zero() || z.re.sign() < 0 && z.re.is_integer()) {
            return Err(RuntimeError::runtime(match &*name {
                "Gamma" if z.re.is_zero() => "Argument 1 is not non-zero",
                "Gamma" => "Argument must not be a negative integer",
                _ => "Argument 1 must not be a non positive integer",
            }));
        }
        let w = match &*name {
            "Gamma" => z.gamma(),
            "LogGamma" => z.log_gamma(),
            _ => z.digamma(),
        };
        return one(super::complex::cv(w));
    }
    let x = real_at(a, 0);
    real_pole(&x)?;
    use calyx_flint::mpfr::*;
    let y = match &*name {
        "Gamma" => x.unary(mpfr_gamma),
        "LogGamma" => x.unary(mpfr_lngamma),
        _ => return one(Value::real(x.unary(mpfr_digamma))),
    };
    if !y.is_finite() {
        return Err(RuntimeError::runtime("Function not defined for this argument"));
    }
    one(Value::real(y))
}

/// Magma's error for a parameter of the wrong type.
pub(super) fn bad_param(it: &Interp, a: &CallArgs, p: &str) -> RuntimeError {
    let types: Vec<String> = a.args.iter().map(|v| it.type_name_ext(v)).collect();
    RuntimeError::runtime(format!("Bad type for parameter '{p}'\nArgument types given: {}", types.join(", ")))
}

/// The precision of a function computed by PARI in Magma: that of its
/// arguments if they are reals of the same precision, else the default one.
fn shared_bits(v: &[Value]) -> u64 {
    match prec_of(&v[0]) {
        Some(p) if v.iter().all(|x| matches!(x, Value::Real(r) if r.x.prec() == p)) => p,
        _ => default_bits(),
    }
}

/// `Gamma(s, t)`: the incomplete gamma function `∫_0^t u^(s-1) e^-u du`,
/// or with `Complementary` `∫_t^∞ u^(s-1) e^-u du`. Given the value `g` of
/// `Γ(s)` as `Gamma`, the lower one is `g` minus the upper one.
fn incomplete_gamma(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    coerce_complex_real_args(it, a, false)?;
    let upper = match a.param("Complementary") {
        Some(Value::Bool(b)) => *b,
        _ => return Err(bad_param(it, a, "Complementary")),
    };
    let g = match a.param("Gamma") {
        None | Some(Value::Undef) => None,
        Some(Value::Real(g)) => Some(g.x.clone()),
        _ => return Err(bad_param(it, a, "Gamma")),
    };
    if upper && g.is_some() {
        return Err(RuntimeError::runtime("Parameter Gamma cannot be given when parameter Complementary is true"));
    }
    let bits = shared_bits(&a.args);
    let (s, t) = (to_real(&a.args[0], bits).unwrap(), to_real(&a.args[1], bits).unwrap());
    // The lower function at a pole of Γ(s), and the integrals from 0 that
    // diverge.
    let pole = s.sign() <= 0 && s.is_integer();
    if pole && !upper && g.is_none() || t.is_zero() && s.sign() <= 0 {
        return Err(RuntimeError::runtime("Division by zero in (possibly) real or complex division. Maybe loss of precision?"));
    }
    one(Value::real(match g {
        Some(g) => g.round_to(bits).sub(&Real::incomplete_gamma(&s, &t, true, bits)),
        None => Real::incomplete_gamma(&s, &t, upper, bits),
    }))
}

/// `GammaD(s)`: `Γ(s + 1/2)`.
fn gamma_d(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = real_at(a, 0);
    // s + 1/2 is a pole when 2s is an odd integer, s < 0.
    let twice = x.add(&x);
    if x.sign() < 0 && twice.is_integer() && !x.is_integer() {
        real_pole(&twice.add(&Real::from_i64(1, x.prec())))?;
    }
    one(Value::real(x.gamma_half()))
}

/// A Bessel function's order: a small non-negative integer.
fn bessel_order(a: &CallArgs) -> RResult<i64> {
    let n = a.int(0)?;
    n.to_i64().filter(|n| (0..1 << 30).contains(n)).ok_or_else(|| RuntimeError::runtime(format!("Argument 1 ({n}) is not small and non-negative")))
}

/// `BesselFunction(n, x)` and `BesselFunctionSecondKind(n, x)`: `J_n(x)`
/// and `Y_n(x)` (MPFR's, so `Y_n(x)` is NaN for x < 0).
fn bessel_function(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = prec_of(&a.args[1]).unwrap_or_else(default_bits);
    let x = to_real_if_real(&a.args[1], bits).ok_or_else(|| bad_types(it, a))?;
    let n = bessel_order(a)?;
    one(Value::real(if &*a.name.as_rc() == "BesselFunction" { Real::bessel_jn(n, &x) } else { Real::bessel_yn(n, &x) }))
}

/// `JBessel(n, x)`: the Bessel function of the first kind of half-integral
/// order `J_(n+1/2)(x)`, x ≥ 0 (by the same formula for a real n).
fn j_bessel(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = real_at(a, 1);
    let n = match &a.args[0] {
        Value::Real(r) => r.x.clone(),
        _ => Real::from_i64(bessel_order(a)?, 64),
    };
    if x.sign() < 0 {
        return Err(RuntimeError::runtime("Argument 2 must be non-negative"));
    }
    one(Value::real(Real::bessel_j_half(&n, &x, x.prec())))
}

/// `KBessel(nu, x)` and `KBessel2(nu, x)`: the modified Bessel function of
/// the second kind `K_nu(x)`, x > 0. For a real order in the smaller
/// precision of nu and x, for a complex one in that of nu, which x must
/// have.
fn k_bessel(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let complex = match &a.args[0] {
        Value::Complex(nu) => Some(nu.clone()),
        _ => None,
    };
    let bits = complex.as_ref().map_or_else(|| common_real_bits(a), |nu| nu.prec());
    if complex.is_some() && prec_of(&a.args[1]) < Some(bits) {
        return Err(RuntimeError::runtime("Argument 2 must have at least the precision of argument 1"));
    }
    let x = to_real(&a.args[1], bits).unwrap();
    if x.sign() <= 0 {
        return Err(RuntimeError::runtime("Argument must be positive"));
    }
    if let Some(nu) = complex {
        return one(super::complex::cv(calyx_flint::Complex::bessel_k(&nu, &calyx_flint::Complex::from_real(x), bits)));
    }
    let nu = to_real(&a.args[0], bits).unwrap();
    one(Value::real(Real::bessel_k(&nu, &x, bits)))
}

/// `HypergeometricU(a, b, x)`: the confluent hypergeometric function
/// `U(a, b, x)`, x > 0. Reals a and b of the same precision need x in their
/// field.
fn hypergeometric_u(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    if let (Some(p), Some(q), Some(r)) = (prec_of(&a.args[0]), prec_of(&a.args[1]), prec_of(&a.args[2])) {
        if p == q && q != r {
            return Err(RuntimeError::runtime("Arguments are not compatible"));
        }
    }
    let bits = shared_bits(&a.args);
    let r = |i: usize| to_real(&a.args[i], bits).unwrap();
    let x = r(2);
    if x.sign() <= 0 {
        return Err(RuntimeError::runtime("Argument 3 must be positive"));
    }
    one(Value::real(Real::hypergeometric_u(&r(0), &r(1), &x, bits)))
}

// ----- other special functions ------------------------------------------------

/// The error functions, the exponential and logarithmic integrals and
/// Dawson's integral of a real number, with an error where the value is
/// not finite. `E1(x)` is `-Ei(-x)`, so it is also defined for x < 0.
fn special_function(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    use calyx_flint::mpfr::*;
    let x = real_at(a, 0);
    let y = match &*a.name.as_rc() {
        "Erf" | "ErrorFunction" => x.unary(mpfr_erf),
        "Erfc" | "ComplementaryErrorFunction" => x.unary(mpfr_erfc),
        "ExponentialIntegral" => x.unary(mpfr_eint),
        "ExponentialIntegralE1" => x.neg().unary(mpfr_eint).neg(),
        "LogIntegral" if x.sign() < 0 => return Err(RuntimeError::runtime("Argument must be non negative")),
        "LogIntegral" if x == Real::from_i64(1, x.prec()) => return Err(RuntimeError::runtime("Argument is 1")),
        "LogIntegral" => x.log_integral(),
        _ => x.dawson(),
    };
    if !y.is_finite() {
        return Err(RuntimeError::runtime("Function not defined for this argument"));
    }
    one(Value::real(y))
}

/// `ZetaFunction(s)`: the Riemann zeta function of a real or complex s ≠ 1.
fn zeta_function(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let one_error = || RuntimeError::runtime("Argument must not be 1");
    if let Value::Complex(z) = &a.args[0] {
        if z.im.is_zero() && z.re == Real::from_i64(1, z.prec()) {
            return Err(one_error());
        }
        return one(super::complex::cv(z.zeta()));
    }
    let x = real_at(a, 0);
    if x.is_nan() || x == Real::from_i64(1, x.prec()) {
        return Err(one_error());
    }
    let y = x.unary(calyx_flint::mpfr::mpfr_zeta);
    if !y.is_finite() {
        return Err(RuntimeError::runtime("Function not defined for this argument"));
    }
    one(Value::real(y))
}

/// `ZetaFunction(R, n)`: `zeta(n)` in R for an integer n ≠ 1, |n| < 2^30.
fn zeta_function_int(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = bits_of(&a.args[0]).unwrap();
    let n = a.int(1)?;
    if n.to_i64() == Some(1) {
        return Err(RuntimeError::runtime("Argument 2 must not be 1"));
    }
    let k = n.to_i64().filter(|n| n.unsigned_abs() < 1 << 30).ok_or_else(|| RuntimeError::runtime(format!("Argument 2 ({n}) is too large")))?;
    one(Value::real(Real::zeta_int(k, bits)))
}

/// `AGM(x, y)`: the arithmetic-geometric mean of two real or complex
/// numbers.
fn agm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = common_real_bits(a);
    if a.args.iter().any(|v| matches!(v, Value::Complex(_))) {
        let c = |v: &Value| super::complex::to_complex(v, bits).unwrap();
        return one(super::complex::cv(c(&a.args[0]).agm(&c(&a.args[1]))));
    }
    let (x, y) = (to_real(&a.args[0], bits).unwrap(), to_real(&a.args[1], bits).unwrap());
    one(Value::real(x.binary(&y, calyx_flint::mpfr::mpfr_agm)))
}

/// The index of a Bernoulli number, if it is non-negative (Magma's `B_n`
/// is 0 for n < 0).
fn bernoulli_index(a: &CallArgs) -> RResult<Option<u64>> {
    let n = a.int(0)?;
    if n.sign() < 0 {
        return Ok(None);
    }
    n.to_u64().filter(|&n| n < 1 << 30).map(Some).ok_or_else(|| RuntimeError::runtime("Argument 1 is too large"))
}

fn bernoulli_number(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(bernoulli_index(a)?.map_or_else(|| Value::int(0), |n| Value::rat(calyx_flint::bernoulli(n))))
}

fn bernoulli_approximation(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = default_bits();
    one(Value::real(bernoulli_index(a)?.map_or_else(|| Real::zero(bits), |n| Real::bernoulli(n, bits))))
}

// ----- infinite series ------------------------------------------------

/// The working precision of the series: Magma sums them by PARI's
/// algorithms in 128 bits whatever the precision of the terms (InfiniteSum
/// and Euler's transformation in `series_bits`), and rounds the sum to their
/// field.
const SERIES_BITS: u64 = 128;

/// The most terms of InfiniteSum and steps of an inner sum of PositiveSum
/// (Magma has no limit), and terms of Euler's transformation (Magma's
/// limit), before giving up.
const SERIES_TERMS: u64 = 1_000_000;
const INNER_STEPS: u64 = 100_000;
const EULER_TERMS: u64 = 10_000;

fn too_many_iterations() -> RuntimeError {
    RuntimeError::runtime("Too many iterations in summation method")
}

/// A series `m(a+1) + m(a+2) + ...` of real or complex terms.
struct Series {
    map: Rc<MapObj>,
    a: Integer,
    /// The precision of the codomain of `m`.
    bits: u64,
}

impl Series {
    /// The series `m(i) + m(i+1) + ...` of `InfiniteSum(m, i)` and the like,
    /// where `m` must go from the integers to a real field (or a complex one,
    /// if `complex`).
    fn new(a: &CallArgs, complex: bool) -> RResult<Series> {
        let Value::Map(m) = &a.args[0] else { unreachable!() };
        if !matches!(&m.domain, Value::Struct(s) if matches!(s.kind, StructKind::Integers)) {
            return Err(RuntimeError::runtime("Map has an invalid domain: should be Integers()"));
        }
        let bits = match &m.codomain {
            Value::Struct(s) if complex || matches!(s.kind, StructKind::Reals(_)) => bits_of(&m.codomain),
            _ => None,
        };
        let Some(bits) = bits else {
            let fields = if complex { "RealField() or ComplexField()" } else { "RealField()" };
            return Err(RuntimeError::runtime(format!("Map has an invalid codomain: should be {fields}")));
        };
        Ok(Series { map: m.clone(), a: a.int(1)? - &Integer::from_i64(1), bits })
    }

    /// The term `m(a + n)` as a complex number of the given precision (with
    /// imaginary part zero for a real).
    fn term(&self, it: &mut Interp, n: &Integer, bits: u64) -> RResult<ComplexV> {
        let v = it.apply_map(&self.map, &Value::Int(&self.a + n))?;
        super::complex::to_complex(&v, bits).ok_or_else(|| RuntimeError::runtime("Terms of the series must be real or complex numbers"))
    }

    fn nth(&self, it: &mut Interp, n: u64, bits: u64) -> RResult<ComplexV> {
        self.term(it, &Integer::from_u64(n), bits)
    }

    /// Magma's check of the first ten terms: none may be negative in a
    /// positive series, and no two consecutive ones may have the same sign in
    /// an alternating one.
    fn check(&self, it: &mut Interp, positive: bool) -> RResult<()> {
        let mut last = 0;
        for n in 1..=10 {
            let sign = self.nth(it, n, self.bits)?.re.sign();
            if positive && sign < 0 {
                return Err(RuntimeError::runtime("Series is not positive"));
            }
            if !positive && sign * last > 0 {
                return Err(RuntimeError::runtime("Series is not alternating"));
            }
            last = sign;
        }
        Ok(())
    }

    /// The sum `z` in the field of the terms.
    fn value(&self, z: ComplexV) -> Value {
        match &self.map.codomain {
            Value::Struct(s) if matches!(s.kind, StructKind::Reals(_)) => Value::real(z.re.round_to(self.bits)),
            _ => super::complex::cv(z.round_to(self.bits)),
        }
    }
}

/// The working precision of InfiniteSum and Euler's transformation for
/// terms of the given precision: whole 64-bit words with room for a few
/// more bits (192 bits from 38 digits, 256 from 58), and at least 128.
fn series_bits(bits: u64) -> u64 {
    (bits + 3).div_ceil(64).max(2) * 64
}

/// PARI's `expo`: `floor(log2 |x|)`, very small for 0.
fn expo_real(x: &Real) -> i64 {
    if x.is_regular() { x.exponent() - 1 } else { i64::MIN / 4 }
}

/// PARI's `gexpo` of a complex number: the larger `expo` of its parts.
fn expo(z: &ComplexV) -> i64 {
    expo_real(&z.re).max(expo_real(&z.im))
}

/// The number of terms of PARI's `sumalt` and `sumpos` in 128 bits.
fn cvz_terms() -> u64 {
    (0.4 * (SERIES_BITS + 7) as f64) as u64
}

/// The Cohen–Villegas–Zagier acceleration in 128 bits (PARI's `sumalt`):
/// the weighted sum of the first terms `x(k)` of an alternating series.
fn cvz_sum(mut x: impl FnMut(u64) -> RResult<Real>) -> RResult<Real> {
    let (bits, n) = (SERIES_BITS, cvz_terms());
    let d = Real::from_i64(8, bits).sqrt().add_i64(3).pow_i64(n as i64);
    let d = d.add(&Real::from_i64(1, bits).div(&d).unwrap()).mul_2exp(-1);
    let mut az = Integer::from_i64(-1);
    let mut c = d.clone();
    let mut sum = Real::zero(bits);
    for k in 0..n {
        c = c.add(&Real::from_integer(&az, bits));
        sum = sum.add(&x(k)?.mul(&c));
        az = (&(&az * &Integer::from_u64((n - k) * (n + k))) * &Integer::from_i64(2)).divexact(&Integer::from_u64((k + 1) * (2 * k + 1)));
    }
    Ok(sum.div(&d).unwrap())
}

/// `InfiniteSum(m, i)`: PARI's `suminf`, adding the terms to 1 until three
/// in a row are negligible (below 2^-133 of the sum) and taking away the 1.
fn infinite_sum(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = Series::new(a, true)?;
    let bits = series_bits(s.bits);
    let g = SERIES_BITS as i64 + 5;
    let unit = ComplexV::from_real(Real::from_i64(1, bits));
    let mut x = unit.clone();
    let mut small = 0;
    for n in 1..=SERIES_TERMS {
        let t = s.nth(it, n, bits)?;
        x = x.add(&t);
        if t.is_zero() || expo(&t) <= expo(&x) - g {
            small += 1;
            if small == 3 {
                return one(s.value(x.sub(&unit)));
            }
        } else {
            small = 0;
        }
    }
    Err(too_many_iterations())
}

/// Magma's error for a parameter with a bad value.
fn bad_param_value(it: &Interp, a: &CallArgs, p: &str, v: &str) -> RuntimeError {
    let types: Vec<String> = a.args.iter().map(|v| it.type_name_ext(v)).collect();
    RuntimeError::runtime(format!("Bad value for parameter '{p}' ({v})\nArgument types given: {}", types.join(", ")))
}

/// `AlternatingSum(m, i)`: the Cohen–Villegas–Zagier acceleration (PARI's
/// `sumalt`), or with `Al := "EulerVanWijngaarden"` Euler's transformation
/// by van Wijngaarden's algorithm.
fn alternating_sum(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let euler = match a.param("Al") {
        Some(Value::Str(t)) if t.as_str() == "Villegas" => false,
        Some(Value::Str(t)) if t.as_str() == "EulerVanWijngaarden" => true,
        Some(Value::Str(t)) => return Err(bad_param_value(it, a, "Al", t.as_str())),
        _ => return Err(bad_param(it, a, "Al")),
    };
    let s = Series::new(a, false)?;
    s.check(it, false)?;
    let sum = if euler { euler_sum(it, &s)? } else { cvz_sum(|k| Ok(s.nth(it, k + 1, SERIES_BITS)?.re))? };
    one(s.value(ComplexV::from_real(sum)))
}

/// Euler's transformation of an alternating series by van Wijngaarden's
/// algorithm in `series_bits`, until an increment from the tenth term on is
/// below 2^-123.
fn euler_sum(it: &mut Interp, s: &Series) -> RResult<Real> {
    let bits = series_bits(s.bits);
    let mut e = calyx_flint::EulerSum::new(bits);
    let mut sum = Real::zero(bits);
    for j in 1..=EULER_TERMS {
        let inc = e.push(&s.nth(it, j, bits)?.re);
        sum = sum.add(&inc);
        if j >= 10 && expo_real(&inc) < 5 - SERIES_BITS as i64 {
            return Ok(sum);
        }
    }
    Err(too_many_iterations())
}

/// `PositiveSum(m, i)`: van Wijngaarden's transformation of a series of
/// positive terms into an alternating one, `b_k = Σ_j 2^j a_(2^j (k+1))`,
/// summed by the Cohen–Villegas–Zagier acceleration (PARI's `sumpos`).
fn positive_sum(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = Series::new(a, false)?;
    s.check(it, true)?;
    let n = cvz_terms();
    let g = 5 - SERIES_BITS as i64;
    // The inner sums Σ_kk 2^kk a_(2^kk (2k+2)), each b_(2k+1) of a b_k.
    let mut stock: Vec<Option<Real>> = vec![None; n as usize + 1];
    let sum = cvz_sum(|k| {
        let b = match stock[k as usize].take() {
            Some(b) => b,
            None => {
                let mut x = Real::zero(SERIES_BITS);
                let mut r = Integer::from_u64(2 * k + 2);
                for kk in 0.. {
                    if kk == INNER_STEPS {
                        return Err(too_many_iterations());
                    }
                    let t = s.term(it, &r, SERIES_BITS)?.re.mul_2exp(kk as i64);
                    x = x.add(&t);
                    if kk > 0 && expo_real(&t) < g {
                        break;
                    }
                    r = &r * &Integer::from_i64(2);
                }
                if 2 * k < n {
                    stock[2 * k as usize + 1] = Some(x.clone());
                }
                s.nth(it, k + 1, SERIES_BITS)?.re.add(&x.mul_2exp(1))
            }
        };
        Ok(if k % 2 == 1 { b.neg() } else { b })
    })?;
    one(s.value(ComplexV::from_real(sum)))
}

// ----- numerical integration ------------------------------------------------

/// A sequence of reals of the given precision.
fn real_seq(bits: u64, v: Vec<Real>) -> Value {
    Value::seq(Some(Value::reals(bits)), v.into_iter().map(Value::real).collect())
}

/// The number of points and the precision (in bits, given in digits) of
/// an integration scheme.
fn scheme_args(a: &CallArgs) -> RResult<(u64, u64)> {
    let (n, d) = (a.int(0)?, a.int(1)?);
    let n = n.to_u64().filter(|&n| n > 0).ok_or_else(|| super::arg_not(1, "positive"))?;
    let d = d.to_u64().filter(|&d| d > 0).ok_or_else(|| super::arg_not(2, "positive"))?;
    Ok((n, bits_for_digits(d)))
}

fn gauss_legendre_points(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, bits) = scheme_args(a)?;
    let (x, w) = calyx_flint::quadrature::gauss_legendre(n, bits);
    Ok(vals![real_seq(bits, x), real_seq(bits, w)])
}

fn gauss_jacobi_points(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, bits) = scheme_args(a)?;
    // Exact exponents are taken to far more than the working precision.
    let exponent = |i: usize| real_arg(&a.args[i]).filter(|_| matches!(a.args[i], Value::Real(_))).unwrap_or_else(|| to_real(&a.args[i], 2 * bits + 192).unwrap());
    let (alpha, beta) = (exponent(2), exponent(3));
    for (i, e) in [(3, &alpha), (4, &beta)] {
        if e.cmp_magma(&Real::from_i64(-1, 2)).is_le() {
            return Err(RuntimeError::runtime(format!("Argument {i} must be greater than -1")));
        }
    }
    let (x, w) = calyx_flint::quadrature::gauss_jacobi(n, &alpha, &beta, bits);
    Ok(vals![real_seq(bits, x), real_seq(bits, w)])
}

fn clenshaw_curtis_points(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, bits) = scheme_args(a)?;
    let (x, w) = calyx_flint::quadrature::clenshaw_curtis(n, bits);
    Ok(vals![real_seq(bits, x), real_seq(bits, w)])
}

fn tanh_sinh_points(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.to_u64().ok_or_else(|| super::arg_not(1, "non-negative"))?;
    let h = real_at(a, 1);
    if h.sign() <= 0 {
        return Err(super::arg_not(2, "positive"));
    }
    let bits = h.prec();
    let (x, w1, w2) = calyx_flint::quadrature::tanh_sinh(n, &h);
    Ok(vals![real_seq(bits, x), real_seq(bits, w1), real_seq(bits, w2)])
}

/// Neville's algorithm as in Numerical Recipes' `polint` (and PARI's
/// `polinterpolate`): the value at `x` of the polynomial through the points
/// `(xa[i], ya[i])`, and the last correction, an estimate of its error;
/// `None` if two points coincide. The tableau is kept in `bits` (as Magma
/// keeps it in sequences over the field of the values).
fn neville(xa: &[Real], ya: &[Real], x: &Real, bits: u64) -> Option<(Real, Real)> {
    let n = xa.len();
    let mut ns = 0;
    let mut dif = x.sub(&xa[0]).abs();
    for (i, xi) in xa.iter().enumerate().skip(1) {
        let dift = x.sub(xi).abs();
        if dift.cmp_magma(&dif).is_lt() {
            ns = i;
            dif = dift;
        }
    }
    let (mut c, mut d) = (ya.to_vec(), ya.to_vec());
    let mut y = ya[ns].clone();
    // ns counts from 1 below, as in Numerical Recipes (after ns--).
    let mut ns = ns as isize;
    let mut dy = Real::zero(y.prec());
    for m in 1..n {
        for i in 0..n - m {
            let (ho, hp) = (xa[i].sub(x), xa[i + m].sub(x));
            let den = c[i + 1].sub(&d[i]).div(&ho.sub(&hp))?;
            d[i] = hp.mul(&den).round_to(bits);
            c[i] = ho.mul(&den).round_to(bits);
        }
        dy = if 2 * ns < (n - m) as isize {
            c[ns as usize].clone()
        } else {
            ns -= 1;
            d[ns as usize].clone()
        };
        y = y.add(&dy);
    }
    Some((y, dy))
}

/// `Interpolation(P, V, t)`: the value at t of the polynomial through the
/// points (P[i], V[i]), and an estimate of its error.
fn interpolation(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (Value::Seq(p), Value::Seq(v)) = (&a.args[0], &a.args[1]) else { unreachable!() };
    if p.elems.len() != v.elems.len() {
        return Err(super::require(RuntimeError::runtime("Arguments 1 and 2 should have the same length")));
    }
    if p.elems.is_empty() {
        return Err(hidden_inner(RuntimeError::runtime("Argument 1 is not non-empty").in_context("Minimum")));
    }
    let xa: Vec<Real> = p.elems.iter().map(|x| real_arg(x).unwrap()).collect();
    let ya: Vec<Real> = v.elems.iter().map(|y| real_arg(y).unwrap()).collect();
    let bits = v.universe.as_ref().and_then(bits_of).unwrap_or_else(|| ya[0].prec());
    let (y, dy) = neville(&xa, &ya, &real_at(a, 2), bits).ok_or_else(|| super::require(RuntimeError::runtime("Two of the x input values are identical (within precision)")))?;
    Ok(vals![Value::real(y), Value::real(dy)])
}

// ----- Romberg-type integration and numerical derivatives -----------------------
//
// Magma computes these in its arithmetic (each operation in the smaller
// precision of its operands) on the values of the integrand, which may be
// integers, rationals, reals or complex numbers. Sums of values are as by
// `&+`, which adds the first half (rounded down) of a sequence to the rest,
// recursively. As in Magma's package code, failed requirements name the
// intrinsic unless the call is a statement of its own (`require`), and
// failed operations do not name the operator and hide Magma's package
// traceback: `hidden_inner` for errors in the intrinsic's own code, and
// `hidden` for those in RombergQuadrature's trapezoidal refinement, a
// function of its own in Magma, whose report shows the intrinsic's frame.
// An error of the integrand f shows the intrinsic's frame before f's.

/// How an error of Magma's package code is reported: `hidden` or
/// `hidden_inner`.
type Hide = fn(RuntimeError) -> RuntimeError;

/// The sum of `value(lo), ..., value(hi - 1)`, evaluated in order, as by
/// Magma's `&+`.
fn tree_sum(it: &mut Interp, lo: u64, hi: u64, hide: Hide, value: &mut dyn FnMut(&mut Interp, u64) -> RResult<Value>) -> RResult<Value> {
    if hi - lo == 1 {
        return value(it, lo);
    }
    let mid = lo + (hi - lo) / 2;
    let x = tree_sum(it, lo, mid, hide, value)?;
    let y = tree_sum(it, mid, hi, hide, value)?;
    arith(it, BinOp::Add, x, y, hide)
}

/// `x op y` in Magma's arithmetic, failing as its package code does
/// (without naming the operator).
fn arith(it: &mut Interp, op: BinOp, x: Value, y: Value, hide: Hide) -> RResult<Value> {
    it.binop(op, x, y).map_err(|mut e| {
        e.context = Some(String::new());
        hide(e)
    })
}

/// `f(x)` for the function f passed to a package intrinsic.
fn apply(it: &mut Interp, f: &Value, x: Value) -> RResult<Value> {
    it.call_function(f, vec![x]).map_err(package_frame)
}

/// RombergQuadrature's n-th trapezoidal sum is Magma's
/// `TrapezoidalRefinement(f, a, b, n, s, it)`, with s the last sum and it
/// the number of its new points; the report of an error of f shows its
/// frame too.
struct Refinement<'a> {
    a: &'a CallArgs,
    n: i64,
    s: Real,
    m: u64,
}

impl Refinement<'_> {
    fn apply(&self, it: &mut Interp, f: &Value, x: Value) -> RResult<Value> {
        it.call_function(f, vec![x]).map_err(|mut e| {
            let vals = [&self.a.args[0], &self.a.args[1], &self.a.args[2], &Value::int(self.n), &Value::real(self.s.clone()), &Value::Int(Integer::from_u64(self.m))];
            let args = ["f", "a", "b", "n", "s", "it"].iter().zip(vals).map(|(p, v)| (p.to_string(), it.frame_arg(v))).collect();
            e.trace.push(TraceFrame { name: crate::sym::Sym::new("TrapezoidalRefinement"), span: None, args });
            package_frame(e)
        })
    }
}

/// `&+[f(x0 + k del) : k in [0..m-1]]` in RombergQuadrature's trapezoidal
/// refinement: the values form a sequence, which fails unless they have a
/// common universe, before they are added.
fn midpoint_sum(it: &mut Interp, f: &Value, x0: &Real, del: &Real, r: &Refinement) -> RResult<Value> {
    let m = r.m;
    let mut vals = Vec::new();
    for k in 0..m {
        vals.push(r.apply(it, f, Value::real(x0.add(&del.mul_i64(k as i64))))?);
    }
    let seq = it.build_aggregate(AggKind::Seq, None, vals, false).map_err(|mut e| {
        e.message = "No valid universe containing all elements".into();
        e.context = Some("sequence construction".into());
        hidden(e)
    })?;
    let Value::Seq(seq) = seq else { unreachable!("a sequence") };
    tree_sum(it, 0, m, hidden, &mut |_, k| Ok(seq.elems[k as usize].clone()))
}

/// `&+[RealField() | f(x + k h) : k in ks]`: the values of f at those
/// points, coerced into the default real field and added there.
fn default_field_sum(it: &mut Interp, f: &Value, x: &Real, h: &Real, ks: impl Iterator<Item = i64>) -> RResult<Value> {
    let mut vals = Vec::new();
    for k in ks {
        vals.push(apply(it, f, Value::real(x.add(&h.mul_i64(k))))?);
    }
    let bits = default_bits();
    let field = Value::reals(bits);
    let mut xs = Vec::with_capacity(vals.len());
    for v in &vals {
        match it.coerce(&field, v) {
            Ok(Value::Real(r)) => xs.push(r.x.clone()),
            _ => return Err(hidden_inner(RuntimeError::runtime("Cannot coerce element into the universe").in_context("sequence construction"))),
        }
    }
    fn sum(xs: &[Real]) -> Real {
        if xs.len() == 1 {
            return xs[0].clone();
        }
        let m = xs.len() / 2;
        sum(&xs[..m]).add(&sum(&xs[m..]))
    }
    Ok(Value::real(if xs.is_empty() { Real::zero(bits) } else { sum(&xs) }))
}

/// The number n of intervals of Simpson's and the trapezoidal rule, at
/// least `min`.
fn intervals(a: &CallArgs, min: i64) -> RResult<i64> {
    let n = a.int(3)?;
    if n.sign() < 0 || n.to_i64().is_some_and(|n| n < min) {
        return Err(super::require(RuntimeError::runtime(format!("Argument 4 ({n}) should be >= {min}"))));
    }
    n.to_i64().ok_or_else(|| RuntimeError::runtime("Argument 4 is too large"))
}

/// The endpoints a and b of an integral, and the width `(b - a)/n` of n
/// intervals, in the precision of the points (the smaller of theirs).
fn interval_width(a: &CallArgs, n: i64) -> (Real, Real) {
    let (x, y) = (real_at(a, 1), real_at(a, 2));
    let h = y.sub(&x).div_i64(n);
    (x, h)
}

/// `TrapezoidalQuadrature(f, a, b, n)`: the trapezoidal rule on n
/// intervals of width h, `h((f(a) + f(b))/2 + Σ f(a + kh))`, the sum taken
/// in the default real field.
fn trapezoidal_quadrature(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = intervals(a, 1)?;
    let f = a.args[0].clone();
    let (x, h) = interval_width(a, n);
    let fa = apply(it, &f, a.args[1].clone())?;
    let fb = apply(it, &f, a.args[2].clone())?;
    let ends = arith(it, BinOp::Add, fa, fb, hidden_inner)?;
    let ends = arith(it, BinOp::Div, ends, Value::int(2), hidden_inner)?;
    let inner = default_field_sum(it, &f, &x, &h, 1..n)?;
    let s = arith(it, BinOp::Add, ends, inner, hidden_inner)?;
    one(arith(it, BinOp::Mul, Value::real(h), s, hidden_inner)?)
}

/// `SimpsonQuadrature(f, a, b, n)`: Simpson's rule on an even number n of
/// intervals of width h, `h/3 (f(a) + f(b) + 4 Σ f(odd points) + 2 Σ
/// f(even points))`, the sums taken in the default real field.
fn simpson_quadrature(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = intervals(a, 2)?;
    if n % 2 == 1 {
        return Err(super::require(RuntimeError::runtime("Argument 4 must be even")));
    }
    let f = a.args[0].clone();
    let (x, h) = interval_width(a, n);
    let fa = apply(it, &f, a.args[1].clone())?;
    let fb = apply(it, &f, a.args[2].clone())?;
    let s = arith(it, BinOp::Add, fa, fb, hidden_inner)?;
    let odd = default_field_sum(it, &f, &x, &h, (1..n).step_by(2))?;
    let odd = arith(it, BinOp::Mul, Value::int(4), odd, hidden_inner)?;
    let s = arith(it, BinOp::Add, s, odd, hidden_inner)?;
    let even = default_field_sum(it, &f, &x, &h, (2..n).step_by(2))?;
    let even = arith(it, BinOp::Mul, Value::int(2), even, hidden_inner)?;
    let s = arith(it, BinOp::Add, s, even, hidden_inner)?;
    let h3 = arith(it, BinOp::Div, Value::real(h), Value::int(3), hidden_inner)?;
    one(arith(it, BinOp::Mul, h3, s, hidden_inner)?)
}

/// The number of trapezoidal sums RombergQuadrature extrapolates from:
/// always five, whatever the parameter K.
const ROMBERG_POINTS: usize = 5;

fn exceeded_steps() -> RuntimeError {
    let msg = "Exceeded maximum number of steps";
    ErrorInfo { kind: ErrKind::User, object: Some(Value::str(msg)), style: ErrStyle::Bare, ..ErrorInfo::runtime(msg) }.into()
}

/// `RombergQuadrature(f, a, b)`: Romberg's method, as in Numerical Recipes'
/// `qromb` and `trapzd`. The first trapezoidal sum is `(b - a)(f(a) +
/// f(b))/2` and the j-th adds the midpoints `x0 + k del` of the `m =
/// 2^(j-2)` intervals of width del, `((b - a) Σ f(x0 + k del)/m + s)/2`;
/// the sums are kept in the default field. From the sixth on, the value at
/// 0 of the polynomial through `(4^(1-i), s_i)` for the last five is the
/// result once the estimate of its error is below `Precision` times its
/// size.
fn romberg_quadrature(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let d = default_bits();
    let eps = match a.param("Precision") {
        Some(Value::Undef) | None => Value::real(Real::parse("1.0e-6", d).unwrap()),
        Some(p) => p.clone(),
    };
    let eps = it.call_intrinsic_named(crate::sym::Sym::new("Abs"), vec![eps]).map_err(hidden_inner)?;
    // Magma prints false for K < 2, and otherwise ignores K.
    let k = a.param("K").cloned().unwrap_or(Value::int(5));
    if matches!(arith(it, BinOp::Lt, k, Value::int(2), hidden_inner)?, Value::Bool(true)) {
        it.out.write("false\n");
    }
    let steps = match a.param("MaxSteps") {
        Some(Value::Int(n)) => n.to_i64().unwrap_or(i64::MAX),
        None => 20,
        Some(_) => return Err(hidden_inner(RuntimeError::runtime("Sequence range does not consist of integers").in_context("[ ... ]"))),
    };
    let f = a.args[0].clone();
    let (x, y) = (real_at(a, 1), real_at(a, 2));
    let span = y.sub(&x);
    let (mut hs, mut ss): (Vec<Real>, Vec<Real>) = (Vec::new(), Vec::new());
    let mut h = Real::from_i64(1, d);
    for j in 1..=steps {
        let s = match ss.last() {
            None => {
                let r = Refinement { a, n: 1, s: Real::zero(d), m: 0 };
                let fa = r.apply(it, &f, a.args[1].clone())?;
                let fb = r.apply(it, &f, a.args[2].clone())?;
                let ends = arith(it, BinOp::Add, fa, fb, hidden)?;
                let s = arith(it, BinOp::Mul, Value::real(span.clone()), ends, hidden)?;
                arith(it, BinOp::Div, s, Value::int(2), hidden)?
            }
            Some(last) => {
                let m = 1u64.checked_shl(j as u32 - 2).filter(|&m| m < 1 << 62).ok_or_else(exceeded_steps)?;
                let del = span.mul_2exp(2 - j);
                let x0 = x.add(&del.mul_2exp(-1));
                let sum = midpoint_sum(it, &f, &x0, &del, &Refinement { a, n: j, s: last.clone(), m })?;
                let t = arith(it, BinOp::Mul, Value::real(span.clone()), sum, hidden)?;
                let t = arith(it, BinOp::Div, t, Value::Int(Integer::from_u64(m)), hidden)?;
                let s = arith(it, BinOp::Add, Value::real(last.clone()), t, hidden)?;
                arith(it, BinOp::Div, s, Value::int(2), hidden)?
            }
        };
        let s = match &s {
            Value::Complex(c) if c.im.is_zero() => c.re.round_to(d),
            _ => to_real(&s, d).ok_or_else(|| hidden_inner(RuntimeError::runtime("Sequence mutation failed").in_context("[]:=")))?,
        };
        if ss.len() == ROMBERG_POINTS {
            hs.remove(0);
            ss.remove(0);
        }
        hs.push(h.clone());
        ss.push(s);
        h = h.mul_2exp(-2);
        if j > ROMBERG_POINTS as i64 {
            let (v, dv) = neville(&hs, &ss, &Real::zero(d), d).expect("distinct points");
            let tol = arith(it, BinOp::Mul, eps.clone(), Value::real(v.abs()), hidden_inner)?;
            if matches!(arith(it, BinOp::Lt, Value::real(dv.abs()), tol, hidden_inner)?, Value::Bool(true)) {
                return one(Value::real(v));
            }
        }
    }
    Err(exceeded_steps())
}

/// `NumericalDerivative(f, n, z)`: the n-th derivative of f at z of d
/// digits from its values at the n + 1 points `x_k = z - h + ks`, `s =
/// 2h/n`, `h = 10^(L - d/2)` for `10^L <= ⌈|z|⌉ + 1 < 10^(L+1)`: `Σ (-1)^k
/// C(n, k) f(x_k)/(-s)^n` in Magma's arithmetic, with `d + n(d/2 + 2 + L)`
/// digits, in the field of z.
fn numerical_derivative(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(1)?;
    if n.sign() < 0 {
        return Err(super::require(RuntimeError::runtime("Derivative must be at least 0")));
    }
    let n = n.to_i64().filter(|&n| n < 1 << 20).ok_or_else(|| RuntimeError::runtime("Argument 2 is too large"))?;
    let (f, z) = (a.args[0].clone(), a.args[2].clone());
    let zb = bits_of(&z).unwrap();
    let parent = if matches!(z, Value::Complex(_)) { it.complex_field(zb) } else { Value::reals(zb) };
    let r = if n == 0 {
        apply(it, &f, z)?
    } else {
        let d = calyx_flint::digits_for_bits(zb);
        let size = match &z {
            Value::Complex(c) => c.abs(),
            _ => real_at(a, 2).abs(),
        };
        let l = if size.is_finite() { (&size.ceil() + &Integer::one()).to_string().len() as u64 - 1 } else { 0 };
        let bits = bits_for_digits(d + (n as u64 * (d + 4 + 2 * l)).div_ceil(2));
        let h = Real::from_i64(10, bits).pow(&Real::from_i64(2 * l as i64 - d as i64, bits).mul_2exp(-1));
        let step = h.mul_2exp(1).div_i64(n);
        let point = |k: i64| match &z {
            Value::Complex(c) => super::complex::cv(ComplexV::new(c.re.round_to(bits).sub(&h).add(&step.mul_i64(k)), c.im.round_to(bits))),
            _ => Value::real(real_at(a, 2).round_to(bits).sub(&h).add(&step.mul_i64(k))),
        };
        let n = n as u64;
        let sum = tree_sum(it, 0, n + 1, hidden_inner, &mut |it, k| {
            let v = apply(it, &f, point(k as i64))?;
            let c = Integer::binomial_u64(n, k);
            arith(it, BinOp::Mul, v, Value::Int(if k % 2 == 1 { -c } else { c }), hidden_inner)
        })?;
        arith(it, BinOp::Div, sum, Value::real(step.neg().pow_i64(n as i64)), hidden_inner)?
    };
    one(it.coerce(&parent, &r).map_err(|e| hidden_inner(e.in_context("!")))?)
}

/// `DiscreteFourierTransform(E)`: `F[k] = Σ_j E[j] e^(-2πi(j-1)(k-1)/n)`.
fn discrete_fourier_transform(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Seq(s) = &a.args[0] else { unreachable!() };
    let bits = s.universe.as_ref().and_then(bits_of).unwrap_or_else(default_bits);
    let v: Vec<calyx_flint::Complex> = s.elems.iter().map(|z| super::complex::to_complex(z, bits).unwrap()).collect();
    let w = calyx_flint::quadrature::dft(&v, bits);
    one(Value::seq(s.universe.clone(), w.into_iter().map(super::complex::cv).collect()))
}

fn mpfr_version(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(&calyx_flint::mpfr::version()))
}

fn gmp_version(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(&calyx_flint::mpfr::gmp_version()))
}

/// calyx computes complex functions with FLINT's ball arithmetic instead
/// of MPC.
fn mpc_version(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str("none"))
}

fn extended_reals(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::extended_reals())
}

fn infinity(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Infinity(true))
}

fn minus_infinity(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Infinity(false))
}

fn infinity_abs(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Infinity(true))
}

fn infinity_sign(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(if matches!(a.args[0], Value::Infinity(true)) { 1 } else { -1 }))
}

fn infinity_is_finite(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Bool(false))
}

fn infinity_itself(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(a.args[0].clone())
}

pub fn register(it: &mut Interp) {
    relations::register(it);
    it.def("Infinity", "-> Infty", "Positive infinity.", infinity);
    it.def("ExtendedReals", "-> ExtRe", "The real numbers together with plus and minus infinity.", extended_reals);
    it.def("MinusInfinity", "-> Infty", "Negative infinity.", minus_infinity);
    it.def("Abs", "x::Infty -> Infty", "Positive infinity.", infinity_abs);
    it.def("Sign", "x::Infty -> RngIntElt", "The sign of x.", infinity_sign);
    it.def("IsFinite", "x::Infty -> BoolElt", "False: x is infinite.", infinity_is_finite);
    for name in ["Floor", "Ceiling", "Round"] {
        it.def(name, "x::Infty -> Infty", "x itself.", infinity_itself);
    }

    // Fields.
    it.def("RealField", "-> FldRe", "The default real field.", real_field);
    it.def_params("RealField", "p::RngIntElt -> FldRe", &[("Bits", Value::Bool(false))], "The real field with p decimal digits of precision (or p bits with Bits).", real_field);
    it.def("RealField", "C::FldCom -> FldRe", "The real field of the precision of C.", real_field);
    it.def("GetDefaultRealField", "-> FldRe", "The parent of real literals.", get_default_real_field);
    it.def("SetDefaultRealField", "R::FldRe", "Make R the parent of real literals and the default real field.", set_default_real_field);
    it.def("GetMPFRVersion", "-> MonStgElt", "The version of MPFR used.", mpfr_version);
    it.def("GetGMPVersion", "-> MonStgElt", "The version of GMP used.", gmp_version);
    it.def("GetMPCVersion", "-> MonStgElt", "\"none\": calyx computes with FLINT's complex balls instead of MPC.", mpc_version);
    for t in ["FldRe", "FldCom"] {
        it.def("Identity", &format!("R::{t} -> {t}Elt"), "The one of R.", identity);
        it.def("Precision", &format!("R::{t} -> RngIntElt"), "The decimal precision of R.", precision);
        it.def("BitPrecision", &format!("R::{t} -> RngIntElt"), "The precision of R in bits.", bit_precision);
        it.def("Pi", &format!("R::{t} -> {t}Elt"), "Pi in R.", pi);
        it.def("EulerGamma", &format!("R::{t} -> {t}Elt"), "Euler's constant in R.", euler_gamma);
        it.def("Catalan", &format!("R::{t} -> {t}Elt"), "Catalan's constant in R.", catalan);
    }
    for t in ["FldReElt", "FldComElt"] {
        it.def("Precision", &format!("x::{t} -> RngIntElt"), "The decimal precision of the parent of x.", precision);
        it.def("BitPrecision", &format!("x::{t} -> RngIntElt"), "The precision in bits of the parent of x.", bit_precision);
        it.def("Precision", &format!("L::[{t}] -> RngIntElt"), "The decimal precision of the universe of L.", precision);
        it.def("ChangePrecision", &format!("x::{t}, n::RngIntElt -> {t}"), "x in the field of precision n.", change_precision);
        for u in ["FldReElt", "FldComElt"] {
            it.def_params("Distance", &format!("x::{t}, L::[{u}] -> FldReElt, RngIntElt"), &[("Max", Value::Infinity(true))], "The least distance from x to an element of L, and its index.", distance);
        }
        it.def_params("Diameter", &format!("L::[{t}] -> FldReElt"), &[("Max", Value::Infinity(true))], "The least distance between distinct elements of L.", diameter);
    }

    // Elements.
    for t in ["FldReElt", "FldComElt"] {
        it.def("MantissaExponent", &format!("x::{t} -> RngIntElt, RngIntElt"), "Integers m, e with x = m*2^e, m of the precision of x.", mantissa_exponent);
    }
    for name in ["Floor", "Ceiling"] {
        it.def(name, "x::FldComElt -> RngIntElt", "The corresponding integer for a complex number whose imaginary part is zero.", complex_real_rounding);
    }
    it.def("IsIntegral", "x::FldReElt -> BoolElt", "Whether x is an integer.", is_integral);
    it.def("ComplexConjugate", "x::FldReElt -> FldReElt", "x itself.", conjugate);
    it.def("Norm", "x::FldReElt -> FldReElt", "The absolute value of x.", abs);
    for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
        it.def("Modulus", &format!("x::{t} -> FldReElt"), "The absolute value of x as a real number.", abs);
        for name in ["Arg", "Argument"] {
            it.def(name, &format!("x::{t} -> FldReElt"), "The argument of x (0, or pi if x is negative).", arg);
        }
        for name in ["Sqrt", "SquareRoot"] {
            it.def(name, &format!("x::{t} -> FldReElt"), "The square root of x (a complex number if x < 0).", sqrt);
        }
        it.def("Root", &format!("x::{t}, n::RngIntElt -> FldReElt"), "The real n-th root of x.", root);
        for name in ["Real", "Re"] {
            it.def(name, &format!("x::{t} -> FldReElt"), "The real part of x.", real_part);
        }
        for name in ["Imaginary", "Im"] {
            it.def(name, &format!("x::{t} -> FldReElt"), "The imaginary part of x (zero).", imaginary_part);
        }
    }

    // Transcendental functions; integers and rationals are in the default
    // field (and their dilogarithm is complex, as in Magma).
    for (name, doc) in REAL_FUNCTIONS {
        for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
            if name != "Dilog" || t == "FldReElt" {
                it.def(name, &format!("x::{t} -> FldReElt"), doc, real_function);
            }
        }
    }
    for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
        it.def("Sincos", &format!("x::{t} -> FldReElt, FldReElt"), "The sine and the cosine of x.", sincos);
        for u in ["RngIntElt", "FldRatElt", "FldReElt"] {
            it.def("Log", &format!("b::{t}, x::{u} -> FldReElt"), "The logarithm of x to the base b.", log_base);
            for name in ["Arctan", "Arctan2"] {
                it.def(name, &format!("x::{t}, y::{u} -> FldReElt"), "The angle of the point (x, y) in (-pi, pi], the inverse tangent of y/x.", arctan2);
            }
        }
    }
    for sig in ["b::FldComElt, x::. -> FldReElt", "b::., x::FldComElt -> FldReElt"] {
        it.def("Log", sig, "The logarithm of x to the base b when complex arguments are real.", log_base);
    }
    for name in ["Arctan", "Arctan2"] {
        for sig in ["x::FldComElt, y::. -> FldReElt", "x::., y::FldComElt -> FldReElt"] {
            it.def(name, sig, "The angle of a point whose complex coordinates are real.", arctan2);
        }
    }

    // Gamma, Bessel and associated functions; integers and rationals are in
    // the default field.
    const REAL_ARGS: [&str; 3] = ["RngIntElt", "FldRatElt", "FldReElt"];
    for t in ["RngIntElt", "FldRatElt", "FldReElt", "FldComElt"] {
        let r = if t == "FldComElt" { t } else { "FldReElt" };
        it.def("Gamma", &format!("x::{t} -> {r}"), "The gamma function of x.", gamma_function);
        it.def("LogGamma", &format!("x::{t} -> {r}"), "The logarithm of the gamma function of x (its principal branch).", gamma_function);
        for name in ["Psi", "LogDerivative"] {
            it.def(name, &format!("x::{t} -> {r}"), "The logarithmic derivative of the gamma function at x.", gamma_function);
        }
    }
    let incomplete = [("Complementary", Value::Bool(false)), ("Gamma", Value::Undef)];
    for t in REAL_ARGS {
        for u in REAL_ARGS {
            it.def_params("Gamma", &format!("s::{t}, t::{u} -> FldReElt"), &incomplete, "The incomplete gamma function: the integral of u^(s-1) e^-u from 0 to t (from t to infinity with Complementary).", incomplete_gamma);
        }
        it.def("GammaD", &format!("s::{t} -> FldReElt"), "The gamma function of s + 1/2.", gamma_d);
        it.def("BesselFunction", &format!("n::RngIntElt, x::{t} -> FldReElt"), "The Bessel function of the first kind J_n(x).", bessel_function);
        it.def("BesselFunctionSecondKind", &format!("n::RngIntElt, x::{t} -> FldReElt"), "The Bessel function of the second kind Y_n(x).", bessel_function);
    }
    for sig in ["s::FldComElt, t::. -> FldReElt", "s::., t::FldComElt -> FldReElt"] {
        it.def_params("Gamma", sig, &incomplete, "The incomplete gamma function when complex arguments are real.", incomplete_gamma);
    }
    it.def("BesselFunction", "n::RngIntElt, x::FldComElt -> FldReElt", "The Bessel function J_n(x) when x is real.", bessel_function);
    for t in ["RngIntElt", "FldReElt"] {
        it.def("JBessel", &format!("n::{t}, x::FldReElt -> FldReElt"), "The Bessel function of the first kind of half-integral order J_(n+1/2)(x).", j_bessel);
    }
    for name in ["KBessel", "KBessel2"] {
        for (t, u) in [("FldReElt", "FldReElt"), ("RngIntElt", "FldReElt"), ("FldRatElt", "FldReElt"), ("FldReElt", "RngIntElt"), ("FldReElt", "FldRatElt"), ("FldComElt", "FldReElt")] {
            let r = if t == "FldComElt" { t } else { "FldReElt" };
            it.def(name, &format!("n::{t}, x::{u} -> {r}"), "The modified Bessel function of the second kind K_n(x), x > 0.", k_bessel);
        }
    }
    for t in REAL_ARGS {
        for u in REAL_ARGS {
            for v in REAL_ARGS {
                it.def("HypergeometricU", &format!("a::{t}, b::{u}, x::{v} -> FldReElt"), "The confluent hypergeometric function U(a, b, x), x > 0.", hypergeometric_u);
            }
        }
    }

    // Other special functions.
    let special = [
        ("Erf", "The error function of x."),
        ("ErrorFunction", "The error function of x."),
        ("Erfc", "The complementary error function of x, 1 - Erf(x)."),
        ("ComplementaryErrorFunction", "The complementary error function of x, 1 - Erf(x)."),
        ("ExponentialIntegral", "The exponential integral Ei(x), the principal value of the integral of e^u/u from minus infinity to x."),
        ("ExponentialIntegralE1", "The exponential integral E1(x), the integral of e^-u/u from x to infinity."),
        ("LogIntegral", "The logarithmic integral li(x) of x >= 0, x /= 1."),
        ("DawsonIntegral", "Dawson's integral e^(-x^2) times the integral of e^(u^2) from 0 to x."),
    ];
    for (name, doc) in special {
        for t in REAL_ARGS {
            it.def(name, &format!("x::{t} -> FldReElt"), doc, special_function);
        }
    }
    for t in ["RngIntElt", "FldRatElt", "FldReElt", "FldComElt"] {
        let r = if t == "FldComElt" { t } else { "FldReElt" };
        it.def("ZetaFunction", &format!("s::{t} -> {r}"), "The Riemann zeta function of s /= 1.", zeta_function);
    }
    for (t, u) in [("FldReElt", "FldReElt"), ("FldComElt", "FldComElt"), ("FldReElt", "FldComElt"), ("FldComElt", "FldReElt")] {
        let r = if t == u && t == "FldReElt" { t } else { "FldComElt" };
        for name in ["AGM", "ArithmeticGeometricMean"] {
            it.def(name, &format!("x::{t}, y::{u} -> {r}"), "The arithmetic-geometric mean of x and y.", agm);
        }
    }
    it.def("ZetaFunction", "R::FldRe, n::RngIntElt -> FldReElt", "The Riemann zeta function of the integer n /= 1, in R.", zeta_function_int);
    it.def("BernoulliNumber", "n::RngIntElt -> FldRatElt", "The n-th Bernoulli number.", bernoulli_number);
    it.def("BernoulliApproximation", "n::RngIntElt -> FldReElt", "The n-th Bernoulli number in the default real field.", bernoulli_approximation);

    // Infinite series.
    it.def("InfiniteSum", "m::Map, i::RngIntElt -> FldReElt", "An approximation to the sum m(i) + m(i+1) + ... (real or complex).", infinite_sum);
    it.def("PositiveSum", "m::Map, i::RngIntElt -> FldReElt", "An approximation to the sum m(i) + m(i+1) + ... of positive terms (van Wijngaarden's transformation).", positive_sum);
    it.def_params("AlternatingSum", "m::Map, i::RngIntElt -> FldReElt", &[("Al", Value::str("Villegas"))], "An approximation to the sum m(i) + m(i+1) + ... of terms of alternating signs.", alternating_sum);

    // Numerical integration.
    it.def("Interpolation", "P::[FldReElt], V::[FldReElt], t::FldReElt -> FldReElt, FldReElt", "The value at t of the polynomial through the points (P[i], V[i]), and an estimate of its error (Neville's algorithm).", interpolation);
    it.def("DiscreteFourierTransform", "E::[FldComElt] -> SeqEnum", "The discrete Fourier transform of E.", discrete_fourier_transform);
    it.def("GaussLegendreIntegrationPoints", "N::RngIntElt, D::RngIntElt -> SeqEnum, SeqEnum", "The nodes and weights of Gauss-Legendre quadrature on N points, to D digits.", gauss_legendre_points);
    for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
        for u in ["RngIntElt", "FldRatElt", "FldReElt"] {
            it.def("GaussJacobiIntegrationPoints", &format!("N::RngIntElt, D::RngIntElt, a::{t}, b::{u} -> SeqEnum, SeqEnum"), "The nodes and weights of Gauss-Jacobi quadrature for the weight (1-x)^a (1+x)^b on N points, to D digits.", gauss_jacobi_points);
        }
    }
    it.def("ClenshawCurtisIntegrationPoints", "N::RngIntElt, D::RngIntElt -> SeqEnum, SeqEnum", "The nodes and weights of Clenshaw-Curtis quadrature on N + 1 points, to D digits.", clenshaw_curtis_points);
    it.def("TanhSinhIntegrationPoints", "N::RngIntElt, h::FldReElt -> SeqEnum, SeqEnum, SeqEnum", "The nodes, weights and extra weights of tanh-sinh quadrature on 2N + 1 points with step h.", tanh_sinh_points);
    let romberg = [("Precision", Value::Undef), ("MaxSteps", Value::int(20)), ("K", Value::int(5))];
    it.def_params("RombergQuadrature", "f::Program, a::FldReElt, b::FldReElt -> FldReElt", &romberg, "The integral of f from a to b by Romberg's method, to relative accuracy Precision (default 1.0e-6) in at most MaxSteps steps.", romberg_quadrature);
    it.def("SimpsonQuadrature", "f::Program, a::FldReElt, b::FldReElt, n::RngIntElt -> FldReElt", "The integral of f from a to b by Simpson's rule on n intervals (n even).", simpson_quadrature);
    it.def("TrapezoidalQuadrature", "f::Program, a::FldReElt, b::FldReElt, n::RngIntElt -> FldReElt", "The integral of f from a to b by the trapezoidal rule on n intervals.", trapezoidal_quadrature);
    for t in ["FldReElt", "FldComElt"] {
        it.def("NumericalDerivative", &format!("f::UserProgram, n::RngIntElt, z::{t} -> {t}"), "The n-th derivative of f at z, from the values of f at n + 1 points near z.", numerical_derivative);
    }
}
