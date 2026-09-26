//! Operators on built-in values.

use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::{Integer, Rational};
use calyx_syntax::ast::BinOp;

use crate::error::{RResult, RuntimeError};
use crate::interp::Interp;
use crate::intrinsics::factseq;
use crate::value::*;

fn rat_of(v: &Value) -> Option<Rational> {
    match v {
        Value::Int(i) => Some(Rational::from_integer(i)),
        Value::Rat(q) => Some((**q).clone()),
        _ => None,
    }
}

fn is_num(v: &Value) -> bool {
    matches!(v, Value::Int(_) | Value::Rat(_))
}

/// The sign of a number or infinity, if `v` is one.
fn extended_sign(v: &Value) -> Option<i32> {
    Some(match v {
        Value::Int(i) => i.sign(),
        Value::Rat(q) => q.sign(),
        Value::Real(r) => r.x.sign(),
        Value::Infinity(pos) => {
            if *pos {
                1
            } else {
                -1
            }
        }
        _ => return None,
    })
}

/// Arithmetic with an infinite operand (the other being a number or
/// infinity).
fn infinity_binop(op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
    use BinOp::*;
    let (Some(sa), Some(sb)) = (extended_sign(a), extended_sign(b)) else {
        return Ok(None);
    };
    let (ia, ib) = (matches!(a, Value::Infinity(_)), matches!(b, Value::Infinity(_)));
    let undefined = || Err(RuntimeError::runtime("Result of computation is not well defined").in_context(op.intrinsic_name()));
    let inf = |s: i32| Ok(Some(Value::Infinity(s > 0)));
    match op {
        Add | Sub => {
            let sb = if op == Sub { -sb } else { sb };
            match (ia, ib) {
                (true, true) if sa != sb => undefined(),
                (true, _) => inf(sa),
                _ => inf(sb),
            }
        }
        Mul => {
            if sa == 0 || sb == 0 {
                return undefined();
            }
            inf(sa * sb)
        }
        Div | IntDiv => match (ia, ib) {
            (true, true) => undefined(),
            (false, true) => Ok(Some(Value::int(0))),
            _ if sb == 0 => Err(div_by_zero().in_context(op.intrinsic_name())),
            _ => inf(sa * sb),
        },
        Mod => Err(RuntimeError::runtime("Bad argument types\nArgument types given: ExtReElt, ExtReElt").in_context("mod")),
        Pow if ia => match b {
            Value::Int(k) if k.sign() > 0 => inf(if sa < 0 && k.is_odd() { -1 } else { 1 }),
            Value::Int(k) if k.sign() < 0 => Ok(Some(Value::int(0))),
            Value::Int(_) => Ok(Some(Value::int(1))),
            _ => Ok(None),
        },
        Eq | Cmpeq => Ok(Some(Value::Bool(a == b))),
        Ne | Cmpne => Ok(Some(Value::Bool(a != b))),
        Lt | Le | Gt | Ge => {
            let o = natural_cmp(a, b).unwrap_or(std::cmp::Ordering::Equal);
            Ok(Some(Value::Bool(match op {
                Lt => o.is_lt(),
                Le => o.is_le(),
                Gt => o.is_gt(),
                _ => o.is_ge(),
            })))
        }
        _ => Ok(None),
    }
}

pub fn div_by_zero() -> RuntimeError {
    RuntimeError::runtime("Division by zero")
}

/// Whether Magma reports errors of `op` without naming it, as it does for
/// arithmetic and comparisons unless the operation is a statement of its
/// own.
pub fn unnamed_op(op: BinOp) -> bool {
    use BinOp::*;
    matches!(op, Add | Sub | Mul | IntDiv | Eq | Ne | Lt | Le | Gt | Ge)
}

/// An error of the operator `op` itself as Magma reports it: + - * div and
/// the comparisons are named only in a statement of their own (`stmt`).
/// Failed requirements (even those an intrinsic for the operator named)
/// are named everywhere but there, except that + - * div and the
/// comparisons never name them.
pub fn op_error(op: BinOp, mut e: RuntimeError, stmt: bool) -> RuntimeError {
    if e.span.is_none() {
        if e.require {
            e.context = Some(if stmt || unnamed_op(op) { String::new() } else { op.intrinsic_name().into() });
        } else if !stmt && unnamed_op(op) && e.context.as_deref() == Some(op.intrinsic_name()) {
            e.context = None;
        }
    }
    e
}

impl Interp {
    pub(crate) fn bad_types(&self, op: BinOp, a: &Value, b: &Value) -> RuntimeError {
        RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}, {}", self.type_name_ext(a), self.type_name_ext(b))).in_context(op.intrinsic_name())
    }

    /// Apply a binary operator (not `and`/`or`, which short-circuit).
    pub fn binop(&mut self, op: BinOp, a: Value, b: Value) -> RResult<Value> {
        // Fast path for small integers.
        if let (Value::Int(x), Value::Int(y)) = (&a, &b) {
            match op {
                BinOp::Add => return Ok(Value::Int(x + y)),
                BinOp::Sub => return Ok(Value::Int(x - y)),
                BinOp::Mul => return Ok(Value::Int(x * y)),
                BinOp::Eq => return Ok(Value::Bool(x == y)),
                BinOp::Ne => return Ok(Value::Bool(x != y)),
                BinOp::Lt => return Ok(Value::Bool(x < y)),
                BinOp::Le => return Ok(Value::Bool(x <= y)),
                BinOp::Gt => return Ok(Value::Bool(x > y)),
                BinOp::Ge => return Ok(Value::Bool(x >= y)),
                _ => {}
            }
        }
        // Fast path for residues and small finite field elements.
        if matches!(a, Value::Small(..)) || matches!(b, Value::Small(..)) {
            if let Some(v) = crate::rings::small_binop(op, &a, &b) {
                return Ok(v);
            }
        }
        // Nearfield elements first: they meet no ring elements.
        let ring_result = if matches!(a, Value::Nfd(_)) || matches!(b, Value::Nfd(_)) {
            self.nfd_binop(op, &a, &b)?
        } else if matches!(a, Value::Sparse(_)) || matches!(b, Value::Sparse(_)) {
            crate::intrinsics::sparse::binop(self, op, &a, &b).map_err(|e| e.in_context(op.intrinsic_name()))?
        } else if matches!(a, Value::Mat(_)) || matches!(b, Value::Mat(_)) {
            crate::intrinsics::matrices::binop(self, op, &a, &b).map_err(|e| e.in_context(op.intrinsic_name()))?
        } else if matches!(a, Value::Elt(_) | Value::Small(..)) || matches!(b, Value::Elt(_) | Value::Small(..)) {
            self.ring_binop(op, &a, &b)?
        } else if matches!(a, Value::Perm(_)) || matches!(b, Value::Perm(_)) {
            self.perm_binop(op, &a, &b)?
        } else if matches!(a, Value::AbElt(_)) || matches!(b, Value::AbElt(_)) {
            self.ab_binop(op, &a, &b)?
        } else if matches!((&a, &b), (Value::Struct(_), Value::Struct(_) | Value::Int(_))) {
            self.ideal_binop(op, &a, &b)?
        } else if factseq::is_fact(&a) || factseq::is_fact(&b) {
            // Factorization sequences compare only with sequences.
            if matches!(op, BinOp::Eq | BinOp::Ne) && !(matches!(a, Value::Seq(_)) && matches!(b, Value::Seq(_))) {
                return Err(self.bad_types(op, &a, &b));
            }
            self.fact_binop(op, &a, &b)?
        } else {
            None
        };
        let builtin = match ring_result {
            Some(v) => Some(v),
            None => self.builtin_binop(op, &a, &b)?,
        };
        match builtin {
            Some(v) => Ok(v),
            None => {
                if let Some(v) = self.dispatch_user_operator(op.intrinsic_name(), vec![a.clone(), b.clone()])? {
                    return Ok(v);
                }
                // `ne`/`cmpne` default to the negation of a user `eq`.
                if matches!(op, BinOp::Ne | BinOp::Cmpne) {
                    if let Some(Value::Bool(e)) = self.dispatch_user_operator("eq", vec![a.clone(), b.clone()])? {
                        return Ok(Value::Bool(!e));
                    }
                }
                // Objects of user types without an 'eq' compare by identity.
                if matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Cmpeq | BinOp::Cmpne) && matches!((&a, &b), (Value::Obj(_), Value::Obj(_))) {
                    let same = a == b;
                    return Ok(Value::Bool(if matches!(op, BinOp::Eq | BinOp::Cmpeq) { same } else { !same }));
                }
                if matches!(op, BinOp::Cmpeq | BinOp::Cmpne) {
                    return Ok(Value::Bool(op == BinOp::Cmpne));
                }
                Err(self.bad_types(op, &a, &b))
            }
        }
    }

    /// `x o:= y`, modifying `x` in place where possible.
    pub fn binop_assign(&mut self, op: BinOp, x: &mut Value, y: Value) -> RResult<()> {
        match (op, &mut *x, &y) {
            (BinOp::Add, Value::Int(a), Value::Int(b)) => {
                *a += b;
                return Ok(());
            }
            (BinOp::Sub, Value::Int(a), Value::Int(b)) => {
                *a -= b;
                return Ok(());
            }
            (BinOp::Mul, Value::Int(a), Value::Int(b)) => {
                *a *= b;
                return Ok(());
            }
            (BinOp::Cat, Value::Seq(s), Value::Seq(t)) if s.universe.is_some() && s.universe == t.universe => {
                Rc::make_mut(s).elems.extend(t.elems.iter().cloned());
                return Ok(());
            }
            (BinOp::Cat, Value::List(s), Value::List(t)) => {
                Rc::make_mut(s).extend(t.iter().cloned());
                return Ok(());
            }
            (BinOp::Join, Value::Set(s), Value::Set(t)) if s.universe.is_some() && s.universe == t.universe => {
                let dst = Rc::make_mut(s).elems_mut();
                for e in t.iter() {
                    dst.insert(e);
                }
                return Ok(());
            }
            (BinOp::Cat, Value::Str(s), Value::Str(t)) => {
                Rc::make_mut(s).push_text(t);
                return Ok(());
            }
            _ => {}
        }
        let cur = x.clone();
        *x = self.binop(op, cur, y)?;
        Ok(())
    }

    fn builtin_binop(&mut self, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
        use BinOp::*;
        use Value::{Bool, Int, List, Seq, Str};
        if matches!(a, Value::Infinity(_)) || matches!(b, Value::Infinity(_)) {
            if let Some(v) = infinity_binop(op, a, b)? {
                return Ok(Some(v));
            }
        }
        if matches!(a, Value::Real(_) | Value::Complex(_)) || matches!(b, Value::Real(_) | Value::Complex(_)) {
            if let Some(v) = crate::intrinsics::reals::num_binop(op, a, b)? {
                return Ok(Some(v));
            }
        }
        Ok(Some(match op {
            Add | Sub | Mul => match (a, b) {
                (Int(x), Int(y)) => Int(match op {
                    Add => x + y,
                    Sub => x - y,
                    _ => x * y,
                }),
                _ if is_num(a) && is_num(b) => {
                    let (x, y) = (rat_of(a).unwrap(), rat_of(b).unwrap());
                    Value::rat(match op {
                        Add => &x + &y,
                        Sub => &x - &y,
                        _ => &x * &y,
                    })
                }
                (Str(x), Str(y)) if op == Mul => Value::str(&format!("{x}{y}")),
                (Value::Map(f), Value::Map(g)) if op == Mul => {
                    let mut parts = Vec::new();
                    for m in [f, g] {
                        match &m.imp {
                            MapImpl::Compose(ms) => parts.extend(ms.iter().cloned()),
                            _ => parts.push(m.clone()),
                        }
                    }
                    Value::Map(Rc::new(MapObj { kind: f.kind, domain: f.domain.clone(), codomain: g.codomain.clone(), imp: MapImpl::Compose(parts) }))
                }
                _ => return Ok(None),
            },
            Div => match (a, b) {
                _ if is_num(a) && is_num(b) => {
                    let (x, y) = (rat_of(a).unwrap(), rat_of(b).unwrap());
                    Value::rat(x.checked_div(&y).ok_or_else(|| div_by_zero().in_context("/"))?)
                }
                _ => return Ok(None),
            },
            IntDiv | Mod => match (a, b) {
                (Int(x), Int(y)) => {
                    // The remainder takes the sign of the divisor.
                    let (q, r) = x.fdiv_qr(y).ok_or_else(|| div_by_zero().in_context(op.intrinsic_name()))?;
                    Int(if op == IntDiv { q } else { r })
                }
                _ if is_num(a) && is_num(b) => {
                    // Rationals with integral values behave like integers.
                    let (x, y) = (rat_of(a).unwrap(), rat_of(b).unwrap());
                    if !x.is_integral() || !y.is_integral() {
                        let msg = "Bad argument types\nArgument types given: FldRatElt, FldRatElt";
                        return Err(RuntimeError::runtime(msg).in_context(op.intrinsic_name()));
                    }
                    let (q, r) = x.numerator().fdiv_qr(&y.numerator()).ok_or_else(|| div_by_zero().in_context(op.intrinsic_name()))?;
                    Int(if op == IntDiv { q } else { r })
                }
                _ => return Ok(None),
            },
            Pow => return self.power(a, b),
            Cat => match (a, b) {
                (Str(x), Str(y)) => Value::str(&format!("{x}{y}")),
                (Seq(x), Seq(y)) => {
                    let u = match (&x.universe, &y.universe) {
                        (None, u) | (u, None) => u.clone(),
                        (Some(p), Some(q)) => Some(self.covering_universe(p, q)?.ok_or_else(|| RuntimeError::runtime("Incompatible sequences").in_context("cat"))?),
                    };
                    let mut elems = Vec::with_capacity(x.elems.len() + y.elems.len());
                    elems.extend(x.elems.iter().cloned());
                    elems.extend(y.elems.iter().cloned());
                    if let Some(u) = &u {
                        if x.universe.as_ref() != Some(u) || y.universe.as_ref() != Some(u) {
                            for e in elems.iter_mut() {
                                if !e.is_undef() {
                                    *e = self.coerce_into_universe(u, e).map_err(|e| e.in_context("cat"))?;
                                }
                            }
                        }
                    }
                    Value::seq(u, elems)
                }
                (List(x), List(y)) => {
                    let mut v = (**x).clone();
                    v.extend(y.iter().cloned());
                    Value::list(v)
                }
                _ => return Ok(None),
            },
            Join | Meet | Diff | Sdiff => return self.set_op(op, a, b),
            Eq | Ne => {
                let e = self.compare_eq(a, b, true).map_err(|mut e| {
                    if op == Ne && e.context.as_deref() == Some("eq") {
                        e.context = Some("ne".into());
                    }
                    e
                })?;
                match e {
                    Some(e) => Bool(if op == Eq { e } else { !e }),
                    None => return Ok(None),
                }
            }
            Cmpeq | Cmpne => {
                let e = self.compare_eq(a, b, false)?;
                match e {
                    Some(e) => Bool(if op == Cmpeq { e } else { !e }),
                    None => return Ok(None),
                }
            }
            Lt | Le | Gt | Ge => match self.compare_ord(a, b)? {
                Some(o) => Bool(match op {
                    Lt => o == Ordering::Less,
                    Le => o != Ordering::Greater,
                    Gt => o == Ordering::Greater,
                    _ => o != Ordering::Less,
                }),
                None => return Ok(None),
            },
            In | Notin => {
                let c = self.contains(b, a).map_err(|mut e| {
                    if op == Notin && e.context.as_deref() == Some("in") {
                        e.context = Some("notin".into());
                    }
                    e
                })?;
                Bool(if op == In { c } else { !c })
            }
            Subset | Notsubset => match self.subset(a, b)? {
                Some(s) => Bool(if op == Subset { s } else { !s }),
                None => return Ok(None),
            },
            And | Or | Xor => match (a, b) {
                (Bool(x), Bool(y)) => Bool(match op {
                    And => *x && *y,
                    Or => *x || *y,
                    _ => x != y,
                }),
                _ => return Ok(None),
            },
            Adj | Notadj => return Ok(None),
        }))
    }

    fn power(&mut self, a: &Value, b: &Value) -> RResult<Option<Value>> {
        let Value::Int(e) = b else {
            return Ok(None);
        };
        Ok(Some(match a {
            Value::Int(x) => {
                let too_large = || RuntimeError::runtime("Argument 2 is too large").in_context("^");
                // 0, 1 and -1 take any power (0 even a huge negative one).
                if x.bits() <= 1 && e.to_i64().is_none() {
                    return Ok(Some(Value::Int(if x.sign() < 0 && e.is_odd() { Integer::from_i64(-1) } else { x.abs() })));
                }
                if e.sign() >= 0 {
                    let e = e.to_u64().ok_or_else(too_large)?;
                    if x.bits() > 1 && e > (1 << 36) {
                        return Err(too_large());
                    }
                    Value::Int(x.pow(e))
                } else {
                    if x.is_zero() {
                        return Err(RuntimeError::runtime("Illegal negative power of zero element").in_context("^"));
                    }
                    // 1 and -1 take any power; others small ones only.
                    let q = Rational::from_integer(x);
                    let e = e.to_i64().filter(|v| x.bits() <= 1 || v.unsigned_abs() < 1 << 30).ok_or_else(too_large)?;
                    Value::rat(q.pow(e).ok_or_else(|| div_by_zero().in_context("^"))?)
                }
            }
            Value::Rat(q) => {
                if q.is_zero() && e.sign() < 0 {
                    return Err(RuntimeError::runtime("Illegal negative power of zero element").in_context("^"));
                }
                let e = e.to_i64().filter(|v| v.unsigned_abs() < 1 << 30).ok_or_else(|| RuntimeError::runtime(format!("Argument 2 ({e}) is too large")).in_context("^"))?;
                Value::rat(q.pow(e).ok_or_else(|| div_by_zero().in_context("^"))?)
            }
            Value::Str(s) => {
                let n = e.to_u64().ok_or_else(|| RuntimeError::runtime("Exponent must be non-negative").in_context("^"))?;
                Value::str(&s.repeat(n as usize))
            }
            _ => return Ok(None),
        }))
    }

    pub fn negate(&mut self, v: Value) -> RResult<Value> {
        match v {
            Value::Infinity(pos) => Ok(Value::Infinity(!pos)),
            Value::Int(i) => Ok(Value::Int(-i)),
            Value::Rat(q) => Ok(Value::rat(-&*q)),
            Value::Real(r) => Ok(Value::Real(Rc::new(RealV { x: r.x.neg(), fixed: r.fixed }))),
            Value::Complex(c) => Ok(crate::intrinsics::complex::negate(&c)),
            Value::Elt(e) => self.ring_negate(&e),
            Value::Small(r, x) => Ok(Value::Small(r, r.neg(x))),
            Value::AbElt(x) => Ok(x.neg()),
            Value::Nfd(x) => crate::intrinsics::nearfields::negate(&x),
            Value::Mat(m) => crate::intrinsics::matrices::negate(&m),
            Value::Sparse(m) => crate::intrinsics::sparse::negate(self, &m),
            other => self.unary_intrinsic("-", other),
        }
    }

    pub fn unary_intrinsic(&mut self, name: &str, v: Value) -> RResult<Value> {
        if let Some(r) = self.dispatch_user_operator(name, vec![v.clone()])? {
            return Ok(r);
        }
        Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", self.type_name_ext(&v))).in_context(name))
    }

    /// `#x`
    pub fn cardinality(&mut self, v: &Value) -> RResult<Value> {
        let n = match v {
            Value::Seq(s) => s.elems.len(),
            Value::Set(s) => s.len(),
            Value::ISet(s) => s.elems.len(),
            Value::MSet(s) => return Ok(Value::Int(Integer::from_u64(s.total()))),
            Value::Str(s) => s.len(),
            Value::Tuple(t) => t.elems.len(),
            Value::List(l) => l.len(),
            Value::Assoc(a) => a.map.len(),
            Value::ECat(t) => t.args().len(),
            Value::Cat(_) => 0,
            Value::Struct(s) => match &s.kind {
                StructKind::Booleans => 2,
                StructKind::Cartesian(parts) => {
                    let mut prod = Integer::one();
                    for p in parts.clone() {
                        match self.cardinality(&p)? {
                            Value::Int(n) => prod = &prod * &n,
                            _ => return Err(RuntimeError::runtime("Structure is not finite").in_context("#")),
                        }
                    }
                    return Ok(Value::Int(prod));
                }
                // For a coproduct, # gives the number of constituents.
                StructKind::Coproduct(parts) => parts.len(),
                StructKind::RecFormat(r) => r.names.len(),
                StructKind::SymGroup(n) => return Ok(Value::Int(Integer::factorial(*n as u64))),
                StructKind::AbGroup(g) => return Ok(g.order().map_or(Value::Infinity(true), Value::Int)),
                StructKind::Nearfield(n) => return Ok(Value::Int(n.order())),
                // An ideal of an affine algebra counts as the algebra, as in Magma.
                StructKind::AffIdeal(id) => return self.cardinality(&Value::Struct(id.algebra.clone())),
                StructKind::Ring(r) if matches!(r.kind, crate::rings::RingKind::MPolyRes { .. }) => {
                    let crate::rings::RingKind::MPolyRes { affine, .. } = &r.kind else { unreachable!() };
                    return match crate::intrinsics::poly_ideals::affine_cardinality(affine).map_err(|e| e.in_context("#"))? {
                        Some(n) => Ok(Value::Int(n)),
                        None => Err(RuntimeError::runtime("Cardinality is infinite or not feasibly computable").in_context("#")),
                    };
                }
                _ if crate::rings::props::ring_props(v).is_some() => {
                    return Ok(match crate::rings::props::ring_props(v).unwrap().cardinality {
                        Some(n) => Value::Int(n),
                        None if crate::rings::ring_of(v).is_some_and(|(_, r)| matches!(r.kind, crate::rings::RingKind::UPolyRes { .. })) => {
                            return Err(RuntimeError::runtime("Cardinality is infinite or not feasibly computable").in_context("#"));
                        }
                        None => Value::Infinity(true),
                    });
                }
                _ => {
                    if let Some(r) = self.dispatch_user_operator("#", vec![v.clone()])? {
                        return Ok(r);
                    }
                    return Err(RuntimeError::runtime("Structure is not finite (or its cardinality is not known)").in_context("#"));
                }
            },
            other => return self.unary_intrinsic("#", other.clone()),
        };
        Ok(Value::int(n as i64))
    }

    // ----- equality and order ---------------------------------------------

    /// Equality with coercion to a common structure. `strict` makes
    /// incomparable values an error (`eq`); otherwise they are unequal
    /// (`cmpeq`). `None` means no built-in rule applies.
    pub fn compare_eq(&mut self, a: &Value, b: &Value, strict: bool) -> RResult<Option<bool>> {
        use Value::{Assoc, Bool, Cat, CopElt, ECat, Formal, Func, ISet, Int, Intr, Io, List, MSet, Map, Obj, Rec, Seq, Set, Str, Struct, Tuple};
        let incompatible = |msg: &str| -> RResult<Option<bool>> {
            if strict {
                Err(RuntimeError::runtime(msg.to_string()).in_context("eq"))
            } else {
                Ok(Some(false))
            }
        };
        if matches!(a, Value::Sparse(_)) || matches!(b, Value::Sparse(_)) {
            return match crate::intrinsics::sparse::equal(self, a, b) {
                Ok(e) => Ok(Some(e)),
                Err(e) if strict => Err(e.in_context("eq")),
                Err(_) => Ok(Some(false)),
            };
        }
        if matches!(a, Value::Mat(_)) || matches!(b, Value::Mat(_)) {
            return match crate::intrinsics::matrices::equal(self, a, b) {
                Ok(e) => Ok(Some(e)),
                Err(e) if strict => Err(e.in_context("eq")),
                Err(_) => Ok(Some(false)),
            };
        }
        if matches!(a, Value::Elt(_) | Value::Small(..)) || matches!(b, Value::Elt(_) | Value::Small(..)) {
            let op = if strict { BinOp::Eq } else { BinOp::Cmpeq };
            return match self.ring_binop(op, a, b)? {
                Some(Value::Bool(e)) => Ok(Some(e)),
                _ => incompatible("Arguments are not compatible"),
            };
        }
        // Record formats cannot be compared.
        if let (Struct(x), Struct(y)) = (a, b) {
            if matches!(x.kind, StructKind::RecFormat(_)) && matches!(y.kind, StructKind::RecFormat(_)) {
                return Ok(None);
            }
            if crate::intrinsics::nearfields::different_kinds(x, y) {
                return incompatible(&format!("Bad argument types\nArgument types given: {}, {}", self.type_name(a), self.type_name(b)));
            }
            if let (StructKind::SymGroup(m), StructKind::SymGroup(n)) = (&x.kind, &y.kind) {
                if m != n {
                    return incompatible("Could not find a covering group");
                }
            }
            if matches!((&x.kind, &y.kind), (StructKind::AbGroup(_), StructKind::AbGroup(_))) && !Rc::ptr_eq(x, y) {
                return incompatible("Could not find a covering module");
            }
            if !Rc::ptr_eq(x, y) {
                if crate::rings::finite::field_of(x).is_some() && crate::rings::finite::field_of(y).is_some() {
                    return match crate::rings::finite::field_eq(x, y) {
                        Ok(e) => Ok(Some(e)),
                        Err(msg) => incompatible(msg),
                    };
                }
                if let (Some(_), Some(_)) = (crate::rings::props::ring_props(a), crate::rings::props::ring_props(b)) {
                    use crate::rings::RingKind;
                    let types = format!("Argument types given: {}, {}", self.type_name_ext(a), self.type_name_ext(b));
                    let kind = |s: &crate::value::Struct| match &s.kind {
                        StructKind::Ring(r) => match &r.kind {
                            RingKind::UPoly { base, .. } => (1, Some(base.clone())),
                            RingKind::MPoly { .. } => (2, None),
                            _ => (0, None),
                        },
                        _ => (0, None),
                    };
                    // The integers and rationals compare; other rings of
                    // different kinds cannot.
                    if a.type_id() != b.type_id() {
                        if matches!((&x.kind, &y.kind), (StructKind::Integers, StructKind::Rationals) | (StructKind::Rationals, StructKind::Integers)) {
                            return Ok(Some(false));
                        }
                        return incompatible(&format!("Bad argument types\n{types}"));
                    }
                    match (kind(x), kind(y)) {
                        ((1, Some(p)), (1, Some(q))) if p != q => return incompatible(&format!("Arguments are not compatible\n{types}")),
                        // Univariate polynomial rings over the same ring are equal.
                        ((1, Some(_)), (1, Some(_))) => return Ok(Some(true)),
                        ((2, _), (2, _)) => return incompatible(&format!("Arguments are not compatible\n{types}")),
                        _ => {}
                    }
                }
            }
        }
        if matches!(a, Value::Infinity(_)) || matches!(b, Value::Infinity(_)) {
            if extended_sign(a).is_some() && extended_sign(b).is_some() {
                return Ok(Some(a == b));
            }
        }
        if let (Value::Perm(x), Value::Perm(y)) = (a, b) {
            if x.degree() != y.degree() {
                return incompatible("Arguments are not compatible\nArgument types given: GrpPermElt, GrpPermElt");
            }
            return Ok(Some(x.images == y.images));
        }
        if let (Map(x), Map(y)) = (a, b) {
            if !Rc::ptr_eq(x, y) && (matches!(x.imp, MapImpl::Native(_)) || matches!(y.imp, MapImpl::Native(_))) {
                return incompatible("Cannot test equality for those maps");
            }
        }
        if let (Value::AbElt(x), Value::AbElt(y)) = (a, b) {
            if !Rc::ptr_eq(&x.group, &y.group) {
                return incompatible("Arguments are not compatible\nArgument types given: GrpAbElt, GrpAbElt");
            }
            return Ok(Some(x.coords == y.coords));
        }
        if let (Value::Nfd(x), Value::Nfd(y)) = (a, b) {
            return crate::intrinsics::nearfields::nfd_equal(x, y).map(Some);
        }
        if let (Value::Drch(x), Value::Drch(y)) = (a, b) {
            return Ok(Some(crate::intrinsics::residue::dirichlet::equal(x, y)));
        }
        if let Some(e) = crate::intrinsics::reals::num_eq(a, b) {
            return Ok(Some(e));
        }
        Ok(Some(match (a, b) {
            (Int(x), Int(y)) => x == y,
            (Bool(x), Bool(y)) => x == y,
            (Str(x), Str(y)) => x == y,
            _ if is_num(a) && is_num(b) => rat_of(a) == rat_of(b),
            (Seq(x), Seq(y)) => {
                if let (Some(u), Some(v)) = (&x.universe, &y.universe) {
                    if self.covering_universe(u, v)?.is_none() {
                        return incompatible("Incompatible sequences");
                    }
                }
                if x.elems.len() != y.elems.len() {
                    return Ok(Some(false));
                }
                for (p, q) in x.elems.iter().zip(&y.elems) {
                    if p.is_undef() || q.is_undef() {
                        if p.is_undef() != q.is_undef() {
                            return Ok(Some(false));
                        }
                        continue;
                    }
                    match self.compare_eq(p, q, strict)? {
                        Some(true) => {}
                        Some(false) => return Ok(Some(false)),
                        None => return Ok(None),
                    }
                }
                true
            }
            (Set(_), Set(_)) | (ISet(_), ISet(_)) | (MSet(_), MSet(_)) => {
                if let (Some(u), Some(v)) = (agg_universe(a), agg_universe(b)) {
                    if self.covering_universe(&u, &v)?.is_none() {
                        return incompatible("Incompatible sets");
                    }
                }
                a == b
            }
            (Tuple(x), Tuple(y)) => {
                if x.elems.len() != y.elems.len() {
                    return incompatible("Incompatible tuples");
                }
                for (p, q) in x.elems.iter().zip(&y.elems) {
                    match self.compare_eq(p, q, strict)? {
                        Some(true) => {}
                        Some(false) => return Ok(Some(false)),
                        None => return if strict { Ok(None) } else { Ok(Some(false)) },
                    }
                }
                true
            }
            (List(x), List(y)) => {
                if x.len() != y.len() {
                    return Ok(Some(false));
                }
                for (p, q) in x.iter().zip(y.iter()) {
                    if !self.values_equal_weak(p, q)? {
                        return Ok(Some(false));
                    }
                }
                true
            }
            (Rec(_), Rec(_))
            | (Assoc(_), Assoc(_))
            | (Func(_), Func(_))
            | (Intr(_), Intr(_))
            | (Map(_), Map(_))
            | (Struct(_), Struct(_))
            | (Cat(_), Cat(_))
            | (ECat(_), ECat(_))
            | (Cat(_), ECat(_))
            | (ECat(_), Cat(_))
            | (Value::Err(_), Value::Err(_))
            | (CopElt(_), CopElt(_))
            | (Formal(_), Formal(_))
            | (Io(_), Io(_)) => a == b,
            (Obj(_), _) | (_, Obj(_)) => return Ok(None),
            (CopElt(c), other) | (other, CopElt(c)) if !matches!(other, CopElt(_)) => {
                let v = c.value.clone();
                return self.compare_eq(&v, other, strict);
            }
            (Struct(_), Seq(_) | Set(_)) | (Seq(_) | Set(_), Struct(_)) => false,
            _ => {
                if strict {
                    return Ok(None);
                }
                false
            }
        }))
    }

    /// Equality as used by `case`, sequences of mixed content, etc.:
    /// errors on incomparable values, like `eq`.
    pub fn values_equal(&mut self, a: &Value, b: &Value) -> RResult<bool> {
        match self.binop(BinOp::Eq, a.clone(), b.clone())? {
            Value::Bool(x) => Ok(x),
            _ => Err(RuntimeError::runtime("'eq' must return a boolean")),
        }
    }

    /// Equality that treats incomparable values as unequal (`cmpeq`).
    pub fn values_equal_weak(&mut self, a: &Value, b: &Value) -> RResult<bool> {
        match self.binop(BinOp::Cmpeq, a.clone(), b.clone())? {
            Value::Bool(x) => Ok(x),
            _ => Ok(false),
        }
    }

    pub fn compare_ord(&mut self, a: &Value, b: &Value) -> RResult<Option<Ordering>> {
        use Value::*;
        if let Some(o) = crate::intrinsics::reals::num_cmp(a, b) {
            return Ok(Some(o));
        }
        Ok(Some(match (a, b) {
            (Int(x), Int(y)) => x.cmp(y),
            _ if is_num(a) && is_num(b) => rat_of(a).unwrap().cmp(&rat_of(b).unwrap()),
            (Str(x), Str(y)) => x.cmp(y),
            (Bool(x), Bool(y)) => x.cmp(y),
            (Infinity(_), _) | (_, Infinity(_)) => return Ok(natural_cmp(a, b)),
            (Elt(x), Elt(y)) if x.ring().id == y.ring().id => {
                let ring = x.ring_rc();
                return self.ring_elt_cmp(&ring, &x.x, &y.x);
            }
            (Small(r, x), Small(s, y)) if r == s => r.cmp_words(*x, *y),
            (Seq(x), Seq(y)) => {
                for (p, q) in x.elems.iter().zip(&y.elems) {
                    match self.compare_ord(p, q)? {
                        Some(Ordering::Equal) => {}
                        Some(o) => return Ok(Some(o)),
                        None => return Ok(None),
                    }
                }
                x.elems.len().cmp(&y.elems.len())
            }
            (Tuple(x), Tuple(y)) if x.elems.len() == y.elems.len() => {
                for (p, q) in x.elems.iter().zip(&y.elems) {
                    match self.compare_ord(p, q)? {
                        Some(Ordering::Equal) => {}
                        Some(o) => return Ok(Some(o)),
                        None => return Ok(None),
                    }
                }
                Ordering::Equal
            }
            _ => {
                if let Some(Value::Bool(lt)) = self.dispatch_user_operator("lt", vec![a.clone(), b.clone()])? {
                    if lt {
                        return Ok(Some(Ordering::Less));
                    }
                    if let Some(Value::Bool(gt)) = self.dispatch_user_operator("lt", vec![b.clone(), a.clone()])? {
                        return Ok(Some(if gt { Ordering::Greater } else { Ordering::Equal }));
                    }
                }
                return Ok(None);
            }
        }))
    }

    /// Compare for sorting; errors if the values cannot be ordered.
    pub fn compare_for_sort(&mut self, a: &Value, b: &Value) -> RResult<Ordering> {
        match self.compare_ord(a, b)? {
            Some(o) => Ok(o),
            None => Err(RuntimeError::runtime(format!("Cannot compare objects of types {} and {}", self.type_name(a), self.type_name(b)))),
        }
    }

    // ----- sets -----------------------------------------------------------

    fn set_op(&mut self, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
        let name = op.intrinsic_name();
        let univ = |me: &mut Interp, x: &Option<Value>, y: &Option<Value>| -> RResult<Option<Value>> {
            Ok(match (x, y) {
                (None, u) | (u, None) => u.clone(),
                (Some(p), Some(q)) => Some(me.covering_universe(p, q)?.ok_or_else(|| RuntimeError::runtime("Incompatible sets").in_context(name))?),
            })
        };
        match (a, b) {
            (Value::Set(x), Value::Set(y)) => {
                let u = univ(self, &x.universe, &y.universe)?;
                let xs = self.coerce_all(x.iter(), &u, x.universe.as_ref(), name)?;
                let ys = self.coerce_all(y.iter(), &u, y.universe.as_ref(), name)?;
                let xset: VSet = xs.iter().cloned().collect();
                let yset: VSet = ys.iter().cloned().collect();
                let out: Vec<Value> = match op {
                    BinOp::Join => {
                        let mut s = xset;
                        for v in ys {
                            s.insert(v);
                        }
                        s.into_iter().collect()
                    }
                    BinOp::Meet => xs.into_iter().filter(|v| yset.contains(v)).collect(),
                    BinOp::Diff => xs.into_iter().filter(|v| !yset.contains(v)).collect(),
                    _ => {
                        let mut v: Vec<Value> = xs.iter().filter(|v| !yset.contains(*v)).cloned().collect();
                        v.extend(ys.into_iter().filter(|w| !xset.contains(w)));
                        v
                    }
                };
                let mut out = out;
                sort_values(&mut out);
                Ok(Some(Value::Set(Rc::new(SetEnum::new(u, out.into_iter().collect())))))
            }
            (Value::ISet(x), Value::ISet(y)) => {
                let u = univ(self, &x.universe, &y.universe)?;
                let xs = self.coerce_all(x.elems.iter().cloned(), &u, x.universe.as_ref(), name)?;
                let ys = self.coerce_all(y.elems.iter().cloned(), &u, y.universe.as_ref(), name)?;
                let xset: VSet = xs.iter().cloned().collect();
                let yset: VSet = ys.iter().cloned().collect();
                let out: VSet = match op {
                    BinOp::Join => {
                        let mut s = xset;
                        for v in ys {
                            s.insert(v);
                        }
                        s
                    }
                    BinOp::Meet => xs.into_iter().filter(|v| yset.contains(v)).collect(),
                    BinOp::Diff => xs.into_iter().filter(|v| !yset.contains(v)).collect(),
                    _ => {
                        let mut v: VSet = xs.iter().filter(|v| !yset.contains(*v)).cloned().collect();
                        v.extend(ys.into_iter().filter(|w| !xset.contains(w)));
                        v
                    }
                };
                Ok(Some(Value::ISet(Rc::new(SetIndx { universe: u, elems: out, name: Default::default() }))))
            }
            (Value::MSet(x), Value::MSet(y)) => {
                let u = univ(self, &x.universe, &y.universe)?;
                let conv = |me: &mut Interp, m: &SetMulti| -> RResult<VMap<u64>> {
                    let mut out = VMap::default();
                    for (e, n) in &m.elems {
                        let e = match &u {
                            Some(u) if m.universe.as_ref() != Some(u) => me.coerce_into_universe(u, e).map_err(|e| e.in_context(name))?,
                            _ => e.clone(),
                        };
                        *out.entry(e).or_insert(0) += n;
                    }
                    Ok(out)
                };
                let xm = conv(self, x)?;
                let ym = conv(self, y)?;
                let mut out = VMap::default();
                match op {
                    BinOp::Join => {
                        for (e, n) in xm.iter().chain(ym.iter()) {
                            *out.entry(e.clone()).or_insert(0) += n;
                        }
                    }
                    BinOp::Meet => {
                        for (e, n) in &xm {
                            if let Some(m) = ym.get(e) {
                                out.insert(e.clone(), (*n).min(*m));
                            }
                        }
                    }
                    BinOp::Diff => {
                        for (e, n) in &xm {
                            let m = ym.get(e).copied().unwrap_or(0);
                            if *n > m {
                                out.insert(e.clone(), n - m);
                            }
                        }
                    }
                    _ => {
                        for (e, n) in &xm {
                            let m = ym.get(e).copied().unwrap_or(0);
                            if n.abs_diff(m) > 0 {
                                out.insert(e.clone(), n.abs_diff(m));
                            }
                        }
                        for (e, m) in &ym {
                            if !xm.contains_key(e) {
                                out.insert(e.clone(), *m);
                            }
                        }
                    }
                }
                Ok(Some(Value::MSet(Rc::new(SetMulti { universe: u, elems: out, name: Default::default() }))))
            }
            _ => Ok(None),
        }
    }

    fn coerce_all(&mut self, it: impl Iterator<Item = Value>, u: &Option<Value>, from: Option<&Value>, ctx: &str) -> RResult<Vec<Value>> {
        match u {
            Some(u) if from != Some(u) => {
                let mut out = Vec::new();
                for v in it {
                    out.push(self.coerce_into_universe(u, &v).map_err(|e| e.in_context(ctx.to_string()))?);
                }
                Ok(out)
            }
            _ => Ok(it.collect()),
        }
    }

    fn subset(&mut self, a: &Value, b: &Value) -> RResult<Option<bool>> {
        match a {
            Value::Set(x) => {
                for e in x.iter() {
                    if !self.contains(b, &e)? {
                        return Ok(Some(false));
                    }
                }
                Ok(Some(true))
            }
            Value::ISet(x) => {
                for e in x.elems.iter() {
                    if !self.contains(b, e)? {
                        return Ok(Some(false));
                    }
                }
                Ok(Some(true))
            }
            Value::MSet(x) => {
                if let Value::MSet(y) = b {
                    for (e, n) in &x.elems {
                        if y.elems.get(e).copied().unwrap_or(0) < *n {
                            return Ok(Some(false));
                        }
                    }
                    return Ok(Some(true));
                }
                for e in x.elems.keys() {
                    if !self.contains(b, e)? {
                        return Ok(Some(false));
                    }
                }
                Ok(Some(true))
            }
            _ => Ok(None),
        }
    }

    // ----- reduction ------------------------------------------------------

    /// `&op S`
    pub fn reduce(&mut self, op: BinOp, s: &Value) -> RResult<Value> {
        let (universe, null) = match s {
            Value::Seq(q) => (q.universe.clone(), q.universe.is_none()),
            Value::Set(q) => (q.universe.clone(), q.universe.is_none()),
            Value::ISet(q) => (q.universe.clone(), q.universe.is_none()),
            Value::MSet(q) => (q.universe.clone(), q.universe.is_none()),
            // Of the reductions, Magma allows only products on tuples.
            Value::Tuple(_) if op == BinOp::Mul => (None, false),
            other => {
                return Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", self.type_name(other))).in_context(format!("&{}", op.intrinsic_name())));
            }
        };
        let ctx = format!("&{}", op.intrinsic_name());
        let mut it = self.iter_value(s, false)?;
        let Some((_, mut acc)) = it.next_item() else {
            return match op {
                BinOp::And => Ok(Value::Bool(true)),
                BinOp::Or => Ok(Value::Bool(false)),
                BinOp::Add | BinOp::Mul => {
                    if null {
                        let what = if matches!(s, Value::Seq(_)) { "sequence" } else { "set" };
                        return Err(RuntimeError::runtime(format!("Illegal null {what}")).in_context(ctx));
                    }
                    let u = universe.unwrap();
                    let unit = if op == BinOp::Add { self.call_intrinsic_named(crate::sym::Sym::new("Zero"), vec![u.clone()]) } else { self.call_intrinsic_named(crate::sym::Sym::new("One"), vec![u.clone()]) };
                    let what = if op == BinOp::Add { "zero" } else { "one" };
                    unit.map_err(|_| RuntimeError::runtime(format!("Universe has no {what} element")).in_context(ctx))
                }
                BinOp::Join => match universe {
                    Some(Value::Struct(st)) => match &st.kind {
                        StructKind::PowerSet(u) => Ok(Value::Set(Rc::new(SetEnum::new(u.clone(), VSet::default())))),
                        StructKind::PowerISet(u) => Ok(Value::ISet(Rc::new(SetIndx { universe: u.clone(), elems: VSet::default(), name: Default::default() }))),
                        StructKind::PowerMSet(u) => Ok(Value::MSet(Rc::new(SetMulti { universe: u.clone(), elems: VMap::default(), name: Default::default() }))),
                        _ => Err(RuntimeError::runtime("Illegal empty set/sequence").in_context(ctx)),
                    },
                    _ => Ok(Value::Set(Rc::new(SetEnum::new(None, VSet::default())))),
                },
                BinOp::Cat => match universe {
                    Some(Value::Struct(st)) => match &st.kind {
                        StructKind::PowerSeq(u) => Ok(Value::seq(u.clone(), Vec::new())),
                        StructKind::Strings => Ok(Value::str("")),
                        _ => Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", self.type_name_ext(s))).in_context(ctx)),
                    },
                    _ => Ok(Value::seq(None, Vec::new())),
                },
                _ => Err(RuntimeError::runtime("Illegal empty set/sequence").in_context(ctx)),
            };
        };
        // Sums and products group their terms as Magma does, which decides
        // how inexact elements round (#70): a sum adds the sum of the first
        // half (rounded down) to that of the rest, and a product multiplies
        // neighbours level by level, so that its first part is the largest
        // power of two below the count.
        if matches!(op, BinOp::Add | BinOp::Mul) {
            // Sums of integers are exact, so they are added in turn.
            if let (BinOp::Add, Value::Seq(q)) = (op, s) {
                if q.elems.iter().all(|v| matches!(v, Value::Int(_))) {
                    let mut sum = Integer::zero();
                    for v in q.elems.iter() {
                        self.check_interrupt()?;
                        if let Value::Int(x) = v {
                            sum += x;
                        }
                    }
                    return Ok(Value::Int(sum));
                }
            }
            let n = match s {
                Value::Seq(q) => q.elems.iter().filter(|v| !v.is_undef()).count(),
                Value::Set(q) => q.len(),
                Value::ISet(q) => q.elems.len(),
                Value::MSet(q) => q.elems.values().sum::<u64>() as usize,
                Value::Tuple(t) => t.elems.len(),
                _ => unreachable!(),
            };
            let mut first = Some(acc);
            let mut next = || first.take().or_else(|| it.next_item().map(|(_, x)| x));
            let r = self.reduce_tree(op, &mut next, n.max(1));
            return r.map(|v| v.expect("a first term")).map_err(|e| self.reduce_error(op, s, e));
        }
        // Conjunctions, disjunctions and concatenations need suitable
        // aggregates, whatever their length.
        let fits = match op {
            BinOp::And | BinOp::Or => matches!(acc, Value::Bool(_)),
            BinOp::Cat => matches!(acc, Value::Seq(_) | Value::Str(_) | Value::List(_)),
            _ => true,
        };
        if !fits {
            return Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", self.type_name_ext(s))).in_context(ctx));
        }
        while let Some((_, x)) = it.next_item() {
            self.check_interrupt()?;
            let cur = std::mem::take(&mut acc);
            acc = match op {
                BinOp::And | BinOp::Or => match (&cur, &x) {
                    (Value::Bool(p), Value::Bool(q)) => Value::Bool(if op == BinOp::And { *p && *q } else { *p || *q }),
                    _ => return Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", self.type_name_ext(s))).in_context(ctx)),
                },
                _ => {
                    let mut c = cur;
                    if let Err(e) = self.binop_assign(op, &mut c, x) {
                        return Err(self.reduce_error(op, s, e));
                    }
                    c
                }
            };
        }
        Ok(acc)
    }

    /// Magma's error for `&op S` when the elements of `S` lack the
    /// operation.
    fn reduce_error(&mut self, op: BinOp, s: &Value, e: RuntimeError) -> RuntimeError {
        if e.span.is_some() || e.context.as_deref() != Some(op.intrinsic_name()) || !e.message.starts_with("Bad argument types") {
            return e;
        }
        let ctx = format!("&{}", op.intrinsic_name());
        if op == BinOp::Cat {
            return RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", self.type_name_ext(s))).in_context(ctx);
        }
        let first = self.iter_value(s, false).ok().and_then(|mut it| it.next_item());
        let t = first.map_or_else(String::new, |(_, x)| self.type_name(&x));
        RuntimeError::runtime(format!("Operation not defined on elements of type {t}")).in_context(ctx)
    }

    /// The sum or product of the next `n` terms from `next`, grouped as in
    /// `reduce`.
    fn reduce_tree(&mut self, op: BinOp, next: &mut dyn FnMut() -> Option<Value>, n: usize) -> RResult<Option<Value>> {
        if n <= 1 {
            return Ok(if n == 1 { next() } else { None });
        }
        let k = if op == BinOp::Add { n / 2 } else { 1 << (usize::BITS - 1 - (n - 1).leading_zeros()) };
        let a = self.reduce_tree(op, next, k)?;
        let b = self.reduce_tree(op, next, n - k)?;
        Ok(match (a, b) {
            (Some(mut a), Some(b)) => {
                self.check_interrupt()?;
                self.binop_assign(op, &mut a, b)?;
                Some(a)
            }
            (a, b) => a.or(b),
        })
    }

    // ----- maps -----------------------------------------------------------

    pub fn apply_map(&mut self, m: &Rc<MapObj>, x: &Value) -> RResult<Value> {
        if let MapImpl::Native(n) = &m.imp {
            return n.clone().apply(self, m, x);
        }
        let x = match self.try_coerce(&m.domain, x)? {
            Ok(v) => v,
            Err(_) => return Err(RuntimeError::runtime("Element is not in the domain of the map").in_context("map application")),
        };
        let y = match &m.imp {
            MapImpl::Rule { f, .. } => {
                let f = f.clone();
                self.call_function(&f, vec![x])?
            }
            MapImpl::Graph(g) => match g.get(&x) {
                Some(y) => y.clone(),
                None => return Err(RuntimeError::runtime("Application of map failed").in_context("map application")),
            },
            MapImpl::Compose(ms) => {
                let mut v = x;
                for mm in ms.clone() {
                    v = self.apply_map(&mm, &v)?;
                }
                return Ok(v);
            }
            MapImpl::Coercion | MapImpl::Reduction(_) => x,
            MapImpl::Injection(i) => {
                let Value::Struct(st) = &m.codomain else { unreachable!() };
                Value::CopElt(Rc::new(CopElt { cop: st.clone(), index: *i, value: x }))
            }
            MapImpl::Inverse(inner) => {
                let inner = inner.clone();
                return self.map_preimage(&inner, &x);
            }
            MapImpl::Native(_) => unreachable!(),
        };
        if matches!(m.imp, MapImpl::Rule { .. } | MapImpl::Coercion | MapImpl::Reduction(_)) {
            return self.coerce(&m.codomain, &y).map_err(|_| RuntimeError::runtime("Element is not in the codomain of the map").in_context("map application"));
        }
        Ok(y)
    }

    pub fn map_preimage(&mut self, m: &Rc<MapObj>, y: &Value) -> RResult<Value> {
        if let MapImpl::Native(n) = &m.imp {
            return n.clone().preimage(self, m, y);
        }
        let y = match self.try_coerce(&m.codomain, y)? {
            Ok(v) => v,
            Err(_) => return Err(RuntimeError::runtime("Argument is not in the codomain of the map").in_context("@@")),
        };
        match &m.imp {
            MapImpl::Rule { inv: Some(g), .. } => {
                let g = g.clone();
                let x = self.call_function(&g, vec![y])?;
                self.coerce(&m.domain, &x)
            }
            MapImpl::Rule { inv: None, .. } => Err(RuntimeError::runtime("No inverse rule is known for the map").in_context("@@")),
            MapImpl::Graph(g) => g.iter().find(|(_, v)| **v == y).map(|(k, _)| k.clone()).ok_or_else(|| RuntimeError::runtime("Element has no preimage under the map").in_context("@@")),
            MapImpl::Compose(ms) => {
                let mut v = y;
                for mm in ms.clone().iter().rev() {
                    v = self.map_preimage(mm, &v)?;
                }
                Ok(v)
            }
            MapImpl::Coercion | MapImpl::Reduction(_) => self.coerce(&m.domain, &y),
            MapImpl::Injection(i) => match &y {
                Value::CopElt(c) if c.index == *i => Ok(c.value.clone()),
                _ => Err(RuntimeError::runtime("Element has no preimage under the injection").in_context("@@")),
            },
            MapImpl::Inverse(inner) => {
                let inner = inner.clone();
                self.apply_map(&inner, &y)
            }
            MapImpl::Native(_) => unreachable!(),
        }
    }

    /// `x @ f`: also images of sets and sequences.
    pub fn image(&mut self, x: &Value, m: &Value) -> RResult<Value> {
        match m {
            Value::Map(mm) => {
                let mm = mm.clone();
                if self.try_coerce(&mm.domain, x)?.is_err() {
                    match x {
                        Value::Set(_) | Value::Seq(_) | Value::ISet(_) => {
                            let mut out = Vec::new();
                            let mut it = self.iter_value(x, false)?;
                            while let Some((_, e)) = it.next_item() {
                                out.push(self.apply_map(&mm, &e)?);
                            }
                            let kind = match x {
                                Value::Seq(_) => calyx_syntax::ast::AggKind::Seq,
                                Value::ISet(_) => calyx_syntax::ast::AggKind::ISet,
                                _ => calyx_syntax::ast::AggKind::Set,
                            };
                            return self.build_aggregate(kind, Some(mm.codomain.clone()), out, false);
                        }
                        _ => {}
                    }
                }
                self.apply_map(&mm, x)
            }
            Value::Func(_) | Value::Intr(_) => self.call_function(m, vec![x.clone()]),
            _ => {
                // Other values act through the intrinsics for '@'.
                if let Some(v) = self.dispatch_user_operator("@", vec![x.clone(), m.clone()])? {
                    return Ok(v);
                }
                // A statement of its own names '@' (see exec_inner), as f(x) does.
                Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}, {}", self.type_name_ext(x), self.type_name_ext(m))))
            }
        }
    }

    pub fn preimage(&mut self, y: &Value, m: &Value) -> RResult<Value> {
        match m {
            Value::Map(mm) => {
                let mm = mm.clone();
                if self.try_coerce(&mm.codomain, y)?.is_err() {
                    if let Value::Set(_) | Value::Seq(_) = y {
                        let mut out = Vec::new();
                        let mut it = self.iter_value(y, false)?;
                        while let Some((_, e)) = it.next_item() {
                            out.push(self.map_preimage(&mm, &e)?);
                        }
                        let kind = if matches!(y, Value::Seq(_)) { calyx_syntax::ast::AggKind::Seq } else { calyx_syntax::ast::AggKind::Set };
                        return self.build_aggregate(kind, Some(mm.domain.clone()), out, false);
                    }
                }
                self.map_preimage(&mm, y)
            }
            _ => Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}, {}", self.type_name(y), self.type_name(m))).in_context("@@")),
        }
    }
}

fn agg_universe(v: &Value) -> Option<Value> {
    match v {
        Value::Set(s) => s.universe.clone(),
        Value::ISet(s) => s.universe.clone(),
        Value::MSet(s) => s.universe.clone(),
        Value::Seq(s) => s.universe.clone(),
        _ => None,
    }
}
