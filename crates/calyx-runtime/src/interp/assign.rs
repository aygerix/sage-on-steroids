//! Assignment, indexing and attributes.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_syntax::ast::BinOp;

use super::{Frame, Interp};
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::nearfields;
use crate::ir::*;
use crate::sym::Sym;
use crate::value::*;

/// One step of an assignment path below a variable.
pub enum PathElem {
    Index(Value),
    Attr(Sym),
}

/// Where a reference argument came from, for writing it back.
pub enum RefTarget {
    Place(Place),
    Path(Place, Vec<PathElem>),
}

impl Interp {
    // ----- reference arguments ----------------------------------------------

    /// Take the value referred to by `~lv` out of its variable (so it can be
    /// modified in place) and remember where it goes back.
    pub fn take_ref(&mut self, lv: &LV, f: &mut Frame) -> RResult<(RefTarget, Value)> {
        match lv {
            LV::Var(p, _) => Ok((RefTarget::Place(*p), self.take_place(*p, f))),
            LV::Discard => Err(RuntimeError::runtime("'_' cannot be passed by reference")),
            _ => {
                let mut path = Vec::new();
                let Some(root) = self.lv_path(lv, f, &mut path)? else {
                    return Err(RuntimeError::runtime("'_' cannot be passed by reference"));
                };
                let mut rv = self.take_place(root, f);
                if rv.is_undef() {
                    return Err(self.unassigned_place(root));
                }
                let r = self.take_at_path(&mut rv, &path);
                self.put_place(root, rv, f);
                Ok((RefTarget::Path(root, path), r?))
            }
        }
    }

    pub fn put_ref(&mut self, t: RefTarget, v: Value, f: &mut Frame) -> RResult<()> {
        match t {
            RefTarget::Place(p) => {
                self.put_place(p, v, f);
                Ok(())
            }
            RefTarget::Path(root, path) => {
                let mut rv = self.take_place(root, f);
                let r = self.put_at_path(&mut rv, &path, v);
                self.put_place(root, rv, f);
                r
            }
        }
    }

    fn put_at_path(&mut self, cur: &mut Value, path: &[PathElem], v: Value) -> RResult<()> {
        // An unassigned associative array entry that stays unassigned is removed.
        if v.is_undef() {
            if let (Some(PathElem::Index(i)), true, Value::Assoc(a)) = (path.first(), path.len() == 1, &mut *cur) {
                let key = i.clone();
                let a = Rc::make_mut(a);
                a.map.shift_remove(&key);
                return Ok(());
            }
            if path.len() == 1 {
                if let (PathElem::Index(i), Value::Seq(s)) = (&path[0], &mut *cur) {
                    let k = seq_index(i, "Sequence")?;
                    let s = Rc::make_mut(s);
                    if k <= s.elems.len() {
                        s.elems[k - 1] = Value::Undef;
                    }
                    return Ok(());
                }
            }
        }
        self.set_path(cur, path, v)
    }

    fn take_at_path(&mut self, cur: &mut Value, path: &[PathElem]) -> RResult<Value> {
        let Some((first, rest)) = path.split_first() else {
            return Ok(std::mem::take(cur));
        };
        let missing = |k: usize| RuntimeError::runtime(format!("Element {k} is not defined"));
        match first {
            PathElem::Index(i) => match cur {
                Value::Seq(s) => {
                    let k = seq_index(i, "Sequence")?;
                    let s = Rc::make_mut(s);
                    if k > s.elems.len() {
                        return if rest.is_empty() { Ok(Value::Undef) } else { Err(missing(k)) };
                    }
                    self.take_at_path(&mut s.elems[k - 1], rest)
                }
                Value::List(l) => {
                    let k = seq_index(i, "List")?;
                    let l = Rc::make_mut(l);
                    if k > l.len() {
                        return if rest.is_empty() { Ok(Value::Undef) } else { Err(missing(k)) };
                    }
                    self.take_at_path(&mut l[k - 1], rest)
                }
                Value::Tuple(t) => {
                    let k = seq_index(i, "Tuple")?;
                    let t = Rc::make_mut(t);
                    if k > t.elems.len() {
                        return Err(missing(k));
                    }
                    self.take_at_path(&mut t.elems[k - 1], rest)
                }
                Value::Assoc(a) => {
                    let key = match &a.universe {
                        Some(u) => {
                            let u = u.clone();
                            self.try_coerce_into_universe(&u, i)?.unwrap_or_else(|| i.clone())
                        }
                        None => i.clone(),
                    };
                    let a = Rc::make_mut(a);
                    match a.map.get_mut(&key) {
                        Some(v) => self.take_at_path(v, rest),
                        None => {
                            let mut d = a.default.clone().unwrap_or(Value::Undef);
                            if rest.is_empty() {
                                return Ok(d);
                            }
                            if d.is_undef() {
                                return Err(RuntimeError::runtime("Index is not in the domain of the associative array"));
                            }
                            self.take_at_path(&mut d, rest)
                        }
                    }
                }
                other => Err(RuntimeError::runtime(format!("Cannot index an object of type {}", self.type_name(other)))),
            },
            PathElem::Attr(name) => match cur {
                Value::Rec(r) => {
                    let StructKind::RecFormat(rf) = &r.format.kind else { unreachable!() };
                    let Some(k) = rf.names.iter().position(|n| n == name) else {
                        return Err(RuntimeError::runtime(format!("Field '{name}' does not exist in this record")));
                    };
                    let r = Rc::make_mut(r);
                    self.take_at_path(&mut r.fields[k], rest)
                }
                Value::Struct(_) | Value::Obj(_) => {
                    let attrs = match cur {
                        Value::Struct(s) => &s.attrs,
                        Value::Obj(o) => &o.attrs,
                        _ => unreachable!(),
                    };
                    let mut v = attrs.borrow_mut().remove(name).unwrap_or(Value::Undef);
                    let r = self.take_at_path(&mut v, rest);
                    if !rest.is_empty() {
                        attrs.borrow_mut().insert(*name, v);
                    }
                    r
                }
                other => Err(RuntimeError::runtime(format!("Objects of type {} do not have attributes", self.type_name(other)))),
            },
        }
    }

    // ----- places ---------------------------------------------------------

    pub fn take_place(&mut self, p: Place, f: &mut Frame) -> Value {
        match p {
            Place::Local(s, _) => std::mem::take(&mut f.slots[s as usize]),
            Place::Global(n) => {
                if let Some(pkg) = self.package_stack.last_mut() {
                    if let Some(v) = pkg.get_mut(&n) {
                        return std::mem::take(v);
                    }
                    return Value::Undef;
                }
                match self.globals.get_mut(&n) {
                    Some(v) => std::mem::take(v),
                    None => Value::Undef,
                }
            }
        }
    }

    pub fn put_place(&mut self, p: Place, v: Value, f: &mut Frame) {
        // A structure or aggregate is known by the first global it is
        // assigned to (see set_global for structures).
        let mut named = None;
        if let (Place::Global(n), Some(cell)) = (&p, v.name_cell()) {
            if cell.borrow().is_none() {
                *cell.borrow_mut() = Some(*n);
            } else if let Value::Struct(s) = &v {
                named = Some((s.clone(), *n));
            }
        }
        self.store_place(p, v, f);
        // A named structure may change names once the global has its slot.
        if let Some((s, n)) = named {
            self.name_struct(&s, n);
        }
    }

    /// Store a value without naming it.
    pub fn store_place(&mut self, p: Place, v: Value, f: &mut Frame) {
        match p {
            Place::Local(s, _) => f.slots[s as usize] = v,
            // A global left without a value is no longer declared (a `_`
            // result, or a reference argument the callee unassigned).
            Place::Global(n) if v.is_undef() => self.remove_global(n),
            Place::Global(n) => self.set_global(n, v),
        }
    }

    pub fn assign_place(&mut self, p: Place, v: Value, f: &mut Frame) -> RResult<()> {
        self.put_place(p, v, f);
        Ok(())
    }

    fn read_place(&mut self, p: Place, f: &mut Frame) -> RResult<Value> {
        let v = match p {
            Place::Local(s, _) => f.get(s).clone(),
            Place::Global(n) => self.lookup_variable(n).unwrap_or(Value::Undef),
        };
        if v.is_undef() {
            return Err(self.unassigned_place(p));
        }
        Ok(v)
    }

    /// The error for reading an unassigned variable: globals that were
    /// never assigned have not been declared either.
    fn unassigned_place(&self, p: Place) -> RuntimeError {
        match p {
            Place::Global(n) => self.unassigned_error(n),
            _ => RuntimeError::runtime(format!("Variable '{}' has not been initialized", p.name())),
        }
    }

    // ----- l-values -------------------------------------------------------

    /// Flatten an l-value into its root place and the path below it.
    fn lv_path(&mut self, lv: &LV, f: &mut Frame, path: &mut Vec<PathElem>) -> RResult<Option<Place>> {
        match lv {
            LV::Var(p, _) => Ok(Some(*p)),
            LV::Discard => Ok(None),
            LV::Index(b, idx, _) => {
                let root = self.lv_path(b, f, path)?;
                for i in idx {
                    let v = self.eval(i, f)?;
                    path.push(PathElem::Index(v));
                }
                Ok(root)
            }
            LV::Attr(b, n, _) => {
                let root = self.lv_path(b, f, path)?;
                path.push(PathElem::Attr(*n));
                Ok(root)
            }
            LV::AttrDyn(b, e, _) => {
                let root = self.lv_path(b, f, path)?;
                let Value::Str(s) = self.eval(e, f)? else {
                    return Err(RuntimeError::runtime("Attribute name must be a string"));
                };
                path.push(PathElem::Attr(Sym::new(&s)));
                Ok(root)
            }
        }
    }

    pub fn assign(&mut self, lv: &LV, v: Value, f: &mut Frame) -> RResult<()> {
        if let LV::Var(p, _) = lv {
            // A function takes the name of the first identifier it is
            // assigned to.
            if let Value::Func(c) = &v {
                if c.name.get().is_none() {
                    c.name.set(Some(p.name()));
                }
            }
            return self.assign_place(*p, v, f);
        }
        let mut path = Vec::new();
        let Some(root) = self.lv_path(lv, f, &mut path)? else {
            return Ok(());
        };
        let mut cur = self.take_place(root, f);
        if cur.is_undef() && !path.is_empty() {
            let e = match root {
                Place::Local(_, name) => RuntimeError::statement(":=", format!("Variable '{name}' has not been initialized")),
                Place::Global(_) => self.unassigned_place(root),
            };
            return Err(e.at(lv_root_span(lv)));
        }
        // Magma copies a shared factorization sequence (another variable,
        // or $1, holds it) as a plain sequence when an entry is assigned.
        if let (Value::Seq(s), Some(PathElem::Index(_))) = (&mut cur, path.first()) {
            if s.fact && Rc::strong_count(s) > 1 {
                Rc::make_mut(s).fact = false;
            }
        }
        let matrix = matches!(cur, Value::Mat(_) | Value::Sparse(_));
        let r = self.set_path(&mut cur, &path, v);
        self.put_place(root, cur, f);
        // Magma reports errors of assignments into matrices at the index.
        if matrix { r.map_err(|e| e.at(lv_root_span(lv))) } else { r }
    }

    /// Make the target of an assignment unassigned (for `_` results).
    pub fn unassign(&mut self, lv: &LV, f: &mut Frame) -> RResult<()> {
        match lv {
            LV::Var(p, _) => {
                self.put_place(*p, Value::Undef, f);
                Ok(())
            }
            LV::Discard => Ok(()),
            _ => Err(RuntimeError::runtime("Right hand side value is undefined")),
        }
    }

    fn set_path(&mut self, cur: &mut Value, path: &[PathElem], v: Value) -> RResult<()> {
        let Some((first, rest)) = path.split_first() else {
            *cur = v;
            return Ok(());
        };
        let last = rest.is_empty();
        match first {
            PathElem::Index(i) => self.set_index(cur, i, rest, v, last),
            PathElem::Attr(name) => self.set_attr(cur, *name, rest, v),
        }
    }

    fn set_index(&mut self, cur: &mut Value, i: &Value, rest: &[PathElem], v: Value, last: bool) -> RResult<()> {
        match cur {
            Value::Seq(s) => {
                if matches!(i, Value::Seq(_)) {
                    return Err(RuntimeError::runtime("Sequence mutation failed").in_context("[]:="));
                }
                let k = seq_index(i, "Sequence")?;
                if last {
                    let v = match &s.universe {
                        Some(u) => {
                            let u = u.clone();
                            self.coerce_into_universe(&u, &v).map_err(|_| RuntimeError::runtime("Sequence mutation failed").in_context("[]:="))?
                        }
                        None => v,
                    };
                    let s = Rc::make_mut(s);
                    if s.universe.is_none() {
                        s.universe = Some(self.parent_of(&v)?);
                    }
                    if k > s.elems.len() {
                        s.elems.resize(k, Value::Undef);
                    }
                    s.elems[k - 1] = v;
                    return Ok(());
                }
                let s = Rc::make_mut(s);
                if k > s.elems.len() || s.elems[k - 1].is_undef() {
                    return Err(RuntimeError::runtime("Bad indexed assign").in_context("[]:="));
                }
                let mut inner = std::mem::take(&mut s.elems[k - 1]);
                let r = self.set_path(&mut inner, rest, v);
                s.elems[k - 1] = inner;
                r
            }
            Value::List(l) => {
                let k = seq_index(i, "List")?;
                let l = Rc::make_mut(l);
                if last {
                    if k > l.len() + 1 {
                        return Err(RuntimeError::runtime("List index out of range").in_context("[]:="));
                    }
                    if k == l.len() + 1 {
                        l.push(v);
                    } else {
                        l[k - 1] = v;
                    }
                    return Ok(());
                }
                if k > l.len() {
                    return Err(RuntimeError::runtime("List index out of range").in_context("[]:="));
                }
                let mut inner = std::mem::take(&mut l[k - 1]);
                let r = self.set_path(&mut inner, rest, v);
                l[k - 1] = inner;
                r
            }
            Value::Tuple(t) => {
                let k = seq_index(i, "Tuple")?;
                if k > t.elems.len() {
                    return Err(RuntimeError::runtime(format!("Tuple index {k} is out of range")).in_context("[]:="));
                }
                let t = Rc::make_mut(t);
                if last {
                    let v = match &t.parent {
                        Some(Value::Struct(p)) => match &p.kind {
                            StructKind::Cartesian(parts) => {
                                let u = parts[k - 1].clone();
                                self.coerce(&u, &v)?
                            }
                            _ => v,
                        },
                        _ => {
                            t.parent = None;
                            v
                        }
                    };
                    t.elems[k - 1] = v;
                    return Ok(());
                }
                let mut inner = std::mem::take(&mut t.elems[k - 1]);
                let r = self.set_path(&mut inner, rest, v);
                t.elems[k - 1] = inner;
                t.parent = None;
                r
            }
            Value::Assoc(a) => {
                let key = self.assoc_key(a, i)?;
                let a = Rc::make_mut(a);
                if last {
                    a.map.insert(key, v);
                    return Ok(());
                }
                if !a.map.contains_key(&key) {
                    match &a.default {
                        Some(d) => {
                            a.map.insert(key.clone(), d.clone());
                        }
                        None => return Err(RuntimeError::runtime("Index is not in the domain of the associative array").in_context("[]:=")),
                    }
                }
                let slot = a.map.get_mut(&key).unwrap();
                let mut inner = std::mem::take(slot);
                let r = self.set_path(&mut inner, rest, v);
                *a.map.get_mut(&key).unwrap() = inner;
                r
            }
            // A[i, j] := x (or A[i][j] := x) sets an entry of a matrix.
            Value::Mat(_) => {
                let mut ids = vec![i.clone()];
                for step in rest {
                    match step {
                        PathElem::Index(j) => ids.push(j.clone()),
                        PathElem::Attr(_) => return Err(RuntimeError::statement(":=", "Bad argument types")),
                    }
                }
                crate::intrinsics::matrices::set_index(self, cur, &ids, v)
            }
            Value::Sparse(_) => {
                let mut ids = vec![i.clone()];
                for step in rest {
                    match step {
                        PathElem::Index(j) => ids.push(j.clone()),
                        PathElem::Attr(_) => return Err(RuntimeError::statement(":=", "Bad argument types")),
                    }
                }
                crate::intrinsics::sparse::set_index(self, cur, &ids, v)
            }
            Value::ISet(_) => Err(RuntimeError::runtime("Indexed sets cannot be modified by indexing").in_context("[]:=")),
            Value::Str(_) => Err(RuntimeError::runtime("Strings cannot be modified by indexing").in_context("[]:=")),
            other => Err(RuntimeError::runtime(format!("Cannot assign by index into an object of type {}", self.type_name(other))).in_context("[]:=")),
        }
    }

    /// Coerce a key into the index universe of an associative array,
    /// widening the universe (and re-coercing existing keys) if needed.
    fn assoc_key(&mut self, a: &mut Rc<Assoc>, i: &Value) -> RResult<Value> {
        let Some(u) = a.universe.clone() else {
            let p = self.parent_of(i)?;
            Rc::make_mut(a).universe = Some(p);
            return Ok(i.clone());
        };
        if let Some(k) = self.try_coerce_into_universe(&u, i)? {
            return Ok(k);
        }
        let p = self.parent_of(i)?;
        // Without a common universe the array accepts keys of any kind.
        let w = self.covering_universe(&u, &p)?.unwrap_or_else(|| Value::structure(StructKind::PowerStructure(crate::types::t::ANY)));
        let old: Vec<(Value, Value)> = a.map.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        let mut map = VMap::default();
        for (k, v) in old {
            map.insert(self.coerce_into_universe(&w, &k)?, v);
        }
        let m = Rc::make_mut(a);
        m.map = map;
        m.universe = Some(w.clone());
        self.coerce_into_universe(&w, i)
    }

    fn set_attr(&mut self, cur: &mut Value, name: Sym, rest: &[PathElem], v: Value) -> RResult<()> {
        match cur {
            Value::Rec(r) => {
                let fmt = r.format.clone();
                let StructKind::RecFormat(rf) = &fmt.kind else { unreachable!() };
                let Some(k) = rf.names.iter().position(|n| *n == name) else {
                    return Err(RuntimeError::statement(":=", format!("Field '{name}' is not in the record")));
                };
                let r = Rc::make_mut(r);
                if rest.is_empty() {
                    let v = match &rf.types[k] {
                        Some(t) => self.coerce_field(t, v).map_err(|e| e.in_context(format!("`{name}")))?,
                        None => v,
                    };
                    r.fields[k] = v;
                    return Ok(());
                }
                if r.fields[k].is_undef() {
                    return Err(RuntimeError::runtime(format!("Field '{name}' is not assigned")));
                }
                let mut inner = std::mem::take(&mut r.fields[k]);
                let res = self.set_path(&mut inner, rest, v);
                r.fields[k] = inner;
                res
            }
            Value::Struct(_) | Value::Obj(_) => {
                self.check_attr_valid(cur, name).map_err(|e| RuntimeError::statement(":=", e.message.clone()))?;
                let attrs = match cur {
                    Value::Struct(s) => &s.attrs,
                    Value::Obj(o) => &o.attrs,
                    _ => unreachable!(),
                };
                if rest.is_empty() {
                    attrs.borrow_mut().insert(name, v);
                    return Ok(());
                }
                let mut inner = attrs.borrow_mut().remove(&name).unwrap_or(Value::Undef);
                if inner.is_undef() {
                    return Err(RuntimeError::runtime(format!("Attribute '{name}' is not assigned")));
                }
                let res = self.set_path(&mut inner, rest, v);
                attrs.borrow_mut().insert(name, inner);
                res
            }
            Value::Err(e) => {
                let e = Rc::make_mut(e);
                match &*name.as_rc() {
                    "Object" => e.object = v,
                    "Position" => e.position = Some(Rc::from(self.to_string_default(&v)?.as_str())),
                    "Traceback" => e.traceback = Some(Rc::from(self.to_string_default(&v)?.as_str())),
                    "Type" => e.kind = Rc::from(self.to_string_default(&v)?.as_str()),
                    _ => return Err(RuntimeError::statement(":=", format!("Invalid attribute '{name}' for this object"))),
                }
                Ok(())
            }
            Value::Nfd(_) => {
                self.check_attr_valid(cur, name).map_err(|e| RuntimeError::statement(":=", e.message.clone()))?;
                let v = if rest.is_empty() {
                    v
                } else {
                    let Value::Nfd(x) = &*cur else { unreachable!() };
                    let mut inner = nearfields::attr(x, name).ok_or_else(|| RuntimeError::runtime(format!("Attribute '{name}' is not assigned")))?;
                    self.set_path(&mut inner, rest, v)?;
                    inner
                };
                nearfields::set_attr(self, cur, name, v)
            }
            Value::Seq(_) => Err(RuntimeError::statement(":=", "Sequence mutation failed")),
            other if attr_owner(other) == "structure" => Err(RuntimeError::statement(":=", invalid_attr(other, name))),
            _ => Err(RuntimeError::statement(":=", "Bad LHS for indexed assign")),
        }
    }

    fn check_attr_valid(&self, v: &Value, name: Sym) -> RResult<()> {
        if self.types.has_attribute(v.type_id(), name) {
            return Ok(());
        }
        Err(RuntimeError::runtime(invalid_attr(v, name)))
    }

    pub fn get_attr(&mut self, v: &Value, name: Sym) -> RResult<Value> {
        match v {
            Value::Rec(r) => {
                let StructKind::RecFormat(rf) = &r.format.kind else { unreachable!() };
                let Some(k) = rf.names.iter().position(|n| *n == name) else {
                    return Err(RuntimeError::runtime(format!("Field '{name}' does not exist in this record")).in_context("`"));
                };
                let x = &r.fields[k];
                if x.is_undef() {
                    return Err(RuntimeError::runtime(format!("Field '{name}' of this record is not assigned")).in_context("`"));
                }
                Ok(x.clone())
            }
            Value::Err(e) => match &*name.as_rc() {
                "Object" => Ok(e.object.clone()),
                "Type" => Ok(Value::str(&e.kind)),
                "Position" => e.position.as_deref().map(Value::str).ok_or_else(|| RuntimeError::runtime("Attribute 'Position' is not assigned")),
                "Traceback" => e.traceback.as_deref().map(Value::str).ok_or_else(|| RuntimeError::runtime("Attribute 'Traceback' is not assigned")),
                _ => Err(RuntimeError::runtime(invalid_attr(v, name)).in_context("`")),
            },
            Value::Struct(_) | Value::Obj(_) => {
                let attrs = match v {
                    Value::Struct(s) => &s.attrs,
                    Value::Obj(o) => &o.attrs,
                    _ => unreachable!(),
                };
                if let Some(x) = attrs.borrow().get(&name) {
                    return Ok(x.clone());
                }
                self.check_attr_valid(v, name).map_err(|e| e.in_context("`"))?;
                Err(RuntimeError::runtime(format!("Attribute '{name}' for this {} is valid but not assigned", attr_owner(v))).in_context("`"))
            }
            Value::Nfd(x) => {
                if let Some(a) = nearfields::attr(x, name) {
                    return Ok(a);
                }
                self.check_attr_valid(v, name).map_err(|e| e.in_context("`"))?;
                Err(RuntimeError::runtime(format!("Attribute '{name}' for this structure is valid but not assigned")).in_context("`"))
            }
            Value::Cat(ty) => match self.category_attr(*ty, name) {
                Some(x) => Ok(x),
                None => Err(RuntimeError::runtime(format!("Invalid attribute '{name}' for this category")).in_context("`")),
            },
            other => Err(RuntimeError::runtime(invalid_attr(other, name)).in_context("`")),
        }
    }

    /// Attributes of categories, such as `RngInt`CunninghamStorageLimit`.
    pub fn category_attr(&self, ty: crate::types::TypeId, name: Sym) -> Option<Value> {
        (ty == crate::types::t::RNG_INT && &*name.as_rc() == "CunninghamStorageLimit").then(|| Value::int(self.cunningham_storage_limit))
    }

    pub fn attr_assigned(&mut self, v: &Value, name: Sym) -> RResult<bool> {
        const CTX: &str = "assigned ... ` ...";
        match v {
            Value::Rec(r) => {
                let StructKind::RecFormat(rf) = &r.format.kind else { unreachable!() };
                let Some(k) = rf.names.iter().position(|n| *n == name) else {
                    return Err(RuntimeError::runtime(format!("Field '{name}' does not exist")).in_context(CTX));
                };
                Ok(!r.fields[k].is_undef())
            }
            Value::Err(e) => Ok(match &*name.as_rc() {
                "Object" | "Type" => true,
                "Position" => e.position.is_some(),
                "Traceback" => e.traceback.is_some(),
                _ => false,
            }),
            Value::Struct(s) => {
                if s.attrs.borrow().contains_key(&name) {
                    return Ok(true);
                }
                self.check_attr_valid(v, name).map_err(|e| e.in_context(CTX))?;
                Ok(false)
            }
            Value::Obj(o) => {
                if o.attrs.borrow().contains_key(&name) {
                    return Ok(true);
                }
                self.check_attr_valid(v, name).map_err(|e| e.in_context(CTX))?;
                Ok(false)
            }
            Value::Nfd(x) => {
                if nearfields::attr(x, name).is_some() {
                    return Ok(true);
                }
                self.check_attr_valid(v, name).map_err(|e| e.in_context(CTX))?;
                Ok(false)
            }
            other => Err(RuntimeError::runtime(invalid_attr(other, name)).in_context(CTX)),
        }
    }

    pub fn delete(&mut self, lv: &LV, f: &mut Frame) -> RResult<()> {
        match lv {
            LV::Var(p, span) => {
                match *p {
                    Place::Local(s, name) if f.get(s).is_undef() => {
                        return Err(RuntimeError::statement("delete", format!("Variable \"{name}\" has already been deleted")));
                    }
                    Place::Global(name) if self.lookup_variable(name).is_none() => return Err(self.unassigned_error(name).at(*span)),
                    _ => {}
                }
                // A deleted global identifier is no longer declared.
                self.put_place(*p, Value::Undef, f);
                Ok(())
            }
            LV::Discard => Ok(()),
            LV::Attr(..) | LV::AttrDyn(..) => {
                let mut path = Vec::new();
                let Some(root) = self.lv_path(lv, f, &mut path)? else { return Ok(()) };
                let Some(PathElem::Attr(name)) = path.pop() else { unreachable!() };
                let mut cur = self.take_place(root, f);
                let r = self.delete_attr_at(&mut cur, &path, name);
                self.put_place(root, cur, f);
                r
            }
            _ => Err(RuntimeError::runtime("Only identifiers and attributes can be deleted")),
        }
    }

    fn delete_attr_at(&mut self, cur: &mut Value, path: &[PathElem], name: Sym) -> RResult<()> {
        if !path.is_empty() {
            return Err(RuntimeError::runtime("Cannot delete a nested attribute"));
        }
        match cur {
            Value::Rec(r) => {
                let StructKind::RecFormat(rf) = &r.format.kind else { unreachable!() };
                let Some(k) = rf.names.iter().position(|n| *n == name) else {
                    return Err(RuntimeError::runtime(format!("Field '{name}' does not exist in this record")).in_context("`"));
                };
                Rc::make_mut(r).fields[k] = Value::Undef;
                Ok(())
            }
            Value::Struct(_) | Value::Obj(_) => {
                self.check_attr_valid(cur, name).map_err(|e| RuntimeError::statement("delete", e.message.clone()))?;
                match cur {
                    Value::Struct(s) => s.attrs.borrow_mut().remove(&name),
                    Value::Obj(o) => o.attrs.borrow_mut().remove(&name),
                    _ => unreachable!(),
                };
                Ok(())
            }
            Value::Nfd(_) => {
                self.check_attr_valid(cur, name).map_err(|e| RuntimeError::statement("delete", e.message.clone()))?;
                let Value::Nfd(x) = &*cur else { unreachable!() };
                x.attrs.borrow_mut().retain(|(n, _)| *n != name);
                Ok(())
            }
            other if attr_owner(other) == "structure" => Err(RuntimeError::statement("delete", invalid_attr(other, name))),
            _ => Err(RuntimeError::statement("delete", "LHS is not a record or structure")),
        }
    }

    // ----- mutation assignment --------------------------------------------

    pub fn op_assign(&mut self, lv: &LV, op: BinOp, rhs: Value, f: &mut Frame, at: calyx_syntax::Span) -> RResult<()> {
        match lv {
            LV::Var(p, _) => {
                let mut cur = self.take_place(*p, f);
                if cur.is_undef() {
                    let msg = format!("Argument 1 has not been initialized\nArgument types given: *nothing ~, {}", self.type_name_ext(&rhs));
                    return Err(RuntimeError::runtime(msg).in_context(&format!("{}:=", op.intrinsic_name())).at(at));
                }
                let r = self.binop_assign(op, &mut cur, rhs);
                self.put_place(*p, cur, f);
                r.map_err(|e| op_assign_error(op, e, at))
            }
            LV::Discard => Err(RuntimeError::runtime("Cannot apply a mutation assignment to '_'")),
            _ => {
                let mut path = Vec::new();
                let Some(root) = self.lv_path(lv, f, &mut path)? else { return Ok(()) };
                let base = self.read_place(root, f)?;
                let mut cur = base;
                for step in &path {
                    cur = match step {
                        PathElem::Index(i) => self.index_one(cur, i)?,
                        PathElem::Attr(n) => self.get_attr(&cur, *n).map_err(|e| e.at(lv_root_span(lv)))?,
                    };
                }
                let newv = self.binop(op, cur, rhs).map_err(|e| op_assign_error(op, e, at))?;
                let mut root_val = self.take_place(root, f);
                let r = self.set_path(&mut root_val, &path, newv);
                self.put_place(root, root_val, f);
                r
            }
        }
    }

    /// `E<x, y> := v` as Magma runs it: E is assigned first, then its generators are named (errors
    /// at `<`), then each name is bound to its generator through Name (errors at the name).
    pub fn gen_assign(&mut self, target: &LV, names: &GenNamesEx, v: Value, f: &mut Frame) -> RResult<()> {
        self.assign(target, v.clone(), f)?;
        let (strs, lt): (Vec<String>, _) = match names {
            GenNamesEx::List(ps, lt) => (ps.iter().map(|(p, _)| p.name().to_string()).collect(), *lt),
            GenNamesEx::Seq(p, _, lt) => {
                let n = self.num_generator_names(&v).map_err(|e| e.at(*lt))?;
                ((1..=n).map(|i| format!("{}[{i}]", p.name())).collect(), *lt)
            }
        };
        let v = self.assign_generator_names(v, &strs).map_err(|e| e.at(lt))?;
        self.assign(target, v.clone(), f)?;
        match names {
            GenNamesEx::List(ps, _) => {
                for (i, (p, sp)) in ps.iter().enumerate() {
                    let g = self.name_generator(&v, i + 1).map_err(|e| {
                        let e = if e.span.is_none() && e.message.starts_with("Bad argument types") { RuntimeError::runtime("Bad argument types").in_context("Name") } else { e };
                        e.at(*sp)
                    })?;
                    self.assign_place(*p, g, f)?;
                }
            }
            GenNamesEx::Seq(p, ..) => {
                let n = self.num_generators(&v)?;
                let mut gens = Vec::new();
                for i in 1..=n {
                    gens.push(self.generator(&v, i)?);
                }
                let u = Some(v.clone());
                self.assign_place(*p, Value::seq(u, gens), f)?;
            }
        }
        Ok(())
    }

    fn num_generator_names(&mut self, v: &Value) -> RResult<usize> {
        if matches!(v.as_struct(), Some(crate::value::StructKind::Ring(r)) if matches!(r.kind, crate::rings::RingKind::Residue(_))) {
            let e = RuntimeError::runtime("Bad argument types\nArgument types given: RngIntRes").in_context("NumberOfNames");
            return Err(crate::intrinsics::hidden_inner(e));
        }
        self.num_generators(v)
    }

    fn name_generator(&mut self, v: &Value, i: usize) -> RResult<Value> {
        match v.as_struct() {
            Some(crate::value::StructKind::Integers) if i == 1 => Ok(Value::int(1)),
            Some(crate::value::StructKind::Rationals) => Err(RuntimeError::runtime("Bad argument types")),
            _ => self.generator(v, i),
        }
    }

    pub fn num_generators(&mut self, v: &Value) -> RResult<usize> {
        let n = self.call_intrinsic_named(Sym::new("Ngens"), vec![v.clone()])?;
        match n {
            Value::Int(i) => Ok(i.to_u64().unwrap_or(0) as usize),
            _ => Err(RuntimeError::runtime("Ngens must return an integer")),
        }
    }

    pub fn generator(&mut self, v: &Value, i: usize) -> RResult<Value> {
        self.call_intrinsic_named(Sym::new("."), vec![v.clone(), Value::int(i as i64)])
    }

    fn assign_generator_names(&mut self, v: Value, names: &[String]) -> RResult<Value> {
        let seq = Value::seq(Some(Value::strings()), names.iter().map(|s| Value::str(s)).collect());
        let sym = Sym::new("AssignNames");
        if self.intrinsics.contains(sym) {
            let mut args = vec![v, seq];
            let mask = [true, false];
            match self.select_signature(sym, &args, &mask, true) {
                Some(_) => {
                    self.call_intrinsic(sym, &mut args, &mask, Vec::new(), 0, true, calyx_syntax::Span::default(), None)?;
                    return Ok(std::mem::take(&mut args[0]));
                }
                None => return Ok(std::mem::take(&mut args[0])),
            }
        }
        Ok(v)
    }

    // ----- reading by index -----------------------------------------------

    pub fn index_multi(&mut self, mut base: Value, ids: &[Value]) -> RResult<Value> {
        // A[i, j] is an entry of a matrix, not a row indexed again.
        if let Value::Mat(m) = &base {
            return crate::intrinsics::matrices::index(self, m, ids);
        }
        if let Value::Sparse(m) = &base {
            return crate::intrinsics::sparse::index(self, m, ids);
        }
        for i in ids {
            base = self.index_one(base, i)?;
        }
        Ok(base)
    }

    pub fn index_one(&mut self, base: Value, i: &Value) -> RResult<Value> {
        let ctx = "[]";
        match &base {
            Value::Seq(s) => {
                if let Value::Seq(ix) = i {
                    let mut out = Vec::with_capacity(ix.elems.len());
                    let undefined = || RuntimeError::runtime("Sequence element not defined").in_context(ctx);
                    for k in &ix.elems {
                        if matches!(k, Value::Int(n) if n.sign() <= 0) {
                            return Err(undefined());
                        }
                        let k = seq_index(k, "Sequence").map_err(|e| e.in_context(ctx))?;
                        match s.elems.get(k - 1) {
                            Some(v) if !v.is_undef() => out.push(v.clone()),
                            _ => return Err(undefined()),
                        }
                    }
                    return Ok(Value::seq(s.universe.clone(), out));
                }
                if let Value::Int(k) = i {
                    let in_range = k.to_i64().is_some_and(|k| k >= 1 && (k as usize) <= s.elems.len());
                    if !in_range {
                        return Err(RuntimeError::runtime(format!("Sequence index {k} should be in the range 1 to {}", s.elems.len())).in_context(ctx));
                    }
                }
                let k = seq_index(i, "Sequence").map_err(|e| e.in_context(ctx))?;
                match s.elems.get(k - 1) {
                    Some(v) if !v.is_undef() => Ok(v.clone()),
                    _ => Err(RuntimeError::runtime(format!("Sequence element {k} not defined")).in_context(ctx)),
                }
            }
            Value::List(l) => {
                if let Value::Seq(ix) = i {
                    let mut out = Vec::new();
                    for k in &ix.elems {
                        let k = seq_index(k, "List").map_err(|e| e.in_context(ctx))?;
                        out.push(l.get(k - 1).cloned().ok_or_else(|| RuntimeError::runtime(format!("List index {k} is out of range")).in_context(ctx))?);
                    }
                    return Ok(Value::list(out));
                }
                let k = seq_index(i, "List").map_err(|e| e.in_context(ctx))?;
                l.get(k - 1).cloned().ok_or_else(|| RuntimeError::runtime(format!("List index {k} is out of range")).in_context(ctx))
            }
            Value::Tuple(t) => {
                let k = seq_index(i, "Tuple").map_err(|e| e.in_context(ctx))?;
                t.elems.get(k - 1).cloned().ok_or_else(|| RuntimeError::runtime(format!("Tuple index {k} is out of range")).in_context(ctx))
            }
            Value::ISet(s) => {
                if let Value::Seq(ix) = i {
                    let mut out = VSet::default();
                    for k in &ix.elems {
                        let k = seq_index(k, "Indexed set").map_err(|e| e.in_context(ctx))?;
                        out.insert(s.elems.get_index(k - 1).cloned().ok_or_else(|| RuntimeError::runtime(format!("Index {k} is out of range")).in_context(ctx))?);
                    }
                    return Ok(Value::ISet(Rc::new(SetIndx { universe: s.universe.clone(), elems: out, name: Default::default() })));
                }
                let k = seq_index(i, "Indexed set").map_err(|e| e.in_context(ctx))?;
                s.elems.get_index(k - 1).cloned().ok_or_else(|| RuntimeError::runtime(format!("Index {k} is out of range")).in_context(ctx))
            }
            Value::Str(s) => {
                if let Value::Seq(ix) = i {
                    // The characters at the given positions, as one string.
                    let chars: Vec<char> = s.chars().collect();
                    let mut out = String::new();
                    for k in &ix.elems {
                        let k = seq_index(k, "String").map_err(|e| e.in_context(ctx))?;
                        out.push(*chars.get(k - 1).ok_or_else(|| RuntimeError::runtime(format!("String index {k} is out of range")).in_context(ctx))?);
                    }
                    return Ok(Value::str(&out));
                }
                let k = seq_index(i, "String").map_err(|e| e.in_context(ctx))?;
                s.char_at(k - 1).map(Value::str).ok_or_else(|| RuntimeError::runtime(format!("String index {k} is out of range")).in_context(ctx))
            }
            Value::BStr(s) => {
                if let Value::Seq(ix) = i {
                    let mut out = Vec::with_capacity(ix.elems.len());
                    for k in &ix.elems {
                        let k = seq_index(k, "Binary string").map_err(|e| e.in_context(ctx))?;
                        out.push(*s.get(k - 1).ok_or_else(|| RuntimeError::runtime(format!("Binary string index {k} is out of range")).in_context(ctx))?);
                    }
                    return Ok(Value::bytes(out));
                }
                let k = seq_index(i, "Binary string").map_err(|e| e.in_context(ctx))?;
                s.get(k - 1).map(|b| Value::int(*b as i64)).ok_or_else(|| RuntimeError::runtime(format!("Binary string index {k} is out of range")).in_context(ctx))
            }
            Value::Assoc(a) => {
                let key = match &a.universe {
                    Some(u) => {
                        let u = u.clone();
                        match self.try_coerce_into_universe(&u, i)? {
                            Some(k) => k,
                            None => return Err(RuntimeError::runtime("Index is not in the universe of the associative array").in_context(ctx)),
                        }
                    }
                    None => i.clone(),
                };
                match a.map.get(&key) {
                    Some(v) => Ok(v.clone()),
                    None => a.default.clone().ok_or_else(|| RuntimeError::runtime("Value for given index is not set").in_context(ctx)),
                }
            }
            Value::ECat(tv) => {
                let k = seq_index(i, "Extended type").map_err(|e| e.in_context(ctx))?;
                match tv.args().get(k - 1) {
                    Some(crate::types::TypeArg::Type(t)) => Ok(Value::ECat(Rc::new(t.clone()))),
                    Some(crate::types::TypeArg::Str(s)) => Ok(Value::str(s)),
                    None => Err(RuntimeError::runtime(format!("Extended type index {k} is out of range")).in_context(ctx)),
                }
            }
            Value::Mat(m) => crate::intrinsics::matrices::index(self, m, std::slice::from_ref(i)),
            Value::Sparse(m) => crate::intrinsics::sparse::index(self, m, std::slice::from_ref(i)),
            Value::Rec(_) => Err(RuntimeError::runtime("Records are accessed with ` not []").in_context(ctx)),
            Value::Struct(st) if matches!(st.kind, StructKind::Cartesian(_) | StructKind::Coproduct(_)) => {
                let (StructKind::Cartesian(parts) | StructKind::Coproduct(parts)) = &st.kind else { unreachable!() };
                let k = seq_index(i, "Component").map_err(|e| e.in_context(ctx))?;
                parts.get(k - 1).cloned().ok_or_else(|| RuntimeError::runtime(format!("Component {k} is out of range")).in_context(ctx))
            }
            _ => {
                if let Some(v) = self.dispatch_user_operator("[]", vec![base.clone(), i.clone()])? {
                    return Ok(v);
                }
                let t1 = self.type_name(&base);
                let t2 = self.type_name(i);
                Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {t1}, {t2}")).in_context(ctx))
            }
        }
    }
}

/// A positive index as `usize`, with a helpful error otherwise.
pub fn seq_index(i: &Value, what: &str) -> RResult<usize> {
    let n = match i {
        Value::Int(n) => n.clone(),
        Value::Rat(q) if q.is_integral() => q.numerator(),
        _ => return Err(RuntimeError::runtime(format!("{what} index must be an integer"))),
    };
    if n.sign() <= 0 {
        return Err(RuntimeError::runtime(format!("{what} index must be positive (got {n})")));
    }
    n.to_u64().filter(|&k| k < (1 << 40)).map(|k| k as usize).ok_or_else(|| RuntimeError::runtime(format!("{what} index {n} is too large")))
}

#[allow(dead_code)]
fn int_value(i: i64) -> Value {
    Value::Int(Integer::from_i64(i))
}

/// Where Magma reports an unassigned root of `x[i]`a := ...`: at the first
/// operation applied to `x`.
/// Magma's word for what has an attribute: structures, aggregates and maps
/// are structures; elements and everything else are objects.
fn attr_owner(v: &Value) -> &'static str {
    match v {
        Value::Struct(s) if !matches!(s.kind, StructKind::RecFormat(_)) => "structure",
        Value::Seq(_) | Value::Set(_) | Value::ISet(_) | Value::MSet(_) | Value::Map(_) | Value::Assoc(_) | Value::Nfd(_) => "structure",
        _ => "object",
    }
}

fn invalid_attr(v: &Value, name: Sym) -> String {
    format!("Invalid attribute '{name}' for this {}", attr_owner(v))
}

fn lv_root_span(lv: &LV) -> calyx_syntax::Span {
    match lv {
        LV::Index(b, _, s) | LV::Attr(b, _, s) | LV::AttrDyn(b, _, s) => match &**b {
            LV::Var(_, bs) => calyx_syntax::Span { file: s.file, lo: bs.hi, hi: s.hi },
            inner => lv_root_span(inner),
        },
        LV::Var(_, s) => *s,
        LV::Discard => calyx_syntax::Span::default(),
    }
}

/// An error of the operation in `x o:= y` as Magma reports it: at the
/// operator, as an error of 'o:=' with its first argument passed by
/// reference, or as a bare "Bad argument types" when the operation does
/// not apply.
fn op_assign_error(op: BinOp, mut e: RuntimeError, at: calyx_syntax::Span) -> RuntimeError {
    if e.span.is_some() || e.context.as_deref() != Some(op.intrinsic_name()) {
        return e;
    }
    if e.message.starts_with("Bad argument types") {
        return RuntimeError::runtime("Bad argument types").at(at);
    }
    e.context = Some(format!("{}:=", op.intrinsic_name()));
    if let Some(i) = e.message.find("Argument types given: ") {
        if let Some(j) = e.message[i..].find(", ") {
            e.message.insert_str(i + j, " ~");
        }
    }
    e.at(at)
}
