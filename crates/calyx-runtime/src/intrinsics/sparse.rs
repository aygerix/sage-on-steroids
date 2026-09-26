//! Sparse matrices (#77), stored as sorted nonzero entries in each row.

use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Ctx, CtxKind, Elem, Truth};
use calyx_flint::mat::Mat;
use rustc_hash::{FxHashMap, FxHasher};

use crate::error::{RResult, RuntimeError};
use crate::interp::Interp;
use crate::print::{Level, Printer};
use crate::rings::structure_key;
use crate::value::*;

/// All sparse matrices over one coefficient ring.
pub struct SparseParent {
    pub ring: Value,
    pub ctx: Rc<Ctx>,
}

/// Rows specialized for the native representation of the coefficient ring.
#[derive(Clone)]
enum Rows {
    Integers(Vec<Vec<(usize, Integer)>>),
    Words(Vec<Vec<(usize, u64)>>),
    Generic(Vec<Vec<(usize, Elem)>>),
}

/// A sparse matrix and its parent.
#[derive(Clone)]
pub struct SparseMatrix {
    pub parent: Rc<Struct>,
    pub nrows: usize,
    pub ncols: usize,
    rows: Rows,
}

impl SparseParent {
    pub fn same_as(&self, other: &SparseParent) -> bool {
        self.ring == other.ring
    }

    pub fn hash_key(&self) -> u64 {
        let mut h = FxHasher::default();
        self.ring.hash(&mut h);
        h.finish()
    }
}

impl SparseMatrix {
    pub fn info(&self) -> &SparseParent {
        parent_info(&self.parent)
    }

    pub fn ring(&self) -> &Value {
        &self.info().ring
    }

    fn zero(parent: Rc<Struct>, nrows: usize, ncols: usize) -> SparseMatrix {
        let rows = match parent_info(&parent).ctx.kind() {
            CtxKind::Integers => Rows::Integers(vec![Vec::new(); nrows]),
            CtxKind::Nmod(_) => Rows::Words(vec![Vec::new(); nrows]),
            _ => Rows::Generic(vec![Vec::new(); nrows]),
        };
        SparseMatrix { parent, nrows, ncols, rows }
    }

    pub fn nnz(&self) -> usize {
        match &self.rows {
            Rows::Integers(rows) => rows.iter().map(Vec::len).sum(),
            Rows::Words(rows) => rows.iter().map(Vec::len).sum(),
            Rows::Generic(rows) => rows.iter().map(Vec::len).sum(),
        }
    }

    pub fn same_as(&self, other: &SparseMatrix) -> bool {
        if self.nrows != other.nrows || self.ncols != other.ncols || self.ring() != other.ring() {
            return false;
        }
        match (&self.rows, &other.rows) {
            (Rows::Integers(a), Rows::Integers(b)) => a == b,
            (Rows::Words(a), Rows::Words(b)) => a == b,
            (Rows::Generic(a), Rows::Generic(b)) => a.iter().zip(b).all(|(r, s)| {
                r.len() == s.len() && r.iter().zip(s).all(|((i, x), (j, y))| i == j && x.equal(y) == Truth::True)
            }),
            _ => false,
        }
    }

    pub fn hash_u64(&self) -> u64 {
        let mut h = FxHasher::default();
        (self.nrows, self.ncols).hash(&mut h);
        self.ring().hash(&mut h);
        match &self.rows {
            Rows::Integers(rows) => for row in rows { for (j, x) in row { j.hash(&mut h); x.hash_u64().hash(&mut h); } },
            Rows::Words(rows) => for row in rows { for e in row { e.hash(&mut h); } },
            Rows::Generic(rows) => for row in rows { for (j, x) in row { j.hash(&mut h); x.to_flint_string().hash(&mut h); } },
        }
        h.finish()
    }

    fn entry(&self, it: &Interp, i: usize, j: usize) -> Value {
        match &self.rows {
            Rows::Integers(rows) => rows[i].binary_search_by_key(&j, |e| e.0).ok().map_or_else(|| Value::int(0), |k| Value::Int(rows[i][k].1.clone())),
            Rows::Words(rows) => rows[i].binary_search_by_key(&j, |e| e.0).ok().map_or_else(
                || it.elem_to_value(self.ring(), Elem::zero(&self.info().ctx)),
                |k| it.elem_to_value(self.ring(), Elem::from_word(&self.info().ctx, rows[i][k].1)),
            ),
            Rows::Generic(rows) => rows[i].binary_search_by_key(&j, |e| e.0).ok().map_or_else(
                || it.elem_to_value(self.ring(), Elem::zero(&self.info().ctx)),
                |k| it.elem_to_value(self.ring(), rows[i][k].1.clone()),
            ),
        }
    }

    fn set(&mut self, it: &mut Interp, i: usize, j: usize, x: &Value) -> RResult<bool> {
        let ring = self.ring().clone();
        let mut cell = Mat::zero(&self.info().ctx, 1, 1);
        if !crate::intrinsics::matrices::set_entry(it, &ring, &mut cell, 0, 0, x)? {
            return Ok(false);
        }
        match &mut self.rows {
            Rows::Integers(rows) => set_sorted(&mut rows[i], j, cell.integer(0, 0), |x| x.is_zero()),
            Rows::Words(rows) => set_sorted(&mut rows[i], j, cell.word(0, 0), |x| *x == 0),
            Rows::Generic(rows) => set_sorted(&mut rows[i], j, cell.entry(0, 0), |x| x.is_zero() == Truth::True),
        }
        Ok(true)
    }

    pub fn dense(&self) -> Mat {
        let mut m = Mat::zero(&self.info().ctx, self.nrows, self.ncols);
        match &self.rows {
            Rows::Integers(rows) => for (i, row) in rows.iter().enumerate() { for (j, x) in row { m.set_integer(i, *j, x).expect("an integer"); } },
            Rows::Words(rows) => for (i, row) in rows.iter().enumerate() { for (j, x) in row { m.set_word(i, *j, *x); } },
            Rows::Generic(rows) => for (i, row) in rows.iter().enumerate() { for (j, x) in row { m.set_entry(i, *j, x); } },
        }
        m
    }
}

fn sparse_value(parent: Rc<Struct>, nrows: usize, ncols: usize) -> Value {
    Value::Sparse(Rc::new(SparseMatrix::zero(parent, nrows, ncols)))
}

fn set_sorted<T>(row: &mut Vec<(usize, T)>, j: usize, x: T, zero: impl Fn(&T) -> bool) {
    match row.binary_search_by_key(&j, |e| e.0) {
        Ok(k) if zero(&x) => { row.remove(k); }
        Ok(k) => row[k].1 = x,
        Err(_) if zero(&x) => {}
        Err(k) => row.insert(k, (j, x)),
    }
}

pub fn parent_info(st: &Struct) -> &SparseParent {
    match &st.kind {
        StructKind::SparseMatrices(p) => p,
        _ => unreachable!("a sparse matrix with a non-sparse parent"),
    }
}

thread_local! {
    static PARENTS: RefCell<FxHashMap<String, Rc<Struct>>> = RefCell::default();
}

pub fn parent(it: &mut Interp, ring: &Value) -> RResult<Rc<Struct>> {
    let key = structure_key(ring);
    if let Some(k) = &key {
        if let Some(p) = PARENTS.with(|ps| ps.borrow().get(k).cloned()) {
            return Ok(p);
        }
    }
    let ctx = crate::intrinsics::matrices::entry_ctx(it, ring)?;
    let p = Struct::new(StructKind::SparseMatrices(Rc::new(SparseParent { ring: ring.clone(), ctx })));
    if let Some(k) = key {
        PARENTS.with(|ps| ps.borrow_mut().insert(k, p.clone()));
    }
    Ok(p)
}

/// `P ! A` for a sparse matrix structure P.
pub fn coerce(_: &mut Interp, st: &Rc<Struct>, x: &Value) -> RResult<Result<Value, Option<String>>> {
    match x {
        Value::Sparse(a) if a.ring() == &parent_info(st).ring => Ok(Ok(x.clone())),
        Value::Int(n) if n.is_zero() => Ok(Ok(sparse_value(st.clone(), 0, 0))),
        _ => Ok(Err(None)),
    }
}

fn bad() -> RuntimeError {
    RuntimeError::runtime("Bad argument types")
}

fn index_at(it: &Interp, a: &SparseMatrix, ids: &[Value], k: usize, n: usize) -> RResult<usize> {
    match &ids[k] {
        Value::Int(v) => match v.to_u64() {
            Some(i) if (1..=n as u64).contains(&i) => Ok(i as usize - 1),
            _ => Err(RuntimeError::runtime(format!("Index {} ({v}) should be in the range [1 .. {n}]", k + 1)).in_context("[]")),
        },
        v => Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}, {}", it.type_name_ext(&Value::Sparse(Rc::new(a.clone()))), it.type_name_ext(v))).in_context("[]")),
    }
}

pub fn index(it: &mut Interp, a: &Rc<SparseMatrix>, ids: &[Value]) -> RResult<Value> {
    match ids {
        [_] => {
            let i = index_at(it, a, ids, 0, a.nrows)?;
            let ring = a.ring().clone();
            let mut row = Mat::zero(&a.info().ctx, 1, a.ncols);
            match &a.rows {
                Rows::Integers(rows) => for (j, x) in &rows[i] { row.set_integer(0, *j, x).expect("an integer"); },
                Rows::Words(rows) => for (j, x) in &rows[i] { row.set_word(0, *j, *x); },
                Rows::Generic(rows) => for (j, x) in &rows[i] { row.set_entry(0, *j, x); },
            }
            crate::intrinsics::matrices::vec_value(it, &ring, row)
        }
        [_, _] => {
            let i = index_at(it, a, ids, 0, a.nrows)?;
            let j = index_at(it, a, ids, 1, a.ncols)?;
            Ok(a.entry(it, i, j))
        }
        _ => Err(bad().in_context("[]")),
    }
}

pub fn set_index(it: &mut Interp, cur: &mut Value, ids: &[Value], x: Value) -> RResult<()> {
    let Value::Sparse(a) = cur else { unreachable!() };
    let i = index_at(it, a, ids, 0, a.nrows).map_err(|_| RuntimeError::statement(":=", format!("Matrix row index is not in the range [1 .. {}]", a.nrows)))?;
    if ids.len() != 2 {
        return Err(RuntimeError::statement(":=", "Bad argument types"));
    }
    let j = index_at(it, a, ids, 1, a.ncols).map_err(|_| RuntimeError::statement(":=", format!("Matrix column index is not in the range [1 .. {}]", a.ncols)))?;
    if !Rc::make_mut(a).set(it, i, j, &x)? {
        return Err(RuntimeError::statement(":=", "RHS cannot be coerced into the coefficient ring"));
    }
    Ok(())
}

/// Print a sparse matrix at the default or Magma level.
pub fn fmt_matrix(it: &mut Interp, p: &mut Printer, a: &SparseMatrix, indent: usize) -> RResult<()> {
    if p.level == Level::Magma {
        p.write("SparseMatrix(");
        it.fmt(p, a.ring(), indent)?;
        p.write(&format!(", {}, {}, ", a.nrows, a.ncols));
        let mut entries = Vec::with_capacity(a.nnz());
        let mut push = |i: usize, j: usize, x: Value| {
            entries.push(Value::tuple(vec![Value::int(i as i64 + 1), Value::int(j as i64 + 1), x]));
        };
        match &a.rows {
            Rows::Integers(rows) => for (i, row) in rows.iter().enumerate() { for (j, x) in row { push(i, *j, Value::Int(x.clone())); } },
            Rows::Words(rows) => for (i, row) in rows.iter().enumerate() {
                for (j, x) in row { push(i, *j, it.elem_to_value(a.ring(), Elem::from_word(&a.info().ctx, *x))); }
            },
            Rows::Generic(rows) => for (i, row) in rows.iter().enumerate() {
                for (j, x) in row { push(i, *j, it.elem_to_value(a.ring(), x.clone())); }
            },
        }
        it.fmt(p, &Value::seq(None, entries), indent)?;
        p.write(")");
        return Ok(());
    }
    p.write(&format!("Sparse matrix with {} row{} and {} column{} over ", a.nrows, if a.nrows == 1 { "" } else { "s" }, a.ncols, if a.ncols == 1 { "" } else { "s" }));
    let saved = p.level;
    p.level = Level::Minimal;
    let r = it.fmt(p, a.ring(), indent);
    p.level = saved;
    r
}

/// Print the structure of sparse matrices over a ring.
pub fn fmt_parent(it: &mut Interp, p: &mut Printer, st: &Struct, indent: usize) -> RResult<()> {
    let ring = parent_info(st).ring.clone();
    if p.level == Level::Magma {
        p.write("SparseMatrixStructure(");
        it.fmt(p, &ring, indent)?;
        p.write(")");
        return Ok(());
    }
    p.write("Sparse Matrix Structure over ");
    let saved = p.level;
    p.level = Level::Minimal;
    let r = it.fmt(p, &ring, indent);
    p.level = saved;
    r
}

pub fn register(_: &mut Interp) {}
