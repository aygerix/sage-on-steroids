//! Sparse matrices (#77), stored as sorted nonzero entries in each row.

mod linalg;

use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Ctx, CtxKind, Elem, Truth};
use calyx_flint::mat::Mat;
use calyx_syntax::ast::BinOp;
use rustc_hash::{FxHashMap, FxHasher};

use crate::error::{RResult, RuntimeError};
use crate::intrinsics::{arg_ge, intv, none, one};
use crate::interp::{CallArgs, Interp};
use crate::print::{Level, Printer};
use crate::rings::{RingKind, ring_of, structure_key};
use crate::types::t;
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

    fn row_len(&self, i: usize) -> usize {
        match &self.rows {
            Rows::Integers(rows) => rows[i].len(),
            Rows::Words(rows) => rows[i].len(),
            Rows::Generic(rows) => rows[i].len(),
        }
    }

    fn columns(&self, i: usize) -> Vec<usize> {
        match &self.rows {
            Rows::Integers(rows) => rows[i].iter().map(|e| e.0).collect(),
            Rows::Words(rows) => rows[i].iter().map(|e| e.0).collect(),
            Rows::Generic(rows) => rows[i].iter().map(|e| e.0).collect(),
        }
    }

    fn entries(&self, it: &Interp) -> Vec<(usize, usize, Value)> {
        let mut out = Vec::with_capacity(self.nnz());
        match &self.rows {
            Rows::Integers(rows) => for (i, row) in rows.iter().enumerate() { for (j, x) in row { out.push((i, *j, Value::Int(x.clone()))); } },
            Rows::Words(rows) => for (i, row) in rows.iter().enumerate() {
                for (j, x) in row { out.push((i, *j, it.elem_to_value(self.ring(), Elem::from_word(&self.info().ctx, *x)))); }
            },
            Rows::Generic(rows) => for (i, row) in rows.iter().enumerate() {
                for (j, x) in row { out.push((i, *j, it.elem_to_value(self.ring(), x.clone()))); }
            },
        }
        out
    }

    fn row_entries(&self, it: &Interp, i: usize) -> Vec<(usize, Value)> {
        match &self.rows {
            Rows::Integers(rows) => rows[i].iter().map(|(j, x)| (*j, Value::Int(x.clone()))).collect(),
            Rows::Words(rows) => rows[i].iter().map(|(j, x)| (*j, it.elem_to_value(self.ring(), Elem::from_word(&self.info().ctx, *x)))).collect(),
            Rows::Generic(rows) => rows[i].iter().map(|(j, x)| (*j, it.elem_to_value(self.ring(), x.clone()))).collect(),
        }
    }

    fn row_elems(&self, i: usize) -> RResult<Vec<(usize, Elem)>> {
        match &self.rows {
            Rows::Integers(rows) => rows[i].iter().map(|(j, x)| Ok((*j, Elem::from_integer(&self.info().ctx, x)?))).collect(),
            Rows::Words(rows) => Ok(rows[i].iter().map(|(j, x)| (*j, Elem::from_word(&self.info().ctx, *x))).collect()),
            Rows::Generic(rows) => Ok(rows[i].iter().map(|(j, x)| (*j, x.clone())).collect()),
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

    fn resize(&mut self, nrows: usize, ncols: usize) {
        if nrows > self.nrows {
            match &mut self.rows {
                Rows::Integers(rows) => rows.resize_with(nrows, Vec::new),
                Rows::Words(rows) => rows.resize_with(nrows, Vec::new),
                Rows::Generic(rows) => rows.resize_with(nrows, Vec::new),
            }
            self.nrows = nrows;
        }
        self.ncols = self.ncols.max(ncols);
    }

    fn swap_rows(&mut self, i: usize, j: usize) {
        match &mut self.rows {
            Rows::Integers(rows) => rows.swap(i, j),
            Rows::Words(rows) => rows.swap(i, j),
            Rows::Generic(rows) => rows.swap(i, j),
        }
    }

    fn reverse_rows(&mut self) {
        match &mut self.rows {
            Rows::Integers(rows) => rows.reverse(),
            Rows::Words(rows) => rows.reverse(),
            Rows::Generic(rows) => rows.reverse(),
        }
    }

    fn map_columns(&mut self, mut f: impl FnMut(usize) -> Option<usize>) {
        match &mut self.rows {
            Rows::Integers(rows) => for row in rows { map_row(row, &mut f); },
            Rows::Words(rows) => for row in rows { map_row(row, &mut f); },
            Rows::Generic(rows) => for row in rows { map_row(row, &mut f); },
        }
    }

    fn retain_rows(&mut self, keep: &[usize]) {
        match &mut self.rows {
            Rows::Integers(rows) => *rows = keep.iter().map(|&i| rows[i].clone()).collect(),
            Rows::Words(rows) => *rows = keep.iter().map(|&i| rows[i].clone()).collect(),
            Rows::Generic(rows) => *rows = keep.iter().map(|&i| rows[i].clone()).collect(),
        }
        self.nrows = keep.len();
    }

    fn clear_block(&mut self, i: usize, j: usize, nrows: usize, ncols: usize) {
        let end = j + ncols;
        match &mut self.rows {
            Rows::Integers(rows) => for row in &mut rows[i..i + nrows] { row.retain(|e| e.0 < j || e.0 >= end); },
            Rows::Words(rows) => for row in &mut rows[i..i + nrows] { row.retain(|e| e.0 < j || e.0 >= end); },
            Rows::Generic(rows) => for row in &mut rows[i..i + nrows] { row.retain(|e| e.0 < j || e.0 >= end); },
        }
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

fn map_row<T>(row: &mut Vec<(usize, T)>, f: &mut impl FnMut(usize) -> Option<usize>) {
    row.retain_mut(|e| match f(e.0) {
        Some(j) => { e.0 = j; true }
        None => false,
    });
    row.sort_unstable_by_key(|e| e.0);
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
pub fn coerce(_it: &mut Interp, st: &Rc<Struct>, x: &Value) -> RResult<Result<Value, Option<String>>> {
    match x {
        Value::Sparse(a) if a.ring() == &parent_info(st).ring => Ok(Ok(x.clone())),
        Value::Int(n) if n.is_zero() => Ok(Ok(sparse_value(st.clone(), 0, 0))),
        _ => Ok(Err(None)),
    }
}

fn bad() -> RuntimeError {
    RuntimeError::runtime("Bad argument types")
}

fn dim(a: &CallArgs, i: usize, num: usize) -> RResult<usize> {
    let n = a.int(i)?;
    match n.to_u64() {
        Some(v) if v < 1 << 32 => Ok(v as usize),
        _ if n.sign() < 0 => Err(arg_ge(num, n, 0)),
        _ => Err(RuntimeError::runtime(format!("Argument {num} ({n}) is too large"))),
    }
}

fn ring_arg(a: &CallArgs, i: usize) -> RResult<Value> {
    match &a.args[i] {
        v @ Value::Struct(_) if matches!(v.type_id(), t::RNG_INT | t::FLD_RAT | t::FLD_RE | t::FLD_COM) => Ok(v.clone()),
        v @ Value::Struct(_) => Ok(v.clone()),
        _ => Err(bad()),
    }
}

fn seq_ring(it: &mut Interp, q: &SeqEnum) -> RResult<Value> {
    match q.elems.first() {
        Some(Value::Tuple(t)) if t.elems.len() == 3 => it.parent_of(&t.elems[2]),
        Some(x) => it.parent_of(x),
        None => match &q.universe {
            Some(u) if it.types.isa(u.type_id(), t::RNG) => Ok(u.clone()),
            _ => Err(RuntimeError::runtime("Illegal null sequence")),
        },
    }
}

fn new_value(it: &mut Interp, ring: &Value, nrows: usize, ncols: usize) -> RResult<Value> {
    Ok(sparse_value(parent(it, ring)?, nrows, ncols))
}

fn from_sequence(it: &mut Interp, ring: &Value, nrows: usize, ncols: usize, q: &SeqEnum) -> RResult<Value> {
    let Value::Sparse(mut out) = new_value(it, ring, nrows, ncols)? else { unreachable!() };
    match q.elems.first() {
        Some(Value::Tuple(_)) => {
            for (k, v) in q.elems.iter().enumerate() {
                let Value::Tuple(t) = v else { return Err(bad()) };
                let [Value::Int(i), Value::Int(j), x] = &t.elems[..] else { return Err(bad()) };
                let at = |v: &Integer, hi: usize, component: usize| match v.to_u64() {
                    Some(x) if (1..=hi as u64).contains(&x) => Ok(x as usize - 1),
                    _ => Err(RuntimeError::runtime(format!("Component {component} of sequence entry {} ({v}) is not in range [1 .. {hi}]", k + 1))),
                };
                let (i, j) = (at(i, nrows, 1)?, at(j, ncols, 2)?);
                if !Rc::make_mut(&mut out).set(it, i, j, x)? {
                    return Err(RuntimeError::runtime(format!("Cannot coerce sequence element {} into the coefficient ring", k + 1)));
                }
            }
        }
        _ => {
            let mut k = 0;
            for i in 0..nrows {
                let Some(Value::Int(weight)) = q.elems.get(k) else { return Err(RuntimeError::runtime("Invalid sparse row encoding")) };
                let Some(weight) = weight.to_u64().map(|x| x as usize) else { return Err(RuntimeError::runtime("Invalid sparse row encoding")) };
                k += 1;
                for _ in 0..weight {
                    let (Some(Value::Int(j)), Some(x)) = (q.elems.get(k), q.elems.get(k + 1)) else {
                        return Err(RuntimeError::runtime("Invalid sparse row encoding"));
                    };
                    let Some(j) = j.to_u64().filter(|j| (1..=ncols as u64).contains(j)).map(|j| j as usize - 1) else {
                        return Err(RuntimeError::runtime("Column index out of range in sparse row encoding"));
                    };
                    if !Rc::make_mut(&mut out).set(it, i, j, x)? {
                        return Err(RuntimeError::runtime(format!("Cannot coerce sequence element {} into the coefficient ring", k + 2)));
                    }
                    k += 2;
                }
            }
            if k != q.elems.len() {
                return Err(RuntimeError::runtime("Invalid sparse row encoding"));
            }
        }
    }
    Ok(Value::Sparse(out))
}

fn sparse_rmnq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let (m, n) = (dim(a, 1, 2)?, dim(a, 2, 3)?);
    let q = a.seq(3)?.clone();
    one(from_sequence(it, &ring, m, n, &q)?)
}

fn sparse_mnq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (m, n) = (dim(a, 0, 1)?, dim(a, 1, 2)?);
    let q = a.seq(2)?.clone();
    let ring = seq_ring(it, &q)?;
    one(from_sequence(it, &ring, m, n, &q)?)
}

fn sparse_rmn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let (m, n) = (dim(a, 1, 2)?, dim(a, 2, 3)?);
    one(new_value(it, &ring, m, n)?)
}

fn sparse_mn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (m, n) = (dim(a, 0, 1)?, dim(a, 1, 2)?);
    one(new_value(it, &Value::integers(), m, n)?)
}

fn sparse_r(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(new_value(it, &ring_arg(a, 0)?, 0, 0)?)
}

fn sparse_empty(it: &mut Interp, _: &mut CallArgs) -> RResult<Vals> {
    one(new_value(it, &Value::integers(), 0, 0)?)
}

fn diagonal(it: &mut Interp, ring: &Value, n: usize, xs: &[Value]) -> RResult<Value> {
    let Value::Sparse(mut a) = new_value(it, ring, n, n)? else { unreachable!() };
    for (i, x) in xs.iter().enumerate() {
        if !Rc::make_mut(&mut a).set(it, i, i, x)? {
            return Err(RuntimeError::runtime(format!("Cannot coerce sequence element {} into the coefficient ring", i + 1)));
        }
    }
    Ok(Value::Sparse(a))
}

fn identity_sparse(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let n = dim(a, 1, 2)?;
    one(diagonal(it, &ring, n, &vec![Value::int(1); n])?)
}

fn scalar_sparse(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = a.args.len() - 2;
    let x = a.args[k + 1].clone();
    let ring = if k == 1 { ring_arg(a, 0)? } else { it.parent_of(&x)? };
    let n = dim(a, k, k + 1)?;
    one(diagonal(it, &ring, n, &vec![x; n])?)
}

fn diagonal_sparse(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = a.args.len() - 1;
    let q = a.seq(k)?.clone();
    let ring = if k == 0 { seq_ring(it, &q)? } else { ring_arg(a, 0)? };
    let n = if k == 2 { dim(a, 1, 2)? } else { q.elems.len() };
    if q.elems.len() != n {
        return Err(RuntimeError::runtime(format!("Length of argument {} is not {n}", k + 1)));
    }
    one(diagonal(it, &ring, n, &q.elems)?)
}

fn sparse_monomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Perm(g) = &a.args[0] else { return Err(bad()) };
    if g.degree() % 2 != 0 {
        return Err(RuntimeError::runtime("Permutation degree must be even"));
    }
    let d = g.degree() / 2;
    let Value::Sparse(mut out) = new_value(it, &Value::integers(), d, d)? else { unreachable!() };
    for i in 0..d {
        let image = g.images[i] as usize;
        let x = Value::int(if image < d { 1 } else { -1 });
        Rc::make_mut(&mut out).set(it, i, image % d, &x)?;
    }
    one(Value::Sparse(out))
}

fn sparse_structure(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Struct(parent(it, &ring_arg(a, 0)?)?))
}

fn sparse_arg(a: &CallArgs, i: usize) -> RResult<Rc<SparseMatrix>> {
    match &a.args[i] {
        Value::Sparse(m) => Ok(m.clone()),
        _ => Err(bad()),
    }
}

fn dense_value(it: &mut Interp, a: &SparseMatrix) -> RResult<Value> {
    crate::intrinsics::matrices::mat_value(it, a.ring(), a.dense())
}

fn row_number(a: &CallArgs, k: usize, n: usize) -> RResult<usize> {
    let x = a.int(k)?;
    match x.to_u64() {
        Some(i) if (1..=n as u64).contains(&i) => Ok(i as usize - 1),
        _ => Err(RuntimeError::runtime(format!("Argument {} ({x}) should be in the range [1 .. {n}]", k + 1))),
    }
}

fn base_ring(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(sparse_arg(a, 0)?.ring().clone())
}

fn nrows(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(sparse_arg(a, 0)?.nrows as u64))
}

fn ncols(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(sparse_arg(a, 0)?.ncols as u64))
}

fn eltseq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    let entries = m.entries(it).into_iter().map(|(i, j, x)| Value::tuple(vec![Value::int(i as i64 + 1), Value::int(j as i64 + 1), x])).collect();
    one(Value::seq(None, entries))
}

fn nnz(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(sparse_arg(a, 0)?.nnz() as u64))
}

fn density(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    let size = m.nrows * m.ncols;
    let q = if size == 0 {
        calyx_flint::Rational::zero()
    } else {
        calyx_flint::Rational::new(&Integer::from_u64(m.nnz() as u64), &Integer::from_u64(size as u64)).expect("a nonzero denominator")
    };
    one(it.coerce(&Value::reals(crate::intrinsics::reals::default_bits()), &Value::rat(q))?)
}

fn support_row(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    let i = row_number(a, 1, m.nrows)?;
    one(Value::int_seq(m.columns(i).into_iter().map(|j| Integer::from_u64(j as u64 + 1))))
}

fn support(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    let pairs = (0..m.nrows).flat_map(|i| m.columns(i).into_iter().map(move |j| Value::tuple(vec![Value::int(i as i64 + 1), Value::int(j as i64 + 1)]))).collect();
    one(Value::seq(None, pairs))
}

fn row_weight(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    let i = row_number(a, 1, m.nrows)?;
    intv(Integer::from_u64(m.row_len(i) as u64))
}

fn row_weights(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    one(Value::int_seq((0..m.nrows).map(|i| Integer::from_u64(m.row_len(i) as u64))))
}

fn column_weights_of(m: &SparseMatrix) -> Vec<usize> {
    let mut weights = vec![0; m.ncols];
    for i in 0..m.nrows {
        for j in m.columns(i) {
            weights[j] += 1;
        }
    }
    weights
}

fn column_weight(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    let j = row_number(a, 1, m.ncols)?;
    intv(Integer::from_u64(column_weights_of(&m)[j] as u64))
}

fn column_weights(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    one(Value::int_seq(column_weights_of(&m).into_iter().map(|n| Integer::from_u64(n as u64))))
}

#[derive(Clone, Copy)]
enum Join {
    Horizontal,
    Vertical,
    Diagonal,
}

fn join(it: &mut Interp, a: &mut CallArgs, how: Join) -> RResult<Vals> {
    let (x, y) = (sparse_arg(a, 0)?, sparse_arg(a, 1)?);
    if x.ring() != y.ring() {
        return Err(RuntimeError::runtime("Arguments have incompatible coefficient rings"));
    }
    if matches!(how, Join::Horizontal) && x.nrows != y.nrows {
        return Err(RuntimeError::runtime("Matrices have incompatible numbers of rows"));
    }
    if matches!(how, Join::Vertical) && x.ncols != y.ncols {
        return Err(RuntimeError::runtime("Matrices have incompatible numbers of columns"));
    }
    let (nrows, ncols, yi, yj) = match how {
        Join::Horizontal => (x.nrows, x.ncols + y.ncols, 0, x.ncols),
        Join::Vertical => (x.nrows + y.nrows, x.ncols, x.nrows, 0),
        Join::Diagonal => (x.nrows + y.nrows, x.ncols + y.ncols, x.nrows, x.ncols),
    };
    let Value::Sparse(mut out) = new_value(it, x.ring(), nrows, ncols)? else { unreachable!() };
    for (i, j, e) in x.entries(it) {
        Rc::make_mut(&mut out).set(it, i, j, &e)?;
    }
    for (i, j, e) in y.entries(it) {
        Rc::make_mut(&mut out).set(it, yi + i, yj + j, &e)?;
    }
    one(Value::Sparse(out))
}

fn horizontal_join(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    join(it, a, Join::Horizontal)
}

fn vertical_join(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    join(it, a, Join::Vertical)
}

fn diagonal_join(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    join(it, a, Join::Diagonal)
}

fn dense_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = sparse_arg(a, 0)?;
    one(crate::intrinsics::matrices::mat_value(it, x.ring(), x.dense())?)
}

fn sparse_from_mat(it: &mut Interp, ring: &Value, m: &Mat) -> RResult<Value> {
    let Value::Sparse(mut out) = new_value(it, ring, m.nrows(), m.ncols())? else { unreachable!() };
    for i in 0..m.nrows() {
        for j in 0..m.ncols() {
            if m.entry_is_zero(i, j) {
                continue;
            }
            let e = crate::intrinsics::matrices::entry_of(it, ring, m, i, j);
            Rc::make_mut(&mut out).set(it, i, j, &e)?;
        }
    }
    Ok(Value::Sparse(out))
}

fn from_dense(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Mat(x) = &a.args[0] else { return Err(bad()) };
    one(sparse_from_mat(it, x.ring(), &x.m)?)
}

fn changed_ring(it: &mut Interp, x: &SparseMatrix, ring: &Value) -> RResult<Value> {
    let Value::Sparse(mut out) = new_value(it, ring, x.nrows, x.ncols)? else { unreachable!() };
    for (i, j, e) in x.entries(it) {
        if !Rc::make_mut(&mut out).set(it, i, j, &e)? {
            return Err(RuntimeError::runtime("Cannot coerce element from source coefficent ring into the destination coefficient ring"));
        }
    }
    Ok(Value::Sparse(out))
}

fn change_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = sparse_arg(a, 0)?;
    let ring = ring_arg(a, 1)?;
    one(changed_ring(it, &x, &ring)?)
}

fn sparse_over(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ring = ring_arg(a, 0)?;
    let x = sparse_arg(a, 1)?;
    one(changed_ring(it, &x, &ring)?)
}

fn square_matrix(a: &CallArgs) -> RResult<Rc<SparseMatrix>> {
    let m = sparse_arg(a, 0)?;
    if m.nrows != m.ncols {
        return Err(RuntimeError::runtime("Argument 1 is not square"));
    }
    Ok(m)
}

fn same_entry(it: &mut Interp, a: Value, b: Value) -> RResult<bool> {
    Ok(matches!(it.compare_eq(&a, &b, true)?, Some(true)))
}

pub fn equal(it: &mut Interp, a: &Value, b: &Value) -> RResult<bool> {
    let (Value::Sparse(x), Value::Sparse(y)) = (a, b) else {
        return Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}, {}", it.type_name_ext(a), it.type_name_ext(b))));
    };
    if x.nrows != y.nrows || x.ncols != y.ncols {
        return Ok(false);
    }
    if x.ring() == y.ring() {
        return Ok(x.same_as(y));
    }
    Err(RuntimeError::runtime("Arguments have incompatible coefficient rings"))
}

fn is_zero(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Bool(sparse_arg(a, 0)?.nnz() == 0))
}

fn identity_test(it: &mut Interp, a: &mut CallArgs, sign: i64) -> RResult<Vals> {
    let m = square_matrix(a)?;
    if m.nnz() != m.nrows {
        return one(Value::Bool(false));
    }
    for i in 0..m.nrows {
        if m.columns(i) != [i] || !same_entry(it, m.entry(it, i, i), Value::int(sign))? {
            return one(Value::Bool(false));
        }
    }
    one(Value::Bool(true))
}

fn is_one(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    identity_test(it, a, 1)
}

fn is_minus_one(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    identity_test(it, a, -1)
}

fn is_diagonal(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = square_matrix(a)?;
    one(Value::Bool((0..m.nrows).all(|i| m.columns(i).into_iter().all(|j| i == j))))
}

fn is_scalar(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = square_matrix(a)?;
    if (0..m.nrows).any(|i| m.columns(i).into_iter().any(|j| i != j)) {
        return one(Value::Bool(false));
    }
    if m.nrows == 0 {
        return one(Value::Bool(false));
    }
    if m.nrows == 1 {
        return one(Value::Bool(true));
    }
    let x = m.entry(it, 0, 0);
    for i in 1..m.nrows {
        if !same_entry(it, x.clone(), m.entry(it, i, i))? {
            return one(Value::Bool(false));
        }
    }
    one(Value::Bool(true))
}

fn is_symmetric(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = square_matrix(a)?;
    for (i, j, x) in m.entries(it) {
        if !same_entry(it, x, m.entry(it, j, i))? {
            return one(Value::Bool(false));
        }
    }
    one(Value::Bool(true))
}

fn is_upper(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    one(Value::Bool((0..m.nrows).all(|i| m.columns(i).into_iter().all(|j| i <= j))))
}

fn is_lower(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    one(Value::Bool((0..m.nrows).all(|i| m.columns(i).into_iter().all(|j| i >= j))))
}

fn compatible(a: &SparseMatrix, b: &SparseMatrix, product: bool) -> RResult<()> {
    let dimensions = if product { a.ncols == b.nrows } else { a.nrows == b.nrows && a.ncols == b.ncols };
    if !dimensions {
        return Err(RuntimeError::runtime("Arguments have incompatible degrees"));
    }
    if a.ring() != b.ring() {
        return Err(RuntimeError::runtime("Arguments have incompatible coefficient rings"));
    }
    Ok(())
}

fn add_matrices(it: &mut Interp, a: &SparseMatrix, b: &SparseMatrix, subtract: bool) -> RResult<Value> {
    compatible(a, b, false)?;
    let mut out = Rc::new(a.clone());
    for (i, j, mut x) in b.entries(it) {
        if subtract {
            x = it.negate(x)?;
        }
        let y = out.entry(it, i, j);
        let sum = add_values(it, y, x)?;
        Rc::make_mut(&mut out).set(it, i, j, &sum)?;
    }
    Ok(Value::Sparse(out))
}

fn multiply_matrices(it: &mut Interp, a: &SparseMatrix, b: &SparseMatrix) -> RResult<Value> {
    compatible(a, b, true)?;
    let Value::Sparse(mut out) = new_value(it, a.ring(), a.nrows, b.ncols)? else { unreachable!() };
    for i in 0..a.nrows {
        let mut sums: FxHashMap<usize, Value> = FxHashMap::default();
        for (k, x) in a.row_entries(it, i) {
            for (j, y) in b.row_entries(it, k) {
                let xy = mul_values(it, x.clone(), y)?;
                let sum = match sums.remove(&j) {
                    Some(z) => add_values(it, z, xy)?,
                    None => xy,
                };
                sums.insert(j, sum);
            }
        }
        let mut sums: Vec<(usize, Value)> = sums.into_iter().collect();
        sums.sort_unstable_by_key(|e| e.0);
        for (j, x) in sums {
            Rc::make_mut(&mut out).set(it, i, j, &x)?;
        }
    }
    Ok(Value::Sparse(out))
}

fn scale_matrix(it: &mut Interp, a: &SparseMatrix, scalar: &Value) -> RResult<Value> {
    let scalar = scalar_value(it, a, scalar)?;
    let Value::Sparse(mut out) = new_value(it, a.ring(), a.nrows, a.ncols)? else { unreachable!() };
    for (i, j, x) in a.entries(it) {
        let y = mul_values(it, scalar.clone(), x)?;
        Rc::make_mut(&mut out).set(it, i, j, &y)?;
    }
    Ok(Value::Sparse(out))
}

pub fn negate(it: &mut Interp, a: &SparseMatrix) -> RResult<Value> {
    scale_matrix(it, a, &Value::int(-1))
}

fn transposed(it: &mut Interp, a: &SparseMatrix) -> RResult<Value> {
    let Value::Sparse(mut out) = new_value(it, a.ring(), a.ncols, a.nrows)? else { unreachable!() };
    for (i, j, x) in a.entries(it) {
        Rc::make_mut(&mut out).set(it, j, i, &x)?;
    }
    Ok(Value::Sparse(out))
}

fn identity_like(it: &mut Interp, a: &SparseMatrix) -> RResult<Value> {
    diagonal(it, a.ring(), a.nrows, &vec![Value::int(1); a.nrows])
}

fn power(it: &mut Interp, a: &SparseMatrix, n: &Integer) -> RResult<Value> {
    if a.nrows != a.ncols {
        return Err(RuntimeError::runtime("Argument 1 is not square"));
    }
    if n.sign() < 0 {
        let inv = a.dense().inv().map_err(|_| RuntimeError::runtime("Argument 1 is not invertible"))?;
        let Value::Sparse(inv) = sparse_from_mat(it, a.ring(), &inv)? else { unreachable!() };
        return power(it, &inv, &-n);
    }
    let Some(mut e) = n.to_u64() else { return Err(RuntimeError::runtime(format!("Argument 2 ({n}) is too large"))) };
    let Value::Sparse(mut result) = identity_like(it, a)? else { unreachable!() };
    let mut base = Rc::new(a.clone());
    while e != 0 {
        if e & 1 == 1 {
            let Value::Sparse(x) = multiply_matrices(it, &result, &base)? else { unreachable!() };
            result = x;
        }
        e >>= 1;
        if e != 0 {
            let Value::Sparse(x) = multiply_matrices(it, &base, &base)? else { unreachable!() };
            base = x;
        }
    }
    Ok(Value::Sparse(result))
}

pub fn binop(it: &mut Interp, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
    use BinOp::*;
    match (op, a, b) {
        (Eq | Ne, Value::Sparse(_), Value::Sparse(_)) => {
            let e = equal(it, a, b)?;
            Ok(Some(Value::Bool(e == (op == Eq))))
        }
        (Add | Sub, Value::Sparse(x), Value::Sparse(y)) => Ok(Some(add_matrices(it, x, y, op == Sub)?)),
        (Mul, Value::Sparse(x), Value::Sparse(y)) => Ok(Some(multiply_matrices(it, x, y)?)),
        (Mul, Value::Mat(x), Value::Sparse(y)) => Ok(Some(dense_product(it, x, y, false)?)),
        (Mul, Value::Sparse(x), y) if !matches!(y, Value::Sparse(_) | Value::Mat(_)) => Ok(Some(scale_matrix(it, x, y)?)),
        (Mul, x, Value::Sparse(y)) if !matches!(x, Value::Sparse(_) | Value::Mat(_)) => Ok(Some(scale_matrix(it, y, x)?)),
        (Pow, Value::Sparse(x), Value::Int(n)) => Ok(Some(power(it, x, n)?)),
        _ => Ok(None),
    }
}

fn transpose(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    one(transposed(it, &m)?)
}

fn dense_product(it: &mut Interp, x: &crate::intrinsics::matrices::Mtrx, y: &SparseMatrix, transpose: bool) -> RResult<Value> {
    if x.ring() != y.ring() {
        return Err(RuntimeError::runtime("Arguments have incompatible coefficient rings"));
    }
    let expected = if transpose { y.ncols } else { y.nrows };
    if x.m.ncols() != expected {
        return Err(RuntimeError::runtime("Arguments have incompatible degrees"));
    }
    let cols = if transpose { y.nrows } else { y.ncols };
    let mut out = Mat::zero(x.m.ctx(), x.m.nrows(), cols);
    let gr = |e| crate::rings::gr_error(e, "Multiplication failed");
    if transpose {
        for r in 0..x.m.nrows() {
            for i in 0..y.nrows {
                let mut sum = Elem::zero(x.m.ctx());
                for (k, a) in y.row_elems(i)? {
                    if !x.m.entry_is_zero(r, k) {
                        sum = sum.add(&x.m.entry(r, k).mul(&a).map_err(gr)?).map_err(gr)?;
                    }
                }
                out.set_entry(r, i, &sum);
            }
        }
    } else {
        for r in 0..x.m.nrows() {
            for k in 0..y.nrows {
                if x.m.entry_is_zero(r, k) {
                    continue;
                }
                let a = x.m.entry(r, k);
                for (j, b) in y.row_elems(k)? {
                    let sum = out.entry(r, j).add(&a.mul(&b).map_err(gr)?).map_err(gr)?;
                    out.set_entry(r, j, &sum);
                }
            }
        }
    }
    if x.is_vector() {
        crate::intrinsics::matrices::vec_value(it, x.ring(), out)
    } else {
        crate::intrinsics::matrices::mat_value(it, x.ring(), out)
    }
}

fn multiply_by_transpose(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Mat(x) = &a.args[0] else { return Err(bad()) };
    let y = sparse_arg(a, 1)?;
    one(dense_product(it, x, &y, true)?)
}

fn set_entry_proc(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (i, j) = (a.int(1)?.to_u64(), a.int(2)?.to_u64());
    let (Some(i), Some(j)) = (i.filter(|&x| x >= 1), j.filter(|&x| x >= 1)) else {
        return Err(RuntimeError::runtime("Row and column numbers must be positive"));
    };
    let x = a.args[3].clone();
    let Value::Sparse(m) = &mut a.args[0] else { unreachable!() };
    let m = Rc::make_mut(m);
    m.resize(i as usize, j as usize);
    if !m.set(it, i as usize - 1, j as usize - 1, &x)? {
        return Err(RuntimeError::runtime("Entry cannot be coerced into the coefficient ring"));
    }
    none()
}

fn submatrix_of(it: &mut Interp, a: &SparseMatrix, rows: &[usize], cols: &[usize]) -> RResult<Value> {
    let Value::Sparse(mut out) = new_value(it, a.ring(), rows.len(), cols.len())? else { unreachable!() };
    for (i, &r) in rows.iter().enumerate() {
        for (j, &c) in cols.iter().enumerate() {
            let x = a.entry(it, r, c);
            Rc::make_mut(&mut out).set(it, i, j, &x)?;
        }
    }
    Ok(Value::Sparse(out))
}

fn int_in(a: &CallArgs, k: usize, lo: i64, hi: i64) -> RResult<usize> {
    let x = a.int(k)?;
    match x.to_i64() {
        Some(v) if (lo..=hi).contains(&v) => Ok(v as usize),
        _ => Err(RuntimeError::runtime(format!("Argument {} ({x}) should be in the range [{lo} .. {hi}]", k + 1))),
    }
}

fn submatrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    let i = int_in(a, 1, 1, m.nrows as i64 + 1)?;
    let j = int_in(a, 2, 1, m.ncols as i64 + 1)?;
    let r = int_in(a, 3, 0, m.nrows as i64 + 1 - i as i64)?;
    let c = int_in(a, 4, 0, m.ncols as i64 + 1 - j as i64)?;
    one(submatrix_of(it, &m, &(i - 1..i - 1 + r).collect::<Vec<_>>(), &(j - 1..j - 1 + c).collect::<Vec<_>>())?)
}

fn submatrix_range(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    let i = int_in(a, 1, 1, m.nrows as i64 + 1)?;
    let j = int_in(a, 2, 1, m.ncols as i64 + 1)?;
    let r = int_in(a, 3, i as i64 - 1, m.nrows as i64)?;
    let c = int_in(a, 4, j as i64 - 1, m.ncols as i64)?;
    one(submatrix_of(it, &m, &(i - 1..r).collect::<Vec<_>>(), &(j - 1..c).collect::<Vec<_>>())?)
}

fn indices(a: &CallArgs, k: usize, n: usize, what: &str) -> RResult<Vec<usize>> {
    a.seq(k)?.elems.iter().map(|x| match x {
        Value::Int(i) => i.to_u64().filter(|&i| (1..=n as u64).contains(&i)).map(|i| i as usize - 1).ok_or_else(|| RuntimeError::runtime(format!("{what} index out of range"))),
        _ => Err(bad()),
    }).collect()
}

fn submatrix_seqs(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    let rows = indices(a, 1, m.nrows, "Row")?;
    let cols = indices(a, 2, m.ncols, "Column")?;
    one(submatrix_of(it, &m, &rows, &cols)?)
}

fn insert_block_in(it: &mut Interp, a: &mut CallArgs) -> RResult<()> {
    let target = sparse_arg(a, 0)?;
    let block = sparse_arg(a, 1)?;
    let (i, j) = (a.int(2)?.clone(), a.int(3)?.clone());
    let fits = |x: &Integer, n: usize, k: usize| x.to_u64().is_some_and(|x| x >= 1 && x as usize + k <= n + 1);
    if !fits(&i, target.nrows, block.nrows) || !fits(&j, target.ncols, block.ncols) {
        return Err(RuntimeError::runtime(format!("Argument 2 ({} by {}) does not fit into argument 1 ({} by {}) at position [{i}, {j}]", block.nrows, block.ncols, target.nrows, target.ncols)));
    }
    if target.ring() != block.ring() {
        return Err(RuntimeError::runtime("Arguments have incompatible coefficient rings"));
    }
    let (i, j) = (i.to_u64().unwrap() as usize - 1, j.to_u64().unwrap() as usize - 1);
    let entries = block.entries(it);
    let Value::Sparse(target) = &mut a.args[0] else { unreachable!() };
    let target = Rc::make_mut(target);
    target.clear_block(i, j, block.nrows, block.ncols);
    for (r, c, x) in entries {
        target.set(it, i + r, j + c, &x)?;
    }
    Ok(())
}

fn insert_block_proc(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    insert_block_in(it, a)?;
    none()
}

fn insert_block_func(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    insert_block_in(it, a)?;
    one(std::mem::take(&mut a.args[0]))
}

fn row_submatrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    let (i, k) = if a.args.len() == 3 {
        let i = int_in(a, 1, 1, m.nrows as i64 + 1)?;
        (i, int_in(a, 2, 0, m.nrows as i64 + 1 - i as i64)?)
    } else {
        (1, int_in(a, 1, 0, m.nrows as i64)?)
    };
    one(submatrix_of(it, &m, &(i - 1..i - 1 + k).collect::<Vec<_>>(), &(0..m.ncols).collect::<Vec<_>>())?)
}

fn row_submatrix_range(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    let i = int_in(a, 1, 1, m.nrows as i64 + 1)?;
    let j = int_in(a, 2, i as i64 - 1, m.nrows as i64)?;
    one(submatrix_of(it, &m, &(i - 1..j).collect::<Vec<_>>(), &(0..m.ncols).collect::<Vec<_>>())?)
}

fn column_submatrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    let (i, k) = if a.args.len() == 3 {
        let i = int_in(a, 1, 1, m.ncols as i64 + 1)?;
        (i, int_in(a, 2, 0, m.ncols as i64 + 1 - i as i64)?)
    } else {
        (1, int_in(a, 1, 0, m.ncols as i64)?)
    };
    one(submatrix_of(it, &m, &(0..m.nrows).collect::<Vec<_>>(), &(i - 1..i - 1 + k).collect::<Vec<_>>())?)
}

fn column_submatrix_range(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = sparse_arg(a, 0)?;
    let i = int_in(a, 1, 1, m.ncols as i64 + 1)?;
    let j = int_in(a, 2, i as i64 - 1, m.ncols as i64)?;
    one(submatrix_of(it, &m, &(0..m.nrows).collect::<Vec<_>>(), &(i - 1..j).collect::<Vec<_>>())?)
}

fn line_number(a: &CallArgs, k: usize, what: &str, n: usize) -> RResult<usize> {
    let x = a.int(k)?;
    x.to_u64().filter(|&x| (1..=n as u64).contains(&x)).map(|x| x as usize - 1)
        .ok_or_else(|| RuntimeError::runtime(format!("Value for {what} number ({x}) should be in the range [1..{n}]")))
}

fn scalar_value(it: &mut Interp, m: &SparseMatrix, x: &Value) -> RResult<Value> {
    crate::intrinsics::matrices::scalar(it, m.ring(), &m.info().ctx, x)?
        .map(|x| it.elem_to_value(m.ring(), x))
        .ok_or_else(|| bad())
}

fn mul_values(it: &mut Interp, a: Value, b: Value) -> RResult<Value> {
    it.binop(BinOp::Mul, a, b).map_err(|e| e.in_context("*"))
}

fn add_values(it: &mut Interp, a: Value, b: Value) -> RResult<Value> {
    it.binop(BinOp::Add, a, b).map_err(|e| e.in_context("+"))
}

fn def_both(it: &mut Interp, name: &str, args: &str, doc: &str, proc_: crate::intrinsics::NativeFn, func: crate::intrinsics::NativeFn) {
    it.def(name, &format!("~A::MtrxSprs{args}"), doc, proc_);
    it.def(name, &format!("A::MtrxSprs{args} -> MtrxSprs"), doc, func);
}

macro_rules! sparse_op {
    ($proc:ident, $func:ident, $body:expr) => {
        fn $proc(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
            let f: fn(&mut Interp, &mut CallArgs) -> RResult<()> = $body;
            f(it, a)?;
            none()
        }
        fn $func(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
            let f: fn(&mut Interp, &mut CallArgs) -> RResult<()> = $body;
            f(it, a)?;
            one(std::mem::take(&mut a.args[0]))
        }
    };
}

sparse_op!(swap_rows_proc, swap_rows_func, |_, a| {
    let m = sparse_arg(a, 0)?;
    let (i, j) = (line_number(a, 1, "row", m.nrows)?, line_number(a, 2, "row", m.nrows)?);
    let Value::Sparse(m) = &mut a.args[0] else { unreachable!() };
    Rc::make_mut(m).swap_rows(i, j);
    Ok(())
});

sparse_op!(swap_cols_proc, swap_cols_func, |_, a| {
    let m = sparse_arg(a, 0)?;
    let (i, j) = (line_number(a, 1, "column", m.ncols)?, line_number(a, 2, "column", m.ncols)?);
    let Value::Sparse(m) = &mut a.args[0] else { unreachable!() };
    Rc::make_mut(m).map_columns(|c| Some(if c == i { j } else if c == j { i } else { c }));
    Ok(())
});

sparse_op!(reverse_rows_proc, reverse_rows_func, |_, a| {
    let Value::Sparse(m) = &mut a.args[0] else { unreachable!() };
    Rc::make_mut(m).reverse_rows();
    Ok(())
});

sparse_op!(reverse_cols_proc, reverse_cols_func, |_, a| {
    let Value::Sparse(m) = &mut a.args[0] else { unreachable!() };
    let n = m.ncols;
    Rc::make_mut(m).map_columns(|c| Some(n - 1 - c));
    Ok(())
});

sparse_op!(add_row_proc, add_row_func, |it, a| {
    let m = sparse_arg(a, 0)?;
    let c = scalar_value(it, &m, &a.args[1])?;
    let (src, dst) = (line_number(a, 2, "row", m.nrows)?, line_number(a, 3, "row", m.nrows)?);
    let entries: Vec<(usize, Value)> = m.columns(src).into_iter().map(|j| (j, m.entry(it, src, j))).collect();
    let Value::Sparse(m) = &mut a.args[0] else { unreachable!() };
    for (j, x) in entries {
        let y = Rc::make_mut(m).entry(it, dst, j);
        let cx = mul_values(it, c.clone(), x)?;
        let z = add_values(it, y, cx)?;
        Rc::make_mut(m).set(it, dst, j, &z)?;
    }
    Ok(())
});

sparse_op!(add_col_proc, add_col_func, |it, a| {
    let m = sparse_arg(a, 0)?;
    let c = scalar_value(it, &m, &a.args[1])?;
    let (src, dst) = (line_number(a, 2, "column", m.ncols)?, line_number(a, 3, "column", m.ncols)?);
    let entries: Vec<(usize, Value)> = (0..m.nrows).filter_map(|i| m.columns(i).contains(&src).then(|| (i, m.entry(it, i, src)))).collect();
    let Value::Sparse(m) = &mut a.args[0] else { unreachable!() };
    for (i, x) in entries {
        let y = Rc::make_mut(m).entry(it, i, dst);
        let cx = mul_values(it, c.clone(), x)?;
        let z = add_values(it, y, cx)?;
        Rc::make_mut(m).set(it, i, dst, &z)?;
    }
    Ok(())
});

sparse_op!(mul_row_proc, mul_row_func, |it, a| {
    let m = sparse_arg(a, 0)?;
    let c = scalar_value(it, &m, &a.args[1])?;
    let i = line_number(a, 2, "row", m.nrows)?;
    let entries: Vec<(usize, Value)> = m.columns(i).into_iter().map(|j| (j, m.entry(it, i, j))).collect();
    let Value::Sparse(m) = &mut a.args[0] else { unreachable!() };
    for (j, x) in entries {
        let z = mul_values(it, c.clone(), x)?;
        Rc::make_mut(m).set(it, i, j, &z)?;
    }
    Ok(())
});

sparse_op!(mul_col_proc, mul_col_func, |it, a| {
    let m = sparse_arg(a, 0)?;
    let c = scalar_value(it, &m, &a.args[1])?;
    let j = line_number(a, 2, "column", m.ncols)?;
    let entries: Vec<(usize, Value)> = (0..m.nrows).filter_map(|i| m.columns(i).contains(&j).then(|| (i, m.entry(it, i, j)))).collect();
    let Value::Sparse(m) = &mut a.args[0] else { unreachable!() };
    for (i, x) in entries {
        let z = mul_values(it, c.clone(), x)?;
        Rc::make_mut(m).set(it, i, j, &z)?;
    }
    Ok(())
});

sparse_op!(remove_row_proc, remove_row_func, |_, a| {
    let m = sparse_arg(a, 0)?;
    let i = line_number(a, 1, "row", m.nrows)?;
    let keep: Vec<usize> = (0..m.nrows).filter(|&r| r != i).collect();
    let Value::Sparse(m) = &mut a.args[0] else { unreachable!() };
    Rc::make_mut(m).retain_rows(&keep);
    Ok(())
});

sparse_op!(remove_col_proc, remove_col_func, |_, a| {
    let m = sparse_arg(a, 0)?;
    let j = line_number(a, 1, "column", m.ncols)?;
    let Value::Sparse(m) = &mut a.args[0] else { unreachable!() };
    let m = Rc::make_mut(m);
    m.map_columns(|c| if c == j { None } else { Some(c - (c > j) as usize) });
    m.ncols -= 1;
    Ok(())
});

sparse_op!(remove_row_col_proc, remove_row_col_func, |_, a| {
    let m = sparse_arg(a, 0)?;
    let (i, j) = (line_number(a, 1, "row", m.nrows)?, line_number(a, 2, "column", m.ncols)?);
    let keep: Vec<usize> = (0..m.nrows).filter(|&r| r != i).collect();
    let Value::Sparse(m) = &mut a.args[0] else { unreachable!() };
    let m = Rc::make_mut(m);
    m.retain_rows(&keep);
    m.map_columns(|c| if c == j { None } else { Some(c - (c > j) as usize) });
    m.ncols -= 1;
    Ok(())
});

sparse_op!(remove_zero_rows_proc, remove_zero_rows_func, |_, a| {
    let m = sparse_arg(a, 0)?;
    let keep: Vec<usize> = (0..m.nrows).filter(|&i| m.row_len(i) != 0).collect();
    let Value::Sparse(m) = &mut a.args[0] else { unreachable!() };
    Rc::make_mut(m).retain_rows(&keep);
    Ok(())
});

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
        if let Rows::Integers(rows) = &a.rows {
            p.write(&format!("SparseMatrix({}, {}, \\[", a.nrows, a.ncols));
            for (i, row) in rows.iter().enumerate() {
                p.newline(indent + 4);
                p.write(&row.len().to_string());
                for (j, x) in row {
                    p.write(&format!(", {},{}", j + 1, x));
                }
                if i + 1 < rows.len() {
                    p.write(",");
                }
            }
            p.newline(indent);
            p.write("])");
            return Ok(());
        }
        if let Rows::Words(rows) = &a.rows {
            p.write("SparseMatrix(");
            it.fmt(p, a.ring(), indent)?;
            p.write(&format!(", {}, {}, \\[", a.nrows, a.ncols));
            for (i, row) in rows.iter().enumerate() {
                p.newline(indent + 4);
                p.write(&row.len().to_string());
                for (j, x) in row {
                    p.write(&format!(", {},{}", j + 1, x));
                }
                if i + 1 < rows.len() {
                    p.write(",");
                }
            }
            p.newline(indent);
            p.write("])");
            return Ok(());
        }
        p.write("SparseMatrix(");
        it.fmt(p, a.ring(), indent)?;
        p.write(&format!(", {}, {}, [", a.nrows, a.ncols));
        let mut entries = Vec::with_capacity(a.nnz());
        let mut push = |i: usize, j: usize, x: Value| {
            entries.push(Value::tuple(vec![Value::int(i as i64 + 1), Value::int(j as i64 + 1), x]));
        };
        match &a.rows {
            Rows::Generic(rows) => for (i, row) in rows.iter().enumerate() {
                for (j, x) in row { push(i, *j, it.elem_to_value(a.ring(), x.clone())); }
            },
            Rows::Integers(_) | Rows::Words(_) => unreachable!(),
        }
        if entries.is_empty() {
            p.newline(indent);
            p.write("])");
        } else {
            p.newline(indent + 4);
            for (i, entry) in entries.iter().enumerate() {
                it.fmt(p, entry, indent + 4)?;
                if i + 1 < entries.len() {
                    p.write(", ");
                }
            }
            p.write("])");
        }
        if let Some((_, ring)) = ring_of(a.ring())
            && matches!(&ring.kind, RingKind::Finite(f) if f.degree > 1)
            && ring.has_names()
        {
            p.write(&format!(" where {} := ", ring.gen_name(1)));
            it.fmt(p, a.ring(), indent)?;
            p.write(".1");
        }
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
    p.write("Set of all sparse matrices over ");
    let saved = p.level;
    p.level = Level::Minimal;
    let r = it.fmt(p, &ring, indent);
    p.level = saved;
    r
}

pub fn register(it: &mut Interp) {
    it.def("SparseMatrix", "R::Rng, m::RngIntElt, n::RngIntElt, Q::SeqEnum -> MtrxSprs", "The m by n sparse matrix over R given by Q.", sparse_rmnq);
    it.def("SparseMatrix", "m::RngIntElt, n::RngIntElt, Q::SeqEnum -> MtrxSprs", "The m by n sparse matrix given by Q.", sparse_mnq);
    it.def("SparseMatrix", "R::Rng, m::RngIntElt, n::RngIntElt -> MtrxSprs", "The m by n zero sparse matrix over R.", sparse_rmn);
    it.def("SparseMatrix", "m::RngIntElt, n::RngIntElt -> MtrxSprs", "The m by n zero sparse matrix over the integers.", sparse_mn);
    it.def("SparseMatrix", "R::Rng -> MtrxSprs", "The empty sparse matrix over R.", sparse_r);
    it.def("SparseMatrix", "-> MtrxSprs", "The empty sparse matrix over the integers.", sparse_empty);
    it.def("IdentitySparseMatrix", "R::Rng, n::RngIntElt -> MtrxSprs", "The n by n identity sparse matrix over R.", identity_sparse);
    it.def("ScalarSparseMatrix", "n::RngIntElt, s::RngElt -> MtrxSprs", "The n by n scalar sparse matrix s.", scalar_sparse);
    it.def("ScalarSparseMatrix", "R::Rng, n::RngIntElt, s::RngElt -> MtrxSprs", "The n by n scalar sparse matrix s over R.", scalar_sparse);
    it.def("DiagonalSparseMatrix", "R::Rng, n::RngIntElt, Q::SeqEnum -> MtrxSprs", "The diagonal sparse matrix over R with diagonal Q.", diagonal_sparse);
    it.def("DiagonalSparseMatrix", "R::Rng, Q::SeqEnum -> MtrxSprs", "The diagonal sparse matrix over R with diagonal Q.", diagonal_sparse);
    it.def("DiagonalSparseMatrix", "Q::SeqEnum -> MtrxSprs", "The diagonal sparse matrix with diagonal Q.", diagonal_sparse);
    it.def("SparseMonomialMatrix", "g::GrpPermElt -> MtrxSprs", "The signed monomial sparse matrix of g.", sparse_monomial);
    it.def("SparseMatrixStructure", "R::Rng -> MtrxSprsStr", "The structure of sparse matrices over R.", sparse_structure);
    for name in ["BaseRing", "CoefficientRing"] {
        it.def(name, "A::MtrxSprs -> Rng", "The coefficient ring of A.", base_ring);
    }
    for name in ["NumberOfRows", "Nrows"] {
        it.def(name, "A::MtrxSprs -> RngIntElt", "The number of rows of A.", nrows);
    }
    for name in ["NumberOfColumns", "Ncols"] {
        it.def(name, "A::MtrxSprs -> RngIntElt", "The number of columns of A.", ncols);
    }
    for name in ["ElementToSequence", "Eltseq"] {
        it.def(name, "A::MtrxSprs -> SeqEnum", "The nonzero entries of A as triples.", eltseq);
    }
    for name in ["NumberOfNonZeroEntries", "NNZEntries"] {
        it.def(name, "A::MtrxSprs -> RngIntElt", "The number of nonzero entries of A.", nnz);
    }
    it.def("Density", "A::MtrxSprs -> FldReElt", "The proportion of nonzero entries of A.", density);
    it.def("Support", "A::MtrxSprs, i::RngIntElt -> [RngIntElt]", "The support of row i of A.", support_row);
    it.def("Support", "A::MtrxSprs -> SeqEnum", "The positions of the nonzero entries of A.", support);
    it.def("RowWeight", "A::MtrxSprs, i::RngIntElt -> RngIntElt", "The number of nonzero entries in row i.", row_weight);
    it.def("RowWeights", "A::MtrxSprs -> [RngIntElt]", "The row weights of A.", row_weights);
    it.def("ColumnWeight", "A::MtrxSprs, j::RngIntElt -> RngIntElt", "The number of nonzero entries in column j.", column_weight);
    it.def("ColumnWeights", "A::MtrxSprs -> [RngIntElt]", "The column weights of A.", column_weights);
    it.def("SetEntry", "~A::MtrxSprs, i::RngIntElt, j::RngIntElt, x::RngElt", "Set entry (i, j), extending A if needed.", set_entry_proc);
    let block = "A::MtrxSprs, i::RngIntElt, j::RngIntElt, p::RngIntElt, q::RngIntElt -> MtrxSprs";
    for name in ["Submatrix", "ExtractBlock"] {
        it.def(name, block, "The p by q sparse block of A at (i, j).", submatrix);
    }
    for name in ["SubmatrixRange", "ExtractBlockRange"] {
        it.def(name, block, "The sparse block of A from (i, j) to (p, q).", submatrix_range);
    }
    it.def("Submatrix", "A::MtrxSprs, I::[RngIntElt], J::[RngIntElt] -> MtrxSprs", "The sparse submatrix with rows I and columns J.", submatrix_seqs);
    it.def("InsertBlock", "~A::MtrxSprs, B::MtrxSprs, i::RngIntElt, j::RngIntElt", "Insert B into A at (i, j).", insert_block_proc);
    it.def("InsertBlock", "A::MtrxSprs, B::MtrxSprs, i::RngIntElt, j::RngIntElt -> MtrxSprs", "A with B inserted at (i, j).", insert_block_func);
    it.def("RowSubmatrix", "A::MtrxSprs, i::RngIntElt, k::RngIntElt -> MtrxSprs", "The k rows of A from row i.", row_submatrix);
    it.def("RowSubmatrix", "A::MtrxSprs, i::RngIntElt -> MtrxSprs", "The first i rows of A.", row_submatrix);
    it.def("RowSubmatrixRange", "A::MtrxSprs, i::RngIntElt, j::RngIntElt -> MtrxSprs", "Rows i through j of A.", row_submatrix_range);
    it.def("ColumnSubmatrix", "A::MtrxSprs, i::RngIntElt, k::RngIntElt -> MtrxSprs", "The k columns of A from column i.", column_submatrix);
    it.def("ColumnSubmatrix", "A::MtrxSprs, i::RngIntElt -> MtrxSprs", "The first i columns of A.", column_submatrix);
    it.def("ColumnSubmatrixRange", "A::MtrxSprs, i::RngIntElt, j::RngIntElt -> MtrxSprs", "Columns i through j of A.", column_submatrix_range);
    let ij = ", i::RngIntElt, j::RngIntElt";
    def_both(it, "SwapRows", ij, "Swap rows i and j of A.", swap_rows_proc, swap_rows_func);
    def_both(it, "SwapColumns", ij, "Swap columns i and j of A.", swap_cols_proc, swap_cols_func);
    def_both(it, "ReverseRows", "", "Reverse the rows of A.", reverse_rows_proc, reverse_rows_func);
    def_both(it, "ReverseColumns", "", "Reverse the columns of A.", reverse_cols_proc, reverse_cols_func);
    let cij = ", c::RngElt, i::RngIntElt, j::RngIntElt";
    def_both(it, "AddRow", cij, "Add c times row i to row j.", add_row_proc, add_row_func);
    def_both(it, "AddColumn", cij, "Add c times column i to column j.", add_col_proc, add_col_func);
    let ci = ", c::RngElt, i::RngIntElt";
    def_both(it, "MultiplyRow", ci, "Multiply row i by c.", mul_row_proc, mul_row_func);
    def_both(it, "MultiplyColumn", ci, "Multiply column i by c.", mul_col_proc, mul_col_func);
    def_both(it, "RemoveRow", ", i::RngIntElt", "Remove row i.", remove_row_proc, remove_row_func);
    def_both(it, "RemoveColumn", ", j::RngIntElt", "Remove column j.", remove_col_proc, remove_col_func);
    def_both(it, "RemoveRowColumn", ij, "Remove row i and column j.", remove_row_col_proc, remove_row_col_func);
    def_both(it, "RemoveZeroRows", "", "Remove all zero rows.", remove_zero_rows_proc, remove_zero_rows_func);
    it.def("HorizontalJoin", "A::MtrxSprs, B::MtrxSprs -> MtrxSprs", "Join B to the right of A.", horizontal_join);
    it.def("VerticalJoin", "A::MtrxSprs, B::MtrxSprs -> MtrxSprs", "Join B below A.", vertical_join);
    it.def("DiagonalJoin", "A::MtrxSprs, B::MtrxSprs -> MtrxSprs", "Join A and B as diagonal blocks.", diagonal_join);
    it.def("Matrix", "A::MtrxSprs -> Mtrx", "The dense matrix equal to A.", dense_matrix);
    it.def("SparseMatrix", "A::Mtrx -> MtrxSprs", "The sparse matrix equal to A.", from_dense);
    it.def("ChangeRing", "A::MtrxSprs, R::Rng -> MtrxSprs", "A with its entries coerced into R.", change_ring);
    it.def("SparseMatrix", "R::Rng, A::MtrxSprs -> MtrxSprs", "The sparse matrix over R with the entries of A.", sparse_over);
    it.def("IsZero", "A::MtrxSprs -> BoolElt", "Whether A is zero.", is_zero);
    it.def("IsOne", "A::MtrxSprs -> BoolElt", "Whether A is the identity.", is_one);
    it.def("IsMinusOne", "A::MtrxSprs -> BoolElt", "Whether A is minus the identity.", is_minus_one);
    it.def("IsScalar", "A::MtrxSprs -> BoolElt", "Whether A is scalar.", is_scalar);
    it.def("IsDiagonal", "A::MtrxSprs -> BoolElt", "Whether A is diagonal.", is_diagonal);
    it.def("IsSymmetric", "A::MtrxSprs -> BoolElt", "Whether A is symmetric.", is_symmetric);
    it.def("IsUpperTriangular", "A::MtrxSprs -> BoolElt", "Whether A is upper triangular.", is_upper);
    it.def("IsLowerTriangular", "A::MtrxSprs -> BoolElt", "Whether A is lower triangular.", is_lower);
    it.def("Transpose", "A::MtrxSprs -> MtrxSprs", "The transpose of A.", transpose);
    it.def("MultiplyByTranspose", "v::ModTupRngElt, A::MtrxSprs -> ModTupRngElt", "v times the transpose of A.", multiply_by_transpose);
    it.def("MultiplyByTranspose", "V::Mtrx, A::MtrxSprs -> Mtrx", "V times the transpose of A.", multiply_by_transpose);
    linalg::register(it);
}
