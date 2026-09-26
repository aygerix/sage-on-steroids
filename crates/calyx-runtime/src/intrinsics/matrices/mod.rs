//! Matrices (#76): creating matrices and vectors, their entries, rows and
//! blocks, arithmetic and linear algebra, as in the Matrices chapter of the
//! handbook.
//!
//! A matrix is a FLINT matrix over the context of its coefficient ring,
//! with a parent that gives its shape and category: the full matrix
//! algebra of degree n (`AlgMat`) for an n by n matrix, the full matrix
//! space (`ModMatRng`, or `ModMatFld` over a field) for another, and the
//! full R-space (`ModTupRng`, `ModTupFld`) for a vector, which is a matrix
//! with one row. The parents are made once for each ring and shape.
//!
//! A subspace of an R-space (a kernel, say) is a parent of the same shape
//! with a basis (`Sub`); its vectors are 1 by n matrices like any others.
//!
//! The submodules follow the sections of the handbook chapter; this module
//! has the values, the parents and the helpers they share.

mod access;
mod arith;
mod blocks;
mod canonical;
mod change;
mod charpoly;
mod creation;
mod linalg;
mod numerical;
mod predicates;
mod print;
mod spaces;

use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use calyx_flint::gr::{Ctx, CtxKind, Elem, Truth};
use calyx_flint::mat::Mat;
use calyx_flint::Real;
use rustc_hash::{FxHashMap, FxHasher};

use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::rings::{RingKind, small, structure_key};
use crate::types::{TypeId, t};
use crate::value::*;

pub use access::{index, set_index};
pub use arith::{binop, equal, negate};
pub use creation::coerce;
pub use linalg::{echelon, rank_of};
pub use print::{fmt_matrix, fmt_parent};
pub use spaces::elements;

/// A matrix or a vector: its entries and its parent.
#[derive(Clone)]
pub struct Mtrx {
    pub parent: Rc<Struct>,
    pub m: Mat,
}

/// A full matrix algebra, matrix space or R-space.
pub struct MatParent {
    /// The coefficient ring.
    pub ring: Value,
    pub nrows: usize,
    pub ncols: usize,
    pub shape: Shape,
    /// Whether the coefficient ring is a field (which makes the categories
    /// `ModMatFld` and `ModTupFld`).
    pub field: bool,
    /// The FLINT context of the entries.
    pub ctx: Rc<Ctx>,
    /// For a subspace of an R-space, its basis.
    pub sub: Option<Sub>,
}

/// The basis of a subspace of an R-space, and the full space.
pub struct Sub {
    /// The full R-space of the same degree.
    pub full: Rc<Struct>,
    /// The basis, a vector in each row.
    pub basis: Mat,
    /// Whether the basis is echelonized (as for kernels), rather than given.
    pub echelonized: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Shape {
    /// All n by n matrices, a ring.
    Algebra,
    /// All m by n matrices, a module.
    Space,
    /// The vectors of length n, as 1 by n matrices.
    Tuples,
}

impl MatParent {
    pub fn type_id(&self) -> TypeId {
        match (self.shape, self.field) {
            (Shape::Algebra, _) => t::ALG_MAT,
            (Shape::Space, false) => t::MOD_MAT_RNG,
            (Shape::Space, true) => t::MOD_MAT_FLD,
            (Shape::Tuples, false) => t::MOD_TUP_RNG,
            (Shape::Tuples, true) => t::MOD_TUP_FLD,
        }
    }

    pub fn elt_type(&self) -> TypeId {
        match (self.shape, self.field) {
            (Shape::Algebra, _) => t::ALG_MAT_ELT,
            (Shape::Space, false) => t::MOD_MAT_RNG_ELT,
            (Shape::Space, true) => t::MOD_MAT_FLD_ELT,
            (Shape::Tuples, false) => t::MOD_TUP_RNG_ELT,
            (Shape::Tuples, true) => t::MOD_TUP_FLD_ELT,
        }
    }

    pub fn same_as(&self, o: &MatParent) -> bool {
        let subs = match (&self.sub, &o.sub) {
            (None, None) => true,
            (Some(a), Some(b)) => a.echelonized == b.echelonized && a.basis.equal(&b.basis) == Truth::True,
            _ => false,
        };
        self.shape == o.shape && self.nrows == o.nrows && self.ncols == o.ncols && self.ring == o.ring && subs
    }

    pub fn hash_key(&self) -> u64 {
        let mut h = FxHasher::default();
        (self.shape, self.nrows, self.ncols).hash(&mut h);
        self.ring.hash(&mut h);
        if let Some(s) = &self.sub {
            s.basis.nrows().hash(&mut h);
        }
        h.finish()
    }

    /// The dimension: the number of basis vectors of a subspace, the degree
    /// of a full space.
    pub fn dimension(&self) -> usize {
        self.sub.as_ref().map_or(self.ncols, |s| s.basis.nrows())
    }
}

impl Mtrx {
    pub fn info(&self) -> &MatParent {
        info(&self.parent)
    }

    pub fn ring(&self) -> &Value {
        &self.info().ring
    }

    pub fn is_vector(&self) -> bool {
        self.info().shape == Shape::Tuples
    }

    pub fn type_id(&self) -> TypeId {
        self.info().elt_type()
    }

    pub fn same_as(&self, o: &Mtrx) -> bool {
        (Rc::ptr_eq(&self.parent, &o.parent) || self.info().same_as(o.info())) && self.m.equal(&o.m) == Truth::True
    }

    pub fn hash_u64(&self) -> u64 {
        let mut h = FxHasher::default();
        let m = &self.m;
        (m.nrows(), m.ncols()).hash(&mut h);
        for i in 0..m.nrows() {
            for j in 0..m.ncols() {
                match m.ctx().kind() {
                    CtxKind::Integers => m.integer(i, j).hash_u64().hash(&mut h),
                    CtxKind::Nmod(_) => m.word(i, j).hash(&mut h),
                    CtxKind::FqZech { .. } | CtxKind::FqNmod { .. } | CtxKind::FqPacked { .. } | CtxKind::Fq { .. } => m.entry(i, j).fq_coords().hash(&mut h),
                    _ => m.entry(i, j).to_flint_string().hash(&mut h),
                }
            }
        }
        h.finish()
    }
}

/// The parent structure of matrices.
pub fn info(st: &Struct) -> &MatParent {
    match &st.kind {
        StructKind::Matrices(p) => p,
        _ => unreachable!("a matrix with a parent that holds no matrices"),
    }
}

/// Whether `v` is an R-space or a subspace of one.
pub fn is_rspace(v: &Value) -> bool {
    parent_info(v).is_some_and(|p| p.shape == Shape::Tuples)
}

/// The parent data of a structure, if it is a matrix algebra or space.
pub fn parent_info(v: &Value) -> Option<&MatParent> {
    match v {
        Value::Struct(st) => match &st.kind {
            StructKind::Matrices(p) => Some(p),
            _ => None,
        },
        _ => None,
    }
}

// ----- parents ----------------------------------------------------------------

thread_local! {
    /// The parents made so far, by ring, dimensions and shape.
    static PARENTS: RefCell<FxHashMap<(String, usize, usize, Shape), Rc<Struct>>> = RefCell::default();
}

/// The full matrix algebra, matrix space or R-space over `ring` of the
/// given shape.
pub fn parent(it: &mut Interp, ring: &Value, nrows: usize, ncols: usize, shape: Shape) -> RResult<Rc<Struct>> {
    let key = structure_key(ring).map(|k| (k, nrows, ncols, shape));
    if let Some(k) = &key {
        if let Some(p) = PARENTS.with(|c| c.borrow().get(k).cloned()) {
            return Ok(p);
        }
    }
    let ctx = entry_ctx(it, ring)?;
    let field = it.types.isa(ring.type_id(), t::FLD);
    let p = Struct::new(StructKind::Matrices(Rc::new(MatParent { ring: ring.clone(), nrows, ncols, shape, field, ctx, sub: None })));
    if let Some(k) = key {
        PARENTS.with(|c| c.borrow_mut().insert(k, p.clone()));
    }
    Ok(p)
}

/// The universe of matrices in two matrix algebras or spaces of one size
/// over different rings: the one over a ring containing both (Z and Q
/// matrices meet in the rational ones). Vectors over different rings have
/// none, as in Magma.
pub fn cover(it: &mut Interp, a: &Value, b: &Value) -> RResult<Option<Value>> {
    let (Some(p), Some(q)) = (parent_info(a), parent_info(b)) else { return Ok(None) };
    if p.shape != q.shape || p.shape == Shape::Tuples || p.nrows != q.nrows || p.ncols != q.ncols || p.sub.is_some() || q.sub.is_some() {
        return Ok(None);
    }
    let (r, s, (m, n, shape)) = (p.ring.clone(), q.ring.clone(), (p.nrows, p.ncols, p.shape));
    let Some(ring) = it.covering_universe(&r, &s)? else { return Ok(None) };
    Ok(parent(it, &ring, m, n, shape).ok().map(Value::Struct))
}

/// The FLINT context of the entries of matrices over `ring`.
pub fn entry_ctx(it: &mut Interp, ring: &Value) -> RResult<Rc<Ctx>> {
    let supported = match ring.as_struct() {
        Some(StructKind::Integers | StructKind::Rationals | StructKind::Reals(_)) => true,
        Some(StructKind::Ring(r)) => !matches!(r.kind, RingKind::UPolyRes { .. } | RingKind::MPolyRes { .. }),
        _ => false,
    };
    match it.ctx_of(ring) {
        Some(ctx) if supported => Ok(ctx),
        _ => Err(RuntimeError::runtime("Matrices over this ring are not supported")),
    }
}

/// The parent of an m by n matrix over `ring`: the matrix algebra when it
/// is square, the matrix space otherwise.
pub fn matrix_parent(it: &mut Interp, ring: &Value, nrows: usize, ncols: usize) -> RResult<Rc<Struct>> {
    parent(it, ring, nrows, ncols, if nrows == ncols { Shape::Algebra } else { Shape::Space })
}

/// A matrix over `ring` with the entries `m`, in the matrix algebra or
/// space of its shape.
pub fn mat_value(it: &mut Interp, ring: &Value, m: Mat) -> RResult<Value> {
    let p = matrix_parent(it, ring, m.nrows(), m.ncols())?;
    Ok(Value::Mat(Rc::new(Mtrx { parent: p, m })))
}

/// A vector over `ring` with the entries of the one row of `m`.
pub fn vec_value(it: &mut Interp, ring: &Value, m: Mat) -> RResult<Value> {
    debug_assert_eq!(m.nrows(), 1);
    let p = parent(it, ring, 1, m.ncols(), Shape::Tuples)?;
    Ok(Value::Mat(Rc::new(Mtrx { parent: p, m })))
}

/// A matrix like `a` (the same ring, shape and dimensions) with the
/// entries `m`.
pub fn like(a: &Mtrx, m: Mat) -> Value {
    debug_assert!(m.nrows() == a.m.nrows() && m.ncols() == a.m.ncols());
    Value::Mat(Rc::new(Mtrx { parent: a.parent.clone(), m }))
}

/// A matrix over the ring of `a` with the entries `m`, which may have
/// other dimensions: a vector if `a` is one and `m` has one row, a matrix
/// otherwise.
pub fn over_ring_of(it: &mut Interp, a: &Mtrx, m: Mat) -> RResult<Value> {
    let info = a.info();
    if m.nrows() == info.nrows && m.ncols() == info.ncols {
        return Ok(like(a, m));
    }
    let ring = info.ring.clone();
    if a.is_vector() && m.nrows() == 1 { vec_value(it, &ring, m) } else { mat_value(it, &ring, m) }
}

// ----- entries -----------------------------------------------------------------

/// The entry (i, j) of `a` as a value (from 0).
pub fn entry_value(it: &Interp, a: &Mtrx, i: usize, j: usize) -> Value {
    entry_of(it, a.ring(), &a.m, i, j)
}

/// The entry (i, j) of `m`, a matrix over `ring`, as a value (from 0).
pub fn entry_of(it: &Interp, ring: &Value, m: &Mat, i: usize, j: usize) -> Value {
    match (m.ctx().kind(), ring) {
        (CtxKind::Integers, _) => Value::Int(m.integer(i, j)),
        (CtxKind::Nmod(_), Value::Struct(st)) => match &st.kind {
            StructKind::Ring(r) if r.small.is_some() => Value::Small(r.small.unwrap(), m.word(i, j)),
            _ => it.elem_to_value(ring, m.entry(i, j)),
        },
        _ if m.neg_zero(i, j) => match it.elem_to_value(ring, m.entry(i, j)) {
            Value::Real(r) => Value::real(Real::signed_zero(r.x.prec(), true)),
            Value::Complex(c) => Value::complex(Real::signed_zero(c.re.prec(), true), c.im.clone()),
            v => v,
        },
        _ => it.elem_to_value(ring, m.entry(i, j)),
    }
}

/// Whether `x` is a real or complex number whose real part is -0.
fn negative_zero(x: &Value) -> bool {
    match x {
        Value::Real(r) => r.x.is_zero() && r.x.is_sign_negative(),
        Value::Complex(c) => c.re.is_zero() && c.re.is_sign_negative(),
        _ => false,
    }
}

/// Set the entry (i, j) of `m`, a matrix over `ring`, to `x` coerced into
/// the ring (as by `!`); false if it does not coerce.
pub fn set_entry(it: &mut Interp, ring: &Value, m: &mut Mat, i: usize, j: usize, x: &Value) -> RResult<bool> {
    match x {
        Value::Int(n) => return Ok(m.set_integer(i, j, n).is_ok()),
        Value::Rat(q) if ring.is_rationals() => return Ok(m.set_rational(i, j, q).is_ok()),
        Value::Small(s, w) => {
            if let Some(StructKind::Ring(r)) = ring.as_struct() {
                if r.small == Some(*s) {
                    match m.ctx().kind() {
                        CtxKind::Nmod(_) => m.set_word(i, j, *w),
                        _ => m.set_entry(i, j, &small::elem_of(*s, &r.ctx, *w)),
                    }
                    return Ok(true);
                }
            }
        }
        Value::Elt(e) => {
            if let Some(StructKind::Ring(r)) = ring.as_struct() {
                if e.ring().id == r.id {
                    m.set_entry(i, j, &e.x);
                    return Ok(true);
                }
            }
        }
        _ => {}
    }
    match it.to_structure_elem(ring, x, true)? {
        Some(e) if Rc::ptr_eq(e.ctx(), m.ctx()) => {
            m.set_entry(i, j, &e);
            if negative_zero(x) {
                m.set_neg_zero(i, j, true);
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

/// The element `x` of the coefficient ring of `a` (coerced as by `!`).
pub fn scalar(it: &mut Interp, ring: &Value, ctx: &Rc<Ctx>, x: &Value) -> RResult<Option<Elem>> {
    let mut m = Mat::zero(ctx, 1, 1);
    Ok(if set_entry(it, ring, &mut m, 0, 0, x)? { Some(m.entry(0, 0)) } else { None })
}

// ----- arguments ---------------------------------------------------------------

fn bad() -> RuntimeError {
    RuntimeError::runtime("Bad argument types")
}

/// Argument i as a matrix.
fn mat_arg(a: &CallArgs, i: usize) -> RResult<&Rc<Mtrx>> {
    match &a.args[i] {
        Value::Mat(m) => Ok(m),
        _ => Err(bad()),
    }
}

/// Argument i as a square matrix.
fn square(a: &CallArgs, i: usize) -> RResult<Rc<Mtrx>> {
    let m = mat_arg(a, i)?;
    if m.m.nrows() != m.m.ncols() {
        return Err(RuntimeError::runtime(format!("Argument {} is not square", i + 1)));
    }
    Ok(m.clone())
}

/// Register the intrinsics of the chapter.
pub fn register(it: &mut Interp) {
    creation::register(it);
    access::register(it);
    blocks::register(it);
    change::register(it);
    arith::register(it);
    linalg::register(it);
    numerical::register(it);
    charpoly::register(it);
    canonical::register(it);
    predicates::register(it);
    spaces::register(it);
}
