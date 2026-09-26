//! Subspaces of R-spaces, as far as the Matrices chapter needs them: the
//! nullspaces of matrices and the solutions of linear systems, with their
//! bases, equality and elements. The Vector Spaces chapter (#78) builds on
//! these.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Elem, Truth};
use calyx_flint::mat::Mat;

use super::{MatParent, Mtrx, Shape, Sub, info, scalar};
use crate::error::{NOT_ITERABLE, RResult, RuntimeError};
use crate::intrinsics::{intv, one};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

/// The subspace of the full R-space `full` with the echelonized basis
/// `basis` (a vector in each row): `full` itself when that is all of it.
pub fn subspace(full: &Rc<Struct>, basis: Mat) -> RResult<Rc<Struct>> {
    let mp = info(full);
    let n = mp.ncols;
    if basis.nrows() == n && basis.equal(&Mat::identity(&mp.ctx, n).map_err(|e| crate::rings::gr_error(e, "Identity failed"))?) == Truth::True {
        return Ok(full.clone());
    }
    let sub = Sub { full: full.clone(), basis, echelonized: true };
    let p = MatParent { ring: mp.ring.clone(), nrows: 1, ncols: n, shape: Shape::Tuples, field: mp.field, ctx: mp.ctx.clone(), sub: Some(sub), form: None };
    Ok(Struct::new(StructKind::Matrices(Rc::new(p))))
}

/// The full R-space of a space: itself, or the one a subspace lies in.
pub fn generic(st: &Rc<Struct>) -> Rc<Struct> {
    info(st).sub.as_ref().map_or_else(|| st.clone(), |s| s.full.clone())
}

/// The basis of a space, a vector in each row.
fn basis_of(st: &Struct) -> RResult<Mat> {
    let mp = info(st);
    match &mp.sub {
        Some(s) => Ok(s.basis.clone()),
        None => Mat::identity(&mp.ctx, mp.ncols).map_err(|e| crate::rings::gr_error(e, "Identity failed")),
    }
}

/// The elements of the finite ring of a space, in the ring's own order
/// (zero first).
fn ring_elements(it: &mut Interp, mp: &MatParent) -> RResult<Vec<Elem>> {
    let ring = mp.ring.clone();
    let finite = crate::rings::props::ring_props(&ring).and_then(|p| p.cardinality).is_some();
    if !finite {
        return Err(RuntimeError::runtime(NOT_ITERABLE));
    }
    let mut elems = it.iter_value(&ring, false)?;
    let mut out = Vec::new();
    while let Some((_, x)) = elems.next_item() {
        out.push(scalar(it, &ring, &mp.ctx, &x)?.expect("an element of the ring"));
    }
    Ok(out)
}

/// The elements of a finite R-space or subspace, one at a time, in Magma's
/// order. A full space counts up in the order of the ring's elements, the
/// first coordinate fastest. A subspace over a field runs through the
/// combinations of its basis like a Gray code: each step moves one
/// coefficient on to the next element of the ring (adding the difference
/// times its basis vector), and the lower ones stay where they are as their
/// counters wrap round. Over a residue ring the coefficients of a subspace
/// count up as the coordinates of a full space do.
pub fn elements(it: &mut Interp, st: &Rc<Struct>) -> RResult<Box<dyn Iterator<Item = Value>>> {
    let mp = info(st);
    if mp.shape != Shape::Tuples {
        return Err(RuntimeError::runtime(NOT_ITERABLE));
    }
    let (n, ctx) = (mp.ncols, mp.ctx.clone());
    let r = ring_elements(it, mp)?;
    let q = r.len();
    let st = st.clone();
    let vector = move |m: &Mat| Value::Mat(Rc::new(Mtrx { parent: st.clone(), m: m.clone() }));
    let mut v = Mat::zero(&ctx, 1, n);
    let Some(sub) = &mp.sub else {
        // The coordinates count up in base q.
        let mut digits = vec![0usize; n];
        let mut done = false;
        return Ok(Box::new(std::iter::from_fn(move || {
            if done {
                return None;
            }
            let out = vector(&v);
            done = true;
            for (j, d) in digits.iter_mut().enumerate() {
                *d = (*d + 1) % q;
                v.set_entry(0, j, &r[*d]);
                if *d != 0 {
                    done = false;
                    break;
                }
            }
            Some(out)
        })));
    };
    let b = sub.basis.clone();
    let k = b.nrows();
    let gr = |e| crate::rings::gr_error(e, "Arithmetic failed");
    // The change each step makes to the vector: in turn for each
    // coefficient, from its d-th value to the next (and, over a residue
    // ring, back to zero as it wraps).
    let mut steps: Vec<Vec<Mat>> = Vec::with_capacity(k);
    let mut counts = Vec::with_capacity(k);
    for j in 0..k {
        let bj = b.block(j, 0, 1, n);
        if mp.field {
            counts.push(q);
            let incs = (1..q).map(|d| bj.scalar_mul(&r[d].sub(&r[d - 1]).map_err(gr)?).map_err(gr)).collect::<RResult<Vec<_>>>()?;
            steps.push(incs);
        } else {
            // The coefficients of a basis vector run up to the additive
            // order of its first nonzero entry.
            let lead = (0..n).find(|&c| !bj.entry_is_zero(0, c)).map_or(Integer::one(), |c| bj.entry(0, c).to_integer().unwrap_or(Integer::one()));
            let m = Integer::from_u64(q as u64);
            let ord = m.divexact(&m.gcd(&lead)).to_u64().unwrap_or(1) as usize;
            counts.push(ord);
            let back = bj.scalar_mul(&Elem::from_integer(&ctx, &Integer::from_u64(ord as u64 - 1)).map_err(gr)?).map_err(gr)?.neg().map_err(gr)?;
            steps.push(vec![bj, back]);
        }
    }
    let field = mp.field;
    let mut digits = vec![0usize; k];
    let mut done = false;
    Ok(Box::new(std::iter::from_fn(move || {
        if done {
            return None;
        }
        let out = vector(&v);
        done = true;
        for j in 0..k {
            if digits[j] + 1 < counts[j] {
                digits[j] += 1;
                let step = if field { &steps[j][digits[j] - 1] } else { &steps[j][0] };
                v = v.add(step).ok()?;
                done = false;
                break;
            }
            digits[j] = 0;
            if !field {
                v = v.add(&steps[j][1]).ok()?;
            }
        }
        Some(out)
    })))
}

/// `#V` for a space over a finite ring.
fn cardinality(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Struct(st) = &a.args[0] else { unreachable!() };
    let mp = info(st);
    let q = match crate::rings::props::ring_props(&mp.ring).and_then(|p| p.cardinality) {
        Some(q) => q,
        None => return one(Value::Infinity(true)),
    };
    let Some(sub) = &mp.sub else {
        return intv(q.pow(mp.nrows as u64 * mp.ncols as u64));
    };
    if mp.field {
        return intv(q.pow(sub.basis.nrows() as u64));
    }
    let mut n = Integer::one();
    for j in 0..sub.basis.nrows() {
        let lead = (0..mp.ncols).find(|&c| !sub.basis.entry_is_zero(j, c)).map_or(Integer::one(), |c| sub.basis.entry(j, c).to_integer().unwrap_or(Integer::one()));
        n = &n * &q.divexact(&q.gcd(&lead));
    }
    let _ = it;
    intv(n)
}

/// `Dimension(V)`.
fn dimension(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Struct(st) = &a.args[0] else { unreachable!() };
    intv(Integer::from_u64(info(st).dimension() as u64))
}

/// `Degree(V)`.
fn degree(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Struct(st) = &a.args[0] else { unreachable!() };
    intv(Integer::from_u64(info(st).ncols as u64))
}

/// `Basis(V)`: its basis vectors, as elements of V.
fn basis(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Struct(st) = &a.args[0] else { unreachable!() };
    let b = basis_of(st)?;
    let n = b.ncols();
    let rows = (0..b.nrows()).map(|i| Value::Mat(Rc::new(Mtrx { parent: st.clone(), m: b.block(i, 0, 1, n) }))).collect();
    let _ = it;
    one(Value::seq(Some(Value::Struct(st.clone())), rows))
}

/// `BasisMatrix(V)`: the basis vectors as the rows of a matrix.
fn basis_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Struct(st) = &a.args[0] else { unreachable!() };
    let ring = info(st).ring.clone();
    let b = basis_of(st)?;
    one(super::mat_value(it, &ring, b)?)
}

pub fn register(it: &mut Interp) {
    for ty in ["ModTupRng", "ModMatRng", "AlgMat"] {
        it.def("#", &format!("V::{ty} -> RngIntElt"), "The number of elements of V.", cardinality);
    }
    it.def("Dimension", "V::ModTupRng -> RngIntElt", "The dimension of V.", dimension);
    it.def("Degree", "V::ModTupRng -> RngIntElt", "The length of the vectors of V.", degree);
    it.def("Basis", "V::ModTupRng -> SeqEnum", "The basis of V.", basis);
    it.def("BasisMatrix", "V::ModTupRng -> Mtrx", "The basis vectors of V as the rows of a matrix.", basis_matrix);
}
