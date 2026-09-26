//! Modular sparse systems and structured elimination (text/300).

use calyx_flint::Integer;
use calyx_flint::gr::CtxKind;
use calyx_flint::mat::Mat;
use rustc_hash::{FxHashMap, FxHashSet};

use super::sparse_arg;
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::factseq::{fact_int, fact_of};
use crate::intrinsics::one;
use crate::interp::{CallArgs, Interp};
use crate::sym::Sym;
use crate::value::*;

fn modulus(v: &Value) -> RResult<Integer> {
    let m = match v {
        Value::Int(m) => m.clone(),
        Value::Seq(_) => fact_int(&fact_of(v)?),
        _ => unreachable!("the signatures accept an integer or factorization"),
    };
    if m.sign() <= 0 {
        return Err(RuntimeError::runtime("The modulus must be positive"));
    }
    Ok(m)
}

#[inline]
fn mul(a: u64, b: u64, p: u64) -> u64 {
    (u128::from(a) * u128::from(b) % u128::from(p)) as u64
}

fn pow(mut a: u64, mut n: u64, p: u64) -> u64 {
    let mut r = 1;
    while n != 0 {
        if n & 1 != 0 { r = mul(r, a, p); }
        n >>= 1;
        if n != 0 { a = mul(a, a, p); }
    }
    r
}

/// One right-nullvector modulo a machine-word prime.  Rows stay sparse while
/// they are reduced against earlier pivots; back substitution then touches
/// only the stored nonzeros.  None means the right kernel is zero.
fn prime_solution(x: &super::SparseMatrix, p: u64) -> RResult<Option<Vec<Integer>>> {
    let modulus = Integer::from_u64(p);
    let mut pivots: FxHashMap<usize, Vec<(usize, u64)>> = FxHashMap::default();
    for i in 0..x.nrows {
        let mut row: FxHashMap<usize, u64> = FxHashMap::default();
        for (j, e) in x.row_elems(i)? {
            let z = e.to_integer().map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?.fdiv_qr(&modulus).unwrap().1.to_u64().unwrap();
            if z != 0 { row.insert(j, z); }
        }
        loop {
            let Some(c) = row.keys().filter(|c| pivots.contains_key(c)).min().copied() else { break };
            let q = row[&c];
            for &(j, y) in &pivots[&c] {
                let old = row.get(&j).copied().unwrap_or(0);
                let z = mul(q, y, p);
                let new = if old >= z { old - z } else { p - (z - old) };
                if new == 0 { row.remove(&j); } else { row.insert(j, new); }
            }
        }
        let Some(c) = row.keys().min().copied() else { continue };
        let inv = pow(row[&c], p - 2, p);
        let mut pivot: Vec<(usize, u64)> = row.into_iter().map(|(j, y)| (j, mul(y, inv, p))).collect();
        pivot.sort_unstable_by_key(|e| e.0);
        pivots.insert(c, pivot);
    }
    if pivots.len() == x.ncols { return Ok(None); }
    let occupied: FxHashSet<usize> = pivots.keys().copied().collect();
    let free = (0..x.ncols).find(|j| !occupied.contains(j)).unwrap();
    let mut v = vec![0u64; x.ncols];
    v[free] = 1;
    let mut pcs: Vec<usize> = pivots.keys().copied().collect();
    pcs.sort_unstable_by(|a, b| b.cmp(a));
    for c in pcs {
        let sum = pivots[&c].iter().filter(|(j, _)| *j != c).fold(0u64, |s, (j, y)| ((u128::from(s) + u128::from(mul(*y, v[*j], p))) % u128::from(p)) as u64);
        v[c] = if sum == 0 { 0 } else { p - sum };
    }
    if let Some(inv) = Integer::from_u64(v[0]).invmod(&modulus) {
        let inv = inv.to_u64().unwrap();
        for y in &mut v { *y = mul(*y, inv, p); }
    }
    Ok(Some(v.into_iter().map(Integer::from_u64).collect()))
}

fn integer_vector(it: &mut Interp, entries: &[Integer]) -> RResult<Value> {
    let integers = Value::integers();
    let zctx = crate::intrinsics::matrices::entry_ctx(it, &integers)?;
    let mut out = Mat::zero(&zctx, 1, entries.len());
    for (j, z) in entries.iter().enumerate() {
        out.set_integer(0, j, z).map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?;
    }
    crate::intrinsics::matrices::vec_value(it, &integers, out)
}

fn modular_solution(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    if !matches!(a.param("Lanczos"), Some(Value::Bool(_))) {
        return Err(RuntimeError::runtime("Bad type for parameter 'Lanczos'"));
    }
    let x = sparse_arg(a, 0)?;
    if !matches!(x.info().ctx.kind(), CtxKind::Integers) {
        return Err(RuntimeError::runtime("Argument 1 must be defined over the integers"));
    }
    let m = modulus(&a.args[1])?;
    if x.nrows.checked_mul(x.ncols).is_some_and(|z| z > 512 * 512) {
        if let Some(p) = m.to_u64().filter(|_| m.is_prime()) {
            if let Some(v) = prime_solution(&x, p)? {
                return one(integer_vector(it, &v)?);
            }
        }
    }
    let ring = it.call_intrinsic_named(Sym::new("Integers"), vec![Value::Int(m.clone())])?;
    let ctx = crate::intrinsics::matrices::entry_ctx(it, &ring)?;
    let mut t = Mat::zero(&ctx, x.ncols, x.nrows);
    for i in 0..x.nrows {
        for (j, e) in x.row_elems(i)? {
            let z = e.to_integer().map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?;
            t.set_integer(j, i, &z).map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?;
        }
    }
    let dense = crate::intrinsics::matrices::mat_value(it, &ring, t)?;
    let Value::Mat(k) = it.call_intrinsic_named(Sym::new("KernelMatrix"), vec![dense])? else { unreachable!("a kernel matrix") };
    let row = (0..k.m.nrows()).find(|&i| (0..k.m.ncols()).any(|j| !k.m.entry_is_zero(i, j)));
    let mut v = row.map_or_else(|| Mat::zero(&ctx, 1, x.ncols), |i| k.m.block(i, 0, 1, x.ncols));
    if x.ncols != 0 {
        let first = v.entry(0, 0).to_integer().map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?;
        if let Some(inv) = first.invmod(&m) {
            let e = calyx_flint::gr::Elem::from_integer(&ctx, &inv).map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?;
            v = v.scalar_mul(&e).map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?;
        }
    }
    let entries: Vec<Integer> = (0..x.ncols).map(|j| v.entry(0, j).to_integer().map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))).collect::<RResult<_>>()?;
    one(integer_vector(it, &entries)?)
}

pub(super) fn register(it: &mut Interp) {
    let params = [("Lanczos", Value::Bool(false))];
    it.def_params("ModularSolution", "A::MtrxSprs, M::RngIntElt -> ModTupRngElt", &params, "A nonzero vector v with v*Transpose(A) zero modulo M.", modular_solution);
    it.def_params("ModularSolution", "A::MtrxSprs, L::RngIntEltFact -> ModTupRngElt", &params, "A nonzero vector v with v*Transpose(A) zero modulo the product L.", modular_solution);
}
