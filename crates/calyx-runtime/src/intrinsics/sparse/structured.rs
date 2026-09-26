//! Structured Gaussian elimination for machine-word prime fields.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use calyx_flint::gr::Truth;
use calyx_flint::mat::Mat;
use calyx_flint::Integer;
use rustc_hash::{FxHashMap, FxHashSet};

use super::{Rows, SparseMatrix};

pub(super) struct WordReduction {
    pub pivots: usize,
    pub factor: u64,
    pub negative: bool,
    pub remainder: Mat,
}

pub(super) struct IntegerReduction {
    pub pivots: usize,
    pub factor: Integer,
    pub negative: bool,
    pub remainder: Mat,
}

struct Fenwick(Vec<usize>);

impl Fenwick {
    fn full(n: usize) -> Fenwick {
        let mut v = vec![0; n + 1];
        for i in 1..=n { v[i] = i & i.wrapping_neg(); }
        Fenwick(v)
    }

    fn before(&self, mut i: usize) -> usize {
        let mut n = 0;
        while i != 0 { n += self.0[i]; i &= i - 1; }
        n
    }

    fn remove(&mut self, i: usize) {
        let mut j = i + 1;
        while j < self.0.len() { self.0[j] -= 1; j += j & j.wrapping_neg(); }
    }
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

/// Peel low-weight rows and columns until the remainder is small enough for
/// FLINT or has become dense.  Choosing the lightest row and then its
/// lightest column is the minimum-degree form of Markowitz pivoting.
pub(super) fn word_reduce(a: &SparseMatrix) -> Option<WordReduction> {
    let Rows::Words(source) = &a.rows else { return None };
    let p = match a.info().ctx.kind() {
        calyx_flint::gr::CtxKind::Nmod(p) if a.info().ctx.is_field() == Truth::True => *p,
        _ => return None,
    };
    let area = a.nrows.checked_mul(a.ncols)?;
    if area <= 512 * 512 { return None; }
    let mut rows: Vec<FxHashMap<usize, u64>> = source.iter().map(|row| row.iter().copied().collect()).collect();
    let mut cols: Vec<FxHashSet<usize>> = vec![FxHashSet::default(); a.ncols];
    for (i, row) in rows.iter().enumerate() { for &j in row.keys() { cols[j].insert(i); } }
    let mut active = vec![true; a.nrows];
    let mut versions = vec![0u64; a.nrows];
    let mut heap: BinaryHeap<Reverse<(usize, u64, usize)>> = BinaryHeap::new();
    for (i, row) in rows.iter().enumerate() { heap.push(Reverse((row.len(), 0, i))); }
    let (mut nr, mut nc, mut nnz) = (a.nrows, a.ncols, a.nnz());
    let (mut pivots, mut factor, mut negative) = (0, 1, false);
    let (mut row_order, mut col_order) = (Fenwick::full(a.nrows), Fenwick::full(a.ncols));
    while nr != 0 && nc != 0 {
        let dense = nr.checked_mul(nc).is_some_and(|z| z <= 512 * 512 || nnz.saturating_mul(8) >= z);
        if dense { break; }
        let r = loop {
            let Reverse((len, version, i)) = heap.pop()?;
            if active[i] && versions[i] == version && rows[i].len() == len { break i; }
        };
        if rows[r].is_empty() {
            active[r] = false;
            row_order.remove(r);
            nr -= 1;
            continue;
        }
        let c = *rows[r].keys().min_by_key(|&&j| (cols[j].len(), j)).unwrap();
        if (row_order.before(r) + col_order.before(c)) & 1 != 0 { negative = !negative; }
        row_order.remove(r);
        col_order.remove(c);
        let pivot = rows[r][&c];
        factor = mul(factor, pivot, p);
        let inverse = pow(pivot, p - 2, p);
        let pivot_row: Vec<(usize, u64)> = rows[r].iter().map(|(&j, &x)| (j, x)).collect();
        let targets: Vec<usize> = cols[c].iter().copied().filter(|&i| i != r).collect();
        for &j in rows[r].keys() { cols[j].remove(&r); }
        nnz -= rows[r].len();
        rows[r].clear();
        active[r] = false;
        nr -= 1;
        nc -= 1;
        pivots += 1;
        for i in targets {
            let q = mul(rows[i][&c], inverse, p);
            for &(j, x) in &pivot_row {
                let old = rows[i].get(&j).copied().unwrap_or(0);
                let y = mul(q, x, p);
                let new = if old >= y { old - y } else { p - (y - old) };
                match (old == 0, new == 0) {
                    (true, false) => { rows[i].insert(j, new); cols[j].insert(i); nnz += 1; }
                    (false, true) => { rows[i].remove(&j); cols[j].remove(&i); nnz -= 1; }
                    (false, false) => { rows[i].insert(j, new); }
                    (true, true) => {}
                }
            }
            versions[i] += 1;
            heap.push(Reverse((rows[i].len(), versions[i], i)));
        }
        cols[c].clear();
    }
    let ris: Vec<usize> = (0..a.nrows).filter(|&i| active[i] && !rows[i].is_empty()).collect();
    let cis: Vec<usize> = (0..a.ncols).filter(|&j| !cols[j].is_empty()).collect();
    let positions: FxHashMap<usize, usize> = cis.iter().enumerate().map(|(j, &c)| (c, j)).collect();
    let mut remainder = Mat::zero(&a.info().ctx, ris.len(), cis.len());
    for (i, &r) in ris.iter().enumerate() {
        for (&c, &x) in &rows[r] {
            if let Some(&j) = positions.get(&c) { remainder.set_word(i, j, x); }
        }
    }
    Some(WordReduction { pivots, factor, negative, remainder })
}

fn unit_entries(row: &FxHashMap<usize, Integer>) -> usize {
    row.values().filter(|x| x.abs().is_one()).count()
}

/// The same reduction over Z, using unit pivots.  It is exact and is
/// especially effective on relation matrices whose structural rows contain
/// coefficients 1 or -1; a non-unit core is left to FLINT.
pub(super) fn integer_reduce(a: &SparseMatrix) -> Option<IntegerReduction> {
    let Rows::Integers(source) = &a.rows else { return None };
    let area = a.nrows.checked_mul(a.ncols)?;
    if area <= 512 * 512 { return None; }
    let mut rows: Vec<FxHashMap<usize, Integer>> = source.iter().map(|row| row.iter().cloned().collect()).collect();
    let mut cols: Vec<FxHashSet<usize>> = vec![FxHashSet::default(); a.ncols];
    for (i, row) in rows.iter().enumerate() { for &j in row.keys() { cols[j].insert(i); } }
    let mut active = vec![true; a.nrows];
    let mut versions = vec![0u64; a.nrows];
    let mut heap: BinaryHeap<Reverse<(usize, u64, usize)>> = BinaryHeap::new();
    for (i, row) in rows.iter().enumerate() {
        if unit_entries(row) != 0 { heap.push(Reverse((row.len(), 0, i))); }
    }
    let (mut nr, mut nc, mut nnz) = (a.nrows, a.ncols, a.nnz());
    let (mut pivots, factor, mut negative) = (0, Integer::one(), false);
    let (mut row_order, mut col_order) = (Fenwick::full(a.nrows), Fenwick::full(a.ncols));
    while nr != 0 && nc != 0 {
        let dense = nr.checked_mul(nc).is_some_and(|z| z <= 64 * 64 || nnz.saturating_mul(8) >= z);
        if dense { break; }
        let Some(r) = (loop {
            let Some(Reverse((len, version, i))) = heap.pop() else { break None };
            if active[i] && versions[i] == version && rows[i].len() == len && unit_entries(&rows[i]) != 0 { break Some(i); }
        }) else { break };
        let c = rows[r].iter().filter(|(_, x)| x.abs().is_one()).map(|(&j, _)| j).min_by_key(|&j| (cols[j].len(), j)).unwrap();
        if (row_order.before(r) + col_order.before(c)) & 1 != 0 { negative = !negative; }
        row_order.remove(r);
        col_order.remove(c);
        let pivot = rows[r][&c].clone();
        if pivot.sign() < 0 { negative = !negative; }
        let pivot_row: Vec<(usize, Integer)> = rows[r].iter().map(|(&j, x)| (j, x.clone())).collect();
        let targets: Vec<usize> = cols[c].iter().copied().filter(|&i| i != r).collect();
        for &j in rows[r].keys() { cols[j].remove(&r); }
        nnz -= rows[r].len();
        rows[r].clear();
        active[r] = false;
        nr -= 1;
        nc -= 1;
        pivots += 1;
        for i in targets {
            let mut q = rows[i][&c].clone();
            if pivot.sign() < 0 { q.neg_assign(); }
            for (j, x) in &pivot_row {
                let old = rows[i].get(j).cloned().unwrap_or_default();
                let new = &old - &(&q * x);
                match (old.is_zero(), new.is_zero()) {
                    (true, false) => { rows[i].insert(*j, new); cols[*j].insert(i); nnz += 1; }
                    (false, true) => { rows[i].remove(j); cols[*j].remove(&i); nnz -= 1; }
                    (false, false) => { rows[i].insert(*j, new); }
                    (true, true) => {}
                }
            }
            versions[i] += 1;
            if unit_entries(&rows[i]) != 0 { heap.push(Reverse((rows[i].len(), versions[i], i))); }
        }
        cols[c].clear();
    }
    let ris: Vec<usize> = (0..a.nrows).filter(|&i| active[i] && !rows[i].is_empty()).collect();
    let cis: Vec<usize> = (0..a.ncols).filter(|&j| !cols[j].is_empty()).collect();
    let positions: FxHashMap<usize, usize> = cis.iter().enumerate().map(|(j, &c)| (c, j)).collect();
    let mut remainder = Mat::zero(&a.info().ctx, ris.len(), cis.len());
    for (i, &r) in ris.iter().enumerate() {
        for (&c, x) in &rows[r] {
            if let Some(&j) = positions.get(&c) { remainder.set_integer(i, j, x).expect("an integer context"); }
        }
    }
    Some(IntegerReduction { pivots, factor, negative, remainder })
}
