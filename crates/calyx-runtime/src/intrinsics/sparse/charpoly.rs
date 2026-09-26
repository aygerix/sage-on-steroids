//! Polynomial invariants, eigenvalues and elementary divisors (text/299).

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::Elem;

use super::linalg::dense_call;
use super::sparse_arg;
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn dense(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    dense_call(it, a, a.nresults)
}

fn add_row(a: &mut [Vec<Integer>], dst: usize, src: usize, q: &Integer) {
    let row = a[src].clone();
    for (x, y) in a[dst].iter_mut().zip(row) {
        *x = &*x + &(q * &y);
    }
}

fn add_col(a: &mut [Vec<Integer>], dst: usize, src: usize, q: &Integer) {
    let col: Vec<Integer> = a.iter().map(|row| row[src].clone()).collect();
    for (row, y) in a.iter_mut().zip(col) {
        row[dst] = &row[dst] + &(q * &y);
    }
}

/// The nonzero Smith diagonal over Z.  At step k, Euclidean row and column
/// operations make the pivot divide the whole trailing block, so later
/// pivots are automatically its multiples.
fn integer_divisors(mut a: Vec<Vec<Integer>>, ncols: usize) -> Vec<Integer> {
    let lim = a.len().min(ncols);
    let mut out = Vec::new();
    for k in 0..lim {
        let mut pos = None;
        for i in k..a.len() {
            for j in k..ncols {
                if !a[i][j].is_zero() && pos.as_ref().is_none_or(|(_, _, z): &(usize, usize, Integer)| a[i][j].abs() < *z) {
                    pos = Some((i, j, a[i][j].abs()));
                }
            }
        }
        let Some((i, j, _)) = pos else { break };
        a.swap(k, i);
        for row in &mut a { row.swap(k, j); }
        loop {
            let mut changed = false;
            for i in k + 1..a.len() {
                if a[i][k].is_zero() { continue; }
                let q = a[i][k].fdiv_qr(&a[k][k]).expect("a nonzero pivot").0;
                add_row(&mut a, i, k, &-q);
                if !a[i][k].is_zero() {
                    a.swap(i, k);
                }
                changed = true;
                break;
            }
            if changed { continue; }
            for j in k + 1..ncols {
                if a[k][j].is_zero() { continue; }
                let q = a[k][j].fdiv_qr(&a[k][k]).expect("a nonzero pivot").0;
                add_col(&mut a, j, k, &-q);
                if !a[k][j].is_zero() {
                    for row in &mut a { row.swap(j, k); }
                }
                changed = true;
                break;
            }
            if changed { continue; }
            let bad = (k + 1..a.len()).find_map(|i| {
                (k + 1..ncols).find(|&j| !a[i][j].fdiv_qr(&a[k][k]).expect("a nonzero pivot").1.is_zero()).map(|j| (i, j))
            });
            let Some((i, j)) = bad else { break };
            add_row(&mut a, k, i, &Integer::one());
            for row in &mut a { row.swap(k, j); }
        }
        if a[k][k].sign() < 0 {
            add_row(&mut a, k, k, &Integer::from_i64(-2));
        }
        out.push(a[k][k].clone());
    }
    out
}

fn elementary_divisors(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = sparse_arg(a, 0)?;
    let ring = x.ring().clone();
    let elems = if it.types.isa(ring.type_id(), crate::types::t::FLD) {
        let dense = crate::intrinsics::matrices::mat_value(it, &ring, x.dense())?;
        let Value::Mat(m) = dense else { unreachable!() };
        let one = Elem::one(&x.info().ctx).map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?;
        vec![it.elem_to_value(&ring, one); crate::intrinsics::matrices::rank_of(&m)?]
    } else if matches!(ring.as_struct(), Some(StructKind::Integers)) {
        let m = x.dense();
        let rows: Vec<Vec<Integer>> = (0..x.nrows).map(|i| (0..x.ncols).map(|j| m.integer(i, j)).collect()).collect();
        integer_divisors(rows, x.ncols).into_iter().map(Value::Int).collect()
    } else {
        return Err(RuntimeError::runtime("Coefficient ring must be a Euclidean ring or field"));
    };
    Ok(vals![Value::seq(Some(ring), elems)])
}

pub(super) fn register(it: &mut Interp) {
    let charpoly = [("Al", Value::str("Modular")), ("Proof", Value::Bool(true))];
    let minpoly = [("Al", Value::str("Default")), ("Proof", Value::Bool(true))];
    let proof = [("Proof", Value::Bool(true))];
    it.def_params("CharacteristicPolynomial", "A::MtrxSprs -> RngUPolElt", &charpoly, "The characteristic polynomial of A.", dense);
    it.def_params("MinimalPolynomial", "A::MtrxSprs -> RngUPolElt", &minpoly, "The minimal polynomial of A.", dense);
    for name in ["MinimalAndCharacteristicPolynomials", "MCPolynomials"] {
        it.def_params(name, "A::MtrxSprs -> RngUPolElt, RngUPolElt", &proof, "The minimal and characteristic polynomials of A.", dense);
    }
    it.def_params("FactoredCharacteristicPolynomial", "A::MtrxSprs -> [Tup]", &charpoly, "The factorization of the characteristic polynomial of A.", dense);
    it.def_params("FactoredMinimalPolynomial", "A::MtrxSprs -> [Tup]", &proof, "The factorization of the minimal polynomial of A.", dense);
    for name in ["FactoredMinimalAndCharacteristicPolynomials", "FactoredMCPolynomials"] {
        it.def_params(name, "A::MtrxSprs -> [Tup], [Tup]", &proof, "The factorizations of the minimal and characteristic polynomials of A.", dense);
    }
    it.def("Eigenvalues", "A::MtrxSprs -> SetEnum", "The eigenvalues of A with their multiplicities.", dense);
    it.def("Eigenspace", "A::MtrxSprs, e::RngElt -> ModTupRng", "The eigenspace of A for e.", dense);
    it.def("ElementaryDivisors", "A::MtrxSprs -> [RngElt]", "The nonzero diagonal entries of the Smith form of A.", elementary_divisors);
    it.verbose.insert(Rc::from("SparseMatrix"), (0, 3));
}
