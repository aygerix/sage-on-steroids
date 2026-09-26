//! Properties of lattices (text/333): the ambient and coordinate spaces,
//! the rank, degree, content, level and determinant, the Gram, basis and
//! inner product matrices, the quadratic form, and the predicates.

use std::rc::Rc;

use calyx_flint::gr::{Ctx, Elem, Truth};
use calyx_flint::mat::Mat;
use calyx_flint::{Integer, Rational};
use calyx_groebner::Order;

use super::{as_elt, elt, integral, lat, num_den, rational, row_of, to_q};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::matrices::{self, Shape};
use crate::intrinsics::{boolv, intv, one};
use crate::value::*;

fn lattice_arg(a: &CallArgs) -> Rc<Struct> {
    match &a.args[0] {
        Value::Struct(st) => st.clone(),
        _ => unreachable!("a lattice"),
    }
}

/// The map from a lattice to a vector space over Q: its embedding in its
/// ambient space, or (`coords`) the coordinates of its elements.
struct ToSpace {
    coords: bool,
}

impl NativeMap for ToSpace {
    fn apply(&self, _it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let Value::Struct(space) = &m.codomain else { unreachable!("a vector space") };
        let v = match (x, &m.domain) {
            (Value::Ext(e), Value::Struct(st)) if Rc::ptr_eq(&e.parent, st) => e,
            _ => return Err(RuntimeError::runtime("Element is not in the domain of the map").in_context("map application")),
        };
        let row = if self.coords {
            let c = lat(&v.parent).coordinates(row_of(v)).expect("an element of the lattice");
            let mut r = Mat::zero(&Ctx::rationals(), 1, c.len());
            for (j, x) in c.iter().enumerate() {
                r.set_integer(0, j, x)?;
            }
            r
        } else {
            to_q(row_of(v))
        };
        Ok(Value::Mat(Rc::new(matrices::Mtrx { parent: space.clone(), m: row })))
    }

    /// The map has no inverse; Magma's error names the domain.
    fn preimage(&self, _it: &mut Interp, _m: &MapObj, _y: &Value) -> RResult<Value> {
        Err(RuntimeError::runtime("Element is not in the domain of the map").in_context("@@"))
    }

    fn rule(&self) -> bool {
        true
    }
}

/// The vector space over Q with the inner product matrix `f`, and the map
/// to it from the lattice argument.
fn space_and_map(it: &mut Interp, a: &CallArgs, f: &Mat, coords: bool) -> RResult<Vals> {
    let st = lattice_arg(a);
    let v = Value::Struct(matrices::form_space(it, &Value::rationals(), to_q(f))?);
    let map = MapObj { kind: MapKind::Map, domain: Value::Struct(st), codomain: v.clone(), imp: MapImpl::Native(Rc::new(ToSpace { coords })) };
    Ok(vals![v, Value::Map(Rc::new(map))])
}

/// `AmbientSpace(L)`: the vector space over Q of the degree of L with its
/// inner product matrix, and the embedding.
fn ambient_space(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let ip = lat(&lattice_arg(a)).ip.clone();
    space_and_map(it, a, &ip, false)
}

/// `CoordinateSpace(L)`: the vector space over Q of the rank of L with
/// the Gram matrix of L as its inner product matrix, and the map taking
/// the elements of L to their coordinates.
fn coordinate_space(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let g = lat(&lattice_arg(a)).gram().clone();
    space_and_map(it, a, &g, true)
}

fn rank(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(lat(&lattice_arg(a)).rank() as u64))
}

fn degree(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(lat(&lattice_arg(a)).degree() as u64))
}

/// A rational as an element of the base ring `ring`.
fn in_ring(ring: &Value, q: Rational) -> Value {
    if ring.is_integers() { Value::Int(q.numerator()) } else { Value::rat(q) }
}

/// The largest c with all inner products in cZ: the gcd of the entries of
/// the Gram matrix.
fn content(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = lattice_arg(a);
    let l = lat(&st);
    let (n, d) = num_den(l.gram());
    one(in_ring(&l.ring, Rational::new(&n.content(), &d).expect("a denominator")))
}

/// The least k with k (v, v) in 2Z for every v in the dual lattice: the
/// least k with k F^-1 integral and even on the diagonal, F being the Gram
/// matrix.
fn level(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = lattice_arg(a);
    let l = lat(&st);
    if !integral(l.gram()) {
        return Err(crate::intrinsics::bare(RuntimeError::runtime("The lattice must be integral")));
    }
    let m = l.rank();
    if m == 0 {
        return intv(Integer::one());
    }
    let inv = to_q(l.gram()).inv()?;
    let half = Rational::new(&Integer::one(), &Integer::from_u64(2)).expect("1/2");
    let mut k = Integer::one();
    for i in 0..m {
        for j in 0..=i {
            let x = rational(&inv, i, j);
            let x = if i == j { &x * &half } else { x };
            k = k.lcm(&x.denominator());
        }
    }
    intv(k)
}

fn determinant(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = lattice_arg(a);
    let l = lat(&st);
    let d = if l.rank() == 0 { Rational::one() } else { to_q(l.gram()).det()?.to_rational()? };
    one(in_ring(&l.ring, d))
}

fn gram_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = lattice_arg(a);
    let l = lat(&st);
    let ring = l.ring.clone();
    one(matrices::mat_value(it, &ring, l.gram().clone())?)
}

/// `GramMatrix(S)`: the inner products of the elements of S, lattice
/// elements of compatible lattices; halved with `Half`.
fn gram_of_elements(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.seq(0)?;
    let elts: Vec<&crate::ext::ExtElt> = s.elems.iter().map(|v| as_elt(v).ok_or_else(|| RuntimeError::runtime("Bad argument types"))).collect::<RResult<_>>()?;
    let Some(first) = elts.first() else { return Err(RuntimeError::runtime("Argument 1 must be non-empty")) };
    let l = lat(&first.parent);
    if elts.iter().any(|x| !Rc::ptr_eq(&x.parent, &first.parent) && !lat(&x.parent).compatible(l)) {
        return Err(RuntimeError::runtime("Arguments are not compatible"));
    }
    let mut rows = Mat::zero(l.ctx(), 0, l.degree());
    for x in &elts {
        rows = rows.concat_vertical(row_of(x));
    }
    let mut g = to_q(&rows.mul(&l.ip)?.mul(&rows.transpose())?);
    if a.param_bool("Half")? {
        g = g.mul_scalar(&Elem::from_rational(&Ctx::rationals(), &Rational::new(&Integer::one(), &Integer::from_u64(2)).expect("1/2"))?)?;
    }
    let ring = if l.ring.is_integers() && integral(&g) { Value::integers() } else { Value::rationals() };
    let g = g.change_ring(&if ring.is_integers() { Ctx::integers() } else { Ctx::rationals() })?;
    one(matrices::mat_value(it, &ring, g)?)
}

/// `GramMatrix(X)`: X Xᵀ.
fn gram_of_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Mat(x) = &a.args[0] else { unreachable!("a matrix") };
    let ring = x.ring().clone();
    let g = x.m.mul(&x.m.transpose())?;
    one(matrices::mat_value(it, &ring, g)?)
}

fn inner_product_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = lattice_arg(a);
    let l = lat(&st);
    let ring = l.ring.clone();
    one(matrices::mat_value(it, &ring, l.ip.clone())?)
}

fn basis(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = lattice_arg(a);
    let l = lat(&st);
    let elems = (0..l.rank()).map(|i| elt(&st, l.basis.block(i, 0, 1, l.degree()))).collect();
    one(Value::seq(Some(Value::Struct(st.clone())), elems))
}

/// The basis matrix, in the matrix space even when it is square.
fn basis_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = lattice_arg(a);
    let l = lat(&st);
    let parent = matrices::parent(it, &l.ring, l.rank(), l.degree(), Shape::Space)?;
    one(Value::Mat(Rc::new(matrices::Mtrx { parent, m: l.basis.clone() })))
}

fn basis_denominator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(num_den(&lat(&lattice_arg(a)).basis).1)
}

/// The quadratic form x F xᵀ of the Gram matrix F, in a new polynomial
/// ring over the base ring with the variables x1, x2, ...
fn quadratic_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = lattice_arg(a);
    let l = lat(&st);
    let m = l.rank();
    let r = it.mpoly_ring(&l.ring, m, Order::Lex, None, false)?;
    let Some(StructKind::Ring(rr)) = r.as_struct() else { unreachable!("a polynomial ring") };
    *rr.names.borrow_mut() = (1..=m).map(|i| Rc::from(format!("x{i}").as_str())).collect();
    let g = l.gram();
    let two = Elem::from_integer(l.ctx(), &Integer::from_u64(2))?;
    let mut terms = Vec::new();
    for i in 0..m {
        for j in i..m {
            let c = if i == j { g.entry(i, i) } else { g.entry(i, j).mul(&two)? };
            if c.is_zero() == Truth::True {
                continue;
            }
            let mut e = vec![0u64; m];
            e[i] += 1;
            e[j] += 1;
            terms.push((c, e));
        }
    }
    let f = Elem::mpoly_from_terms(&rr.ctx, &terms)?;
    one(it.elem_to_value(&r, f))
}

fn is_zero(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(lat(&lattice_arg(a)).rank() == 0)
}

fn is_full(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = lattice_arg(a);
    let l = lat(&st);
    boolv(l.rank() == l.degree())
}

fn yes(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    boolv(true)
}

fn no(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    boolv(false)
}

fn is_integral(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(integral(lat(&lattice_arg(a)).gram()))
}

/// Integral, with even norms: an integral Gram matrix with an even
/// diagonal.
fn is_even(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = lattice_arg(a);
    let l = lat(&st);
    let g = l.gram();
    boolv(integral(g) && (0..l.rank()).all(|i| !rational(g, i, i).numerator().is_odd()))
}

fn base_ring(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(lat(&lattice_arg(a)).ring.clone())
}

fn coordinate_ring(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::integers())
}

pub fn register(it: &mut Interp) {
    let doc = "The vector space over Q in which L embeds, and the embedding.";
    it.def("AmbientSpace", "L::Lat -> ModTupFld, Map", doc, ambient_space);
    let doc = "The vector space over Q of the coordinates of L, with the Gram matrix of L, and the map to it.";
    it.def("CoordinateSpace", "L::Lat -> ModTupFld, Map", doc, coordinate_space);
    for name in ["Rank", "Dimension"] {
        it.def(name, "L::Lat -> RngIntElt", "The rank of L, the number of its basis vectors.", rank);
    }
    it.def("Degree", "L::Lat -> RngIntElt", "The degree of L, the length of its vectors.", degree);
    it.def("Content", "L::Lat -> RngElt", "The largest rational c with all inner products in L in cZ.", content);
    it.def("Level", "L::Lat -> RngElt", "The least k with k (v, v) in 2Z for all v in the dual of L.", level);
    it.def("Determinant", "L::Lat -> RngElt", "The determinant of the Gram matrix of L.", determinant);
    it.def("GramMatrix", "L::Lat -> AlgMatElt", "The inner products of the basis vectors of L.", gram_matrix);
    it.def_params("GramMatrix", "S::[LatElt] -> AlgMatElt", &[("Half", Value::Bool(false))], "The inner products of the elements of S.", gram_of_elements);
    it.def("GramMatrix", "X::Mtrx -> AlgMatElt", "X times its transpose.", gram_of_matrix);
    it.def("InnerProductMatrix", "L::Lat -> AlgMatElt", "The inner product matrix of L.", inner_product_matrix);
    it.def("Basis", "L::Lat -> SeqEnum", "The basis vectors of L.", basis);
    it.def("BasisMatrix", "L::Lat -> Mtrx", "The basis vectors of L as the rows of a matrix.", basis_matrix);
    it.def("BasisDenominator", "L::Lat -> RngIntElt", "The least common denominator of the basis vectors of L.", basis_denominator);
    it.def("QuadraticForm", "L::Lat -> RngMPolElt", "The quadratic form of L, from its Gram matrix.", quadratic_form);
    it.def("IsZero", "L::Lat -> BoolElt", "Whether L has rank 0.", is_zero);
    it.def("IsFull", "L::Lat -> BoolElt", "Whether the rank of L is its degree.", is_full);
    it.def("IsHermitian", "L::Lat -> BoolElt", "False: lattices are not Hermitian.", no);
    it.def("IsQuadratic", "L::Lat -> BoolElt", "True: lattices are quadratic.", yes);
    it.def("IsExact", "L::Lat -> BoolElt", "True: lattices over Z and Q are exact.", yes);
    it.def("IsIntegral", "L::Lat -> BoolElt", "Whether all inner products in L are integers.", is_integral);
    it.def("IsEven", "L::Lat -> BoolElt", "Whether L is integral with even norms.", is_even);
    for name in ["BaseRing", "CoefficientRing"] {
        it.def(name, "L::Lat -> Rng", "The ring the basis and inner product matrix of L are over, Z or Q.", base_ring);
    }
    for name in ["CoordinateRing", "Order"] {
        it.def(name, "L::Lat -> RngInt", "The ring of coordinates of L, Z.", coordinate_ring);
    }
}

