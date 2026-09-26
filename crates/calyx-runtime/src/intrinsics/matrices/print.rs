//! Printing matrices, vectors and their parents.
//!
//! Magma prints a matrix one row per line, in brackets (a vector in
//! parentheses), with the entries right-aligned to a common width: that of
//! the widest entry, or over a prime field below 2^30 or a field with Zech
//! logarithms, that of the widest element of the field. Over polynomial
//! rings with such coefficients, the constant term of an entry counts as
//! padded to that width too. When a row does not fit on a line that way,
//! and over the real and complex fields, the entries are not aligned (three
//! spaces apart over polynomial rings), and long rows continue on further
//! indented lines.

use calyx_flint::gr::{CtxKind, Truth};

use calyx_flint::mat::Mat;

use super::{Mtrx, Shape, entry_of, entry_value, info};
use crate::error::RResult;
use crate::interp::Interp;
use crate::print::{Level, Printer};
use crate::rings::small::SmallKind;
use crate::value::*;

/// `Matrix with 0 rows and 6 columns`.
fn empty_text(r: usize, c: usize) -> String {
    let s = |n: usize| if n == 1 { "" } else { "s" };
    format!("Matrix with {r} row{} and {c} column{}", s(r), s(c))
}

/// The width of the widest element of a finite field whose elements are
/// all padded to it: a prime field below 2^30, or a field with Zech
/// logarithms.
fn field_width(it: &mut Interp, ring: &Value, level: Level) -> RResult<Option<usize>> {
    let Some(StructKind::Ring(r)) = ring.as_struct() else { return Ok(None) };
    let Some(s) = r.small else { return Ok(None) };
    let info = s.info();
    let widest = match info.kind {
        SmallKind::PrimeField if info.m.modulus() < 1 << 30 => info.m.modulus() - 1,
        SmallKind::Zech(z) => z.zero() - 1,
        _ => return Ok(None),
    };
    Ok(Some(it.format_flat(&Value::Small(s, widest), level)?.chars().count()))
}

/// The width of the widest entry of `m`, a matrix over a polynomial ring
/// whose coefficients are padded (see `field_width`), with the constant term
/// of each entry counted as padded; 0 over other rings.
fn padded_poly_width(it: &mut Interp, ring: &Value, m: &Mat, texts: &[String], level: Level) -> RResult<usize> {
    let Some(StructKind::Ring(r)) = ring.as_struct() else { return Ok(0) };
    let Some(base) = r.base().cloned() else { return Ok(0) };
    let poly = match m.ctx().kind() {
        CtxKind::Poly => true,
        CtxKind::MPoly { .. } => false,
        _ => return Ok(0),
    };
    let Some(fw) = field_width(it, &base, level)? else { return Ok(0) };
    let mut w = 0;
    for (k, s) in texts.iter().enumerate() {
        let e = m.entry(k / m.ncols(), k % m.ncols());
        let c = if poly {
            if e.poly_len() == 0 {
                continue;
            }
            e.poly_coeff(0)
        } else {
            // The constant term is the last.
            match e.mpoly_len().checked_sub(1).map(|n| e.mpoly_term(n)) {
                Some((c, exps)) if exps.iter().all(|&x| x == 0) => c,
                _ => continue,
            }
        };
        if c.is_zero() == Truth::True {
            continue;
        }
        let t = it.format_flat(&it.elem_to_value(&base, c), level)?;
        w = w.max(s.chars().count() + fw.saturating_sub(t.chars().count()));
    }
    Ok(w)
}

/// The entries of `m`, a matrix over `ring`, as text, row after row.
fn entry_texts(it: &mut Interp, ring: &Value, m: &Mat, level: Level) -> RResult<Vec<String>> {
    let (r, c) = (m.nrows(), m.ncols());
    let mut out = Vec::with_capacity(r * c);
    for i in 0..r {
        for j in 0..c {
            let s = match m.ctx().kind() {
                CtxKind::Integers if level != Level::Hex => m.integer(i, j).to_string(),
                _ => {
                    let v = entry_of(it, ring, m, i, j);
                    it.format_flat(&v, level)?
                }
            };
            out.push(s);
        }
    }
    Ok(out)
}

pub fn fmt_matrix(it: &mut Interp, p: &mut Printer, a: &Mtrx, indent: usize) -> RResult<()> {
    let (r, c) = (a.m.nrows(), a.m.ncols());
    if p.level == Level::Magma {
        return fmt_magma(it, p, a, indent);
    }
    if r == 0 || c == 0 {
        p.write(&empty_text(r, c));
        return Ok(());
    }
    let ring = a.ring().clone();
    fmt_rows(it, p, &ring, &a.m, a.is_vector(), indent)
}

/// The rows of `m`, a matrix over `ring` with at least one entry, one per
/// line: in brackets, or in parentheses as vectors.
fn fmt_rows(it: &mut Interp, p: &mut Printer, ring: &Value, m: &Mat, vectors: bool, indent: usize) -> RResult<()> {
    let (r, c) = (m.nrows(), m.ncols());
    let level = if p.level == Level::Hex { Level::Hex } else { Level::Default };
    let texts = entry_texts(it, ring, m, level)?;
    let unaligned = matches!(m.ctx().kind(), CtxKind::RealFloat(_) | CtxKind::ComplexFloat(_));
    let mut w = texts.iter().map(|s| s.chars().count()).max().unwrap_or(0);
    if let Some(fw) = field_width(it, ring, level)? {
        w = w.max(fw);
    }
    w = w.max(padded_poly_width(it, ring, m, &texts, level)?);
    let aligned = !unaligned && 2 + c * w + (c - 1) < p.width;
    let sep = if !aligned && matches!(m.ctx().kind(), CtxKind::Poly | CtxKind::MPoly { .. }) { "   " } else { " " };
    let (open, close) = if vectors { ('(', ')') } else { ('[', ']') };
    let saved = p.cont;
    p.cont = if aligned { indent } else { indent + 4 };
    for i in 0..r {
        if i > 0 {
            p.newline(indent);
        }
        let mut row = String::with_capacity(2 + c * (w + 1));
        row.push(open);
        for (j, s) in texts[i * c..(i + 1) * c].iter().enumerate() {
            if j > 0 {
                row.push_str(sep);
            }
            if aligned {
                for _ in s.chars().count()..w {
                    row.push(' ');
                }
            }
            row.push_str(s);
        }
        row.push(close);
        p.text(&row);
    }
    p.cont = saved;
    Ok(())
}

/// A matrix at the Magma level: its parent applied to its entries.
fn fmt_magma(it: &mut Interp, p: &mut Printer, a: &Mtrx, indent: usize) -> RResult<()> {
    let (r, c) = (a.m.nrows(), a.m.ncols());
    let parent = Value::Struct(a.parent.clone());
    it.fmt(p, &parent, indent)?;
    p.write(" ! ");
    let mut elems = Vec::with_capacity(r * c);
    for i in 0..r {
        for j in 0..c {
            elems.push(entry_value(it, a, i, j));
        }
    }
    // Entries of residue rings and prime fields show as integers.
    let ints = elems.iter().all(|v| matches!(v, Value::Int(_) | Value::Small(..)) && !matches!(v, Value::Small(s, _) if s.zech().is_some()));
    let seq = if ints {
        Value::int_seq(elems.iter().map(|v| match v {
            Value::Int(n) => n.clone(),
            Value::Small(_, w) => calyx_flint::Integer::from_u64(*w),
            _ => unreachable!(),
        }))
    } else {
        Value::seq(Some(a.ring().clone()), elems)
    };
    let shape = info(&a.parent).shape;
    if shape == Shape::Space {
        let ring = a.ring().clone();
        p.write("Matrix(");
        it.fmt(p, &ring, indent)?;
        p.write(&format!(", {r}, {c}, "));
        it.fmt(p, &seq, indent)?;
        p.write(")");
    } else {
        it.fmt(p, &seq, indent)?;
    }
    Ok(())
}

/// A full matrix algebra, matrix space or R-space. The coefficient ring
/// prints briefly.
pub fn fmt_parent(it: &mut Interp, p: &mut Printer, st: &Struct, indent: usize) -> RResult<()> {
    let mp = info(st);
    let ring = mp.ring.clone();
    if mp.sub.is_some() {
        return fmt_subspace(it, p, st, indent);
    }
    if p.level == Level::Magma {
        let (name, dims) = match mp.shape {
            Shape::Algebra => ("MatrixAlgebra", format!("{}", mp.nrows)),
            Shape::Space => (if mp.field { "KMatrixSpace" } else { "RMatrixSpace" }, format!("{}, {}", mp.nrows, mp.ncols)),
            Shape::Tuples => (if mp.field { "VectorSpace" } else { "RSpace" }, format!("{}", mp.ncols)),
        };
        p.write(&format!("{name}("));
        it.fmt(p, &ring, indent)?;
        p.write(&format!(", {dims})"));
        return Ok(());
    }
    p.write(&match mp.shape {
        Shape::Algebra => format!("Full Matrix Algebra of degree {} over ", mp.nrows),
        Shape::Space => format!("Full {}MatrixSpace of {} by {} matrices over ", if mp.field { "K" } else { "R" }, mp.nrows, mp.ncols),
        Shape::Tuples if mp.field => format!("Full Vector space of degree {} over ", mp.ncols),
        Shape::Tuples => format!("Full RSpace of degree {} over ", mp.ncols),
    });
    let saved = p.level;
    p.level = Level::Minimal;
    let r = it.fmt(p, &ring, indent);
    p.level = saved;
    r?;
    match &mp.form {
        Some(f) if saved != Level::Minimal => fmt_form(it, p, &ring, f, indent),
        _ => Ok(()),
    }
}

/// The inner product matrix of a space, below it.
fn fmt_form(it: &mut Interp, p: &mut Printer, ring: &Value, f: &Mat, indent: usize) -> RResult<()> {
    p.newline(indent);
    p.write("Inner Product Matrix:");
    p.newline(indent);
    fmt_rows(it, p, ring, f, false, indent)
}

/// A subspace of an R-space: its degree and dimension, and its basis
/// (below them, or at the Magma level as a `sub` constructor).
fn fmt_subspace(it: &mut Interp, p: &mut Printer, st: &Struct, indent: usize) -> RResult<()> {
    let mp = info(st);
    let sub = mp.sub.as_ref().expect("a subspace");
    let ring = mp.ring.clone();
    let basis = sub.basis.clone();
    if p.level == Level::Magma {
        p.write("sub<");
        it.fmt(p, &Value::Struct(sub.full.clone()), indent)?;
        p.write(" |");
        for i in 0..basis.nrows() {
            if i > 0 {
                p.write(",");
            }
            p.newline(indent + 4);
            let row = Value::seq(Some(ring.clone()), (0..basis.ncols()).map(|j| entry_of(it, &ring, &basis, i, j)).collect());
            it.fmt(p, &row, indent + 4)?;
        }
        if basis.nrows() == 0 {
            p.newline(indent);
        }
        p.newline(indent);
        p.write(">");
        return Ok(());
    }
    let name = if mp.field { "Vector space" } else { "RSpace" };
    p.write(&format!("{name} of degree {}, dimension {} over ", mp.ncols, basis.nrows()));
    let saved = p.level;
    p.level = Level::Minimal;
    let r = it.fmt(p, &ring, indent);
    p.level = saved;
    r?;
    if saved == Level::Minimal || basis.nrows() == 0 {
        return Ok(());
    }
    p.newline(indent);
    p.write(if sub.echelonized { "Echelonized basis:" } else { "Basis:" });
    p.newline(indent);
    fmt_rows(it, p, &ring, &basis, true, indent)?;
    match &info(&sub.full).form {
        Some(f) => fmt_form(it, p, &ring, f, indent),
        None => Ok(()),
    }
}
