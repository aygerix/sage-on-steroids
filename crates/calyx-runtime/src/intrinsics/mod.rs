//! The table of intrinsics (built-in and user-defined functions with type
//! signatures) and the built-in libraries.

pub mod abgroups;
pub mod algass;
pub mod aggregates;
pub mod combinat;
pub mod complex;
pub mod core;
pub mod dlog;
pub mod env;
pub mod factoring;
pub mod factseq;
pub mod finite_fields;
pub mod groebner;
pub mod ideals;
pub mod ints;
pub mod io;
pub mod lattices;
pub mod maps;
pub mod matrices;
pub mod polar;
pub mod sparse;
pub mod mpoly;
pub mod nearfields;
pub mod numtheory;
pub mod perms;
pub mod poly_ideals;
pub mod rationals;
pub mod ring_elts;
pub mod reals;
pub mod residue;
pub mod rings;
pub mod strings;
pub mod upoly;

use std::path::PathBuf;
use std::rc::Rc;

use calyx_flint::Integer;
use rustc_hash::FxHashMap;

use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::sym::Sym;
use crate::types::{TypePat, parse_type_pat};
use crate::value::*;

pub type NativeFn = fn(&mut Interp, &mut CallArgs) -> RResult<Vals>;

pub enum Imp {
    Native(NativeFn),
    User(Rc<Closure>),
}

pub struct ArgSig {
    pub name: Rc<str>,
    pub pat: TypePat,
    pub is_ref: bool,
    /// A reference argument without a type (may be unassigned).
    pub untyped: bool,
}

pub struct ParamSig {
    pub name: Sym,
    pub default: Value,
    pub default_text: Rc<str>,
}

pub struct Signature {
    pub args: Vec<ArgSig>,
    pub variadic: bool,
    /// `None` for procedures.
    pub returns: Option<Vec<TypePat>>,
    pub params: Vec<ParamSig>,
    pub doc: Rc<str>,
    pub imp: Imp,
    /// A catch-all operator signature implemented by the evaluator.
    pub generic: bool,
    pub order: u64,
    /// The package file that defined this signature, if any.
    pub source: Option<PathBuf>,
    /// Written in Magma's language (a package intrinsic): parameters it does
    /// not take fail as for user functions, without the argument types.
    pub package: bool,
}

/// The signature last chosen at a call site, remembered with the argument
/// types it was chosen for. Only calls whose candidate signatures test
/// plain types are remembered, since their choice depends on nothing else;
/// for other calls the site remembers not to try.
#[derive(Default)]
pub struct SigCache(std::cell::RefCell<SiteChoice>);

#[derive(Default)]
enum SiteChoice {
    #[default]
    Empty,
    Chosen(SiteKey, Rc<Signature>),
    Never(Sym, (u64, u64)),
}

#[derive(PartialEq)]
pub struct SiteKey {
    name: Sym,
    stamp: (u64, u64),
    stmt: bool,
    arity: usize,
    refs: u32,
    types: [u32; 4],
}

impl SiteKey {
    /// The key of a call with at most four arguments.
    pub fn new(it: &Interp, name: Sym, args: &[Value], refmask: &[bool], stmt: bool) -> Option<SiteKey> {
        if args.len() > 4 {
            return None;
        }
        let mut types = [0; 4];
        let mut refs = 0;
        for (i, v) in args.iter().enumerate() {
            types[i] = if v.is_undef() { u32::MAX } else { v.type_id().0 };
            if refmask.get(i).copied().unwrap_or(false) {
                refs |= 1 << i;
            }
        }
        let stamp = (it.intrinsics.generation(), it.types.version());
        Some(SiteKey { name, stamp, stmt, arity: args.len(), refs, types })
    }
}

impl SigCache {
    pub fn get(&self, key: &SiteKey) -> Option<Rc<Signature>> {
        match &*self.0.borrow() {
            SiteChoice::Chosen(k, sig) if k == key => Some(sig.clone()),
            _ => None,
        }
    }

    /// Whether calls of `name` here are known not to be remembered.
    pub fn never(&self, it: &Interp, name: Sym) -> bool {
        matches!(&*self.0.borrow(), SiteChoice::Never(n, stamp) if *n == name && *stamp == (it.intrinsics.generation(), it.types.version()))
    }

    pub fn put(&self, key: SiteKey, sig: Rc<Signature>) {
        *self.0.borrow_mut() = SiteChoice::Chosen(key, sig);
    }

    pub fn put_never(&self, key: SiteKey) {
        *self.0.borrow_mut() = SiteChoice::Never(key.name, key.stamp);
    }
}

#[derive(Default)]
pub struct IntrinsicTable {
    map: FxHashMap<Sym, Vec<Rc<Signature>>>,
    counter: u64,
}

impl IntrinsicTable {
    pub fn new() -> IntrinsicTable {
        IntrinsicTable::default()
    }

    pub fn contains(&self, name: Sym) -> bool {
        self.map.get(&name).is_some_and(|v| !v.is_empty())
    }

    pub fn get(&self, name: Sym) -> Option<&Vec<Rc<Signature>>> {
        self.map.get(&name).filter(|v| !v.is_empty())
    }

    /// Whether every signature of `name` taking `arity` arguments tests
    /// them by type only.
    pub fn plain(&self, name: Sym, arity: usize) -> bool {
        let takes = |s: &Signature| if s.variadic { arity >= s.args.len() } else { arity == s.args.len() };
        self.get(name).is_some_and(|sigs| sigs.iter().filter(|s| takes(s)).all(|s| s.args.iter().all(|a| matches!(a.pat, TypePat::Any | TypePat::Is(_)))))
    }

    pub fn add(&mut self, name: Sym, mut sig: Signature) -> &mut Signature {
        self.counter += 1;
        sig.order = self.counter;
        let sigs = self.map.entry(name).or_default();
        sigs.push(Rc::new(sig));
        Rc::get_mut(sigs.last_mut().unwrap()).unwrap()
    }

    /// Changes whenever signatures are added or removed.
    pub fn generation(&self) -> u64 {
        self.counter
    }

    /// Remove all signatures defined by a package file.
    pub fn remove_source(&mut self, path: &PathBuf) {
        self.counter += 1;
        for sigs in self.map.values_mut() {
            sigs.retain(|s| s.source.as_ref() != Some(path));
        }
    }

    pub fn names(&self) -> impl Iterator<Item = Sym> + '_ {
        self.map.iter().filter(|(_, v)| !v.is_empty()).map(|(k, _)| *k)
    }
}

/// Parse `"x::RngIntElt, ~S::SeqEnum -> RngIntElt"`.
fn parse_sig(it: &Interp, s: &str) -> Result<(Vec<ArgSig>, bool, Option<Vec<TypePat>>), String> {
    let (lhs, rhs) = match s.rfind("->") {
        Some(i) => (&s[..i], Some(&s[i + 2..])),
        None => (s, None),
    };
    let mut args = Vec::new();
    let mut variadic = false;
    for part in split_top(lhs) {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        if part == "..." {
            variadic = true;
            continue;
        }
        let (is_ref, rest) = match part.strip_prefix('~') {
            Some(r) => (true, r),
            None => (false, part),
        };
        let (name, pat, untyped) = match rest.split_once("::") {
            Some((n, t)) => (n.trim(), parse_type_pat(t.trim(), &it.types)?, false),
            None => (rest.trim(), TypePat::Any, true),
        };
        args.push(ArgSig { name: Rc::from(name), pat, is_ref, untyped: untyped && is_ref });
    }
    let returns = match rhs {
        None => None,
        Some(r) => {
            let mut v = Vec::new();
            for t in split_top(r) {
                let t = t.trim();
                if !t.is_empty() {
                    v.push(parse_type_pat(t, &it.types)?);
                }
            }
            Some(v)
        }
    };
    Ok((args, variadic, returns))
}

fn split_top(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in s.char_indices() {
        match c {
            '[' | '{' | '<' => depth += 1,
            ']' | '}' | '>' => depth -= 1,
            ',' if depth == 0 => {
                out.push(&s[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(&s[start..]);
    out
}

impl Interp {
    /// Register a native intrinsic. Set `package` on the signature returned
    /// for one that Magma writes in its own language.
    pub fn def(&mut self, name: &str, sig: &str, doc: &str, f: NativeFn) -> &mut Signature {
        self.def_params(name, sig, &[], doc, f)
    }

    /// Register a native intrinsic with named parameters and defaults.
    pub fn def_params(&mut self, name: &str, sig: &str, params: &[(&str, Value)], doc: &str, f: NativeFn) -> &mut Signature {
        let (args, variadic, returns) = parse_sig(self, sig).unwrap_or_else(|e| panic!("bad signature for {name}: {sig}: {e}"));
        let params = params
            .iter()
            .map(|(n, v)| ParamSig { name: Sym::new(n), default: v.clone(), default_text: Rc::from(self.format_flat(v, crate::print::Level::Magma).unwrap_or_default().as_str()) })
            .collect();
        let sig = Signature { args, variadic, returns, params, doc: Rc::from(doc), imp: Imp::Native(f), generic: false, order: 0, source: None, package: false };
        self.intrinsics.add(Sym::new(name), sig)
    }

    /// Register a catch-all operator signature.
    pub fn def_generic(&mut self, name: &str, sig: &str, doc: &str, f: NativeFn) {
        let (args, variadic, returns) = parse_sig(self, sig).unwrap();
        let sig = Signature { args, variadic, returns, params: Vec::new(), doc: Rc::from(doc), imp: Imp::Native(f), generic: true, order: 0, source: None, package: false };
        self.intrinsics.add(Sym::new(name), sig);
    }

    /// Text describing an intrinsic and its signatures.
    pub fn describe_intrinsic(&self, name: Sym) -> String {
        let mut out = format!("Intrinsic '{name}'\n\nSignatures:\n");
        if let Some(sigs) = self.intrinsics.get(name) {
            for s in sigs {
                out.push('\n');
                out.push_str("    ");
                out.push_str(&self.signature_line(s));
                out.push('\n');
                if !s.params.is_empty() {
                    for p in &s.params {
                        out.push_str(&format!("    [\n        {}: default {}\n    ]\n", p.name, p.default_text));
                    }
                }
                if !s.doc.is_empty() {
                    out.push('\n');
                    for line in wrap_text(&s.doc, 68) {
                        out.push_str("        ");
                        out.push_str(&line);
                        out.push('\n');
                    }
                }
            }
        }
        out.trim_end().to_string()
    }

    pub fn signature_line(&self, s: &Signature) -> String {
        let mut parts: Vec<String> = s
            .args
            .iter()
            .map(|a| {
                let t = a.pat.describe(&self.types);
                format!("{}<{}> {}", if a.is_ref { "~" } else { "" }, t, a.name)
            })
            .collect();
        if s.variadic {
            parts.push("...".into());
        }
        let mut line = format!("({})", parts.join(", "));
        if let Some(r) = &s.returns {
            let rs: Vec<String> = r.iter().map(|t| t.describe(&self.types)).collect();
            line.push_str(&format!(" -> {}", rs.join(", ")));
        }
        line
    }
}

fn wrap_text(s: &str, width: usize) -> Vec<String> {
    let mut lines = Vec::new();
    let mut cur = String::new();
    for w in s.split_whitespace() {
        if !cur.is_empty() && cur.len() + 1 + w.len() > width {
            lines.push(std::mem::take(&mut cur));
        }
        if !cur.is_empty() {
            cur.push(' ');
        }
        cur.push_str(w);
    }
    if !cur.is_empty() {
        lines.push(cur);
    }
    lines
}

// ----- helpers for native implementations ----------------------------------

pub fn one(v: Value) -> RResult<Vals> {
    Ok(vals![v])
}

pub fn none() -> RResult<Vals> {
    Ok(Vals::new())
}

pub fn boolv(b: bool) -> RResult<Vals> {
    one(Value::Bool(b))
}

pub fn intv(i: Integer) -> RResult<Vals> {
    one(Value::Int(i))
}

// ----- Magma's wording for bad arguments -------------------------------------

/// `Argument i (v) should be >= lo`.
pub fn arg_ge(i: usize, v: &Integer, lo: impl std::fmt::Display) -> RuntimeError {
    RuntimeError::runtime(format!("Argument {i} ({v}) should be >= {lo}"))
}

/// `Argument i (v) should be <= hi`.
pub fn arg_le(i: usize, v: &Integer, hi: impl std::fmt::Display) -> RuntimeError {
    RuntimeError::runtime(format!("Argument {i} ({v}) should be <= {hi}"))
}

/// `Argument i (v) should be in the range [lo .. hi]`.
pub fn arg_range(i: usize, v: &Integer, lo: impl std::fmt::Display, hi: impl std::fmt::Display) -> RuntimeError {
    RuntimeError::runtime(format!("Argument {i} ({v}) should be in the range [{lo} .. {hi}]"))
}

/// `Argument i is not <what>` (`non-zero`, `positive`, `non-negative`).
pub fn arg_not(i: usize, what: &str) -> RuntimeError {
    RuntimeError::runtime(format!("Argument {i} is not {what}"))
}

/// `Argument i (v) should be prime`.
pub fn arg_prime(i: usize, v: &Integer) -> RuntimeError {
    RuntimeError::runtime(format!("Argument {i} ({v}) should be prime"))
}

/// An error reported without naming the intrinsic, as errors inside the
/// code of Magma's package intrinsics are.
pub fn bare(e: RuntimeError) -> RuntimeError {
    e.in_context("")
}

/// An error raised in the code of a package intrinsic, which Magma reports
/// with the call frames and positions in its package sources. Those
/// positions are not ours to show (they quote Magma's code): the reference
/// outputs have them replaced by "[Magma package traceback hidden]", and so
/// does calyx. The frames printed are the intrinsic's own and those of the
/// user functions calling it; the error is unnamed.
pub fn hidden(e: RuntimeError) -> RuntimeError {
    let mut e = bare(e);
    e.hidden = true;
    e.frame = true;
    e
}

/// As `hidden`, for an error raised deeper in the package code, whose
/// report lacks the intrinsic's call frame. An error of another intrinsic
/// called there keeps its name.
pub fn hidden_inner(e: RuntimeError) -> RuntimeError {
    let mut e = bare(e);
    e.hidden = true;
    e
}

/// An error of a user function called back by a package intrinsic, whose
/// report shows the intrinsic's call frame before the function's.
pub fn package_frame(mut e: RuntimeError) -> RuntimeError {
    e.frame = true;
    e
}

/// A failed requirement of a package intrinsic: as Magma reports them, it
/// names the intrinsic unless the call is a statement of its own.
pub fn require(e: RuntimeError) -> RuntimeError {
    let mut e = bare(e);
    e.require = true;
    e
}

impl CallArgs {
    /// Argument `i` as an integer that is at least `lo`, else Magma's
    /// `should be >= lo` error.
    pub fn int_ge(&self, i: usize, lo: i64) -> RResult<Integer> {
        let n = self.int(i)?;
        if *n < Integer::from_i64(lo) {
            return Err(arg_ge(i + 1, n, lo));
        }
        Ok(n.clone())
    }

    /// Argument `i` as a machine integer that is at least `lo`.
    pub fn small_ge(&self, i: usize, lo: i64) -> RResult<u64> {
        let n = self.int_ge(i, lo)?;
        n.to_u64().ok_or_else(|| RuntimeError::runtime(format!("Argument {} ({n}) is too large", i + 1)))
    }

    pub fn int(&self, i: usize) -> RResult<&Integer> {
        match &self.args[i] {
            Value::Int(n) => Ok(n),
            other => Err(RuntimeError::runtime(format!("Argument {} must be an integer (got {})", i + 1, crate::value_kind(other)))),
        }
    }

    pub fn i64(&self, i: usize) -> RResult<i64> {
        self.int(i)?.to_i64().ok_or_else(|| RuntimeError::runtime(format!("Argument {} is too large", i + 1)))
    }

    /// Argument `i` as one of Magma's small integers, |n| < 2^30.
    pub fn small(&self, i: usize) -> RResult<i64> {
        let n = self.int(i)?;
        n.to_i64().filter(|v| v.unsigned_abs() < 1 << 30).ok_or_else(|| RuntimeError::runtime(format!("Argument {} ({n}) is not small", i + 1)))
    }

    pub fn usize(&self, i: usize) -> RResult<usize> {
        let n = self.int(i)?;
        if n.sign() < 0 {
            return Err(RuntimeError::runtime(format!("Argument {} must be non-negative", i + 1)));
        }
        n.to_u64().map(|v| v as usize).ok_or_else(|| RuntimeError::runtime(format!("Argument {} is too large", i + 1)))
    }

    pub fn str(&self, i: usize) -> RResult<&str> {
        match &self.args[i] {
            Value::Str(s) => Ok(s),
            other => Err(RuntimeError::runtime(format!("Argument {} must be a string (got {})", i + 1, crate::value_kind(other)))),
        }
    }

    pub fn bool(&self, i: usize) -> RResult<bool> {
        match &self.args[i] {
            Value::Bool(b) => Ok(*b),
            other => Err(RuntimeError::runtime(format!("Argument {} must be a boolean (got {})", i + 1, crate::value_kind(other)))),
        }
    }

    pub fn seq(&self, i: usize) -> RResult<&Rc<SeqEnum>> {
        match &self.args[i] {
            Value::Seq(s) => Ok(s),
            other => Err(RuntimeError::runtime(format!("Argument {} must be a sequence (got {})", i + 1, crate::value_kind(other)))),
        }
    }

    pub fn param_bool(&self, name: &str) -> RResult<bool> {
        match self.param(name) {
            Some(Value::Bool(b)) => Ok(*b),
            Some(_) => Err(RuntimeError::runtime(format!("Parameter '{name}' must be a boolean"))),
            None => Ok(false),
        }
    }
}

/// Register every built-in library.
pub fn register_all(it: &mut Interp) {
    core::register(it);
    ints::register(it);
    factseq::register(it);
    numtheory::register(it);
    combinat::register(it);
    factoring::register(it);
    reals::register(it);
    strings::register(it);
    aggregates::register(it);
    maps::register(it);
    rings::register(it);
    residue::register(it);
    abgroups::register(it);
    perms::register(it);
    ring_elts::register(it);
    ideals::register(it);
    // The Part III chapters that are still being written, one module each.
    rationals::register(it);
    finite_fields::register(it);
    nearfields::register(it);
    algass::register(it);
    upoly::register(it);
    mpoly::register(it);
    groebner::register(it);
    poly_ideals::register(it);
    complex::register(it);
    // Part IV.
    matrices::register(it);
    polar::register(it);
    sparse::register(it);
    // Part V.
    lattices::register(it);
    io::register(it);
    env::register(it);
}
