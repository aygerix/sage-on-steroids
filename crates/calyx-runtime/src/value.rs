//! Runtime values.
//!
//! Aggregates are immutable values shared through `Rc` and copied on write
//! (`Rc::make_mut`), which gives Magma's value semantics cheaply. Structures
//! and objects of user-defined types have reference semantics.

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::rc::Rc;

use calyx_flint::{Integer, Rational, Real};
use indexmap::{IndexMap, IndexSet};
use rustc_hash::{FxHashMap, FxHasher};

use crate::abgroups::{AbElt, AbGroup};
use crate::error::RResult;
use crate::interp::Interp;
use crate::ir::FuncCode;
use crate::perms::Perm;
use crate::rings::small::SmallRing;
use crate::rings::{Elt, Ring};
use crate::sym::Sym;
use crate::types::{TypeId, TypeVal, t};

pub type FxBuild = BuildHasherDefault<FxHasher>;

/// The results of a call: usually one value, held without allocating.
pub type Vals = smallvec::SmallVec<[Value; 1]>;
pub type VSet = IndexSet<Value, FxBuild>;
pub type VMap<V> = IndexMap<Value, V, FxBuild>;

#[derive(Clone, Default)]
pub enum Value {
    /// An undefined entry (a hole in a sequence, or `_` in a return list).
    #[default]
    Undef,
    Bool(bool),
    Int(Integer),
    Rat(Rc<Rational>),
    Real(Rc<RealV>),
    /// A complex number (an element of a complex field).
    Complex(Rc<ComplexV>),
    Str(Rc<Text>),
    /// A binary string, stored as bytes rather than Unicode text.
    BStr(Rc<Vec<u8>>),
    Seq(Rc<SeqEnum>),
    Set(Rc<SetEnum>),
    ISet(Rc<SetIndx>),
    MSet(Rc<SetMulti>),
    Formal(Rc<Formal>),
    Tuple(Rc<Tuple>),
    List(Rc<Vec<Value>>),
    Rec(Rc<Record>),
    Assoc(Rc<Assoc>),
    Func(Rc<Closure>),
    /// An intrinsic, referred to by name (resolved at call time).
    Intr(Sym),
    Map(Rc<MapObj>),
    Struct(Rc<Struct>),
    Cat(TypeId),
    ECat(Rc<TypeVal>),
    Err(Rc<ErrObj>),
    Obj(Rc<UserObj>),
    CopElt(Rc<CopElt>),
    Io(Rc<IoObj>),
    /// An element of a ring built on FLINT (residue class rings, finite
    /// fields, polynomial rings, the complex field, ...).
    Elt(Rc<Elt>),
    /// An element of a ring whose elements fit in a word (`Z/nZ` or `GF(p)`
    /// with a modulus below 2^64): the ring and the residue.
    Small(SmallRing, u64),
    /// A permutation, an element of `Sym(n)`.
    Perm(Rc<Perm>),
    /// An element of an abelian group (`GrpAbElt`).
    AbElt(Rc<AbElt>),
    /// An element of a nearfield (`NfdElt`).
    Nfd(Rc<crate::intrinsics::nearfields::NfdElt>),
    /// An element of an associative algebra (`AlgAssElt`).
    Alg(Rc<crate::intrinsics::algass::AlgAssElt>),
    /// A Dirichlet character (`GrpDrchElt`).
    Drch(Rc<crate::intrinsics::residue::dirichlet::DrchElt>),
    /// `Infinity()` (`true`) or `-Infinity()` (`false`).
    Infinity(bool),
    /// A matrix or a vector (`intrinsics/matrices`).
    Mat(Rc<crate::intrinsics::matrices::Mtrx>),
    /// A sparse matrix (`intrinsics/sparse`).
    Sparse(Rc<crate::intrinsics::sparse::SparseMatrix>),
}

// Values are copied everywhere; keep them two words.
const _: () = assert!(std::mem::size_of::<Value>() == 16);

/// The contents of a string. Strings grow in place under `cat:=` when not
/// shared, and remember whether they are ASCII so that lengths and
/// indices of ASCII text take constant time.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Text {
    s: String,
    ascii: bool,
}

impl Text {
    pub fn new(s: String) -> Text {
        Text { ascii: s.is_ascii(), s }
    }

    pub fn as_str(&self) -> &str {
        &self.s
    }

    pub fn push_str(&mut self, t: &str) {
        self.ascii &= t.is_ascii();
        self.s.push_str(t);
    }

    pub fn push_text(&mut self, t: &Text) {
        self.ascii &= t.ascii;
        self.s.push_str(&t.s);
    }

    /// The number of characters.
    pub fn len(&self) -> usize {
        if self.ascii { self.s.len() } else { self.s.chars().count() }
    }

    /// The `k`th character (from 0).
    pub fn char_at(&self, k: usize) -> Option<&str> {
        if self.ascii { self.s.get(k..k + 1) } else { self.s.char_indices().nth(k).map(|(i, c)| &self.s[i..i + c.len_utf8()]) }
    }
}

impl std::fmt::Display for Text {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.s)
    }
}

impl std::ops::Deref for Text {
    type Target = str;

    fn deref(&self) -> &str {
        &self.s
    }
}

/// A real number. Its precision in bits determines its real field.
#[derive(Clone)]
pub struct RealV {
    pub x: Real,
    /// Print with this many decimals instead (used for timings).
    pub fixed: Option<u32>,
}

impl RealV {
    pub fn new(x: Real) -> RealV {
        RealV { x, fixed: None }
    }

    /// The decimal precision of its field.
    pub fn digits(&self) -> u32 {
        self.x.digits() as u32
    }
}

/// A complex number: real and imaginary parts of the same precision, which
/// determines its complex field.
pub type ComplexV = calyx_flint::Complex;

// ----- aggregates -----------------------------------------------------------

/// The identifier an aggregate was first assigned to, which maps print as
/// its name (`SetEnum: T`). A copy, made when a shared aggregate is
/// modified, starts without one.
#[derive(Default)]
pub struct NameCell(pub RefCell<Option<Sym>>);

impl Clone for NameCell {
    fn clone(&self) -> NameCell {
        NameCell::default()
    }
}

/// An enumerated sequence. Holes are stored as `Value::Undef`.
#[derive(Clone, Default)]
pub struct SeqEnum {
    /// `None` for the null sequence `[]`.
    pub universe: Option<Value>,
    pub elems: Vec<Value>,
    /// Built as an arithmetic progression `[a..b by c]`; it prints that way
    /// while its elements still form a progression.
    pub range_hint: bool,
    pub name: NameCell,
    /// A factorization sequence (`RngIntEltFact`): sorted `<p, k>` pairs
    /// of primes and positive exponents with its own arithmetic.
    pub fact: bool,
}

impl SeqEnum {
    pub fn new(universe: Option<Value>, elems: Vec<Value>) -> SeqEnum {
        SeqEnum { universe, elems, range_hint: false, name: NameCell::default(), fact: false }
    }

    /// `(first, last, step)` if this prints as an arithmetic progression.
    pub fn as_progression(&self) -> Option<(Integer, Integer, Integer)> {
        if !self.range_hint || self.elems.len() < 2 {
            return None;
        }
        let ints: Option<Vec<&Integer>> = self.elems.iter().map(|v| if let Value::Int(i) = v { Some(i) } else { None }).collect();
        let ints = ints?;
        let step = if ints.len() >= 2 { ints[1] - ints[0] } else { Integer::one() };
        if step.is_zero() {
            return None;
        }
        for w in ints.windows(2) {
            if &(w[1] - w[0]) != &step {
                return None;
            }
        }
        Some((ints[0].clone(), ints[ints.len() - 1].clone(), step))
    }

    pub fn is_complete(&self) -> bool {
        !self.elems.iter().any(|v| matches!(v, Value::Undef))
    }
}

/// An enumerated set. Arithmetic progressions of integers are stored lazily
/// until the set is modified.
#[derive(Clone)]
pub struct SetEnum {
    pub universe: Option<Value>,
    pub repr: SetRepr,
    pub name: NameCell,
}

#[derive(Clone)]
pub enum SetRepr {
    /// `{ lo .. hi by step }` with `len` elements (step never zero).
    Range { lo: Integer, step: Integer, len: u64 },
    Elems(VSet),
}

impl SetEnum {
    pub fn new(universe: Option<Value>, elems: VSet) -> SetEnum {
        SetEnum { universe, repr: SetRepr::Elems(elems), name: NameCell::default() }
    }

    pub fn range(lo: Integer, hi: &Integer, step: Integer) -> SetEnum {
        let len = range_len(&lo, hi, &step);
        // A set does not remember direction: store it ascending.
        if step.sign() < 0 && len > 0 {
            let last = &lo + &(&step * &Integer::from_u64(len - 1));
            return SetEnum { universe: Some(Value::integers()), repr: SetRepr::Range { lo: last, step: -step, len }, name: NameCell::default() };
        }
        SetEnum { universe: Some(Value::integers()), repr: SetRepr::Range { lo, step, len }, name: NameCell::default() }
    }

    pub fn len(&self) -> usize {
        match &self.repr {
            SetRepr::Range { len, .. } => *len as usize,
            SetRepr::Elems(s) => s.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn contains(&self, v: &Value) -> bool {
        match &self.repr {
            SetRepr::Range { lo, step, len } => {
                let Value::Int(x) = v else {
                    return match v {
                        Value::Rat(q) if q.is_integral() => self.contains(&Value::Int(q.numerator())),
                        _ => false,
                    };
                };
                let d = x - lo;
                match d.div_rem_euclid(step) {
                    Some((q, r)) => r.is_zero() && q.sign() >= 0 && q.to_u64().is_some_and(|q| q < *len),
                    None => false,
                }
            }
            SetRepr::Elems(s) => s.contains(v),
        }
    }

    /// Switch to the explicit representation (needed before modification).
    pub fn elems_mut(&mut self) -> &mut VSet {
        if let SetRepr::Range { .. } = self.repr {
            let s: VSet = self.iter().collect();
            self.repr = SetRepr::Elems(s);
        }
        match &mut self.repr {
            SetRepr::Elems(s) => s,
            SetRepr::Range { .. } => unreachable!(),
        }
    }

    pub fn iter(&self) -> Box<dyn Iterator<Item = Value> + '_> {
        match &self.repr {
            SetRepr::Range { lo, step, len } => {
                let lo = lo.clone();
                let step = step.clone();
                Box::new((0..*len).map(move |i| Value::Int(&lo + &(&step * &Integer::from_u64(i)))))
            }
            SetRepr::Elems(s) => Box::new(s.iter().cloned()),
        }
    }

    pub fn is_range(&self) -> bool {
        matches!(self.repr, SetRepr::Range { .. })
    }
}

/// The number of terms in `lo, lo+step, ...` not passing `hi`.
pub fn range_len(lo: &Integer, hi: &Integer, step: &Integer) -> u64 {
    let span = hi - lo;
    if span.is_zero() {
        return 1;
    }
    if span.sign() != step.sign() {
        return 0;
    }
    let (q, _) = span.tdiv_qr(step).unwrap();
    q.to_u64().map(|q| q + 1).unwrap_or(u64::MAX)
}

#[derive(Clone, Default)]
pub struct SetIndx {
    pub universe: Option<Value>,
    pub elems: VSet,
    pub name: NameCell,
}

#[derive(Clone, Default)]
pub struct SetMulti {
    pub universe: Option<Value>,
    pub elems: VMap<u64>,
    pub name: NameCell,
}

impl SetMulti {
    pub fn total(&self) -> u64 {
        self.elems.values().sum()
    }

    pub fn insert(&mut self, v: Value, n: u64) {
        if n > 0 {
            *self.elems.entry(v).or_insert(0) += n;
        }
    }
}

/// A formal set `{! x in S | P !}` or formal sequence `[! ... !]`.
#[derive(Clone)]
pub struct Formal {
    pub is_seq: bool,
    pub universe: Value,
    /// The predicate as a one-argument function, if present.
    pub pred: Option<Value>,
}

#[derive(Clone)]
pub struct Tuple {
    pub elems: Vec<Value>,
    /// The Cartesian product this tuple belongs to, when known.
    pub parent: Option<Value>,
}

#[derive(Clone)]
pub struct Record {
    pub format: Rc<Struct>,
    pub fields: Vec<Value>,
}

#[derive(Clone, Default)]
pub struct Assoc {
    pub universe: Option<Value>,
    pub map: VMap<Value>,
    /// Value returned for keys that are not present (`Default` parameter).
    pub default: Option<Value>,
}

// ----- programs and maps ----------------------------------------------------

/// A user function or procedure value.
pub struct Closure {
    pub code: Rc<FuncCode>,
    pub captures: Rc<[Value]>,
    /// The name its call frames show: that of its definition, or else of
    /// the first identifier it is assigned to.
    pub name: Cell<Option<Sym>>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MapKind {
    Map,
    PMap,
    Hom,
    Iso,
}

pub struct MapObj {
    pub kind: MapKind,
    pub domain: Value,
    pub codomain: Value,
    pub imp: MapImpl,
}

pub enum MapImpl {
    /// `x :-> e(x)` with an optional inverse rule.
    Rule { f: Value, inv: Option<Value> },
    /// An explicit graph (domain element to image).
    Graph(VMap<Value>),
    /// Apply the maps in order.
    Compose(Vec<Rc<MapObj>>),
    /// The coercion map from domain to codomain.
    Coercion,
    /// Reduction of the integers modulo m (a coercion that prints its
    /// modulus).
    Reduction(Integer),
    /// The i-th injection into a coproduct (codomain).
    Injection(usize),
    /// The inverse of another map.
    Inverse(Rc<MapObj>),
    /// A map computed by the runtime (the maps of unit groups, for example).
    Native(Rc<dyn NativeMap>),
}

/// A map implemented in Rust. Unlike other maps, arguments reach it as
/// given, so it decides itself what it accepts.
pub trait NativeMap {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value>;
    fn preimage(&self, it: &mut Interp, m: &MapObj, y: &Value) -> RResult<Value>;

    /// The pairs `<x, y>` printed after a map that Magma defines by its
    /// graph.
    fn graph(&self, _m: &MapObj) -> Option<Vec<(Value, Value)>> {
        None
    }

    /// Whether the map prints as given by a rule (with no inverse).
    fn rule(&self) -> bool {
        false
    }

    /// Whether the map prints as given by a rule that has an inverse.
    fn rule_with_inverse(&self) -> bool {
        false
    }

    /// Whether `Inverse` applies (Magma refuses it for maps with no inverse).
    fn has_inverse(&self) -> bool {
        true
    }

    /// `Image(f)`, for maps that give it themselves.
    fn image(&self, _it: &mut Interp, _m: &MapObj) -> Option<RResult<Value>> {
        None
    }
}

// ----- structures -----------------------------------------------------------

/// A built-in parent structure. Attributes may be attached to structures.
pub struct Struct {
    pub kind: StructKind,
    pub attrs: RefCell<FxHashMap<Sym, Value>>,
    /// The identifier the structure is known by in printing: the first
    /// global it was assigned to that still holds it.
    pub name: RefCell<Option<Sym>>,
    /// The other globals assigned the structure since, in order; one of
    /// them takes over the name when its holder is rebound.
    pub aliases: RefCell<Vec<Sym>>,
}

#[derive(Clone)]
pub enum StructKind {
    Integers,
    Rationals,
    /// The real field with the given precision in bits.
    Reals(u64),
    Booleans,
    Strings,
    PowerSet(Option<Value>),
    PowerSeq(Option<Value>),
    PowerISet(Option<Value>),
    PowerMSet(Option<Value>),
    /// `car< ... >`
    Cartesian(Vec<Value>),
    RecFormat(RecFormat),
    /// The set of maps from one structure to another.
    Maps(Value, Value),
    Coproduct(Vec<Value>),
    /// The parent of some category of objects without a finer parent.
    PowerStructure(TypeId),
    /// A ring whose elements are `Value::Elt`.
    Ring(Rc<Ring>),
    /// The symmetric group of the given degree.
    SymGroup(u32),
    /// The reals with the two infinities (the universe of numbers mixed
    /// with `Infinity()`).
    ExtendedReals,
    /// The ideal `nZ` of the integers (`n = 0` or `n > 1`), itself of type
    /// `RngInt`.
    IntIdeal(Integer),
    /// The ideal `dR` of a residue class ring `R = Z/mZ`, for a divisor
    /// `d > 1` of `m` (`d = m` is the zero ideal); of type `RngIntRes`.
    ResIdeal(Rc<Struct>, Integer),
    /// A proper ideal of a univariate polynomial ring over a field, of type
    /// `RngUPol`, with its monic (or zero) generator.
    UPolIdeal(Rc<crate::rings::Elt>),
    /// An ideal of a multivariate polynomial ring, of type `RngMPol`
    /// (`intrinsics/poly_ideals.rs`).
    MPolIdeal(Rc<crate::intrinsics::poly_ideals::MPolIdeal>),
    /// An ideal of an affine algebra, of type `RngMPolRes` like the algebra
    /// (`intrinsics/poly_ideals/affine.rs`).
    AffIdeal(Rc<crate::intrinsics::poly_ideals::AffIdeal>),
    /// An abelian group; every construction makes a new group.
    AbGroup(Rc<AbGroup>),
    /// A nearfield (`intrinsics/nearfields.rs`).
    Nearfield(Rc<crate::intrinsics::nearfields::Nearfield>),
    /// The set of all automorphisms of a structure (`PowMapAut`).
    Automorphisms(Value),
    /// An associative algebra (`intrinsics/algass.rs`).
    AlgAss(Rc<crate::intrinsics::algass::AlgAss>),
    /// A group of Dirichlet characters (`intrinsics/residue/dirichlet.rs`).
    DrchGroup(Rc<crate::intrinsics::residue::dirichlet::DrchGroup>),
    /// A matrix algebra, matrix space or R-space (`intrinsics/matrices`).
    Matrices(Rc<crate::intrinsics::matrices::MatParent>),
    /// All sparse matrices over a coefficient ring (`intrinsics/sparse`).
    SparseMatrices(Rc<crate::intrinsics::sparse::SparseParent>),
}

#[derive(Clone)]
pub struct RecFormat {
    pub names: Vec<Sym>,
    /// Optional structure constraint for each field.
    pub types: Vec<Option<Value>>,
}

impl Struct {
    pub fn new(kind: StructKind) -> Rc<Struct> {
        Rc::new(Struct { kind, attrs: RefCell::default(), name: RefCell::default(), aliases: RefCell::default() })
    }
}

pub struct UserObj {
    pub ty: TypeId,
    pub attrs: RefCell<FxHashMap<Sym, Value>>,
    pub id: u64,
}

thread_local! {
    static NEXT_OBJ_ID: Cell<u64> = const { Cell::new(1) };
    static INTEGERS: Rc<Struct> = Struct::new(StructKind::Integers);
    static RATIONALS: Rc<Struct> = Struct::new(StructKind::Rationals);
    static BOOLEANS: Rc<Struct> = Struct::new(StructKind::Booleans);
    static STRINGS: Rc<Struct> = Struct::new(StructKind::Strings);
    static EXTENDED_REALS: Rc<Struct> = Struct::new(StructKind::ExtendedReals);
    /// One real field per precision (in bits).
    static REALS: RefCell<FxHashMap<u64, Rc<Struct>>> = RefCell::default();
    static TIMINGS: Rc<Struct> = Struct::new(StructKind::Reals(TIMING_BITS));
}

/// The precision in bits of the field of timings (Cputime, Realtime), a
/// real field of its own that prints as of precision 15.
pub const TIMING_BITS: u64 = 52;

/// The decimals timings print with.
pub const TIMING_DECIMALS: u32 = 3;

/// Whether `s` is the field of timings.
pub fn is_timing_reals(s: &Struct) -> bool {
    TIMINGS.with(|t| std::ptr::eq(&**t, s))
}

pub fn next_object_id() -> u64 {
    NEXT_OBJ_ID.with(|c| {
        let v = c.get();
        c.set(v + 1);
        v
    })
}

#[derive(Clone)]
pub struct ErrObj {
    pub object: Value,
    /// `"Err"` for system errors, `"ErrUser"` for user errors.
    pub kind: Rc<str>,
    pub position: Option<Rc<str>>,
    pub traceback: Option<Rc<str>>,
    /// How a caught error prints: as it would have been reported.
    pub report: Option<Rc<str>>,
}

pub struct CopElt {
    pub cop: Rc<Struct>,
    pub index: usize,
    pub value: Value,
}

/// A file or pipe opened with `Open`/`POpen`.
pub struct IoObj {
    pub name: String,
    pub mode: String,
    pub kind: IoKind,
    pub state: RefCell<IoState>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum IoKind {
    File,
    Pipe,
    Socket,
}

pub enum IoState {
    Reader { data: Vec<u8>, pos: usize },
    Writer(std::fs::File),
    PipeReader { child: std::process::Child, stdout: std::process::ChildStdout, eof: bool },
    PipeWriter { child: std::process::Child, stdin: Option<std::process::ChildStdin> },
    Closed,
}

impl Drop for IoObj {
    fn drop(&mut self) {
        if let Ok(mut state) = self.state.try_borrow_mut() {
            if let IoState::PipeWriter { child, stdin } = &mut *state {
                stdin.take();
                let _ = child.wait();
            }
        }
    }
}

// ----- constructors and accessors -------------------------------------------

impl Value {
    pub fn integers() -> Value {
        INTEGERS.with(|s| Value::Struct(s.clone()))
    }

    pub fn rationals() -> Value {
        RATIONALS.with(|s| Value::Struct(s.clone()))
    }

    pub fn extended_reals() -> Value {
        EXTENDED_REALS.with(|s| Value::Struct(s.clone()))
    }

    /// The field of timings: its elements print with `TIMING_DECIMALS`
    /// decimals, and so do results in it.
    pub fn timing_reals() -> Value {
        TIMINGS.with(|s| Value::Struct(s.clone()))
    }

    /// The real field with the given precision in bits.
    pub fn reals(bits: u64) -> Value {
        REALS.with(|m| Value::Struct(m.borrow_mut().entry(bits).or_insert_with(|| Struct::new(StructKind::Reals(bits))).clone()))
    }

    pub fn real(x: Real) -> Value {
        Value::Real(Rc::new(RealV::new(x)))
    }

    pub fn complex(re: Real, im: Real) -> Value {
        Value::Complex(Rc::new(ComplexV::new(re, im)))
    }

    pub fn booleans() -> Value {
        BOOLEANS.with(|s| Value::Struct(s.clone()))
    }

    pub fn strings() -> Value {
        STRINGS.with(|s| Value::Struct(s.clone()))
    }

    pub fn structure(kind: StructKind) -> Value {
        Value::Struct(Struct::new(kind))
    }

    pub fn int(i: i64) -> Value {
        Value::Int(Integer::from_i64(i))
    }

    pub fn str(s: &str) -> Value {
        Value::Str(Rc::new(Text::new(s.to_string())))
    }

    pub fn string(s: String) -> Value {
        Value::Str(Rc::new(Text::new(s)))
    }

    pub fn bytes(s: Vec<u8>) -> Value {
        Value::BStr(Rc::new(s))
    }

    /// A rational, normalised to an integer if it is integral... but kept as
    /// a rational field element (Magma distinguishes `2` from `4/2`).
    pub fn rat(q: Rational) -> Value {
        Value::Rat(Rc::new(q))
    }

    pub fn seq(universe: Option<Value>, elems: Vec<Value>) -> Value {
        Value::Seq(Rc::new(SeqEnum::new(universe, elems)))
    }

    pub fn int_seq(elems: impl IntoIterator<Item = Integer>) -> Value {
        Value::seq(Some(Value::integers()), elems.into_iter().map(Value::Int).collect())
    }

    pub fn tuple(elems: Vec<Value>) -> Value {
        Value::Tuple(Rc::new(Tuple { elems, parent: None }))
    }

    pub fn list(elems: Vec<Value>) -> Value {
        Value::List(Rc::new(elems))
    }

    /// Where the name of a value that assignment names is kept: structures
    /// and enumerated aggregates.
    pub fn name_cell(&self) -> Option<&RefCell<Option<Sym>>> {
        match self {
            Value::Struct(s) => Some(&s.name),
            Value::Seq(s) => Some(&s.name.0),
            Value::Set(s) => Some(&s.name.0),
            Value::ISet(s) => Some(&s.name.0),
            Value::MSet(s) => Some(&s.name.0),
            _ => None,
        }
    }

    pub fn is_undef(&self) -> bool {
        matches!(self, Value::Undef)
    }

    pub fn as_struct(&self) -> Option<&StructKind> {
        match self {
            Value::Struct(s) => Some(&s.kind),
            _ => None,
        }
    }

    pub fn is_integers(&self) -> bool {
        matches!(self.as_struct(), Some(StructKind::Integers))
    }

    pub fn is_rationals(&self) -> bool {
        matches!(self.as_struct(), Some(StructKind::Rationals))
    }

    /// The category of this value (not consulting user overrides).
    pub fn type_id(&self) -> TypeId {
        match self {
            Value::Undef => t::ANY,
            Value::Bool(_) => t::BOOL_ELT,
            Value::Int(_) => t::RNG_INT_ELT,
            Value::Rat(_) => t::FLD_RAT_ELT,
            Value::Real(_) => t::FLD_RE_ELT,
            Value::Complex(_) => t::FLD_COM_ELT,
            Value::Str(_) => t::MON_STG_ELT,
            Value::BStr(_) => t::B_STG_ELT,
            Value::Seq(s) if s.fact => t::RNG_INT_ELT_FACT,
            Value::Seq(_) => t::SEQ_ENUM,
            Value::Set(_) => t::SET_ENUM,
            Value::ISet(_) => t::SET_INDX,
            Value::MSet(_) => t::SET_MULTI,
            Value::Formal(f) => {
                if f.is_seq {
                    t::SEQ_FORMAL
                } else {
                    t::SET_FORMAL
                }
            }
            Value::Tuple(_) => t::TUP,
            Value::List(_) => t::LIST,
            Value::Rec(_) => t::REC,
            Value::Assoc(_) => t::ASSOC,
            Value::Func(_) => t::USER_PROGRAM,
            Value::Intr(_) => t::INTRINSIC,
            Value::Map(_) => t::MAP,
            Value::Struct(s) => match &s.kind {
                StructKind::Integers => t::RNG_INT,
                StructKind::Rationals => t::FLD_RAT,
                StructKind::Reals(_) => t::FLD_RE,
                StructKind::Booleans => t::BOOL,
                StructKind::Strings => t::MON_STG,
                StructKind::PowerSet(_) => t::POW_SET_ENUM,
                StructKind::PowerSeq(_) => t::POW_SEQ_ENUM,
                StructKind::PowerISet(_) => t::POW_SET_INDX,
                StructKind::PowerMSet(_) => t::POW_SET_MULTI,
                StructKind::Cartesian(_) => t::SET_CART,
                StructKind::RecFormat(_) => t::REC_FRMT,
                StructKind::Maps(..) => t::POW_MAP,
                StructKind::Coproduct(_) => t::COP,
                StructKind::PowerStructure(_) => t::POW_STR,
                StructKind::Ring(r) => r.type_id(),
                StructKind::SymGroup(_) => t::GRP_PERM,
                StructKind::ExtendedReals => t::EXT_RE,
                StructKind::IntIdeal(_) => t::RNG_INT,
                StructKind::ResIdeal(..) => t::RNG_INT_RES,
                StructKind::UPolIdeal(_) => t::RNG_UPOL,
                StructKind::MPolIdeal(_) => t::RNG_MPOL,
                StructKind::AffIdeal(_) => t::RNG_MPOL_RES,
                StructKind::AbGroup(_) => t::GRP_AB,
                StructKind::Nearfield(n) => n.type_id(),
                StructKind::Automorphisms(_) => t::POW_MAP_AUT,
                StructKind::AlgAss(_) => t::ALG_ASS,
                StructKind::DrchGroup(_) => t::GRP_DRCH,
                StructKind::Matrices(m) => m.type_id(),
                StructKind::SparseMatrices(_) => t::MTRX_SPRS_STR,
            },
            Value::Cat(_) => t::CAT,
            Value::ECat(_) => t::ECAT,
            Value::Err(_) => t::ERR,
            Value::Obj(o) => o.ty,
            Value::CopElt(_) => t::COP_ELT,
            Value::Io(_) => t::IO,
            Value::Elt(e) => e.ring().elt_type(),
            Value::Small(r, _) => r.elt_type(),
            Value::Perm(_) => t::GRP_PERM_ELT,
            Value::AbElt(_) => t::GRP_AB_ELT,
            Value::Nfd(_) => t::NFD_ELT,
            Value::Alg(_) => t::ALG_ASS_ELT,
            Value::Drch(_) => t::GRP_DRCH_ELT,
            Value::Infinity(_) => t::INFTY,
            Value::Mat(m) => m.type_id(),
            Value::Sparse(_) => t::MTRX_SPRS,
        }
    }

    /// Whether this value can be the universe of an aggregate (a structure,
    /// or an aggregate used as a structure).
    pub fn is_structure_like(&self) -> bool {
        matches!(
            self,
            Value::Struct(_) | Value::Seq(_) | Value::Set(_) | Value::ISet(_) | Value::MSet(_) | Value::Formal(_) | Value::Obj(_)
        )
    }
}

// ----- equality, hashing and ordering ---------------------------------------

fn hash_one<T: Hash>(x: &T) -> u64 {
    let mut h = FxHasher::default();
    x.hash(&mut h);
    h.finish()
}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Value::Undef => state.write_u8(0),
            Value::Bool(b) => state.write_u8(if *b { 2 } else { 1 }),
            // Integers and integral rationals must hash alike.
            Value::Int(i) => state.write_u64(i.hash_u64()),
            Value::Rat(q) => state.write_u64(q.hash_u64()),
            Value::Real(r) => state.write_u64(r.x.hash_u64()),
            Value::Complex(c) => {
                state.write_u64(c.re.hash_u64());
                state.write_u64(c.im.hash_u64());
            }
            Value::Str(s) => s.hash(state),
            Value::BStr(s) => {
                state.write_u8(31);
                s.hash(state);
            }
            Value::Seq(s) => {
                state.write_u8(10);
                state.write_usize(s.elems.len());
                for e in &s.elems {
                    e.hash(state);
                }
            }
            Value::Set(s) => {
                state.write_u8(11);
                state.write_usize(s.len());
                state.write_u64(s.iter().map(|e| hash_one(&e)).fold(0u64, |a, b| a.wrapping_add(b)));
            }
            Value::ISet(s) => {
                state.write_u8(12);
                state.write_usize(s.elems.len());
                state.write_u64(s.elems.iter().map(hash_one).fold(0u64, |a, b| a.wrapping_add(b)));
            }
            Value::MSet(s) => {
                state.write_u8(13);
                state.write_u64(s.elems.iter().map(|(e, n)| hash_one(e).wrapping_mul(*n | 1)).fold(0u64, |a, b| a.wrapping_add(b)));
            }
            Value::Tuple(tp) => {
                state.write_u8(14);
                for e in &tp.elems {
                    e.hash(state);
                }
            }
            Value::List(l) => {
                state.write_u8(15);
                for e in l.iter() {
                    e.hash(state);
                }
            }
            Value::Rec(r) => {
                state.write_u8(16);
                for e in &r.fields {
                    e.hash(state);
                }
            }
            Value::Assoc(a) => {
                state.write_u8(17);
                state.write_usize(a.map.len());
            }
            Value::Func(f) => (Rc::as_ptr(f) as usize).hash(state),
            Value::Intr(s) => s.hash(state),
            Value::Map(m) => (Rc::as_ptr(m) as usize).hash(state),
            Value::Struct(s) => struct_hash(s, state),
            Value::Cat(t) => t.hash(state),
            Value::ECat(t) => t.hash(state),
            Value::Err(e) => (Rc::as_ptr(e) as usize).hash(state),
            Value::Obj(o) => o.id.hash(state),
            Value::CopElt(c) => {
                c.index.hash(state);
                c.value.hash(state);
            }
            Value::Formal(f) => (Rc::as_ptr(f) as usize).hash(state),
            Value::Io(f) => (Rc::as_ptr(f) as usize).hash(state),
            Value::Elt(e) => state.write_u64(e.hash_u64()),
            Value::Small(r, x) => {
                r.hash(state);
                state.write_u64(*x);
            }
            Value::Perm(p) => {
                state.write_u8(18);
                p.images.hash(state);
            }
            Value::AbElt(x) => {
                state.write_u8(21);
                x.coords.hash(state);
            }
            Value::Nfd(x) => {
                state.write_u8(22);
                crate::intrinsics::nearfields::as_field_value(x).hash(state);
            }
            Value::Alg(x) => {
                state.write_u8(32);
                crate::intrinsics::algass::hash_key(x).hash(state);
            }
            // Equal characters over different rings hash alike.
            Value::Drch(x) => {
                state.write_u8(26);
                x.modulus().hash(state);
                x.exps.hash(state);
            }
            Value::Infinity(pos) => state.write_u8(if *pos { 19 } else { 20 }),
            Value::Mat(m) => {
                state.write_u8(28);
                state.write_u64(m.hash_u64());
            }
            Value::Sparse(m) => {
                state.write_u8(30);
                state.write_u64(m.hash_u64());
            }
        }
    }
}

fn struct_hash<H: Hasher>(s: &Struct, state: &mut H) {
    match &s.kind {
        StructKind::Integers => state.write_u8(1),
        StructKind::Rationals => state.write_u8(2),
        StructKind::Reals(d) => {
            state.write_u8(9);
            d.hash(state);
        }
        StructKind::Booleans => state.write_u8(3),
        StructKind::Strings => state.write_u8(4),
        StructKind::PowerSet(u) | StructKind::PowerSeq(u) | StructKind::PowerISet(u) | StructKind::PowerMSet(u) => {
            state.write_u8(5);
            if let Some(u) = u {
                u.hash(state);
            }
        }
        StructKind::Cartesian(v) | StructKind::Coproduct(v) => {
            state.write_u8(6);
            for x in v {
                x.hash(state);
            }
        }
        StructKind::RecFormat(f) => {
            state.write_u8(7);
            f.names.hash(state);
        }
        StructKind::Maps(a, b) => {
            state.write_u8(8);
            a.hash(state);
            b.hash(state);
        }
        StructKind::PowerStructure(t) => t.hash(state),
        StructKind::Ring(r) => r.id.hash(state),
        StructKind::SymGroup(n) => {
            state.write_u8(10);
            n.hash(state);
        }
        StructKind::ExtendedReals => state.write_u8(11),
        StructKind::IntIdeal(n) => {
            state.write_u8(12);
            n.hash(state);
        }
        StructKind::ResIdeal(r, d) => {
            state.write_u8(13);
            struct_hash(r, state);
            d.hash(state);
        }
        StructKind::UPolIdeal(g) => {
            state.write_u8(14);
            g.hash_u64().hash(state);
        }
        // Equal ideals may have different bases.
        StructKind::MPolIdeal(id) => {
            state.write_u8(24);
            id.poly_ring().id.hash(state);
        }
        StructKind::AffIdeal(id) => {
            state.write_u8(25);
            struct_hash(&id.algebra, state);
        }
        StructKind::AbGroup(g) => (Rc::as_ptr(g) as usize).hash(state),
        StructKind::Nearfield(n) => {
            state.write_u8(23);
            n.hash_key().hash(state);
        }
        StructKind::Automorphisms(x) => {
            state.write_u8(14);
            x.hash(state);
        }
        StructKind::AlgAss(a) => (Rc::as_ptr(a) as usize).hash(state),
        StructKind::DrchGroup(g) => {
            state.write_u8(27);
            g.modulus.hash(state);
        }
        StructKind::Matrices(m) => {
            state.write_u8(29);
            m.hash_key().hash(state);
        }
        StructKind::SparseMatrices(m) => {
            state.write_u8(31);
            m.hash_key().hash(state);
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        use Value::*;
        match (self, other) {
            (Undef, Undef) => true,
            (Bool(a), Bool(b)) => a == b,
            (Int(a), Int(b)) => a == b,
            (Rat(a), Rat(b)) => a == b,
            (Int(a), Rat(b)) | (Rat(b), Int(a)) => b.is_integral() && b.numerator() == *a,
            (Real(a), Real(b)) => a.x == b.x,
            (Complex(a), Complex(b)) => a.re == b.re && a.im == b.im,
            (Str(a), Str(b)) => a == b,
            (BStr(a), BStr(b)) => a == b,
            (Seq(a), Seq(b)) => Rc::ptr_eq(a, b) || a.elems == b.elems,
            (Set(a), Set(b)) => Rc::ptr_eq(a, b) || (a.len() == b.len() && a.iter().all(|x| b.contains(&x))),
            (ISet(a), ISet(b)) => a.elems.len() == b.elems.len() && a.elems.iter().all(|x| b.elems.contains(x)),
            (MSet(a), MSet(b)) => a.elems.len() == b.elems.len() && a.elems.iter().all(|(x, n)| b.elems.get(x) == Some(n)),
            (Tuple(a), Tuple(b)) => a.elems == b.elems,
            (List(a), List(b)) => a == b,
            (Rec(a), Rec(b)) => Rc::ptr_eq(&a.format, &b.format) && a.fields == b.fields,
            (Assoc(a), Assoc(b)) => a.map.len() == b.map.len() && a.map.iter().all(|(k, v)| b.map.get(k) == Some(v)),
            (Func(a), Func(b)) => Rc::ptr_eq(a, b),
            (Intr(a), Intr(b)) => a == b,
            (Map(a), Map(b)) => Rc::ptr_eq(a, b),
            (Struct(a), Struct(b)) => struct_eq(a, b),
            (Cat(a), Cat(b)) => a == b,
            (ECat(a), ECat(b)) => a == b,
            (Cat(a), ECat(b)) | (ECat(b), Cat(a)) => b.args().is_empty() && b.base() == *a,
            (Err(a), Err(b)) => Rc::ptr_eq(a, b),
            (Obj(a), Obj(b)) => a.id == b.id,
            (CopElt(a), CopElt(b)) => struct_eq(&a.cop, &b.cop) && a.index == b.index && a.value == b.value,
            (Formal(a), Formal(b)) => Rc::ptr_eq(a, b),
            (Io(a), Io(b)) => Rc::ptr_eq(a, b),
            (Elt(a), Elt(b)) => a.same_as(b),
            (Small(r, x), Small(s, y)) => r == s && x == y,
            (Perm(a), Perm(b)) => a.images == b.images,
            (AbElt(a), AbElt(b)) => Rc::ptr_eq(&a.group, &b.group) && a.coords == b.coords,
            (Nfd(a), Nfd(b)) => crate::intrinsics::nearfields::nfd_equal(a, b).unwrap_or(false),
            (Alg(a), Alg(b)) => crate::intrinsics::algass::same(a, b),
            (Drch(a), Drch(b)) => crate::intrinsics::residue::dirichlet::equal(a, b),
            (Infinity(a), Infinity(b)) => a == b,
            (Mat(a), Mat(b)) => a.same_as(b),
            (Sparse(a), Sparse(b)) => a.same_as(b),
            _ => false,
        }
    }
}

impl Eq for Value {}

pub fn struct_eq(a: &Rc<Struct>, b: &Rc<Struct>) -> bool {
    if Rc::ptr_eq(a, b) {
        return true;
    }
    use StructKind::*;
    match (&a.kind, &b.kind) {
        (Integers, Integers) | (Rationals, Rationals) | (Booleans, Booleans) | (Strings, Strings) => true,
        (Reals(x), Reals(y)) => x == y && is_timing_reals(a) == is_timing_reals(b),
        (PowerSet(x), PowerSet(y)) | (PowerSeq(x), PowerSeq(y)) | (PowerISet(x), PowerISet(y)) | (PowerMSet(x), PowerMSet(y)) => x == y,
        (Cartesian(x), Cartesian(y)) | (Coproduct(x), Coproduct(y)) => x == y,
        (RecFormat(_), RecFormat(_)) => false,
        (Maps(a1, b1), Maps(a2, b2)) => a1 == a2 && b1 == b2,
        (PowerStructure(x), PowerStructure(y)) => x == y,
        (Ring(x), Ring(y)) => x.id == y.id,
        (SymGroup(x), SymGroup(y)) => x == y,
        (ExtendedReals, ExtendedReals) => true,
        (IntIdeal(m), IntIdeal(n)) => m == n,
        (ResIdeal(r, d), ResIdeal(s, e)) => struct_eq(r, s) && d == e,
        (UPolIdeal(f), UPolIdeal(g)) => f.same_as(g),
        (MPolIdeal(x), MPolIdeal(y)) => x.same_as(y),
        (AffIdeal(x), AffIdeal(y)) => x.same_as(y),
        (AbGroup(x), AbGroup(y)) => Rc::ptr_eq(x, y),
        (Nearfield(x), Nearfield(y)) => x.same_as(y),
        (Automorphisms(x), Automorphisms(y)) => x == y,
        (AlgAss(x), AlgAss(y)) => Rc::ptr_eq(x, y),
        (DrchGroup(x), DrchGroup(y)) => crate::intrinsics::residue::dirichlet::same_group(x, y),
        (Matrices(x), Matrices(y)) => x.same_as(y),
        (SparseMatrices(x), SparseMatrices(y)) => x.same_as(y),
        _ => false,
    }
}

/// A total order used for canonical printing of sets and for `Sort` on
/// values with a natural order. Returns `None` if the values are not
/// comparable this way.
pub fn natural_cmp(a: &Value, b: &Value) -> Option<Ordering> {
    use Value::*;
    Some(match (a, b) {
        (Int(x), Int(y)) => x.cmp(y),
        (Rat(x), Rat(y)) => x.as_ref().cmp(y),
        (Int(x), Rat(y)) => Rational::from_integer(x).cmp(y),
        (Rat(x), Int(y)) => x.as_ref().cmp(&Rational::from_integer(y)),
        (Real(x), Real(y)) => x.x.cmp(&y.x),
        (Str(x), Str(y)) => x.cmp(y),
        (BStr(x), BStr(y)) => x.cmp(y),
        (Bool(x), Bool(y)) => x.cmp(y),
        (Infinity(x), Infinity(y)) => x.cmp(y),
        (Infinity(x), Int(_) | Rat(_) | Real(_)) => if *x { Ordering::Greater } else { Ordering::Less },
        (Int(_) | Rat(_) | Real(_), Infinity(y)) => if *y { Ordering::Less } else { Ordering::Greater },
        (Elt(x), Elt(y)) => x.natural_cmp(y)?,
        (Small(r, x), Small(s, y)) if r == s => x.cmp(y),
        (Seq(x), Seq(y)) => seq_cmp(&x.elems, &y.elems)?,
        (Tuple(x), Tuple(y)) => seq_cmp(&x.elems, &y.elems)?,
        (Set(x), Set(y)) => match x.len().cmp(&y.len()) {
            Ordering::Equal => {
                let mut xs: Vec<Value> = x.iter().collect();
                let mut ys: Vec<Value> = y.iter().collect();
                sort_values(&mut xs);
                sort_values(&mut ys);
                seq_cmp(&xs, &ys)?
            }
            o => o,
        },
        _ => return None,
    })
}

fn seq_cmp(a: &[Value], b: &[Value]) -> Option<Ordering> {
    for (x, y) in a.iter().zip(b) {
        match natural_cmp(x, y)? {
            Ordering::Equal => {}
            o => return Some(o),
        }
    }
    Some(a.len().cmp(&b.len()))
}

/// Sort values in their natural order if they all have one; otherwise leave
/// them as they are. Returns whether sorting happened.
pub fn sort_values(v: &mut [Value]) -> bool {
    if v.windows(2).any(|w| natural_cmp(&w[0], &w[1]).is_none()) {
        return false;
    }
    v.sort_by(|a, b| natural_cmp(a, b).unwrap_or(Ordering::Equal));
    true
}

/// `sort_values` for the elements of a set, reordering them in place.
pub fn sort_value_set(s: &mut VSet) -> bool {
    if s.iter().zip(s.iter().skip(1)).any(|(a, b)| natural_cmp(a, b).is_none()) {
        return false;
    }
    s.sort_by(|a, b| natural_cmp(a, b).unwrap_or(Ordering::Equal));
    true
}
