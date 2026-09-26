//! Magma's type system: categories (`Cat`), extended types (`ECat`),
//! inheritance (`ISA`), and the type patterns used in intrinsic signatures.

use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::sym::Sym;

/// A category (type) identifier.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct TypeId(pub u32);

macro_rules! builtin_types {
    ($( $konst:ident = $name:literal : [$($parent:ident),*] ),* $(,)?) => {
        #[allow(non_camel_case_types, dead_code)]
        #[repr(u32)]
        enum BuiltinIndex { $($konst),* }
        pub mod t {
            use super::TypeId;
            $( pub const $konst: TypeId = TypeId(super::BuiltinIndex::$konst as u32); )*
        }
        fn builtin_table() -> Vec<(&'static str, Vec<TypeId>)> {
            vec![ $( ($name, vec![$(t::$parent),*]) ),* ]
        }
    };
}

builtin_types! {
    ANY = "Any": [],
    ELT = "Elt": [ANY],
    STR = "Str": [ANY],
    RNG_ELT = "RngElt": [ELT],
    FLD_ELT = "FldElt": [RNG_ELT],
    RNG = "Rng": [STR],
    FLD = "Fld": [RNG],
    RNG_INT = "RngInt": [RNG],
    RNG_INT_ELT = "RngIntElt": [RNG_ELT],
    FLD_RAT = "FldRat": [FLD],
    FLD_RAT_ELT = "FldRatElt": [FLD_ELT],
    BOOL = "Bool": [STR],
    BOOL_ELT = "BoolElt": [ELT],
    MON_STG = "MonStg": [STR],
    MON_STG_ELT = "MonStgElt": [ELT],
    SET = "Set": [ANY],
    SEQ_ENUM = "SeqEnum": [ANY],
    SET_ENUM = "SetEnum": [SET],
    SET_INDX = "SetIndx": [SET],
    SET_MULTI = "SetMulti": [SET],
    SET_FORMAL = "SetFormal": [ANY],
    SEQ_FORMAL = "SeqFormal": [ANY],
    TUP = "Tup": [ANY],
    LIST = "List": [ANY],
    REC = "Rec": [ANY],
    REC_FRMT = "RecFrmt": [STR],
    ASSOC = "Assoc": [ANY],
    PROGRAM = "Program": [ANY],
    USER_PROGRAM = "UserProgram": [PROGRAM],
    INTRINSIC = "Intrinsic": [PROGRAM],
    MAP = "Map": [ANY],
    POW_MAP = "PowMap": [STR],
    POW_SET_ENUM = "PowSetEnum": [STR],
    POW_SEQ_ENUM = "PowSeqEnum": [STR],
    POW_SET_INDX = "PowSetIndx": [STR],
    POW_SET_MULTI = "PowSetMulti": [STR],
    SET_CART = "SetCart": [STR],
    COP = "Cop": [STR],
    COP_ELT = "CopElt": [ELT],
    CAT = "Cat": [ANY],
    ECAT = "ECat": [ANY],
    ERR = "Err": [ANY],
    IO = "IO": [ANY],
    POW_STR = "PowStr": [STR],
    RNG_INT_RES = "RngIntRes": [RNG],
    RNG_INT_RES_ELT = "RngIntResElt": [RNG_ELT],
    FLD_FIN = "FldFin": [FLD],
    FLD_FIN_ELT = "FldFinElt": [FLD_ELT],
    FLD_RE = "FldRe": [FLD],
    FLD_RE_ELT = "FldReElt": [FLD_ELT],
    GRP = "Grp": [STR],
    GRP_ELT = "GrpElt": [ELT],
    GRP_PERM = "GrpPerm": [GRP],
    GRP_PERM_ELT = "GrpPermElt": [GRP_ELT],
    MOD = "Mod": [STR],
    MOD_ELT = "ModElt": [ELT],
    ALG = "Alg": [RNG],
    ALG_ELT = "AlgElt": [RNG_ELT],
    MTRX = "Mtrx": [ELT],
    RNG_UPOL = "RngUPol": [RNG],
    RNG_UPOL_ELT = "RngUPolElt": [RNG_ELT],
    RNG_MPOL = "RngMPol": [RNG],
    RNG_MPOL_ELT = "RngMPolElt": [RNG_ELT],
    FLD_COM = "FldCom": [FLD],
    FLD_COM_ELT = "FldComElt": [FLD_ELT],
    RNG_INT_ELT_FACT = "RngIntEltFact": [SEQ_ENUM],
    INFTY = "Infty": [ANY],
    EXT_RE = "ExtRe": [STR],
    EXT_RE_ELT = "ExtReElt": [ELT],
    GRP_AB = "GrpAb": [GRP],
    GRP_AB_ELT = "GrpAbElt": [GRP_ELT],
    // The chapters being written in parallel add their types each in its
    // own block below, so that their branches merge cleanly.

    // Rational field (#38, #53).
    POW_MAP_AUT = "PowMapAut": [POW_MAP],
    ALG_ASS = "AlgAss": [ALG],
    ALG_ASS_ELT = "AlgAssElt": [ALG_ELT],
    // Dirichlet characters (#48).
    GRP_DRCH = "GrpDrch": [STR],
    GRP_DRCH_ELT = "GrpDrchElt": [ELT],

    // Finite fields and nearfields (#39, #43).
    NFD = "Nfd": [STR],
    NFD_DCK = "NfdDck": [NFD],
    NFD_ZSS = "NfdZss": [NFD],
    NFD_ELT = "NfdElt": [ELT],
    // Matrices and vector spaces (#76, #78).
    ALG_MAT = "AlgMat": [ALG],
    ALG_MAT_ELT = "AlgMatElt": [ALG_ELT, MTRX],
    MOD_MAT_RNG = "ModMatRng": [MOD],
    MOD_MAT_FLD = "ModMatFld": [MOD_MAT_RNG],
    MOD_MAT_RNG_ELT = "ModMatRngElt": [MOD_ELT, MTRX],
    MOD_MAT_FLD_ELT = "ModMatFldElt": [MOD_MAT_RNG_ELT],
    MOD_TUP_RNG = "ModTupRng": [MOD],
    MOD_TUP_FLD = "ModTupFld": [MOD_TUP_RNG],
    MOD_TUP_RNG_ELT = "ModTupRngElt": [MOD_ELT, MTRX],
    MOD_TUP_FLD_ELT = "ModTupFldElt": [MOD_TUP_RNG_ELT],

    // Polynomial rings (#40, #41).
    RNG_UPOL_RES = "RngUPolRes": [RNG],
    RNG_UPOL_RES_ELT = "RngUPolResElt": [RNG_ELT],
    RNG_MPOL_RES = "RngMPolRes": [RNG],
    RNG_MPOL_RES_ELT = "RngMPolResElt": [RNG_ELT],

    // Real and complex fields (#42).

    // Sparse matrices (#77).
    MTRX_SPRS_STR = "MtrxSprsStr": [STR],
    MTRX_SPRS = "MtrxSprs": [MTRX],
}

#[derive(Clone, Debug)]
pub struct TypeInfo {
    pub name: Rc<str>,
    pub parents: Vec<TypeId>,
    /// For structure types, the type of their elements.
    pub elt_type: Option<TypeId>,
    pub user: bool,
    /// Valid attribute names for objects of this type.
    pub attributes: Vec<Sym>,
}

/// The table of all categories, including user-declared ones.
pub struct TypeRegistry {
    types: Vec<TypeInfo>,
    by_name: FxHashMap<Rc<str>, TypeId>,
    /// Known answers of `isa`, an n by n table for n types (0 unknown,
    /// 1 no, 2 yes), dropped when types are added or change.
    isa_cache: RefCell<(usize, Vec<u8>)>,
    /// Bumped whenever a type is added or gains parents.
    version: u64,
}

impl Default for TypeRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeRegistry {
    pub fn new() -> TypeRegistry {
        let mut r = TypeRegistry { types: Vec::new(), by_name: FxHashMap::default(), isa_cache: RefCell::default(), version: 0 };
        for (name, parents) in builtin_table() {
            r.add(name, parents, false);
        }
        let elts = [
            (t::RNG_INT, t::RNG_INT_ELT),
            (t::FLD_RAT, t::FLD_RAT_ELT),
            (t::BOOL, t::BOOL_ELT),
            (t::MON_STG, t::MON_STG_ELT),
            (t::POW_SET_ENUM, t::SET_ENUM),
            (t::POW_SEQ_ENUM, t::SEQ_ENUM),
            (t::POW_SET_INDX, t::SET_INDX),
            (t::POW_SET_MULTI, t::SET_MULTI),
            (t::SET_CART, t::TUP),
            (t::REC_FRMT, t::REC),
            (t::POW_MAP, t::MAP),
            (t::COP, t::COP_ELT),
            (t::RNG_INT_RES, t::RNG_INT_RES_ELT),
            (t::FLD_FIN, t::FLD_FIN_ELT),
            (t::FLD_RE, t::FLD_RE_ELT),
            (t::GRP_PERM, t::GRP_PERM_ELT),
            (t::RNG_UPOL, t::RNG_UPOL_ELT),
            (t::RNG_MPOL, t::RNG_MPOL_ELT),
            (t::FLD_COM, t::FLD_COM_ELT),
            (t::EXT_RE, t::EXT_RE_ELT),
            (t::GRP_AB, t::GRP_AB_ELT),
            // Rational field (#38, #53).
            (t::GRP_DRCH, t::GRP_DRCH_ELT),
            (t::ALG_ASS, t::ALG_ASS_ELT),

            // Finite fields and nearfields (#39, #43).
            (t::NFD, t::NFD_ELT),
            (t::NFD_DCK, t::NFD_ELT),
            (t::NFD_ZSS, t::NFD_ELT),
            // Matrices and vector spaces (#76, #78).
            (t::ALG_MAT, t::ALG_MAT_ELT),
            (t::MOD_MAT_RNG, t::MOD_MAT_RNG_ELT),
            (t::MOD_MAT_FLD, t::MOD_MAT_FLD_ELT),
            (t::MOD_TUP_RNG, t::MOD_TUP_RNG_ELT),
            (t::MOD_TUP_FLD, t::MOD_TUP_FLD_ELT),

            // Polynomial rings (#40, #41).
            (t::RNG_UPOL_RES, t::RNG_UPOL_RES_ELT),
            (t::RNG_MPOL_RES, t::RNG_MPOL_RES_ELT),

            // Real and complex fields (#42).

            // Sparse matrices (#77).
            (t::MTRX_SPRS_STR, t::MTRX_SPRS),
        ];
        for (s, e) in elts {
            r.types[s.0 as usize].elt_type = Some(e);
        }
        r
    }

    fn add(&mut self, name: &str, parents: Vec<TypeId>, user: bool) -> TypeId {
        let id = TypeId(self.types.len() as u32);
        let name: Rc<str> = Rc::from(name);
        self.types.push(TypeInfo { name: name.clone(), parents, elt_type: None, user, attributes: Vec::new() });
        self.by_name.insert(name, id);
        self.version += 1;
        id
    }

    /// Changes whenever the answers of `isa` may change.
    pub fn version(&self) -> u64 {
        self.version
    }

    /// Declare (or re-declare) a user type.
    pub fn declare_user(&mut self, name: &str, parents: Vec<TypeId>) -> TypeId {
        if let Some(&id) = self.by_name.get(name) {
            let info = &mut self.types[id.0 as usize];
            for p in parents {
                if !info.parents.contains(&p) {
                    info.parents.push(p);
                }
            }
            *self.isa_cache.borrow_mut() = (0, Vec::new());
            self.version += 1;
            return id;
        }
        let parents = if parents.is_empty() { vec![t::ANY] } else { parents };
        self.add(name, parents, true)
    }

    pub fn set_elt_type(&mut self, s: TypeId, e: TypeId) {
        self.types[s.0 as usize].elt_type = Some(e);
    }

    pub fn lookup(&self, name: &str) -> Option<TypeId> {
        self.by_name.get(name).copied()
    }

    pub fn info(&self, id: TypeId) -> &TypeInfo {
        &self.types[id.0 as usize]
    }

    pub fn info_mut(&mut self, id: TypeId) -> &mut TypeInfo {
        &mut self.types[id.0 as usize]
    }

    pub fn name(&self, id: TypeId) -> Rc<str> {
        self.types[id.0 as usize].name.clone()
    }

    pub fn all(&self) -> impl Iterator<Item = (TypeId, &TypeInfo)> {
        self.types.iter().enumerate().map(|(i, info)| (TypeId(i as u32), info))
    }

    /// Whether objects of type `a` inherit from type `b`.
    pub fn isa(&self, a: TypeId, b: TypeId) -> bool {
        if a == b || b == t::ANY {
            return true;
        }
        let n = self.types.len();
        let cell = a.0 as usize * n + b.0 as usize;
        {
            let cache = self.isa_cache.borrow();
            if cache.0 == n && cache.1[cell] != 0 {
                return cache.1[cell] == 2;
            }
        }
        let r = self.types[a.0 as usize].parents.iter().any(|&p| self.isa(p, b));
        let mut cache = self.isa_cache.borrow_mut();
        if cache.0 != n {
            *cache = (n, vec![0; n * n]);
        }
        cache.1[cell] = 1 + r as u8;
        r
    }

    /// Add a valid attribute name for a category.
    pub fn add_attribute(&mut self, id: TypeId, name: Sym) {
        let attrs = &mut self.types[id.0 as usize].attributes;
        if !attrs.contains(&name) {
            attrs.push(name);
        }
    }

    /// Whether `name` is a valid attribute for objects of type `id`
    /// (declared on the type or any of its ancestors).
    pub fn has_attribute(&self, id: TypeId, name: Sym) -> bool {
        let info = &self.types[id.0 as usize];
        info.attributes.contains(&name) || info.parents.iter().any(|&p| self.has_attribute(p, name))
    }
}

/// A runtime type value: a category or an extended type.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TypeVal {
    Cat(TypeId),
    Ext(TypeId, Rc<[TypeArg]>),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TypeArg {
    Type(TypeVal),
    Str(Rc<str>),
}

impl TypeVal {
    pub fn base(&self) -> TypeId {
        match self {
            TypeVal::Cat(t) | TypeVal::Ext(t, _) => *t,
        }
    }

    pub fn args(&self) -> &[TypeArg] {
        match self {
            TypeVal::Cat(_) => &[],
            TypeVal::Ext(_, a) => a,
        }
    }

    pub fn display<'a>(&'a self, reg: &'a TypeRegistry) -> TypeDisplay<'a> {
        TypeDisplay(self, reg)
    }
}

pub struct TypeDisplay<'a>(&'a TypeVal, &'a TypeRegistry);

impl fmt::Display for TypeDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.1.name(self.0.base()))?;
        let args = self.0.args();
        if !args.is_empty() {
            write!(f, "[")?;
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                match a {
                    TypeArg::Type(tv) => write!(f, "{}", tv.display(self.1))?,
                    TypeArg::Str(s) => write!(f, "\"{s}\"")?,
                }
            }
            write!(f, "]")?;
        }
        Ok(())
    }
}

/// A pattern in an intrinsic signature.
#[derive(Clone, PartialEq, Debug)]
pub enum TypePat {
    Any,
    Is(TypeId),
    /// `T[A, ...]`: base type and parameter patterns.
    Ext(TypeId, Vec<TypePat>),
    Seq(Option<Box<TypePat>>),
    Set(Option<Box<TypePat>>),
    SetOrSeq(Option<Box<TypePat>>),
    ISet(Option<Box<TypePat>>),
    MSet(Option<Box<TypePat>>),
    Tuple,
}

impl TypePat {
    /// Whether every value matching `self` also matches `other`
    /// (so `self` is at least as specific).
    pub fn leq(&self, other: &TypePat, reg: &TypeRegistry) -> bool {
        use TypePat::*;
        let sub = |a: &Option<Box<TypePat>>, b: &Option<Box<TypePat>>| match (a, b) {
            (_, None) => true,
            (None, Some(_)) => false,
            (Some(x), Some(y)) => x.leq(y, reg),
        };
        match (self, other) {
            (_, Any) => true,
            (Any, _) => false,
            (Is(a), Is(b)) => reg.isa(*a, *b),
            (Ext(a, _), Is(b)) => reg.isa(*a, *b),
            (Ext(a, pa), Ext(b, pb)) => reg.isa(*a, *b) && pa.len() == pb.len() && pa.iter().zip(pb).all(|(x, y)| x.leq(y, reg)),
            (Seq(_), Is(b)) => reg.isa(t::SEQ_ENUM, *b),
            (Set(_), Is(b)) => reg.isa(t::SET_ENUM, *b),
            (ISet(_), Is(b)) => reg.isa(t::SET_INDX, *b),
            (MSet(_), Is(b)) => reg.isa(t::SET_MULTI, *b),
            (Tuple, Is(b)) => reg.isa(t::TUP, *b),
            (Seq(a), Seq(b)) | (Set(a), Set(b)) | (ISet(a), ISet(b)) | (MSet(a), MSet(b)) => sub(a, b),
            (Seq(a) | Set(a), SetOrSeq(b)) => sub(a, b),
            (SetOrSeq(a), SetOrSeq(b)) => sub(a, b),
            (Tuple, Tuple) => true,
            _ => false,
        }
    }

    pub fn describe(&self, reg: &TypeRegistry) -> String {
        use TypePat::*;
        let inner = |p: &Option<Box<TypePat>>| p.as_ref().map(|x| x.describe(reg)).unwrap_or_default();
        match self {
            Any => ".".into(),
            Is(t) => reg.name(*t).to_string(),
            Ext(t, ps) => format!("{}[{}]", reg.name(*t), ps.iter().map(|p| p.describe(reg)).collect::<Vec<_>>().join(", ")),
            Seq(p) => format!("[{}]", inner(p)),
            Set(p) => format!("{{{}}}", inner(p)),
            SetOrSeq(p) => format!("{{[{}]}}", inner(p)),
            ISet(p) => format!("{{@{}@}}", inner(p)),
            MSet(p) => format!("{{*{}*}}", inner(p)),
            Tuple => "<>".into(),
        }
    }
}

/// Parse a type pattern written in signature syntax, e.g. `RngIntElt`,
/// `[RngIntElt]`, `SeqEnum[FldRatElt]`, `{@@}` or `.`.
pub fn parse_type_pat(s: &str, reg: &TypeRegistry) -> Result<TypePat, String> {
    let mut p = PatParser { s: s.as_bytes(), i: 0, reg };
    let r = p.pat()?;
    p.skip_ws();
    if p.i != p.s.len() {
        return Err(format!("trailing input in type '{s}'"));
    }
    Ok(r)
}

struct PatParser<'a> {
    s: &'a [u8],
    i: usize,
    reg: &'a TypeRegistry,
}

impl PatParser<'_> {
    fn skip_ws(&mut self) {
        while self.i < self.s.len() && self.s[self.i] == b' ' {
            self.i += 1;
        }
    }

    fn eat(&mut self, lit: &str) -> bool {
        self.skip_ws();
        if self.s[self.i..].starts_with(lit.as_bytes()) {
            self.i += lit.len();
            true
        } else {
            false
        }
    }

    fn opt_inner(&mut self, close: &str) -> Result<Option<Box<TypePat>>, String> {
        if self.eat(close) {
            return Ok(None);
        }
        let p = self.pat()?;
        if !self.eat(close) {
            return Err(format!("expected '{close}'"));
        }
        Ok(Some(Box::new(p)))
    }

    fn pat(&mut self) -> Result<TypePat, String> {
        self.skip_ws();
        if self.eat(".") {
            return Ok(TypePat::Any);
        }
        if self.eat("{[") {
            return Ok(TypePat::SetOrSeq(self.opt_inner("]}")?));
        }
        if self.eat("{@") {
            return Ok(TypePat::ISet(self.opt_inner("@}")?));
        }
        if self.eat("{*") {
            return Ok(TypePat::MSet(self.opt_inner("*}")?));
        }
        if self.eat("{") {
            return Ok(TypePat::Set(self.opt_inner("}")?));
        }
        if self.eat("[") {
            return Ok(TypePat::Seq(self.opt_inner("]")?));
        }
        if self.eat("<>") {
            return Ok(TypePat::Tuple);
        }
        let start = self.i;
        while self.i < self.s.len() && (self.s[self.i].is_ascii_alphanumeric() || self.s[self.i] == b'_') {
            self.i += 1;
        }
        let name = std::str::from_utf8(&self.s[start..self.i]).unwrap();
        if name.is_empty() {
            return Err("expected a type name".into());
        }
        let id = self.reg.lookup(name).ok_or_else(|| format!("unknown type '{name}'"))?;
        if self.eat("[") {
            let mut ps = vec![self.pat()?];
            while self.eat(",") {
                ps.push(self.pat()?);
            }
            if !self.eat("]") {
                return Err("expected ']'".into());
            }
            return Ok(TypePat::Ext(id, ps));
        }
        if id == t::ANY {
            return Ok(TypePat::Any);
        }
        Ok(TypePat::Is(id))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn isa_and_patterns() {
        let r = TypeRegistry::new();
        assert!(r.isa(t::RNG_INT_ELT, t::RNG_ELT));
        assert!(r.isa(t::FLD_RAT, t::FLD));
        assert!(r.isa(t::FLD_RAT, t::RNG));
        assert!(!r.isa(t::RNG_INT_ELT, t::FLD_ELT));
        let a = parse_type_pat("[RngIntElt]", &r).unwrap();
        let b = parse_type_pat("SeqEnum", &r).unwrap();
        let c = parse_type_pat("[]", &r).unwrap();
        assert!(a.leq(&c, &r) && c.leq(&b, &r) && !b.leq(&a, &r));
        assert_eq!(parse_type_pat("{@ RngIntElt @}", &r).unwrap().describe(&r), "{@RngIntElt@}");
        assert!(parse_type_pat("Nope", &r).is_err());
    }
}
