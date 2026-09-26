//! Safe wrappers around FLINT's generic rings (`gr`).
//!
//! A [`Ctx`] describes a ring (integers modulo n, a finite field, a
//! polynomial ring over another context, floating-point reals, ...) and an
//! [`Elem`] is an element of one. Every operation that can fail returns a
//! [`GrResult`]: `Domain` when the operation is mathematically undefined
//! (dividing by a non-unit, say) and `Unable` when FLINT has no algorithm
//! for it.
//!
//! Contexts live behind `Rc` at a fixed address, because FLINT contexts
//! may point at each other (a polynomial ring refers to its coefficient
//! ring). Elements keep their context alive.

use std::cell::UnsafeCell;
use std::ffi::{CString, c_char, c_int, c_void};
use std::ptr::NonNull;
use std::rc::Rc;

use flint3_sys as sys;

use crate::{Integer, Rational, Real, take_flint_string};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GrError {
    /// The operation is not defined for these arguments.
    Domain,
    /// FLINT cannot perform the operation.
    Unable,
}

pub type GrResult<T> = Result<T, GrError>;

pub(crate) fn check(status: c_int) -> GrResult<()> {
    if status == 0 {
        Ok(())
    } else if status & 1 != 0 {
        Err(GrError::Domain)
    } else {
        Err(GrError::Unable)
    }
}

/// A three-valued truth value, as returned by FLINT predicates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Truth {
    True,
    False,
    Unknown,
}

impl Truth {
    pub(crate) fn from_raw(t: sys::truth_t) -> Truth {
        match t {
            sys::truth_t_T_TRUE => Truth::True,
            sys::truth_t_T_FALSE => Truth::False,
            _ => Truth::Unknown,
        }
    }

    pub fn known(self) -> Option<bool> {
        match self {
            Truth::True => Some(true),
            Truth::False => Some(false),
            Truth::Unknown => None,
        }
    }
}

/// Set an `arf` to a real rounded to `prec` bits (NaN and infinities map
/// to FLINT's special values; the sign of zero is lost).
unsafe fn set_arf_from_real(a: *mut sys::arf_struct, x: &Real, prec: u64) {
    unsafe {
        crate::mpfr::arf_set_mpfr(a, x.raw());
        sys::arf_set_round(a, a, prec as sys::slong, sys::arf_rnd_t_ARF_RND_NEAR);
    }
}

/// A real of `prec` bits from an `arf`.
unsafe fn real_from_arf(a: *const sys::arf_struct, prec: u64) -> Real {
    let mut r = Real::zero(prec);
    unsafe { crate::mpfr::arf_to_mpfr(r.raw_mut(), a) };
    r
}

// Constructors that FLINT exports but does not declare in its headers.
unsafe extern "C" {
    fn gr_ctx_init_fq_nmod_modulus_nmod_poly(ctx: *mut sys::gr_ctx_struct, modulus: *const sys::nmod_poly_struct, var: *const c_char) -> c_int;
    fn gr_ctx_init_fq_modulus_fmpz_mod_poly(
        ctx: *mut sys::gr_ctx_struct,
        modulus: *const sys::fmpz_mod_poly_struct,
        mod_ctx: *mut sys::fmpz_mod_ctx_struct,
        var: *const c_char,
    ) -> c_int;
}

/// Monomial orderings supported by FLINT's multivariate polynomials.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MonomialOrder {
    Lex,
    DegLex,
    DegRevLex,
}

/// What kind of ring a context is.
#[derive(Clone, Debug)]
pub enum CtxKind {
    Integers,
    Rationals,
    /// Integers modulo a word-sized modulus.
    Nmod(u64),
    /// Integers modulo an arbitrary modulus.
    FmpzMod(Integer),
    /// A finite field of order `p^degree` with Zech logarithm representation.
    FqZech { p: u64, degree: u64 },
    /// A finite field with word-sized characteristic.
    FqNmod { p: u64, degree: u64 },
    /// A finite field with large characteristic.
    Fq { p: Integer, degree: u64 },
    /// A finite field of small characteristic with its elements packed
    /// into words (see `packed`).
    FqPacked { p: u64, degree: u64 },
    /// Dense univariate polynomials over the base context.
    Poly,
    /// Sparse multivariate polynomials over the base context.
    MPoly { nvars: usize, order: MonomialOrder },
    /// Floating-point reals with the given precision in bits.
    RealFloat(u64),
    /// Floating-point complex numbers with the given precision in bits.
    ComplexFloat(u64),
}

pub struct Ctx {
    raw: Box<UnsafeCell<sys::gr_ctx_struct>>,
    kind: CtxKind,
    base: Option<Rc<Ctx>>,
}

impl Drop for Ctx {
    fn drop(&mut self) {
        unsafe { sys::gr_ctx_clear(self.raw.get()) };
    }
}

impl std::fmt::Debug for Ctx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Ctx({:?})", self.kind)
    }
}

fn new_raw() -> Box<UnsafeCell<sys::gr_ctx_struct>> {
    Box::new(UnsafeCell::new(sys::gr_ctx_struct::default()))
}

thread_local! {
    static ZZ: Rc<Ctx> = Ctx::build(CtxKind::Integers, None, |c| unsafe { sys::gr_ctx_init_fmpz(c) });
    static QQ: Rc<Ctx> = Ctx::build(CtxKind::Rationals, None, |c| unsafe { sys::gr_ctx_init_fmpq(c) });
}

impl Ctx {
    fn build(kind: CtxKind, base: Option<Rc<Ctx>>, init: impl FnOnce(*mut sys::gr_ctx_struct)) -> Rc<Ctx> {
        let raw = new_raw();
        init(raw.get());
        Rc::new(Ctx { raw, kind, base })
    }

    /// Like `build`, for initialisers that can fail (in which case nothing
    /// needs to be cleared).
    pub(crate) fn try_build(kind: CtxKind, base: Option<Rc<Ctx>>, init: impl FnOnce(*mut sys::gr_ctx_struct) -> c_int) -> GrResult<Rc<Ctx>> {
        let raw = new_raw();
        check(init(raw.get()))?;
        Ok(Rc::new(Ctx { raw, kind, base }))
    }

    pub fn integers() -> Rc<Ctx> {
        ZZ.with(Rc::clone)
    }

    pub fn rationals() -> Rc<Ctx> {
        QQ.with(Rc::clone)
    }

    /// The integers modulo `n` (n ≥ 1).
    pub fn residue_ring(n: &Integer) -> Rc<Ctx> {
        match n.to_u64() {
            Some(m) if m >= 1 => Ctx::build(CtxKind::Nmod(m), None, |c| {
                unsafe { sys::gr_ctx_init_nmod(c, m as sys::ulong) };
            }),
            _ => Ctx::build(CtxKind::FmpzMod(n.clone()), None, |c| unsafe { sys::gr_ctx_init_fmpz_mod(c, n.raw_ptr()) }),
        }
    }

    /// The finite field `F_p[x]/(f)` for a monic irreducible `f` given by its
    /// coefficients (constant term first). With `zech`, a table of Zech
    /// logarithms is used if `f` is primitive; that fails with `Domain`
    /// otherwise. Without, GF(p^n) for n >= 2 packs its elements into
    /// words (p = 2) or lanes (odd p < 2^16) when it can (see `packed`).
    pub fn finite_field(p: &Integer, modulus: &[Integer], zech: bool) -> GrResult<Rc<Ctx>> {
        if let Some(pw) = p.to_u64().filter(|&pw| !zech && pw < 1 << 16 && modulus.len() > 2) {
            let cs: Vec<u64> = modulus.iter().map(|c| c.mod_u64(pw)).collect();
            match Ctx::packed_field(pw, &cs) {
                Err(GrError::Unable) => {}
                r => return r,
            }
        }
        Ctx::flint_field(p, modulus, zech)
    }

    /// `finite_field` with FLINT's own representations.
    pub(crate) fn flint_field(p: &Integer, modulus: &[Integer], zech: bool) -> GrResult<Rc<Ctx>> {
        let degree = modulus.len().saturating_sub(1) as u64;
        let var = CString::new("a").unwrap();
        if let Some(pw) = p.to_u64() {
            let mut poly = sys::nmod_poly_struct::default();
            unsafe {
                sys::nmod_poly_init(&mut poly, pw as sys::ulong);
                for (i, c) in modulus.iter().enumerate() {
                    let r = c.div_rem_euclid(&Integer::from_u64(pw)).and_then(|(_, r)| r.to_u64()).unwrap_or(0);
                    sys::nmod_poly_set_coeff_ui(&mut poly, i as sys::slong, r as sys::ulong);
                }
            }
            let result = if zech {
                Ctx::try_build(CtxKind::FqZech { p: pw, degree }, None, |c| unsafe { crate::fq::init_fq_zech(c, &poly, var.as_ptr()) })
            } else {
                Ctx::try_build(CtxKind::FqNmod { p: pw, degree }, None, |c| unsafe { gr_ctx_init_fq_nmod_modulus_nmod_poly(c, &poly, var.as_ptr()) })
            };
            unsafe { sys::nmod_poly_clear(&mut poly) };
            result
        } else {
            if zech {
                return Err(GrError::Unable);
            }
            let mut mctx = sys::fmpz_mod_ctx_struct::default();
            let mut poly = sys::fmpz_mod_poly_struct::default();
            unsafe {
                sys::fmpz_mod_ctx_init(&mut mctx, p.raw_ptr());
                sys::fmpz_mod_poly_init(&mut poly, &mctx);
                for (i, c) in modulus.iter().enumerate() {
                    sys::fmpz_mod_poly_set_coeff_fmpz(&mut poly, i as sys::slong, c.raw_ptr(), &mctx);
                }
            }
            let result = Ctx::try_build(CtxKind::Fq { p: p.clone(), degree }, None, |c| unsafe {
                gr_ctx_init_fq_modulus_fmpz_mod_poly(c, &poly, &mut mctx, var.as_ptr())
            });
            unsafe {
                sys::fmpz_mod_poly_clear(&mut poly, &mctx);
                sys::fmpz_mod_ctx_clear(&mut mctx);
            }
            result
        }
    }

    /// Dense univariate polynomials over `base`.
    pub fn poly(base: &Rc<Ctx>) -> Rc<Ctx> {
        Ctx::build(CtxKind::Poly, Some(base.clone()), |c| unsafe { sys::gr_ctx_init_gr_poly(c, base.ptr()) })
    }

    /// Multivariate polynomials in `nvars` variables over `base`.
    pub fn mpoly(base: &Rc<Ctx>, nvars: usize, order: MonomialOrder) -> Rc<Ctx> {
        let ord = match order {
            MonomialOrder::Lex => sys::ordering_t_ORD_LEX,
            MonomialOrder::DegLex => sys::ordering_t_ORD_DEGLEX,
            MonomialOrder::DegRevLex => sys::ordering_t_ORD_DEGREVLEX,
        };
        Ctx::build(CtxKind::MPoly { nvars, order }, Some(base.clone()), |c| unsafe { sys::gr_mpoly_ctx_init(c, base.ptr(), nvars as sys::slong, ord) })
    }

    /// Floating-point reals with `prec` bits.
    pub fn real_float(prec: u64) -> Rc<Ctx> {
        Ctx::build(CtxKind::RealFloat(prec), None, |c| unsafe { sys::gr_ctx_init_real_float_arf(c, prec as sys::slong) })
    }

    /// Floating-point complex numbers with `prec` bits.
    pub fn complex_float(prec: u64) -> Rc<Ctx> {
        Ctx::build(CtxKind::ComplexFloat(prec), None, |c| unsafe { sys::gr_ctx_init_complex_float_acf(c, prec as sys::slong) })
    }

    pub fn ptr(&self) -> *mut sys::gr_ctx_struct {
        self.raw.get()
    }

    pub fn kind(&self) -> &CtxKind {
        &self.kind
    }

    /// The coefficient ring of a polynomial ring.
    pub fn base(&self) -> Option<&Rc<Ctx>> {
        self.base.as_ref()
    }

    pub fn elem_size(&self) -> usize {
        unsafe { (*self.ptr()).sizeof_elem as usize }
    }

    /// Whether the elements are plain words, all zero for zero and with
    /// nothing to free (packed finite fields): `Elem` makes, copies and
    /// drops them without calling FLINT.
    fn plain(&self) -> bool {
        matches!(self.kind, CtxKind::FqPacked { .. })
    }

    pub fn is_field(&self) -> Truth {
        Truth::from_raw(unsafe { sys::gr_ctx_is_field(self.ptr()) })
    }

    pub fn is_integral_domain(&self) -> Truth {
        Truth::from_raw(unsafe { sys::gr_ctx_is_integral_domain(self.ptr()) })
    }

    /// The order of a finite field context.
    pub fn fq_order(&self) -> Option<Integer> {
        let mut z = Integer::zero();
        check(unsafe { sys::gr_ctx_fq_order(z.raw_mut_ptr(), self.ptr()) }).ok()?;
        Some(z)
    }

    /// The generator of the ring (the variable of a polynomial ring, the
    /// root of the modulus of a finite field).
    pub fn generator(self: &Rc<Ctx>) -> GrResult<Elem> {
        let mut e = Elem::new(self);
        check(unsafe { sys::gr_gen(e.as_mut_ptr(), self.ptr()) })?;
        Ok(e)
    }

    /// The generators of a multivariate polynomial ring.
    pub fn mpoly_gen(self: &Rc<Ctx>, i: usize) -> GrResult<Elem> {
        let mut e = Elem::new(self);
        check(unsafe { sys::gr_mpoly_gen(e.as_mut_ptr().cast(), i as sys::slong, self.ptr()) })?;
        Ok(e)
    }
}

/// Elements of up to this many words (integers mod n, finite field
/// elements, polynomials, floats) are stored inside the `Elem`, so making
/// one does not allocate; larger ones go on the heap. FLINT elements hold
/// no pointers into themselves, so they can be moved.
const INLINE_WORDS: usize = 8;

/// An element of a generic ring.
pub struct Elem {
    ctx: Rc<Ctx>,
    data: Data,
}

enum Data {
    Inline([u64; INLINE_WORDS]),
    Heap(NonNull<c_void>),
}

impl Drop for Elem {
    fn drop(&mut self) {
        match self.data {
            Data::Inline(_) if self.ctx.plain() => {}
            Data::Inline(_) => unsafe { sys::gr_clear(self.as_mut_ptr(), self.ctx.ptr()) },
            Data::Heap(p) => unsafe { sys::gr_heap_clear(p.as_ptr(), self.ctx.ptr()) },
        }
    }
}

impl Clone for Elem {
    fn clone(&self) -> Elem {
        if let (true, Data::Inline(w)) = (self.ctx.plain(), &self.data) {
            return Elem { ctx: self.ctx.clone(), data: Data::Inline(*w) };
        }
        let mut e = Elem::new(&self.ctx);
        let st = unsafe { sys::gr_set(e.as_mut_ptr(), self.as_ptr(), self.ctx.ptr()) };
        assert_eq!(st, 0, "gr_set failed");
        e
    }
}

impl std::fmt::Debug for Elem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_flint_string())
    }
}

macro_rules! binary_ops {
    ($($name:ident => $f:ident),* $(,)?) => {
        $(
            pub fn $name(&self, other: &Elem) -> GrResult<Elem> {
                debug_assert!(Rc::ptr_eq(&self.ctx, &other.ctx));
                let mut r = Elem::new(&self.ctx);
                check(unsafe { sys::$f(r.as_mut_ptr(), self.as_ptr(), other.as_ptr(), self.ctx.ptr()) })?;
                Ok(r)
            }
        )*
    };
}

macro_rules! unary_ops {
    ($($name:ident => $f:ident),* $(,)?) => {
        $(
            pub fn $name(&self) -> GrResult<Elem> {
                let mut r = Elem::new(&self.ctx);
                check(unsafe { sys::$f(r.as_mut_ptr(), self.as_ptr(), self.ctx.ptr()) })?;
                Ok(r)
            }
        )*
    };
}

macro_rules! predicates {
    ($($name:ident => $f:ident),* $(,)?) => {
        $(
            pub fn $name(&self) -> Truth {
                Truth::from_raw(unsafe { sys::$f(self.as_ptr(), self.ctx.ptr()) })
            }
        )*
    };
}

impl Elem {
    /// The zero element of `ctx`.
    pub fn new(ctx: &Rc<Ctx>) -> Elem {
        if ctx.elem_size() <= INLINE_WORDS * 8 {
            let mut e = Elem { ctx: ctx.clone(), data: Data::Inline([0; INLINE_WORDS]) };
            if !ctx.plain() {
                unsafe { sys::gr_init(e.as_mut_ptr(), ctx.ptr()) };
            }
            return e;
        }
        let p = unsafe { sys::gr_heap_init(ctx.ptr()) };
        Elem { ctx: ctx.clone(), data: Data::Heap(NonNull::new(p).expect("gr_heap_init returned null")) }
    }

    pub fn zero(ctx: &Rc<Ctx>) -> Elem {
        Elem::new(ctx)
    }

    pub fn one(ctx: &Rc<Ctx>) -> GrResult<Elem> {
        let mut e = Elem::new(ctx);
        check(unsafe { sys::gr_one(e.as_mut_ptr(), ctx.ptr()) })?;
        Ok(e)
    }

    pub fn from_i64(ctx: &Rc<Ctx>, v: i64) -> GrResult<Elem> {
        let mut e = Elem::new(ctx);
        check(unsafe { sys::gr_set_si(e.as_mut_ptr(), v as sys::slong, ctx.ptr()) })?;
        Ok(e)
    }

    /// An element of an integers-mod-n context from its residue `v < n`.
    pub fn from_word(ctx: &Rc<Ctx>, v: u64) -> Elem {
        let mut e = Elem::new(ctx);
        let st = unsafe { sys::gr_set_ui(e.as_mut_ptr(), v as sys::ulong, ctx.ptr()) };
        assert_eq!(st, 0, "gr_set_ui failed");
        e
    }

    /// The residue of an element of an integers-mod-n context.
    pub fn to_word(&self) -> Option<u64> {
        match self.ctx.kind {
            CtxKind::Nmod(_) => Some(unsafe { *self.as_ptr().cast::<sys::ulong>() } as u64),
            _ => None,
        }
    }

    pub fn from_integer(ctx: &Rc<Ctx>, v: &Integer) -> GrResult<Elem> {
        let mut e = Elem::new(ctx);
        check(unsafe { sys::gr_set_fmpz(e.as_mut_ptr(), v.raw_ptr(), ctx.ptr()) })?;
        Ok(e)
    }

    pub fn from_rational(ctx: &Rc<Ctx>, v: &Rational) -> GrResult<Elem> {
        let mut e = Elem::new(ctx);
        check(unsafe { sys::gr_set_fmpq(e.as_mut_ptr(), v.raw_ptr(), ctx.ptr()) })?;
        Ok(e)
    }

    /// A real number as an element of a real floating-point context.
    pub fn from_real(ctx: &Rc<Ctx>, x: &Real) -> GrResult<Elem> {
        let mut e = Elem::new(ctx);
        match ctx.kind {
            // acf = (real arf, imaginary arf); the imaginary part stays zero.
            CtxKind::RealFloat(prec) | CtxKind::ComplexFloat(prec) => unsafe { set_arf_from_real(e.as_mut_ptr().cast(), x, prec) },
            _ => {
                let q = x.to_rational().ok_or(GrError::Domain)?;
                return Elem::from_rational(ctx, &q);
            }
        }
        Ok(e)
    }

    /// The value of an element of a real floating-point context.
    pub fn to_real(&self) -> Option<Real> {
        match self.ctx.kind {
            CtxKind::RealFloat(prec) => Some(unsafe { real_from_arf(self.as_ptr().cast(), prec) }),
            _ => None,
        }
    }

    /// The real and imaginary parts of a complex floating-point element.
    pub fn to_complex_parts(&self) -> Option<(Real, Real)> {
        match self.ctx.kind {
            CtxKind::ComplexFloat(prec) => {
                let p = self.as_ptr() as *const sys::arf_struct;
                Some(unsafe { (real_from_arf(p, prec), real_from_arf(p.add(1), prec)) })
            }
            _ => None,
        }
    }

    /// A complex floating-point element from its parts.
    pub fn from_complex_parts(ctx: &Rc<Ctx>, re: &Real, im: &Real) -> GrResult<Elem> {
        let CtxKind::ComplexFloat(prec) = ctx.kind else { return Err(GrError::Domain) };
        let mut e = Elem::new(ctx);
        let p = e.as_mut_ptr() as *mut sys::arf_struct;
        unsafe {
            set_arf_from_real(p, re, prec);
            set_arf_from_real(p.add(1), im, prec);
        }
        Ok(e)
    }

    /// Convert an element of another ring into `ctx`, if FLINT knows how.
    pub fn from_other(ctx: &Rc<Ctx>, x: &Elem) -> GrResult<Elem> {
        let mut e = Elem::new(ctx);
        check(unsafe { sys::gr_set_other(e.as_mut_ptr(), x.as_ptr(), x.ctx.ptr(), ctx.ptr()) })?;
        Ok(e)
    }

    pub fn ctx(&self) -> &Rc<Ctx> {
        &self.ctx
    }

    #[inline]
    pub fn as_ptr(&self) -> *const c_void {
        match &self.data {
            Data::Inline(w) => w.as_ptr().cast(),
            Data::Heap(p) => p.as_ptr(),
        }
    }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut c_void {
        match &mut self.data {
            Data::Inline(w) => w.as_mut_ptr().cast(),
            Data::Heap(p) => p.as_ptr(),
        }
    }

    binary_ops! {
        add => gr_add,
        sub => gr_sub,
        div => gr_div,
        divexact => gr_divexact,
        euclidean_div => gr_euclidean_div,
        euclidean_rem => gr_euclidean_rem,
        gcd => gr_gcd,
        lcm => gr_lcm,
    }

    unary_ops! {
        neg => gr_neg,
        inv => gr_inv,
        sqr => gr_sqr,
        sqrt => gr_sqrt,
        abs => gr_abs,
        floor => gr_floor,
        ceil => gr_ceil,
        trunc => gr_trunc,
        nint => gr_nint,
        conj => gr_conj,
        re => gr_re,
        im => gr_im,
    }

    predicates! {
        is_zero => gr_is_zero,
        is_one => gr_is_one,
        is_neg_one => gr_is_neg_one,
        is_invertible => gr_is_invertible,
        is_square => gr_is_square,
    }

    pub fn mul(&self, other: &Elem) -> GrResult<Elem> {
        if let Some(r) = crate::floatpoly::mul(self, other) {
            return r;
        }
        debug_assert!(Rc::ptr_eq(&self.ctx, &other.ctx));
        let mut r = Elem::new(&self.ctx);
        check(unsafe { sys::gr_mul(r.as_mut_ptr(), self.as_ptr(), other.as_ptr(), self.ctx.ptr()) })?;
        Ok(r)
    }

    pub fn equal(&self, other: &Elem) -> Truth {
        Truth::from_raw(unsafe { sys::gr_equal(self.as_ptr(), other.as_ptr(), self.ctx.ptr()) })
    }

    pub fn divides(&self, other: &Elem) -> Truth {
        Truth::from_raw(unsafe { sys::gr_divides(self.as_ptr(), other.as_ptr(), self.ctx.ptr()) })
    }

    /// Quotient and remainder of Euclidean division.
    pub fn euclidean_divrem(&self, other: &Elem) -> GrResult<(Elem, Elem)> {
        let mut q = Elem::new(&self.ctx);
        let mut r = Elem::new(&self.ctx);
        check(unsafe { sys::gr_euclidean_divrem(q.as_mut_ptr(), r.as_mut_ptr(), self.as_ptr(), other.as_ptr(), self.ctx.ptr()) })?;
        Ok((q, r))
    }

    pub fn pow_i64(&self, e: i64) -> GrResult<Elem> {
        let mut r = Elem::new(&self.ctx);
        check(unsafe { sys::gr_pow_si(r.as_mut_ptr(), self.as_ptr(), e as sys::slong, self.ctx.ptr()) })?;
        Ok(r)
    }

    pub fn pow(&self, e: &Integer) -> GrResult<Elem> {
        if let Some(r) = crate::floatpoly::pow(self, e) {
            return r;
        }
        let mut r = Elem::new(&self.ctx);
        check(unsafe { sys::gr_pow_fmpz(r.as_mut_ptr(), self.as_ptr(), e.raw_ptr(), self.ctx.ptr()) })?;
        Ok(r)
    }

    pub fn mul_integer(&self, n: &Integer) -> GrResult<Elem> {
        let mut r = Elem::new(&self.ctx);
        check(unsafe { sys::gr_mul_fmpz(r.as_mut_ptr(), self.as_ptr(), n.raw_ptr(), self.ctx.ptr()) })?;
        Ok(r)
    }

    /// Compare in an ordered ring: -1, 0 or 1.
    pub fn cmp(&self, other: &Elem) -> GrResult<i32> {
        let mut r: c_int = 0;
        check(unsafe { sys::gr_cmp(&mut r, self.as_ptr(), other.as_ptr(), self.ctx.ptr()) })?;
        Ok(r.signum())
    }

    pub fn to_integer(&self) -> GrResult<Integer> {
        let mut z = Integer::zero();
        check(unsafe { sys::gr_get_fmpz(z.raw_mut_ptr(), self.as_ptr(), self.ctx.ptr()) })?;
        Ok(z)
    }

    pub fn to_rational(&self) -> GrResult<Rational> {
        let mut q = Rational::zero();
        check(unsafe { sys::gr_get_fmpq(q.raw_mut_ptr(), self.as_ptr(), self.ctx.ptr()) })?;
        Ok(q)
    }

    /// FLINT's own rendering (for debugging; calyx prints in Magma's format).
    pub fn to_flint_string(&self) -> String {
        let mut s: *mut c_char = std::ptr::null_mut();
        let st = unsafe { sys::gr_get_str(&mut s, self.as_ptr(), self.ctx.ptr()) };
        if st != 0 || s.is_null() {
            return "<?>".to_string();
        }
        unsafe { take_flint_string(s) }
    }

    // ----- finite fields -------------------------------------------------

    /// The multiplicative order of a nonzero finite field element.
    pub fn fq_multiplicative_order(&self) -> GrResult<Integer> {
        let mut z = Integer::zero();
        check(unsafe { sys::gr_fq_multiplicative_order(z.raw_mut_ptr(), self.as_ptr(), self.ctx.ptr()) })?;
        Ok(z)
    }

    /// `x^(p^k)`.
    pub fn fq_frobenius(&self, k: i64) -> GrResult<Elem> {
        let mut r = Elem::new(&self.ctx);
        check(unsafe { sys::gr_fq_frobenius(r.as_mut_ptr(), self.as_ptr(), k as sys::slong, self.ctx.ptr()) })?;
        Ok(r)
    }

    /// The absolute norm to the prime field.
    pub fn fq_norm(&self) -> GrResult<Integer> {
        let mut z = Integer::zero();
        check(unsafe { sys::gr_fq_norm(z.raw_mut_ptr(), self.as_ptr(), self.ctx.ptr()) })?;
        Ok(z)
    }

    /// The absolute trace to the prime field.
    pub fn fq_trace(&self) -> GrResult<Integer> {
        let mut z = Integer::zero();
        check(unsafe { sys::gr_fq_trace(z.raw_mut_ptr(), self.as_ptr(), self.ctx.ptr()) })?;
        Ok(z)
    }

    /// The Zech logarithm of a finite field element (its power of the
    /// generator), or `None` for zero or other representations.
    pub fn zech_log(&self) -> Option<u64> {
        match self.ctx.kind {
            CtxKind::FqZech { p, degree } => {
                let v = unsafe { (*(self.as_ptr() as *const sys::fq_zech_struct)).value } as u64;
                let qm1 = (p as u128).pow(degree as u32) - 1;
                if v as u128 == qm1 { None } else { Some(v) }
            }
            _ => None,
        }
    }

    /// The coordinates of a finite field element in the power basis of its
    /// generator, as integers in `[0, p)`, constant term first, padded to the
    /// degree.
    pub fn fq_coords(&self) -> Vec<Integer> {
        match self.ctx.kind {
            CtxKind::FqZech { degree, .. } => {
                // Go through the underlying fq_nmod representation.
                let zctx = unsafe { *((*self.ctx.ptr()).data.as_ptr() as *const *mut sys::fq_zech_ctx_struct) };
                let nctx = unsafe { (*zctx).fq_nmod_ctx };
                let mut a = sys::nmod_poly_struct::default();
                unsafe {
                    sys::fq_nmod_init(&mut a, nctx);
                    sys::fq_zech_get_fq_nmod(&mut a, self.as_ptr() as *const sys::fq_zech_struct, zctx);
                }
                let out = nmod_coeffs(&a, degree as usize);
                unsafe { sys::fq_nmod_clear(&mut a, nctx) };
                out
            }
            CtxKind::FqNmod { degree, .. } => nmod_coeffs(unsafe { &*(self.as_ptr() as *const sys::nmod_poly_struct) }, degree as usize),
            CtxKind::FqPacked { .. } => crate::packed::coords(self).into_iter().map(Integer::from_u64).collect(),
            CtxKind::Fq { degree, .. } => {
                let f = unsafe { &*(self.as_ptr() as *const sys::fmpz_poly_struct) };
                let mut out = Vec::with_capacity(degree as usize);
                for i in 0..degree as usize {
                    let mut z = Integer::zero();
                    if (i as i64) < f.length as i64 {
                        unsafe { sys::fmpz_set(z.raw_mut_ptr(), f.coeffs.add(i)) };
                    }
                    out.push(z);
                }
                out
            }
            _ => Vec::new(),
        }
    }

    /// The value of a finite field element lying in the prime field.
    pub fn fq_prime_value(&self) -> Option<Integer> {
        let c = self.fq_coords();
        if c.iter().skip(1).all(Integer::is_zero) { Some(c.into_iter().next().unwrap_or_default()) } else { None }
    }

    /// Build a finite field element from coordinates in the power basis.
    pub fn fq_from_coords(ctx: &Rc<Ctx>, coords: &[Integer]) -> GrResult<Elem> {
        let g = ctx.generator()?;
        let mut acc = Elem::zero(ctx);
        let mut pw = Elem::one(ctx)?;
        for c in coords {
            if !c.is_zero() {
                acc = acc.add(&pw.mul_integer(c)?)?;
            }
            pw = pw.mul(&g)?;
        }
        Ok(acc)
    }

    // ----- univariate polynomials ------------------------------------------

    fn poly_raw(&self) -> &sys::gr_poly_struct {
        debug_assert!(matches!(self.ctx.kind, CtxKind::Poly));
        unsafe { &*(self.as_ptr() as *const sys::gr_poly_struct) }
    }

    fn poly_raw_mut(&mut self) -> *mut sys::gr_poly_struct {
        self.as_mut_ptr().cast()
    }

    fn base_ctx(&self) -> &Rc<Ctx> {
        self.ctx.base.as_ref().expect("not a polynomial ring")
    }

    /// The number of coefficients (degree + 1, or 0 for the zero polynomial).
    pub fn poly_len(&self) -> usize {
        self.poly_raw().length as usize
    }

    /// The coefficient of `x^i`.
    pub fn poly_coeff(&self, i: usize) -> Elem {
        let base = self.base_ctx();
        let mut c = Elem::new(base);
        let st = unsafe { sys::gr_poly_get_coeff_scalar(c.as_mut_ptr(), self.poly_raw(), i as sys::slong, base.ptr()) };
        assert_eq!(st, 0, "gr_poly_get_coeff_scalar failed");
        c
    }

    /// The polynomial with the given coefficients (constant term first).
    pub fn poly_from_coeffs(ctx: &Rc<Ctx>, coeffs: &[Elem]) -> GrResult<Elem> {
        let base = ctx.base.as_ref().expect("not a polynomial ring");
        let mut p = Elem::new(ctx);
        for (i, c) in coeffs.iter().enumerate().rev() {
            check(unsafe { sys::gr_poly_set_coeff_scalar(p.poly_raw_mut(), i as sys::slong, c.as_ptr(), base.ptr()) })?;
        }
        Ok(p)
    }

    pub fn poly_derivative(&self) -> GrResult<Elem> {
        let mut r = Elem::new(&self.ctx);
        check(unsafe { sys::gr_poly_derivative(r.poly_raw_mut(), self.poly_raw(), self.base_ctx().ptr()) })?;
        Ok(r)
    }

    /// Evaluate at a coefficient-ring element.
    pub fn poly_evaluate(&self, x: &Elem) -> GrResult<Elem> {
        let base = self.base_ctx();
        let mut r = Elem::new(base);
        check(unsafe { sys::gr_poly_evaluate(r.as_mut_ptr(), self.poly_raw(), x.as_ptr(), base.ptr()) })?;
        Ok(r)
    }

    /// `self(g)` for another polynomial `g` of the same ring.
    pub fn poly_compose(&self, g: &Elem) -> GrResult<Elem> {
        let mut r = Elem::new(&self.ctx);
        check(unsafe { sys::gr_poly_compose(r.poly_raw_mut(), self.poly_raw(), g.poly_raw(), self.base_ctx().ptr()) })?;
        Ok(r)
    }

    /// Quotient and remainder by a polynomial whose leading coefficient is a
    /// unit.
    pub fn poly_divrem(&self, g: &Elem) -> GrResult<(Elem, Elem)> {
        let mut q = Elem::new(&self.ctx);
        let mut r = Elem::new(&self.ctx);
        check(unsafe { sys::gr_poly_divrem(q.poly_raw_mut(), r.poly_raw_mut(), self.poly_raw(), g.poly_raw(), self.base_ctx().ptr()) })?;
        Ok((q, r))
    }

    /// The monic greatest common divisor (over a field).
    pub fn poly_gcd(&self, g: &Elem) -> GrResult<Elem> {
        let mut r = Elem::new(&self.ctx);
        check(unsafe { sys::gr_poly_gcd(r.poly_raw_mut(), self.poly_raw(), g.poly_raw(), self.base_ctx().ptr()) })?;
        Ok(r)
    }

    /// `(d, a, b)` with `d = a*self + b*g` monic (over a field).
    pub fn poly_xgcd(&self, g: &Elem) -> GrResult<(Elem, Elem, Elem)> {
        let mut d = Elem::new(&self.ctx);
        let mut a = Elem::new(&self.ctx);
        let mut b = Elem::new(&self.ctx);
        check(unsafe { sys::gr_poly_xgcd(d.poly_raw_mut(), a.poly_raw_mut(), b.poly_raw_mut(), self.poly_raw(), g.poly_raw(), self.base_ctx().ptr()) })?;
        Ok((d, a, b))
    }

    pub fn poly_resultant(&self, g: &Elem) -> GrResult<Elem> {
        let base = self.base_ctx();
        let mut r = Elem::new(base);
        check(unsafe { sys::gr_poly_resultant(r.as_mut_ptr(), self.poly_raw(), g.poly_raw(), base.ptr()) })?;
        Ok(r)
    }

    /// Multiply by a coefficient-ring scalar.
    pub fn poly_mul_scalar(&self, c: &Elem) -> GrResult<Elem> {
        let mut r = Elem::new(&self.ctx);
        check(unsafe { sys::gr_poly_mul_scalar(r.poly_raw_mut(), self.poly_raw(), c.as_ptr(), self.base_ctx().ptr()) })?;
        Ok(r)
    }

    /// The roots in the coefficient ring with their multiplicities.
    pub fn poly_roots(&self) -> GrResult<Vec<(Elem, u64)>> {
        let base = self.base_ctx();
        let mut roots = sys::gr_vec_struct::default();
        let mut mult = sys::gr_vec_struct::default();
        let zz = Ctx::integers();
        unsafe {
            sys::gr_vec_init(&mut roots, 0, base.ptr());
            sys::gr_vec_init(&mut mult, 0, zz.ptr());
        }
        let st = unsafe { sys::gr_poly_roots(&mut roots, (&mut mult as *mut sys::gr_vec_struct).cast(), self.poly_raw(), 0, base.ptr()) };
        let mut out = Vec::new();
        if st == 0 {
            for i in 0..roots.length as usize {
                let mut r = Elem::new(base);
                let src = unsafe { roots.entries.cast::<u8>().add(i * base.elem_size()) };
                unsafe { sys::gr_set(r.as_mut_ptr(), src.cast(), base.ptr()) };
                let m = unsafe { sys::fmpz_get_si(mult.entries.cast::<sys::fmpz>().add(i)) } as u64;
                out.push((r, m));
            }
        }
        unsafe {
            sys::gr_vec_clear(&mut roots, base.ptr());
            sys::gr_vec_clear(&mut mult, zz.ptr());
        }
        check(st)?;
        Ok(out)
    }
}

impl Elem {
    // ----- multivariate polynomials -------------------------------------------

    fn mpoly_raw(&self) -> &sys::gr_mpoly_struct {
        debug_assert!(matches!(self.ctx.kind, CtxKind::MPoly { .. }));
        unsafe { &*(self.as_ptr() as *const sys::gr_mpoly_struct) }
    }

    fn mpoly_mctx(&self) -> *const sys::mpoly_ctx_struct {
        unsafe { (*((*self.ctx.ptr()).data.as_ptr() as *const sys::_gr_mpoly_ctx_struct)).mctx }
    }

    /// The number of terms.
    pub fn mpoly_len(&self) -> usize {
        self.mpoly_raw().length as usize
    }

    /// The coefficient and exponent vector of the i-th term (in the ring's
    /// monomial order, largest first).
    pub fn mpoly_term(&self, i: usize) -> (Elem, Vec<u64>) {
        let poly = self.mpoly_raw();
        let base = self.ctx.base.as_ref().expect("not a polynomial ring");
        let mctx = self.mpoly_mctx();
        let bits = poly.bits;
        let words = unsafe {
            if bits as u64 <= 64 { (*mctx).lut_words_per_exp[bits as usize - 1] } else { (bits as i64 / 64) as sys::slong * (*mctx).nfields }
        } as usize;
        let nvars = unsafe { (*mctx).nvars } as usize;
        let mut exps: Vec<sys::ulong> = vec![0; nvars];
        unsafe { sys::mpoly_get_monomial_ui(exps.as_mut_ptr(), poly.exps.add(i * words), bits, mctx) };
        let mut c = Elem::new(base);
        let src = unsafe { poly.coeffs.cast::<u8>().add(i * base.elem_size()) };
        unsafe { sys::gr_set(c.as_mut_ptr(), src.cast(), base.ptr()) };
        (c, exps.into_iter().map(|e| e as u64).collect())
    }

    /// The polynomial with the given terms (in any order; like terms are
    /// combined).
    pub fn mpoly_from_terms(ctx: &Rc<Ctx>, terms: &[(Elem, Vec<u64>)]) -> GrResult<Elem> {
        let mut e = Elem::new(ctx);
        for (c, exps) in terms {
            let ex: Vec<sys::ulong> = exps.iter().map(|&x| x as sys::ulong).collect();
            check(unsafe { sys::gr_mpoly_push_term_scalar_ui(e.as_mut_ptr().cast(), c.as_ptr(), ex.as_ptr(), ctx.ptr()) })?;
        }
        unsafe { sys::gr_mpoly_sort_terms(e.as_mut_ptr().cast(), ctx.ptr()) };
        check(unsafe { sys::gr_mpoly_combine_like_terms(e.as_mut_ptr().cast(), ctx.ptr()) })?;
        Ok(e)
    }

    /// Multiply a multivariate polynomial by a coefficient-ring scalar.
    pub fn mpoly_mul_scalar(&self, c: &Elem) -> GrResult<Elem> {
        let mut r = Elem::new(&self.ctx);
        check(unsafe { sys::gr_mpoly_mul_scalar(r.as_mut_ptr().cast(), self.as_ptr().cast(), c.as_ptr(), self.ctx.ptr()) })?;
        Ok(r)
    }

    /// Set a multivariate polynomial to a constant.
    pub fn mpoly_set_scalar(&mut self, c: &Elem) -> GrResult<()> {
        let ctx = self.ctx.clone();
        check(unsafe { sys::gr_mpoly_set_scalar(self.as_mut_ptr().cast(), c.as_ptr(), ctx.ptr()) })
    }
}

fn nmod_coeffs(a: &sys::nmod_poly_struct, degree: usize) -> Vec<Integer> {
    (0..degree).map(|i| if (i as i64) < a.length as i64 { Integer::from_u64(unsafe { *a.coeffs.add(i) } as u64) } else { Integer::zero() }).collect()
}

/// The Conway polynomial of degree `n` over `F_p` from FLINT's table, as
/// coefficients (constant term first), if it is known.
pub fn conway_polynomial(p: u64, n: u64) -> Option<Vec<Integer>> {
    if n == 0 || n > 1 << 16 {
        return None;
    }
    let mut buf: Vec<sys::ulong> = vec![0; n as usize + 1];
    let ok = unsafe { sys::_nmod_poly_conway(buf.as_mut_ptr(), p as sys::ulong, n as sys::slong) };
    if ok == 0 {
        return None;
    }
    // FLINT stores the monic polynomial without its leading coefficient.
    buf[n as usize] = 1;
    Some(buf.into_iter().map(|c| Integer::from_u64(c as u64)).collect())
}

/// Whether the polynomial with the given coefficients (constant term first)
/// is irreducible over `F_p`.
pub fn is_irreducible_mod_p(p: &Integer, coeffs: &[Integer]) -> bool {
    if let Some(pw) = p.to_u64() {
        let mut poly = sys::nmod_poly_struct::default();
        let pz = Integer::from_u64(pw);
        unsafe {
            sys::nmod_poly_init(&mut poly, pw as sys::ulong);
            for (i, c) in coeffs.iter().enumerate() {
                let r = c.div_rem_euclid(&pz).and_then(|(_, r)| r.to_u64()).unwrap_or(0);
                sys::nmod_poly_set_coeff_ui(&mut poly, i as sys::slong, r as sys::ulong);
            }
            let ok = sys::nmod_poly_is_irreducible(&poly) != 0;
            sys::nmod_poly_clear(&mut poly);
            ok
        }
    } else {
        let mut mctx = sys::fmpz_mod_ctx_struct::default();
        let mut poly = sys::fmpz_mod_poly_struct::default();
        unsafe {
            sys::fmpz_mod_ctx_init(&mut mctx, p.raw_ptr());
            sys::fmpz_mod_poly_init(&mut poly, &mctx);
            for (i, c) in coeffs.iter().enumerate() {
                sys::fmpz_mod_poly_set_coeff_fmpz(&mut poly, i as sys::slong, c.raw_ptr(), &mctx);
            }
            let ok = sys::fmpz_mod_poly_is_irreducible(&poly, &mctx) != 0;
            sys::fmpz_mod_poly_clear(&mut poly, &mctx);
            sys::fmpz_mod_ctx_clear(&mut mctx);
            ok
        }
    }
}

/// An nmod_poly that clears itself.
struct NPoly(sys::nmod_poly_struct);

impl NPoly {
    fn new(p: u64) -> NPoly {
        let mut a = sys::nmod_poly_struct::default();
        unsafe { sys::nmod_poly_init(&mut a, p as sys::ulong) };
        NPoly(a)
    }
}

impl Drop for NPoly {
    fn drop(&mut self) {
        unsafe { sys::nmod_poly_clear(&mut self.0) };
    }
}

/// Whether the monic polynomial with the given coefficients modulo the word
/// prime p (constant term first) is irreducible. Ben-Or's test looks for
/// factors of degree 1, 2, ... in turn (f is irreducible when it is coprime
/// to x^(p^i) - x for i <= n/2), so most reducible polynomials fail early:
/// much faster than a full test when searching for an irreducible one. The
/// gcds are taken of products of the x^(p^i) - x, at i = 1, 2, 4, 8, ...
pub fn is_irreducible_word(p: u64, coeffs: &[u64]) -> bool {
    let n = coeffs.len().saturating_sub(1);
    if n <= 1 {
        return n == 1;
    }
    let mut f = NPoly::new(p);
    unsafe {
        for (i, &c) in coeffs.iter().enumerate() {
            sys::nmod_poly_set_coeff_ui(&mut f.0, i as sys::slong, c as sys::ulong);
        }
        // Roots in the first few elements are found faster by evaluation.
        if (0..p.min(8)).any(|a| sys::nmod_poly_evaluate_nmod(&f.0, a as sys::ulong) == 0) {
            return false;
        }
        // The inverse of the reversal of f, for reduction modulo f.
        let (mut rev, mut finv) = (NPoly::new(p), NPoly::new(p));
        sys::nmod_poly_reverse(&mut rev.0, &f.0, (n + 1) as sys::slong);
        sys::nmod_poly_inv_series(&mut finv.0, &rev.0, (n + 1) as sys::slong);
        let (mut x, mut h, mut t, mut g) = (NPoly::new(p), NPoly::new(p), NPoly::new(p), NPoly::new(p));
        let mut acc = NPoly::new(p);
        sys::nmod_poly_set_coeff_ui(&mut x.0, 1, 1);
        sys::nmod_poly_set_coeff_ui(&mut h.0, 1, 1);
        sys::nmod_poly_set_coeff_ui(&mut acc.0, 0, 1);
        for i in 1..=n / 2 {
            // h = x^(p^i) modulo f, and acc the product of the h - x.
            sys::nmod_poly_powmod_ui_binexp_preinv(&mut t.0, &h.0, p as sys::ulong, &f.0, &finv.0);
            std::mem::swap(&mut h, &mut t);
            sys::nmod_poly_sub(&mut t.0, &h.0, &x.0);
            sys::nmod_poly_mulmod_preinv(&mut g.0, &acc.0, &t.0, &f.0, &finv.0);
            std::mem::swap(&mut acc, &mut g);
            if i.is_power_of_two() || i == n / 2 {
                sys::nmod_poly_gcd(&mut g.0, &acc.0, &f.0);
                if g.0.length != 1 {
                    return false;
                }
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(v: i64) -> Integer {
        Integer::from_i64(v)
    }

    #[test]
    fn ben_or_agrees_with_flint() {
        // All monic polynomials of degree 2 to 6 over GF(2) and GF(3) with
        // non-zero constant term, against FLINT's full test.
        for p in [2u64, 3] {
            for n in 2..=6u32 {
                for c in 0..p.pow(n) {
                    let mut coeffs: Vec<u64> = (0..n).map(|i| c / p.pow(i) % p).collect();
                    coeffs.push(1);
                    let ints: Vec<Integer> = coeffs.iter().map(|&x| Integer::from_u64(x)).collect();
                    let full = coeffs[0] != 0 && is_irreducible_mod_p(&Integer::from_u64(p), &ints);
                    assert_eq!(is_irreducible_word(p, &coeffs), full, "{coeffs:?} mod {p}");
                }
            }
        }
    }

    #[test]
    fn residue_arithmetic() {
        let r = Ctx::residue_ring(&int(12));
        let a = Elem::from_i64(&r, 7).unwrap();
        let b = Elem::from_i64(&r, 9).unwrap();
        assert_eq!(a.add(&b).unwrap().to_integer().unwrap(), int(4));
        assert_eq!(a.mul(&b).unwrap().to_integer().unwrap(), int(3));
        assert_eq!(a.inv().unwrap().to_integer().unwrap(), int(7));
        assert_eq!(b.inv().err(), Some(GrError::Domain));
        let big = Ctx::residue_ring(&Integer::from_i64(2).pow(100));
        let x = Elem::from_i64(&big, -1).unwrap();
        assert_eq!(x.to_integer().unwrap(), Integer::from_i64(2).pow(100) - Integer::from_i64(1));
    }

    #[test]
    fn finite_fields() {
        let c = conway_polynomial(3, 2).unwrap();
        assert_eq!(c, vec![int(2), int(2), int(1)]);
        let f = Ctx::finite_field(&int(3), &c, true).unwrap();
        assert_eq!(f.fq_order().unwrap(), int(9));
        let w = f.generator().unwrap();
        assert_eq!(w.zech_log(), Some(1));
        assert_eq!(w.pow_i64(4).unwrap().fq_prime_value(), Some(int(2)));
        assert_eq!(w.fq_prime_value(), None);
        assert_eq!(w.fq_multiplicative_order().unwrap(), int(8));
        assert_eq!(w.pow_i64(5).unwrap().zech_log(), Some(5));
        assert_eq!(Elem::zero(&f).zech_log(), None);
        // w^2 = -2w - 2 = w + 1.
        assert_eq!(w.sqr().unwrap().fq_coords(), vec![int(1), int(1)]);
        // A non-primitive modulus cannot use Zech logarithms.
        let x2p1 = [int(1), int(0), int(1)];
        assert_eq!(Ctx::finite_field(&int(3), &x2p1, true).err(), Some(GrError::Domain));
        let g = Ctx::finite_field(&int(3), &x2p1, false).unwrap();
        let i = g.generator().unwrap();
        assert!(i.sqr().unwrap().add(&Elem::one(&g).unwrap()).unwrap().is_zero() == Truth::True);
    }

    #[test]
    fn polynomials() {
        let zz = Ctx::integers();
        let p = Ctx::poly(&zz);
        let x = p.generator().unwrap();
        let one = Elem::one(&p).unwrap();
        let f = x.sqr().unwrap().sub(&one).unwrap();
        assert_eq!(f.poly_len(), 3);
        assert_eq!(f.poly_coeff(0).to_integer().unwrap(), int(-1));
        let (q, r) = f.poly_divrem(&x.sub(&one).unwrap()).unwrap();
        assert!(r.is_zero() == Truth::True);
        assert!(q.equal(&x.add(&one).unwrap()) == Truth::True);
        let two = Elem::from_i64(&zz, 2).unwrap();
        assert_eq!(f.poly_evaluate(&two).unwrap().to_integer().unwrap(), int(3));
        let roots = f.poly_roots().unwrap();
        let mut rs: Vec<i64> = roots.iter().map(|(r, _)| r.to_integer().unwrap().to_i64().unwrap()).collect();
        rs.sort();
        assert_eq!(rs, vec![-1, 1]);
    }

    #[test]
    fn floats() {
        let r = Ctx::real_float(100);
        let two = Elem::from_i64(&r, 2).unwrap();
        let s = two.sqrt().unwrap();
        let back = s.sqr().unwrap();
        assert!(back.sub(&two).unwrap().abs().unwrap().cmp(&Elem::from_rational(&r, &Rational::new(&int(1), &int(2).pow(90)).unwrap()).unwrap()).unwrap() < 0);
    }
}
