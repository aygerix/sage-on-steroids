//! Univariate polynomial algorithms on FLINT's specialised polynomial types.
//!
//! calyx keeps univariate polynomials as generic `gr_poly`s (elements of a
//! `Poly` context). Over the integers, the integers modulo a large n and
//! finite fields, a `gr_poly` has the memory layout of FLINT's polynomial
//! type for that ring (fmpz_poly, fmpz_mod_poly, fq_*_poly), so the
//! specialised algorithms run on it in place; over Z/nZ with a word-sized n
//! it lacks only the modulus of an nmod_poly, and over Q it is converted to
//! an fmpq_poly. Other coefficient rings use gr_poly's generic algorithms
//! where FLINT has them, and report `Unable` otherwise.
//!
//! FLINT aborts the process when an algorithm meets a non-invertible
//! element, so everything here checks its preconditions first: algorithms
//! that need a field run only over prime moduli.

use std::ffi::{c_int, c_void};
use std::rc::Rc;

use flint3_sys as sys;

use crate::gr::{Ctx, CtxKind, Elem, GrError, GrResult, Truth};
use crate::{Integer, Rational};

type P = *mut c_void;
type C = *const c_void;

// FLINT's polynomial functions over finite fields come from templates that
// flint3-sys does not read; they are declared here with untyped pointers
// (the three representations share their shapes).
unsafe extern "C" {
    fn fq_nmod_poly_gcd(r: P, a: C, b: C, ctx: C);
    fn fq_nmod_poly_xgcd(g: P, s: P, t: P, a: C, b: C, ctx: C);
    fn fq_nmod_poly_divrem(q: P, r: P, a: C, b: C, ctx: C);
    fn fq_nmod_poly_powmod_fmpz_binexp(r: P, a: C, e: *const sys::fmpz, f: C, ctx: C);
    fn fq_nmod_poly_factor_init(f: P, ctx: C);
    fn fq_nmod_poly_factor_clear(f: P, ctx: C);
    fn fq_nmod_poly_factor(f: P, lc: P, a: C, ctx: C);
    fn fq_nmod_poly_factor_squarefree(f: P, a: C, ctx: C);
    fn fq_nmod_poly_factor_distinct_deg(f: P, a: C, degs: *const *mut sys::slong, ctx: C);
    fn fq_nmod_poly_factor_equal_deg(f: P, a: C, d: sys::slong, ctx: C);
    fn fq_nmod_poly_roots(f: P, a: C, mult: c_int, ctx: C);
    fn fq_nmod_poly_is_irreducible(a: C, ctx: C) -> c_int;

    fn fq_zech_poly_gcd(r: P, a: C, b: C, ctx: C);
    fn fq_zech_poly_xgcd(g: P, s: P, t: P, a: C, b: C, ctx: C);
    fn fq_zech_poly_divrem(q: P, r: P, a: C, b: C, ctx: C);
    fn fq_zech_poly_powmod_fmpz_binexp(r: P, a: C, e: *const sys::fmpz, f: C, ctx: C);
    fn fq_zech_poly_factor_init(f: P, ctx: C);
    fn fq_zech_poly_factor_clear(f: P, ctx: C);
    fn fq_zech_poly_factor(f: P, lc: P, a: C, ctx: C);
    fn fq_zech_poly_factor_squarefree(f: P, a: C, ctx: C);
    fn fq_zech_poly_factor_distinct_deg(f: P, a: C, degs: *const *mut sys::slong, ctx: C);
    fn fq_zech_poly_factor_equal_deg(f: P, a: C, d: sys::slong, ctx: C);
    fn fq_zech_poly_roots(f: P, a: C, mult: c_int, ctx: C);
    fn fq_zech_poly_is_irreducible(a: C, ctx: C) -> c_int;

    fn fq_poly_gcd(r: P, a: C, b: C, ctx: C);
    fn fq_poly_xgcd(g: P, s: P, t: P, a: C, b: C, ctx: C);
    fn fq_poly_divrem(q: P, r: P, a: C, b: C, ctx: C);
    fn fq_poly_powmod_fmpz_binexp(r: P, a: C, e: *const sys::fmpz, f: C, ctx: C);
    fn fq_poly_factor_init(f: P, ctx: C);
    fn fq_poly_factor_clear(f: P, ctx: C);
    fn fq_poly_factor(f: P, lc: P, a: C, ctx: C);
    fn fq_poly_factor_squarefree(f: P, a: C, ctx: C);
    fn fq_poly_factor_distinct_deg(f: P, a: C, degs: *const *mut sys::slong, ctx: C);
    fn fq_poly_factor_equal_deg(f: P, a: C, d: sys::slong, ctx: C);
    fn fq_poly_roots(f: P, a: C, mult: c_int, ctx: C);
    fn fq_poly_is_irreducible(a: C, ctx: C) -> c_int;
}

/// The polynomial functions of one representation of finite fields.
struct FqFns {
    gcd: unsafe extern "C" fn(P, C, C, C),
    xgcd: unsafe extern "C" fn(P, P, P, C, C, C),
    divrem: unsafe extern "C" fn(P, P, C, C, C),
    powmod: unsafe extern "C" fn(P, C, *const sys::fmpz, C, C),
    fac_init: unsafe extern "C" fn(P, C),
    fac_clear: unsafe extern "C" fn(P, C),
    factor: unsafe extern "C" fn(P, P, C, C),
    sqfree: unsafe extern "C" fn(P, C, C),
    ddf: unsafe extern "C" fn(P, C, *const *mut sys::slong, C),
    edf: unsafe extern "C" fn(P, C, sys::slong, C),
    roots: unsafe extern "C" fn(P, C, c_int, C),
    irreducible: unsafe extern "C" fn(C, C) -> c_int,
}

static FQ_NMOD: FqFns = FqFns {
    gcd: fq_nmod_poly_gcd,
    xgcd: fq_nmod_poly_xgcd,
    divrem: fq_nmod_poly_divrem,
    powmod: fq_nmod_poly_powmod_fmpz_binexp,
    fac_init: fq_nmod_poly_factor_init,
    fac_clear: fq_nmod_poly_factor_clear,
    factor: fq_nmod_poly_factor,
    sqfree: fq_nmod_poly_factor_squarefree,
    ddf: fq_nmod_poly_factor_distinct_deg,
    edf: fq_nmod_poly_factor_equal_deg,
    roots: fq_nmod_poly_roots,
    irreducible: fq_nmod_poly_is_irreducible,
};

/// Fields with Zech logarithms pass their gr context (see `zech_ctx`).
static FQ_ZECH: FqFns = FqFns {
    gcd: zech_gcd,
    xgcd: zech_xgcd,
    divrem: zech_divrem,
    powmod: zech_powmod,
    fac_init: zech_fac_init,
    fac_clear: zech_fac_clear,
    factor: zech_factor,
    sqfree: zech_sqfree,
    ddf: zech_ddf,
    edf: zech_edf,
    roots: zech_roots,
    irreducible: zech_irreducible,
};

// Over a field with Zech logarithms, division, gcds and powers modulo a
// polynomial go through gr on the field's context, whose methods run the
// kernels of `smallfq` (and FLINT's fq_zech functions should gr give up);
// the rest are FLINT's fq_zech functions.

/// The fq_zech context of the gr context of a field with Zech logarithms
/// (its first word).
unsafe fn zech_ctx(ctx: C) -> C {
    unsafe { *(ctx as *const C) }
}

unsafe extern "C" fn zech_gcd(r: P, a: C, b: C, ctx: C) {
    unsafe {
        if sys::gr_poly_gcd(r.cast(), a.cast(), b.cast(), ctx as *mut _) != 0 {
            fq_zech_poly_gcd(r, a, b, zech_ctx(ctx));
        }
    }
}

unsafe extern "C" fn zech_xgcd(g: P, s: P, t: P, a: C, b: C, ctx: C) {
    unsafe {
        if sys::gr_poly_xgcd(g.cast(), s.cast(), t.cast(), a.cast(), b.cast(), ctx as *mut _) != 0 {
            fq_zech_poly_xgcd(g, s, t, a, b, zech_ctx(ctx));
        }
    }
}

unsafe extern "C" fn zech_divrem(q: P, r: P, a: C, b: C, ctx: C) {
    unsafe {
        if sys::gr_poly_divrem(q.cast(), r.cast(), a.cast(), b.cast(), ctx as *mut _) != 0 {
            fq_zech_poly_divrem(q, r, a, b, zech_ctx(ctx));
        }
    }
}

unsafe extern "C" fn zech_powmod(r: P, a: C, e: *const sys::fmpz, f: C, ctx: C) {
    unsafe {
        if sys::gr_poly_powmod_fmpz_binexp(r.cast(), a.cast(), e, f.cast(), ctx as *mut _) != 0 {
            fq_zech_poly_powmod_fmpz_binexp(r, a, e, f, zech_ctx(ctx));
        }
    }
}

/// `$name`: FLINT's fq_zech function `$f` with the fq_zech context of the
/// gr context passed last.
macro_rules! on_zech_ctx {
    ($($name:ident = $f:ident($($a:ident: $t:ty),*) $(-> $r:ty)?;)*) => {$(
        unsafe extern "C" fn $name($($a: $t,)* ctx: C) $(-> $r)? {
            unsafe { $f($($a,)* zech_ctx(ctx)) }
        }
    )*};
}

on_zech_ctx! {
    zech_fac_init = fq_zech_poly_factor_init(f: P);
    zech_fac_clear = fq_zech_poly_factor_clear(f: P);
    zech_factor = fq_zech_poly_factor(f: P, lc: P, a: C);
    zech_sqfree = fq_zech_poly_factor_squarefree(f: P, a: C);
    zech_ddf = fq_zech_poly_factor_distinct_deg(f: P, a: C, degs: *const *mut sys::slong);
    zech_edf = fq_zech_poly_factor_equal_deg(f: P, a: C, d: sys::slong);
    zech_roots = fq_zech_poly_roots(f: P, a: C, mult: c_int);
    zech_irreducible = fq_zech_poly_is_irreducible(a: C) -> c_int;
}

/// Packed fields convert to and from fq_nmod (see `packed`).
static FQ_PACKED: FqFns = FqFns {
    gcd: crate::packed::poly_gcd,
    xgcd: crate::packed::poly_xgcd,
    divrem: crate::packed::poly_divrem,
    powmod: crate::packed::poly_powmod,
    fac_init: crate::packed::fac_init,
    fac_clear: crate::packed::fac_clear,
    factor: crate::packed::poly_factor,
    sqfree: crate::packed::poly_factor_squarefree,
    ddf: crate::packed::poly_factor_distinct_deg,
    edf: crate::packed::poly_factor_equal_deg,
    roots: crate::packed::poly_roots_factored,
    irreducible: crate::packed::poly_is_irreducible,
};

static FQ: FqFns = FqFns {
    gcd: fq_poly_gcd,
    xgcd: fq_poly_xgcd,
    divrem: fq_poly_divrem,
    powmod: fq_poly_powmod_fmpz_binexp,
    fac_init: fq_poly_factor_init,
    fac_clear: fq_poly_factor_clear,
    factor: fq_poly_factor,
    sqfree: fq_poly_factor_squarefree,
    ddf: fq_poly_factor_distinct_deg,
    edf: fq_poly_factor_equal_deg,
    roots: fq_poly_roots,
    irreducible: fq_poly_is_irreducible,
};

/// The factorization structures of fmpz_mod and finite field polynomials
/// (all laid out alike, with 3-word polynomials).
#[repr(C)]
struct RawFac {
    poly: *mut sys::gr_poly_struct,
    exp: *mut sys::slong,
    num: sys::slong,
    alloc: sys::slong,
}

/// How the polynomials over a coefficient context are handled.
#[derive(Clone, Copy)]
enum Rep {
    Z,
    Q,
    /// Z/nZ with a word-sized n, and whether n is prime.
    Nmod(Mod, bool),
    /// Z/nZ with a large n, and whether n is prime.
    FmpzMod(*const sys::fmpz_mod_ctx_struct, bool),
    /// A finite field with FLINT's functions for its representation.
    Fq(&'static FqFns, C),
    Generic,
}

/// A word-sized modulus (FLINT's `nmod_t`, which is not `Copy`).
#[derive(Clone, Copy)]
struct Mod {
    n: sys::ulong,
    ninv: sys::ulong,
    norm: sys::flint_bitcnt_t,
}

impl Mod {
    fn of(m: &sys::nmod_t) -> Mod {
        Mod { n: m.n, ninv: m.ninv, norm: m.norm }
    }

    fn t(self) -> sys::nmod_t {
        sys::nmod_t { n: self.n, ninv: self.ninv, norm: self.norm }
    }
}

fn check(status: c_int) -> GrResult<()> {
    if status == 0 {
        Ok(())
    } else if status & 1 != 0 {
        Err(GrError::Domain)
    } else {
        Err(GrError::Unable)
    }
}

/// The coefficient context of a polynomial context.
fn base_of(ctx: &Rc<Ctx>) -> &Rc<Ctx> {
    ctx.base().expect("not a polynomial ring")
}

/// Whether the context of integers modulo a large n is a field, deciding it
/// (and remembering it in the context) the first time.
pub(crate) fn fmpz_mod_is_field(base: &Ctx) -> bool {
    match base.is_field() {
        Truth::True => true,
        Truth::False => false,
        Truth::Unknown => {
            let CtxKind::FmpzMod(n) = base.kind() else { return false };
            let prime = unsafe { sys::fmpz_is_probabprime(n.raw_ptr()) } != 0;
            let t = if prime { sys::truth_t_T_TRUE } else { sys::truth_t_T_FALSE };
            unsafe { sys::gr_ctx_set_is_field(base.ptr(), t) };
            prime
        }
    }
}

fn rep(base: &Ctx) -> Rep {
    // A gr context starts with its data: the nmod_t, or a pointer to the
    // fmpz_mod or finite field context.
    let data = base.ptr() as *const u8;
    unsafe {
        match base.kind() {
            CtxKind::Integers => Rep::Z,
            CtxKind::Rationals => Rep::Q,
            CtxKind::Nmod(n) => Rep::Nmod(Mod::of(&*(data as *const sys::nmod_t)), sys::n_is_prime(*n as sys::ulong) != 0),
            CtxKind::FmpzMod(_) => Rep::FmpzMod(*(data as *const *const sys::fmpz_mod_ctx_struct), fmpz_mod_is_field(base)),
            CtxKind::FqNmod { .. } => Rep::Fq(&FQ_NMOD, *(data as *const C)),
            CtxKind::Fq { .. } => Rep::Fq(&FQ, *(data as *const C)),
            // With the gr context itself.
            CtxKind::FqZech { .. } => Rep::Fq(&FQ_ZECH, base.ptr() as C),
            CtxKind::FqPacked { .. } => Rep::Fq(&FQ_PACKED, base.ptr() as C),
            _ => Rep::Generic,
        }
    }
}

/// Whether the coefficient ring of polynomials of `ctx` is a field on which
/// the specialised algorithms (or gr's generic ones) can run.
pub fn over_field(ctx: &Rc<Ctx>) -> bool {
    match rep(base_of(ctx)) {
        Rep::Z => false,
        Rep::Q | Rep::Fq(..) => true,
        Rep::Nmod(_, p) | Rep::FmpzMod(_, p) => p,
        Rep::Generic => base_of(ctx).is_field() == Truth::True,
    }
}

/// Whether polynomials of `ctx` factor here: over the integers, the
/// rationals, prime residue rings and finite fields.
pub fn can_factor(ctx: &Rc<Ctx>) -> bool {
    match rep(base_of(ctx)) {
        Rep::Z | Rep::Q | Rep::Fq(..) => true,
        Rep::Nmod(_, p) | Rep::FmpzMod(_, p) => p,
        Rep::Generic => false,
    }
}

/// Whether the coefficient ring of `ctx` is a finite field (a prime residue
/// ring included).
pub fn over_finite_field(ctx: &Rc<Ctx>) -> bool {
    match rep(base_of(ctx)) {
        Rep::Fq(..) => true,
        Rep::Nmod(_, p) | Rep::FmpzMod(_, p) => p,
        _ => false,
    }
}

// ----- raw views ---------------------------------------------------------------

fn gp(e: &Elem) -> *const sys::gr_poly_struct {
    e.as_ptr().cast()
}

fn gp_mut(e: &mut Elem) -> *mut sys::gr_poly_struct {
    e.as_mut_ptr().cast()
}

fn len(e: &Elem) -> usize {
    unsafe { (*gp(e)).length as usize }
}

/// A copy of a polynomial of FLINT's own type for the base ring of `ctx`
/// (its first three words are laid out as a gr_poly) as an element of
/// `ctx`.
fn from_raw(ctx: &Rc<Ctx>, p: *const c_void) -> Elem {
    let mut e = Elem::new(ctx);
    let base = base_of(ctx);
    let st = unsafe { sys::gr_poly_set(gp_mut(&mut e), p.cast(), base.ptr()) };
    assert_eq!(st, 0, "gr_poly_set failed");
    e
}

/// An nmod_poly sharing the coefficients of a polynomial over Z/nZ, for
/// reading only.
fn nview(e: &Elem, m: Mod) -> sys::nmod_poly_struct {
    let p = unsafe { &*gp(e) };
    sys::nmod_poly_struct { coeffs: p.coeffs.cast(), alloc: p.alloc, length: p.length, mod_: m.t() }
}

/// An nmod_poly owned by Rust.
struct NPoly(sys::nmod_poly_struct);

impl NPoly {
    fn new(m: Mod) -> NPoly {
        let mut p = sys::nmod_poly_struct::default();
        unsafe { sys::nmod_poly_init_mod(&mut p, m.t()) };
        NPoly(p)
    }

    /// Move the coefficients into a new element of `ctx`.
    fn into_elem(self, ctx: &Rc<Ctx>) -> Elem {
        let me = std::mem::ManuallyDrop::new(self);
        let mut e = Elem::new(ctx);
        unsafe {
            let g = gp_mut(&mut e);
            (*g).coeffs = me.0.coeffs.cast();
            (*g).alloc = me.0.alloc;
            (*g).length = me.0.length;
        }
        e
    }
}

impl Drop for NPoly {
    fn drop(&mut self) {
        unsafe { sys::nmod_poly_clear(&mut self.0) };
    }
}

/// An fmpq_poly owned by Rust.
struct QPoly(sys::fmpq_poly_struct);

impl QPoly {
    fn new() -> QPoly {
        let mut p = sys::fmpq_poly_struct::default();
        unsafe { sys::fmpq_poly_init(&mut p) };
        QPoly(p)
    }

    /// A polynomial over Q (a gr_poly of fmpq) in FLINT's representation
    /// with a common denominator.
    fn of(e: &Elem) -> QPoly {
        let mut q = QPoly::new();
        let p = unsafe { &*gp(e) };
        if p.length > 0 {
            unsafe {
                sys::fmpq_poly_fit_length(&mut q.0, p.length);
                sys::_fmpq_vec_get_fmpz_vec_fmpz(q.0.coeffs, q.0.den.as_mut_ptr(), p.coeffs as *const sys::fmpq, p.length);
                sys::_fmpq_poly_set_length(&mut q.0, p.length);
            }
        }
        q
    }

    fn to_elem(&self, ctx: &Rc<Ctx>) -> Elem {
        let mut e = Elem::new(ctx);
        let n = self.0.length;
        let qq = base_of(ctx);
        unsafe {
            let g = gp_mut(&mut e);
            sys::gr_poly_fit_length(g, n, qq.ptr());
            for i in 0..n {
                sys::fmpq_poly_get_coeff_fmpq(((*g).coeffs as *mut sys::fmpq).add(i as usize), &self.0, i);
            }
            sys::_gr_poly_set_length(g, n, qq.ptr());
        }
        e
    }

    /// The numerator: the primitive-up-to-content integer polynomial
    /// `den * self`.
    fn numerator(&self, zctx: &Rc<Ctx>) -> Elem {
        let mut e = Elem::new(zctx);
        unsafe { sys::fmpq_poly_get_numerator(e.as_mut_ptr().cast(), &self.0) };
        e
    }
}

impl Drop for QPoly {
    fn drop(&mut self) {
        unsafe { sys::fmpq_poly_clear(&mut self.0) };
    }
}

fn fz(e: &Elem) -> *const sys::fmpz_poly_struct {
    e.as_ptr().cast()
}

fn fz_mut(e: &mut Elem) -> *mut sys::fmpz_poly_struct {
    e.as_mut_ptr().cast()
}

/// A leading or other coefficient-ring element read from a raw pointer.
fn base_elem(base: &Rc<Ctx>, x: *const c_void) -> Elem {
    let mut e = Elem::new(base);
    let st = unsafe { sys::gr_set(e.as_mut_ptr(), x, base.ptr()) };
    assert_eq!(st, 0, "gr_set failed");
    e
}

/// The polynomial ring over the integers, for the numerators of rational
/// polynomials.
fn zpoly_ctx() -> Rc<Ctx> {
    thread_local! {
        static ZX: Rc<Ctx> = Ctx::poly(&Ctx::integers());
    }
    ZX.with(Rc::clone)
}

/// `f` with its coefficients mapped into the coefficient ring of `ctx`
/// (where FLINT can convert them: from the integers into any ring, from
/// Z/nZ onto Z/mZ, ...).
pub fn convert(ctx: &Rc<Ctx>, f: &Elem) -> GrResult<Elem> {
    let mut e = Elem::new(ctx);
    check(unsafe { sys::gr_poly_set_gr_poly_other(gp_mut(&mut e), gp(f), base_of(f.ctx()).ptr(), base_of(ctx).ptr()) })?;
    Ok(e)
}

/// The leading coefficient (zero for the zero polynomial).
pub fn lead(f: &Elem) -> Elem {
    let n = len(f);
    if n == 0 { Elem::zero(base_of(f.ctx())) } else { f.poly_coeff(n - 1) }
}

// ----- shapes ----------------------------------------------------------------------

/// `c x^k`.
pub fn monomial(ctx: &Rc<Ctx>, c: &Elem, k: usize) -> GrResult<Elem> {
    let mut e = Elem::new(ctx);
    check(unsafe { sys::gr_poly_set_coeff_scalar(gp_mut(&mut e), k as sys::slong, c.as_ptr(), base_of(ctx).ptr()) })?;
    Ok(e)
}

/// `f x^k`.
pub fn shift_left(f: &Elem, k: usize) -> GrResult<Elem> {
    let mut e = Elem::new(f.ctx());
    check(unsafe { sys::gr_poly_shift_left(gp_mut(&mut e), gp(f), k as sys::slong, base_of(f.ctx()).ptr()) })?;
    Ok(e)
}

/// `f div x^k`.
pub fn shift_right(f: &Elem, k: usize) -> GrResult<Elem> {
    let mut e = Elem::new(f.ctx());
    check(unsafe { sys::gr_poly_shift_right(gp_mut(&mut e), gp(f), k as sys::slong, base_of(f.ctx()).ptr()) })?;
    Ok(e)
}

/// `f mod x^n`.
pub fn truncate(f: &Elem, n: usize) -> GrResult<Elem> {
    let mut e = Elem::new(f.ctx());
    check(unsafe { sys::gr_poly_truncate(gp_mut(&mut e), gp(f), n as sys::slong, base_of(f.ctx()).ptr()) })?;
    Ok(e)
}

/// `x^(n-1) f(1/x)` for `f` of length at most `n`: the first `n`
/// coefficients reversed.
pub fn reverse(f: &Elem, n: usize) -> GrResult<Elem> {
    let mut e = Elem::new(f.ctx());
    check(unsafe { sys::gr_poly_reverse(gp_mut(&mut e), gp(f), n as sys::slong, base_of(f.ctx()).ptr()) })?;
    Ok(e)
}

/// The n-th derivative.
pub fn nth_derivative(f: &Elem, n: u64) -> GrResult<Elem> {
    let mut e = Elem::new(f.ctx());
    check(unsafe { sys::gr_poly_nth_derivative(gp_mut(&mut e), gp(f), n as sys::ulong, base_of(f.ctx()).ptr()) })?;
    Ok(e)
}

/// The integral with constant term zero (over a ring where the division by
/// the exponents is possible).
pub fn integral(f: &Elem) -> GrResult<Elem> {
    let mut e = Elem::new(f.ctx());
    check(unsafe { sys::gr_poly_integral(gp_mut(&mut e), gp(f), base_of(f.ctx()).ptr()) })?;
    Ok(e)
}

/// The monic associate over a field.
pub fn make_monic(f: &Elem) -> GrResult<Elem> {
    let mut e = Elem::new(f.ctx());
    check(unsafe { sys::gr_poly_make_monic(gp_mut(&mut e), gp(f), base_of(f.ctx()).ptr()) })?;
    Ok(e)
}

/// The polynomial of length at most `xs.len()` taking the values `ys` at
/// the distinct points `xs` of a field.
pub fn interpolate(ctx: &Rc<Ctx>, xs: &[Elem], ys: &[Elem]) -> GrResult<Elem> {
    let base = base_of(ctx);
    let n = xs.len();
    if ys.len() != n {
        return Err(GrError::Domain);
    }
    let sz = base.elem_size();
    let mut vx = sys::gr_vec_struct::default();
    let mut vy = sys::gr_vec_struct::default();
    let mut e = Elem::new(ctx);
    let st;
    unsafe {
        sys::gr_vec_init(&mut vx, n as sys::slong, base.ptr());
        sys::gr_vec_init(&mut vy, n as sys::slong, base.ptr());
        for i in 0..n {
            sys::gr_set(vx.entries.cast::<u8>().add(i * sz).cast(), xs[i].as_ptr(), base.ptr());
            sys::gr_set(vy.entries.cast::<u8>().add(i * sz).cast(), ys[i].as_ptr(), base.ptr());
        }
        st = sys::gr_poly_interpolate(gp_mut(&mut e), &vx, &vy, base.ptr());
        sys::gr_vec_clear(&mut vx, base.ptr());
        sys::gr_vec_clear(&mut vy, base.ptr());
    }
    check(st)?;
    Ok(e)
}

// ----- gcds ----------------------------------------------------------------------

/// The greatest common divisor, normalised as Magma normalises it: with a
/// non-negative leading coefficient over the integers, monic over a field.
pub fn gcd(f: &Elem, g: &Elem) -> GrResult<Elem> {
    let ctx = f.ctx();
    let base = base_of(ctx);
    let mut r = Elem::new(ctx);
    unsafe {
        match rep(base) {
            Rep::Z => sys::fmpz_poly_gcd(fz_mut(&mut r), fz(f), fz(g)),
            Rep::Q => {
                let mut c = QPoly::new();
                sys::fmpq_poly_gcd(&mut c.0, &QPoly::of(f).0, &QPoly::of(g).0);
                return Ok(c.to_elem(ctx));
            }
            Rep::Nmod(m, true) => {
                let mut c = NPoly::new(m);
                sys::nmod_poly_gcd(&mut c.0, &nview(f, m), &nview(g, m));
                return Ok(c.into_elem(ctx));
            }
            Rep::FmpzMod(c, true) => sys::fmpz_mod_poly_gcd(r.as_mut_ptr().cast(), f.as_ptr().cast(), g.as_ptr().cast(), c),
            Rep::Fq(fns, c) => (fns.gcd)(r.as_mut_ptr(), f.as_ptr(), g.as_ptr(), c),
            _ => {
                check(sys::gr_poly_gcd(gp_mut(&mut r), gp(f), gp(g), base.ptr()))?;
                if base.is_field() == Truth::True && len(&r) > 0 {
                    check(sys::gr_poly_make_monic(gp_mut(&mut r), gp(&r), base.ptr()))?;
                }
            }
        }
    }
    Ok(r)
}

/// `(d, a, b)` with `d = a f + b g` the monic gcd over a field, with Magma's
/// cofactors: those of the Euclidean algorithm on `(f, g)`, so `(g, 0, 1)`
/// (made monic) when `g` divides `f`, and the unique ones of least degree
/// otherwise.
pub fn xgcd(f: &Elem, g: &Elem) -> GrResult<(Elem, Elem, Elem)> {
    let ctx = f.ctx();
    let base = base_of(ctx);
    let float = matches!(base.kind(), CtxKind::RealFloat(_) | CtxKind::ComplexFloat(_));
    if !over_field(ctx) && !float {
        return Err(GrError::Domain);
    }
    let zero = Elem::zero(ctx);
    let (fz0, gz0) = (len(f) == 0, len(g) == 0);
    if fz0 && gz0 {
        return Ok((zero.clone(), zero.clone(), zero));
    }
    // The first step of the Euclidean algorithm leaves (g, 0, 1) when g
    // divides f, and (f, 1, 0) when then f divides g.
    let unit_of = |p: &Elem| -> GrResult<Elem> { lead(p).inv() };
    if !gz0 && divrem(f, g)?.1.is_zero() == Truth::True {
        let u = unit_of(g)?;
        return Ok((g.poly_mul_scalar(&u)?, zero, Elem::poly_from_coeffs(ctx, &[u])?));
    }
    if !fz0 && divrem(g, f)?.1.is_zero() == Truth::True {
        let u = unit_of(f)?;
        return Ok((f.poly_mul_scalar(&u)?, Elem::poly_from_coeffs(ctx, &[u])?, zero));
    }
    if float {
        return euclid_xgcd(f, g);
    }
    let (mut d, mut a, mut b) = (Elem::new(ctx), Elem::new(ctx), Elem::new(ctx));
    unsafe {
        match rep(base) {
            Rep::Q => {
                let (mut qd, mut qa, mut qb) = (QPoly::new(), QPoly::new(), QPoly::new());
                sys::fmpq_poly_xgcd(&mut qd.0, &mut qa.0, &mut qb.0, &QPoly::of(f).0, &QPoly::of(g).0);
                return Ok((qd.to_elem(ctx), qa.to_elem(ctx), qb.to_elem(ctx)));
            }
            Rep::Nmod(m, _) => {
                let (mut nd, mut na, mut nb) = (NPoly::new(m), NPoly::new(m), NPoly::new(m));
                sys::nmod_poly_xgcd(&mut nd.0, &mut na.0, &mut nb.0, &nview(f, m), &nview(g, m));
                return Ok((nd.into_elem(ctx), na.into_elem(ctx), nb.into_elem(ctx)));
            }
            Rep::FmpzMod(c, _) => sys::fmpz_mod_poly_xgcd(d.as_mut_ptr().cast(), a.as_mut_ptr().cast(), b.as_mut_ptr().cast(), f.as_ptr().cast(), g.as_ptr().cast(), c),
            Rep::Fq(fns, c) => (fns.xgcd)(d.as_mut_ptr(), a.as_mut_ptr(), b.as_mut_ptr(), f.as_ptr(), g.as_ptr(), c),
            _ => {
                check(sys::gr_poly_xgcd(gp_mut(&mut d), gp_mut(&mut a), gp_mut(&mut b), gp(f), gp(g), base.ptr()))?;
            }
        }
    }
    Ok((d, a, b))
}

/// The extended Euclidean algorithm on `(f, g)`, `g` non-zero, made monic:
/// over the floating-point fields, which gr does not count as fields.
fn euclid_xgcd(f: &Elem, g: &Elem) -> GrResult<(Elem, Elem, Elem)> {
    let ctx = f.ctx();
    let (mut r0, mut r1) = (f.clone(), g.clone());
    let (mut s0, mut s1) = (Elem::one(ctx)?, Elem::zero(ctx));
    let (mut t0, mut t1) = (Elem::zero(ctx), Elem::one(ctx)?);
    while len(&r1) > 0 {
        let (q, r) = divrem(&r0, &r1)?;
        let s = s0.sub(&q.mul(&s1)?)?;
        let t = t0.sub(&q.mul(&t1)?)?;
        (r0, r1, s0, s1, t0, t1) = (r1, r, s1, s, t1, t);
    }
    let u = lead(&r0).inv()?;
    Ok((r0.poly_mul_scalar(&u)?, s0.poly_mul_scalar(&u)?, t0.poly_mul_scalar(&u)?))
}

// ----- division --------------------------------------------------------------------

/// Quotient and remainder. Over a field (or with a unit leading coefficient
/// of `g`) the remainder has lower degree than `g`. Over the integers, as in
/// Magma, each coefficient of the quotient from the top is the floor of the
/// current coefficient divided by the leading coefficient of `g`, so the
/// remainder can keep higher terms. `g` must be non-zero.
pub fn divrem(f: &Elem, g: &Elem) -> GrResult<(Elem, Elem)> {
    let ctx = f.ctx();
    let base = base_of(ctx);
    if len(g) == 0 {
        return Err(GrError::Domain);
    }
    let (mut q, mut r) = (Elem::new(ctx), Elem::new(ctx));
    unsafe {
        match rep(base) {
            Rep::Z => {
                let lc = lead(g);
                if lc.is_one() == Truth::True || lc.is_neg_one() == Truth::True {
                    sys::fmpz_poly_divrem(fz_mut(&mut q), fz_mut(&mut r), fz(f), fz(g));
                } else {
                    return Ok(floor_divrem(f, g));
                }
            }
            Rep::Q => {
                let (mut qq, mut qr) = (QPoly::new(), QPoly::new());
                sys::fmpq_poly_divrem(&mut qq.0, &mut qr.0, &QPoly::of(f).0, &QPoly::of(g).0);
                return Ok((qq.to_elem(ctx), qr.to_elem(ctx)));
            }
            Rep::Nmod(m, true) => {
                let (mut nq, mut nr) = (NPoly::new(m), NPoly::new(m));
                sys::nmod_poly_divrem(&mut nq.0, &mut nr.0, &nview(f, m), &nview(g, m));
                return Ok((nq.into_elem(ctx), nr.into_elem(ctx)));
            }
            Rep::FmpzMod(c, true) => sys::fmpz_mod_poly_divrem(q.as_mut_ptr().cast(), r.as_mut_ptr().cast(), f.as_ptr().cast(), g.as_ptr().cast(), c),
            Rep::Fq(fns, c) => (fns.divrem)(q.as_mut_ptr(), r.as_mut_ptr(), f.as_ptr(), g.as_ptr(), c),
            _ => check(sys::gr_poly_divrem(gp_mut(&mut q), gp_mut(&mut r), gp(f), gp(g), base.ptr()))?,
        }
    }
    Ok((q, r))
}

/// Magma's division over the integers by a polynomial whose leading
/// coefficient is not a unit: see `divrem`.
fn floor_divrem(f: &Elem, g: &Elem) -> (Elem, Elem) {
    let ctx = f.ctx();
    let (lf, lg) = (len(f), len(g));
    let mut r = f.clone();
    let mut q = Elem::new(ctx);
    if lf < lg {
        return (q, r);
    }
    unsafe {
        let (rp, qp, gpz) = (fz_mut(&mut r), fz_mut(&mut q), fz(g));
        sys::fmpz_poly_fit_length(qp, (lf - lg + 1) as sys::slong);
        let lc = (*gpz).coeffs.add(lg - 1);
        let mut c: sys::fmpz = 0;
        for i in (lg - 1..lf).rev() {
            sys::fmpz_fdiv_q(&mut c, (*rp).coeffs.add(i), lc);
            if c != 0 {
                sys::fmpz_set((*qp).coeffs.add(i + 1 - lg), &c);
                sys::_fmpz_vec_scalar_submul_fmpz((*rp).coeffs.add(i + 1 - lg), (*gpz).coeffs, lg as sys::slong, &c);
            }
        }
        sys::fmpz_clear(&mut c);
        sys::_fmpz_poly_set_length(qp, (lf - lg + 1) as sys::slong);
        sys::_fmpz_poly_normalise(qp);
        sys::_fmpz_poly_normalise(rp);
    }
    (q, r)
}

/// The exact quotient `f / g`, if `g` divides `f`.
pub fn divides(f: &Elem, g: &Elem) -> GrResult<Option<Elem>> {
    let ctx = f.ctx();
    if len(g) == 0 {
        return Ok(if len(f) == 0 { Some(Elem::new(ctx)) } else { None });
    }
    if matches!(rep(base_of(ctx)), Rep::Z) {
        let mut q = Elem::new(ctx);
        let ok = unsafe { sys::fmpz_poly_divides(fz_mut(&mut q), fz(f), fz(g)) } != 0;
        return Ok(ok.then_some(q));
    }
    let (q, r) = divrem(f, g)?;
    Ok((r.is_zero() == Truth::True).then_some(q))
}

/// The pseudo-remainder `r` with `lc(g)^d f = q g + r`, `d = max(0, deg f -
/// deg g + 1)`, and `deg r < deg g`. `g` must be non-zero.
pub fn pseudo_rem(f: &Elem, g: &Elem) -> GrResult<Elem> {
    let ctx = f.ctx();
    let (lf, lg) = (len(f), len(g));
    if lg == 0 {
        return Err(GrError::Domain);
    }
    if lf < lg {
        return Ok(f.clone());
    }
    if matches!(rep(base_of(ctx)), Rep::Z) {
        let mut r = Elem::new(ctx);
        unsafe { sys::fmpz_poly_pseudo_rem_cohen(fz_mut(&mut r), fz(f), fz(g)) };
        return Ok(r);
    }
    // Scale by the leading coefficient before each step (Knuth's
    // algorithm R), which needs no division.
    let lc = lead(g);
    let mut r = f.clone();
    let x = ctx.generator()?;
    for _ in 0..lf - lg + 1 {
        let n = len(&r);
        r = r.poly_mul_scalar(&lc)?;
        if n >= lg {
            let c = r.poly_coeff(n - 1).div(&lc)?;
            let shift = x.pow_i64((n - lg) as i64)?;
            r = r.sub(&g.poly_mul_scalar(&c)?.mul(&shift)?)?;
        }
    }
    Ok(r)
}

/// `f^e mod g` for `e >= 0` over a field (0 for a constant `g`).
pub fn powmod(f: &Elem, e: &Integer, g: &Elem) -> GrResult<Elem> {
    let ctx = f.ctx();
    let base = base_of(ctx);
    if len(g) == 0 || e.sign() < 0 {
        return Err(GrError::Domain);
    }
    if len(g) == 1 {
        return Ok(Elem::new(ctx));
    }
    let f = divrem(f, g)?.1;
    let mut r = Elem::new(ctx);
    unsafe {
        match rep(base) {
            Rep::Nmod(m, true) => {
                let mut nr = NPoly::new(m);
                let mut ee = e.clone();
                sys::nmod_poly_powmod_fmpz_binexp(&mut nr.0, &nview(&f, m), ee.as_raw_mut(), &nview(g, m));
                return Ok(nr.into_elem(ctx));
            }
            Rep::FmpzMod(c, true) => sys::fmpz_mod_poly_powmod_fmpz_binexp(r.as_mut_ptr().cast(), f.as_ptr().cast(), e.as_raw(), g.as_ptr().cast(), c),
            Rep::Fq(fns, c) => (fns.powmod)(r.as_mut_ptr(), f.as_ptr(), e.as_raw(), g.as_ptr(), c),
            _ => {
                // Square and multiply, reducing as we go.
                let mut acc = Elem::one(ctx)?;
                let bits = e.bits();
                for i in (0..bits).rev() {
                    acc = divrem(&acc.sqr()?, g)?.1;
                    if e.fdiv_2exp(i).is_odd() {
                        acc = divrem(&acc.mul(&f)?, g)?.1;
                    }
                }
                return Ok(acc);
            }
        }
    }
    Ok(r)
}

// ----- content ---------------------------------------------------------------------

/// The content of a polynomial over the integers (non-negative).
pub fn content_z(f: &Elem) -> Integer {
    let mut c = Integer::zero();
    unsafe { sys::fmpz_poly_content(c.raw_mut_ptr(), fz(f)) };
    c
}

/// `f / c` for a divisor `c` of the content of an integer polynomial.
pub fn divexact_z(f: &Elem, c: &Integer) -> Elem {
    let mut r = Elem::new(f.ctx());
    unsafe { sys::fmpz_poly_scalar_divexact_fmpz(fz_mut(&mut r), fz(f), c.raw_ptr()) };
    r
}

/// The n with `f` the n-th cyclotomic polynomial, for a polynomial over the
/// integers; 0 if it is none.
pub fn cyclotomic_index(f: &Elem) -> u64 {
    unsafe { sys::fmpz_poly_is_cyclotomic(fz(f)) as u64 }
}

// ----- factorization ----------------------------------------------------------------

/// A factorization `unit * prod f_i^e_i`: over the integers the unit is the
/// content with the sign of `f` and the factors are primitive with positive
/// leading coefficients; over a field the unit is the leading coefficient
/// and the factors are monic.
pub struct Factored {
    pub unit: Elem,
    pub factors: Vec<(Elem, u64)>,
}

/// The factors of FLINT's factorization structures for fmpz_mod and finite
/// field polynomials.
unsafe fn raw_factors(ctx: &Rc<Ctx>, fac: &RawFac) -> Vec<(Elem, u64)> {
    (0..fac.num as usize).map(|i| unsafe { (from_raw(ctx, fac.poly.add(i).cast()), *fac.exp.add(i) as u64) }).collect()
}

unsafe fn nmod_factors(ctx: &Rc<Ctx>, fac: &sys::nmod_poly_factor_struct) -> Vec<(Elem, u64)> {
    (0..fac.num as usize).map(|i| unsafe { (from_raw(ctx, fac.p.add(i).cast()), *fac.exp.add(i) as u64) }).collect()
}

unsafe fn fmpz_factors(ctx: &Rc<Ctx>, fac: &sys::fmpz_poly_factor_struct) -> Vec<(Elem, u64)> {
    (0..fac.num as usize).map(|i| unsafe { (from_raw(ctx, fac.p.add(i).cast()), *fac.exp.add(i) as u64) }).collect()
}

/// A factorization structure of the kind used by `rep`, initialised.
struct Fac {
    raw: RawFac,
    nmod: sys::nmod_poly_factor_struct,
    fmpz: sys::fmpz_poly_factor_struct,
    rep: Rep,
}

impl Fac {
    fn new(rep: Rep) -> Fac {
        let mut f = Fac {
            raw: RawFac { poly: std::ptr::null_mut(), exp: std::ptr::null_mut(), num: 0, alloc: 0 },
            nmod: sys::nmod_poly_factor_struct::default(),
            fmpz: sys::fmpz_poly_factor_struct::default(),
            rep,
        };
        unsafe {
            match rep {
                Rep::Z | Rep::Q => sys::fmpz_poly_factor_init(&mut f.fmpz),
                Rep::Nmod(..) => sys::nmod_poly_factor_init(&mut f.nmod),
                Rep::FmpzMod(c, _) => sys::fmpz_mod_poly_factor_init((&mut f.raw as *mut RawFac).cast(), c),
                Rep::Fq(fns, c) => (fns.fac_init)((&mut f.raw as *mut RawFac).cast(), c),
                Rep::Generic => {}
            }
        }
        f
    }

    fn raw_ptr(&mut self) -> P {
        (&mut self.raw as *mut RawFac).cast()
    }

    fn factors(&self, ctx: &Rc<Ctx>) -> Vec<(Elem, u64)> {
        unsafe {
            match self.rep {
                Rep::Z | Rep::Q => fmpz_factors(ctx, &self.fmpz),
                Rep::Nmod(..) => nmod_factors(ctx, &self.nmod),
                Rep::FmpzMod(..) | Rep::Fq(..) => raw_factors(ctx, &self.raw),
                Rep::Generic => Vec::new(),
            }
        }
    }
}

impl Drop for Fac {
    fn drop(&mut self) {
        unsafe {
            match self.rep {
                Rep::Z | Rep::Q => sys::fmpz_poly_factor_clear(&mut self.fmpz),
                Rep::Nmod(..) => sys::nmod_poly_factor_clear(&mut self.nmod),
                Rep::FmpzMod(c, _) => sys::fmpz_mod_poly_factor_clear((&mut self.raw as *mut RawFac).cast(), c),
                Rep::Fq(fns, c) => (fns.fac_clear)((&mut self.raw as *mut RawFac).cast(), c),
                Rep::Generic => {}
            }
        }
    }
}

/// Monic associate over a field.
fn monic(f: &Elem) -> GrResult<Elem> {
    f.poly_mul_scalar(&lead(f).inv()?)
}

/// The factorization of a non-zero polynomial into irreducibles (see
/// `Factored`), over the integers, the rationals, prime residue rings and
/// finite fields.
pub fn factor(f: &Elem) -> GrResult<Factored> {
    let ctx = f.ctx();
    let base = base_of(ctx);
    if len(f) == 0 {
        return Err(GrError::Domain);
    }
    let r = rep(base);
    let mut fac = Fac::new(r);
    unsafe {
        match r {
            Rep::Z => {
                sys::fmpz_poly_factor(&mut fac.fmpz, fz(f));
                let unit = base_elem(base, (&fac.fmpz.c as *const sys::fmpz).cast());
                return Ok(Factored { unit, factors: fac.factors(ctx) });
            }
            Rep::Q => {
                let zx = zpoly_ctx();
                let num = QPoly::of(f).numerator(&zx);
                sys::fmpz_poly_factor(&mut fac.fmpz, fz(&num));
                let mut factors = Vec::with_capacity(fac.fmpz.num as usize);
                for (p, e) in fac.factors(&zx) {
                    factors.push((monic(&convert(ctx, &p)?)?, e));
                }
                return Ok(Factored { unit: lead(f), factors });
            }
            Rep::Nmod(m, true) => {
                sys::nmod_poly_factor(&mut fac.nmod, &nview(f, m));
            }
            Rep::FmpzMod(c, true) => sys::fmpz_mod_poly_factor(fac.raw_ptr().cast(), f.as_ptr().cast(), c),
            Rep::Fq(fns, c) => {
                let mut lc = Elem::new(base);
                (fns.factor)(fac.raw_ptr(), lc.as_mut_ptr(), f.as_ptr(), c);
            }
            _ => return Err(GrError::Unable),
        }
    }
    Ok(Factored { unit: lead(f), factors: fac.factors(ctx) })
}

/// The squarefree factorization `f = unit * prod g_i^i` with pairwise coprime
/// squarefree `g_i` (primitive with positive leading coefficient over the
/// integers, monic over a field), as the pairs `(g_i, i)` with `g_i` not
/// constant, in increasing order of `i`. Over the integers the unit is the
/// content with the sign of `f`.
pub fn factor_squarefree(f: &Elem) -> GrResult<Factored> {
    let ctx = f.ctx();
    let base = base_of(ctx);
    if len(f) == 0 {
        return Err(GrError::Domain);
    }
    let r = rep(base);
    let mut fac = Fac::new(r);
    let pieces = unsafe {
        match r {
            Rep::Z => {
                sys::fmpz_poly_factor_squarefree(&mut fac.fmpz, fz(f));
                let unit = base_elem(base, (&fac.fmpz.c as *const sys::fmpz).cast());
                return Ok(Factored { unit, factors: merge_by_exponent(fac.factors(ctx))? });
            }
            Rep::Q => {
                let zx = zpoly_ctx();
                let num = QPoly::of(f).numerator(&zx);
                sys::fmpz_poly_factor_squarefree(&mut fac.fmpz, fz(&num));
                let mut v = Vec::new();
                for (p, e) in fac.factors(&zx) {
                    v.push((monic(&convert(ctx, &p)?)?, e));
                }
                v
            }
            Rep::Nmod(m, true) => {
                sys::nmod_poly_factor_squarefree(&mut fac.nmod, &nview(&monic(f)?, m));
                fac.factors(ctx)
            }
            Rep::FmpzMod(c, true) => {
                sys::fmpz_mod_poly_factor_squarefree(fac.raw_ptr().cast(), monic(f)?.as_ptr().cast(), c);
                fac.factors(ctx)
            }
            Rep::Fq(fns, c) => {
                (fns.sqfree)(fac.raw_ptr(), monic(f)?.as_ptr(), c);
                fac.factors(ctx)
            }
            _ => return Err(GrError::Unable),
        }
    };
    Ok(Factored { unit: lead(f), factors: merge_by_exponent(pieces)? })
}

/// Multiply together the factors with equal exponents, dropping constants,
/// in increasing order of exponent.
fn merge_by_exponent(mut v: Vec<(Elem, u64)>) -> GrResult<Vec<(Elem, u64)>> {
    v.retain(|(p, _)| len(p) > 1);
    v.sort_by_key(|(_, e)| *e);
    let mut out: Vec<(Elem, u64)> = Vec::with_capacity(v.len());
    for (p, e) in v {
        match out.last_mut() {
            Some((q, k)) if *k == e => *q = q.mul(&p)?,
            _ => out.push((p, e)),
        }
    }
    Ok(out)
}

/// Whether a polynomial of positive degree is irreducible, over the
/// rings `factor` handles (over the integers it must also be primitive).
pub fn is_irreducible(f: &Elem) -> GrResult<bool> {
    let ctx = f.ctx();
    let base = base_of(ctx);
    if len(f) < 2 {
        return Ok(false);
    }
    unsafe {
        match rep(base) {
            Rep::Nmod(m, true) => Ok(sys::nmod_poly_is_irreducible(&nview(f, m)) != 0),
            Rep::FmpzMod(c, true) => Ok(sys::fmpz_mod_poly_is_irreducible(f.as_ptr().cast(), c) != 0),
            Rep::Fq(fns, c) => Ok((fns.irreducible)(f.as_ptr(), c) != 0),
            Rep::Z | Rep::Q => {
                let fac = factor(f)?;
                let unit_ok = matches!(rep(base), Rep::Q) || fac.unit.is_one() == Truth::True || fac.unit.is_neg_one() == Truth::True;
                Ok(unit_ok && fac.factors.len() == 1 && fac.factors[0].1 == 1)
            }
            _ => Err(GrError::Unable),
        }
    }
}

/// The roots in the coefficient ring with their multiplicities (unsorted):
/// over the integers, the rationals, prime residue rings and finite fields.
pub fn roots(f: &Elem) -> GrResult<Vec<(Elem, u64)>> {
    let ctx = f.ctx();
    let base = base_of(ctx);
    if len(f) == 0 {
        return Err(GrError::Domain);
    }
    let r = rep(base);
    // Roots from monic linear factors x + c.
    let from_linear = |v: Vec<(Elem, u64)>| -> GrResult<Vec<(Elem, u64)>> {
        let mut out = Vec::new();
        for (p, e) in v {
            if len(&p) == 2 {
                out.push((p.poly_coeff(0).neg()?.div(&p.poly_coeff(1))?, e));
            }
        }
        Ok(out)
    };
    let mut fac = Fac::new(r);
    unsafe {
        match r {
            Rep::Z => {
                // Integer roots come from the linear factors x - a.
                let v = factor(f)?.factors.into_iter().filter(|(p, _)| len(p) == 2 && p.poly_coeff(1).is_one() == Truth::True).collect();
                from_linear(v)
            }
            Rep::Q => from_linear(factor(f)?.factors),
            Rep::Nmod(m, true) => {
                sys::nmod_poly_roots(&mut fac.nmod, &nview(f, m), 1);
                from_linear(fac.factors(ctx))
            }
            Rep::FmpzMod(c, true) => {
                sys::fmpz_mod_poly_roots(fac.raw_ptr().cast(), f.as_ptr().cast(), 1, c);
                from_linear(fac.factors(ctx))
            }
            Rep::Fq(fns, c) => {
                (fns.roots)(fac.raw_ptr(), f.as_ptr(), 1, c);
                from_linear(fac.factors(ctx))
            }
            _ => Err(GrError::Unable),
        }
    }
}

/// The distinct-degree factorization of a squarefree polynomial over a
/// finite field: pairs `(d, product of the monic irreducible factors of
/// degree d)` in increasing order of `d`.
pub fn distinct_degree(f: &Elem) -> GrResult<Vec<(u64, Elem)>> {
    let ctx = f.ctx();
    let base = base_of(ctx);
    if len(f) < 2 {
        return Ok(Vec::new());
    }
    let r = rep(base);
    let f = monic(f)?;
    let n = len(&f) - 1;
    let mut degs: Vec<sys::slong> = vec![0; n + 1];
    let dp = degs.as_mut_ptr();
    let mut fac = Fac::new(r);
    unsafe {
        match r {
            Rep::Nmod(m, true) => sys::nmod_poly_factor_distinct_deg(&mut fac.nmod, &nview(&f, m), &dp),
            Rep::FmpzMod(c, true) => sys::fmpz_mod_poly_factor_distinct_deg(fac.raw_ptr().cast(), f.as_ptr().cast(), &dp, c),
            Rep::Fq(fns, c) => (fns.ddf)(fac.raw_ptr(), f.as_ptr(), &dp, c),
            _ => return Err(GrError::Unable),
        }
    }
    // FLINT's order is that of its baby-step giant-step intervals.
    let mut v: Vec<(u64, Elem)> = fac.factors(ctx).into_iter().enumerate().map(|(i, (p, _))| (degs[i] as u64, p)).collect();
    v.sort_by_key(|(d, _)| *d);
    Ok(v)
}

/// The irreducible factors of a monic squarefree polynomial over a finite
/// field whose irreducible factors all have degree `d`.
pub fn equal_degree(f: &Elem, d: u64) -> GrResult<Vec<Elem>> {
    let ctx = f.ctx();
    let base = base_of(ctx);
    if len(f) < 2 || d == 0 || (len(f) - 1) as u64 % d != 0 {
        return Err(GrError::Domain);
    }
    let r = rep(base);
    let f = monic(f)?;
    let mut fac = Fac::new(r);
    unsafe {
        match r {
            Rep::Nmod(m, true) => {
                sys::nmod_poly_factor_equal_deg(&mut fac.nmod, &nview(&f, m), d as sys::slong);
            }
            Rep::FmpzMod(c, true) => sys::fmpz_mod_poly_factor_equal_deg(fac.raw_ptr().cast(), f.as_ptr().cast(), d as sys::slong, c),
            Rep::Fq(fns, c) => (fns.edf)(fac.raw_ptr(), f.as_ptr(), d as sys::slong, c),
            _ => return Err(GrError::Unable),
        }
    }
    Ok(fac.factors(ctx).into_iter().map(|(p, _)| p).collect())
}

// ----- resultants ------------------------------------------------------------------

/// The resultant, over any commutative ring (as the determinant of the
/// Sylvester matrix where the Euclidean algorithm needs a non-unit
/// inverted).
pub fn resultant(f: &Elem, g: &Elem) -> GrResult<Elem> {
    let ctx = f.ctx();
    let base = base_of(ctx);
    let mut r = Elem::new(base);
    unsafe {
        match rep(base) {
            Rep::Z => sys::fmpz_poly_resultant(r.as_mut_ptr().cast(), fz(f), fz(g)),
            Rep::Q => sys::fmpq_poly_resultant(r.as_mut_ptr().cast(), &QPoly::of(f).0, &QPoly::of(g).0),
            Rep::Nmod(m, true) => return Ok(Elem::from_word(base, sys::nmod_poly_resultant(&nview(f, m), &nview(g, m)) as u64)),
            Rep::FmpzMod(c, true) => sys::fmpz_mod_poly_resultant(r.as_mut_ptr().cast(), f.as_ptr().cast(), g.as_ptr().cast(), c),
            _ => {
                if sys::gr_poly_resultant(r.as_mut_ptr(), gp(f), gp(g), base.ptr()) != 0 {
                    check(sys::gr_poly_resultant_sylvester(r.as_mut_ptr(), gp(f), gp(g), base.ptr()))?;
                }
            }
        }
    }
    Ok(r)
}

/// The discriminant `(-1)^(n(n-1)/2) Res(f, f') / lc(f)` of a polynomial of
/// degree `n >= 1`, with `f'` taken to have formal degree `n - 1`.
pub fn discriminant(f: &Elem) -> GrResult<Elem> {
    let ctx = f.ctx();
    let base = base_of(ctx);
    let n = len(f);
    if n < 2 {
        return Err(GrError::Domain);
    }
    let mut r = Elem::new(base);
    unsafe {
        match rep(base) {
            Rep::Z => {
                sys::fmpz_poly_discriminant(r.as_mut_ptr().cast(), fz(f));
                return Ok(r);
            }
            Rep::Q => {
                sys::fmpq_poly_discriminant(r.as_mut_ptr().cast(), &QPoly::of(f).0);
                return Ok(r);
            }
            Rep::Nmod(m, true) => return Ok(Elem::from_word(base, sys::nmod_poly_discriminant(&nview(f, m)) as u64)),
            Rep::FmpzMod(c, true) => {
                sys::fmpz_mod_poly_discriminant(r.as_mut_ptr().cast(), f.as_ptr().cast(), c);
                return Ok(r);
            }
            _ => {}
        }
    }
    if n == 2 {
        return Elem::one(base);
    }
    // Res(f, f') for the actual degree of f' differs from the one with
    // formal degree n - 2 by the factor lc(f)^(n - 2 - deg f').
    let d = f.poly_derivative()?;
    let lc = lead(f);
    let res = resultant(f, &d)?;
    let deg = n - 1;
    let dd = len(&d).saturating_sub(1);
    let mut v = res.mul(&lc.pow_i64((deg - 1 - dd) as i64)?)?;
    // Divide by lc(f), exactly (the resultant has it as a factor).
    v = v.divexact(&lc).or_else(|_| v.div(&lc))?;
    if (deg * (deg - 1) / 2) % 2 == 1 {
        v = v.neg()?;
    }
    Ok(v)
}

// ----- Hensel lifting --------------------------------------------------------------

/// Lift the factorization modulo a prime `p` of the integer polynomial `f`
/// (monic squarefree `factors` over Z/pZ whose product is `f` mod p up to
/// its leading coefficient) to one modulo `p^n`, as integer polynomials
/// with coefficients in `[0, p^n)`, in the order of `factors`.
pub fn hensel_lift(f: &Elem, factors: &[Elem], n: u64) -> GrResult<Vec<Elem>> {
    let zx = f.ctx();
    let Some(first) = factors.first() else { return Ok(Vec::new()) };
    let Rep::Nmod(m, true) = rep(base_of(first.ctx())) else { return Err(GrError::Unable) };
    if factors.len() == 1 {
        return Ok(vec![f.clone()]);
    }
    let mut local = sys::nmod_poly_factor_struct::default();
    let mut lifted = sys::fmpz_poly_factor_struct::default();
    let out;
    unsafe {
        sys::nmod_poly_factor_init(&mut local);
        for p in factors {
            sys::nmod_poly_factor_insert(&mut local, &nview(p, m), 1);
        }
        sys::fmpz_poly_factor_init(&mut lifted);
        sys::fmpz_poly_hensel_lift_once(&mut lifted, fz(f), &local, n as sys::slong);
        out = fmpz_factors(zx, &lifted);
        sys::fmpz_poly_factor_clear(&mut lifted);
        sys::nmod_poly_factor_clear(&mut local);
    }
    // FLINT returns the lifted factors in its own order: match them with
    // the factors they reduce to.
    let pctx = first.ctx();
    let mut result: Vec<Option<Elem>> = vec![None; factors.len()];
    for (g, _) in out {
        let red = monic(&convert(pctx, &g)?)?;
        let i = factors.iter().enumerate().position(|(i, p)| result[i].is_none() && p.equal(&red) == Truth::True).ok_or(GrError::Unable)?;
        result[i] = Some(g);
    }
    result.into_iter().map(|g| g.ok_or(GrError::Unable)).collect()
}

// ----- special polynomials ---------------------------------------------------------

/// The n-th Swinnerton-Dyer polynomial `prod (x +- sqrt(2) +- ... +- sqrt(p_n))`
/// in the integer polynomial ring `zx`.
pub fn swinnerton_dyer(zx: &Rc<Ctx>, n: u64) -> Elem {
    let mut f = Elem::new(zx);
    unsafe { sys::fmpz_poly_swinnerton_dyer(fz_mut(&mut f), n as sys::ulong) };
    f
}

/// The classical families with FLINT constructions.
#[derive(Clone, Copy)]
pub enum Family {
    /// Chebyshev polynomials of the first kind, over Z.
    ChebyshevT,
    /// Chebyshev polynomials of the second kind `U_n`, over Z.
    ChebyshevU,
    /// Hermite polynomials (physicists'), over Z.
    Hermite,
    /// Legendre polynomials, over Q.
    Legendre,
    /// Laguerre polynomials, over Q.
    Laguerre,
    /// Bernoulli polynomials, over Q.
    Bernoulli,
}

/// The n-th polynomial of a family in `ctx`, a polynomial ring over the
/// integers or the rationals as the family has it.
pub fn family(ctx: &Rc<Ctx>, fam: Family, n: u64) -> Elem {
    let n = n as sys::ulong;
    let mut f = Elem::new(ctx);
    unsafe {
        match fam {
            Family::ChebyshevT => sys::fmpz_poly_chebyshev_t(fz_mut(&mut f), n),
            Family::ChebyshevU => sys::fmpz_poly_chebyshev_u(fz_mut(&mut f), n),
            Family::Hermite => sys::fmpz_poly_hermite_h(fz_mut(&mut f), n),
            Family::Legendre | Family::Laguerre | Family::Bernoulli => {
                let mut q = QPoly::new();
                match fam {
                    Family::Legendre => sys::fmpq_poly_legendre_p(&mut q.0, n),
                    Family::Laguerre => sys::fmpq_poly_laguerre_l(&mut q.0, n),
                    _ => sys::arith_bernoulli_polynomial(&mut q.0, n),
                }
                return q.to_elem(ctx);
            }
        }
    }
    f
}

/// The rational numbers as coefficients, for callers that build rational
/// polynomials.
pub fn rational_coeff(f: &Elem, i: usize) -> Option<Rational> {
    f.poly_coeff(i).to_rational().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Elements that meet in one operation must share their context, so the
    // helpers take the polynomial ring rather than making one per call.
    fn zpoly(cs: &[i64]) -> Elem {
        over(&zpoly_ctx(), cs)
    }

    fn coeffs_i64(f: &Elem) -> Vec<i64> {
        (0..len(f)).map(|i| f.poly_coeff(i).to_integer().unwrap().to_i64().unwrap()).collect()
    }

    fn over(px: &Rc<Ctx>, cs: &[i64]) -> Elem {
        let base = px.base().unwrap();
        let v: Vec<Elem> = cs.iter().map(|&c| Elem::from_i64(base, c).unwrap()).collect();
        Elem::poly_from_coeffs(px, &v).unwrap()
    }

    fn residue_poly(n: i64) -> Rc<Ctx> {
        Ctx::poly(&Ctx::residue_ring(&Integer::from_i64(n)))
    }

    #[test]
    fn integer_division_floors() {
        // 3x^5 - 2x^3 + 7x^2 + 1 by 2x^2 + 1, as Magma divides.
        let (q, r) = divrem(&zpoly(&[1, 0, 7, -2, 0, 3]), &zpoly(&[1, 0, 2])).unwrap();
        assert_eq!(coeffs_i64(&q), vec![3, -2, 0, 1]);
        assert_eq!(coeffs_i64(&r), vec![-2, 2, 1, 1, 0, 1]);
        let (q, r) = divrem(&zpoly(&[0, 0, 3]), &zpoly(&[0, -2])).unwrap();
        assert_eq!((coeffs_i64(&q), coeffs_i64(&r)), (vec![0, -2], vec![0, 0, -1]));
        // A unit leading coefficient divides fully.
        let (q, r) = divrem(&zpoly(&[1, 0, 7, -2, 0, 3]), &zpoly(&[1, 0, 1])).unwrap();
        assert_eq!((coeffs_i64(&q), coeffs_i64(&r)), (vec![7, -5, 0, 3], vec![-6, 5]));
    }

    #[test]
    fn integer_gcd_factor() {
        let g = gcd(&zpoly(&[-6, 0, 6]), &zpoly(&[4, 8, 4])).unwrap();
        assert_eq!(coeffs_i64(&g), vec![2, 2]);
        let fac = factor(&zpoly(&[0, 6, 0, -12, 0, 6])).unwrap();
        assert_eq!(fac.unit.to_integer().unwrap(), Integer::from_i64(6));
        let mut fs: Vec<(Vec<i64>, u64)> = fac.factors.iter().map(|(p, e)| (coeffs_i64(p), *e)).collect();
        fs.sort();
        assert_eq!(fs, vec![(vec![-1, 1], 2), (vec![0, 1], 1), (vec![1, 1], 2)]);
        assert!(is_irreducible(&zpoly(&[1, 0, 1])).unwrap());
        assert!(!is_irreducible(&zpoly(&[2, 0, 2])).unwrap());
        let r: Vec<i64> = roots(&zpoly(&[0, -1, 0, 1])).unwrap().iter().map(|(r, _)| r.to_integer().unwrap().to_i64().unwrap()).collect();
        assert_eq!(r.len(), 3);
        assert_eq!(resultant(&zpoly(&[1, 0, 1]), &zpoly(&[-2, 0, 0, 1])).unwrap().to_integer().unwrap(), Integer::from_i64(5));
        assert_eq!(discriminant(&zpoly(&[5, -1, 0, 3])).unwrap().to_integer().unwrap(), Integer::from_i64(-6063));
    }

    #[test]
    fn modular() {
        let f7 = residue_poly(7);
        // z^6 - 1 splits into linear factors over GF(7).
        let f = over(&f7, &[-1, 0, 0, 0, 0, 0, 1]);
        assert_eq!(factor(&f).unwrap().factors.len(), 6);
        assert_eq!(roots(&f).unwrap().len(), 6);
        let (d, a, b) = xgcd(&over(&f7, &[3, 0, 3]), &over(&f7, &[5, 2])).unwrap();
        assert_eq!(coeffs_i64_mod(&d), vec![1]);
        assert_eq!(coeffs_i64_mod(&a), vec![6]);
        assert_eq!(coeffs_i64_mod(&b), vec![5, 5]);
        // (z + 1)^100 mod z^3 + z + 1 over GF(5).
        let f5 = residue_poly(5);
        let p = powmod(&over(&f5, &[1, 1]), &Integer::from_i64(100), &over(&f5, &[1, 1, 0, 1])).unwrap();
        assert_eq!(coeffs_i64_mod(&p), vec![3, 2, 4]);
        // Composite moduli are not fields.
        let z12 = residue_poly(12);
        assert!(factor(&over(&z12, &[1, 0, 1])).is_err());
        assert!(!over_field(&z12));
    }

    fn coeffs_i64_mod(f: &Elem) -> Vec<i64> {
        (0..len(f)).map(|i| f.poly_coeff(i).to_integer().unwrap().to_i64().unwrap()).collect()
    }

    #[test]
    fn rationals() {
        let qq = Ctx::rationals();
        let qx = Ctx::poly(&qq);
        let q = |n: i64, d: i64| Elem::from_rational(&qq, &Rational::new(&Integer::from_i64(n), &Integer::from_i64(d)).unwrap()).unwrap();
        // (y^2/2 + 1, y - 1/3) has resultant 19/18.
        let f = Elem::poly_from_coeffs(&qx, &[q(1, 1), q(0, 1), q(1, 2)]).unwrap();
        let g = Elem::poly_from_coeffs(&qx, &[q(-1, 3), q(1, 1)]).unwrap();
        assert_eq!(resultant(&f, &g).unwrap().to_rational().unwrap(), Rational::new(&Integer::from_i64(19), &Integer::from_i64(18)).unwrap());
        let h = f.mul(&g).unwrap().mul(&g).unwrap();
        let sq = factor_squarefree(&h).unwrap();
        assert_eq!(sq.factors.len(), 2);
        assert_eq!(sq.factors[1].1, 2);
        assert!(sq.factors[1].0.equal(&g) == Truth::True);
    }

    #[test]
    fn special_and_generic() {
        // S_2 = x^4 - 10x^2 + 1.
        let zx = Ctx::poly(&Ctx::integers());
        assert_eq!(coeffs_i64(&swinnerton_dyer(&zx, 2)), vec![1, 0, -10, 0, 1]);
        // Over Z/6 the Euclidean resultant fails; the Sylvester determinant
        // gives Res(3x^2 + 2x + 1, x + 5) = 3 + 2 + 1 = 0.
        let z6 = residue_poly(6);
        assert!(resultant(&over(&z6, &[1, 2, 3]), &over(&z6, &[5, 1])).unwrap().is_zero() == Truth::True);
        assert_eq!(resultant(&over(&z6, &[1, 1]), &over(&z6, &[2, 1])).unwrap().to_integer().unwrap(), Integer::from_i64(1));
        assert!(!can_factor(&z6) && !over_finite_field(&z6));
        // Distinct-degree factorization by increasing degree.
        let f7 = residue_poly(7);
        let g = over(&f7, &[1, 0, 1]).mul(&over(&f7, &[2, 3, 1])).unwrap().mul(&over(&f7, &[1, 1, 0, 1])).unwrap();
        let ddf: Vec<(u64, Vec<i64>)> = distinct_degree(&g).unwrap().iter().map(|(d, p)| (*d, coeffs_i64_mod(p))).collect();
        assert_eq!(ddf, vec![(1, vec![2, 3, 1]), (2, vec![1, 0, 1]), (3, vec![1, 1, 0, 1])]);
    }

    #[test]
    fn hensel() {
        // The handbook's example: x^5 - x^3 + 2x^2 - 2 modulo 5^3.
        let f = zpoly(&[-2, 0, 2, -1, 0, 1]);
        let f5 = residue_poly(5);
        let fs = vec![over(&f5, &[1, 1]), over(&f5, &[3, 1]), over(&f5, &[4, 1]), over(&f5, &[4, 2, 1])];
        let lifted = hensel_lift(&f, &fs, 3).unwrap();
        let cs: Vec<Vec<i64>> = lifted.iter().map(|g| coeffs_i64(g).iter().map(|c| c.rem_euclid(125)).collect()).collect();
        assert_eq!(cs, vec![vec![1, 1], vec![53, 1], vec![124, 1], vec![59, 72, 1]]);
    }
}
