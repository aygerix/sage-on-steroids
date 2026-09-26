//! Finite fields of small characteristic with their elements packed into
//! words, as FLINT generic-ring contexts implemented here: GF(2^n) with n up
//! to 512, whose elements are the bits of their coordinates
//! (`gf2x::Gf2Words`), and GF(p^n) for odd p below 2^16 with n up to 64 (p
//! below 2^8) or 32, whose coordinates take a byte or two each
//! (`lanes::FpLanes`).
//!
//! An element takes at most eight words and holds no pointers, so an `Elem`
//! keeps it inline and arithmetic never allocates (FLINT's `fq_nmod` keeps
//! each element's polynomial on the heap and multiplies by Kronecker
//! substitution). Each context carries an `fq_nmod` context for the same
//! field, its companion, for what FLINT does only on its own types:
//! multiplicative orders, square roots and roots of polynomials.

use std::ffi::{CString, c_int, c_void};
use std::rc::Rc;

use flint3_sys as sys;

use crate::Integer;
use crate::gf2x::Gf2Words;
use crate::lanes::{FpLanes, Lane};
use crate::gr::{Ctx, CtxKind, Elem, GrError, GrResult};

type GrCtx = *mut sys::gr_ctx_struct;

const SUCCESS: c_int = 0;
const DOMAIN: c_int = 1;
const TAB_SIZE: usize = sys::gr_method_GR_METHOD_TAB_SIZE as usize;

/// The arithmetic of one packed representation.
pub(crate) trait Kernel: 'static {
    /// An element: at most eight words, without pointers.
    type E: Copy + Eq;
    fn zero(&self) -> Self::E;
    /// The element c of the prime field, for c below p.
    fn scalar(&self, c: u64) -> Self::E;
    /// The root of the modulus.
    fn generator(&self) -> Self::E;
    fn add(&self, a: &Self::E, b: &Self::E) -> Self::E;
    fn sub(&self, a: &Self::E, b: &Self::E) -> Self::E;
    fn neg(&self, a: &Self::E) -> Self::E;
    fn mul(&self, a: &Self::E, b: &Self::E) -> Self::E;
    /// a*c for c below p.
    fn mul_scalar(&self, a: &Self::E, c: u64) -> Self::E;
    fn sqr(&self, a: &Self::E) -> Self::E;
    /// The inverse of a unit.
    fn inv(&self, a: &Self::E) -> Option<Self::E>;
    /// a^e for the exponent with the given words (least significant first).
    fn pow(&self, a: &Self::E, e: &[u64]) -> Self::E;
    /// a^(p^k), for k below n.
    fn frobenius(&self, a: &Self::E, k: u64) -> Self::E;
    /// The absolute trace and norm, below p.
    fn trace(&self, a: &Self::E) -> u64;
    fn norm(&self, a: &Self::E) -> u64;
    /// The n coordinates in the power basis of the generator (constant term
    /// first), and the element with the given ones (below p; missing ones
    /// are zero).
    fn coords(&self, a: &Self::E) -> Vec<u64>;
    fn from_coords(&self, c: &[u64]) -> Self::E;
    /// The n coordinates of a written to `out`.
    fn coords_into(&self, a: &Self::E, out: &mut [u64]);
    /// The element c_0 + c_1 x + ... for at most 2n - 1 coefficients c_i
    /// below p, reduced modulo the modulus.
    fn reduce_coeffs(&self, c: &[u64]) -> Self::E;
    /// The length of the shorter factor from which products of polynomials
    /// go by Kronecker substitution (see `poly_mullow`).
    fn ks_cutoff(&self) -> usize;
}

impl<const W: usize> Kernel for Gf2Words<W> {
    type E = [u64; W];

    fn zero(&self) -> [u64; W] {
        [0; W]
    }

    fn scalar(&self, c: u64) -> [u64; W] {
        let mut r = [0; W];
        r[0] = c & 1;
        r
    }

    fn generator(&self) -> [u64; W] {
        // x, which is g modulo x + g in degree 1.
        if self.degree() == 1 { self.scalar(self.modulus_low()[0]) } else { self.from_coords(&[0, 1]) }
    }

    fn add(&self, a: &[u64; W], b: &[u64; W]) -> [u64; W] {
        std::array::from_fn(|i| a[i] ^ b[i])
    }

    fn sub(&self, a: &[u64; W], b: &[u64; W]) -> [u64; W] {
        std::array::from_fn(|i| a[i] ^ b[i])
    }

    fn neg(&self, a: &[u64; W]) -> [u64; W] {
        *a
    }

    fn mul(&self, a: &[u64; W], b: &[u64; W]) -> [u64; W] {
        Gf2Words::mul(self, a, b)
    }

    fn mul_scalar(&self, a: &[u64; W], c: u64) -> [u64; W] {
        if c & 1 == 1 { *a } else { [0; W] }
    }

    fn sqr(&self, a: &[u64; W]) -> [u64; W] {
        Gf2Words::sqr(self, a)
    }

    fn inv(&self, a: &[u64; W]) -> Option<[u64; W]> {
        Gf2Words::inv(self, a)
    }

    fn pow(&self, a: &[u64; W], e: &[u64]) -> [u64; W] {
        Gf2Words::pow(self, a, e)
    }

    fn frobenius(&self, a: &[u64; W], k: u64) -> [u64; W] {
        self.sqr_n(a, k)
    }

    fn trace(&self, a: &[u64; W]) -> u64 {
        Gf2Words::trace(self, a)
    }

    fn norm(&self, a: &[u64; W]) -> u64 {
        (*a != [0; W]) as u64
    }

    fn coords(&self, a: &[u64; W]) -> Vec<u64> {
        (0..self.degree() as usize).map(|i| a[i / 64] >> (i % 64) & 1).collect()
    }

    fn from_coords(&self, c: &[u64]) -> [u64; W] {
        let mut r = [0; W];
        for (i, &x) in c.iter().enumerate().take(self.degree() as usize) {
            r[i / 64] |= (x & 1) << (i % 64);
        }
        r
    }

    fn coords_into(&self, a: &[u64; W], out: &mut [u64]) {
        for (i, x) in out.iter_mut().enumerate() {
            *x = a[i / 64] >> (i % 64) & 1;
        }
    }

    fn reduce_coeffs(&self, c: &[u64]) -> [u64; W] {
        Gf2Words::reduce_coeffs(self, c)
    }

    /// A bit takes a word in FLINT's polynomials over F_2, so substitution
    /// pays only for long products.
    fn ks_cutoff(&self) -> usize {
        3 * self.degree() as usize
    }
}

impl<T: Lane, const N: usize> Kernel for FpLanes<T, N> {
    type E = [T; N];

    fn zero(&self) -> [T; N] {
        [T::default(); N]
    }

    fn scalar(&self, c: u64) -> [T; N] {
        FpLanes::scalar(self, c)
    }

    fn generator(&self) -> [T; N] {
        FpLanes::generator(self)
    }

    fn add(&self, a: &[T; N], b: &[T; N]) -> [T; N] {
        FpLanes::add(self, a, b)
    }

    fn sub(&self, a: &[T; N], b: &[T; N]) -> [T; N] {
        FpLanes::sub(self, a, b)
    }

    fn neg(&self, a: &[T; N]) -> [T; N] {
        FpLanes::neg(self, a)
    }

    fn mul(&self, a: &[T; N], b: &[T; N]) -> [T; N] {
        FpLanes::mul(self, a, b)
    }

    fn mul_scalar(&self, a: &[T; N], c: u64) -> [T; N] {
        FpLanes::mul_scalar(self, a, c)
    }

    fn sqr(&self, a: &[T; N]) -> [T; N] {
        FpLanes::sqr(self, a)
    }

    fn inv(&self, a: &[T; N]) -> Option<[T; N]> {
        FpLanes::inv(self, a)
    }

    fn pow(&self, a: &[T; N], e: &[u64]) -> [T; N] {
        FpLanes::pow(self, a, e)
    }

    fn frobenius(&self, a: &[T; N], k: u64) -> [T; N] {
        FpLanes::frobenius(self, a, k)
    }

    fn trace(&self, a: &[T; N]) -> u64 {
        FpLanes::trace(self, a)
    }

    fn norm(&self, a: &[T; N]) -> u64 {
        FpLanes::norm(self, a)
    }

    fn coords(&self, a: &[T; N]) -> Vec<u64> {
        FpLanes::coords(self, a)
    }

    fn from_coords(&self, c: &[u64]) -> [T; N] {
        FpLanes::from_coords(self, c)
    }

    fn coords_into(&self, a: &[T; N], out: &mut [u64]) {
        for (x, y) in out.iter_mut().zip(a) {
            *x = y.get() as u64;
        }
    }

    fn reduce_coeffs(&self, c: &[u64]) -> [T; N] {
        FpLanes::reduce_coeffs(self, c)
    }

    fn ks_cutoff(&self) -> usize {
        6
    }
}

/// What a packed field context holds whatever its kernel (the first word
/// of the gr context points to it, and the kernel follows, in `Packed`).
#[repr(C)]
pub(crate) struct Head {
    p: u64,
    n: u64,
    /// q - 1, which exponents of units reduce modulo.
    qm1: Integer,
    /// The same field over FLINT's fq_nmod, with the same modulus.
    companion: Rc<Ctx>,
    methods: Box<[sys::gr_funcptr; TAB_SIZE]>,
    /// The kernel's coordinates of the element at a pointer, and the
    /// element with the given coordinates written at one.
    coords: unsafe fn(&Head, *const c_void) -> Vec<u64>,
    from_coords: unsafe fn(&Head, &[u64], *mut c_void),
}

#[repr(C)]
struct Packed<K> {
    head: Head,
    k: K,
}

impl Head {
    /// The element of the companion with the coordinates of the one at x.
    unsafe fn to_companion(&self, x: *const c_void) -> Elem {
        Elem::fq_from_coords_u64(&self.companion, &unsafe { (self.coords)(self, x) })
    }

    /// Write at r the element with the coordinates of the fq_nmod element
    /// at x.
    unsafe fn from_fq_nmod(&self, x: *const c_void, r: *mut c_void) {
        let a = unsafe { &*(x as *const sys::nmod_poly_struct) };
        let c: Vec<u64> = (0..a.length as usize).map(|i| unsafe { *a.coeffs.add(i) } as u64).collect();
        unsafe { (self.from_coords)(self, &c, r) }
    }
}

unsafe fn coords_of<K: Kernel>(h: &Head, x: *const c_void) -> Vec<u64> {
    let k = unsafe { &(*(h as *const Head as *const Packed<K>)).k };
    k.coords(&unsafe { get::<K>(x) })
}

unsafe fn from_coords_of<K: Kernel>(h: &Head, c: &[u64], r: *mut c_void) {
    let k = unsafe { &(*(h as *const Head as *const Packed<K>)).k };
    unsafe { put::<K>(r, k.from_coords(c)) }
}

unsafe fn packed<'a, K>(ctx: GrCtx) -> &'a Packed<K> {
    unsafe { &*std::ptr::read_unaligned((*ctx).data.as_ptr() as *const *const Packed<K>) }
}

unsafe fn head<'a>(ctx: GrCtx) -> &'a Head {
    unsafe { &*std::ptr::read_unaligned((*ctx).data.as_ptr() as *const *const Head) }
}

unsafe fn kernel<'a, K>(ctx: GrCtx) -> &'a K {
    unsafe { &packed::<K>(ctx).k }
}

/// Elements are read by value, so that the result may be written where an
/// argument lives.
unsafe fn get<K: Kernel>(x: *const c_void) -> K::E {
    unsafe { *(x as *const K::E) }
}

unsafe fn put<K: Kernel>(r: *mut c_void, v: K::E) {
    unsafe { *(r as *mut K::E) = v }
}

fn truth(b: bool) -> sys::truth_t {
    if b { sys::truth_t_T_TRUE } else { sys::truth_t_T_FALSE }
}

// ----- the gr methods ------------------------------------------------------

unsafe extern "C" fn ctx_clear<K: Kernel>(ctx: GrCtx) {
    unsafe { drop(Box::from_raw(packed::<K>(ctx) as *const Packed<K> as *mut Packed<K>)) }
}

unsafe extern "C" fn ctx_write(out: *mut sys::gr_stream_struct, ctx: GrCtx) -> c_int {
    let h = unsafe { head(ctx) };
    let s = CString::new(format!("Finite field (packed) of order {}^{}", h.p, h.n)).unwrap();
    unsafe { sys::gr_stream_write(out, s.as_ptr()) }
}

unsafe extern "C" fn init<K: Kernel>(x: *mut c_void, ctx: GrCtx) {
    unsafe { put::<K>(x, kernel::<K>(ctx).zero()) }
}

unsafe extern "C" fn clear(_x: *mut c_void, _ctx: GrCtx) {}

unsafe extern "C" fn swap<K: Kernel>(x: *mut c_void, y: *mut c_void, _ctx: GrCtx) {
    unsafe { std::ptr::swap(x as *mut K::E, y as *mut K::E) }
}

unsafe extern "C" fn set_shallow<K: Kernel>(r: *mut c_void, x: *const c_void, _ctx: GrCtx) {
    unsafe { put::<K>(r, get::<K>(x)) }
}

unsafe extern "C" fn set<K: Kernel>(r: *mut c_void, x: *const c_void, _ctx: GrCtx) -> c_int {
    unsafe { put::<K>(r, get::<K>(x)) };
    SUCCESS
}

unsafe extern "C" fn randtest<K: Kernel>(r: *mut c_void, state: *mut sys::flint_rand_struct, ctx: GrCtx) -> c_int {
    let pk = unsafe { packed::<K>(ctx) };
    let c: Vec<u64> = (0..pk.head.n).map(|_| unsafe { sys::n_randint(state, pk.head.p as sys::ulong) } as u64).collect();
    unsafe { put::<K>(r, pk.k.from_coords(&c)) };
    SUCCESS
}

/// FLINT's rendering of the element of the companion.
unsafe extern "C" fn write(out: *mut sys::gr_stream_struct, x: *const c_void, ctx: GrCtx) -> c_int {
    let s = CString::new(unsafe { head(ctx).to_companion(x) }.to_flint_string()).unwrap();
    unsafe { sys::gr_stream_write(out, s.as_ptr()) }
}

unsafe extern "C" fn zero<K: Kernel>(r: *mut c_void, ctx: GrCtx) -> c_int {
    unsafe { put::<K>(r, kernel::<K>(ctx).zero()) };
    SUCCESS
}

unsafe extern "C" fn one<K: Kernel>(r: *mut c_void, ctx: GrCtx) -> c_int {
    unsafe { put::<K>(r, kernel::<K>(ctx).scalar(1)) };
    SUCCESS
}

unsafe extern "C" fn neg_one<K: Kernel>(r: *mut c_void, ctx: GrCtx) -> c_int {
    unsafe { put::<K>(r, kernel::<K>(ctx).scalar(head(ctx).p - 1)) };
    SUCCESS
}

unsafe extern "C" fn generator<K: Kernel>(r: *mut c_void, ctx: GrCtx) -> c_int {
    unsafe { put::<K>(r, kernel::<K>(ctx).generator()) };
    SUCCESS
}

unsafe extern "C" fn is_zero<K: Kernel>(x: *const c_void, ctx: GrCtx) -> sys::truth_t {
    truth(unsafe { get::<K>(x) == kernel::<K>(ctx).zero() })
}

unsafe extern "C" fn is_one<K: Kernel>(x: *const c_void, ctx: GrCtx) -> sys::truth_t {
    truth(unsafe { get::<K>(x) == kernel::<K>(ctx).scalar(1) })
}

unsafe extern "C" fn is_neg_one<K: Kernel>(x: *const c_void, ctx: GrCtx) -> sys::truth_t {
    truth(unsafe { get::<K>(x) == kernel::<K>(ctx).scalar(head(ctx).p - 1) })
}

unsafe extern "C" fn equal<K: Kernel>(x: *const c_void, y: *const c_void, _ctx: GrCtx) -> sys::truth_t {
    truth(unsafe { get::<K>(x) == get::<K>(y) })
}

unsafe extern "C" fn set_si<K: Kernel>(r: *mut c_void, v: sys::slong, ctx: GrCtx) -> c_int {
    let c = (v as i128).rem_euclid(unsafe { head(ctx).p } as i128) as u64;
    unsafe { put::<K>(r, kernel::<K>(ctx).scalar(c)) };
    SUCCESS
}

unsafe extern "C" fn set_ui<K: Kernel>(r: *mut c_void, v: sys::ulong, ctx: GrCtx) -> c_int {
    unsafe { put::<K>(r, kernel::<K>(ctx).scalar(v as u64 % head(ctx).p)) };
    SUCCESS
}

unsafe extern "C" fn set_fmpz<K: Kernel>(r: *mut c_void, v: *const sys::fmpz, ctx: GrCtx) -> c_int {
    unsafe { put::<K>(r, kernel::<K>(ctx).scalar(sys::fmpz_fdiv_ui(v, head(ctx).p as sys::ulong) as u64)) };
    SUCCESS
}

/// From the same context, the integers modulo p, and what gr's generic
/// conversion knows (integers and rationals).
unsafe extern "C" fn set_other<K: Kernel>(r: *mut c_void, x: *const c_void, xctx: GrCtx, ctx: GrCtx) -> c_int {
    unsafe {
        if xctx == ctx {
            return set::<K>(r, x, ctx);
        }
        let nmod = sys::gr_which_structure_GR_CTX_NMOD as sys::ulong;
        if (*xctx).which_ring == nmod && (*((*xctx).data.as_ptr() as *const sys::nmod_t)).n as u64 == head(ctx).p {
            return set_ui::<K>(r, *(x as *const sys::ulong), ctx);
        }
        sys::gr_generic_set_other(r, x, xctx, ctx)
    }
}

macro_rules! unary {
    ($($name:ident => $op:ident),* $(,)?) => {
        $(
            unsafe extern "C" fn $name<K: Kernel>(r: *mut c_void, x: *const c_void, ctx: GrCtx) -> c_int {
                unsafe { put::<K>(r, kernel::<K>(ctx).$op(&get::<K>(x))) };
                SUCCESS
            }
        )*
    };
}

macro_rules! binary {
    ($($name:ident => $op:ident),* $(,)?) => {
        $(
            unsafe extern "C" fn $name<K: Kernel>(r: *mut c_void, x: *const c_void, y: *const c_void, ctx: GrCtx) -> c_int {
                unsafe { put::<K>(r, kernel::<K>(ctx).$op(&get::<K>(x), &get::<K>(y))) };
                SUCCESS
            }
        )*
    };
}

unary! { neg => neg, sqr => sqr }
binary! { add => add, sub => sub, mul => mul }

unsafe extern "C" fn mul_ui<K: Kernel>(r: *mut c_void, x: *const c_void, c: sys::ulong, ctx: GrCtx) -> c_int {
    unsafe { put::<K>(r, kernel::<K>(ctx).mul_scalar(&get::<K>(x), c as u64 % head(ctx).p)) };
    SUCCESS
}

unsafe extern "C" fn mul_si<K: Kernel>(r: *mut c_void, x: *const c_void, c: sys::slong, ctx: GrCtx) -> c_int {
    let c = (c as i128).rem_euclid(unsafe { head(ctx).p } as i128) as u64;
    unsafe { put::<K>(r, kernel::<K>(ctx).mul_scalar(&get::<K>(x), c)) };
    SUCCESS
}

unsafe extern "C" fn mul_fmpz<K: Kernel>(r: *mut c_void, x: *const c_void, c: *const sys::fmpz, ctx: GrCtx) -> c_int {
    unsafe { put::<K>(r, kernel::<K>(ctx).mul_scalar(&get::<K>(x), sys::fmpz_fdiv_ui(c, head(ctx).p as sys::ulong) as u64)) };
    SUCCESS
}

unsafe extern "C" fn inv<K: Kernel>(r: *mut c_void, x: *const c_void, ctx: GrCtx) -> c_int {
    match unsafe { kernel::<K>(ctx).inv(&get::<K>(x)) } {
        Some(v) => {
            unsafe { put::<K>(r, v) };
            SUCCESS
        }
        None => DOMAIN,
    }
}

unsafe extern "C" fn div<K: Kernel>(r: *mut c_void, x: *const c_void, y: *const c_void, ctx: GrCtx) -> c_int {
    let k = unsafe { kernel::<K>(ctx) };
    match k.inv(&unsafe { get::<K>(y) }) {
        Some(t) => {
            unsafe { put::<K>(r, k.mul(&get::<K>(x), &t)) };
            SUCCESS
        }
        None => DOMAIN,
    }
}

unsafe extern "C" fn is_invertible<K: Kernel>(x: *const c_void, ctx: GrCtx) -> sys::truth_t {
    truth(unsafe { get::<K>(x) != kernel::<K>(ctx).zero() })
}

/// x^e, or (1/x)^-e for negative e.
unsafe fn pow_words<K: Kernel>(r: *mut c_void, x: *const c_void, e: &[u64], negative: bool, ctx: GrCtx) -> c_int {
    let k = unsafe { kernel::<K>(ctx) };
    let a = unsafe { get::<K>(x) };
    let Some(b) = (if negative { k.inv(&a) } else { Some(a) }) else { return DOMAIN };
    unsafe { put::<K>(r, k.pow(&b, e)) };
    SUCCESS
}

/// Whether x is a unit, whose exponents reduce modulo q - 1.
unsafe fn is_unit<K: Kernel>(x: *const c_void, ctx: GrCtx) -> bool {
    unsafe { get::<K>(x) != kernel::<K>(ctx).zero() }
}

unsafe extern "C" fn pow_ui<K: Kernel>(r: *mut c_void, x: *const c_void, e: sys::ulong, ctx: GrCtx) -> c_int {
    let e = match unsafe { head(ctx).qm1.to_u64() } {
        Some(m) if e as u64 >= m && unsafe { is_unit::<K>(x, ctx) } => e as u64 % m,
        _ => e as u64,
    };
    unsafe { pow_words::<K>(r, x, &[e], false, ctx) }
}

unsafe extern "C" fn pow_si<K: Kernel>(r: *mut c_void, x: *const c_void, e: sys::slong, ctx: GrCtx) -> c_int {
    let a = match unsafe { head(ctx).qm1.to_u64() } {
        Some(m) if e.unsigned_abs() >= m && unsafe { is_unit::<K>(x, ctx) } => e.unsigned_abs() % m,
        _ => e.unsigned_abs(),
    };
    unsafe { pow_words::<K>(r, x, &[a], e < 0, ctx) }
}

unsafe extern "C" fn pow_fmpz<K: Kernel>(r: *mut c_void, x: *const c_void, e: *const sys::fmpz, ctx: GrCtx) -> c_int {
    unsafe {
        let mut t: sys::fmpz = 0;
        sys::fmpz_init(&mut t);
        sys::fmpz_abs(&mut t, e);
        let qm1 = head(ctx).qm1.raw_ptr();
        if sys::fmpz_cmp(&t, qm1) >= 0 && is_unit::<K>(x, ctx) {
            sys::fmpz_fdiv_r(&mut t, &t, qm1);
        }
        let len = sys::fmpz_size(&t);
        let mut w = vec![0 as sys::ulong; len.max(1) as usize];
        if len > 0 {
            sys::fmpz_get_ui_array(w.as_mut_ptr(), len, &t);
        }
        sys::fmpz_clear(&mut t);
        let w: Vec<u64> = w.into_iter().map(|x| x as u64).collect();
        pow_words::<K>(r, x, &w, sys::fmpz_sgn(e) < 0, ctx)
    }
}

unsafe extern "C" fn fq_prime(p: *mut sys::fmpz, ctx: GrCtx) -> c_int {
    unsafe { sys::fmpz_set_ui(p, head(ctx).p as sys::ulong) };
    SUCCESS
}

unsafe extern "C" fn fq_degree(d: *mut sys::slong, ctx: GrCtx) -> c_int {
    unsafe { *d = head(ctx).n as sys::slong };
    SUCCESS
}

unsafe extern "C" fn fq_order(q: *mut sys::fmpz, ctx: GrCtx) -> c_int {
    let h = unsafe { head(ctx) };
    unsafe { sys::fmpz_ui_pow_ui(q, h.p as sys::ulong, h.n as sys::ulong) };
    SUCCESS
}

/// x^(p^e), with e taken modulo n.
unsafe extern "C" fn frobenius<K: Kernel>(r: *mut c_void, x: *const c_void, e: sys::slong, ctx: GrCtx) -> c_int {
    let k = (e as i64).rem_euclid(unsafe { head(ctx).n } as i64) as u64;
    unsafe { put::<K>(r, kernel::<K>(ctx).frobenius(&get::<K>(x), k)) };
    SUCCESS
}

/// x^(p^(n - 1)), whose p-th power is x.
unsafe extern "C" fn pth_root<K: Kernel>(r: *mut c_void, x: *const c_void, ctx: GrCtx) -> c_int {
    unsafe { put::<K>(r, kernel::<K>(ctx).frobenius(&get::<K>(x), head(ctx).n - 1)) };
    SUCCESS
}

unsafe extern "C" fn norm<K: Kernel>(res: *mut sys::fmpz, x: *const c_void, ctx: GrCtx) -> c_int {
    unsafe { sys::fmpz_set_ui(res, kernel::<K>(ctx).norm(&get::<K>(x)) as sys::ulong) };
    SUCCESS
}

unsafe extern "C" fn trace<K: Kernel>(res: *mut sys::fmpz, x: *const c_void, ctx: GrCtx) -> c_int {
    unsafe { sys::fmpz_set_ui(res, kernel::<K>(ctx).trace(&get::<K>(x)) as sys::ulong) };
    SUCCESS
}

// Through the companion.

unsafe extern "C" fn multiplicative_order(res: *mut sys::fmpz, x: *const c_void, ctx: GrCtx) -> c_int {
    let h = unsafe { head(ctx) };
    let e = unsafe { h.to_companion(x) };
    unsafe { sys::gr_fq_multiplicative_order(res, e.as_ptr(), h.companion.ptr()) }
}

unsafe extern "C" fn is_primitive(x: *const c_void, ctx: GrCtx) -> sys::truth_t {
    let h = unsafe { head(ctx) };
    let e = unsafe { h.to_companion(x) };
    unsafe { sys::gr_fq_is_primitive(e.as_ptr(), h.companion.ptr()) }
}

unsafe extern "C" fn is_square(x: *const c_void, ctx: GrCtx) -> sys::truth_t {
    let h = unsafe { head(ctx) };
    let e = unsafe { h.to_companion(x) };
    unsafe { sys::gr_is_square(e.as_ptr(), h.companion.ptr()) }
}

unsafe extern "C" fn sqrt(r: *mut c_void, x: *const c_void, ctx: GrCtx) -> c_int {
    let h = unsafe { head(ctx) };
    let e = unsafe { h.to_companion(x) };
    let mut s = Elem::zero(&h.companion);
    let st = unsafe { sys::gr_sqrt(s.as_mut_ptr(), e.as_ptr(), h.companion.ptr()) };
    if st == SUCCESS {
        unsafe { h.from_fq_nmod(s.as_ptr(), r) };
    }
    st
}

/// The first `len` coefficients of the product of the polynomials a and b
/// of lengths la and lb, by Kronecker substitution: the coordinates of
/// their coefficients 2n - 1 apart in polynomials over F_p, whose product
/// FLINT finds (by FFT when they are long), then each block of 2n - 1
/// coefficients of it reduced modulo the modulus. Short products take
/// FLINT's generic algorithm, product by product of coefficients.
unsafe extern "C" fn poly_mullow<K: Kernel>(
    res: *mut c_void,
    a: *const c_void,
    la: sys::slong,
    b: *const c_void,
    lb: sys::slong,
    len: sys::slong,
    ctx: GrCtx,
) -> c_int {
    let pk = unsafe { packed::<K>(ctx) };
    if (la.min(lb) as usize) < pk.k.ks_cutoff() || len < 1 {
        return unsafe { sys::_gr_poly_mullow_generic(res, a, la, b, lb, len, ctx) };
    }
    let (n, s) = (pk.head.n as usize, 2 * pk.head.n as usize - 1);
    let spread = |x: *const c_void, l: usize| {
        let mut v = vec![0u64; (l - 1) * s + n];
        for i in 0..l {
            let e = unsafe { get::<K>((x as *const K::E).add(i).cast()) };
            pk.k.coords_into(&e, &mut v[i * s..i * s + n]);
        }
        v
    };
    let (x, y) = (spread(a, la as usize), if a == b && la == lb { Vec::new() } else { spread(b, lb as usize) });
    // FLINT squares when both factors are one, and wants the longer first.
    let (x, y) = match y.is_empty() {
        true => (&x, &x),
        false if x.len() < y.len() => (&y, &x),
        false => (&x, &y),
    };
    let mut md = sys::nmod_t::default();
    let mut c = vec![0u64; len as usize * s];
    unsafe {
        sys::nmod_init(&mut md, pk.head.p as sys::ulong);
        sys::_nmod_poly_mullow(c.as_mut_ptr(), x.as_ptr(), x.len() as sys::slong, y.as_ptr(), y.len() as sys::slong, c.len() as sys::slong, md);
    }
    for (k, block) in c.chunks_exact(s).enumerate() {
        unsafe { put::<K>((res as *mut K::E).add(k).cast(), pk.k.reduce_coeffs(block)) };
    }
    SUCCESS
}

unsafe extern "C" fn poly_roots(
    roots: *mut sys::gr_vec_struct,
    mult: *mut sys::gr_vec_struct,
    poly: *const sys::gr_poly_struct,
    flags: c_int,
    ctx: GrCtx,
) -> c_int {
    unsafe {
        let h = head(ctx);
        let (c, size) = (h.companion.ptr(), (*ctx).sizeof_elem as usize);
        let mut f = Elem::zero(&Ctx::poly(&h.companion));
        for i in (0..(*poly).length).rev() {
            let e = h.to_companion((*poly).coeffs.cast::<u8>().add(i as usize * size).cast());
            let st = sys::gr_poly_set_coeff_scalar(f.as_mut_ptr().cast(), i, e.as_ptr(), c);
            if st != SUCCESS {
                return st;
            }
        }
        let mut cr = sys::gr_vec_struct::default();
        sys::gr_vec_init(&mut cr, 0, c);
        let st = sys::gr_poly_roots(&mut cr, mult.cast(), f.as_ptr().cast(), flags, c);
        if st == SUCCESS {
            sys::gr_vec_set_length(roots, cr.length, ctx);
            for i in 0..cr.length {
                h.from_fq_nmod(sys::gr_vec_entry_ptr(&mut cr, i, c), sys::gr_vec_entry_ptr(roots, i, ctx));
            }
        }
        sys::gr_vec_clear(&mut cr, c);
        st
    }
}

/// The method table of a packed field with kernel K; gr fills in the rest
/// with its generic methods.
fn methods<K: Kernel>() -> Vec<sys::gr_method_tab_input> {
    let m = |index: sys::gr_method, f: *const ()| sys::gr_method_tab_input {
        index,
        function: Some(unsafe { std::mem::transmute::<*const (), unsafe extern "C" fn() -> c_int>(f) }),
    };
    let yes = sys::gr_generic_ctx_predicate_true as *const ();
    let no = sys::gr_generic_ctx_predicate_false as *const ();
    vec![
        m(sys::gr_method_GR_METHOD_CTX_CLEAR, ctx_clear::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_CTX_WRITE, ctx_write as *const ()),
        m(sys::gr_method_GR_METHOD_CTX_IS_RING, yes),
        m(sys::gr_method_GR_METHOD_CTX_IS_COMMUTATIVE_RING, yes),
        m(sys::gr_method_GR_METHOD_CTX_IS_INTEGRAL_DOMAIN, yes),
        m(sys::gr_method_GR_METHOD_CTX_IS_FIELD, yes),
        m(sys::gr_method_GR_METHOD_CTX_IS_UNIQUE_FACTORIZATION_DOMAIN, yes),
        m(sys::gr_method_GR_METHOD_CTX_IS_FINITE, yes),
        m(sys::gr_method_GR_METHOD_CTX_IS_FINITE_CHARACTERISTIC, yes),
        m(sys::gr_method_GR_METHOD_CTX_IS_EXACT, yes),
        m(sys::gr_method_GR_METHOD_CTX_IS_CANONICAL, yes),
        m(sys::gr_method_GR_METHOD_CTX_IS_ALGEBRAICALLY_CLOSED, no),
        m(sys::gr_method_GR_METHOD_CTX_IS_ORDERED_RING, no),
        // The companion is reference-counted without atomics.
        m(sys::gr_method_GR_METHOD_CTX_IS_THREADSAFE, no),
        m(sys::gr_method_GR_METHOD_CTX_NGENS, sys::gr_generic_ctx_ngens_1 as *const ()),
        m(sys::gr_method_GR_METHOD_INIT, init::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_CLEAR, clear as *const ()),
        m(sys::gr_method_GR_METHOD_SWAP, swap::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_SET_SHALLOW, set_shallow::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_RANDTEST, randtest::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_WRITE, write as *const ()),
        m(sys::gr_method_GR_METHOD_ZERO, zero::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_ONE, one::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_NEG_ONE, neg_one::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_GEN, generator::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_GENS, sys::gr_generic_gens_single as *const ()),
        m(sys::gr_method_GR_METHOD_IS_ZERO, is_zero::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_IS_ONE, is_one::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_IS_NEG_ONE, is_neg_one::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_EQUAL, equal::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_SET, set::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_SET_SI, set_si::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_SET_UI, set_ui::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_SET_FMPZ, set_fmpz::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_SET_OTHER, set_other::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_NEG, neg::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_ADD, add::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_SUB, sub::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_MUL, mul::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_MUL_UI, mul_ui::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_MUL_SI, mul_si::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_MUL_FMPZ, mul_fmpz::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_SQR, sqr::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_IS_INVERTIBLE, is_invertible::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_INV, inv::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_DIV, div::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_POW_UI, pow_ui::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_POW_SI, pow_si::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_POW_FMPZ, pow_fmpz::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_IS_SQUARE, is_square as *const ()),
        m(sys::gr_method_GR_METHOD_SQRT, sqrt as *const ()),
        m(sys::gr_method_GR_METHOD_CTX_FQ_PRIME, fq_prime as *const ()),
        m(sys::gr_method_GR_METHOD_CTX_FQ_DEGREE, fq_degree as *const ()),
        m(sys::gr_method_GR_METHOD_CTX_FQ_ORDER, fq_order as *const ()),
        m(sys::gr_method_GR_METHOD_FQ_FROBENIUS, frobenius::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_FQ_MULTIPLICATIVE_ORDER, multiplicative_order as *const ()),
        m(sys::gr_method_GR_METHOD_FQ_NORM, norm::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_FQ_TRACE, trace::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_FQ_IS_PRIMITIVE, is_primitive as *const ()),
        m(sys::gr_method_GR_METHOD_FQ_PTH_ROOT, pth_root::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_POLY_MULLOW, poly_mullow::<K> as *const ()),
        m(sys::gr_method_GR_METHOD_POLY_ROOTS, poly_roots as *const ()),
        sys::gr_method_tab_input { index: 0, function: None },
    ]
}

/// Make `c` the packed field of `head` with kernel `k`.
unsafe fn init_ctx<K: Kernel>(c: GrCtx, head: Head, k: K) {
    let pk = Box::into_raw(Box::new(Packed { head, k }));
    unsafe {
        let mut tab = methods::<K>();
        sys::gr_method_tab_init((*pk).head.methods.as_mut_ptr(), tab.as_mut_ptr());
        std::ptr::write_unaligned((*c).data.as_mut_ptr() as *mut *mut Packed<K>, pk);
        (*c).which_ring = sys::gr_which_structure_GR_CTX_UNKNOWN_DOMAIN as sys::ulong;
        (*c).sizeof_elem = std::mem::size_of::<K::E>() as sys::slong;
        (*c).size_limit = i64::MAX as sys::ulong;
        (*c).methods = (*pk).head.methods.as_mut_ptr();
    }
}

fn build<K: Kernel>(p: u64, n: usize, companion: Rc<Ctx>, k: K) -> GrResult<Rc<Ctx>> {
    Ctx::try_build(CtxKind::FqPacked { p, degree: n as u64 }, None, move |c| {
        let qm1 = &Integer::from_u64(p).pow(n as u64) - &Integer::one();
        let head = Head { p, n: n as u64, qm1, companion, methods: Box::new([None; TAB_SIZE]), coords: coords_of::<K>, from_coords: from_coords_of::<K> };
        unsafe { init_ctx(c, head, k) };
        SUCCESS
    })
}

fn head_of(ctx: &Ctx) -> Option<&Head> {
    matches!(ctx.kind(), CtxKind::FqPacked { .. }).then(|| unsafe { head(ctx.ptr()) })
}

impl Ctx {
    /// GF(p^n) = F_p[x]/(f) with its elements packed into words, for a prime
    /// p and f monic and irreducible of degree n, given by its coefficients
    /// below p (constant term first). `Unable` when no packed representation
    /// covers the field: p must be 2 with n at most 512, or odd and below 2^8
    /// with n at most 64, or below 2^16 with n at most 32.
    pub fn packed_field(p: u64, modulus: &[u64]) -> GrResult<Rc<Ctx>> {
        let n = modulus.len().saturating_sub(1);
        let most = match p {
            2 => 512,
            3..256 => 64,
            256..65536 => 32,
            _ => 0,
        };
        if !(1..=most).contains(&n) || modulus[n] % p != 1 || !Integer::from_u64(p).is_prime() {
            return Err(GrError::Unable);
        }
        let ints: Vec<Integer> = modulus.iter().map(|&c| Integer::from_u64(c % p)).collect();
        let companion = Ctx::flint_field(&Integer::from_u64(p), &ints, false)?;
        if p != 2 {
            let f = &modulus[..n];
            return match (p < 256, n) {
                (true, 1..=16) => build(p, n, companion, FpLanes::<u8, 16>::new(p, f)),
                (true, 17..=32) => build(p, n, companion, FpLanes::<u8, 32>::new(p, f)),
                (true, _) => build(p, n, companion, FpLanes::<u8, 64>::new(p, f)),
                (false, 1..=8) => build(p, n, companion, FpLanes::<u16, 8>::new(p, f)),
                (false, 9..=16) => build(p, n, companion, FpLanes::<u16, 16>::new(p, f)),
                (false, _) => build(p, n, companion, FpLanes::<u16, 32>::new(p, f)),
            };
        }
        let mut g = [0u64; 8];
        for (i, &c) in modulus[..n].iter().enumerate() {
            g[i / 64] |= (c & 1) << (i % 64);
        }
        let (d, g) = (n as u32, &g[..n.div_ceil(64)]);
        match g.len() {
            1 => build(p, n, companion, Gf2Words::<1>::new(d, g)),
            2 => build(p, n, companion, Gf2Words::<2>::new(d, g)),
            3 => build(p, n, companion, Gf2Words::<3>::new(d, g)),
            4 => build(p, n, companion, Gf2Words::<4>::new(d, g)),
            5 => build(p, n, companion, Gf2Words::<5>::new(d, g)),
            6 => build(p, n, companion, Gf2Words::<6>::new(d, g)),
            7 => build(p, n, companion, Gf2Words::<7>::new(d, g)),
            _ => build(p, n, companion, Gf2Words::<8>::new(d, g)),
        }
    }

    /// For a packed field, the same field over FLINT's fq_nmod (with the
    /// same modulus), for what FLINT does only on its own types.
    pub fn fq_companion(&self) -> Option<&Rc<Ctx>> {
        head_of(self).map(|h| &h.companion)
    }
}

/// The coordinates of an element of a packed field.
pub(crate) fn coords(x: &Elem) -> Vec<u64> {
    let h = head_of(x.ctx()).expect("a packed field");
    unsafe { (h.coords)(h, x.as_ptr()) }
}

/// The element of a packed field with the given coordinates (below p).
pub(crate) fn from_coords(ctx: &Rc<Ctx>, c: &[u64]) -> Elem {
    let h = head_of(ctx).expect("a packed field");
    let mut e = Elem::zero(ctx);
    unsafe { (h.from_coords)(h, c, e.as_mut_ptr()) };
    e
}

// ----- polynomials, through the companion ---------------------------------

type P = *mut c_void;
type C = *const c_void;

// FLINT's factorizations over fq_nmod, which flint3-sys does not declare
// (declared as upoly declares them).
unsafe extern "C" {
    fn fq_nmod_poly_factor_init(f: P, ctx: C);
    fn fq_nmod_poly_factor_clear(f: P, ctx: C);
    fn fq_nmod_poly_factor(f: P, lc: P, a: C, ctx: C);
    fn fq_nmod_poly_factor_squarefree(f: P, a: C, ctx: C);
    fn fq_nmod_poly_factor_distinct_deg(f: P, a: C, degs: *const *mut sys::slong, ctx: C);
    fn fq_nmod_poly_factor_equal_deg(f: P, a: C, d: sys::slong, ctx: C);
    fn fq_nmod_poly_roots(f: P, a: C, mult: c_int, ctx: C);
    fn fq_nmod_poly_is_irreducible(a: C, ctx: C) -> c_int;
}

impl Head {
    /// The companion's fq_nmod context.
    fn nctx(&self) -> *const sys::fq_nmod_ctx_struct {
        unsafe { std::ptr::read_unaligned((*self.companion.ptr()).data.as_ptr() as *const *const sys::fq_nmod_ctx_struct) }
    }

    /// Set the fq_nmod element t (of the companion) to the element at x.
    unsafe fn to_fq_nmod(&self, x: *const c_void, t: *mut sys::nmod_poly_struct) {
        let c = unsafe { (self.coords)(self, x) };
        let len = c.iter().rposition(|&v| v != 0).map_or(0, |i| i + 1);
        unsafe {
            sys::nmod_poly_fit_length(t, len as sys::slong);
            for (i, &v) in c[..len].iter().enumerate() {
                *(*t).coeffs.add(i) = v as sys::ulong;
            }
            (*t).length = len as sys::slong;
        }
    }
}

/// An fq_nmod_poly over the companion of a packed field, cleared when
/// dropped.
struct FPoly {
    p: sys::fq_nmod_poly_struct,
    nctx: *const sys::fq_nmod_ctx_struct,
}

impl FPoly {
    fn new(h: &Head) -> FPoly {
        let mut p = sys::fq_nmod_poly_struct::default();
        unsafe { sys::fq_nmod_poly_init(&mut p, h.nctx()) };
        FPoly { p, nctx: h.nctx() }
    }

    /// The gr_poly at a over the packed field ctx.
    unsafe fn of(h: &Head, a: *const c_void, ctx: GrCtx) -> FPoly {
        let mut f = FPoly::new(h);
        unsafe {
            let a = &*(a as *const sys::gr_poly_struct);
            let size = (*ctx).sizeof_elem as usize;
            sys::fq_nmod_poly_fit_length(&mut f.p, a.length, f.nctx);
            for i in 0..a.length as usize {
                h.to_fq_nmod(a.coeffs.cast::<u8>().add(i * size).cast(), f.p.coeffs.add(i));
            }
            f.p.length = a.length;
        }
        f
    }
}

impl FPoly {
    fn raw(&self) -> C {
        (&self.p as *const sys::fq_nmod_poly_struct).cast()
    }
}

impl Drop for FPoly {
    fn drop(&mut self) {
        unsafe { sys::fq_nmod_poly_clear(&mut self.p, self.nctx) };
    }
}

/// Set the gr_poly at r over the packed field ctx to the fq_nmod_poly p.
unsafe fn put_poly(h: &Head, p: &sys::fq_nmod_poly_struct, r: *mut c_void, ctx: GrCtx) {
    unsafe {
        let r = r as *mut sys::gr_poly_struct;
        let size = (*ctx).sizeof_elem as usize;
        sys::gr_poly_fit_length(r, p.length, ctx);
        for i in 0..p.length as usize {
            h.from_fq_nmod(p.coeffs.add(i).cast(), (*r).coeffs.cast::<u8>().add(i * size).cast());
        }
        sys::_gr_poly_set_length(r, p.length, ctx);
    }
}

/// A factorization over a packed field, laid out as FLINT's (and upoly's
/// `RawFac`) but with gr_polys over the packed field.
#[repr(C)]
struct PFac {
    poly: *mut sys::gr_poly_struct,
    exp: *mut sys::slong,
    num: sys::slong,
    alloc: sys::slong,
}

/// A factorization over the companion, cleared when dropped.
struct FFac {
    f: sys::fq_nmod_poly_factor_struct,
    nctx: *const sys::fq_nmod_ctx_struct,
}

impl FFac {
    fn new(h: &Head) -> FFac {
        let mut f = sys::fq_nmod_poly_factor_struct::default();
        unsafe { fq_nmod_poly_factor_init((&mut f as *mut sys::fq_nmod_poly_factor_struct).cast(), h.nctx().cast()) };
        FFac { f, nctx: h.nctx() }
    }

    fn raw(&mut self) -> P {
        (&mut self.f as *mut sys::fq_nmod_poly_factor_struct).cast()
    }

    /// Append the factors to the factorization at f over the packed field
    /// ctx.
    unsafe fn push_to(&self, h: &Head, f: *mut c_void, ctx: GrCtx) {
        unsafe {
            let f = &mut *(f as *mut PFac);
            for i in 0..self.f.num as usize {
                if f.num == f.alloc {
                    f.alloc = (2 * f.alloc).max(4);
                    f.poly = sys::flint_realloc(f.poly.cast(), f.alloc as usize * std::mem::size_of::<sys::gr_poly_struct>()).cast();
                    f.exp = sys::flint_realloc(f.exp.cast(), f.alloc as usize * std::mem::size_of::<sys::slong>()).cast();
                }
                let p = f.poly.add(f.num as usize);
                sys::gr_poly_init(p, ctx);
                put_poly(h, &*self.f.poly.add(i), p.cast(), ctx);
                *f.exp.add(f.num as usize) = *self.f.exp.add(i);
                f.num += 1;
            }
        }
    }
}

impl Drop for FFac {
    fn drop(&mut self) {
        unsafe { fq_nmod_poly_factor_clear(self.raw(), self.nctx.cast()) };
    }
}

/// The head and gr context of a packed field passed as upoly's context.
unsafe fn parts<'a>(ctx: C) -> (&'a Head, GrCtx) {
    (unsafe { head(ctx as GrCtx) }, ctx as GrCtx)
}

// The polynomial functions of upoly's `FqFns` for packed fields: FLINT's
// fq_nmod ones on copies over the companion, so that results are those of
// an fq_nmod field.

pub(crate) unsafe extern "C" fn poly_gcd(r: P, a: C, b: C, ctx: C) {
    unsafe {
        let (h, g) = parts(ctx);
        let (x, y, mut t) = (FPoly::of(h, a, g), FPoly::of(h, b, g), FPoly::new(h));
        sys::fq_nmod_poly_gcd(&mut t.p, &x.p, &y.p, t.nctx);
        put_poly(h, &t.p, r, g);
    }
}

pub(crate) unsafe extern "C" fn poly_xgcd(d: P, s: P, t: P, a: C, b: C, ctx: C) {
    unsafe {
        let (h, g) = parts(ctx);
        let (x, y) = (FPoly::of(h, a, g), FPoly::of(h, b, g));
        let (mut u, mut v, mut w) = (FPoly::new(h), FPoly::new(h), FPoly::new(h));
        sys::fq_nmod_poly_xgcd(&mut u.p, &mut v.p, &mut w.p, &x.p, &y.p, u.nctx);
        put_poly(h, &u.p, d, g);
        put_poly(h, &v.p, s, g);
        put_poly(h, &w.p, t, g);
    }
}

pub(crate) unsafe extern "C" fn poly_divrem(q: P, r: P, a: C, b: C, ctx: C) {
    unsafe {
        let (h, g) = parts(ctx);
        let (x, y) = (FPoly::of(h, a, g), FPoly::of(h, b, g));
        let (mut u, mut v) = (FPoly::new(h), FPoly::new(h));
        sys::fq_nmod_poly_divrem(&mut u.p, &mut v.p, &x.p, &y.p, u.nctx);
        put_poly(h, &u.p, q, g);
        put_poly(h, &v.p, r, g);
    }
}

pub(crate) unsafe extern "C" fn poly_powmod(r: P, a: C, e: *const sys::fmpz, f: C, ctx: C) {
    unsafe {
        let (h, g) = parts(ctx);
        let (x, m, mut t) = (FPoly::of(h, a, g), FPoly::of(h, f, g), FPoly::new(h));
        sys::fq_nmod_poly_powmod_fmpz_binexp(&mut t.p, &x.p, e, &m.p, t.nctx);
        put_poly(h, &t.p, r, g);
    }
}

pub(crate) unsafe extern "C" fn fac_init(f: P, _ctx: C) {
    unsafe { *(f as *mut PFac) = PFac { poly: std::ptr::null_mut(), exp: std::ptr::null_mut(), num: 0, alloc: 0 } };
}

pub(crate) unsafe extern "C" fn fac_clear(f: P, ctx: C) {
    unsafe {
        let f = &mut *(f as *mut PFac);
        for i in 0..f.num as usize {
            sys::gr_poly_clear(f.poly.add(i), ctx as GrCtx);
        }
        sys::flint_free(f.poly.cast());
        sys::flint_free(f.exp.cast());
    }
}

pub(crate) unsafe extern "C" fn poly_factor(f: P, lc: P, a: C, ctx: C) {
    unsafe {
        let (h, g) = parts(ctx);
        let (x, mut t) = (FPoly::of(h, a, g), FFac::new(h));
        let mut c = sys::nmod_poly_struct::default();
        sys::fq_nmod_init(&mut c, t.nctx);
        fq_nmod_poly_factor(t.raw(), (&mut c as *mut sys::nmod_poly_struct).cast(), x.raw(), t.nctx.cast());
        h.from_fq_nmod((&c as *const sys::nmod_poly_struct).cast(), lc);
        sys::fq_nmod_clear(&mut c, t.nctx);
        t.push_to(h, f, g);
    }
}

pub(crate) unsafe extern "C" fn poly_factor_squarefree(f: P, a: C, ctx: C) {
    unsafe {
        let (h, g) = parts(ctx);
        let (x, mut t) = (FPoly::of(h, a, g), FFac::new(h));
        fq_nmod_poly_factor_squarefree(t.raw(), x.raw(), t.nctx.cast());
        t.push_to(h, f, g);
    }
}

pub(crate) unsafe extern "C" fn poly_factor_distinct_deg(f: P, a: C, degs: *const *mut sys::slong, ctx: C) {
    unsafe {
        let (h, g) = parts(ctx);
        let (x, mut t) = (FPoly::of(h, a, g), FFac::new(h));
        fq_nmod_poly_factor_distinct_deg(t.raw(), x.raw(), degs, t.nctx.cast());
        t.push_to(h, f, g);
    }
}

pub(crate) unsafe extern "C" fn poly_factor_equal_deg(f: P, a: C, d: sys::slong, ctx: C) {
    unsafe {
        let (h, g) = parts(ctx);
        let (x, mut t) = (FPoly::of(h, a, g), FFac::new(h));
        fq_nmod_poly_factor_equal_deg(t.raw(), x.raw(), d, t.nctx.cast());
        t.push_to(h, f, g);
    }
}

pub(crate) unsafe extern "C" fn poly_roots_factored(f: P, a: C, mult: c_int, ctx: C) {
    unsafe {
        let (h, g) = parts(ctx);
        let (x, mut t) = (FPoly::of(h, a, g), FFac::new(h));
        fq_nmod_poly_roots(t.raw(), x.raw(), mult, t.nctx.cast());
        t.push_to(h, f, g);
    }
}

pub(crate) unsafe extern "C" fn poly_is_irreducible(a: C, ctx: C) -> c_int {
    unsafe {
        let (h, g) = parts(ctx);
        fq_nmod_poly_is_irreducible(FPoly::of(h, a, g).raw(), h.nctx().cast())
    }
}

// Coefficients of multivariate polynomials (mpoly), as fq_nmod_mpoly keeps
// them: d words, the coordinates.

/// Write the coordinates of the element at x of the packed field ctx at
/// out.
pub(crate) unsafe fn get_n_fq(out: *mut sys::ulong, x: *const c_void, ctx: GrCtx) {
    unsafe {
        let h = head(ctx);
        for (i, v) in (h.coords)(h, x).into_iter().enumerate() {
            *out.add(i) = v as sys::ulong;
        }
    }
}

/// Write at r the element of the packed field ctx with the coordinates at
/// a.
pub(crate) unsafe fn set_n_fq(r: *mut c_void, a: *const sys::ulong, ctx: GrCtx) {
    unsafe {
        let h = head(ctx);
        let c: Vec<u64> = (0..h.n as usize).map(|i| *a.add(i) as u64).collect();
        (h.from_coords)(h, &c, r);
    }
}

/// Write at r the element of the packed field ctx with the coordinates of
/// the fq_nmod element at a.
pub(crate) unsafe fn set_fq_nmod(r: *mut c_void, a: *const c_void, ctx: GrCtx) {
    unsafe { head(ctx).from_fq_nmod(a, r) }
}

/// The companion's fq_nmod context of a packed field.
pub(crate) fn fq_nmod_ctx(ctx: &Ctx) -> *const sys::fq_nmod_ctx_struct {
    head_of(ctx).expect("a packed field").nctx()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gr::{Truth, conway_polynomial, is_irreducible_mod_p};

    struct Lcg(u64);

    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            self.0 ^ self.0 >> 29
        }
    }

    fn same(a: &Elem, b: &Elem) {
        assert_eq!(a.fq_coords_u64(), b.fq_coords_u64());
    }

    /// The packed field with modulus `cs` against FLINT's fq_nmod field.
    fn agree(p: u64, cs: &[u64], rng: &mut Lcg) {
        let n = cs.len() - 1;
        let ints: Vec<Integer> = cs.iter().map(|&c| Integer::from_u64(c)).collect();
        let pk = Ctx::packed_field(p, cs).unwrap();
        let fq = Ctx::flint_field(&Integer::from_u64(p), &ints, false).unwrap();
        let size = match p {
            2 => 8 * n.div_ceil(64),
            3..256 => [16, 32, 64].into_iter().find(|&m| n <= m).unwrap(),
            _ => 2 * [8, 16, 32].into_iter().find(|&m| n <= m).unwrap(),
        };
        assert!(matches!(pk.kind(), CtxKind::FqPacked { .. }) && pk.elem_size() == size);
        let rand = |rng: &mut Lcg| -> Vec<u64> { (0..n).map(|_| rng.next() % p).collect() };
        let q = Integer::from_u64(p).pow(n as u64);
        for i in 0..30 {
            let (ca, cb) = (rand(rng), if i == 0 { vec![0; n] } else { rand(rng) });
            let (a, fa) = (Elem::fq_from_coords_u64(&pk, &ca), Elem::fq_from_coords_u64(&fq, &ca));
            let (b, fb) = (Elem::fq_from_coords_u64(&pk, &cb), Elem::fq_from_coords_u64(&fq, &cb));
            assert_eq!(a.fq_coords_u64(), ca);
            same(&a.add(&b).unwrap(), &fa.add(&fb).unwrap());
            same(&a.sub(&b).unwrap(), &fa.sub(&fb).unwrap());
            same(&a.mul(&b).unwrap(), &fa.mul(&fb).unwrap());
            same(&a.neg().unwrap(), &fa.neg().unwrap());
            same(&a.sqr().unwrap(), &fa.sqr().unwrap());
            assert_eq!(b.div(&a).map(|x| x.fq_coords_u64()), fb.div(&fa).map(|x| x.fq_coords_u64()));
            assert_eq!(a.div(&b).map(|x| x.fq_coords_u64()), fa.div(&fb).map(|x| x.fq_coords_u64()));
            assert_eq!(b.inv().map(|x| x.fq_coords_u64()), fb.inv().map(|x| x.fq_coords_u64()));
            let e = rng.next() as i64 >> (rng.next() % 64);
            assert_eq!(a.pow_i64(e).map(|x| x.fq_coords_u64()), fa.pow_i64(e).map(|x| x.fq_coords_u64()), "{e}");
            assert_eq!(a.pow_i64(-e).map(|x| x.fq_coords_u64()), fa.pow_i64(-e).map(|x| x.fq_coords_u64()));
            let big = Integer::from_limbs(&[rng.next(), rng.next(), rng.next()], i % 2 == 1);
            assert_eq!(a.pow(&big).map(|x| x.fq_coords_u64()), fa.pow(&big).map(|x| x.fq_coords_u64()));
            same(&a.pow(&q).unwrap(), &a);
            for k in [-1i64, 0, 1, 3, n as i64 + 2] {
                same(&a.fq_frobenius(k).unwrap(), &fa.fq_frobenius(k).unwrap());
            }
            assert_eq!(a.fq_norm().unwrap(), fa.fq_norm().unwrap());
            assert_eq!(a.fq_trace().unwrap(), fa.fq_trace().unwrap());
            assert_eq!(a.equal(&b), fa.equal(&fb));
            assert_eq!(a.equal(&a.clone()), Truth::True);
            assert_eq!((a.is_zero(), b.is_zero(), a.is_one()), (fa.is_zero(), fb.is_zero(), fa.is_one()));
            assert_eq!(a.mul_integer(&Integer::from_i64(-3)).unwrap().fq_coords_u64(), fa.mul_integer(&Integer::from_i64(-3)).unwrap().fq_coords_u64());
            assert_eq!(a.to_flint_string(), fa.to_flint_string());
            assert_eq!(a.is_square(), fa.is_square());
            match a.sqrt() {
                Ok(s) => same(&s.sqr().unwrap(), &a),
                Err(e) => assert_eq!(fa.sqrt().err(), Some(e)),
            }
        }
        same(&pk.generator().unwrap(), &fq.generator().unwrap());
        for v in [-1i64, 0, 1, 2, 5] {
            same(&Elem::from_i64(&pk, v).unwrap(), &Elem::from_i64(&fq, v).unwrap());
        }
        same(&Elem::from_integer(&pk, &q).unwrap(), &Elem::zero(&fq));
        let fp = Ctx::residue_ring(&Integer::from_u64(p));
        same(&Elem::from_other(&pk, &Elem::from_i64(&fp, 1).unwrap()).unwrap(), &Elem::one(&fq).unwrap());
        assert_eq!(pk.fq_order(), fq.fq_order());
        if q.bits() <= 64 {
            let g = pk.generator().unwrap();
            let x = Elem::fq_from_coords_u64(&pk, &rand(rng));
            for y in [&g, &x] {
                let fy = Elem::fq_from_coords_u64(&fq, &y.fq_coords_u64());
                assert_eq!(y.fq_multiplicative_order(), fy.fq_multiplicative_order());
            }
        }
        // Polynomials over the field, through gr's generic algorithms and
        // the companion: (x - c0)(x - c1)^2(x - c2) and (x - c1)(x - c2).
        let cs: Vec<Vec<u64>> = (0..3).map(|_| rand(rng)).collect();
        let poly = |ctx: &Rc<Ctx>, roots: &[usize]| {
            let px = Ctx::poly(ctx);
            let x = px.generator().unwrap();
            roots.iter().fold(Elem::one(&px).unwrap(), |f, &i| {
                let c = Elem::poly_from_coeffs(&px, &[Elem::fq_from_coords_u64(ctx, &cs[i])]).unwrap();
                f.mul(&x.sub(&c).unwrap()).unwrap()
            })
        };
        let coeffs = |f: &Elem| (0..f.poly_len()).map(|i| f.poly_coeff(i).fq_coords_u64()).collect::<Vec<_>>();
        let roots = |f: &Elem| {
            let mut r: Vec<(Vec<u64>, u64)> = f.poly_roots().unwrap().iter().map(|(x, m)| (x.fq_coords_u64(), *m)).collect();
            r.sort();
            r
        };
        let (f, ff) = (poly(&pk, &[0, 1, 1, 2]), poly(&fq, &[0, 1, 1, 2]));
        assert_eq!(coeffs(&f), coeffs(&ff));
        assert_eq!(roots(&f), roots(&ff));
        let (g, fg) = (poly(&pk, &[1, 2]), poly(&fq, &[1, 2]));
        assert_eq!(coeffs(&f.poly_gcd(&g).unwrap()), coeffs(&ff.poly_gcd(&fg).unwrap()));
    }

    /// x^n + g irreducible over GF(2) with many terms below x^n.
    fn dense(n: usize, rng: &mut Lcg) -> Vec<u64> {
        for _ in 0..20 * n {
            let mut cs: Vec<u64> = (0..n).map(|_| rng.next() & 1).collect();
            (cs[0], cs[n - 1]) = (1, 1);
            cs.push(1);
            let ints: Vec<Integer> = cs.iter().map(|&c| Integer::from_u64(c)).collect();
            if is_irreducible_mod_p(&Integer::from_u64(2), &ints) {
                return cs;
            }
        }
        panic!("no irreducible of degree {n}");
    }

    #[test]
    fn packed_fields_agree_with_fq_nmod() {
        let mut rng = Lcg(0x9e37_79b9_7f4a_7c15);
        for n in [2u64, 3, 20, 63, 64, 65, 100, 127, 128, 129, 200, 256, 300, 400, 512] {
            let cs: Vec<u64> = match conway_polynomial(2, n) {
                Some(c) => c.iter().map(|x| x.to_u64().unwrap()).collect(),
                None => {
                    let g = crate::gf2x::least_low_term(n as usize).unwrap();
                    (0..=n).map(|i| if i == n { 1 } else if i < 64 { g >> i & 1 } else { 0 }).collect()
                }
            };
            agree(2, &cs, &mut rng);
        }
        for n in [100usize, 300] {
            let cs = dense(n, &mut rng);
            agree(2, &cs, &mut rng);
        }
        for (p, n) in [(3u64, 1usize), (3, 2), (3, 13), (3, 40), (3, 64), (5, 9), (7, 30), (251, 3), (251, 64), (257, 2), (1009, 9), (32003, 16), (65521, 32)] {
            let cs = odd_modulus(p, n, &mut rng);
            agree(p, &cs, &mut rng);
        }
        for (p, cs) in [(2, vec![1; 514]), (3, vec![1; 66]), (257, vec![1; 34]), (65537, vec![1, 0, 1]), (9, vec![1, 0, 1]), (3, vec![1, 0, 2])] {
            assert_eq!(Ctx::packed_field(p, &cs).err(), Some(GrError::Unable));
        }
    }

    /// Products of polynomials by Kronecker substitution against FLINT's
    /// generic ones, coefficient by coefficient, truncated or not, and for
    /// squares.
    #[test]
    fn polynomial_products_by_kronecker_substitution() {
        let mut rng = Lcg(0x2545_f491_4f6c_dd1d);
        for (p, n) in [(2u64, 20usize), (2, 64), (2, 100), (3, 1), (3, 12), (7, 30), (251, 10), (257, 3), (65521, 4)] {
            let cs: Vec<u64> = if p == 2 {
                let g = crate::gf2x::least_low_term(n).unwrap();
                (0..=n).map(|i| if i == n { 1 } else if i < 64 { g >> i & 1 } else { 0 }).collect()
            } else {
                odd_modulus(p, n, &mut rng)
            };
            let pk = Ctx::packed_field(p, &cs).unwrap();
            let size = pk.elem_size();
            // A vector of l random elements, as FLINT holds it.
            let mut vector = |l: usize| {
                let mut v = vec![0u8; l * size];
                for i in 0..l {
                    let e = Elem::fq_from_coords_u64(&pk, &(0..n).map(|_| rng.next() % p).collect::<Vec<_>>());
                    unsafe { std::ptr::copy_nonoverlapping(e.as_ptr() as *const u8, v[i * size..].as_mut_ptr(), size) };
                }
                v
            };
            // Lengths about the cutoff for substitution, 3n for p = 2 and 6
            // otherwise, and some longer.
            let c = if p == 2 { 3 * n } else { 6 };
            for (la, lb) in [(c - 1, c + 4), (c, c), (c + 3, 2 * c), (2 * c, c + 1), (33, 33), (100, 57)] {
                let (a, b) = (vector(la), vector(lb));
                for (y, ly) in [(&b, lb), (&a, la)] {
                    for len in [1, la.min(ly), la + ly - 2, la + ly - 1] {
                        let (mut r1, mut r2) = (vec![0u8; len * size], vec![0u8; len * size]);
                        let (ap, yp, l) = (a.as_ptr().cast(), y.as_ptr().cast(), len as sys::slong);
                        unsafe {
                            assert_eq!(sys::_gr_poly_mullow(r1.as_mut_ptr().cast(), ap, la as sys::slong, yp, ly as sys::slong, l, pk.ptr()), SUCCESS);
                            assert_eq!(sys::_gr_poly_mullow_generic(r2.as_mut_ptr().cast(), ap, la as sys::slong, yp, ly as sys::slong, l, pk.ptr()), SUCCESS);
                        }
                        assert!(r1 == r2, "GF({p}^{n}), lengths {la} and {ly}, first {len}");
                    }
                }
            }
        }
    }

    /// A monic irreducible polynomial of degree n over F_p for odd p:
    /// Conway's if known, else a random one.
    fn odd_modulus(p: u64, n: usize, rng: &mut Lcg) -> Vec<u64> {
        if let Some(c) = conway_polynomial(p, n as u64) {
            return c.iter().map(|x| x.to_u64().unwrap()).collect();
        }
        for _ in 0..100 * n {
            let cs: Vec<u64> = (0..n).map(|_| rng.next() % p).chain([1]).collect();
            let ints: Vec<Integer> = cs.iter().map(|&c| Integer::from_u64(c)).collect();
            if is_irreducible_mod_p(&Integer::from_u64(p), &ints) {
                return cs;
            }
        }
        panic!("no irreducible of degree {n} over F_{p}");
    }

    /// The coordinates of the coefficients of a univariate polynomial.
    fn coeffs(f: &Elem) -> Vec<Vec<u64>> {
        (0..f.poly_len()).map(|i| f.poly_coeff(i).fq_coords_u64()).collect()
    }

    /// The terms of a multivariate polynomial, coefficients as coordinates.
    fn terms(f: &Elem) -> Vec<(Vec<u64>, Vec<u64>)> {
        (0..f.mpoly_len()).map(|i| f.mpoly_term(i)).map(|(c, e)| (c.fq_coords_u64(), e)).collect()
    }

    /// Polynomial arithmetic over `k` with the elements `r`, as coordinates,
    /// to compare between representations of the same field.
    fn poly_summary(k: &Rc<Ctx>, r: &[Vec<u64>], e: &Integer) -> Vec<String> {
        use crate::{mpoly, upoly};
        let (el, one) = (|i: usize| Elem::fq_from_coords_u64(k, &r[i]), Elem::one(k).unwrap());
        let px = Ctx::poly(k);
        let up = |c: &[Elem]| Elem::poly_from_coeffs(&px, c).unwrap();
        let prod = |v: &[&Elem]| v.iter().fold(Elem::one(&px).unwrap(), |f, g| f.mul(g).unwrap());
        let facs = |v: &[(Elem, u64)]| v.iter().map(|(h, e)| (coeffs(h), *e)).collect::<Vec<_>>();
        let sorted = |mut v: Vec<Vec<Vec<u64>>>| {
            v.sort();
            v
        };
        // f = (x + r0)(x + r1)^2 (x^2 + r2 x + r3)(x^3 + r4 x + r5), g = (x + r1)(x^3 + r4 x + r5).
        let (l0, l1, l2) = (up(&[el(0), one.clone()]), up(&[el(1), one.clone()]), up(&[el(2), one.clone()]));
        let (q, c) = (up(&[el(3), el(2), one.clone()]), up(&[el(5), el(4), Elem::zero(k), one.clone()]));
        let (f, g) = (prod(&[&l0, &l1, &l1, &q, &c]), prod(&[&l1, &c]));
        let (d, s, t) = upoly::xgcd(&f, &g.add(&Elem::one(&px).unwrap()).unwrap()).unwrap();
        let (quo, rem) = upoly::divrem(&f, &g).unwrap();
        let a = f.mul(&up(&[k.generator().unwrap()])).unwrap();
        let (fa, sq) = (upoly::factor(&a).unwrap(), upoly::factor_squarefree(&f).unwrap());
        let roots = upoly::roots(&f).unwrap().iter().map(|(x, m)| vec![x.fq_coords_u64(), vec![*m]]).collect();
        let ddf: Vec<_> = upoly::distinct_degree(&q.mul(&c).unwrap()).unwrap().iter().map(|(d, h)| (*d, coeffs(h))).collect();
        let edf = upoly::equal_degree(&prod(&[&l0, &l1, &l2]), 1).unwrap().iter().map(coeffs).collect();
        let irr: Vec<bool> = [&f, &q, &c].iter().map(|h| upoly::is_irreducible(h).unwrap()).collect();
        let mut out = vec![
            format!("{:?} {:?}", coeffs(&f), coeffs(&upoly::gcd(&f, &g).unwrap())),
            format!("{:?} {:?} {:?} {:?} {:?}", coeffs(&d), coeffs(&s), coeffs(&t), coeffs(&quo), coeffs(&rem)),
            format!("{:?}", coeffs(&upoly::powmod(&px.generator().unwrap(), e, &f).unwrap())),
            format!("{:?} {:?} {:?}", fa.unit.fq_coords_u64(), facs(&fa.factors), facs(&sq.factors)),
            format!("{:?} {ddf:?} {:?} {irr:?}", sorted(roots), sorted(edf)),
        ];
        // u + r0 v, u v + r1 and u + v in GF(q)[u, v].
        let pm = Ctx::mpoly(k, 2, crate::gr::MonomialOrder::Lex);
        let mp = |t: &[(Elem, [u64; 2])]| Elem::mpoly_from_terms(&pm, &t.iter().map(|(c, e)| (c.clone(), e.to_vec())).collect::<Vec<_>>()).unwrap();
        let (a, b) = (mp(&[(one.clone(), [1, 0]), (el(0), [0, 1])]), mp(&[(one.clone(), [1, 1]), (el(1), [0, 0])]));
        let c = mp(&[(one.clone(), [1, 0]), (one.clone(), [0, 1])]);
        let (x, y) = (a.sqr().unwrap().mul(&b).unwrap(), a.mul(&c).unwrap());
        let (u, mf) = mpoly::factor(&x.mul(&c).unwrap(), false).unwrap();
        let mut mf: Vec<_> = mf.iter().map(|(h, e)| (terms(h), *e)).collect();
        mf.sort();
        out.push(format!("{:?} {:?} {mf:?}", terms(&mpoly::gcd(&x, &y).unwrap()), u.fq_coords_u64()));
        out.push(format!("{:?} {:?}", mpoly::divides(&x, &a).unwrap().map(|h| terms(&h)), terms(&mpoly::resultant(&x, &y, 0).unwrap())));
        out
    }

    #[test]
    fn polynomials_through_the_companion() {
        let mut rng = Lcg(0x2545_f491_4f6c_dd1d);
        for (p, n) in [(2u64, 21u64), (2, 70), (2, 200), (3, 17), (7, 30), (251, 3), (65521, 5)] {
            let cs: Vec<u64> = match (p, conway_polynomial(p, n)) {
                (_, Some(c)) => c.iter().map(|x| x.to_u64().unwrap()).collect(),
                (2, None) => {
                    let g = crate::gf2x::least_low_term(n as usize).unwrap();
                    (0..=n).map(|i| if i == n { 1 } else if i < 64 { g >> i & 1 } else { 0 }).collect()
                }
                _ => odd_modulus(p, n as usize, &mut rng),
            };
            let ints: Vec<Integer> = cs.iter().map(|&c| Integer::from_u64(c)).collect();
            let pk = Ctx::packed_field(p, &cs).unwrap();
            let fq = Ctx::flint_field(&Integer::from_u64(p), &ints, false).unwrap();
            assert!(matches!(fq.kind(), CtxKind::FqNmod { .. }));
            assert!(matches!(Ctx::finite_field(&Integer::from_u64(p), &ints, false).unwrap().kind(), CtxKind::FqPacked { .. }));
            let r: Vec<Vec<u64>> = (0..6).map(|_| (0..n).map(|_| rng.next() % p).collect()).collect();
            let e = Integer::from_i64(2).pow(n + 7);
            assert_eq!(poly_summary(&pk, &r, &e), poly_summary(&fq, &r, &e));
        }
    }
}
