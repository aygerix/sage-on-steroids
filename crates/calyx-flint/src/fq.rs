//! Finite fields: fast coordinates of elements and Zech logarithms, and
//! irreducibility and factorisation of polynomials over finite fields
//! (through `upoly`).

use std::rc::Rc;

use flint3_sys as sys;

use crate::Integer;
use crate::gr::{Ctx, CtxKind, Elem, GrResult};

impl Ctx {
    /// For GF(2^n) with n up to 64 (without Zech logarithms), its words:
    /// the field defined by the modulus.
    pub fn fq_gf2_field(&self) -> Option<crate::gf2x::Gf2Field> {
        if let CtxKind::FqPacked { p: 2, degree: 1..=64 } = *self.kind() {
            return self.fq_companion()?.fq_gf2_field();
        }
        let CtxKind::FqNmod { p: 2, degree: n @ 1..=64 } = *self.kind() else { return None };
        let nctx = fq_ctx_ptr::<sys::fq_nmod_ctx_struct>(self);
        let f = unsafe { &(*nctx).modulus[0] };
        let g = (0..n as usize).fold(0u64, |g, i| g | ((unsafe { *f.coeffs.add(i) } as u64 & 1) << i));
        Some(crate::gf2x::Gf2Field::new(n as u32, g))
    }
}

/// `gr_ctx_init_fq_zech_modulus_nmod_poly` with the tables of Zech
/// logarithms built by `zech_tables` rather than FLINT's loop, which
/// multiplies with `fq_nmod_mul` and takes most of the time of making a
/// small field. The tables are FLINT's own, so FLINT clears them. The
/// context gets its own copy of FLINT's methods, with the kernels of
/// `smallfq` in place of some.
///
/// # Safety
/// `c` must point to a zeroed context and `modulus` to a monic irreducible
/// polynomial of degree at least 1 with p^degree below 2^32.
pub(crate) unsafe fn init_fq_zech(c: *mut sys::gr_ctx_struct, modulus: *const sys::nmod_poly_struct, var: *const std::os::raw::c_char) -> std::os::raw::c_int {
    unsafe {
        let nctx = sys::flint_malloc(std::mem::size_of::<sys::fq_nmod_ctx_struct>()) as *mut sys::fq_nmod_ctx_struct;
        let zctx = sys::flint_malloc(std::mem::size_of::<sys::fq_zech_ctx_struct>()) as *mut sys::fq_zech_ctx_struct;
        sys::fq_nmod_ctx_init_modulus(nctx, modulus, var);
        if zech_tables(zctx, nctx) {
            (*zctx).owns_fq_nmod_ctx = 1;
            sys::_gr_ctx_init_fq_zech_from_ref(c, zctx as *const std::ffi::c_void);
            crate::smallfq::install(c);
            0
        } else {
            sys::fq_nmod_ctx_clear(nctx);
            sys::flint_free(zctx.cast());
            sys::flint_free(nctx.cast());
            1
        }
    }
}

/// `fq_zech_ctx_init_fq_nmod_ctx_check`: fill in `ctx` for the field of
/// `ctx2`, or return false (leaving nothing to free) if the generator is
/// not primitive.
///
/// The powers of the generator are kept as coefficient vectors (bits for p
/// = 2) and multiplied by it with a shift and one multiple of the modulus;
/// the tables are those of FLINT: the log of the element with base-p
/// digits i, the digits of g^i, and log(g^i + 1).
unsafe fn zech_tables(ctx: *mut sys::fq_zech_ctx_struct, ctx2: *mut sys::fq_nmod_ctx_struct) -> bool {
    let (z, n2) = unsafe { (&mut *ctx, &*ctx2) };
    let p = n2.mod_.n as u64;
    let f: &[sys::ulong] = unsafe { std::slice::from_raw_parts(n2.modulus[0].coeffs, n2.modulus[0].length as usize) };
    let d = f.len() - 1;
    let q = (0..d).try_fold(1u64, |a, _| a.checked_mul(p)).filter(|&q| q < 1 << 32).expect("a field small enough for Zech logarithms");
    let qm1 = q - 1;
    z.fq_nmod_ctx = ctx2;
    z.owns_fq_nmod_ctx = 0;
    z.is_conway = 0;
    z.p = p as sys::ulong;
    z.ppre = unsafe { sys::n_precompute_inverse(p as sys::ulong) };
    z.qm1 = qm1 as sys::ulong;
    z.qm1o2 = if p == 2 { 0 } else { qm1 / 2 } as sys::ulong;
    z.qm1opm1 = (qm1 / (p - 1)) as sys::ulong;
    // The norm of the generator (FLINT reads the first nonzero coefficient).
    let a0 = unsafe { *n2.a } as u64;
    z.prime_root = if d % 2 == 1 { p - a0 } else { a0 } as sys::ulong;
    let (qs, ps) = (q as usize, p as usize);
    let tables = unsafe { sys::flint_malloc(std::mem::size_of::<sys::ulong>() * (2 * qs + ps)) as *mut sys::ulong };
    let all = unsafe { std::slice::from_raw_parts_mut(tables, 2 * qs + ps) };
    let (zech, rest) = all.split_at_mut(qs);
    let (prime, eval) = rest.split_at_mut(ps);
    let mut rev = vec![qm1 as sys::ulong; qs];
    zech[qs - 1] = 0;
    prime[0] = qm1 as sys::ulong;
    eval[qs - 1] = 0;
    // Record g^i, whose digits have the value `v`; false if g^i was seen.
    let mut record = |i: u64, v: u64| {
        if rev[v as usize] != qm1 as sys::ulong {
            return false;
        }
        rev[v as usize] = i as sys::ulong;
        eval[i as usize] = v as sys::ulong;
        if v < p {
            prime[v as usize] = i as sys::ulong;
        }
        true
    };
    let ok = if p == 2 {
        let full = f.iter().enumerate().fold(0u64, |a, (k, &c)| a | (c as u64 & 1) << k);
        let mut r = 1u64;
        (0..qm1).all(|i| {
            let ok = record(i, r);
            r <<= 1;
            if r >> d & 1 == 1 {
                r ^= full;
            }
            ok
        })
    } else {
        // neg[t*d + k] = -t*f_k mod p, added when x^d (with coefficient t)
        // is reduced.
        let neg: Vec<u64> = (0..p).flat_map(|t| f[..d].iter().map(move |&c| (p - t * c as u64 % p) % p)).collect();
        let mut r = vec![0u64; d];
        r[0] = 1;
        (0..qm1).all(|i| {
            let ok = record(i, r.iter().rev().fold(0, |v, &c| v * p + c));
            let t = r[d - 1] as usize;
            r.copy_within(..d - 1, 1);
            r[0] = 0;
            if t != 0 {
                for (c, &n) in r.iter_mut().zip(&neg[t * d..(t + 1) * d]) {
                    let s = *c + n;
                    *c = if s >= p { s - p } else { s };
                }
            }
            ok
        })
    };
    if !ok {
        unsafe { sys::flint_free(tables.cast()) };
        return false;
    }
    // log(g^i + 1): adding one changes the constant digit only.
    let mut c = 0;
    for i in 0..qs {
        let nz = if c == ps - 1 { i + 1 - ps } else { i + 1 };
        zech[rev[i] as usize] = rev[nz];
        c = if c == ps - 1 { 0 } else { c + 1 };
    }
    z.zech_log_table = tables;
    z.prime_field_table = unsafe { tables.add(qs) };
    z.eval_table = unsafe { tables.add(qs + ps) };
    true
}

/// The coefficients of an `nmod_poly`, padded to `degree`.
fn nmod_words(a: &sys::nmod_poly_struct, degree: usize) -> Vec<u64> {
    (0..degree).map(|i| if (i as i64) < a.length as i64 { (unsafe { *a.coeffs.add(i) }) as u64 } else { 0 }).collect()
}

/// The FLINT context behind a `gr` finite field context.
fn fq_ctx_ptr<T>(ctx: &Ctx) -> *const T {
    unsafe { *((*ctx.ptr()).data.as_ptr() as *const *const T) }
}

impl Elem {
    /// The coordinates of an element of a finite field of word-sized
    /// characteristic in the power basis of its generator (constant term
    /// first, padded to the degree); the residue of a prime field element.
    pub fn fq_coords_u64(&self) -> Vec<u64> {
        match *self.ctx().kind() {
            CtxKind::Nmod(_) => vec![self.to_word().unwrap_or(0)],
            CtxKind::FqNmod { degree, .. } => {
                nmod_words(unsafe { &*(self.as_ptr() as *const sys::nmod_poly_struct) }, degree as usize)
            }
            CtxKind::FqPacked { .. } => crate::packed::coords(self),
            CtxKind::FqZech { degree, .. } => {
                let zctx = fq_ctx_ptr::<sys::fq_zech_ctx_struct>(self.ctx());
                let nctx = unsafe { (*zctx).fq_nmod_ctx };
                let mut a = sys::nmod_poly_struct::default();
                unsafe {
                    sys::fq_nmod_init(&mut a, nctx);
                    sys::fq_zech_get_fq_nmod(&mut a, self.as_ptr() as *const sys::fq_zech_struct, zctx);
                }
                let out = nmod_words(&a, degree as usize);
                unsafe { sys::fq_nmod_clear(&mut a, nctx) };
                out
            }
            _ => self.fq_coords().iter().map(|c| c.to_u64().unwrap_or(0)).collect(),
        }
    }

    /// The element of a finite field of word-sized characteristic with the
    /// given coordinates (each below p; missing ones are zero).
    pub fn fq_from_coords_u64(ctx: &Rc<Ctx>, coords: &[u64]) -> Elem {
        let mut e = Elem::zero(ctx);
        match *ctx.kind() {
            CtxKind::Nmod(_) => return Elem::from_word(ctx, coords.first().copied().unwrap_or(0)),
            CtxKind::FqPacked { .. } => return crate::packed::from_coords(ctx, coords),
            CtxKind::FqNmod { degree, .. } => {
                let a = e.as_mut_ptr() as *mut sys::nmod_poly_struct;
                for (i, &c) in coords.iter().enumerate().take(degree as usize).rev() {
                    if c != 0 {
                        unsafe { sys::nmod_poly_set_coeff_ui(a, i as sys::slong, c as sys::ulong) };
                    }
                }
            }
            CtxKind::FqZech { degree, .. } => {
                let zctx = fq_ctx_ptr::<sys::fq_zech_ctx_struct>(ctx);
                let nctx = unsafe { (*zctx).fq_nmod_ctx };
                let mut a = sys::nmod_poly_struct::default();
                unsafe {
                    sys::fq_nmod_init(&mut a, nctx);
                    for (i, &c) in coords.iter().enumerate().take(degree as usize).rev() {
                        if c != 0 {
                            sys::nmod_poly_set_coeff_ui(&mut a, i as sys::slong, c as sys::ulong);
                        }
                    }
                    sys::fq_zech_set_fq_nmod(e.as_mut_ptr() as *mut sys::fq_zech_struct, &a, zctx);
                    sys::fq_nmod_clear(&mut a, nctx);
                }
            }
            _ => {
                let cs: Vec<Integer> = coords.iter().map(|&c| Integer::from_u64(c)).collect();
                return Elem::fq_from_coords(ctx, &cs).expect("coordinates of a finite field element");
            }
        }
        e
    }

    /// The coordinates of an element of GF(2^n) with n up to 64 (without
    /// Zech logarithms) as bits, for `gf2x::Gf2Field`.
    pub fn fq_gf2_bits(&self) -> Option<u64> {
        if let CtxKind::FqPacked { p: 2, degree: 1..=64 } = *self.ctx().kind() {
            return Some(unsafe { *(self.as_ptr() as *const u64) });
        }
        let CtxKind::FqNmod { p: 2, degree: 1..=64 } = *self.ctx().kind() else { return None };
        let a = unsafe { &*(self.as_ptr() as *const sys::nmod_poly_struct) };
        Some((0..a.length as usize).fold(0, |b, i| b | ((unsafe { *a.coeffs.add(i) } as u64 & 1) << i)))
    }

    /// The element of GF(2^n) with n up to 64 with the given bits.
    pub fn fq_from_gf2_bits(ctx: &Rc<Ctx>, bits: u64) -> Elem {
        if let CtxKind::FqPacked { p: 2, degree: n @ 1..=64 } = *ctx.kind() {
            let mut e = Elem::zero(ctx);
            unsafe { *(e.as_mut_ptr() as *mut u64) = bits & u64::MAX >> (64 - n) };
            return e;
        }
        let coords: Vec<u64> = (0..64).map(|i| bits >> i & 1).collect();
        Elem::fq_from_coords_u64(ctx, &coords)
    }

    /// The element `g^k` of a field with Zech logarithms, where g is its
    /// generator (`k < q - 1`).
    pub fn fq_from_zech_log(ctx: &Rc<Ctx>, k: u64) -> Option<Elem> {
        let CtxKind::FqZech { .. } = ctx.kind() else { return None };
        let mut e = Elem::zero(ctx);
        unsafe { (*(e.as_mut_ptr() as *mut sys::fq_zech_struct)).value = k as sys::ulong };
        Some(e)
    }

    /// The number q - 1 for a field with Zech logarithms.
    pub fn zech_order(ctx: &Ctx) -> Option<u64> {
        match ctx.kind() {
            CtxKind::FqZech { .. } => Some(unsafe { (*fq_ctx_ptr::<sys::fq_zech_ctx_struct>(ctx)).qm1 } as u64),
            _ => None,
        }
    }

    /// Whether a polynomial over a finite field (a prime field included) is
    /// irreducible. Constants are not.
    pub fn poly_is_irreducible(&self) -> GrResult<bool> {
        crate::upoly::is_irreducible(self)
    }

    /// The factorisation of a non-zero polynomial over a finite field: its
    /// leading coefficient and its monic irreducible factors with their
    /// multiplicities, in FLINT's order.
    pub fn poly_factor(&self) -> GrResult<(Elem, Vec<(Elem, u64)>)> {
        let f = crate::upoly::factor(self)?;
        Ok((f.unit, f.factors))
    }
}

/// Arithmetic on the words of a field with Zech logarithms: an element is
/// its logarithm to the base of the field's generator g, in [0, q - 1), or
/// q - 1 for zero, as in FLINT. The handle reads the tables of the field's
/// context, which it keeps alive for good, so that it can be copied freely.
#[derive(Clone, Copy)]
pub struct Zech {
    /// q - 1, also the word of zero.
    qm1: u64,
    /// The logarithm of -1: (q - 1)/2, or 0 in characteristic 2.
    minus_one: u64,
    p: crate::Nmod,
    /// Z(n) with 1 + g^n = g^Z(n) (q - 1 where that is zero).
    zech: &'static [sys::ulong],
    /// The logarithms of 0, 1, ..., p - 1.
    prime: &'static [sys::ulong],
    /// The coordinates of g^n as the digits of an integer in base p.
    eval: &'static [sys::ulong],
}

impl PartialEq for Zech {
    fn eq(&self, o: &Zech) -> bool {
        std::ptr::eq(self.zech, o.zech)
    }
}

impl Eq for Zech {}

impl std::fmt::Debug for Zech {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Zech(q = {})", self.qm1 + 1)
    }
}

/// A table of a context that outlives its use (see `Zech::from_raw`).
unsafe fn table(t: *const sys::ulong, n: usize) -> &'static [sys::ulong] {
    unsafe { std::slice::from_raw_parts(t, n) }
}

impl Zech {
    /// The tables of `ctx`, a field with Zech logarithms.
    pub fn of(ctx: &Rc<Ctx>) -> Option<Zech> {
        let CtxKind::FqZech { .. } = ctx.kind() else { return None };
        std::mem::forget(ctx.clone());
        Some(unsafe { Zech::from_raw(fq_ctx_ptr::<sys::fq_zech_ctx_struct>(ctx)) })
    }

    /// The tables of the fq_zech context `z`, which must outlive every copy
    /// of the handle (`of` keeps its context alive for good instead).
    pub(crate) unsafe fn from_raw(z: *const sys::fq_zech_ctx_struct) -> Zech {
        let z = unsafe { &*z };
        let (q, p) = (z.qm1 as usize + 1, z.p as usize);
        Zech {
            qm1: z.qm1 as u64,
            minus_one: z.qm1o2 as u64,
            p: crate::Nmod::new(z.p as u64),
            zech: unsafe { table(z.zech_log_table, q) },
            prime: unsafe { table(z.prime_field_table, p) },
            eval: unsafe { table(z.eval_table, q) },
        }
    }

    /// The word of zero, q - 1.
    #[inline]
    pub fn zero(self) -> u64 {
        self.qm1
    }

    #[inline]
    pub fn mul(self, x: u64, y: u64) -> u64 {
        if x == self.qm1 || y == self.qm1 {
            return self.qm1;
        }
        let s = x + y;
        if s >= self.qm1 { s - self.qm1 } else { s }
    }

    #[inline]
    pub fn add(self, x: u64, y: u64) -> u64 {
        if x == self.qm1 {
            return y;
        }
        if y == self.qm1 {
            return x;
        }
        // g^x + g^y = g^y (1 + g^(x - y)).
        let c = self.zech[if x >= y { x - y } else { x + self.qm1 - y } as usize] as u64;
        self.mul(c, y)
    }

    #[inline]
    pub fn neg(self, x: u64) -> u64 {
        if x == self.qm1 { x } else { self.mul(x, self.minus_one) }
    }

    #[inline]
    pub fn sub(self, x: u64, y: u64) -> u64 {
        self.add(x, self.neg(y))
    }

    /// 1/x, unless x is zero.
    #[inline]
    pub fn inv(self, x: u64) -> Option<u64> {
        (x != self.qm1).then(|| if x == 0 { 0 } else { self.qm1 - x })
    }

    /// x/y, unless y is zero.
    #[inline]
    pub fn div(self, x: u64, y: u64) -> Option<u64> {
        Some(self.mul(x, self.inv(y)?))
    }

    /// x^e, unless x is zero and e negative.
    pub fn pow(self, x: u64, e: &Integer) -> Option<u64> {
        if x == self.qm1 {
            return (e.sign() >= 0).then_some(if e.is_zero() { 0 } else { self.qm1 });
        }
        Some((x as u128 * e.mod_u64(self.qm1) as u128 % self.qm1 as u128) as u64)
    }

    /// The word of the integer n.
    pub fn from_integer(self, n: &Integer) -> u64 {
        self.prime[self.p.reduce_integer(n) as usize] as u64
    }

    /// The value in [0, p) of x if it lies in the prime field.
    pub fn prime_value(self, x: u64) -> Option<u64> {
        let v = self.eval[x as usize] as u64;
        (v < self.p.modulus()).then_some(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gr::conway_polynomial;

    fn int(v: i64) -> Integer {
        Integer::from_i64(v)
    }

    #[test]
    fn coordinates() {
        let c = conway_polynomial(7, 4).unwrap();
        for zech in [true, false] {
            let f = Ctx::finite_field(&int(7), &c, zech).unwrap();
            let x = Elem::fq_from_coords_u64(&f, &[3, 0, 5, 1]);
            assert_eq!(x.fq_coords_u64(), vec![3, 0, 5, 1]);
            let g = f.generator().unwrap();
            let y = g.pow_i64(3).unwrap().add(&g.sqr().unwrap().mul_integer(&int(5)).unwrap()).unwrap().add(&Elem::from_i64(&f, 3).unwrap()).unwrap();
            assert!(x.equal(&y) == crate::gr::Truth::True);
        }
        let f = Ctx::finite_field(&int(7), &c, true).unwrap();
        assert_eq!(Elem::zech_order(&f), Some(2400));
        let g5 = Elem::fq_from_zech_log(&f, 5).unwrap();
        assert!(g5.equal(&f.generator().unwrap().pow_i64(5).unwrap()) == crate::gr::Truth::True);
    }

    /// FLINT's tables and ours for the field defined by `cs` over GF(p).
    fn zech_contexts_agree(p: u64, cs: &[u64]) {
        unsafe {
            let mut poly = sys::nmod_poly_struct::default();
            sys::nmod_poly_init(&mut poly, p as sys::ulong);
            for (i, &c) in cs.iter().enumerate() {
                sys::nmod_poly_set_coeff_ui(&mut poly, i as sys::slong, c as sys::ulong);
            }
            let var = std::ffi::CString::new("a").unwrap();
            let (mut na, mut nb) = (sys::fq_nmod_ctx_struct::default(), sys::fq_nmod_ctx_struct::default());
            sys::fq_nmod_ctx_init_modulus(&mut na, &poly, var.as_ptr());
            sys::fq_nmod_ctx_init_modulus(&mut nb, &poly, var.as_ptr());
            let (mut za, mut zb) = (sys::fq_zech_ctx_struct::default(), sys::fq_zech_ctx_struct::default());
            let ok = sys::fq_zech_ctx_init_fq_nmod_ctx_check(&mut za, &mut na) != 0;
            assert_eq!(zech_tables(&mut zb, &mut nb), ok, "{p} {cs:?}");
            if ok {
                assert_eq!((za.qm1, za.qm1o2, za.qm1opm1, za.p, za.prime_root), (zb.qm1, zb.qm1o2, zb.qm1opm1, zb.p, zb.prime_root), "{p} {cs:?}");
                assert_eq!(za.ppre.to_bits(), zb.ppre.to_bits());
                let n = 2 * (za.qm1 as usize + 1) + p as usize;
                assert!(std::slice::from_raw_parts(za.zech_log_table, n) == std::slice::from_raw_parts(zb.zech_log_table, n), "{p} {cs:?}");
                sys::fq_zech_ctx_clear(&mut za);
                sys::fq_zech_ctx_clear(&mut zb);
            }
            sys::fq_nmod_ctx_clear(&mut na);
            sys::fq_nmod_ctx_clear(&mut nb);
            sys::nmod_poly_clear(&mut poly);
        }
    }

    #[test]
    fn zech_tables_agree_with_flint() {
        for (p, dmax) in [(2u64, 16u64), (3, 10), (5, 6), (7, 5), (11, 4), (13, 3), (101, 2), (1021, 2), (65521, 1)] {
            for d in 1..=dmax {
                let c = conway_polynomial(p, d).unwrap();
                zech_contexts_agree(p, &c.iter().map(|x| x.to_u64().unwrap()).collect::<Vec<_>>());
            }
        }
        // Irreducible but not primitive: x^2 + 1 over GF(3), x^4 + x^3 +
        // x^2 + x + 1 over GF(2); and primitive but not Conway.
        zech_contexts_agree(3, &[1, 0, 1]);
        zech_contexts_agree(2, &[1, 1, 1, 1, 1]);
        zech_contexts_agree(2, &[1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]);
        zech_contexts_agree(7, &[3, 1, 1]);
        let f = Ctx::finite_field(&int(3), &[int(1), int(2), int(0), int(1)], true).unwrap();
        assert_eq!(Elem::zech_order(&f), Some(26));
        assert!(Ctx::finite_field(&int(3), &[int(1), int(0), int(1)], true).is_err());
    }

    #[test]
    fn zech_words_agree_with_flint() {
        for (p, d, cs) in [(2u64, 1u64, None), (2, 8, None), (3, 5, None), (7, 4, None), (13, 2, None), (7, 2, Some(vec![3, 1, 1]))] {
            let c: Vec<Integer> = cs.map_or_else(|| conway_polynomial(p, d).unwrap(), |cs| cs.into_iter().map(Integer::from_u64).collect());
            let f = Ctx::finite_field(&Integer::from_u64(p), &c, true).unwrap();
            let z = Zech::of(&f).unwrap();
            let q1 = z.zero();
            let elt = |w: u64| Elem::fq_from_zech_log(&f, w).unwrap();
            let word = |e: Elem| e.zech_log().unwrap_or(q1);
            let mut ws: Vec<u64> = (0..q1).step_by((q1 as usize / 30).max(1)).collect();
            ws.extend([q1, q1 / 2, q1 - 1]);
            for &x in &ws {
                let ex = elt(x);
                assert_eq!(z.neg(x), word(ex.neg().unwrap()));
                assert_eq!(z.inv(x), ex.inv().ok().map(word));
                assert_eq!(z.prime_value(x), ex.fq_prime_value().map(|v| v.to_u64().unwrap()));
                for e in [-7i64, -1, 0, 1, 2, 12345] {
                    assert_eq!(z.pow(x, &int(e)), ex.pow_i64(e).ok().map(word), "{p}^{d}: ({x})^{e}");
                }
                for &y in &ws {
                    let ey = elt(y);
                    assert_eq!(z.add(x, y), word(ex.add(&ey).unwrap()), "{p}^{d}: {x} + {y}");
                    assert_eq!(z.sub(x, y), word(ex.sub(&ey).unwrap()));
                    assert_eq!(z.mul(x, y), word(ex.mul(&ey).unwrap()));
                    assert_eq!(z.div(x, y), ex.div(&ey).ok().map(word));
                }
            }
            for n in [-5i64, -1, 0, 1, 2, 100, 1 << 40] {
                assert_eq!(z.from_integer(&int(n)), word(Elem::from_i64(&f, n).unwrap()));
            }
            assert_eq!(z, Zech::of(&f).unwrap());
        }
    }

    #[test]
    fn gf2_words() {
        let c = conway_polynomial(2, 40).unwrap();
        let f = Ctx::finite_field(&int(2), &c, false).unwrap();
        let k = f.fq_gf2_field().unwrap();
        let g = f.generator().unwrap();
        let (a, b) = (g.pow_i64(12345).unwrap(), g.pow_i64(987654321).unwrap());
        let (wa, wb) = (a.fq_gf2_bits().unwrap(), b.fq_gf2_bits().unwrap());
        assert_eq!(k.mul(wa, wb), a.mul(&b).unwrap().fq_gf2_bits().unwrap());
        assert_eq!(k.pow(2, 12345), wa);
        assert!(Elem::fq_from_gf2_bits(&f, wa).equal(&a) == crate::gr::Truth::True);
        assert!(Ctx::finite_field(&int(2), &conway_polynomial(2, 10).unwrap(), true).unwrap().fq_gf2_field().is_none());
    }

    #[test]
    fn irreducibility_and_factors() {
        // x^2 + 1 is irreducible over GF(7) and splits over GF(49).
        let fp = Ctx::residue_ring(&int(7));
        let px = Ctx::poly(&fp);
        let one = Elem::one(&fp).unwrap();
        let f = Elem::poly_from_coeffs(&px, &[one.clone(), Elem::zero(&fp), one.clone()]).unwrap();
        assert!(f.poly_is_irreducible().unwrap());
        let (lc, fs) = f.poly_factor().unwrap();
        assert!(lc.is_one() == crate::gr::Truth::True);
        assert_eq!(fs.len(), 1);
        for zech in [true, false] {
            let k = Ctx::finite_field(&int(7), &conway_polynomial(7, 2).unwrap(), zech).unwrap();
            let kx = Ctx::poly(&k);
            let o = Elem::one(&k).unwrap();
            let g = Elem::poly_from_coeffs(&kx, &[o.clone(), Elem::zero(&k), o.clone()]).unwrap();
            assert!(!g.poly_is_irreducible().unwrap());
            let (_, fs) = g.poly_factor().unwrap();
            assert_eq!(fs.iter().map(|(h, e)| (h.poly_len(), *e)).collect::<Vec<_>>(), vec![(2, 1), (2, 1)]);
        }
        // Over a prime field of multi-word characteristic.
        let p = Integer::from_i64(2).pow(89) - Integer::one();
        let fp = Ctx::residue_ring(&p);
        let px = Ctx::poly(&fp);
        let o = Elem::one(&fp).unwrap();
        let x2m1 = Elem::poly_from_coeffs(&px, &[o.neg().unwrap(), Elem::zero(&fp), o]).unwrap();
        assert!(!x2m1.poly_is_irreducible().unwrap());
        assert_eq!(x2m1.poly_factor().unwrap().1.len(), 2);
    }
}
