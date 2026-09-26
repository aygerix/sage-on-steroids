//! Dense matrices over FLINT's generic rings (`gr_mat`).
//!
//! A [`Mat`] keeps its entries as elements of a [`Ctx`], row after row.
//! FLINT's own matrix types (`fmpz_mat`, `fmpq_mat`, `nmod_mat`,
//! `fq_zech_mat`, ...) have the same layout, and the generic functions
//! hand the work to them where the ring's context says so: a product of
//! matrices over the integers is `fmpz_mat_mul`, one over `Z/nZ` is
//! `nmod_mat_mul`.

use std::ffi::c_void;
use std::rc::Rc;

use flint3_sys as sys;

use crate::gr::{Ctx, CtxKind, Elem, GrError, GrResult, Truth, check};
use crate::{Integer, Rational};

pub struct Mat {
    ctx: Rc<Ctx>,
    raw: sys::gr_mat_struct,
    /// Which entries (row after row) are negative zeros. Magma's reals keep
    /// the sign of zero and FLINT's floating-point entries do not, so a
    /// matrix of them keeps it here: set through `set_neg_zero`, moved by
    /// the rearrangements and following IEEE rules in sums and scalar
    /// multiples. Other results have positive zeros, as Magma's negations
    /// and products do. Empty while there is none.
    negz: Vec<bool>,
}

impl Drop for Mat {
    fn drop(&mut self) {
        unsafe { sys::gr_mat_clear(&mut self.raw, self.ctx.ptr()) };
    }
}

impl Clone for Mat {
    fn clone(&self) -> Mat {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        let st = unsafe { sys::gr_mat_set(&mut m.raw, &self.raw, self.ctx.ptr()) };
        assert_eq!(st, 0, "gr_mat_set failed");
        m.negz = self.negz.clone();
        m
    }
}

impl std::fmt::Debug for Mat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Mat({} x {} over {:?})", self.nrows(), self.ncols(), self.ctx.kind())
    }
}

impl Mat {
    /// The r by c zero matrix over `ctx`.
    pub fn zero(ctx: &Rc<Ctx>, r: usize, c: usize) -> Mat {
        let mut raw = sys::gr_mat_struct::default();
        unsafe { sys::gr_mat_init(&mut raw, r as sys::slong, c as sys::slong, ctx.ptr()) };
        Mat { ctx: ctx.clone(), raw, negz: Vec::new() }
    }

    /// The n by n identity matrix.
    pub fn identity(ctx: &Rc<Ctx>, n: usize) -> GrResult<Mat> {
        let mut m = Mat::zero(ctx, n, n);
        check(unsafe { sys::gr_mat_one(&mut m.raw, ctx.ptr()) })?;
        Ok(m)
    }

    /// The n by n matrix with `x` on the diagonal.
    pub fn scalar(n: usize, x: &Elem) -> GrResult<Mat> {
        let mut m = Mat::zero(x.ctx(), n, n);
        check(unsafe { sys::gr_mat_set_scalar(&mut m.raw, x.as_ptr(), m.ctx.ptr()) })?;
        Ok(m)
    }

    pub fn ctx(&self) -> &Rc<Ctx> {
        &self.ctx
    }

    #[inline]
    pub fn nrows(&self) -> usize {
        self.raw.r as usize
    }

    #[inline]
    pub fn ncols(&self) -> usize {
        self.raw.c as usize
    }

    #[inline]
    fn ptr(&self, i: usize, j: usize) -> *const c_void {
        debug_assert!(i < self.nrows() && j < self.ncols());
        let k = i * self.raw.stride as usize + j;
        unsafe { self.raw.entries.cast::<u8>().add(k * self.ctx.elem_size()).cast() }
    }

    #[inline]
    fn ptr_mut(&mut self, i: usize, j: usize) -> *mut c_void {
        self.ptr(i, j).cast_mut()
    }

    /// The entry in row i and column j (from 0).
    pub fn entry(&self, i: usize, j: usize) -> Elem {
        let mut e = Elem::new(&self.ctx);
        let st = unsafe { sys::gr_set(e.as_mut_ptr(), self.ptr(i, j), self.ctx.ptr()) };
        assert_eq!(st, 0, "gr_set failed");
        e
    }

    /// Whether the entry (i, j) is a negative zero.
    #[inline]
    pub fn neg_zero(&self, i: usize, j: usize) -> bool {
        !self.negz.is_empty() && self.negz[i * self.ncols() + j]
    }

    /// Mark the entry (i, j), a zero of a floating-point matrix, as a
    /// negative zero or not. Setting an entry unmarks it.
    pub fn set_neg_zero(&mut self, i: usize, j: usize, on: bool) {
        if self.negz.is_empty() {
            if !on {
                return;
            }
            self.negz = vec![false; self.nrows() * self.ncols()];
        }
        let c = self.ncols();
        self.negz[i * c + j] = on;
    }

    /// Set an entry to `x`, an element of the matrix's ring.
    pub fn set_entry(&mut self, i: usize, j: usize, x: &Elem) {
        debug_assert!(Rc::ptr_eq(x.ctx(), &self.ctx));
        self.set_neg_zero(i, j, false);
        let st = unsafe { sys::gr_set(self.ptr_mut(i, j), x.as_ptr(), self.ctx.ptr()) };
        assert_eq!(st, 0, "gr_set failed");
    }

    pub fn set_integer(&mut self, i: usize, j: usize, x: &Integer) -> GrResult<()> {
        self.set_neg_zero(i, j, false);
        check(unsafe { sys::gr_set_fmpz(self.ptr_mut(i, j), x.raw_ptr(), self.ctx.ptr()) })
    }

    pub fn set_rational(&mut self, i: usize, j: usize, x: &Rational) -> GrResult<()> {
        self.set_neg_zero(i, j, false);
        check(unsafe { sys::gr_set_fmpq(self.ptr_mut(i, j), x.raw_ptr(), self.ctx.ptr()) })
    }

    pub fn set_si(&mut self, i: usize, j: usize, x: i64) -> GrResult<()> {
        self.set_neg_zero(i, j, false);
        check(unsafe { sys::gr_set_si(self.ptr_mut(i, j), x as sys::slong, self.ctx.ptr()) })
    }

    /// The residue in an entry of a matrix over integers modulo a word.
    #[inline]
    pub fn word(&self, i: usize, j: usize) -> u64 {
        debug_assert!(matches!(self.ctx.kind(), CtxKind::Nmod(_)));
        unsafe { *self.ptr(i, j).cast::<u64>() }
    }

    /// Set an entry of a matrix over integers modulo a word to a residue.
    #[inline]
    pub fn set_word(&mut self, i: usize, j: usize, v: u64) {
        debug_assert!(matches!(self.ctx.kind(), CtxKind::Nmod(n) if v < *n));
        unsafe { *self.ptr_mut(i, j).cast::<u64>() = v };
    }

    /// An entry of a matrix over the integers.
    pub fn integer(&self, i: usize, j: usize) -> Integer {
        debug_assert!(matches!(self.ctx.kind(), CtxKind::Integers));
        let mut z = Integer::zero();
        unsafe { sys::fmpz_set(z.raw_mut_ptr(), self.ptr(i, j).cast()) };
        z
    }

    pub fn entry_is_zero(&self, i: usize, j: usize) -> bool {
        unsafe { sys::gr_is_zero(self.ptr(i, j), self.ctx.ptr()) == sys::truth_t_T_TRUE }
    }

    pub fn equal(&self, o: &Mat) -> Truth {
        if self.nrows() != o.nrows() || self.ncols() != o.ncols() {
            return Truth::False;
        }
        Truth::from_raw(unsafe { sys::gr_mat_equal(&self.raw, &o.raw, self.ctx.ptr()) })
    }

    pub fn is_zero(&self) -> Truth {
        Truth::from_raw(unsafe { sys::gr_mat_is_zero(&self.raw, self.ctx.ptr()) })
    }

    pub fn is_one(&self) -> Truth {
        Truth::from_raw(unsafe { sys::gr_mat_is_one(&self.raw, self.ctx.ptr()) })
    }

    pub fn is_neg_one(&self) -> Truth {
        Truth::from_raw(unsafe { sys::gr_mat_is_neg_one(&self.raw, self.ctx.ptr()) })
    }

    /// Whether a square matrix is a multiple of the identity.
    pub fn is_scalar(&self) -> Truth {
        Truth::from_raw(unsafe { sys::gr_mat_is_scalar(&self.raw, self.ctx.ptr()) })
    }

    pub fn is_diagonal(&self) -> Truth {
        Truth::from_raw(unsafe { sys::gr_mat_is_diagonal(&self.raw, self.ctx.ptr()) })
    }

    /// Whether the entries below the diagonal are zero.
    pub fn is_upper_triangular(&self) -> Truth {
        Truth::from_raw(unsafe { sys::gr_mat_is_upper_triangular(&self.raw, self.ctx.ptr()) })
    }

    /// Whether the entries above the diagonal are zero.
    pub fn is_lower_triangular(&self) -> Truth {
        Truth::from_raw(unsafe { sys::gr_mat_is_lower_triangular(&self.raw, self.ctx.ptr()) })
    }

    /// The number of entries that are not zero.
    pub fn count_nonzero(&self) -> usize {
        let mut n = 0;
        for i in 0..self.nrows() {
            for j in 0..self.ncols() {
                n += !self.entry_is_zero(i, j) as usize;
            }
        }
        n
    }

    /// The same entries over another context (`gr_set_other` on each).
    pub fn change_ring(&self, ctx: &Rc<Ctx>) -> GrResult<Mat> {
        let mut m = Mat::zero(ctx, self.nrows(), self.ncols());
        for i in 0..self.nrows() {
            for j in 0..self.ncols() {
                check(unsafe { sys::gr_set_other(m.ptr_mut(i, j), self.ptr(i, j), self.ctx.ptr(), ctx.ptr()) })?;
                if self.neg_zero(i, j) && m.floating() {
                    m.set_neg_zero(i, j, true);
                }
            }
        }
        Ok(m)
    }

    // ----- blocks and rearrangements ------------------------------------------

    /// The r by c block whose top left entry is (i, j).
    pub fn block(&self, i: usize, j: usize, r: usize, c: usize) -> Mat {
        assert!(i + r <= self.nrows() && j + c <= self.ncols(), "block out of range");
        let mut m = Mat::zero(&self.ctx, r, c);
        if r > 0 && c > 0 {
            let mut w = sys::gr_mat_struct::default();
            unsafe {
                sys::gr_mat_window_init(&mut w, &self.raw, i as sys::slong, j as sys::slong, (i + r) as sys::slong, (j + c) as sys::slong, self.ctx.ptr());
                let st = sys::gr_mat_set(&mut m.raw, &w, self.ctx.ptr());
                sys::gr_mat_window_clear(&mut w, self.ctx.ptr());
                assert_eq!(st, 0, "gr_mat_set failed");
            }
        }
        if !self.negz.is_empty() {
            for a in 0..r {
                for b in 0..c {
                    m.set_neg_zero(a, b, self.neg_zero(i + a, j + b));
                }
            }
        }
        m
    }

    /// The matrix of the given rows and columns (from 0), in that order.
    pub fn select(&self, rows: &[usize], cols: &[usize]) -> Mat {
        let mut m = Mat::zero(&self.ctx, rows.len(), cols.len());
        for (a, &i) in rows.iter().enumerate() {
            for (b, &j) in cols.iter().enumerate() {
                let st = unsafe { sys::gr_set(m.ptr_mut(a, b), self.ptr(i, j), self.ctx.ptr()) };
                assert_eq!(st, 0, "gr_set failed");
                if self.neg_zero(i, j) {
                    m.set_neg_zero(a, b, true);
                }
            }
        }
        m
    }

    /// Copy `b` into the block whose top left entry is (i, j).
    pub fn insert(&mut self, b: &Mat, i: usize, j: usize) {
        assert!(i + b.nrows() <= self.nrows() && j + b.ncols() <= self.ncols(), "block out of range");
        if b.nrows() == 0 || b.ncols() == 0 {
            return;
        }
        let mut w = sys::gr_mat_struct::default();
        unsafe {
            sys::gr_mat_window_init(&mut w, &self.raw, i as sys::slong, j as sys::slong, (i + b.nrows()) as sys::slong, (j + b.ncols()) as sys::slong, self.ctx.ptr());
            let st = sys::gr_mat_set(&mut w, &b.raw, self.ctx.ptr());
            sys::gr_mat_window_clear(&mut w, self.ctx.ptr());
            assert_eq!(st, 0, "gr_mat_set failed");
        }
        if !self.negz.is_empty() || !b.negz.is_empty() {
            for a in 0..b.nrows() {
                for c in 0..b.ncols() {
                    self.set_neg_zero(i + a, j + c, b.neg_zero(a, c));
                }
            }
        }
    }

    pub fn swap_rows(&mut self, i: usize, j: usize) {
        if i != j {
            unsafe { sys::gr_mat_swap_rows(&mut self.raw, std::ptr::null_mut(), i as sys::slong, j as sys::slong, self.ctx.ptr()) };
            if !self.negz.is_empty() {
                let c = self.ncols();
                for k in 0..c {
                    self.negz.swap(i * c + k, j * c + k);
                }
            }
        }
    }

    pub fn swap_cols(&mut self, i: usize, j: usize) {
        if i != j {
            unsafe { sys::gr_mat_swap_cols(&mut self.raw, std::ptr::null_mut(), i as sys::slong, j as sys::slong, self.ctx.ptr()) };
            if !self.negz.is_empty() {
                let c = self.ncols();
                for k in 0..self.nrows() {
                    self.negz.swap(k * c + i, k * c + j);
                }
            }
        }
    }

    pub fn transpose(&self) -> Mat {
        let mut m = Mat::zero(&self.ctx, self.ncols(), self.nrows());
        let st = unsafe { sys::gr_mat_transpose(&mut m.raw, &self.raw, self.ctx.ptr()) };
        assert_eq!(st, 0, "gr_mat_transpose failed");
        if !self.negz.is_empty() {
            for i in 0..self.nrows() {
                for j in 0..self.ncols() {
                    m.set_neg_zero(j, i, self.neg_zero(i, j));
                }
            }
        }
        m
    }

    /// `self` with `b` to its right.
    pub fn concat_horizontal(&self, b: &Mat) -> Mat {
        assert_eq!(self.nrows(), b.nrows());
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols() + b.ncols());
        m.insert(self, 0, 0);
        m.insert(b, 0, self.ncols());
        m
    }

    /// `self` with `b` below it.
    pub fn concat_vertical(&self, b: &Mat) -> Mat {
        assert_eq!(self.ncols(), b.ncols());
        let mut m = Mat::zero(&self.ctx, self.nrows() + b.nrows(), self.ncols());
        m.insert(self, 0, 0);
        m.insert(b, self.nrows(), 0);
        m
    }

    // ----- arithmetic ---------------------------------------------------------

    pub fn add(&self, b: &Mat) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_add(&mut m.raw, &self.raw, &b.raw, self.ctx.ptr()) })?;
        // -0 + -0 is the only sum that is a negative zero.
        if !self.negz.is_empty() && !b.negz.is_empty() {
            m.negz = self.negz.iter().zip(&b.negz).map(|(x, y)| *x && *y).collect();
        }
        Ok(m)
    }

    pub fn sub(&self, b: &Mat) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_sub(&mut m.raw, &self.raw, &b.raw, self.ctx.ptr()) })?;
        // And -0 - +0 the only such difference.
        if !self.negz.is_empty() {
            let c = self.ncols();
            for (k, &x) in self.negz.iter().enumerate() {
                if x && b.entry_is_zero(k / c, k % c) && !b.neg_zero(k / c, k % c) {
                    m.set_neg_zero(k / c, k % c, true);
                }
            }
        }
        Ok(m)
    }

    pub fn neg(&self) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_neg(&mut m.raw, &self.raw, self.ctx.ptr()) })?;
        Ok(m)
    }

    pub fn mul(&self, b: &Mat) -> GrResult<Mat> {
        assert_eq!(self.ncols(), b.nrows());
        let mut m = Mat::zero(&self.ctx, self.nrows(), b.ncols());
        check(unsafe { sys::gr_mat_mul(&mut m.raw, &self.raw, &b.raw, self.ctx.ptr()) })?;
        Ok(m)
    }

    /// `x * self`.
    pub fn scalar_mul(&self, x: &Elem) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_scalar_mul(&mut m.raw, x.as_ptr(), &self.raw, self.ctx.ptr()) })?;
        m.scaled_zeros(self, x);
        Ok(m)
    }

    /// `self * x`.
    pub fn mul_scalar(&self, x: &Elem) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_mul_scalar(&mut m.raw, &self.raw, x.as_ptr(), self.ctx.ptr()) })?;
        m.scaled_zeros(self, x);
        Ok(m)
    }

    /// `self / x`, for a unit x.
    pub fn div_scalar(&self, x: &Elem) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_div_scalar(&mut m.raw, &self.raw, x.as_ptr(), self.ctx.ptr()) })?;
        m.scaled_zeros(self, x);
        Ok(m)
    }

    /// The signs of the zeros of `self`, the product or quotient of `a` and
    /// a real scalar x (complex with zero imaginary part): the sign of a
    /// zero entry is that of the entry of `a` times that of x.
    fn scaled_zeros(&mut self, a: &Mat, x: &Elem) {
        if !self.floating() {
            return;
        }
        let re = match self.ctx.kind() {
            CtxKind::RealFloat(_) => x.to_real(),
            _ => x.to_complex_parts().filter(|(_, im)| im.is_zero()).map(|(re, _)| re),
        };
        let Some(re) = re else { return };
        let negative = re.sign() < 0;
        for i in 0..self.nrows() {
            for j in 0..self.ncols() {
                if self.entry_is_zero(i, j) {
                    let sa = if a.entry_is_zero(i, j) { a.neg_zero(i, j) } else { a.entry_sign_negative(i, j) };
                    self.set_neg_zero(i, j, sa != negative);
                }
            }
        }
    }

    /// Whether the (real part of the) entry (i, j) of a floating-point
    /// matrix is negative.
    fn entry_sign_negative(&self, i: usize, j: usize) -> bool {
        let e = self.entry(i, j);
        match self.ctx.kind() {
            CtxKind::RealFloat(_) => e.to_real().is_some_and(|r| r.sign() < 0),
            _ => e.to_complex_parts().is_some_and(|(re, _)| re.sign() < 0),
        }
    }

    /// `self^e` for a square matrix (e < 0 needs an invertible one).
    pub fn pow(&self, e: &Integer) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_pow_fmpz(&mut m.raw, &self.raw, e.raw_ptr(), self.ctx.ptr()) })?;
        Ok(m)
    }

    /// The inverse of a square matrix; `Domain` if it has none.
    pub fn inv(&self) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        let ok = match self.ctx.kind() {
            CtxKind::Nmod(_) => unsafe { sys::nmod_mat_inv(&mut m.nmod_view(), &self.nmod_view()) },
            // Multimodular, where the generic elimination over Q is slow.
            CtxKind::Rationals => unsafe { sys::fmpq_mat_inv(&mut m.fmpq_view(), &self.fmpq_view()) },
            _ => {
                check(unsafe { sys::gr_mat_inv(&mut m.raw, &self.raw, self.ctx.ptr()) })?;
                return Ok(m);
            }
        };
        if ok == 0 {
            return Err(GrError::Domain);
        }
        Ok(m)
    }

    /// The solution X of A·X = B for a square matrix A, or None if A is
    /// singular.
    pub fn nonsingular_solve(&self, b: &Mat) -> GrResult<Option<Mat>> {
        let mut x = Mat::zero(&self.ctx, self.ncols(), b.ncols());
        if let CtxKind::Nmod(_) = self.ctx.kind() {
            let ok = unsafe { sys::nmod_mat_solve(&mut x.nmod_view(), &self.nmod_view(), &b.nmod_view()) };
            return Ok((ok != 0).then_some(x));
        }
        match check(unsafe { sys::gr_mat_nonsingular_solve(&mut x.raw, &self.raw, &b.raw, self.ctx.ptr()) }) {
            Ok(()) => Ok(Some(x)),
            Err(GrError::Domain) => Ok(None),
            Err(e) => Err(e),
        }
    }

    pub fn trace(&self) -> GrResult<Elem> {
        let mut e = Elem::new(&self.ctx);
        check(unsafe { sys::gr_mat_trace(e.as_mut_ptr(), &self.raw, self.ctx.ptr()) })?;
        Ok(e)
    }

    // ----- linear algebra -------------------------------------------------------
    //
    // FLINT's own matrices over the integers, the rationals and the integers
    // modulo a word share the layout of `gr_mat`, so their fast routines run
    // on views of the same entries. The routines used here leave the entries
    // of their outputs in place (none swaps in new ones), as views need.

    fn nmod_view(&self) -> sys::nmod_mat_struct {
        debug_assert!(matches!(self.ctx.kind(), CtxKind::Nmod(_)));
        let n = unsafe { &*self.ctx.ptr().cast::<sys::nmod_t>() };
        let mod_ = sys::nmod_t { n: n.n, ninv: n.ninv, norm: n.norm };
        sys::nmod_mat_struct { entries: self.raw.entries.cast(), r: self.raw.r, c: self.raw.c, stride: self.raw.stride, mod_ }
    }

    fn fmpz_view(&self) -> sys::fmpz_mat_struct {
        debug_assert!(matches!(self.ctx.kind(), CtxKind::Integers));
        sys::fmpz_mat_struct { entries: self.raw.entries.cast(), r: self.raw.r, c: self.raw.c, stride: self.raw.stride }
    }

    fn fmpq_view(&self) -> sys::fmpq_mat_struct {
        debug_assert!(matches!(self.ctx.kind(), CtxKind::Rationals));
        sys::fmpq_mat_struct { entries: self.raw.entries.cast(), r: self.raw.r, c: self.raw.c, stride: self.raw.stride }
    }

    /// Whether the ring of the entries is known to be a field.
    pub fn over_field(&self) -> bool {
        self.floating() || self.ctx.is_field() == Truth::True
    }

    /// Whether the entries are floating-point reals or complex numbers,
    /// which FLINT treats as a field only through LU decompositions.
    pub fn floating(&self) -> bool {
        matches!(self.ctx.kind(), CtxKind::RealFloat(_) | CtxKind::ComplexFloat(_))
    }

    /// The reduced row echelon form of a matrix over a field, and the
    /// column of the pivot of each of its nonzero rows.
    pub fn rref(&self) -> GrResult<(Mat, Vec<usize>)> {
        let (r, c) = (self.nrows(), self.ncols());
        let (b, rank) = match self.ctx.kind() {
            CtxKind::Nmod(_) => {
                let b = self.clone();
                let rank = unsafe { sys::nmod_mat_rref(&mut b.nmod_view()) };
                (b, rank)
            }
            CtxKind::Rationals => {
                let b = Mat::zero(&self.ctx, r, c);
                let rank = unsafe { sys::fmpq_mat_rref(&mut b.fmpq_view(), &self.fmpq_view()) };
                (b, rank)
            }
            _ => {
                let mut b = Mat::zero(&self.ctx, r, c);
                let mut rank: sys::slong = 0;
                let rref = if self.floating() { sys::gr_mat_rref_lu } else { sys::gr_mat_rref };
                check(unsafe { rref(&mut rank, &mut b.raw, &self.raw, self.ctx.ptr()) })?;
                (b, rank)
            }
        };
        let pivots = (0..rank as usize).map(|i| (0..c).find(|&j| !b.entry_is_zero(i, j)).expect("a pivot in each nonzero row")).collect();
        Ok((b, pivots))
    }

    /// The rank of a matrix over the integers or a field.
    pub fn rank(&self) -> GrResult<usize> {
        let rank = match self.ctx.kind() {
            CtxKind::Integers => unsafe { sys::fmpz_mat_rank(&self.fmpz_view()) },
            CtxKind::Nmod(_) | CtxKind::Rationals => return Ok(self.rref()?.1.len()),
            _ => {
                let mut rank: sys::slong = 0;
                let f = if self.floating() { sys::gr_mat_rank_lu } else { sys::gr_mat_rank };
                match check(unsafe { f(&mut rank, &self.raw, self.ctx.ptr()) }) {
                    Err(GrError::Unable) if self.ctx.is_integral_domain() == Truth::True => return self.rank_division_free(),
                    st => st?,
                }
                rank
            }
        };
        Ok(rank as usize)
    }

    /// The rank over an integral domain by elimination without division,
    /// each row below a pivot p with entry a becoming p·row - a·(pivot
    /// row): for rings such as FLINT's generic multivariate polynomials,
    /// which cannot divide exactly as fraction-free LU needs. The entries
    /// grow fast, so it suits small matrices (Jacobians and the like).
    fn rank_division_free(&self) -> GrResult<usize> {
        let (m, n) = (self.nrows(), self.ncols());
        let mut w = self.clone();
        let mut row = 0;
        for col in 0..n {
            if row == m {
                break;
            }
            let Some(r) = (row..m).find(|&i| !w.entry_is_zero(i, col)) else { continue };
            w.swap_rows(r, row);
            let p = w.entry(row, col);
            for i in row + 1..m {
                if w.entry_is_zero(i, col) {
                    continue;
                }
                let a = w.entry(i, col);
                for k in col + 1..n {
                    let x = p.mul(&w.entry(i, k))?.sub(&a.mul(&w.entry(row, k))?)?;
                    w.set_entry(i, k, &x);
                }
                w.set_entry(i, col, &Elem::new(&self.ctx));
            }
            row += 1;
        }
        Ok(row)
    }

    /// The determinant of a square matrix.
    pub fn det(&self) -> GrResult<Elem> {
        assert_eq!(self.nrows(), self.ncols(), "determinant of a matrix that is not square");
        if let CtxKind::Nmod(_) = self.ctx.kind() {
            return Ok(Elem::from_word(&self.ctx, unsafe { sys::nmod_mat_det(&self.nmod_view()) }));
        }
        let mut e = Elem::new(&self.ctx);
        check(unsafe { sys::gr_mat_det(e.as_mut_ptr(), &self.raw, self.ctx.ptr()) })?;
        Ok(e)
    }

    /// The coefficients of the characteristic polynomial det(x·I - A) of a
    /// square matrix, the constant term first.
    pub fn charpoly(&self) -> GrResult<Vec<Elem>> {
        let n = self.nrows();
        let mut c = Mat::zero(&self.ctx, 1, n + 1);
        check(unsafe { sys::_gr_mat_charpoly(c.ptr_mut(0, 0), &self.raw, self.ctx.ptr()) })?;
        Ok((0..=n).map(|j| c.entry(0, j)).collect())
    }

    /// The coefficients of the minimal polynomial of a square matrix over
    /// the integers or a field, the constant term first: FLINT's modular
    /// algorithms over the integers and the rationals, and otherwise its
    /// Krylov-space one over a field.
    pub fn minpoly(&self) -> GrResult<Vec<Elem>> {
        assert_eq!(self.nrows(), self.ncols(), "minimal polynomial of a matrix that is not square");
        if self.nrows() == 0 {
            return Ok(vec![Elem::one(&self.ctx)?]);
        }
        let elem = |f: &mut dyn FnMut(*mut c_void)| {
            let mut e = Elem::new(&self.ctx);
            f(e.as_mut_ptr());
            e
        };
        unsafe {
            match self.ctx.kind() {
                CtxKind::Integers => {
                    let mut p = sys::fmpz_poly_struct::default();
                    sys::fmpz_poly_init(&mut p);
                    sys::fmpz_mat_minpoly(&mut p, &self.fmpz_view());
                    let cs = (0..p.length as usize).map(|i| elem(&mut |e| sys::fmpz_set(e.cast(), p.coeffs.add(i)))).collect();
                    sys::fmpz_poly_clear(&mut p);
                    Ok(cs)
                }
                CtxKind::Rationals => {
                    let mut p = sys::fmpq_poly_struct::default();
                    sys::fmpq_poly_init(&mut p);
                    sys::fmpq_mat_minpoly(&mut p, &self.fmpq_view());
                    let cs = (0..p.length).map(|i| elem(&mut |e| sys::fmpq_poly_get_coeff_fmpq(e.cast(), &p, i))).collect();
                    sys::fmpq_poly_clear(&mut p);
                    Ok(cs)
                }
                CtxKind::Nmod(_) if self.ctx.is_field() == Truth::True => {
                    let view = self.nmod_view();
                    let mut p = sys::nmod_poly_struct::default();
                    sys::nmod_poly_init(&mut p, view.mod_.n);
                    sys::nmod_mat_minpoly(&mut p, &view);
                    let cs = (0..p.length as usize).map(|i| Elem::from_word(&self.ctx, *p.coeffs.add(i))).collect();
                    sys::nmod_poly_clear(&mut p);
                    Ok(cs)
                }
                _ => {
                    let mut p = sys::gr_poly_struct::default();
                    sys::gr_poly_init(&mut p, self.ctx.ptr());
                    let st = sys::gr_mat_minpoly_field(&mut p, &self.raw, self.ctx.ptr());
                    let cs = (0..p.length).map(|i| elem(&mut |e| assert_eq!(sys::gr_poly_get_coeff_scalar(e, &p, i, self.ctx.ptr()), 0))).collect();
                    sys::gr_poly_clear(&mut p, self.ctx.ptr());
                    check(st).map(|_| cs)
                }
            }
        }
    }

    /// A basis of the left kernel {v : v·A = 0} of a matrix over a field,
    /// as Magma's `KernelMatrix` gives it: from the reduced echelon form of
    /// the transpose, a row for each column f without a pivot, with -1 in
    /// place f and the entries of column f in the places of the pivots.
    pub fn left_kernel(&self) -> GrResult<Mat> {
        let (e, pivots) = self.transpose().rref()?;
        let m = self.nrows();
        let free: Vec<usize> = (0..m).filter(|j| !pivots.contains(j)).collect();
        let mut k = Mat::zero(&self.ctx, free.len(), m);
        let minus_one = Elem::from_i64(&self.ctx, -1)?;
        for (row, &f) in free.iter().enumerate() {
            k.set_entry(row, f, &minus_one);
            for (i, &p) in pivots.iter().enumerate() {
                let st = unsafe { sys::gr_set(k.ptr_mut(row, p), e.ptr(i, f), self.ctx.ptr()) };
                assert_eq!(st, 0, "gr_set failed");
            }
        }
        Ok(k)
    }

    /// Row i minus c times row k (over integers modulo a word, by FLINT's
    /// own vector routines).
    fn submul_row(&mut self, i: usize, k: usize, c: &Elem) -> GrResult<()> {
        let n = self.ncols();
        if n == 0 {
            return Ok(());
        }
        let (dst, src) = (self.ptr_mut(i, 0), self.ptr(k, 0));
        if let Some(w) = c.to_word() {
            let md = self.nmod_view().mod_;
            if w != 0 {
                unsafe { sys::_nmod_vec_scalar_addmul_nmod(dst.cast(), src.cast(), n as sys::slong, md.n - w, md) };
            }
            return Ok(());
        }
        check(unsafe { sys::_gr_vec_submul_scalar(dst, src, n as sys::slong, c.as_ptr(), self.ctx.ptr()) })
    }

    /// Row i times c.
    fn scale_row(&mut self, i: usize, c: &Elem) -> GrResult<()> {
        let n = self.ncols();
        if n == 0 {
            return Ok(());
        }
        let (dst, src) = (self.ptr_mut(i, 0), self.ptr(i, 0));
        if let Some(w) = c.to_word() {
            let md = self.nmod_view().mod_;
            unsafe { sys::_nmod_vec_scalar_mul_nmod(dst.cast(), src.cast(), n as sys::slong, w, md) };
            return Ok(());
        }
        check(unsafe { sys::_gr_vec_mul_scalar(dst, src, n as sys::slong, c.as_ptr(), self.ctx.ptr()) })
    }

    /// The reduced echelon form of a matrix over a field with a
    /// transformation, as Magma finds them: each row in turn is reduced by
    /// the pivots found so far and scaled to a pivot of 1, and a row that
    /// becomes zero is swapped with the last row not yet reduced (so the
    /// zero rows collect at the bottom). The pivot rows are then cleared
    /// above their pivots and sorted by pivot column.
    pub fn echelon_transform(&self) -> GrResult<Echelon> {
        let (m, n) = (self.nrows(), self.ncols());
        let mut w = self.clone();
        let mut t = Mat::identity(&self.ctx, m)?;
        // The pivots found, as (column, row).
        let mut piv: Vec<(usize, usize)> = Vec::new();
        let (mut i, mut last) = (0, m);
        while i < last {
            for &(col, k) in &piv {
                if !w.entry_is_zero(i, col) {
                    let c = w.entry(i, col);
                    w.submul_row(i, k, &c)?;
                    t.submul_row(i, k, &c)?;
                }
            }
            match (0..n).find(|&j| !w.entry_is_zero(i, j)) {
                None => {
                    last -= 1;
                    w.swap_rows(i, last);
                    t.swap_rows(i, last);
                }
                Some(j) => {
                    let inv = w.entry(i, j).inv()?;
                    w.scale_row(i, &inv)?;
                    t.scale_row(i, &inv)?;
                    piv.push((j, i));
                    i += 1;
                }
            }
        }
        for a in 0..piv.len() {
            let (col, k) = piv[a];
            for &(_, i) in &piv {
                if i != k && !w.entry_is_zero(i, col) {
                    let c = w.entry(i, col);
                    w.submul_row(i, k, &c)?;
                    t.submul_row(i, k, &c)?;
                }
            }
        }
        piv.sort_unstable();
        let rows: Vec<usize> = piv.iter().map(|&(_, k)| k).chain(piv.len()..m).collect();
        let (e, t) = (w.select(&rows, &(0..n).collect::<Vec<_>>()), t.select(&rows, &(0..m).collect::<Vec<_>>()));
        Ok(Echelon { e, t, pivots: piv.iter().map(|&(col, _)| col).collect() })
    }

    /// A basis of the right nullspace {v : A·v = 0} of a matrix over the
    /// integers, as the columns of a matrix (integral, but not reduced).
    pub fn nullspace_z(&self) -> Mat {
        let c = self.ncols();
        let res = Mat::zero(&self.ctx, c, c);
        let nullity = unsafe { sys::fmpz_mat_nullspace(&mut res.fmpz_view(), &self.fmpz_view()) } as usize;
        res.block(0, 0, c, nullity)
    }

    /// The Hermite normal form of a matrix over the integers: upper
    /// triangular, with positive pivots and the entries above each pivot
    /// reduced to [0, pivot).
    pub fn hnf(&self) -> Mat {
        let h = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        unsafe { sys::fmpz_mat_hnf(&mut h.fmpz_view(), &self.fmpz_view()) };
        h
    }

    /// The Hermite normal form H of a matrix over the integers with a
    /// unimodular U such that U·A = H.
    pub fn hnf_transform(&self) -> (Mat, Mat) {
        let m = self.nrows();
        let (h, u) = (Mat::zero(&self.ctx, m, self.ncols()), Mat::zero(&self.ctx, m, m));
        unsafe { sys::fmpz_mat_hnf_transform(&mut h.fmpz_view(), &mut u.fmpz_view(), &self.fmpz_view()) };
        (h, u)
    }

    /// The rows of a matrix over the integers reduced by LLL (δ = 0.99,
    /// η = 0.51), with the unimodular transformation, in place.
    pub fn lll_transform(&mut self, u: &mut Mat) {
        let mut fl = sys::fmpz_lll_struct::default();
        unsafe {
            sys::fmpz_lll_context_init(&mut fl, 0.99, 0.51, sys::rep_type_Z_BASIS, sys::gram_type_APPROX);
            sys::fmpz_lll(&mut self.fmpz_view(), &mut u.fmpz_view(), &fl);
        }
    }
}

/// A reduced echelon form with a transformation (`Mat::echelon_transform`).
pub struct Echelon {
    /// The reduced row echelon form E.
    pub e: Mat,
    /// An invertible T with T·A = E.
    pub t: Mat,
    /// The column of the pivot of each nonzero row of E.
    pub pivots: Vec<usize>,
}
