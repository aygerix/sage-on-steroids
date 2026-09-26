//! Safe wrappers around the parts of FLINT used by calyx.
//!
//! This crate is the only place in the workspace that talks to `flint3-sys`
//! directly. Everything else works with the types exported here, so the
//! arithmetic backend can be swapped or extended without touching the
//! interpreter.

pub mod approx;
pub mod ball;
mod complex;
mod crt;
mod floatpoly;
pub mod fq;
pub mod gf2x;
pub mod gr;
pub mod mpoly;
pub mod upoly;
mod integer;
mod lanes;
mod lll;
pub mod mat;
mod packed;
pub mod polroots;
mod modular;
pub mod modn;
pub mod mpfr;
mod nmod;
pub mod nmod_poly;
pub mod quadrature;
mod rational;
mod real;
mod series;
pub mod smallfq;
mod special;

pub use complex::{Complex, Elementary, ModifiedPolylog};
pub use crt::Crt;
pub use integer::{Factorization, Integer};
pub use lll::{lll, lll_l2, lll_with};
pub use modular::{Modular, ThetaCost};
pub use nmod::{Nmod, gcd as gcd_u64};
pub use rational::Rational;
pub use real::{Real, bits_for_digits, digits_for_bits, parse_decimal};
pub use series::EulerSum;
pub use special::bernoulli;

use std::ffi::{CStr, c_void};
use std::os::raw::c_char;
use std::path::PathBuf;

unsafe extern "C" {
    static flint_version: c_char;
}

#[repr(C)]
struct DlInfo {
    filename: *const c_char,
    base: *mut c_void,
    symbol: *const c_char,
    address: *mut c_void,
}

#[cfg_attr(target_os = "linux", link(name = "dl"))]
unsafe extern "C" {
    fn dladdr(address: *const c_void, info: *mut DlInfo) -> i32;
}

/// The version of the FLINT library linked at run time.
pub fn version() -> String {
    unsafe { CStr::from_ptr(&raw const flint_version).to_string_lossy().into_owned() }
}

/// The shared FLINT library selected by the dynamic loader.
pub fn library_path() -> Option<PathBuf> {
    let mut info = DlInfo { filename: std::ptr::null(), base: std::ptr::null_mut(), symbol: std::ptr::null(), address: std::ptr::null_mut() };
    let found = unsafe { dladdr((&raw const flint_version).cast(), &mut info) };
    (found != 0 && !info.filename.is_null()).then(|| PathBuf::from(unsafe { CStr::from_ptr(info.filename) }.to_string_lossy().into_owned()))
}

/// Copy a FLINT-allocated C string into a Rust `String` and free it.
///
/// # Safety
/// `ptr` must be a NUL-terminated string allocated by FLINT's allocator.
unsafe fn take_flint_string(ptr: *mut c_char) -> String {
    let s = unsafe { CStr::from_ptr(ptr) }.to_string_lossy().into_owned();
    unsafe { flint3_sys::flint_free(ptr.cast()) };
    s
}
