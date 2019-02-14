// Copyright © 2016–2019 University of Malta

// This program is free software: you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation, either version 3 of
// the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License and a copy of the GNU General Public License along with
// this program. If not, see <https://www.gnu.org/licenses/>.

use cast;
use gmp_mpfr_sys::gmp::{self, mpz_t};
use misc::NegAbs;
use ops::NegAssign;
use std::cmp::Ordering;
use std::os::raw::{c_int, c_long, c_ulong};
use std::ptr;
use std::{i16, i8, u16, u8};
use Integer;

#[cfg(gmp_limb_bits_32)]
pub use ext::xmpz32::*;
#[cfg(gmp_limb_bits_64)]
pub use ext::xmpz64::*;

macro_rules! wrap {
    (fn $fn:ident($($op:ident),* $(; $param:ident: $T:ty)*) -> $deleg:path) => {
        #[inline]
        pub fn $fn(
            rop: &mut Integer,
            $($op: Option<&Integer>,)*
            $($param: $T,)*
        ) {
            unsafe {
                $deleg(
                    rop.as_raw_mut(),
                    $($op.unwrap_or(rop).as_raw(),)*
                    $($param.into(),)*
                );
            }
        }
    };
}

macro_rules! wrap0 {
    (fn $fn:ident($($param:ident: $T:ty),*) -> $deleg:path) => {
        #[inline]
        pub fn $fn(rop: &mut Integer, $($param: $T),*) {
            unsafe {
                $deleg(rop.as_raw_mut(), $($param.into()),*);
            }
        }
    };
}

#[inline]
pub fn si_pow_ui(rop: &mut Integer, base: i32, exp: u32) {
    let (base_neg, base_abs) = base.neg_abs();
    ui_pow_ui(rop, base_abs, exp);
    if base_neg && (exp & 1) == 1 {
        neg(rop, None);
    }
}

#[inline]
pub fn signum(rop: &mut Integer, op: Option<&Integer>) {
    let size = op.unwrap_or(rop).inner().size;
    if size < 0 {
        set_m1(rop);
    } else if size > 0 {
        set_1(rop);
    } else {
        set_0(rop);
    }
}

pub fn keep_signed_bits(rop: &mut Integer, op: Option<&Integer>, b: u32) {
    let rop_ptr = rop.as_raw_mut();
    let op_ptr = op.unwrap_or(rop).as_raw();
    let b = b.into();
    unsafe {
        if b > 0 && gmp::mpz_tstbit(op_ptr, b - 1) != 0 {
            gmp::mpz_cdiv_r_2exp(rop_ptr, op_ptr, b);
        } else {
            gmp::mpz_fdiv_r_2exp(rop_ptr, op_ptr, b);
        }
    }
}

pub fn next_pow_of_two(rop: &mut Integer, op: Option<&Integer>) {
    let size = op.unwrap_or(rop).inner().size;
    if size <= 0 {
        set_1(rop);
        return;
    }
    let significant = cast::cast(significant_bits(op.unwrap_or(rop)));
    let first_one = unsafe { gmp::mpn_scan1(op.unwrap_or(rop).inner().d, 0) };
    let bit = if first_one == significant - 1 {
        if op.is_none() {
            return;
        }
        first_one
    } else {
        significant
    };
    set_0(rop);
    unsafe {
        gmp::mpz_setbit(rop.as_raw_mut(), bit);
    }
}

#[inline]
pub fn divexact_ui(q: &mut Integer, dividend: Option<&Integer>, divisor: u32) {
    assert_ne!(divisor, 0, "division by zero");
    unsafe {
        gmp::mpz_divexact_ui(
            q.as_raw_mut(),
            dividend.unwrap_or(q).as_raw(),
            divisor.into(),
        );
    }
}

#[inline]
pub fn root(rop: &mut Integer, op: Option<&Integer>, n: u32) {
    assert_ne!(n, 0, "zeroth root");
    let op_ptr = op.unwrap_or(rop).as_raw();
    let even_root_of_neg = n & 1 == 0 && unsafe { gmp::mpz_sgn(op_ptr) < 0 };
    assert!(!even_root_of_neg, "even root of negative");
    unsafe {
        gmp::mpz_root(rop.as_raw_mut(), op_ptr, n.into());
    }
}

#[inline]
pub fn square(rop: &mut Integer, op: Option<&Integer>) {
    let op_ptr = op.unwrap_or(rop).as_raw();
    unsafe {
        gmp::mpz_mul(rop.as_raw_mut(), op_ptr, op_ptr);
    }
}

#[inline]
pub fn sqrt(rop: &mut Integer, op: Option<&Integer>) {
    let op_ptr = op.unwrap_or(rop).as_raw();
    let square_root_of_neg = unsafe { gmp::mpz_sgn(op_ptr) < 0 };
    assert!(!square_root_of_neg, "square root of negative");
    unsafe {
        gmp::mpz_sqrt(rop.as_raw_mut(), op_ptr);
    }
}

#[inline]
pub fn rootrem(
    root: &mut Integer,
    rem: &mut Integer,
    op: Option<&Integer>,
    n: u32,
) {
    assert_ne!(n, 0, "zeroth root");
    let op_ptr = op.unwrap_or(root).as_raw();
    let even_root_of_neg = n & 1 == 0 && unsafe { gmp::mpz_sgn(op_ptr) < 0 };
    assert!(!even_root_of_neg, "even root of negative");
    unsafe {
        gmp::mpz_rootrem(root.as_raw_mut(), rem.as_raw_mut(), op_ptr, n.into());
    }
}

#[inline]
pub fn sqrtrem(root: &mut Integer, rem: &mut Integer, op: Option<&Integer>) {
    let op_ptr = op.unwrap_or(root).as_raw();
    let square_root_of_neg = unsafe { gmp::mpz_sgn(op_ptr) < 0 };
    assert!(!square_root_of_neg, "square root of negative");
    unsafe {
        gmp::mpz_sqrtrem(root.as_raw_mut(), rem.as_raw_mut(), op_ptr);
    }
}

// op2

#[inline]
pub fn divexact(
    q: &mut Integer,
    dividend: Option<&Integer>,
    divisor: &Integer,
) {
    assert_ne!(divisor.cmp0(), Ordering::Equal, "division by zero");
    unsafe {
        gmp::mpz_divexact(
            q.as_raw_mut(),
            dividend.unwrap_or(q).as_raw(),
            divisor.as_raw(),
        );
    }
}

#[inline]
pub fn gcd(rop: &mut Integer, op1: Option<&Integer>, op2: &Integer) {
    unsafe {
        gmp::mpz_gcd(
            rop.as_raw_mut(),
            op1.unwrap_or(rop).as_raw(),
            op2.as_raw(),
        );
    }
}

#[inline]
pub fn lcm(rop: &mut Integer, op1: Option<&Integer>, op2: &Integer) {
    unsafe {
        gmp::mpz_lcm(
            rop.as_raw_mut(),
            op1.unwrap_or(rop).as_raw(),
            op2.as_raw(),
        );
    }
}

// op2_2

#[inline]
pub fn tdiv_qr(
    q: &mut Integer,
    r: &mut Integer,
    n: Option<&Integer>,
    d: Option<&Integer>,
) {
    let n_ptr = n.unwrap_or(q).as_raw();
    let d_ptr = d.unwrap_or(r).as_raw();
    unsafe {
        assert_ne!(gmp::mpz_sgn(d_ptr), 0, "division by zero");
        gmp::mpz_tdiv_qr(q.as_raw_mut(), r.as_raw_mut(), n_ptr, d_ptr);
    }
}

#[inline]
pub fn cdiv_qr(
    q: &mut Integer,
    r: &mut Integer,
    n: Option<&Integer>,
    d: Option<&Integer>,
) {
    let n_ptr = n.unwrap_or(q).as_raw();
    let d_ptr = d.unwrap_or(r).as_raw();
    unsafe {
        assert_ne!(gmp::mpz_sgn(d_ptr), 0, "division by zero");
        gmp::mpz_cdiv_qr(q.as_raw_mut(), r.as_raw_mut(), n_ptr, d_ptr);
    }
}

#[inline]
pub fn fdiv_qr(
    q: &mut Integer,
    r: &mut Integer,
    n: Option<&Integer>,
    d: Option<&Integer>,
) {
    let n_ptr = n.unwrap_or(q).as_raw();
    let d_ptr = d.unwrap_or(r).as_raw();
    unsafe {
        assert_ne!(gmp::mpz_sgn(d_ptr), 0, "division by zero");
        gmp::mpz_fdiv_qr(q.as_raw_mut(), r.as_raw_mut(), n_ptr, d_ptr);
    }
}

pub fn rdiv_qr(
    q: &mut Integer,
    r: &mut Integer,
    n: Option<&Integer>,
    d: Option<&Integer>,
) {
    let n_ptr = n.unwrap_or(q).as_raw();
    // make sure d is not going to be aliased and overwritten
    let r_clone;
    let d_ptr = if let Some(d) = d {
        d.as_raw()
    } else {
        r_clone = r.clone();
        r_clone.as_raw()
    };
    unsafe {
        assert_ne!(gmp::mpz_sgn(d_ptr), 0, "division by zero");
        gmp::mpz_tdiv_qr(q.as_raw_mut(), r.as_raw_mut(), n_ptr, d_ptr);
        if round_away(r.as_raw(), d_ptr) {
            if (gmp::mpz_sgn(r.as_raw()) < 0) == (gmp::mpz_sgn(d_ptr) < 0) {
                // positive q
                gmp::mpz_add_ui(q.as_raw_mut(), q.as_raw(), 1);
                gmp::mpz_sub(r.as_raw_mut(), r.as_raw(), d_ptr);
            } else {
                // negative q
                gmp::mpz_sub_ui(q.as_raw_mut(), q.as_raw(), 1);
                gmp::mpz_add(r.as_raw_mut(), r.as_raw(), d_ptr);
            }
        }
    }
}

#[inline]
pub fn ediv_qr(
    q: &mut Integer,
    r: &mut Integer,
    n: Option<&Integer>,
    d: Option<&Integer>,
) {
    match d.unwrap_or(r).cmp0() {
        Ordering::Equal => panic!("division by zero"),
        Ordering::Less => cdiv_qr(q, r, n, d),
        Ordering::Greater => fdiv_qr(q, r, n, d),
    }
}

// op2_3

#[inline]
pub fn gcdext(
    g: &mut Integer,
    s: &mut Integer,
    t: Option<&mut Integer>,
    op1: Option<&Integer>,
    op2: Option<&Integer>,
) {
    unsafe {
        gmp::mpz_gcdext(
            g.as_raw_mut(),
            s.as_raw_mut(),
            t.map(|x| x.as_raw_mut()).unwrap_or_else(ptr::null_mut),
            op1.unwrap_or(g).as_raw(),
            op2.unwrap_or(s).as_raw(),
        );
    }
}

wrap0! { fn ui_pow_ui(base: u32, exponent: u32) -> gmp::mpz_ui_pow_ui }
wrap0! { fn fac_ui(n: u32) -> gmp::mpz_fac_ui }
wrap0! { fn twofac_ui(n: u32) -> gmp::mpz_2fac_ui }
wrap0! { fn mfac_uiui(n: u32, m: u32) -> gmp::mpz_mfac_uiui }
wrap0! { fn primorial_ui(n: u32) -> gmp::mpz_primorial_ui }
wrap0! { fn bin_uiui(n: u32, k: u32) -> gmp::mpz_bin_uiui }
wrap0! { fn fib_ui(n: u32) -> gmp::mpz_fib_ui }
wrap0! { fn lucnum_ui(n: u32) -> gmp::mpz_lucnum_ui }
wrap! { fn neg(op) -> gmp::mpz_neg }
wrap! { fn com(op) -> gmp::mpz_com }
wrap! { fn abs(op) -> gmp::mpz_abs }
wrap! { fn fdiv_r_2exp(op; n: u32) -> gmp::mpz_fdiv_r_2exp }
wrap! { fn nextprime(op) -> gmp::mpz_nextprime }
wrap! { fn bin_ui(op; k: u32) -> gmp::mpz_bin_ui }

#[inline]
pub fn set_0(rop: &mut Integer) {
    unsafe {
        rop.inner_mut().size = 0;
    }
}

#[inline]
pub fn set_1(rop: &mut Integer) {
    unsafe {
        if rop.inner().alloc < 1 {
            gmp::_mpz_realloc(rop.as_raw_mut(), 1);
        }
        *limb_mut(rop, 0) = 1;
        rop.inner_mut().size = 1;
    }
}

#[inline]
pub fn set_m1(rop: &mut Integer) {
    unsafe {
        if rop.inner().alloc < 1 {
            gmp::_mpz_realloc(rop.as_raw_mut(), 1);
        }
        *limb_mut(rop, 0) = 1;
        rop.inner_mut().size = -1;
    }
}

#[inline]
pub fn set_nonzero(rop: &mut Integer, limb: gmp::limb_t) {
    unsafe {
        if rop.inner().alloc < 1 {
            gmp::_mpz_realloc(rop.as_raw_mut(), 1);
        }
        *limb_mut(rop, 0) = limb;
        rop.inner_mut().size = 1;
    }
}

#[inline]
pub unsafe fn mpz_set_0(rop: *mut mpz_t) {
    (*rop).size = 0;
}

#[inline]
pub unsafe fn mpz_set_1(rop: *mut mpz_t) {
    if (*rop).alloc < 1 {
        gmp::_mpz_realloc(rop, 1);
    }
    *mpz_limb_mut(rop, 0) = 1;
    (*rop).size = 1;
}

#[inline]
pub unsafe fn mpz_set_m1(rop: *mut mpz_t) {
    if (*rop).alloc < 1 {
        gmp::_mpz_realloc(rop, 1);
    }
    *mpz_limb_mut(rop, 0) = 1;
    (*rop).size = -1;
}

#[inline]
pub unsafe fn mpz_set_nonzero(rop: *mut mpz_t, limb: gmp::limb_t) {
    if (*rop).alloc < 1 {
        gmp::_mpz_realloc(rop, 1);
    }
    *mpz_limb_mut(rop, 0) = limb;
    (*rop).size = 1;
}

#[inline]
pub unsafe fn mpz_set_limb(rop: *mut mpz_t, limb: gmp::limb_t) {
    if limb == 0 {
        mpz_set_0(rop);
    } else {
        mpz_set_nonzero(rop, limb);
    }
}

#[inline]
pub unsafe fn mpz_tdiv_q_check(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_tdiv_q(q, n, d);
}

#[inline]
pub unsafe fn mpz_tdiv_r_check(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_tdiv_r(r, n, d);
}

#[inline]
pub unsafe fn mpz_tdiv_q_ui_check(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    assert_ne!(d, 0, "division by zero");
    gmp::mpz_tdiv_q_ui(q, n, d)
}

#[inline]
pub unsafe fn mpz_tdiv_r_ui_check(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    assert_ne!(d, 0, "division by zero");
    gmp::mpz_tdiv_r_ui(r, n, d)
}

pub unsafe fn mpz_ui_tdiv_q_check(
    q: *mut mpz_t,
    n: c_ulong,
    d: *const mpz_t,
) -> c_ulong {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(d, n) > 0 {
        // n / +abs_d -> 0, n
        // n / -abs_d -> 0, n
        mpz_set_0(q);
        n
    } else {
        // n / +abs_d -> +abs_q, +abs_r
        // n / -abs_d -> -abs_q, +abs_r
        let abs_d = gmp::mpz_get_ui(d);
        let (abs_q, abs_r) = (n / abs_d, n % abs_d);
        gmp::mpz_set_ui(q, abs_q);
        if sgn_d < 0 {
            gmp::mpz_neg(q, q);
        }
        abs_r
    }
}

pub unsafe fn mpz_ui_tdiv_r_check(
    r: *mut mpz_t,
    n: c_ulong,
    d: *const mpz_t,
) -> c_ulong {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(d, n) > 0 {
        // n / +abs_d -> 0, n
        // n / -abs_d -> 0, n
        gmp::mpz_set_ui(r, n);
        n
    } else {
        // n / +abs_d -> +abs_q, +abs_r
        // n / -abs_d -> -abs_q, +abs_r
        let abs_d = gmp::mpz_get_ui(d);
        let abs_r = n % abs_d;
        gmp::mpz_set_ui(r, abs_r);
        abs_r
    }
}

#[inline]
pub unsafe fn mpz_tdiv_q_si_check(q: *mut mpz_t, n: *const mpz_t, d: c_long) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    let (neg_d, abs_d) = d.neg_abs();
    mpz_tdiv_q_ui_check(q, n, abs_d);
    if neg_d {
        gmp::mpz_neg(q, q);
    }
}

#[inline]
pub unsafe fn mpz_tdiv_r_si_check(r: *mut mpz_t, n: *const mpz_t, d: c_long) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    mpz_tdiv_r_ui_check(r, n, d.neg_abs().1);
}

#[inline]
pub unsafe fn mpz_si_tdiv_q_check(q: *mut mpz_t, n: c_long, d: *const mpz_t) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    let (neg_n, abs_n) = n.neg_abs();
    mpz_ui_tdiv_q_check(q, abs_n, d);
    if neg_n {
        gmp::mpz_neg(q, q);
    }
}

#[inline]
pub unsafe fn mpz_si_tdiv_r_check(r: *mut mpz_t, n: c_long, d: *const mpz_t) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    let (neg_n, abs_n) = n.neg_abs();
    mpz_ui_tdiv_r_check(r, abs_n, d);
    if neg_n {
        gmp::mpz_neg(r, r);
    }
}

#[inline]
pub unsafe fn mpz_cdiv_q_check(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_cdiv_q(q, n, d);
}

#[inline]
pub unsafe fn mpz_cdiv_r_check(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_cdiv_r(r, n, d);
}

#[inline]
pub unsafe fn mpz_cdiv_q_ui_check(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    assert_ne!(d, 0, "division by zero");
    gmp::mpz_cdiv_q_ui(q, n, d)
}

#[inline]
pub unsafe fn mpz_cdiv_r_ui_check(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    assert_ne!(d, 0, "division by zero");
    gmp::mpz_cdiv_r_ui(r, n, d)
}

pub unsafe fn mpz_ui_cdiv_q_check(q: *mut mpz_t, n: c_ulong, d: *const mpz_t) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(d, n) > 0 {
        // n / +abs_d -> 0, n + if n > 0 { 1, -abs_d }
        // n / -abs_d -> 0, n
        if n > 0 && sgn_d > 0 {
            mpz_set_1(q);
        } else {
            mpz_set_0(q);
        }
    } else {
        // n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
        // n / -abs_d -> -abs_q, +abs_r
        let abs_d = gmp::mpz_get_ui(d);
        let (mut abs_q, abs_r) = (n / abs_d, n % abs_d);
        if sgn_d < 0 {
            gmp::mpz_set_ui(q, abs_q);
            gmp::mpz_neg(q, q);
        } else {
            if abs_r > 0 {
                abs_q += 1;
            }
            gmp::mpz_set_ui(q, abs_q);
        }
    }
}

pub unsafe fn mpz_ui_cdiv_r_check(r: *mut mpz_t, n: c_ulong, d: *const mpz_t) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(d, n) > 0 {
        // n / +abs_d -> 0, n + if n > 0 { 1, -abs_d }
        // n / -abs_d -> 0, n
        if n > 0 && sgn_d > 0 {
            gmp::mpz_ui_sub(r, n, d);
        } else {
            gmp::mpz_set_ui(r, n);
        }
    } else {
        // n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
        // n / -abs_d -> -abs_q, +abs_r
        let abs_d = gmp::mpz_get_ui(d);
        let abs_r = n % abs_d;
        if sgn_d < 0 {
            gmp::mpz_set_ui(r, abs_r);
        } else if abs_r > 0 {
            gmp::mpz_set_ui(r, abs_d - abs_r);
            gmp::mpz_neg(r, r);
        } else {
            mpz_set_0(r);
        }
    }
}

#[inline]
pub unsafe fn mpz_cdiv_q_si_check(q: *mut mpz_t, n: *const mpz_t, d: c_long) {
    // +abs_n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r + if abs_r > 0 { 1, +abs_d }
    let (neg_d, abs_d) = d.neg_abs();
    let some_r = mpz_cdiv_q_ui_check(q, n, abs_d) != 0;
    if neg_d {
        if some_r {
            gmp::mpz_ui_sub(q, 1, q);
        } else {
            gmp::mpz_neg(q, q);
        }
    }
}

#[inline]
pub unsafe fn mpz_cdiv_r_si_check(r: *mut mpz_t, n: *const mpz_t, d: c_long) {
    // +abs_n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r + if abs_r > 0 { 1, +abs_d }
    let (neg_d, abs_d) = d.neg_abs();
    let some_r = mpz_cdiv_r_ui_check(r, n, abs_d) != 0;
    if neg_d && some_r {
        mpz_sub_si(r, r, d);
    }
}

pub unsafe fn mpz_si_cdiv_q_check(q: *mut mpz_t, n: c_long, d: *const mpz_t) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    let (neg_n, abs_n) = n.neg_abs();
    if gmp::mpz_cmpabs_ui(d, abs_n) > 0 {
        // +abs_n / +abs_d -> 0, +abs_n + if abs_n > 0 { 1, -abs_d }
        // +abs_n / -abs_d -> 0, +abs_n
        // -abs_n / +abs_d -> 0, -abs_n
        // -abs_n / -abs_d -> 0, -abs_n + if abs_n > 0 { 1, +abs_d }
        if (n > 0 && sgn_d > 0) || (neg_n && sgn_d < 0) {
            mpz_set_1(q);
        } else {
            mpz_set_0(q);
        }
    } else {
        // +abs_n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
        // +abs_n / -abs_d -> -abs_q, +abs_r
        // -abs_n / +abs_d -> -abs_q, -abs_r
        // -abs_n / -abs_d -> +abs_q, -abs_r + if abs_r > 0 { 1, +abs_d }
        let abs_d = gmp::mpz_get_ui(d);
        let (mut abs_q, abs_r) = (abs_n / abs_d, abs_n % abs_d);
        if (n > 0 && sgn_d < 0) || (neg_n && sgn_d > 0) {
            gmp::mpz_set_ui(q, abs_q);
            gmp::mpz_neg(q, q);
        } else {
            if abs_r > 0 {
                abs_q += 1;
            }
            gmp::mpz_set_ui(q, abs_q);
        }
    }
}

pub unsafe fn mpz_si_cdiv_r_check(r: *mut mpz_t, n: c_long, d: *const mpz_t) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    let (neg_n, abs_n) = n.neg_abs();
    if gmp::mpz_cmpabs_ui(d, abs_n) > 0 {
        // +abs_n / +abs_d -> 0, +abs_n + if abs_n > 0 { 1, -abs_d }
        // +abs_n / -abs_d -> 0, +abs_n
        // -abs_n / +abs_d -> 0, -abs_n
        // -abs_n / -abs_d -> 0, -abs_n + if abs_n > 0 { 1, +abs_d }
        if (n > 0 && sgn_d > 0) || (neg_n && sgn_d < 0) {
            mpz_si_sub(r, n, d);
        } else {
            gmp::mpz_set_si(r, n);
        }
    } else {
        // +abs_n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
        // +abs_n / -abs_d -> -abs_q, +abs_r
        // -abs_n / +abs_d -> -abs_q, -abs_r
        // -abs_n / -abs_d -> +abs_q, -abs_r + if abs_r > 0 { 1, +abs_d }
        let abs_d = gmp::mpz_get_ui(d);
        let abs_r = abs_n % abs_d;
        if n > 0 && sgn_d < 0 {
            gmp::mpz_set_ui(r, abs_r);
        } else if neg_n && sgn_d > 0 {
            gmp::mpz_set_ui(r, abs_r);
            gmp::mpz_neg(r, r);
        } else if abs_r > 0 {
            gmp::mpz_set_ui(r, abs_d - abs_r);
            if sgn_d > 0 {
                gmp::mpz_neg(r, r);
            }
        } else {
            mpz_set_0(r);
        }
    }
}

#[inline]
pub unsafe fn mpz_fdiv_q_check(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_fdiv_q(q, n, d);
}

#[inline]
pub unsafe fn mpz_fdiv_r_check(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_fdiv_r(r, n, d);
}

#[inline]
pub unsafe fn mpz_fdiv_q_ui_check(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    assert_ne!(d, 0, "division by zero");
    gmp::mpz_fdiv_q_ui(q, n, d)
}

#[inline]
pub unsafe fn mpz_fdiv_r_ui_check(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    assert_ne!(d, 0, "division by zero");
    gmp::mpz_fdiv_r_ui(r, n, d)
}

pub unsafe fn mpz_ui_fdiv_q_check(q: *mut mpz_t, n: c_ulong, d: *const mpz_t) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(d, n) > 0 {
        // n / +abs_d -> 0, n
        // n / -abs_d -> 0, n + if n > 0 { -1, -abs_d }
        if n > 0 && sgn_d < 0 {
            mpz_set_m1(q);
        } else {
            mpz_set_0(q);
        }
    } else {
        // n / +abs_d -> +abs_q, +abs_r
        // n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
        let abs_d = gmp::mpz_get_ui(d);
        let (mut abs_q, abs_r) = (n / abs_d, n % abs_d);
        if sgn_d > 0 {
            gmp::mpz_set_ui(q, abs_q);
        } else {
            if abs_r > 0 {
                abs_q += 1;
            }
            gmp::mpz_set_ui(q, abs_q);
            gmp::mpz_neg(q, q);
        }
    }
}

pub unsafe fn mpz_ui_fdiv_r_check(r: *mut mpz_t, n: c_ulong, d: *const mpz_t) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(d, n) > 0 {
        // n / +abs_d -> 0, n
        // n / -abs_d -> 0, n + if n > 0 { -1, -abs_d }
        if n > 0 && sgn_d < 0 {
            gmp::mpz_add_ui(r, d, n);
        } else {
            gmp::mpz_set_ui(r, n);
        }
    } else {
        // n / +abs_d -> +abs_q, +abs_r
        // n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
        let abs_d = gmp::mpz_get_ui(d);
        let abs_r = n % abs_d;
        if sgn_d > 0 {
            gmp::mpz_set_ui(r, abs_r);
        } else if abs_r > 0 {
            gmp::mpz_set_ui(r, abs_d - abs_r);
            gmp::mpz_neg(r, r);
        } else {
            mpz_set_0(r);
        }
    }
}

#[inline]
pub unsafe fn mpz_fdiv_q_si_check(q: *mut mpz_t, n: *const mpz_t, d: c_long) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
    // -abs_n / +abs_d -> -abs_q, -abs_r + if abs_r > 0 { -1, +abs_d }
    // -abs_n / -abs_d -> +abs_q, -abs_r
    let (neg_d, abs_d) = d.neg_abs();
    let some_r = mpz_fdiv_q_ui_check(q, n, abs_d) != 0;
    if neg_d {
        if some_r {
            mpz_si_sub(q, -1, q);
        } else {
            gmp::mpz_neg(q, q);
        }
    }
}

#[inline]
pub unsafe fn mpz_fdiv_r_si_check(r: *mut mpz_t, n: *const mpz_t, d: c_long) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
    // -abs_n / +abs_d -> -abs_q, -abs_r + if abs_r > 0 { -1, +abs_d }
    // -abs_n / -abs_d -> +abs_q, -abs_r
    let (neg_d, abs_d) = d.neg_abs();
    let some_r = mpz_fdiv_r_ui_check(r, n, abs_d) != 0;
    if neg_d && some_r {
        mpz_add_si(r, r, d);
    }
}

pub unsafe fn mpz_si_fdiv_q_check(q: *mut mpz_t, n: c_long, d: *const mpz_t) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    let (neg_n, abs_n) = n.neg_abs();
    if gmp::mpz_cmpabs_ui(d, abs_n) > 0 {
        // +abs_n / +abs_d -> 0, +abs_n
        // +abs_n / -abs_d -> 0, +abs_n + if abs_n > 0 { -1, -abs_d }
        // -abs_n / +abs_d -> 0, -abs_n + if abs_n > 0 { -1, +abs_d }
        // -abs_n / -abs_d -> 0, -abs_n
        if (n > 0 && sgn_d < 0) || (neg_n && sgn_d > 0) {
            mpz_set_m1(q);
        } else {
            mpz_set_0(q);
        }
    } else {
        // +abs_n / +abs_d -> +abs_q, +abs_r
        // +abs_n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
        // -abs_n / +abs_d -> -abs_q, -abs_r + if abs_r > 0 { -1, +abs_d }
        // -abs_n / -abs_d -> +abs_q, -abs_r
        let abs_d = gmp::mpz_get_ui(d);
        let (mut abs_q, abs_r) = (abs_n / abs_d, abs_n % abs_d);
        if (n > 0 && sgn_d > 0) || (neg_n && sgn_d < 0) {
            gmp::mpz_set_ui(q, abs_q);
        } else {
            if abs_r > 0 {
                abs_q += 1;
            }
            gmp::mpz_set_ui(q, abs_q);
            gmp::mpz_neg(q, q);
        }
    }
}

pub unsafe fn mpz_si_fdiv_r_check(r: *mut mpz_t, n: c_long, d: *const mpz_t) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    let (neg_n, abs_n) = n.neg_abs();
    if gmp::mpz_cmpabs_ui(d, abs_n) > 0 {
        // +abs_n / +abs_d -> 0, +abs_n
        // +abs_n / -abs_d -> 0, +abs_n + if abs_n > 0 { -1, -abs_d }
        // -abs_n / +abs_d -> 0, -abs_n + if abs_n > 0 { -1, +abs_d }
        // -abs_n / -abs_d -> 0, -abs_n
        if (n > 0 && sgn_d < 0) || (neg_n && sgn_d > 0) {
            mpz_add_si(r, d, n);
        } else {
            gmp::mpz_set_si(r, n);
        }
    } else {
        // +abs_n / +abs_d -> +abs_q, +abs_r
        // +abs_n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
        // -abs_n / +abs_d -> -abs_q, -abs_r + if abs_r > 0 { -1, +abs_d }
        // -abs_n / -abs_d -> +abs_q, -abs_r
        let abs_d = gmp::mpz_get_ui(d);
        let abs_r = abs_n % abs_d;
        if n > 0 && sgn_d > 0 {
            gmp::mpz_set_ui(r, abs_r);
        } else if neg_n && sgn_d < 0 {
            gmp::mpz_set_ui(r, abs_r);
            gmp::mpz_neg(r, r);
        } else if abs_r > 0 {
            gmp::mpz_set_ui(r, abs_d - abs_r);
            if sgn_d < 0 {
                gmp::mpz_neg(r, r);
            }
        } else {
            mpz_set_0(r);
        }
    }
}

#[inline]
pub unsafe fn mpz_ediv_q_check(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_cdiv_q_check(q, n, d);
    } else {
        mpz_fdiv_q_check(q, n, d);
    }
}

#[inline]
pub unsafe fn mpz_ediv_r_check(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_cdiv_r_check(r, n, d);
    } else {
        mpz_fdiv_r_check(r, n, d);
    }
}

#[inline]
pub unsafe fn mpz_ediv_q_ui_check(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    mpz_fdiv_q_ui_check(q, n, d)
}

#[inline]
pub unsafe fn mpz_ediv_r_ui_check(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    mpz_fdiv_r_ui_check(r, n, d)
}

#[inline]
pub unsafe fn mpz_ui_ediv_q_check(q: *mut mpz_t, n: c_ulong, d: *const mpz_t) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_ui_cdiv_q_check(q, n, d);
    } else {
        mpz_ui_fdiv_q_check(q, n, d);
    }
}

#[inline]
pub unsafe fn mpz_ui_ediv_r_check(r: *mut mpz_t, n: c_ulong, d: *const mpz_t) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_ui_cdiv_r_check(r, n, d);
    } else {
        mpz_ui_fdiv_r_check(r, n, d);
    }
}

#[inline]
pub unsafe fn mpz_ediv_q_si_check(q: *mut mpz_t, n: *const mpz_t, d: c_long) {
    if d < 0 {
        mpz_cdiv_q_si_check(q, n, d);
    } else {
        mpz_fdiv_q_si_check(q, n, d);
    }
}

#[inline]
pub unsafe fn mpz_ediv_r_si_check(r: *mut mpz_t, n: *const mpz_t, d: c_long) {
    if d < 0 {
        mpz_cdiv_r_si_check(r, n, d);
    } else {
        mpz_fdiv_r_si_check(r, n, d);
    }
}

#[inline]
pub unsafe fn mpz_si_ediv_q_check(q: *mut mpz_t, n: c_long, d: *const mpz_t) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_si_cdiv_q_check(q, n, d);
    } else {
        mpz_si_fdiv_q_check(q, n, d);
    }
}

#[inline]
pub unsafe fn mpz_si_ediv_r_check(r: *mut mpz_t, n: c_long, d: *const mpz_t) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_si_cdiv_r_check(r, n, d);
    } else {
        mpz_si_fdiv_r_check(r, n, d);
    }
}

#[inline]
pub unsafe fn mpz_add_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        gmp::mpz_add_ui(rop, op1, op2_abs);
    } else {
        gmp::mpz_sub_ui(rop, op1, op2_abs);
    }
}

#[inline]
pub unsafe fn mpz_sub_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        gmp::mpz_sub_ui(rop, op1, op2_abs);
    } else {
        gmp::mpz_add_ui(rop, op1, op2_abs);
    }
}

#[inline]
pub unsafe fn mpz_si_sub(rop: *mut mpz_t, op1: c_long, op2: *const mpz_t) {
    let (op1_neg, op1_abs) = op1.neg_abs();
    if !op1_neg {
        gmp::mpz_ui_sub(rop, op1_abs, op2);
    } else {
        gmp::mpz_neg(rop, op2);
        gmp::mpz_sub_ui(rop, rop, op1_abs);
    }
}

#[inline]
pub unsafe fn mpz_lshift_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        gmp::mpz_mul_2exp(rop, op1, op2_abs);
    } else {
        gmp::mpz_fdiv_q_2exp(rop, op1, op2_abs);
    }
}

#[inline]
pub unsafe fn mpz_rshift_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        gmp::mpz_fdiv_q_2exp(rop, op1, op2_abs);
    } else {
        gmp::mpz_mul_2exp(rop, op1, op2_abs);
    }
}

pub unsafe fn bitand_ui(rop: *mut mpz_t, op1: *const mpz_t, op2: c_ulong) {
    let lop2 = gmp::limb_t::from(op2);
    let ans_limb0 = match (*op1).size.cmp(&0) {
        Ordering::Equal => 0,
        Ordering::Greater => mpz_limb(op1, 0) & lop2,
        Ordering::Less => mpz_limb(op1, 0).wrapping_neg() & lop2,
    };
    if ans_limb0 == 0 {
        (*rop).size = 0;
    } else {
        mpz_set_nonzero(rop, ans_limb0);
    }
}

pub unsafe fn bitor_ui(rop: *mut mpz_t, op1: *const mpz_t, op2: c_ulong) {
    let lop2 = gmp::limb_t::from(op2);
    match (*op1).size.cmp(&0) {
        Ordering::Equal => {
            if op2 == 0 {
                (*rop).size = 0;
            } else {
                mpz_set_nonzero(rop, lop2);
            }
        }
        Ordering::Greater => {
            gmp::mpz_set(rop, op1);
            *mpz_limb_mut(rop, 0) |= lop2;
        }
        Ordering::Less => {
            gmp::mpz_com(rop, op1);
            if (*rop).size != 0 {
                *mpz_limb_mut(rop, 0) &= !lop2;
                if (*rop).size == 1 && mpz_limb(rop, 0) == 0 {
                    (*rop).size = 0;
                }
            }
            gmp::mpz_com(rop, rop);
        }
    }
}

pub unsafe fn bitxor_ui(rop: *mut mpz_t, op1: *const mpz_t, op2: c_ulong) {
    let lop2 = gmp::limb_t::from(op2);
    match (*op1).size.cmp(&0) {
        Ordering::Equal => {
            if op2 == 0 {
                (*rop).size = 0;
            } else {
                mpz_set_nonzero(rop, lop2);
            }
        }
        Ordering::Greater => {
            gmp::mpz_set(rop, op1);
            *mpz_limb_mut(rop, 0) ^= lop2;
            if (*rop).size == 1 && mpz_limb(rop, 0) == 0 {
                (*rop).size = 0;
            }
        }
        Ordering::Less => {
            gmp::mpz_com(rop, op1);
            if (*rop).size == 0 {
                if lop2 != 0 {
                    mpz_set_nonzero(rop, lop2);
                }
            } else {
                *mpz_limb_mut(rop, 0) ^= lop2;
                if (*rop).size == 1 && mpz_limb(rop, 0) == 0 {
                    (*rop).size = 0;
                }
            }
            gmp::mpz_com(rop, rop);
        }
    }
}

pub unsafe fn bitand_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    let lop2 = if op2 >= 0 {
        gmp::limb_t::from(op2 as c_ulong)
    } else {
        !gmp::limb_t::from(!op2 as c_ulong)
    };
    match (*op1).size.cmp(&0) {
        Ordering::Equal => {
            (*rop).size = 0;
        }
        Ordering::Greater => {
            if op2 >= 0 {
                mpz_set_limb(rop, mpz_limb(op1, 0) & lop2);
            } else {
                gmp::mpz_set(rop, op1);
                *mpz_limb_mut(rop, 0) &= lop2;
                if (*rop).size == 1 && mpz_limb(rop, 0) == 0 {
                    (*rop).size = 0;
                }
            }
        }
        Ordering::Less => {
            if op2 >= 0 {
                mpz_set_limb(rop, mpz_limb(op1, 0).wrapping_neg() & lop2);
            } else {
                gmp::mpz_com(rop, op1);
                if (*rop).size == 0 {
                    if !lop2 != 0 {
                        mpz_set_nonzero(rop, !lop2);
                    }
                } else {
                    *mpz_limb_mut(rop, 0) |= !lop2;
                }
                gmp::mpz_com(rop, rop);
            }
        }
    }
}

pub unsafe fn bitor_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    let lop2 = if op2 >= 0 {
        gmp::limb_t::from(op2 as c_ulong)
    } else {
        !gmp::limb_t::from(!op2 as c_ulong)
    };
    match (*op1).size.cmp(&0) {
        Ordering::Equal => {
            gmp::mpz_set_si(rop, op2);
        }
        Ordering::Greater => {
            if op2 >= 0 {
                gmp::mpz_set(rop, op1);
                *mpz_limb_mut(rop, 0) |= lop2;
            } else {
                mpz_set_limb(rop, !mpz_limb(op1, 0) & !lop2);
                gmp::mpz_com(rop, rop);
            }
        }
        Ordering::Less => {
            if op2 >= 0 {
                gmp::mpz_com(rop, op1);
                if (*rop).size != 0 {
                    *mpz_limb_mut(rop, 0) &= !lop2;
                    if (*rop).size == 1 && mpz_limb(rop, 0) == 0 {
                        (*rop).size = 0;
                    }
                }
                gmp::mpz_com(rop, rop);
            } else {
                mpz_set_limb(rop, mpz_limb(op1, 0).wrapping_sub(1) & !lop2);
                gmp::mpz_com(rop, rop);
            }
        }
    }
}

pub unsafe fn bitxor_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    let lop2 = if op2 >= 0 {
        gmp::limb_t::from(op2 as c_ulong)
    } else {
        !gmp::limb_t::from(!op2 as c_ulong)
    };
    match (*op1).size.cmp(&0) {
        Ordering::Equal => {
            gmp::mpz_set_si(rop, op2);
        }
        Ordering::Greater => {
            if op2 >= 0 {
                gmp::mpz_set(rop, op1);
                *mpz_limb_mut(rop, 0) ^= lop2;
                if (*rop).size == 1 && mpz_limb(rop, 0) == 0 {
                    (*rop).size = 0;
                }
            } else {
                gmp::mpz_set(rop, op1);
                *mpz_limb_mut(rop, 0) ^= !lop2;
                if (*rop).size == 1 && mpz_limb(rop, 0) == 0 {
                    (*rop).size = 0;
                }
                gmp::mpz_com(rop, rop);
            }
        }
        Ordering::Less => {
            if op2 >= 0 {
                gmp::mpz_com(rop, op1);
                if (*rop).size == 0 {
                    if lop2 != 0 {
                        mpz_set_nonzero(rop, lop2);
                    }
                } else {
                    *mpz_limb_mut(rop, 0) ^= lop2;
                    if (*rop).size == 1 && mpz_limb(rop, 0) == 0 {
                        (*rop).size = 0;
                    }
                }
                gmp::mpz_com(rop, rop);
            } else {
                gmp::mpz_com(rop, op1);
                if (*rop).size == 0 {
                    if !lop2 != 0 {
                        mpz_set_nonzero(rop, !lop2);
                    }
                } else {
                    *mpz_limb_mut(rop, 0) ^= !lop2;
                    if (*rop).size == 1 && mpz_limb(rop, 0) == 0 {
                        (*rop).size = 0;
                    }
                }
            }
        }
    }
}

#[cfg(int_128)]
#[inline]
pub fn set_i128(rop: &mut Integer, i: i128) {
    let (neg_i, abs_i) = i.neg_abs();
    set_u128(rop, abs_i);
    if neg_i {
        rop.neg_assign();
    }
}

#[inline]
pub fn set_i64(rop: &mut Integer, i: i64) {
    let (neg_i, abs_i) = i.neg_abs();
    set_u64(rop, abs_i);
    if neg_i {
        rop.neg_assign();
    }
}

#[inline]
pub fn set_i32(rop: &mut Integer, i: i32) {
    let (neg_i, abs_i) = i.neg_abs();
    set_u32(rop, abs_i);
    if neg_i {
        rop.neg_assign();
    }
}

#[cfg(int_128)]
#[inline]
pub fn init_set_u128(rop: &mut Integer, u: u128) {
    unsafe {
        gmp::mpz_init2(rop.as_raw_mut(), 128);
    }
    set_u128(rop, u);
}

#[cfg(int_128)]
#[inline]
pub fn init_set_i128(rop: &mut Integer, i: i128) {
    unsafe {
        gmp::mpz_init2(rop.as_raw_mut(), 128);
    }
    set_i128(rop, i);
}

#[inline]
pub fn init_set_u32(rop: &mut Integer, u: u32) {
    unsafe {
        gmp::mpz_init_set_ui(rop.as_raw_mut(), u.into());
    }
}

#[inline]
pub fn init_set_i32(rop: &mut Integer, i: i32) {
    unsafe {
        gmp::mpz_init_set_si(rop.as_raw_mut(), i.into());
    }
}

#[inline]
pub fn fits_u8(op: &Integer) -> bool {
    match op.inner().size {
        0 => true,
        1 => (unsafe { limb(op, 0) }) <= gmp::limb_t::from(u8::MAX),
        _ => false,
    }
}

#[inline]
pub fn fits_i8(op: &Integer) -> bool {
    match op.inner().size {
        0 => true,
        1 => (unsafe { limb(op, 0) }) <= gmp::limb_t::from(i8::MAX as u8),
        -1 => (unsafe { limb(op, 0) }) <= gmp::limb_t::from(i8::MIN as u8),
        _ => false,
    }
}

#[inline]
pub fn fits_u16(op: &Integer) -> bool {
    match op.inner().size {
        0 => true,
        1 => (unsafe { limb(op, 0) }) <= gmp::limb_t::from(u16::MAX),
        _ => false,
    }
}

#[inline]
pub fn fits_i16(op: &Integer) -> bool {
    match op.inner().size {
        0 => true,
        1 => (unsafe { limb(op, 0) }) <= gmp::limb_t::from(i16::MAX as u16),
        -1 => (unsafe { limb(op, 0) }) <= gmp::limb_t::from(i16::MIN as u16),
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_addmul_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        gmp::mpz_addmul_ui(rop, op1, op2_abs);
    } else {
        gmp::mpz_submul_ui(rop, op1, op2_abs);
    }
}

#[inline]
pub unsafe fn mpz_submul_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        gmp::mpz_submul_ui(rop, op1, op2_abs);
    } else {
        gmp::mpz_addmul_ui(rop, op1, op2_abs);
    }
}

// rop = op1 * op2 - rop
#[inline]
pub unsafe fn mpz_mulsub(
    rop: *mut mpz_t,
    op1: *const mpz_t,
    op2: *const mpz_t,
) {
    gmp::mpz_submul(rop, op1, op2);
    (*rop).size = -(*rop).size;
}

#[inline]
pub unsafe fn mpz_mulsub_ui(rop: *mut mpz_t, op1: *const mpz_t, op2: c_ulong) {
    gmp::mpz_submul_ui(rop, op1, op2);
    (*rop).size = -(*rop).size;
}

#[inline]
pub unsafe fn mpz_mulsub_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    mpz_submul_si(rop, op1, op2);
    (*rop).size = -(*rop).size;
}

#[inline]
pub unsafe fn mpz_zerocount(op: *const mpz_t) -> gmp::bitcnt_t {
    if (*op).size >= 0 {
        c_ulong::max_value()
    } else {
        let size = gmp::size_t::from((*op).size);
        let abs_size = size.wrapping_neg();
        let abs_popcount = gmp::mpn_popcount((*op).d, abs_size);
        let first_one = gmp::mpn_scan1((*op).d, 0);
        abs_popcount + first_one - 1
    }
}

#[inline]
pub unsafe fn mpz_significant_bits(op: *const mpz_t) -> gmp::bitcnt_t {
    let size = (*op).size;
    if size == 0 {
        return 0;
    }
    let size = size.neg_abs().1;
    let size_in_base = gmp::mpn_sizeinbase((*op).d, cast::cast(size), 2);
    cast::cast(size_in_base)
}

#[inline]
pub fn significant_bits(op: &Integer) -> usize {
    let size = op.inner().size;
    if size == 0 {
        return 0;
    }
    let size = size.neg_abs().1;
    unsafe { gmp::mpn_sizeinbase(op.inner().d, cast::cast(size), 2) }
}

pub unsafe fn mpz_signed_bits(op: *const mpz_t) -> gmp::bitcnt_t {
    let size = (*op).size;
    let significant = mpz_significant_bits(op);
    if size < 0 {
        let first_one = gmp::mpn_scan1((*op).d, 0);
        if first_one == significant - 1 {
            return significant;
        }
    }
    significant.checked_add(1).expect("overflow")
}

pub unsafe fn mpz_is_pow_of_two(op: *const mpz_t) -> bool {
    let size = (*op).size;
    if size <= 0 {
        return false;
    }
    let significant = mpz_significant_bits(op);
    let first_one = gmp::mpn_scan1((*op).d, 0);
    first_one == significant - 1
}

#[inline]
pub unsafe fn limb(z: &Integer, index: isize) -> gmp::limb_t {
    *z.inner().d.offset(index)
}

#[inline]
pub unsafe fn limb_mut(z: &mut Integer, index: isize) -> &mut gmp::limb_t {
    &mut *z.inner_mut().d.offset(index)
}

#[inline]
pub unsafe fn mpz_limb(z: *const mpz_t, index: isize) -> gmp::limb_t {
    *(*z).d.offset(index)
}

#[inline]
pub unsafe fn mpz_limb_mut(z: *const mpz_t, index: isize) -> *mut gmp::limb_t {
    (*z).d.offset(index)
}

#[inline]
pub fn ord_int(o: Ordering) -> c_int {
    match o {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}

#[cfg_attr(feature = "cargo-clippy", allow(clippy::cast_lossless))]
pub unsafe fn realloc_for_mpn_set_str(rop: *mut mpz_t, len: usize, radix: i32) {
    // add 1 for possible rounding errors
    let bits = (f64::from(radix).log2() * (len as f64)).ceil() + 1.0;
    // add 1 because mpn_set_str requires an extra limb
    let limbs = (bits / f64::from(gmp::LIMB_BITS)).ceil() + 1.0;
    gmp::_mpz_realloc(rop, cast::cast(limbs));
}

// dividend must not be zero
pub unsafe fn round_away(rem: *const mpz_t, dividend: *const mpz_t) -> bool {
    let s_rem = (*rem).size.checked_abs().expect("overflow");
    if s_rem == 0 {
        return false;
    }
    let s_dividend = (*dividend).size.checked_abs().expect("overflow");
    debug_assert!(s_dividend > 0);
    debug_assert!(s_rem <= s_dividend);
    if s_rem < s_dividend - 1 {
        return false;
    }

    let mut rem_limb = if s_rem == s_dividend {
        let rem_next_limb = mpz_limb(rem, cast::cast(s_rem - 1));
        if (rem_next_limb >> (gmp::LIMB_BITS - 1)) != 0 {
            return true;
        }
        rem_next_limb << 1
    } else {
        0
    };
    for i in (1..s_dividend).rev() {
        let div_limb = mpz_limb(dividend, cast::cast(i));
        let rem_next_limb = mpz_limb(rem, cast::cast(i - 1));
        rem_limb |= (rem_next_limb >> (gmp::LIMB_BITS - 1)) & 1;
        if rem_limb > div_limb {
            return true;
        }
        if rem_limb < div_limb {
            return false;
        }
        rem_limb = rem_next_limb << 1;
    }
    let div_limb = mpz_limb(dividend, 0);
    rem_limb >= div_limb
}
