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
use gmp_mpfr_sys::gmp;
use misc::NegAbs;
use ops::NegAssign;
use std::cmp::Ordering;
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
pub fn check_div0(divisor: &Integer) {
    assert_ne!(divisor.cmp0(), Ordering::Equal, "division by zero");
}

#[inline]
pub fn check_div0_or(divisor: Option<&Integer>, or: &Integer) {
    check_div0(divisor.unwrap_or(or));
}

#[inline]
pub fn set(rop: &mut Integer, op: Option<&Integer>) {
    if let Some(op) = op {
        unsafe {
            gmp::mpz_set(rop.as_raw_mut(), op.as_raw());
        }
    }
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

#[inline]
pub fn divexact(
    q: &mut Integer,
    dividend: Option<&Integer>,
    divisor: &Integer,
) {
    check_div0(divisor);
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

#[inline]
pub fn tdiv_qr(
    q: &mut Integer,
    r: &mut Integer,
    n: Option<&Integer>,
    d: Option<&Integer>,
) {
    check_div0_or(d, r);
    unsafe {
        gmp::mpz_tdiv_qr(
            q.as_raw_mut(),
            r.as_raw_mut(),
            n.unwrap_or(q).as_raw(),
            d.unwrap_or(r).as_raw(),
        );
    }
}

#[inline]
pub fn cdiv_qr(
    q: &mut Integer,
    r: &mut Integer,
    n: Option<&Integer>,
    d: Option<&Integer>,
) {
    check_div0_or(d, r);
    unsafe {
        gmp::mpz_cdiv_qr(
            q.as_raw_mut(),
            r.as_raw_mut(),
            n.unwrap_or(q).as_raw(),
            d.unwrap_or(r).as_raw(),
        );
    }
}

#[inline]
pub fn fdiv_qr(
    q: &mut Integer,
    r: &mut Integer,
    n: Option<&Integer>,
    d: Option<&Integer>,
) {
    check_div0_or(d, r);
    unsafe {
        gmp::mpz_fdiv_qr(
            q.as_raw_mut(),
            r.as_raw_mut(),
            n.unwrap_or(q).as_raw(),
            d.unwrap_or(r).as_raw(),
        );
    }
}

pub fn rdiv_qr(
    q: &mut Integer,
    r: &mut Integer,
    n: Option<&Integer>,
    d: Option<&Integer>,
) {
    // make sure d is not going to be aliased and overwritten
    let r_clone;
    let d = if let Some(d) = d {
        d
    } else {
        r_clone = r.clone();
        &r_clone
    };
    check_div0(d);
    tdiv_qr(q, r, n, Some(d));
    if round_away(r, d) {
        if (r.cmp0() == Ordering::Less) == (d.cmp0() == Ordering::Less) {
            // positive q
            add_u32(q, None, 1);
            sub(r, None, Some(d));
        } else {
            // negative q
            sub_u32(q, None, 1);
            add(r, None, Some(d));
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
    if d.unwrap_or(r).cmp0() == Ordering::Less {
        cdiv_qr(q, r, n, d)
    } else {
        fdiv_qr(q, r, n, d)
    }
}

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

#[inline]
pub fn tdiv_q(q: &mut Integer, n: Option<&Integer>, d: Option<&Integer>) {
    check_div0_or(d, q);
    unsafe {
        gmp::mpz_tdiv_q(
            q.as_raw_mut(),
            n.unwrap_or(q).as_raw(),
            d.unwrap_or(q).as_raw(),
        );
    }
}

#[inline]
pub fn tdiv_r(r: &mut Integer, n: Option<&Integer>, d: Option<&Integer>) {
    check_div0_or(d, r);
    unsafe {
        gmp::mpz_tdiv_r(
            r.as_raw_mut(),
            n.unwrap_or(r).as_raw(),
            d.unwrap_or(r).as_raw(),
        );
    }
}

#[inline]
pub fn cdiv_q(q: &mut Integer, n: Option<&Integer>, d: Option<&Integer>) {
    check_div0_or(d, q);
    unsafe {
        gmp::mpz_cdiv_q(
            q.as_raw_mut(),
            n.unwrap_or(q).as_raw(),
            d.unwrap_or(q).as_raw(),
        );
    }
}

#[inline]
pub fn cdiv_r(r: &mut Integer, n: Option<&Integer>, d: Option<&Integer>) {
    check_div0_or(d, r);
    unsafe {
        gmp::mpz_cdiv_r(
            r.as_raw_mut(),
            n.unwrap_or(r).as_raw(),
            d.unwrap_or(r).as_raw(),
        );
    }
}

#[inline]
pub fn fdiv_q(q: &mut Integer, n: Option<&Integer>, d: Option<&Integer>) {
    check_div0_or(d, q);
    unsafe {
        gmp::mpz_fdiv_q(
            q.as_raw_mut(),
            n.unwrap_or(q).as_raw(),
            d.unwrap_or(q).as_raw(),
        );
    }
}

#[inline]
pub fn fdiv_r(r: &mut Integer, n: Option<&Integer>, d: Option<&Integer>) {
    check_div0_or(d, r);
    unsafe {
        gmp::mpz_fdiv_r(
            r.as_raw_mut(),
            n.unwrap_or(r).as_raw(),
            d.unwrap_or(r).as_raw(),
        );
    }
}

#[inline]
pub fn ediv_q(q: &mut Integer, n: Option<&Integer>, d: Option<&Integer>) {
    if d.unwrap_or(q).cmp0() == Ordering::Less {
        cdiv_q(q, n, d)
    } else {
        fdiv_q(q, n, d)
    }
}

#[inline]
pub fn ediv_r(r: &mut Integer, n: Option<&Integer>, d: Option<&Integer>) {
    if d.unwrap_or(r).cmp0() == Ordering::Less {
        cdiv_r(r, n, d)
    } else {
        fdiv_r(r, n, d)
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
wrap! { fn add(op1, op2) -> gmp::mpz_add }
wrap! { fn sub(op1, op2) -> gmp::mpz_sub }
wrap! { fn mul(op1, op2) -> gmp::mpz_mul }
wrap! { fn and(op1, op2) -> gmp::mpz_and }
wrap! { fn ior(op1, op2) -> gmp::mpz_ior }
wrap! { fn xor(op1, op2) -> gmp::mpz_xor }
wrap! { fn mul_i32(op1; op2: i32) -> gmp::mpz_mul_si }
wrap! { fn add_u32(op1; op2: u32) -> gmp::mpz_add_ui }
wrap! { fn sub_u32(op1; op2: u32) -> gmp::mpz_sub_ui }
wrap! { fn mul_u32(op1; op2: u32) -> gmp::mpz_mul_ui }
wrap! { fn mul_2exp(op1; op2: u32) -> gmp::mpz_mul_2exp }
wrap! { fn fdiv_q_2exp(op1; op2: u32) -> gmp::mpz_fdiv_q_2exp }
wrap! { fn pow_u32(op1; op2: u32) -> gmp::mpz_pow_ui }
wrap! { fn abs(op) -> gmp::mpz_abs }
wrap! { fn fdiv_r_2exp(op; n: u32) -> gmp::mpz_fdiv_r_2exp }
wrap! { fn nextprime(op) -> gmp::mpz_nextprime }
wrap! { fn bin_ui(op; k: u32) -> gmp::mpz_bin_ui }

#[inline]
pub fn is_1(op: &Integer) -> bool {
    op.inner().size == 1 && unsafe { limb(op, 0) == 1 }
}

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
pub fn set_limb(rop: &mut Integer, limb: gmp::limb_t) {
    if limb == 0 {
        set_0(rop);
    } else {
        set_nonzero(rop, limb);
    }
}

#[inline]
pub fn tdiv_q_u32(q: &mut Integer, n: Option<&Integer>, d: u32) {
    assert_ne!(d, 0, "division by zero");
    unsafe {
        gmp::mpz_tdiv_q_ui(q.as_raw_mut(), n.unwrap_or(q).as_raw(), d.into());
    }
}

#[inline]
pub fn tdiv_r_u32(r: &mut Integer, n: Option<&Integer>, d: u32) {
    assert_ne!(d, 0, "division by zero");
    unsafe {
        gmp::mpz_tdiv_r_ui(r.as_raw_mut(), n.unwrap_or(r).as_raw(), d.into());
    }
}

pub fn u32_tdiv_q(q: &mut Integer, n: u32, d: Option<&Integer>) {
    check_div0_or(d, q);
    let n = n.into();
    let neg_d = d.unwrap_or(q).cmp0() == Ordering::Less;
    let d_ptr = d.unwrap_or(q).as_raw();
    let abs_d_greater_n = unsafe { gmp::mpz_cmpabs_ui(d_ptr, n) > 0 };
    if abs_d_greater_n {
        // n / +abs_d -> 0, n
        // n / -abs_d -> 0, n
        set_0(q);
    } else {
        // n / +abs_d -> +abs_q, +abs_r
        // n / -abs_d -> -abs_q, +abs_r
        let abs_d = unsafe { gmp::mpz_get_ui(d_ptr) };
        let abs_q = n / abs_d;
        unsafe {
            gmp::mpz_set_ui(q.as_raw_mut(), abs_q);
        }
        if neg_d {
            neg(q, None);
        }
    }
}

pub fn u32_tdiv_r(r: &mut Integer, n: u32, d: Option<&Integer>) {
    check_div0_or(d, r);
    let n = n.into();
    let d_ptr = d.unwrap_or(r).as_raw();
    let abs_d_greater_n = unsafe { gmp::mpz_cmpabs_ui(d_ptr, n) > 0 };
    if abs_d_greater_n {
        // n / +abs_d -> 0, n
        // n / -abs_d -> 0, n
        unsafe {
            gmp::mpz_set_ui(r.as_raw_mut(), n);
        }
    } else {
        // n / +abs_d -> +abs_q, +abs_r
        // n / -abs_d -> -abs_q, +abs_r
        let abs_d = unsafe { gmp::mpz_get_ui(d_ptr) };
        let abs_r = n % abs_d;
        unsafe {
            gmp::mpz_set_ui(r.as_raw_mut(), abs_r);
        }
    }
}

#[inline]
pub fn tdiv_q_i32(q: &mut Integer, n: Option<&Integer>, d: i32) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    let (neg_d, abs_d) = d.neg_abs();
    tdiv_q_u32(q, n, abs_d);
    if neg_d {
        neg(q, None);
    }
}

#[inline]
pub fn tdiv_r_i32(r: &mut Integer, n: Option<&Integer>, d: i32) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    tdiv_r_u32(r, n, d.neg_abs().1);
}

#[inline]
pub fn i32_tdiv_q(q: &mut Integer, n: i32, d: Option<&Integer>) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    let (neg_n, abs_n) = n.neg_abs();
    u32_tdiv_q(q, abs_n, d);
    if neg_n {
        neg(q, None);
    }
}

#[inline]
pub fn i32_tdiv_r(r: &mut Integer, n: i32, d: Option<&Integer>) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    let (neg_n, abs_n) = n.neg_abs();
    u32_tdiv_r(r, abs_n, d);
    if neg_n {
        neg(r, None);
    }
}

#[inline]
pub fn cdiv_q_u32(q: &mut Integer, n: Option<&Integer>, d: u32) -> bool {
    assert_ne!(d, 0, "division by zero");
    (unsafe {
        gmp::mpz_cdiv_q_ui(q.as_raw_mut(), n.unwrap_or(q).as_raw(), d.into())
    }) != 0
}

#[inline]
pub fn cdiv_r_u32(r: &mut Integer, n: Option<&Integer>, d: u32) -> bool {
    assert_ne!(d, 0, "division by zero");
    (unsafe {
        gmp::mpz_cdiv_r_ui(r.as_raw_mut(), n.unwrap_or(r).as_raw(), d.into())
    }) != 0
}

pub fn u32_cdiv_q(q: &mut Integer, n: u32, d: Option<&Integer>) {
    check_div0_or(d, q);
    let n = n.into();
    let neg_d = d.unwrap_or(q).cmp0() == Ordering::Less;
    let d_ptr = d.unwrap_or(q).as_raw();
    let abs_d_greater_n = unsafe { gmp::mpz_cmpabs_ui(d_ptr, n) > 0 };
    if abs_d_greater_n {
        // n / +abs_d -> 0, n + if n > 0 { 1, -abs_d }
        // n / -abs_d -> 0, n
        if n > 0 && !neg_d {
            set_1(q);
        } else {
            set_0(q);
        }
    } else {
        // n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
        // n / -abs_d -> -abs_q, +abs_r
        let abs_d = unsafe { gmp::mpz_get_ui(d_ptr) };
        let (mut abs_q, abs_r) = (n / abs_d, n % abs_d);
        if neg_d {
            unsafe {
                gmp::mpz_set_ui(q.as_raw_mut(), abs_q);
            }
            neg(q, None);
        } else {
            if abs_r > 0 {
                abs_q += 1;
            }
            unsafe {
                gmp::mpz_set_ui(q.as_raw_mut(), abs_q);
            }
        }
    }
}

pub fn u32_cdiv_r(r: &mut Integer, n: u32, d: Option<&Integer>) {
    check_div0_or(d, r);
    let n = n.into();
    let neg_d = d.unwrap_or(r).cmp0() == Ordering::Less;
    let d_ptr = d.unwrap_or(r).as_raw();
    let abs_d_greater_n = unsafe { gmp::mpz_cmpabs_ui(d_ptr, n) > 0 };
    if abs_d_greater_n {
        // n / +abs_d -> 0, n + if n > 0 { 1, -abs_d }
        // n / -abs_d -> 0, n
        if n > 0 && !neg_d {
            unsafe {
                gmp::mpz_ui_sub(r.as_raw_mut(), n, d_ptr);
            }
        } else {
            unsafe {
                gmp::mpz_set_ui(r.as_raw_mut(), n);
            }
        }
    } else {
        // n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
        // n / -abs_d -> -abs_q, +abs_r
        let abs_d = unsafe { gmp::mpz_get_ui(d_ptr) };
        let abs_r = n % abs_d;
        if neg_d {
            unsafe {
                gmp::mpz_set_ui(r.as_raw_mut(), abs_r);
            }
        } else if abs_r > 0 {
            unsafe {
                gmp::mpz_set_ui(r.as_raw_mut(), abs_d - abs_r);
            }
            neg(r, None);
        } else {
            set_0(r);
        }
    }
}

#[inline]
pub fn cdiv_q_i32(q: &mut Integer, n: Option<&Integer>, d: i32) {
    // +abs_n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r + if abs_r > 0 { 1, +abs_d }
    let (neg_d, abs_d) = d.neg_abs();
    let some_r = cdiv_q_u32(q, n, abs_d);
    if neg_d {
        if some_r {
            unsafe {
                gmp::mpz_ui_sub(q.as_raw_mut(), 1, q.as_raw());
            }
        } else {
            neg(q, None);
        }
    }
}

#[inline]
pub fn cdiv_r_i32(r: &mut Integer, n: Option<&Integer>, d: i32) {
    // +abs_n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r + if abs_r > 0 { 1, +abs_d }
    let (neg_d, abs_d) = d.neg_abs();
    let some_r = cdiv_r_u32(r, n, abs_d);
    if neg_d && some_r {
        sub_i32(r, None, d);
    }
}

pub fn i32_cdiv_q(q: &mut Integer, n: i32, d: Option<&Integer>) {
    check_div0_or(d, q);
    let (neg_n, abs_n) = n.neg_abs();
    let abs_n = abs_n.into();
    let neg_d = d.unwrap_or(q).cmp0() == Ordering::Less;
    let d_ptr = d.unwrap_or(q).as_raw();
    let abs_d_greater_abs_n = unsafe { gmp::mpz_cmpabs_ui(d_ptr, abs_n) > 0 };
    if abs_d_greater_abs_n {
        // +abs_n / +abs_d -> 0, +abs_n + if abs_n > 0 { 1, -abs_d }
        // +abs_n / -abs_d -> 0, +abs_n
        // -abs_n / +abs_d -> 0, -abs_n
        // -abs_n / -abs_d -> 0, -abs_n + if abs_n > 0 { 1, +abs_d }
        if (n > 0 && !neg_d) || (neg_n && neg_d) {
            set_1(q);
        } else {
            set_0(q);
        }
    } else {
        // +abs_n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
        // +abs_n / -abs_d -> -abs_q, +abs_r
        // -abs_n / +abs_d -> -abs_q, -abs_r
        // -abs_n / -abs_d -> +abs_q, -abs_r + if abs_r > 0 { 1, +abs_d }
        let abs_d = unsafe { gmp::mpz_get_ui(d_ptr) };
        let (mut abs_q, abs_r) = (abs_n / abs_d, abs_n % abs_d);
        if (n > 0 && neg_d) || (neg_n && !neg_d) {
            unsafe {
                gmp::mpz_set_ui(q.as_raw_mut(), abs_q);
            }
            neg(q, None);
        } else {
            if abs_r > 0 {
                abs_q += 1;
            }
            unsafe {
                gmp::mpz_set_ui(q.as_raw_mut(), abs_q);
            }
        }
    }
}

pub fn i32_cdiv_r(r: &mut Integer, n: i32, d: Option<&Integer>) {
    check_div0_or(d, r);
    let (neg_n, abs_n) = n.neg_abs();
    let abs_n = abs_n.into();
    let neg_d = d.unwrap_or(r).cmp0() == Ordering::Less;
    let d_ptr = d.unwrap_or(r).as_raw();
    let abs_d_greater_abs_n = unsafe { gmp::mpz_cmpabs_ui(d_ptr, abs_n) > 0 };
    if abs_d_greater_abs_n {
        // +abs_n / +abs_d -> 0, +abs_n + if abs_n > 0 { 1, -abs_d }
        // +abs_n / -abs_d -> 0, +abs_n
        // -abs_n / +abs_d -> 0, -abs_n
        // -abs_n / -abs_d -> 0, -abs_n + if abs_n > 0 { 1, +abs_d }
        if (n > 0 && !neg_d) || (neg_n && neg_d) {
            i32_sub(r, n, d);
        } else {
            set_i32(r, n);
        }
    } else {
        // +abs_n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
        // +abs_n / -abs_d -> -abs_q, +abs_r
        // -abs_n / +abs_d -> -abs_q, -abs_r
        // -abs_n / -abs_d -> +abs_q, -abs_r + if abs_r > 0 { 1, +abs_d }
        let abs_d = unsafe { gmp::mpz_get_ui(d_ptr) };
        let abs_r = abs_n % abs_d;
        if n > 0 && neg_d {
            unsafe {
                gmp::mpz_set_ui(r.as_raw_mut(), abs_r);
            }
        } else if neg_n && !neg_d {
            unsafe {
                gmp::mpz_set_ui(r.as_raw_mut(), abs_r);
            }
            neg(r, None);
        } else if abs_r > 0 {
            unsafe {
                gmp::mpz_set_ui(r.as_raw_mut(), abs_d - abs_r);
            }
            if !neg_d {
                neg(r, None);
            }
        } else {
            set_0(r);
        }
    }
}

#[inline]
pub fn fdiv_q_u32(q: &mut Integer, n: Option<&Integer>, d: u32) -> bool {
    assert_ne!(d, 0, "division by zero");
    (unsafe {
        gmp::mpz_fdiv_q_ui(q.as_raw_mut(), n.unwrap_or(q).as_raw(), d.into())
    }) != 0
}

#[inline]
pub fn fdiv_r_u32(r: &mut Integer, n: Option<&Integer>, d: u32) -> bool {
    assert_ne!(d, 0, "division by zero");
    (unsafe {
        gmp::mpz_fdiv_r_ui(r.as_raw_mut(), n.unwrap_or(r).as_raw(), d.into())
    }) != 0
}

pub fn u32_fdiv_q(q: &mut Integer, n: u32, d: Option<&Integer>) {
    check_div0_or(d, q);
    let n = n.into();
    let neg_d = d.unwrap_or(q).cmp0() == Ordering::Less;
    let d_ptr = d.unwrap_or(q).as_raw();
    let abs_d_greater_n = unsafe { gmp::mpz_cmpabs_ui(d_ptr, n) > 0 };
    if abs_d_greater_n {
        // n / +abs_d -> 0, n
        // n / -abs_d -> 0, n + if n > 0 { -1, -abs_d }
        if n > 0 && neg_d {
            set_m1(q);
        } else {
            set_0(q);
        }
    } else {
        // n / +abs_d -> +abs_q, +abs_r
        // n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
        let abs_d = unsafe { gmp::mpz_get_ui(d_ptr) };
        let (mut abs_q, abs_r) = (n / abs_d, n % abs_d);
        if !neg_d {
            unsafe {
                gmp::mpz_set_ui(q.as_raw_mut(), abs_q);
            }
        } else {
            if abs_r > 0 {
                abs_q += 1;
            }
            unsafe {
                gmp::mpz_set_ui(q.as_raw_mut(), abs_q);
            }
            neg(q, None);
        }
    }
}

pub fn u32_fdiv_r(r: &mut Integer, n: u32, d: Option<&Integer>) {
    check_div0_or(d, r);
    let n = n.into();
    let neg_d = d.unwrap_or(r).cmp0() == Ordering::Less;
    let d_ptr = d.unwrap_or(r).as_raw();
    let abs_d_greater_n = unsafe { gmp::mpz_cmpabs_ui(d_ptr, n) > 0 };
    if abs_d_greater_n {
        // n / +abs_d -> 0, n
        // n / -abs_d -> 0, n + if n > 0 { -1, -abs_d }
        if n > 0 && neg_d {
            unsafe {
                gmp::mpz_add_ui(r.as_raw_mut(), d_ptr, n);
            }
        } else {
            unsafe {
                gmp::mpz_set_ui(r.as_raw_mut(), n);
            }
        }
    } else {
        // n / +abs_d -> +abs_q, +abs_r
        // n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
        let abs_d = unsafe { gmp::mpz_get_ui(d_ptr) };
        let abs_r = n % abs_d;
        if !neg_d {
            unsafe {
                gmp::mpz_set_ui(r.as_raw_mut(), abs_r);
            }
        } else if abs_r > 0 {
            unsafe {
                gmp::mpz_set_ui(r.as_raw_mut(), abs_d - abs_r);
            }
            neg(r, None);
        } else {
            set_0(r);
        }
    }
}

#[inline]
pub fn fdiv_q_i32(q: &mut Integer, n: Option<&Integer>, d: i32) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
    // -abs_n / +abs_d -> -abs_q, -abs_r + if abs_r > 0 { -1, +abs_d }
    // -abs_n / -abs_d -> +abs_q, -abs_r
    let (neg_d, abs_d) = d.neg_abs();
    let some_r = fdiv_q_u32(q, n, abs_d);
    if neg_d {
        if some_r {
            i32_sub(q, -1, None);
        } else {
            neg(q, None);
        }
    }
}

#[inline]
pub fn fdiv_r_i32(r: &mut Integer, n: Option<&Integer>, d: i32) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
    // -abs_n / +abs_d -> -abs_q, -abs_r + if abs_r > 0 { -1, +abs_d }
    // -abs_n / -abs_d -> +abs_q, -abs_r
    let (neg_d, abs_d) = d.neg_abs();
    let some_r = fdiv_r_u32(r, n, abs_d);
    if neg_d && some_r {
        add_i32(r, None, d);
    }
}

pub fn i32_fdiv_q(q: &mut Integer, n: i32, d: Option<&Integer>) {
    check_div0_or(d, q);
    let (neg_n, abs_n) = n.neg_abs();
    let abs_n = abs_n.into();
    let neg_d = d.unwrap_or(q).cmp0() == Ordering::Less;
    let d_ptr = d.unwrap_or(q).as_raw();
    let abs_d_greater_abs_n = unsafe { gmp::mpz_cmpabs_ui(d_ptr, abs_n) > 0 };
    if abs_d_greater_abs_n {
        // +abs_n / +abs_d -> 0, +abs_n
        // +abs_n / -abs_d -> 0, +abs_n + if abs_n > 0 { -1, -abs_d }
        // -abs_n / +abs_d -> 0, -abs_n + if abs_n > 0 { -1, +abs_d }
        // -abs_n / -abs_d -> 0, -abs_n
        if (n > 0 && neg_d) || (neg_n && !neg_d) {
            set_m1(q);
        } else {
            set_0(q);
        }
    } else {
        // +abs_n / +abs_d -> +abs_q, +abs_r
        // +abs_n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
        // -abs_n / +abs_d -> -abs_q, -abs_r + if abs_r > 0 { -1, +abs_d }
        // -abs_n / -abs_d -> +abs_q, -abs_r
        let abs_d = unsafe { gmp::mpz_get_ui(d_ptr) };
        let (mut abs_q, abs_r) = (abs_n / abs_d, abs_n % abs_d);
        if (n > 0 && !neg_d) || (neg_n && neg_d) {
            unsafe {
                gmp::mpz_set_ui(q.as_raw_mut(), abs_q);
            }
        } else {
            if abs_r > 0 {
                abs_q += 1;
            }
            unsafe {
                gmp::mpz_set_ui(q.as_raw_mut(), abs_q);
            }
            neg(q, None);
        }
    }
}

pub fn i32_fdiv_r(r: &mut Integer, n: i32, d: Option<&Integer>) {
    check_div0_or(d, r);
    let (neg_n, abs_n) = n.neg_abs();
    let abs_n = abs_n.into();
    let neg_d = d.unwrap_or(r).cmp0() == Ordering::Less;
    let d_ptr = d.unwrap_or(r).as_raw();
    let abs_d_greater_abs_n = unsafe { gmp::mpz_cmpabs_ui(d_ptr, abs_n) > 0 };
    if abs_d_greater_abs_n {
        // +abs_n / +abs_d -> 0, +abs_n
        // +abs_n / -abs_d -> 0, +abs_n + if abs_n > 0 { -1, -abs_d }
        // -abs_n / +abs_d -> 0, -abs_n + if abs_n > 0 { -1, +abs_d }
        // -abs_n / -abs_d -> 0, -abs_n
        if (n > 0 && neg_d) || (neg_n && !neg_d) {
            add_i32(r, d, n);
        } else {
            set_i32(r, n);
        }
    } else {
        // +abs_n / +abs_d -> +abs_q, +abs_r
        // +abs_n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
        // -abs_n / +abs_d -> -abs_q, -abs_r + if abs_r > 0 { -1, +abs_d }
        // -abs_n / -abs_d -> +abs_q, -abs_r
        let abs_d = unsafe { gmp::mpz_get_ui(d_ptr) };
        let abs_r = abs_n % abs_d;
        if n > 0 && !neg_d {
            unsafe {
                gmp::mpz_set_ui(r.as_raw_mut(), abs_r);
            }
        } else if neg_n && neg_d {
            unsafe {
                gmp::mpz_set_ui(r.as_raw_mut(), abs_r);
            }
            neg(r, None);
        } else if abs_r > 0 {
            unsafe {
                gmp::mpz_set_ui(r.as_raw_mut(), abs_d - abs_r);
            }
            if neg_d {
                neg(r, None);
            }
        } else {
            set_0(r);
        }
    }
}

#[inline]
pub fn ediv_q_u32(q: &mut Integer, n: Option<&Integer>, d: u32) {
    fdiv_q_u32(q, n, d);
}

#[inline]
pub fn ediv_r_u32(r: &mut Integer, n: Option<&Integer>, d: u32) {
    fdiv_r_u32(r, n, d);
}

#[inline]
pub fn u32_ediv_q(q: &mut Integer, n: u32, d: Option<&Integer>) {
    if d.unwrap_or(q).cmp0() == Ordering::Less {
        u32_cdiv_q(q, n, d);
    } else {
        u32_fdiv_q(q, n, d);
    }
}

#[inline]
pub fn u32_ediv_r(r: &mut Integer, n: u32, d: Option<&Integer>) {
    if d.unwrap_or(r).cmp0() == Ordering::Less {
        u32_cdiv_r(r, n, d);
    } else {
        u32_fdiv_r(r, n, d);
    }
}

#[inline]
pub fn ediv_q_i32(q: &mut Integer, n: Option<&Integer>, d: i32) {
    if d < 0 {
        cdiv_q_i32(q, n, d);
    } else {
        fdiv_q_i32(q, n, d);
    }
}

#[inline]
pub fn ediv_r_i32(r: &mut Integer, n: Option<&Integer>, d: i32) {
    if d < 0 {
        cdiv_r_i32(r, n, d);
    } else {
        fdiv_r_i32(r, n, d);
    }
}

#[inline]
pub fn i32_ediv_q(q: &mut Integer, n: i32, d: Option<&Integer>) {
    if d.unwrap_or(q).cmp0() == Ordering::Less {
        i32_cdiv_q(q, n, d);
    } else {
        i32_fdiv_q(q, n, d);
    }
}

#[inline]
pub fn i32_ediv_r(r: &mut Integer, n: i32, d: Option<&Integer>) {
    if d.unwrap_or(r).cmp0() == Ordering::Less {
        i32_cdiv_r(r, n, d);
    } else {
        i32_fdiv_r(r, n, d);
    }
}

#[inline]
pub fn add_i32(rop: &mut Integer, op1: Option<&Integer>, op2: i32) {
    let op1_ptr = op1.unwrap_or(rop).as_raw();
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        unsafe {
            gmp::mpz_add_ui(rop.as_raw_mut(), op1_ptr, op2_abs.into());
        }
    } else {
        unsafe {
            gmp::mpz_sub_ui(rop.as_raw_mut(), op1_ptr, op2_abs.into());
        }
    }
}

#[inline]
pub fn u32_sub(rop: &mut Integer, op1: u32, op2: Option<&Integer>) {
    unsafe {
        gmp::mpz_ui_sub(
            rop.as_raw_mut(),
            op1.into(),
            op2.unwrap_or(rop).as_raw(),
        );
    }
}

#[inline]
pub fn sub_i32(rop: &mut Integer, op1: Option<&Integer>, op2: i32) {
    let op1_ptr = op1.unwrap_or(rop).as_raw();
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        unsafe {
            gmp::mpz_sub_ui(rop.as_raw_mut(), op1_ptr, op2_abs.into());
        }
    } else {
        unsafe {
            gmp::mpz_add_ui(rop.as_raw_mut(), op1_ptr, op2_abs.into());
        }
    }
}

#[inline]
pub fn i32_sub(rop: &mut Integer, op1: i32, op2: Option<&Integer>) {
    let (op1_neg, op1_abs) = op1.neg_abs();
    let op2_ptr = op2.unwrap_or(rop).as_raw();
    if !op1_neg {
        unsafe {
            gmp::mpz_ui_sub(rop.as_raw_mut(), op1_abs.into(), op2_ptr);
        }
    } else {
        unsafe {
            gmp::mpz_add_ui(rop.as_raw_mut(), op2_ptr, op1_abs.into());
        }
        neg(rop, None);
    }
}

#[inline]
pub fn lshift_i32(rop: &mut Integer, op1: Option<&Integer>, op2: i32) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        mul_2exp(rop, op1, op2_abs);
    } else {
        fdiv_q_2exp(rop, op1, op2_abs);
    }
}

#[inline]
pub fn rshift_i32(rop: &mut Integer, op1: Option<&Integer>, op2: i32) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        fdiv_q_2exp(rop, op1, op2_abs);
    } else {
        mul_2exp(rop, op1, op2_abs);
    }
}

pub fn and_u32(rop: &mut Integer, op1: Option<&Integer>, op2: u32) {
    let lop2 = gmp::limb_t::from(op2);
    let ans_limb0 = {
        let op1 = op1.unwrap_or(rop);
        match op1.cmp0() {
            Ordering::Equal => 0,
            Ordering::Greater => (unsafe { limb(op1, 0) }) & lop2,
            Ordering::Less => (unsafe { limb(op1, 0) }).wrapping_neg() & lop2,
        }
    };
    set_limb(rop, ans_limb0);
}

pub fn ior_u32(rop: &mut Integer, op1: Option<&Integer>, op2: u32) {
    let lop2 = gmp::limb_t::from(op2);
    match op1.unwrap_or(rop).cmp0() {
        Ordering::Equal => {
            set_u32(rop, op2);
        }
        Ordering::Greater => {
            set(rop, op1);
            unsafe {
                *limb_mut(rop, 0) |= lop2;
            }
        }
        Ordering::Less => {
            com(rop, op1);
            if rop.cmp0() != Ordering::Equal {
                unsafe {
                    *limb_mut(rop, 0) &= !lop2;
                    if rop.inner().size == 1 && limb(rop, 0) == 0 {
                        set_0(rop);
                    }
                }
            }
            com(rop, None);
        }
    }
}

pub fn xor_u32(rop: &mut Integer, op1: Option<&Integer>, op2: u32) {
    let lop2 = gmp::limb_t::from(op2);
    match op1.unwrap_or(rop).cmp0() {
        Ordering::Equal => {
            set_u32(rop, op2);
        }
        Ordering::Greater => {
            set(rop, op1);
            unsafe {
                *limb_mut(rop, 0) ^= lop2;
                if rop.inner().size == 1 && limb(rop, 0) == 0 {
                    set_0(rop);
                }
            }
        }
        Ordering::Less => {
            com(rop, op1);
            if rop.cmp0() == Ordering::Equal {
                if lop2 != 0 {
                    set_nonzero(rop, lop2);
                }
            } else {
                unsafe {
                    *limb_mut(rop, 0) ^= lop2;
                    if rop.inner().size == 1 && limb(rop, 0) == 0 {
                        set_0(rop);
                    }
                }
            }
            com(rop, None);
        }
    }
}

pub fn and_i32(rop: &mut Integer, op1: Option<&Integer>, op2: i32) {
    let lop2 = op2 as gmp::limb_t;
    match op1.unwrap_or(rop).cmp0() {
        Ordering::Equal => {
            set_0(rop);
        }
        Ordering::Greater => {
            if op2 >= 0 {
                let cur_limb = unsafe { limb(op1.unwrap_or(rop), 0) };
                set_limb(rop, cur_limb & lop2);
            } else {
                set(rop, op1);
                unsafe {
                    *limb_mut(rop, 0) &= lop2;
                    if rop.inner().size == 1 && limb(rop, 0) == 0 {
                        set_0(rop);
                    }
                }
            }
        }
        Ordering::Less => {
            if op2 >= 0 {
                let cur_limb = unsafe { limb(op1.unwrap_or(rop), 0) };
                set_limb(rop, cur_limb.wrapping_neg() & lop2);
            } else {
                com(rop, op1);
                if rop.cmp0() == Ordering::Equal {
                    if !lop2 != 0 {
                        set_nonzero(rop, !lop2);
                    }
                } else {
                    unsafe {
                        *limb_mut(rop, 0) |= !lop2;
                    }
                }
                com(rop, None);
            }
        }
    }
}

pub fn ior_i32(rop: &mut Integer, op1: Option<&Integer>, op2: i32) {
    let lop2 = op2 as gmp::limb_t;
    match op1.unwrap_or(rop).cmp0() {
        Ordering::Equal => {
            set_i32(rop, op2);
        }
        Ordering::Greater => {
            if op2 >= 0 {
                set(rop, op1);
                unsafe {
                    *limb_mut(rop, 0) |= lop2;
                }
            } else {
                let cur_limb = unsafe { limb(op1.unwrap_or(rop), 0) };
                set_limb(rop, !cur_limb & !lop2);
                com(rop, None);
            }
        }
        Ordering::Less => {
            if op2 >= 0 {
                com(rop, op1);
                if rop.cmp0() != Ordering::Equal {
                    unsafe {
                        *limb_mut(rop, 0) &= !lop2;
                        if rop.inner().size == 1 && limb(rop, 0) == 0 {
                            set_0(rop);
                        }
                    }
                }
                com(rop, None);
            } else {
                let cur_limb = unsafe { limb(op1.unwrap_or(rop), 0) };
                set_limb(rop, cur_limb.wrapping_sub(1) & !lop2);
                com(rop, None);
            }
        }
    }
}

pub fn xor_i32(rop: &mut Integer, op1: Option<&Integer>, op2: i32) {
    let lop2 = op2 as gmp::limb_t;
    match op1.unwrap_or(rop).cmp0() {
        Ordering::Equal => {
            set_i32(rop, op2);
        }
        Ordering::Greater => {
            if op2 >= 0 {
                set(rop, op1);
                unsafe {
                    *limb_mut(rop, 0) ^= lop2;
                    if rop.inner().size == 1 && limb(rop, 0) == 0 {
                        set_0(rop);
                    }
                }
            } else {
                set(rop, op1);
                unsafe {
                    *limb_mut(rop, 0) ^= !lop2;
                    if rop.inner().size == 1 && limb(rop, 0) == 0 {
                        set_0(rop);
                    }
                }
                com(rop, None);
            }
        }
        Ordering::Less => {
            if op2 >= 0 {
                com(rop, op1);
                if rop.cmp0() == Ordering::Equal {
                    if lop2 != 0 {
                        set_nonzero(rop, lop2);
                    }
                } else {
                    unsafe {
                        *limb_mut(rop, 0) ^= lop2;
                        if rop.inner().size == 1 && limb(rop, 0) == 0 {
                            set_0(rop);
                        }
                    }
                }
                com(rop, None);
            } else {
                com(rop, op1);
                if rop.cmp0() == Ordering::Equal {
                    if !lop2 != 0 {
                        set_nonzero(rop, !lop2);
                    }
                } else {
                    unsafe {
                        *limb_mut(rop, 0) ^= !lop2;
                        if rop.inner().size == 1 && limb(rop, 0) == 0 {
                            set_0(rop);
                        }
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
pub fn addmul(rop: &mut Integer, op1: &Integer, op2: &Integer) {
    unsafe {
        gmp::mpz_addmul(rop.as_raw_mut(), op1.as_raw(), op2.as_raw());
    }
}

#[inline]
pub fn addmul_u32(rop: &mut Integer, op1: &Integer, op2: u32) {
    unsafe {
        gmp::mpz_addmul_ui(rop.as_raw_mut(), op1.as_raw(), op2.into());
    }
}

#[inline]
pub fn addmul_i32(rop: &mut Integer, op1: &Integer, op2: i32) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        addmul_u32(rop, op1, op2_abs);
    } else {
        submul_u32(rop, op1, op2_abs);
    }
}

#[inline]
pub fn submul(rop: &mut Integer, op1: &Integer, op2: &Integer) {
    unsafe {
        gmp::mpz_submul(rop.as_raw_mut(), op1.as_raw(), op2.as_raw());
    }
}

// rop = op1 * op2 - rop
#[inline]
pub fn mulsub(rop: &mut Integer, op1: &Integer, op2: &Integer) {
    submul(rop, op1, op2);
    rop.neg_assign();
}

#[inline]
pub fn submul_u32(rop: &mut Integer, op1: &Integer, op2: u32) {
    unsafe {
        gmp::mpz_submul_ui(rop.as_raw_mut(), op1.as_raw(), op2.into());
    }
}

#[inline]
pub fn mulsub_u32(rop: &mut Integer, op1: &Integer, op2: u32) {
    submul_u32(rop, op1, op2);
    rop.neg_assign();
}

#[inline]
pub fn submul_i32(rop: &mut Integer, op1: &Integer, op2: i32) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        submul_u32(rop, op1, op2_abs);
    } else {
        addmul_u32(rop, op1, op2_abs);
    }
}

#[inline]
pub fn mulsub_i32(rop: &mut Integer, op1: &Integer, op2: i32) {
    submul_i32(rop, op1, op2);
    rop.neg_assign();
}

#[inline]
fn bitcount_to_u32(bits: gmp::bitcnt_t) -> Option<u32> {
    if bits == !0 {
        None
    } else {
        Some(cast::cast(bits))
    }
}

#[inline]
pub fn popcount(op: &Integer) -> Option<u32> {
    bitcount_to_u32(unsafe { gmp::mpz_popcount(op.as_raw()) })
}

#[inline]
pub fn zerocount(op: &Integer) -> Option<u32> {
    if op.cmp0() == Ordering::Less {
        let size = gmp::size_t::from(op.inner().size);
        let abs_size = size.wrapping_neg();
        let d = op.inner().d;
        let count = unsafe {
            let abs_popcount = gmp::mpn_popcount(d, abs_size);
            let first_one = gmp::mpn_scan1(d, 0);
            abs_popcount + first_one - 1
        };
        bitcount_to_u32(count)
    } else {
        None
    }
}

#[inline]
pub fn scan0(op: &Integer, start: u32) -> Option<u32> {
    bitcount_to_u32(unsafe { gmp::mpz_scan0(op.as_raw(), start.into()) })
}

#[inline]
pub fn scan1(op: &Integer, start: u32) -> Option<u32> {
    bitcount_to_u32(unsafe { gmp::mpz_scan1(op.as_raw(), start.into()) })
}

#[inline]
pub fn hamdist(op1: &Integer, op2: &Integer) -> Option<u32> {
    bitcount_to_u32(unsafe { gmp::mpz_hamdist(op1.as_raw(), op2.as_raw()) })
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

pub fn signed_bits(op: &Integer) -> u32 {
    let significant = significant_bits(op);
    if op.cmp0() == Ordering::Less {
        let first_one: usize =
            cast::cast(unsafe { gmp::mpn_scan1(op.inner().d, 0) });
        if first_one == significant - 1 {
            return cast::cast(significant);
        }
    }
    cast::cast(significant.checked_add(1).expect("overflow"))
}

pub fn power_of_two_p(op: &Integer) -> bool {
    if op.cmp0() != Ordering::Greater {
        return false;
    }
    let significant = significant_bits(op);
    let first_one: usize =
        cast::cast(unsafe { gmp::mpn_scan1(op.inner().d, 0) });
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

#[cfg_attr(feature = "cargo-clippy", allow(clippy::cast_lossless))]
pub fn realloc_for_mpn_set_str(rop: &mut Integer, len: usize, radix: i32) {
    // add 1 for possible rounding errors
    let bits = (f64::from(radix).log2() * (len as f64)).ceil() + 1.0;
    // add 1 because mpn_set_str requires an extra limb
    let limbs = (bits / f64::from(gmp::LIMB_BITS)).ceil() + 1.0;
    unsafe {
        gmp::_mpz_realloc(rop.as_raw_mut(), cast::cast(limbs));
    }
}

pub fn round_away(rem: &Integer, divisor: &Integer) -> bool {
    let s_rem = rem.inner().size.checked_abs().expect("overflow");
    if s_rem == 0 {
        return false;
    }
    let s_divisor = divisor.inner().size.checked_abs().expect("overflow");
    assert!(s_divisor > 0);
    debug_assert!(s_rem <= s_divisor);
    if s_rem < s_divisor - 1 {
        return false;
    }

    let mut rem_limb = if s_rem == s_divisor {
        let rem_next_limb = unsafe { limb(rem, cast::cast(s_rem - 1)) };
        if (rem_next_limb >> (gmp::LIMB_BITS - 1)) != 0 {
            return true;
        }
        rem_next_limb << 1
    } else {
        0
    };
    for i in (1..s_divisor).rev() {
        let div_limb = unsafe { limb(divisor, cast::cast(i)) };
        let rem_next_limb = unsafe { limb(rem, cast::cast(i - 1)) };
        rem_limb |= (rem_next_limb >> (gmp::LIMB_BITS - 1)) & 1;
        if rem_limb > div_limb {
            return true;
        }
        if rem_limb < div_limb {
            return false;
        }
        rem_limb = rem_next_limb << 1;
    }
    let div_limb = unsafe { limb(divisor, 0) };
    rem_limb >= div_limb
}

#[inline]
pub fn start_invert(op: &Integer, modulo: &Integer) -> Option<Integer> {
    if modulo.cmp0() == Ordering::Equal {
        return None;
    }
    let (gcd, sinverse) =
        <(Integer, Integer)>::from(op.gcd_cofactors_ref(modulo));
    if is_1(&gcd) {
        Some(sinverse)
    } else {
        None
    }
}

#[inline]
pub fn finish_invert(rop: &mut Integer, s: Option<&Integer>, modulo: &Integer) {
    if s.unwrap_or(rop).cmp0() == Ordering::Less {
        if modulo.cmp0() == Ordering::Less {
            sub(rop, s, Some(modulo))
        } else {
            add(rop, s, Some(modulo))
        }
    } else {
        set(rop, s)
    }
}

#[inline]
pub fn pow_mod(
    rop: &mut Integer,
    base: Option<&Integer>,
    exponent: &Integer,
    modulo: &Integer,
) {
    if exponent.cmp0() == Ordering::Less {
        finish_invert(rop, base, modulo);
        unsafe {
            gmp::mpz_powm(
                rop.as_raw_mut(),
                rop.as_raw(),
                exponent.as_neg().as_raw(),
                modulo.as_raw(),
            );
        }
    } else {
        unsafe {
            gmp::mpz_powm(
                rop.as_raw_mut(),
                base.unwrap_or(rop).as_raw(),
                exponent.as_raw(),
                modulo.as_raw(),
            );
        }
    }
}
