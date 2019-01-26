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
use inner::Inner;
use misc::NegAbs;
use std::cmp::Ordering;
use std::mem;
use std::os::raw::{c_int, c_long, c_ulong};
use std::ptr;
use std::{i16, i8, u16, u8};
use Integer;

#[cfg(gmp_limb_bits_32)]
pub use ext::gmp32::*;
#[cfg(gmp_limb_bits_64)]
pub use ext::gmp64::*;

#[inline]
pub unsafe fn mpz_set_0(rop: *mut mpz_t) {
    (*rop).size = 0;
}

#[inline]
pub unsafe fn mpz_set_1(rop: *mut mpz_t) {
    if (*rop).alloc < 1 {
        gmp::_mpz_realloc(rop, 1);
    }
    *limb_mut(rop, 0) = 1;
    (*rop).size = 1;
}

#[inline]
pub unsafe fn mpz_set_m1(rop: *mut mpz_t) {
    if (*rop).alloc < 1 {
        gmp::_mpz_realloc(rop, 1);
    }
    *limb_mut(rop, 0) = 1;
    (*rop).size = -1;
}

#[inline]
pub unsafe fn mpz_set_nonzero(rop: *mut mpz_t, limb: gmp::limb_t) {
    if (*rop).alloc < 1 {
        gmp::_mpz_realloc(rop, 1);
    }
    *limb_mut(rop, 0) = limb;
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
pub unsafe fn mpz_signum(rop: *mut mpz_t, op: *const mpz_t) {
    if (*op).size < 0 {
        mpz_set_m1(rop);
    } else if (*op).size > 0 {
        mpz_set_1(rop);
    } else {
        mpz_set_0(rop);
    }
}

#[inline]
pub unsafe fn mpz_square(rop: *mut mpz_t, op: *const mpz_t) {
    gmp::mpz_mul(rop, op, op);
}

#[inline]
pub unsafe fn mpz_root_check(
    rop: *mut mpz_t,
    op: *const mpz_t,
    n: c_ulong,
) -> c_int {
    assert_ne!(n, 0, "zeroth root");
    assert!(n & 1 == 1 || gmp::mpz_sgn(op) >= 0, "even root of negative");
    gmp::mpz_root(rop, op, n)
}

#[inline]
pub unsafe fn mpz_rootrem_check(
    root: *mut mpz_t,
    rem: *mut mpz_t,
    op: *const mpz_t,
    n: c_ulong,
) {
    assert_ne!(n, 0, "zeroth root");
    assert!(n & 1 == 1 || gmp::mpz_sgn(op) >= 0, "even root of negative");
    gmp::mpz_rootrem(root, rem, op, n);
}

#[inline]
pub unsafe fn mpz_sqrt_check(rop: *mut mpz_t, op: *const mpz_t) {
    assert!(gmp::mpz_sgn(op) >= 0, "square root of negative");
    gmp::mpz_sqrt(rop, op);
}

#[inline]
pub unsafe fn mpz_sqrtrem_check(
    rop1: *mut mpz_t,
    rop2: *mut mpz_t,
    op: *const mpz_t,
) {
    assert!(gmp::mpz_sgn(op) >= 0, "square root of negative");
    gmp::mpz_sqrtrem(rop1, rop2, op);
}

#[inline]
pub unsafe fn mpz_tdiv_qr_check(
    q: *mut mpz_t,
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_tdiv_qr(q, r, n, d);
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
pub unsafe fn mpz_cdiv_qr_check(
    q: *mut mpz_t,
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_cdiv_qr(q, r, n, d);
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
pub unsafe fn mpz_fdiv_qr_check(
    q: *mut mpz_t,
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_fdiv_qr(q, r, n, d);
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
pub unsafe fn mpz_ediv_qr_check(
    q: *mut mpz_t,
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_cdiv_qr_check(q, r, n, d);
    } else {
        mpz_fdiv_qr_check(q, r, n, d);
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

pub unsafe fn mpz_rdiv_qr_check(
    q: *mut mpz_t,
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    let den;
    // make sure d is not going to be aliased and overwritten
    let d = if d == r || d == q {
        let mut den_z = mem::uninitialized();
        gmp::mpz_init_set(&mut den_z, d);
        den = Integer::from_raw(den_z);
        den.inner()
    } else {
        d
    };
    gmp::mpz_tdiv_qr(q, r, n, d);
    if round_away(r, d) {
        if (gmp::mpz_sgn(r) < 0) == (gmp::mpz_sgn(d) < 0) {
            // positive q
            gmp::mpz_add_ui(q, q, 1);
            gmp::mpz_sub(r, r, d);
        } else {
            // negative q
            gmp::mpz_sub_ui(q, q, 1);
            gmp::mpz_add(r, r, d);
        }
    }
}

pub unsafe fn mpz_keep_signed_bits(
    r: *mut mpz_t,
    n: *const mpz_t,
    b: gmp::bitcnt_t,
) {
    if b > 0 && gmp::mpz_tstbit(n, b - 1) != 0 {
        gmp::mpz_cdiv_r_2exp(r, n, b);
    } else {
        gmp::mpz_fdiv_r_2exp(r, n, b);
    }
}

#[inline]
pub unsafe fn mpz_divexact_check(
    q: *mut mpz_t,
    dividend: *const mpz_t,
    divisor: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(divisor), 0, "division by zero");
    gmp::mpz_divexact(q, dividend, divisor);
}

#[inline]
pub unsafe fn mpz_divexact_ui_check(
    q: *mut mpz_t,
    dividend: *const mpz_t,
    divisor: c_ulong,
) {
    assert_ne!(divisor, 0, "division by zero");
    gmp::mpz_divexact_ui(q, dividend, divisor);
}

#[inline]
pub unsafe fn mpz_si_pow_ui(rop: *mut mpz_t, base: c_long, exp: c_ulong) {
    let (base_neg, base_abs) = base.neg_abs();
    gmp::mpz_ui_pow_ui(rop, base_abs, exp);
    if base_neg && (exp & 1) == 1 {
        gmp::mpz_neg(rop, rop);
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
        Ordering::Greater => limb(op1, 0) & lop2,
        Ordering::Less => limb(op1, 0).wrapping_neg() & lop2,
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
            *limb_mut(rop, 0) |= lop2;
        }
        Ordering::Less => {
            gmp::mpz_com(rop, op1);
            if (*rop).size != 0 {
                *limb_mut(rop, 0) &= !lop2;
                if (*rop).size == 1 && limb(rop, 0) == 0 {
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
            *limb_mut(rop, 0) ^= lop2;
            if (*rop).size == 1 && limb(rop, 0) == 0 {
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
                *limb_mut(rop, 0) ^= lop2;
                if (*rop).size == 1 && limb(rop, 0) == 0 {
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
                mpz_set_limb(rop, limb(op1, 0) & lop2);
            } else {
                gmp::mpz_set(rop, op1);
                *limb_mut(rop, 0) &= lop2;
                if (*rop).size == 1 && limb(rop, 0) == 0 {
                    (*rop).size = 0;
                }
            }
        }
        Ordering::Less => {
            if op2 >= 0 {
                mpz_set_limb(rop, limb(op1, 0).wrapping_neg() & lop2);
            } else {
                gmp::mpz_com(rop, op1);
                if (*rop).size == 0 {
                    if !lop2 != 0 {
                        mpz_set_nonzero(rop, !lop2);
                    }
                } else {
                    *limb_mut(rop, 0) |= !lop2;
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
                *limb_mut(rop, 0) |= lop2;
            } else {
                mpz_set_limb(rop, !limb(op1, 0) & !lop2);
                gmp::mpz_com(rop, rop);
            }
        }
        Ordering::Less => {
            if op2 >= 0 {
                gmp::mpz_com(rop, op1);
                if (*rop).size != 0 {
                    *limb_mut(rop, 0) &= !lop2;
                    if (*rop).size == 1 && limb(rop, 0) == 0 {
                        (*rop).size = 0;
                    }
                }
                gmp::mpz_com(rop, rop);
            } else {
                mpz_set_limb(rop, limb(op1, 0).wrapping_sub(1) & !lop2);
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
                *limb_mut(rop, 0) ^= lop2;
                if (*rop).size == 1 && limb(rop, 0) == 0 {
                    (*rop).size = 0;
                }
            } else {
                gmp::mpz_set(rop, op1);
                *limb_mut(rop, 0) ^= !lop2;
                if (*rop).size == 1 && limb(rop, 0) == 0 {
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
                    *limb_mut(rop, 0) ^= lop2;
                    if (*rop).size == 1 && limb(rop, 0) == 0 {
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
                    *limb_mut(rop, 0) ^= !lop2;
                    if (*rop).size == 1 && limb(rop, 0) == 0 {
                        (*rop).size = 0;
                    }
                }
            }
        }
    }
}

#[cfg(int_128)]
#[inline]
pub unsafe fn mpz_set_i128(rop: *mut mpz_t, i: i128) {
    let (neg_i, abs_i) = i.neg_abs();
    mpz_set_u128(rop, abs_i);
    if neg_i {
        (*rop).size = -(*rop).size;
    }
}

#[inline]
pub unsafe fn mpz_set_i64(rop: *mut mpz_t, i: i64) {
    let (neg_i, abs_i) = i.neg_abs();
    mpz_set_u64(rop, abs_i);
    if neg_i {
        (*rop).size = -(*rop).size;
    }
}

#[inline]
pub unsafe fn mpz_set_i32(rop: *mut mpz_t, i: i32) {
    let (neg_i, abs_i) = i.neg_abs();
    mpz_set_u32(rop, abs_i);
    if neg_i {
        (*rop).size = -(*rop).size;
    }
}

#[inline]
pub unsafe fn mpz_fits_u8(op: *const mpz_t) -> bool {
    match (*op).size {
        0 => true,
        1 => limb(op, 0) <= gmp::limb_t::from(u8::MAX),
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_fits_i8(op: *const mpz_t) -> bool {
    match (*op).size {
        0 => true,
        1 => limb(op, 0) <= gmp::limb_t::from(i8::MAX as u8),
        -1 => limb(op, 0) <= gmp::limb_t::from(i8::MIN as u8),
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_fits_u16(op: *const mpz_t) -> bool {
    match (*op).size {
        0 => true,
        1 => limb(op, 0) <= gmp::limb_t::from(u16::MAX),
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_fits_i16(op: *const mpz_t) -> bool {
    match (*op).size {
        0 => true,
        1 => limb(op, 0) <= gmp::limb_t::from(i16::MAX as u16),
        -1 => limb(op, 0) <= gmp::limb_t::from(i16::MIN as u16),
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

pub unsafe fn mpz_next_pow_of_two(rop: *mut mpz_t, op: *const mpz_t) {
    let size = (*op).size;
    if size <= 0 {
        mpz_set_1(rop);
        return;
    }
    let significant = mpz_significant_bits(op);
    let first_one = gmp::mpn_scan1((*op).d, 0);
    let bit = if first_one == significant - 1 {
        if rop as *const mpz_t == op {
            return;
        }
        first_one
    } else {
        significant
    };
    mpz_set_0(rop);
    gmp::mpz_setbit(rop, bit);
}

#[inline]
pub unsafe fn mpz_gcdext1(
    g: *mut mpz_t,
    s: *mut mpz_t,
    a: *const mpz_t,
    b: *const mpz_t,
) {
    gmp::mpz_gcdext(g, s, ptr::null_mut(), a, b);
}

#[inline]
pub unsafe fn limb(z: *const mpz_t, index: isize) -> gmp::limb_t {
    *(*z).d.offset(index)
}

#[inline]
pub unsafe fn limb_mut(z: *const mpz_t, index: isize) -> *mut gmp::limb_t {
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
unsafe fn round_away(rem: *const mpz_t, dividend: *const mpz_t) -> bool {
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
        let rem_next_limb = limb(rem, cast::cast(s_rem - 1));
        if (rem_next_limb >> (gmp::LIMB_BITS - 1)) != 0 {
            return true;
        }
        rem_next_limb << 1
    } else {
        0
    };
    for i in (1..s_dividend).rev() {
        let div_limb = limb(dividend, cast::cast(i));
        let rem_next_limb = limb(rem, cast::cast(i - 1));
        rem_limb |= (rem_next_limb >> (gmp::LIMB_BITS - 1)) & 1;
        if rem_limb > div_limb {
            return true;
        }
        if rem_limb < div_limb {
            return false;
        }
        rem_limb = rem_next_limb << 1;
    }
    let div_limb = limb(dividend, 0);
    rem_limb >= div_limb
}

#[cfg(feature = "rational")]
pub use self::rational::*;
#[cfg(feature = "rational")]
mod rational {
    use super::*;
    use gmp_mpfr_sys::gmp::mpq_t;
    use inner::Inner;
    use rational::SmallRational;

    #[inline]
    pub unsafe fn mpq_signum(signum: *mut mpz_t, op: *const mpq_t) {
        let num = gmp::mpq_numref_const(op);
        mpz_signum(signum, num);
    }

    #[inline]
    pub unsafe fn mpq_square(rop: *mut mpq_t, op: *const mpq_t) {
        mpz_square(gmp::mpq_numref(rop), gmp::mpq_numref_const(op));
        mpz_square(gmp::mpq_denref(rop), gmp::mpq_denref_const(op));
    }

    #[inline]
    pub unsafe fn mpq_inv_check(rop: *mut mpq_t, op: *const mpq_t) {
        assert_ne!(gmp::mpq_sgn(op), 0, "division by zero");
        gmp::mpq_inv(rop, op);
    }

    #[inline]
    pub unsafe fn mpq_mul_2exp_si(
        rop: *mut mpq_t,
        op1: *const mpq_t,
        op2: c_long,
    ) {
        let (op2_neg, op2_abs) = op2.neg_abs();
        if !op2_neg {
            gmp::mpq_mul_2exp(rop, op1, op2_abs);
        } else {
            gmp::mpq_div_2exp(rop, op1, op2_abs);
        }
    }

    #[inline]
    pub unsafe fn mpq_div_2exp_si(
        rop: *mut mpq_t,
        op1: *const mpq_t,
        op2: c_long,
    ) {
        let (op2_neg, op2_abs) = op2.neg_abs();
        if !op2_neg {
            gmp::mpq_div_2exp(rop, op1, op2_abs);
        } else {
            gmp::mpq_mul_2exp(rop, op1, op2_abs);
        }
    }

    #[inline]
    pub unsafe fn mpq_pow_ui(rop: *mut mpq_t, op1: *const mpq_t, op2: c_ulong) {
        let rop_num = gmp::mpq_numref(rop);
        let rop_den = gmp::mpq_denref(rop);
        let op1_num = gmp::mpq_numref_const(op1);
        let op1_den = gmp::mpq_denref_const(op1);
        gmp::mpz_pow_ui(rop_num, op1_num, op2);
        gmp::mpz_pow_ui(rop_den, op1_den, op2);
    }

    #[inline]
    pub unsafe fn mpq_pow_si(rop: *mut mpq_t, op1: *const mpq_t, op2: c_long) {
        let (op2_neg, op2_abs) = op2.neg_abs();
        if !op2_neg {
            mpq_pow_ui(rop, op1, op2_abs);
        } else {
            assert_ne!(gmp::mpq_sgn(op1), 0, "division by zero");
            mpq_pow_ui(rop, op1, op2_abs);
            gmp::mpq_inv(rop, rop);
        }
    }

    #[inline]
    pub unsafe fn mpq_trunc(trunc: *mut mpz_t, op: *const mpq_t) {
        let num = gmp::mpq_numref_const(op);
        let den = gmp::mpq_denref_const(op);
        gmp::mpz_tdiv_q(trunc, num, den);
    }

    #[inline]
    pub unsafe fn mpq_trunc_fract(fract: *mut mpq_t, op: *const mpq_t) {
        let fract_num = gmp::mpq_numref(fract);
        let fract_den = gmp::mpq_denref(fract);
        let num = gmp::mpq_numref_const(op);
        let den = gmp::mpq_denref_const(op);
        gmp::mpz_tdiv_r(fract_num, num, den);
        gmp::mpz_set(fract_den, den);
    }

    #[inline]
    pub unsafe fn mpq_trunc_fract_whole(
        fract: *mut mpq_t,
        trunc: *mut mpz_t,
        op: *const mpq_t,
    ) {
        let fract_num = gmp::mpq_numref(fract);
        let fract_den = gmp::mpq_denref(fract);
        let num = gmp::mpq_numref_const(op);
        let den = gmp::mpq_denref_const(op);
        gmp::mpz_tdiv_qr(trunc, fract_num, num, den);
        gmp::mpz_set(fract_den, den);
    }

    #[inline]
    pub unsafe fn mpq_ceil(ceil: *mut mpz_t, op: *const mpq_t) {
        let num = gmp::mpq_numref_const(op);
        let den = gmp::mpq_denref_const(op);
        if gmp::mpz_cmp_ui(den, 1) == 0 {
            gmp::mpz_set(ceil, num);
        } else {
            // use tdiv_q rather than cdiv_q to allow GMP not to keep remainder
            let neg = gmp::mpz_sgn(num) < 0;
            gmp::mpz_tdiv_q(ceil, num, den);
            if !neg {
                gmp::mpz_add_ui(ceil, ceil, 1);
            }
        }
    }

    #[inline]
    pub unsafe fn mpq_ceil_fract(fract: *mut mpq_t, op: *const mpq_t) {
        let fract_num = gmp::mpq_numref(fract);
        let fract_den = gmp::mpq_denref(fract);
        let num = gmp::mpq_numref_const(op);
        let den = gmp::mpq_denref_const(op);
        gmp::mpz_cdiv_r(fract_num, num, den);
        gmp::mpz_set(fract_den, den);
    }

    #[inline]
    pub unsafe fn mpq_ceil_fract_whole(
        fract: *mut mpq_t,
        ceil: *mut mpz_t,
        op: *const mpq_t,
    ) {
        let fract_num = gmp::mpq_numref(fract);
        let fract_den = gmp::mpq_denref(fract);
        let num = gmp::mpq_numref_const(op);
        let den = gmp::mpq_denref_const(op);
        gmp::mpz_cdiv_qr(ceil, fract_num, num, den);
        gmp::mpz_set(fract_den, den);
    }

    #[inline]
    pub unsafe fn mpq_floor(floor: *mut mpz_t, op: *const mpq_t) {
        let num = gmp::mpq_numref_const(op);
        let den = gmp::mpq_denref_const(op);
        if gmp::mpz_cmp_ui(den, 1) == 0 {
            gmp::mpz_set(floor, num);
        } else {
            // use tdiv_q rather than fdiv_q to allow GMP not to keep remainder
            let neg = gmp::mpz_sgn(num) < 0;
            gmp::mpz_tdiv_q(floor, num, den);
            if neg {
                gmp::mpz_sub_ui(floor, floor, 1);
            }
        }
    }

    #[inline]
    pub unsafe fn mpq_floor_fract(fract: *mut mpq_t, op: *const mpq_t) {
        let fract_num = gmp::mpq_numref(fract);
        let fract_den = gmp::mpq_denref(fract);
        let num = gmp::mpq_numref_const(op);
        let den = gmp::mpq_denref_const(op);
        gmp::mpz_fdiv_r(fract_num, num, den);
        gmp::mpz_set(fract_den, den);
    }

    #[inline]
    pub unsafe fn mpq_floor_fract_whole(
        fract: *mut mpq_t,
        floor: *mut mpz_t,
        op: *const mpq_t,
    ) {
        let fract_num = gmp::mpq_numref(fract);
        let fract_den = gmp::mpq_denref(fract);
        let num = gmp::mpq_numref_const(op);
        let den = gmp::mpq_denref_const(op);
        gmp::mpz_fdiv_qr(floor, fract_num, num, den);
        gmp::mpz_set(fract_den, den);
    }

    pub unsafe fn mpq_round(round: *mut mpz_t, op: *const mpq_t) {
        let num = gmp::mpq_numref_const(op);
        let den = gmp::mpq_denref_const(op);
        if gmp::mpz_cmp_ui(den, 1) == 0 {
            gmp::mpz_set(round, num);
            return;
        }
        // The remainder cannot be larger than the divisor, but we
        // allocate an extra limb because the GMP docs suggest we should.
        let limbs = cast::cast::<_, gmp::bitcnt_t>((*den).size.abs()) + 1;
        let bits = limbs
            .checked_mul(cast::cast::<_, gmp::bitcnt_t>(gmp::LIMB_BITS))
            .expect("overflow");
        let mut rem: mpz_t = mem::uninitialized();
        gmp::mpz_init2(&mut rem, bits);
        gmp::mpz_tdiv_qr(round, &mut rem, num, den);
        if round_away(&rem, den) {
            if gmp::mpz_sgn(&rem) >= 0 {
                // positive number
                gmp::mpz_add_ui(round, round, 1);
            } else {
                // negative number
                gmp::mpz_sub_ui(round, round, 1);
            }
        }
        gmp::mpz_clear(&mut rem);
    }

    pub unsafe fn mpq_round_fract(fract: *mut mpq_t, op: *const mpq_t) {
        let fract_num = gmp::mpq_numref(fract);
        let fract_den = gmp::mpq_denref(fract);
        let num = gmp::mpq_numref_const(op);
        let den = gmp::mpq_denref_const(op);
        if gmp::mpz_cmp_ui(den, 1) == 0 {
            mpz_set_0(fract_num);
            mpz_set_1(fract_den);
            return;
        }
        gmp::mpz_tdiv_r(fract_num, num, den);
        gmp::mpz_set(fract_den, den);
        if round_away(fract_num, fract_den) {
            if gmp::mpz_sgn(fract_num) >= 0 {
                // positive number
                gmp::mpz_sub(fract_num, fract_num, fract_den);
            } else {
                // negative number
                gmp::mpz_add(fract_num, fract_num, fract_den);
            }
        }
    }

    pub unsafe fn mpq_round_fract_whole(
        fract: *mut mpq_t,
        round: *mut mpz_t,
        op: *const mpq_t,
    ) {
        let fract_num = gmp::mpq_numref(fract);
        let fract_den = gmp::mpq_denref(fract);
        let num = gmp::mpq_numref_const(op);
        let den = gmp::mpq_denref_const(op);
        if gmp::mpz_cmp_ui(den, 1) == 0 {
            // set round before fract_num, which might alias num
            gmp::mpz_set(round, num);
            mpz_set_0(fract_num);
            mpz_set_1(fract_den);
            return;
        }
        gmp::mpz_tdiv_qr(round, fract_num, num, den);
        gmp::mpz_set(fract_den, den);
        if round_away(fract_num, fract_den) {
            if gmp::mpz_sgn(fract_num) >= 0 {
                // positive number
                gmp::mpz_sub(fract_num, fract_num, fract_den);
                gmp::mpz_add_ui(round, round, 1);
            } else {
                // negative number
                gmp::mpz_add(fract_num, fract_num, fract_den);
                gmp::mpz_sub_ui(round, round, 1);
            }
        }
    }

    #[inline]
    pub unsafe fn mpq_cmp_u64(op1: *const mpq_t, n2: u64, d2: u64) -> c_int {
        if let Some(n2) = cast::checked_cast(n2) {
            if let Some(d2) = cast::checked_cast(d2) {
                return gmp::mpq_cmp_ui(op1, n2, d2);
            }
        }
        let small = SmallRational::from((n2, d2));
        gmp::mpq_cmp(op1, (*small).inner())
    }

    #[inline]
    pub unsafe fn mpq_cmp_i64(op1: *const mpq_t, n2: i64, d2: u64) -> c_int {
        if let Some(n2) = cast::checked_cast(n2) {
            if let Some(d2) = cast::checked_cast(d2) {
                return gmp::mpq_cmp_si(op1, n2, d2);
            }
        }
        let small = SmallRational::from((n2, d2));
        gmp::mpq_cmp(op1, (*small).inner())
    }

    #[cfg(int_128)]
    #[inline]
    pub unsafe fn mpq_cmp_u128(op1: *const mpq_t, n2: u128, d2: u128) -> c_int {
        if let Some(n2) = cast::checked_cast(n2) {
            if let Some(d2) = cast::checked_cast(d2) {
                return gmp::mpq_cmp_ui(op1, n2, d2);
            }
        }
        let small = SmallRational::from((n2, d2));
        gmp::mpq_cmp(op1, (*small).inner())
    }

    #[cfg(int_128)]
    #[inline]
    pub unsafe fn mpq_cmp_i128(op1: *const mpq_t, n2: i128, d2: u128) -> c_int {
        if let Some(n2) = cast::checked_cast(n2) {
            if let Some(d2) = cast::checked_cast(d2) {
                return gmp::mpq_cmp_si(op1, n2, d2);
            }
        }
        let small = SmallRational::from((n2, d2));
        gmp::mpq_cmp(op1, (*small).inner())
    }

    pub unsafe fn mpq_cmp_finite_d(op1: *const mpq_t, op2: f64) -> c_int {
        let num1 = gmp::mpq_numref_const(op1);
        let den1 = gmp::mpq_denref_const(op1);
        let den1_bits = gmp::mpz_sizeinbase(den1, 2);
        // cmp(num1, op2 * den1)
        let mut op2_f = mem::uninitialized();
        let mut rhs = mem::uninitialized();
        gmp::mpf_init2(&mut op2_f, 53);
        gmp::mpf_set_d(&mut op2_f, op2);
        gmp::mpf_init2(&mut rhs, cast::cast(den1_bits + 53));
        gmp::mpf_set_z(&mut rhs, den1);
        gmp::mpf_mul(&mut rhs, &rhs, &op2_f);
        let ret = -gmp::mpf_cmp_z(&rhs, num1);
        gmp::mpf_clear(&mut rhs);
        gmp::mpf_clear(&mut op2_f);
        ret
    }
}
