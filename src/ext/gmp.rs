// Copyright © 2016–2018 University of Malta

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
// this program. If not, see <http://www.gnu.org/licenses/>.

use cast::cast;
use gmp_mpfr_sys::gmp::{self, mpz_t};
use std::{i16, i32, i64, i8, u16, u32, u64, u8};
use std::cmp::Ordering;
use std::mem;
use std::os::raw::{c_int, c_long, c_ulong};

#[inline]
pub unsafe fn mpz_set_0(rop: *mut mpz_t) {
    (*rop).size = 0;
}

#[inline]
pub unsafe fn mpz_set_1(rop: *mut mpz_t) {
    *limb_mut(rop, 0) = 1;
    (*rop).size = 1;
}

#[inline]
pub unsafe fn mpz_set_m1(rop: *mut mpz_t) {
    *limb_mut(rop, 0) = 1;
    (*rop).size = -1;
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
    mpz_tdiv_q_ui_check(q, n, d.wrapping_abs() as c_ulong);
    if d < 0 {
        gmp::mpz_neg(q, q);
    }
}

#[inline]
pub unsafe fn mpz_tdiv_r_si_check(r: *mut mpz_t, n: *const mpz_t, d: c_long) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    mpz_tdiv_r_ui_check(r, n, d.wrapping_abs() as c_ulong);
}

#[inline]
pub unsafe fn mpz_si_tdiv_q_check(q: *mut mpz_t, n: c_long, d: *const mpz_t) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    mpz_ui_tdiv_q_check(q, n.wrapping_abs() as c_ulong, d);
    if n < 0 {
        gmp::mpz_neg(q, q);
    }
}

#[inline]
pub unsafe fn mpz_si_tdiv_r_check(r: *mut mpz_t, n: c_long, d: *const mpz_t) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    mpz_ui_tdiv_r_check(r, n.wrapping_abs() as c_ulong, d);
    if n < 0 {
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
    let some_r = mpz_cdiv_q_ui_check(q, n, d.wrapping_abs() as c_ulong) != 0;
    if d < 0 {
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
    let some_r = mpz_cdiv_r_ui_check(r, n, d.wrapping_abs() as c_ulong) != 0;
    if d < 0 && some_r {
        mpz_sub_si(r, r, d);
    }
}

pub unsafe fn mpz_si_cdiv_q_check(q: *mut mpz_t, n: c_long, d: *const mpz_t) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(d, n.wrapping_abs() as c_ulong) > 0 {
        // +abs_n / +abs_d -> 0, +abs_n + if abs_n > 0 { 1, -abs_d }
        // +abs_n / -abs_d -> 0, +abs_n
        // -abs_n / +abs_d -> 0, -abs_n
        // -abs_n / -abs_d -> 0, -abs_n + if abs_n > 0 { 1, +abs_d }
        if (n > 0 && sgn_d > 0) || (n < 0 && sgn_d < 0) {
            mpz_set_1(q);
        } else {
            mpz_set_0(q);
        }
    } else {
        // +abs_n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
        // +abs_n / -abs_d -> -abs_q, +abs_r
        // -abs_n / +abs_d -> -abs_q, -abs_r
        // -abs_n / -abs_d -> +abs_q, -abs_r + if abs_r > 0 { 1, +abs_d }
        let abs_n = n.wrapping_abs() as c_ulong;
        let abs_d = gmp::mpz_get_ui(d);
        let (mut abs_q, abs_r) = (abs_n / abs_d, abs_n % abs_d);
        if (n > 0 && sgn_d < 0) || (n < 0 && sgn_d > 0) {
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
    if gmp::mpz_cmpabs_ui(d, n.wrapping_abs() as c_ulong) > 0 {
        // +abs_n / +abs_d -> 0, +abs_n + if abs_n > 0 { 1, -abs_d }
        // +abs_n / -abs_d -> 0, +abs_n
        // -abs_n / +abs_d -> 0, -abs_n
        // -abs_n / -abs_d -> 0, -abs_n + if abs_n > 0 { 1, +abs_d }
        if (n > 0 && sgn_d > 0) || (n < 0 && sgn_d < 0) {
            mpz_si_sub(r, n, d);
        } else {
            gmp::mpz_set_si(r, n);
        }
    } else {
        // +abs_n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
        // +abs_n / -abs_d -> -abs_q, +abs_r
        // -abs_n / +abs_d -> -abs_q, -abs_r
        // -abs_n / -abs_d -> +abs_q, -abs_r + if abs_r > 0 { 1, +abs_d }
        let abs_n = n.wrapping_abs() as c_ulong;
        let abs_d = gmp::mpz_get_ui(d);
        let abs_r = abs_n % abs_d;
        if n > 0 && sgn_d < 0 {
            gmp::mpz_set_ui(r, abs_r);
        } else if n < 0 && sgn_d > 0 {
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
    let some_r = mpz_fdiv_q_ui_check(q, n, d.wrapping_abs() as c_ulong) != 0;
    if d < 0 {
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
    let some_r = mpz_fdiv_r_ui_check(r, n, d.wrapping_abs() as c_ulong) != 0;
    if d < 0 && some_r {
        mpz_add_si(r, r, d);
    }
}

pub unsafe fn mpz_si_fdiv_q_check(q: *mut mpz_t, n: c_long, d: *const mpz_t) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(d, n.wrapping_abs() as c_ulong) > 0 {
        // +abs_n / +abs_d -> 0, +abs_n
        // +abs_n / -abs_d -> 0, +abs_n + if abs_n > 0 { -1, -abs_d }
        // -abs_n / +abs_d -> 0, -abs_n + if abs_n > 0 { -1, +abs_d }
        // -abs_n / -abs_d -> 0, -abs_n
        if (n > 0 && sgn_d < 0) || (n < 0 && sgn_d > 0) {
            mpz_set_m1(q);
        } else {
            mpz_set_0(q);
        }
    } else {
        // +abs_n / +abs_d -> +abs_q, +abs_r
        // +abs_n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
        // -abs_n / +abs_d -> -abs_q, -abs_r + if abs_r > 0 { -1, +abs_d }
        // -abs_n / -abs_d -> +abs_q, -abs_r
        let abs_n = n.wrapping_abs() as c_ulong;
        let abs_d = gmp::mpz_get_ui(d);
        let (mut abs_q, abs_r) = (abs_n / abs_d, abs_n % abs_d);
        if (n > 0 && sgn_d > 0) || (n < 0 && sgn_d < 0) {
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
    if gmp::mpz_cmpabs_ui(d, n.wrapping_abs() as c_ulong) > 0 {
        // +abs_n / +abs_d -> 0, +abs_n
        // +abs_n / -abs_d -> 0, +abs_n + if abs_n > 0 { -1, -abs_d }
        // -abs_n / +abs_d -> 0, -abs_n + if abs_n > 0 { -1, +abs_d }
        // -abs_n / -abs_d -> 0, -abs_n
        if (n > 0 && sgn_d < 0) || (n < 0 && sgn_d > 0) {
            mpz_add_si(r, d, n);
        } else {
            gmp::mpz_set_si(r, n);
        }
    } else {
        // +abs_n / +abs_d -> +abs_q, +abs_r
        // +abs_n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
        // -abs_n / +abs_d -> -abs_q, -abs_r + if abs_r > 0 { -1, +abs_d }
        // -abs_n / -abs_d -> +abs_q, -abs_r
        let abs_n = n.wrapping_abs() as c_ulong;
        let abs_d = gmp::mpz_get_ui(d);
        let abs_r = abs_n % abs_d;
        if n > 0 && sgn_d > 0 {
            gmp::mpz_set_ui(r, abs_r);
        } else if n < 0 && sgn_d < 0 {
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
pub unsafe fn mpz_invert_check(
    inv: *mut mpz_t,
    n: *const mpz_t,
    m: *const mpz_t,
) -> c_int {
    assert_ne!(gmp::mpz_sgn(m), 0, "division by zero");
    gmp::mpz_invert(inv, n, m)
}

#[inline]
pub unsafe fn mpz_si_pow_ui(rop: *mut mpz_t, base: c_long, exp: c_ulong) {
    if base >= 0 {
        gmp::mpz_ui_pow_ui(rop, base as c_ulong, exp);
    } else {
        gmp::mpz_ui_pow_ui(rop, base.wrapping_neg() as c_ulong, exp);
        if (exp & 1) == 1 {
            (*rop).size = -(*rop).size;
        }
    }
}

#[inline]
pub unsafe fn mpz_add_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    if op2 >= 0 {
        gmp::mpz_add_ui(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpz_sub_ui(rop, op1, op2.wrapping_neg() as c_ulong);
    }
}

#[inline]
pub unsafe fn mpz_sub_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    if op2 >= 0 {
        gmp::mpz_sub_ui(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpz_add_ui(rop, op1, op2.wrapping_neg() as c_ulong);
    }
}

#[inline]
pub unsafe fn mpz_si_sub(rop: *mut mpz_t, op1: c_long, op2: *const mpz_t) {
    if op1 >= 0 {
        gmp::mpz_ui_sub(rop, op1 as c_ulong, op2);
    } else {
        gmp::mpz_neg(rop, op2);
        gmp::mpz_sub_ui(rop, rop, op1.wrapping_neg() as c_ulong);
    }
}

#[inline]
pub unsafe fn mpz_lshift_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    if op2 >= 0 {
        gmp::mpz_mul_2exp(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpz_fdiv_q_2exp(rop, op1, op2.wrapping_neg() as c_ulong);
    }
}

#[inline]
pub unsafe fn mpz_rshift_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    if op2 >= 0 {
        gmp::mpz_fdiv_q_2exp(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpz_mul_2exp(rop, op1, op2.wrapping_neg() as c_ulong);
    }
}

pub unsafe fn bitand_ui(rop: *mut mpz_t, op1: *const mpz_t, op2: c_ulong) {
    let lop2 = gmp::limb_t::from(op2);
    match (*op1).size.cmp(&0) {
        Ordering::Equal => {
            (*rop).size = 0;
        }
        Ordering::Greater => {
            *limb_mut(rop, 0) = limb(op1, 0) & lop2;
            (*rop).size = if limb(rop, 0) == 0 { 0 } else { 1 }
        }
        Ordering::Less => {
            *limb_mut(rop, 0) = limb(op1, 0).wrapping_neg() & lop2;
            (*rop).size = if limb(rop, 0) == 0 { 0 } else { 1 }
        }
    }
}

pub unsafe fn bitor_ui(rop: *mut mpz_t, op1: *const mpz_t, op2: c_ulong) {
    let lop2 = gmp::limb_t::from(op2);
    match (*op1).size.cmp(&0) {
        Ordering::Equal => if op2 == 0 {
            (*rop).size = 0;
        } else {
            *limb_mut(rop, 0) = lop2;
            (*rop).size = 1;
        },
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
        Ordering::Equal => if op2 == 0 {
            (*rop).size = 0;
        } else {
            *limb_mut(rop, 0) = lop2;
            (*rop).size = 1;
        },
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
                    *limb_mut(rop, 0) = lop2;
                    (*rop).size = 1;
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
        Ordering::Greater => if op2 >= 0 {
            *limb_mut(rop, 0) = limb(op1, 0) & lop2;
            (*rop).size = if limb(rop, 0) == 0 { 0 } else { 1 }
        } else {
            gmp::mpz_set(rop, op1);
            *limb_mut(rop, 0) &= lop2;
            if (*rop).size == 1 && limb(rop, 0) == 0 {
                (*rop).size = 0;
            }
        },
        Ordering::Less => if op2 >= 0 {
            *limb_mut(rop, 0) = limb(op1, 0).wrapping_neg() & lop2;
            (*rop).size = if limb(rop, 0) == 0 { 0 } else { 1 }
        } else {
            gmp::mpz_com(rop, op1);
            if (*rop).size == 0 {
                if !lop2 != 0 {
                    *limb_mut(rop, 0) = !lop2;
                    (*rop).size = 1;
                }
            } else {
                *limb_mut(rop, 0) |= !lop2;
            }
            gmp::mpz_com(rop, rop);
        },
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
        Ordering::Greater => if op2 >= 0 {
            gmp::mpz_set(rop, op1);
            *limb_mut(rop, 0) |= lop2;
        } else {
            *limb_mut(rop, 0) = !limb(op1, 0) & !lop2;
            (*rop).size = if limb(rop, 0) == 0 { 0 } else { 1 };
            gmp::mpz_com(rop, rop);
        },
        Ordering::Less => if op2 >= 0 {
            gmp::mpz_com(rop, op1);
            if (*rop).size != 0 {
                *limb_mut(rop, 0) &= !lop2;
                if (*rop).size == 1 && limb(rop, 0) == 0 {
                    (*rop).size = 0;
                }
            }
            gmp::mpz_com(rop, rop);
        } else {
            *limb_mut(rop, 0) = limb(op1, 0).wrapping_sub(1) & !lop2;
            (*rop).size = if limb(rop, 0) == 0 { 0 } else { 1 };
            gmp::mpz_com(rop, rop);
        },
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
        Ordering::Greater => if op2 >= 0 {
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
        },
        Ordering::Less => if op2 >= 0 {
            gmp::mpz_com(rop, op1);
            if (*rop).size == 0 {
                if lop2 != 0 {
                    *limb_mut(rop, 0) = lop2;
                    (*rop).size = 1;
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
                    *limb_mut(rop, 0) = !lop2;
                    (*rop).size = 1;
                }
            } else {
                *limb_mut(rop, 0) ^= !lop2;
                if (*rop).size == 1 && limb(rop, 0) == 0 {
                    (*rop).size = 0;
                }
            }
        },
    }
}

#[inline]
pub unsafe fn mpz_set_u64(rop: *mut mpz_t, u: u64) {
    #[cfg(gmp_limb_bits_64)]
    {
        if u == 0 {
            (*rop).size = 0;
        } else {
            (*rop).size = 1;
            *limb_mut(rop, 0) = cast(u);
        }
    }
    #[cfg(gmp_limb_bits_32)]
    {
        if u == 0 {
            (*rop).size = 0;
        } else if u <= 0xffff_ffff {
            (*rop).size = 1;
            *limb_mut(rop, 0) = cast(u);
        } else {
            gmp::_mpz_realloc(rop, 2);
            (*rop).size = 2;
            *limb_mut(rop, 0) = cast(u as u32);
            *limb_mut(rop, 1) = cast((u >> 32) as u32);
        }
    }
}

#[inline]
pub unsafe fn mpz_set_i64(rop: *mut mpz_t, i: i64) {
    mpz_set_u64(rop, i.wrapping_abs() as u64);
    if i < 0 {
        (*rop).size = -(*rop).size;
    }
}

#[inline]
pub unsafe fn mpz_set_u32(rop: *mut mpz_t, u: u32) {
    if u == 0 {
        (*rop).size = 0;
    } else {
        (*rop).size = 1;
        *limb_mut(rop, 0) = u.into();
    }
}

#[inline]
pub unsafe fn mpz_set_i32(rop: *mut mpz_t, i: i32) {
    mpz_set_u32(rop, i.wrapping_abs() as u32);
    if i < 0 {
        (*rop).size = -(*rop).size;
    }
}

#[inline]
pub unsafe fn mpz_init_set_u64(rop: *mut mpz_t, u: u64) {
    if mem::size_of::<c_ulong>() >= mem::size_of::<u64>() {
        gmp::mpz_init_set_ui(rop, u as c_ulong);
    } else {
        gmp::mpz_init(rop);
        mpz_set_u64(rop, u);
    }
}

#[inline]
pub unsafe fn mpz_init_set_i64(rop: *mut mpz_t, i: i64) {
    if mem::size_of::<c_long>() >= mem::size_of::<i64>() {
        gmp::mpz_init_set_si(rop, i as c_long);
    } else {
        gmp::mpz_init(rop);
        mpz_set_i64(rop, i);
    }
}

#[inline]
pub unsafe fn mpz_get_abs_u64(op: *const mpz_t) -> u64 {
    #[cfg(gmp_limb_bits_64)]
    {
        match (*op).size {
            0 => 0,
            _ => limb(op, 0) as u64,
        }
    }
    #[cfg(gmp_limb_bits_32)]
    {
        match (*op).size {
            0 => 0,
            -1 | 1 => limb(op, 0) as u64,
            _ => (limb(op, 1) as u64) << 32 | limb(op, 0) as u64,
        }
    }
}

#[inline]
pub unsafe fn mpz_get_abs_u32(op: *const mpz_t) -> u32 {
    match (*op).size {
        0 => 0,
        _ => limb(op, 0) as u32,
    }
}

#[inline]
pub unsafe fn mpz_cmp_u64(op1: *const mpz_t, op2: u64) -> c_int {
    #[cfg(gmp_limb_bits_64)]
    {
        match (*op1).size {
            0 if op2 == 0 => 0,
            0 => -1,
            size if size < 0 => -1,
            1 => ord_int(limb(op1, 0).cmp(&cast::<_, gmp::limb_t>(op2))),
            _ => 1,
        }
    }
    #[cfg(gmp_limb_bits_32)]
    {
        let op1_u = match (*op1).size {
            0 => return if op2 == 0 { 0 } else { -1 },
            size if size < 0 => return -1,
            1 => limb(op1, 0) as u64,
            2 => (limb(op1, 1) as u64) << 32 | limb(op1, 0) as u64,
            _ => return 1,
        };
        ord_int(op1_u.cmp(&op2))
    }
}

#[inline]
pub unsafe fn mpz_cmp_i64(op1: *const mpz_t, op2: i64) -> c_int {
    let neg1 = (*op1).size < 0;
    #[cfg(gmp_limb_bits_64)]
    {
        match (*op1).size {
            0 => ord_int(0.cmp(&op2)),
            -1 | 1 => {
                let mag1 = limb(op1, 0);
                let mag2: gmp::limb_t = cast(op2.wrapping_abs() as u64);
                match (neg1, op2 < 0) {
                    (false, false) => ord_int(mag1.cmp(&mag2)),
                    (false, true) => 1,
                    (true, false) => -1,
                    (true, true) => ord_int(mag2.cmp(&mag1)),
                }
            }
            _ if neg1 => -1,
            _ => 1,
        }
    }
    #[cfg(gmp_limb_bits_32)]
    {
        let mag1 = match (*op1).size {
            0 => 0,
            -1 | 1 => limb(op1, 0) as u64,
            -2 | 2 => (limb(op1, 1) as u64) << 32 | limb(op1, 0) as u64,
            _ => return if neg1 { -1 } else { 1 },
        };
        let ord = match (neg1, op2 < 0) {
            (false, false) => mag1.cmp(&(op2 as u64)),
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            (true, true) => (op2.wrapping_neg() as u64).cmp(&mag1),
        };
        ord_int(ord)
    }
}

#[inline]
pub unsafe fn mpz_cmp_u32(op1: *const mpz_t, op2: u32) -> c_int {
    match (*op1).size {
        0 if op2 == 0 => 0,
        0 => -1,
        size if size < 0 => -1,
        1 => ord_int(limb(op1, 0).cmp(&gmp::limb_t::from(op2))),
        _ => 1,
    }
}

#[inline]
pub unsafe fn mpz_cmp_i32(op1: *const mpz_t, op2: i32) -> c_int {
    let neg1 = (*op1).size < 0;
    match (*op1).size {
        0 => ord_int(0.cmp(&op2)),
        -1 | 1 => {
            let mag1 = limb(op1, 0);
            let mag2: gmp::limb_t = cast(op2.wrapping_abs() as u32);
            match (neg1, op2 < 0) {
                (false, false) => ord_int(mag1.cmp(&mag2)),
                (false, true) => 1,
                (true, false) => -1,
                (true, true) => ord_int(mag2.cmp(&mag1)),
            }
        }
        _ if neg1 => -1,
        _ => 1,
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
pub unsafe fn mpz_fits_u32(op: *const mpz_t) -> bool {
    #[cfg(gmp_limb_bits_64)]
    match (*op).size {
        0 => true,
        1 => limb(op, 0) <= gmp::limb_t::from(u32::MAX),
        _ => false,
    }
    #[cfg(gmp_limb_bits_32)]
    match (*op).size {
        0 | 1 => true,
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_fits_i32(op: *const mpz_t) -> bool {
    match (*op).size {
        0 => true,
        1 => limb(op, 0) <= gmp::limb_t::from(i32::MAX as u32),
        -1 => limb(op, 0) <= gmp::limb_t::from(i32::MIN as u32),
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_fits_u64(op: *const mpz_t) -> bool {
    #[cfg(gmp_limb_bits_64)]
    match (*op).size {
        0 | 1 => true,
        _ => false,
    }
    #[cfg(gmp_limb_bits_32)]
    match (*op).size {
        0 | 1 | 2 => true,
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_fits_i64(op: *const mpz_t) -> bool {
    #[cfg(gmp_limb_bits_64)]
    match (*op).size {
        0 => true,
        1 => limb(op, 0) <= gmp::limb_t::from(i64::MAX as u64),
        -1 => limb(op, 0) <= gmp::limb_t::from(i64::MIN as u64),
        _ => false,
    }
    #[cfg(gmp_limb_bits_32)]
    match (*op).size {
        0 | 1 | -1 => true,
        2 => limb(op, 1) <= gmp::limb_t::from(i32::MAX as u32),
        -2 => {
            limb(op, 1) < gmp::limb_t::from(i32::MIN as u32)
                || (limb(op, 1) == gmp::limb_t::from(i32::MIN as u32)
                    && limb(op, 0) == 0)
        }
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_addmul_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    if op2 >= 0 {
        gmp::mpz_addmul_ui(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpz_submul_ui(rop, op1, op2.wrapping_neg() as c_ulong);
    }
}

#[inline]
pub unsafe fn mpz_submul_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    if op2 >= 0 {
        gmp::mpz_submul_ui(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpz_addmul_ui(rop, op1, op2.wrapping_neg() as c_ulong);
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
        let abs_size = gmp::size_t::from((*op).size).wrapping_abs();
        let abs_popcount = gmp::mpn_popcount((*op).d, abs_size);
        let first_one = gmp::mpn_scan1((*op).d, 0);
        abs_popcount + first_one - 1
    }
}

pub unsafe fn mpz_next_pow_of_two(rop: *mut mpz_t, op: *const mpz_t) {
    let size = (*op).size;
    if size <= 0 {
        mpz_set_1(rop);
        return;
    }
    let significant: gmp::bitcnt_t =
        cast(gmp::mpn_sizeinbase((*op).d, cast(size), 2));
    let first_one = gmp::mpn_scan1((*op).d, 0);
    let bit = if significant - 1 == first_one {
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
unsafe fn limb(z: *const mpz_t, index: isize) -> gmp::limb_t {
    *((*z).d.offset(index))
}

#[inline]
unsafe fn limb_mut(z: *const mpz_t, index: isize) -> *mut gmp::limb_t {
    (*z).d.offset(index)
}

#[inline]
fn ord_int(o: Ordering) -> c_int {
    match o {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
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
        if op2 >= 0 {
            gmp::mpq_mul_2exp(rop, op1, op2 as c_ulong);
        } else {
            gmp::mpq_div_2exp(rop, op1, op2.wrapping_neg() as c_ulong);
        }
    }

    #[inline]
    pub unsafe fn mpq_div_2exp_si(
        rop: *mut mpq_t,
        op1: *const mpq_t,
        op2: c_long,
    ) {
        if op2 >= 0 {
            gmp::mpq_div_2exp(rop, op1, op2 as c_ulong);
        } else {
            gmp::mpq_mul_2exp(rop, op1, op2.wrapping_neg() as c_ulong);
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
        if op2 < 0 {
            assert_ne!(gmp::mpq_sgn(op1), 0, "division by zero");
            mpq_pow_ui(rop, op1, op2.wrapping_neg() as c_ulong);
            gmp::mpq_inv(rop, rop);
        } else {
            mpq_pow_ui(rop, op1, op2 as c_ulong);
        };
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
        let neg = gmp::mpz_sgn(num) < 0;
        // The remainder cannot be larger than the divisor, but we
        // allocate an extra limb because the GMP docs say we should,
        // and also because we have to multiply by 2.
        let limbs = cast::<_, gmp::bitcnt_t>((*den).size.abs()) + 1;
        let bits = limbs
            .checked_mul(cast::<_, gmp::bitcnt_t>(gmp::LIMB_BITS))
            .expect("overflow");
        let mut rem: mpz_t = mem::uninitialized();
        gmp::mpz_init2(&mut rem, bits);
        gmp::mpz_tdiv_qr(round, &mut rem, num, den);
        if neg {
            gmp::mpz_neg(&mut rem, &rem);
        }
        // if 2 * abs(rem) >= den, move one away from zero
        gmp::mpz_mul_2exp(&mut rem, &rem, 1);
        let away = gmp::mpz_cmp(&rem, den) >= 0;
        if away {
            if neg {
                gmp::mpz_sub_ui(round, round, 1);
            } else {
                gmp::mpz_add_ui(round, round, 1);
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
        let neg = gmp::mpz_sgn(num) < 0;
        gmp::mpz_tdiv_r(fract_num, num, den);
        if neg {
            gmp::mpz_neg(fract_num, fract_num);
        }
        gmp::mpz_set(fract_den, den);
        // if 2 * abs(rem) >= den, move one away from zero
        gmp::mpz_mul_2exp(fract_num, fract_num, 1);
        let away = gmp::mpz_cmp(fract_num, fract_den) >= 0;
        gmp::mpz_tdiv_q_2exp(fract_num, fract_num, 1);
        if away {
            gmp::mpz_sub(fract_num, fract_num, fract_den);
        }
        if neg {
            gmp::mpz_neg(fract_num, fract_num);
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
        let neg = gmp::mpz_sgn(num) < 0;
        gmp::mpz_tdiv_qr(round, fract_num, num, den);
        if neg {
            gmp::mpz_neg(fract_num, fract_num);
            gmp::mpz_neg(round, round);
        }
        gmp::mpz_set(fract_den, den);
        // if 2 * abs(rem) >= den, round away from zero
        gmp::mpz_mul_2exp(fract_num, fract_num, 1);
        let away = gmp::mpz_cmp(fract_num, fract_den) >= 0;
        gmp::mpz_tdiv_q_2exp(fract_num, fract_num, 1);
        if away {
            gmp::mpz_sub(fract_num, fract_num, fract_den);
            gmp::mpz_add_ui(round, round, 1);
        }
        if neg {
            gmp::mpz_neg(fract_num, fract_num);
            gmp::mpz_neg(round, round);
        }
    }

    #[inline]
    pub unsafe fn mpq_cmp_u64(op1: *const mpq_t, n2: u64, d2: u64) -> c_int {
        if mem::size_of::<c_ulong>() >= mem::size_of::<u64>() {
            gmp::mpq_cmp_ui(op1, n2 as c_ulong, d2 as c_ulong)
        } else {
            let small = SmallRational::from((n2, d2));
            gmp::mpq_cmp(op1, (*small).inner())
        }
    }

    #[inline]
    pub unsafe fn mpq_cmp_i64(op1: *const mpq_t, n2: i64, d2: i64) -> c_int {
        if mem::size_of::<c_long>() >= mem::size_of::<i64>() {
            gmp::mpq_cmp_si(op1, n2 as c_long, d2 as c_ulong)
        } else {
            let small = SmallRational::from((n2, d2));
            gmp::mpq_cmp(op1, (*small).inner())
        }
    }
}
