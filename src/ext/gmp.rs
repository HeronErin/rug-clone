// Copyright © 2017 University of Malta

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

use gmp_mpfr_sys::gmp::{self, mpz_t};
use std::{i32, i64, u32, u64};
use std::cmp::Ordering;
use std::mem;
use std::os::raw::{c_int, c_long, c_ulong};

#[inline]
pub unsafe fn mpz_tdiv_qr_check_0(
    q: *mut mpz_t,
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_tdiv_qr(q, r, n, d);
}

#[inline]
pub unsafe fn mpz_tdiv_q_check_0(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_tdiv_q(q, n, d);
}

#[inline]
pub unsafe fn mpz_tdiv_r_check_0(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_tdiv_r(r, n, d);
}

#[inline]
pub unsafe fn mpz_tdiv_q_ui_check_0(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    assert_ne!(d, 0, "division by zero");
    gmp::mpz_tdiv_q_ui(q, n, d)
}

#[inline]
pub unsafe fn mpz_tdiv_r_ui_check_0(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    assert_ne!(d, 0, "division by zero");
    gmp::mpz_tdiv_r_ui(r, n, d)
}

#[inline]
pub unsafe fn mpz_ui_tdiv_q_check_0(
    q: *mut mpz_t,
    n: c_ulong,
    d: *const mpz_t,
) -> c_ulong {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(d, n) > 0 {
        // n / +abs_d -> 0, n
        // n / -abs_d -> 0, n
        gmp::mpz_set_ui(q, 0);
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

#[inline]
pub unsafe fn mpz_ui_tdiv_r_check_0(
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
pub unsafe fn mpz_tdiv_q_si_check_0(q: *mut mpz_t, n: *const mpz_t, d: c_long) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    mpz_tdiv_q_ui_check_0(q, n, d.wrapping_abs() as c_ulong);
    if d < 0 {
        gmp::mpz_neg(q, q);
    }
}

#[inline]
pub unsafe fn mpz_tdiv_r_si_check_0(r: *mut mpz_t, n: *const mpz_t, d: c_long) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    mpz_tdiv_r_ui_check_0(r, n, d.wrapping_abs() as c_ulong);
}

#[inline]
pub unsafe fn mpz_si_tdiv_q_check_0(q: *mut mpz_t, n: c_long, d: *const mpz_t) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    mpz_ui_tdiv_q_check_0(q, n.wrapping_abs() as c_ulong, d);
    if n < 0 {
        gmp::mpz_neg(q, q);
    }
}

#[inline]
pub unsafe fn mpz_si_tdiv_r_check_0(r: *mut mpz_t, n: c_long, d: *const mpz_t) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r
    mpz_ui_tdiv_r_check_0(r, n.wrapping_abs() as c_ulong, d);
    if n < 0 {
        gmp::mpz_neg(r, r);
    }
}

#[inline]
pub unsafe fn mpz_cdiv_qr_check_0(
    q: *mut mpz_t,
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_cdiv_qr(q, r, n, d);
}

#[inline]
pub unsafe fn mpz_cdiv_q_check_0(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_cdiv_q(q, n, d);
}

#[inline]
pub unsafe fn mpz_cdiv_r_check_0(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_cdiv_r(r, n, d);
}

#[inline]
pub unsafe fn mpz_cdiv_q_ui_check_0(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    assert_ne!(d, 0, "division by zero");
    gmp::mpz_cdiv_q_ui(q, n, d)
}

#[inline]
pub unsafe fn mpz_cdiv_r_ui_check_0(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    assert_ne!(d, 0, "division by zero");
    gmp::mpz_cdiv_r_ui(r, n, d)
}

#[inline]
pub unsafe fn mpz_ui_cdiv_q_check_0(
    q: *mut mpz_t,
    n: c_ulong,
    d: *const mpz_t,
) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(d, n) > 0 {
        // n / +abs_d -> 0, n + if n > 0 { 1, -abs_d }
        // n / -abs_d -> 0, n
        if n > 0 && sgn_d > 0 {
            gmp::mpz_set_ui(q, 1);
        } else {
            gmp::mpz_set_ui(q, 0);
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

#[inline]
pub unsafe fn mpz_ui_cdiv_r_check_0(
    r: *mut mpz_t,
    n: c_ulong,
    d: *const mpz_t,
) {
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
            gmp::mpz_set_ui(r, 0);
        }
    }
}

#[inline]
pub unsafe fn mpz_cdiv_q_si_check_0(q: *mut mpz_t, n: *const mpz_t, d: c_long) {
    // +abs_n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r + if abs_r > 0 { 1, +abs_d }
    let some_r = mpz_cdiv_q_ui_check_0(q, n, d.wrapping_abs() as c_ulong) != 0;
    if d < 0 {
        if some_r {
            gmp::mpz_ui_sub(q, 1, q);
        } else {
            gmp::mpz_neg(q, q);
        }
    }
}

#[inline]
pub unsafe fn mpz_cdiv_r_si_check_0(r: *mut mpz_t, n: *const mpz_t, d: c_long) {
    // +abs_n / +abs_d -> +abs_q, +abs_r + if abs_r > 0 { 1, -abs_d }
    // +abs_n / -abs_d -> -abs_q, +abs_r
    // -abs_n / +abs_d -> -abs_q, -abs_r
    // -abs_n / -abs_d -> +abs_q, -abs_r + if abs_r > 0 { 1, +abs_d }
    let some_r = mpz_cdiv_r_ui_check_0(r, n, d.wrapping_abs() as c_ulong) != 0;
    if d < 0 && some_r {
        mpz_sub_si(r, r, d);
    }
}

#[inline]
pub unsafe fn mpz_si_cdiv_q_check_0(q: *mut mpz_t, n: c_long, d: *const mpz_t) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(d, n.wrapping_abs() as c_ulong) > 0 {
        // +abs_n / +abs_d -> 0, +abs_n + if abs_n > 0 { 1, -abs_d }
        // +abs_n / -abs_d -> 0, +abs_n
        // -abs_n / +abs_d -> 0, -abs_n
        // -abs_n / -abs_d -> 0, -abs_n + if abs_n > 0 { 1, +abs_d }
        if (n > 0 && sgn_d > 0) || (n < 0 && sgn_d < 0) {
            gmp::mpz_set_ui(q, 1);
        } else {
            gmp::mpz_set_ui(q, 0);
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

#[inline]
pub unsafe fn mpz_si_cdiv_r_check_0(r: *mut mpz_t, n: c_long, d: *const mpz_t) {
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
            gmp::mpz_set_ui(r, 0);
        }
    }
}

#[inline]
pub unsafe fn mpz_fdiv_qr_check_0(
    q: *mut mpz_t,
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_fdiv_qr(q, r, n, d);
}

#[inline]
pub unsafe fn mpz_fdiv_q_check_0(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_fdiv_q(q, n, d);
}

#[inline]
pub unsafe fn mpz_fdiv_r_check_0(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(d), 0, "division by zero");
    gmp::mpz_fdiv_r(r, n, d);
}

#[inline]
pub unsafe fn mpz_fdiv_q_ui_check_0(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    assert_ne!(d, 0, "division by zero");
    gmp::mpz_fdiv_q_ui(q, n, d)
}

#[inline]
pub unsafe fn mpz_fdiv_r_ui_check_0(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    assert_ne!(d, 0, "division by zero");
    gmp::mpz_fdiv_r_ui(r, n, d)
}

#[inline]
pub unsafe fn mpz_ui_fdiv_q_check_0(
    q: *mut mpz_t,
    n: c_ulong,
    d: *const mpz_t,
) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(d, n) > 0 {
        // n / +abs_d -> 0, n
        // n / -abs_d -> 0, n + if n > 0 { -1, -abs_d }
        if n > 0 && sgn_d < 0 {
            gmp::mpz_set_si(q, -1);
        } else {
            gmp::mpz_set_ui(q, 0);
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

#[inline]
pub unsafe fn mpz_ui_fdiv_r_check_0(
    r: *mut mpz_t,
    n: c_ulong,
    d: *const mpz_t,
) {
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
            gmp::mpz_set_ui(r, 0);
        }
    }
}

#[inline]
pub unsafe fn mpz_fdiv_q_si_check_0(q: *mut mpz_t, n: *const mpz_t, d: c_long) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
    // -abs_n / +abs_d -> -abs_q, -abs_r + if abs_r > 0 { -1, +abs_d }
    // -abs_n / -abs_d -> +abs_q, -abs_r
    let some_r = mpz_fdiv_q_ui_check_0(q, n, d.wrapping_abs() as c_ulong) != 0;
    if d < 0 {
        if some_r {
            mpz_si_sub(q, -1, q);
        } else {
            gmp::mpz_neg(q, q);
        }
    }
}

#[inline]
pub unsafe fn mpz_fdiv_r_si_check_0(r: *mut mpz_t, n: *const mpz_t, d: c_long) {
    // +abs_n / +abs_d -> +abs_q, +abs_r
    // +abs_n / -abs_d -> -abs_q, +abs_r + if abs_r > 0 { -1, -abs_d }
    // -abs_n / +abs_d -> -abs_q, -abs_r + if abs_r > 0 { -1, +abs_d }
    // -abs_n / -abs_d -> +abs_q, -abs_r
    let some_r = mpz_fdiv_r_ui_check_0(r, n, d.wrapping_abs() as c_ulong) != 0;
    if d < 0 && some_r {
        mpz_add_si(r, r, d);
    }
}

#[inline]
pub unsafe fn mpz_si_fdiv_q_check_0(q: *mut mpz_t, n: c_long, d: *const mpz_t) {
    let sgn_d = gmp::mpz_sgn(d);
    assert_ne!(sgn_d, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(d, n.wrapping_abs() as c_ulong) > 0 {
        // +abs_n / +abs_d -> 0, +abs_n
        // +abs_n / -abs_d -> 0, +abs_n + if abs_n > 0 { -1, -abs_d }
        // -abs_n / +abs_d -> 0, -abs_n + if abs_n > 0 { -1, +abs_d }
        // -abs_n / -abs_d -> 0, -abs_n
        if (n > 0 && sgn_d < 0) || (n < 0 && sgn_d > 0) {
            gmp::mpz_set_si(q, -1);
        } else {
            gmp::mpz_set_ui(q, 0);
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

#[inline]
pub unsafe fn mpz_si_fdiv_r_check_0(r: *mut mpz_t, n: c_long, d: *const mpz_t) {
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
            gmp::mpz_set_ui(r, 0);
        }
    }
}

#[inline]
pub unsafe fn mpz_ediv_qr_check_0(
    q: *mut mpz_t,
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_cdiv_qr_check_0(q, r, n, d);
    } else {
        mpz_fdiv_qr_check_0(q, r, n, d);
    }
}

#[inline]
pub unsafe fn mpz_ediv_q_check_0(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_cdiv_q_check_0(q, n, d);
    } else {
        mpz_fdiv_q_check_0(q, n, d);
    }
}

#[inline]
pub unsafe fn mpz_ediv_r_check_0(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: *const mpz_t,
) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_cdiv_r_check_0(r, n, d);
    } else {
        mpz_fdiv_r_check_0(r, n, d);
    }
}

#[inline]
pub unsafe fn mpz_ediv_q_ui_check_0(
    q: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    mpz_fdiv_q_ui_check_0(q, n, d)
}

#[inline]
pub unsafe fn mpz_ediv_r_ui_check_0(
    r: *mut mpz_t,
    n: *const mpz_t,
    d: c_ulong,
) -> c_ulong {
    mpz_fdiv_r_ui_check_0(r, n, d)
}

#[inline]
pub unsafe fn mpz_ui_ediv_q_check_0(
    q: *mut mpz_t,
    n: c_ulong,
    d: *const mpz_t,
) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_ui_cdiv_q_check_0(q, n, d);
    } else {
        mpz_ui_fdiv_q_check_0(q, n, d);
    }
}

#[inline]
pub unsafe fn mpz_ui_ediv_r_check_0(
    r: *mut mpz_t,
    n: c_ulong,
    d: *const mpz_t,
) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_ui_cdiv_r_check_0(r, n, d);
    } else {
        mpz_ui_fdiv_r_check_0(r, n, d);
    }
}

#[inline]
pub unsafe fn mpz_ediv_q_si_check_0(q: *mut mpz_t, n: *const mpz_t, d: c_long) {
    if d < 0 {
        mpz_cdiv_q_si_check_0(q, n, d);
    } else {
        mpz_fdiv_q_si_check_0(q, n, d);
    }
}

#[inline]
pub unsafe fn mpz_ediv_r_si_check_0(r: *mut mpz_t, n: *const mpz_t, d: c_long) {
    if d < 0 {
        mpz_cdiv_r_si_check_0(r, n, d);
    } else {
        mpz_fdiv_r_si_check_0(r, n, d);
    }
}

#[inline]
pub unsafe fn mpz_si_ediv_q_check_0(q: *mut mpz_t, n: c_long, d: *const mpz_t) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_si_cdiv_q_check_0(q, n, d);
    } else {
        mpz_si_fdiv_q_check_0(q, n, d);
    }
}

#[inline]
pub unsafe fn mpz_si_ediv_r_check_0(r: *mut mpz_t, n: c_long, d: *const mpz_t) {
    if gmp::mpz_sgn(d) < 0 {
        mpz_si_cdiv_r_check_0(r, n, d);
    } else {
        mpz_si_fdiv_r_check_0(r, n, d);
    }
}

#[inline]
pub unsafe fn mpz_divexact_check_0(
    q: *mut mpz_t,
    dividend: *const mpz_t,
    divisor: *const mpz_t,
) {
    assert_ne!(gmp::mpz_sgn(divisor), 0, "division by zero");
    gmp::mpz_divexact(q, dividend, divisor);
}

#[inline]
pub unsafe fn mpz_divexact_ui_check_0(
    q: *mut mpz_t,
    dividend: *const mpz_t,
    divisor: c_ulong,
) {
    assert_ne!(divisor, 0, "division by zero");
    gmp::mpz_divexact_ui(q, dividend, divisor);
}

#[inline]
pub unsafe fn mpz_invert_check_0(
    inv: *mut mpz_t,
    n: *const mpz_t,
    m: *const mpz_t,
) -> c_int {
    assert_ne!(gmp::mpz_sgn(m), 0, "division by zero");
    gmp::mpz_invert(inv, n, m)
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

#[inline]
pub unsafe fn bitand_ui(rop: *mut mpz_t, op1: *const mpz_t, op2: c_ulong) {
    let lop2 = gmp::limb_t::from(op2);
    match (*op1).size.cmp(&0) {
        Ordering::Equal => {
            (*rop).size = 0;
        }
        Ordering::Greater => {
            *rop.limb_mut(0) = op1.limb(0) & lop2;
            (*rop).size = if rop.limb(0) == 0 { 0 } else { 1 }
        }
        Ordering::Less => {
            *rop.limb_mut(0) = op1.limb(0).wrapping_neg() & lop2;
            (*rop).size = if rop.limb(0) == 0 { 0 } else { 1 }
        }
    }
}

pub unsafe fn bitor_ui(rop: *mut mpz_t, op1: *const mpz_t, op2: c_ulong) {
    let lop2 = gmp::limb_t::from(op2);
    match (*op1).size.cmp(&0) {
        Ordering::Equal => if op2 == 0 {
            (*rop).size = 0;
        } else {
            *rop.limb_mut(0) = lop2;
            (*rop).size = 1;
        },
        Ordering::Greater => {
            gmp::mpz_set(rop, op1);
            *rop.limb_mut(0) |= lop2;
        }
        Ordering::Less => {
            gmp::mpz_com(rop, op1);
            if (*rop).size != 0 {
                *rop.limb_mut(0) &= !lop2;
                if (*rop).size == 1 && rop.limb(0) == 0 {
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
            *rop.limb_mut(0) = lop2;
            (*rop).size = 1;
        },
        Ordering::Greater => {
            gmp::mpz_set(rop, op1);
            *rop.limb_mut(0) ^= lop2;
            if (*rop).size == 1 && rop.limb(0) == 0 {
                (*rop).size = 0;
            }
        }
        Ordering::Less => {
            gmp::mpz_com(rop, op1);
            if (*rop).size == 0 {
                if lop2 != 0 {
                    *rop.limb_mut(0) = lop2;
                    (*rop).size = 1;
                }
            } else {
                *rop.limb_mut(0) ^= lop2;
                if (*rop).size == 1 && rop.limb(0) == 0 {
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
            *rop.limb_mut(0) = op1.limb(0) & lop2;
            (*rop).size = if rop.limb(0) == 0 { 0 } else { 1 }
        } else {
            gmp::mpz_set(rop, op1);
            *rop.limb_mut(0) &= lop2;
            if (*rop).size == 1 && rop.limb(0) == 0 {
                (*rop).size = 0;
            }
        },
        Ordering::Less => if op2 >= 0 {
            *rop.limb_mut(0) = op1.limb(0).wrapping_neg() & lop2;
            (*rop).size = if rop.limb(0) == 0 { 0 } else { 1 }
        } else {
            gmp::mpz_com(rop, op1);
            if (*rop).size == 0 {
                if !lop2 != 0 {
                    *rop.limb_mut(0) = !lop2;
                    (*rop).size = 1;
                }
            } else {
                *rop.limb_mut(0) |= !lop2;
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
            *rop.limb_mut(0) |= lop2;
        } else {
            *rop.limb_mut(0) = !op1.limb(0) & !lop2;
            (*rop).size = if rop.limb(0) == 0 { 0 } else { 1 };
            gmp::mpz_com(rop, rop);
        },
        Ordering::Less => if op2 >= 0 {
            gmp::mpz_com(rop, op1);
            if (*rop).size != 0 {
                *rop.limb_mut(0) &= !lop2;
                if (*rop).size == 1 && rop.limb(0) == 0 {
                    (*rop).size = 0;
                }
            }
            gmp::mpz_com(rop, rop);
        } else {
            *rop.limb_mut(0) = op1.limb(0).wrapping_sub(1) & !lop2;
            (*rop).size = if rop.limb(0) == 0 { 0 } else { 1 };
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
            *rop.limb_mut(0) ^= lop2;
            if (*rop).size == 1 && rop.limb(0) == 0 {
                (*rop).size = 0;
            }
        } else {
            gmp::mpz_set(rop, op1);
            *rop.limb_mut(0) ^= !lop2;
            if (*rop).size == 1 && rop.limb(0) == 0 {
                (*rop).size = 0;
            }
            gmp::mpz_com(rop, rop);
        },
        Ordering::Less => if op2 >= 0 {
            gmp::mpz_com(rop, op1);
            if (*rop).size == 0 {
                if lop2 != 0 {
                    *rop.limb_mut(0) = lop2;
                    (*rop).size = 1;
                }
            } else {
                *rop.limb_mut(0) ^= lop2;
                if (*rop).size == 1 && rop.limb(0) == 0 {
                    (*rop).size = 0;
                }
            }
            gmp::mpz_com(rop, rop);
        } else {
            gmp::mpz_com(rop, op1);
            if (*rop).size == 0 {
                if !lop2 != 0 {
                    *rop.limb_mut(0) = !lop2;
                    (*rop).size = 1;
                }
            } else {
                *rop.limb_mut(0) ^= !lop2;
                if (*rop).size == 1 && rop.limb(0) == 0 {
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
            *rop.limb_mut(0) = u as gmp::limb_t;
        }
    }
    #[cfg(gmp_limb_bits_32)]
    {
        if u == 0 {
            (*rop).size = 0;
        } else if u <= 0xffff_ffff {
            (*rop).size = 1;
            *rop.limb_mut(0) = u as gmp::limb_t;
        } else {
            gmp::_mpz_realloc(rop, 2);
            (*rop).size = 2;
            *rop.limb_mut(0) = u as u32 as gmp::limb_t;
            *rop.limb_mut(1) = (u >> 32) as u32 as gmp::limb_t;
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
        *rop.limb_mut(0) = u.into();
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
pub unsafe fn mpz_get_abs_u64(op: *const mpz_t) -> u64 {
    #[cfg(gmp_limb_bits_64)]
    {
        match (*op).size {
            0 => 0,
            _ => op.limb(0) as u64,
        }
    }
    #[cfg(gmp_limb_bits_32)]
    {
        match (*op).size {
            0 => 0,
            -1 | 1 => op.limb(0) as u64,
            _ => (op.limb(1) as u64) << 32 | op.limb(0) as u64,
        }
    }
}

#[inline]
pub unsafe fn mpz_get_abs_u32(op: *const mpz_t) -> u32 {
    match (*op).size {
        0 => 0,
        _ => op.limb(0) as u32,
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
            1 => op1.limb(0).cmp(&(op2 as gmp::limb_t)).to_c_int(),
            _ => 1,
        }
    }
    #[cfg(gmp_limb_bits_32)]
    {
        let op1_u = match (*op1).size {
            0 => return if op2 == 0 { 0 } else { -1 },
            size if size < 0 => return -1,
            1 => op1.limb(0) as u64,
            2 => (op1.limb(1) as u64) << 32 | op1.limb(0) as u64,
            _ => return 1,
        };
        op1_u.cmp(&op2).to_c_int()
    }
}

#[inline]
pub unsafe fn mpz_cmp_i64(op1: *const mpz_t, op2: i64) -> c_int {
    let neg1 = (*op1).size < 0;
    #[cfg(gmp_limb_bits_64)]
    {
        match (*op1).size {
            0 => 0.cmp(&op2).to_c_int(),
            -1 | 1 => {
                let mag1 = op1.limb(0);
                let mag2 = op2.wrapping_abs() as u64 as gmp::limb_t;
                match (neg1, op2 < 0) {
                    (false, false) => mag1.cmp(&mag2).to_c_int(),
                    (false, true) => 1,
                    (true, false) => -1,
                    (true, true) => mag2.cmp(&mag1).to_c_int(),
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
            -1 | 1 => op1.limb(0) as u64,
            -2 | 2 => (op1.limb(1) as u64) << 32 | op1.limb(0) as u64,
            _ => return if neg1 { -1 } else { 1 },
        };
        let ord = match (neg1, op2 < 0) {
            (false, false) => mag1.cmp(&(op2 as u64)),
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            (true, true) => (op2.wrapping_neg() as u64).cmp(&mag1),
        };
        ord.to_c_int()
    }
}

#[inline]
pub unsafe fn mpz_cmp_u32(op1: *const mpz_t, op2: u32) -> c_int {
    match (*op1).size {
        0 if op2 == 0 => 0,
        0 => -1,
        size if size < 0 => -1,
        1 => op1.limb(0).cmp(&gmp::limb_t::from(op2)).to_c_int(),
        _ => 1,
    }
}

#[inline]
pub unsafe fn mpz_cmp_i32(op1: *const mpz_t, op2: i32) -> c_int {
    let neg1 = (*op1).size < 0;
    match (*op1).size {
        0 => 0.cmp(&op2).to_c_int(),
        -1 | 1 => {
            let mag1 = op1.limb(0);
            let mag2 = gmp::limb_t::from(op2.wrapping_abs() as u32);
            match (neg1, op2 < 0) {
                (false, false) => mag1.cmp(&mag2).to_c_int(),
                (false, true) => 1,
                (true, false) => -1,
                (true, true) => mag2.cmp(&mag1).to_c_int(),
            }
        }
        _ if neg1 => -1,
        _ => 1,
    }
}

#[inline]
pub unsafe fn mpz_fits_u32(op: *const mpz_t) -> bool {
    #[cfg(gmp_limb_bits_64)]
    match (*op).size {
        0 => true,
        1 => op.limb(0) <= gmp::limb_t::from(u32::MAX),
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
        1 => op.limb(0) <= gmp::limb_t::from(i32::MAX as u32),
        -1 => op.limb(0) <= gmp::limb_t::from(i32::MIN as u32),
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
        1 => op.limb(0) <= gmp::limb_t::from(i64::MAX as u64),
        -1 => op.limb(0) <= gmp::limb_t::from(i64::MIN as u64),
        _ => false,
    }
    #[cfg(gmp_limb_bits_32)]
    match (*op).size {
        0 | 1 | -1 => true,
        2 => op.limb(1) <= gmp::limb_t::from(i32::MAX as u32),
        -2 => {
            op.limb(1) < gmp::limb_t::from(i32::MIN as u32)
                || (op.limb(1) == gmp::limb_t::from(i32::MIN as u32)
                    && op.limb(0) == 0)
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
        gmp::mpz_set_ui(rop, 1);
        return;
    }
    let significant_u = gmp::mpn_sizeinbase((*op).d, size.into(), 2);
    let significant = significant_u as gmp::bitcnt_t;
    assert_eq!(significant as usize, significant_u, "overflow");
    let first_one = gmp::mpn_scan1((*op).d, 0);
    let bit = if significant - 1 == first_one {
        if rop as *const mpz_t == op {
            return;
        }
        first_one
    } else {
        significant
    };
    gmp::mpz_set_ui(rop, 0);
    gmp::mpz_setbit(rop, bit);
}

trait Limb {
    unsafe fn limb(self, index: c_int) -> gmp::limb_t;
}

impl Limb for *const mpz_t {
    unsafe fn limb(self, index: c_int) -> gmp::limb_t {
        *((*self).d.offset(index as isize))
    }
}

impl Limb for *mut mpz_t {
    #[inline]
    unsafe fn limb(self, index: c_int) -> gmp::limb_t {
        *((*self).d.offset(index as isize))
    }
}

trait LimbMut {
    unsafe fn limb_mut(self, index: c_int) -> *mut gmp::limb_t;
}

impl LimbMut for *mut mpz_t {
    #[inline]
    unsafe fn limb_mut(self, index: c_int) -> *mut gmp::limb_t {
        (*self).d.offset(index as isize)
    }
}

trait ToCInt {
    fn to_c_int(self) -> c_int;
}
impl ToCInt for Ordering {
    #[inline]
    fn to_c_int(self) -> c_int {
        match self {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    }
}

#[cfg(feature = "rational")]
pub use self::rational::*;
#[cfg(feature = "rational")]
mod rational {
    use super::*;
    use gmp_mpfr_sys::gmp::mpq_t;

    #[inline]
    pub unsafe fn mpq_inv_check_0(rop: *mut mpq_t, op: *const mpq_t) {
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
    pub unsafe fn mpq_ceil(rop: *mut mpz_t, op: *const mpq_t) {
        let numref = gmp::mpq_numref_const(op);
        let denref = gmp::mpq_denref_const(op);
        num_den_ceil(rop, numref, denref);
    }

    #[inline]
    pub unsafe fn num_den_ceil(
        rop: *mut mpz_t,
        num: *const mpz_t,
        den: *const mpz_t,
    ) {
        if gmp::mpz_cmp_ui(den, 1) == 0 {
            gmp::mpz_set(rop, num);
        } else {
            gmp::mpz_tdiv_q(rop, num, den);
            if gmp::mpz_sgn(num) > 0 {
                gmp::mpz_add_ui(rop, rop, 1);
            }
        }
    }

    #[inline]
    pub unsafe fn mpq_floor(rop: *mut mpz_t, op: *const mpq_t) {
        let numref = gmp::mpq_numref_const(op);
        let denref = gmp::mpq_denref_const(op);
        num_den_floor(rop, numref, denref);
    }

    #[inline]
    pub unsafe fn num_den_floor(
        rop: *mut mpz_t,
        num: *const mpz_t,
        den: *const mpz_t,
    ) {
        if gmp::mpz_cmp_ui(den, 1) == 0 {
            gmp::mpz_set(rop, num);
        } else {
            gmp::mpz_tdiv_q(rop, num, den);
            if gmp::mpz_sgn(num) < 0 {
                gmp::mpz_sub_ui(rop, rop, 1);
            }
        }
    }

    #[inline]
    pub unsafe fn mpq_round(rop: *mut mpz_t, op: *const mpq_t) {
        let numref = gmp::mpq_numref_const(op);
        let denref = gmp::mpq_denref_const(op);
        num_den_round(rop, numref, denref);
    }

    pub unsafe fn num_den_round(
        rop: *mut mpz_t,
        num: *const mpz_t,
        den: *const mpz_t,
    ) {
        if gmp::mpz_cmp_ui(den, 1) == 0 {
            gmp::mpz_set(rop, num);
        } else {
            // The remainder cannot be larger than the divisor, but we
            // allocate an extra limb because the GMP docs say we should,
            // and we have to multiply by 2.
            let bits = (*den).size.checked_abs().expect("overflow");
            let bits = bits as gmp::bitcnt_t + 1;
            let bits = bits.checked_mul(gmp::LIMB_BITS as gmp::bitcnt_t)
                .expect("overflow");
            let mut rem: mpz_t = mem::uninitialized();
            gmp::mpz_init2(&mut rem, bits);
            gmp::mpz_tdiv_qr(rop, &mut rem, num, den);
            // if 2 * abs(rem) >= divisor, move one away from zero
            gmp::mpz_abs(&mut rem, &rem);
            gmp::mpz_mul_2exp(&mut rem, &rem, 1);
            if gmp::mpz_cmp(&rem, den) >= 0 {
                if gmp::mpz_sgn(num) > 0 {
                    gmp::mpz_add_ui(rop, rop, 1);
                } else {
                    gmp::mpz_sub_ui(rop, rop, 1);
                }
            }
            gmp::mpz_clear(&mut rem);
        }
    }

    #[inline]
    pub unsafe fn mpq_trunc(rop: *mut mpz_t, op: *const mpq_t) {
        let numref = gmp::mpq_numref_const(op);
        let denref = gmp::mpq_denref_const(op);
        num_den_trunc(rop, numref, denref);
    }

    #[inline]
    pub unsafe fn num_den_trunc(
        rop: *mut mpz_t,
        num: *const mpz_t,
        den: *const mpz_t,
    ) {
        gmp::mpz_tdiv_q(rop, num, den);
    }

    #[inline]
    pub unsafe fn mpq_fract(rop: *mut mpq_t, op: *const mpq_t) {
        let numref = gmp::mpq_numref_const(op);
        let denref = gmp::mpq_denref_const(op);
        num_den_fract(rop, numref, denref);
    }

    #[inline]
    pub unsafe fn num_den_fract(
        rop: *mut mpq_t,
        num: *const mpz_t,
        den: *const mpz_t,
    ) {
        let r_numref = gmp::mpq_numref(rop);
        let r_denref = gmp::mpq_denref(rop);
        gmp::mpz_tdiv_r(r_numref, num, den);
        gmp::mpz_set(r_denref, den);
    }

    #[inline]
    pub unsafe fn mpq_fract_trunc(
        fop: *mut mpq_t,
        trunc_op: *mut mpz_t,
        op: *const mpq_t,
    ) {
        let f_numref = gmp::mpq_numref(fop);
        let f_denref = gmp::mpq_denref(fop);
        let numref = gmp::mpq_numref_const(op);
        let denref = gmp::mpq_denref_const(op);
        gmp::mpz_tdiv_qr(trunc_op, f_numref, numref, denref);
        gmp::mpz_set(f_denref, denref);
    }

    #[inline]
    pub unsafe fn mpq_fract_floor(
        fop: *mut mpq_t,
        floor_op: *mut mpz_t,
        op: *const mpq_t,
    ) {
        let f_numref = gmp::mpq_numref(fop);
        let f_denref = gmp::mpq_denref(fop);
        let numref = gmp::mpq_numref_const(op);
        let denref = gmp::mpq_denref_const(op);
        gmp::mpz_fdiv_qr(floor_op, f_numref, numref, denref);
        gmp::mpz_set(f_denref, denref);
    }

    #[inline]
    pub unsafe fn mpq_fract_ceil(
        fop: *mut mpq_t,
        ceil_op: *mut mpz_t,
        op: *const mpq_t,
    ) {
        let f_numref = gmp::mpq_numref(fop);
        let f_denref = gmp::mpq_denref(fop);
        let numref = gmp::mpq_numref_const(op);
        let denref = gmp::mpq_denref_const(op);
        gmp::mpz_cdiv_qr(ceil_op, f_numref, numref, denref);
        gmp::mpz_set(f_denref, denref);
    }
}
