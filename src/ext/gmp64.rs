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
// this program. If not, see <https://www.gnu.org/licenses/>.

use cast;
#[cfg(int_128)]
use ext::gmp::mpz_set_i128;
use ext::gmp::{limb, limb_mut, mpz_set_i64, ord_int};
use gmp_mpfr_sys::gmp::{self, mpz_t};
use misc::NegAbs;
#[cfg(int_128)]
use std::i128;
use std::os::raw::c_int;
use std::{i32, i64, u32};

#[cfg(int_128)]
#[inline]
pub unsafe fn mpz_set_u128(rop: *mut mpz_t, u: u128) {
    if u == 0 {
        (*rop).size = 0;
    } else if u <= 0xffff_ffff_ffff_ffff {
        if (*rop).alloc < 1 {
            gmp::_mpz_realloc(rop, 1);
        }
        (*rop).size = 1;
        *limb_mut(rop, 0) = u as u64;
    } else {
        if (*rop).alloc < 2 {
            gmp::_mpz_realloc(rop, 2);
        }
        (*rop).size = 2;
        *limb_mut(rop, 0) = u as u64;
        *limb_mut(rop, 1) = (u >> 64) as u64;
    }
}

#[inline]
pub unsafe fn mpz_set_u64(rop: *mut mpz_t, u: u64) {
    if u == 0 {
        (*rop).size = 0;
    } else {
        if (*rop).alloc < 1 {
            gmp::_mpz_realloc(rop, 1);
        }
        (*rop).size = 1;
        *limb_mut(rop, 0) = u;
    }
}

#[inline]
pub unsafe fn mpz_set_u32(rop: *mut mpz_t, u: u32) {
    if u == 0 {
        (*rop).size = 0;
    } else {
        if (*rop).alloc < 1 {
            gmp::_mpz_realloc(rop, 1);
        }
        (*rop).size = 1;
        *limb_mut(rop, 0) = u64::from(u);
    }
}

#[cfg(int_128)]
#[inline]
pub unsafe fn mpz_init_set_u128(rop: *mut mpz_t, u: u128) {
    gmp::mpz_init2(rop, 128);
    mpz_set_u128(rop, u);
}

#[cfg(int_128)]
#[inline]
pub unsafe fn mpz_init_set_i128(rop: *mut mpz_t, i: i128) {
    gmp::mpz_init2(rop, 128);
    mpz_set_i128(rop, i);
}

#[inline]
pub unsafe fn mpz_init_set_u64(rop: *mut mpz_t, u: u64) {
    if let Some(u) = cast::checked_cast(u) {
        gmp::mpz_init_set_ui(rop, u);
    } else {
        gmp::mpz_init2(rop, 64);
        mpz_set_u64(rop, u);
    }
}

#[inline]
pub unsafe fn mpz_init_set_i64(rop: *mut mpz_t, i: i64) {
    if let Some(i) = cast::checked_cast(i) {
        gmp::mpz_init_set_si(rop, i);
    } else {
        gmp::mpz_init2(rop, 64);
        mpz_set_i64(rop, i);
    }
}

#[cfg(int_128)]
#[inline]
pub unsafe fn mpz_get_abs_u128(op: *const mpz_t) -> u128 {
    match (*op).size {
        0 => 0,
        -1 | 1 => u128::from(limb(op, 0)),
        _ => u128::from(limb(op, 1)) << 64 | u128::from(limb(op, 0)),
    }
}

#[inline]
pub unsafe fn mpz_get_abs_u64(op: *const mpz_t) -> u64 {
    match (*op).size {
        0 => 0,
        _ => limb(op, 0),
    }
}

#[inline]
pub unsafe fn mpz_get_abs_u32(op: *const mpz_t) -> u32 {
    match (*op).size {
        0 => 0,
        _ => limb(op, 0) as u32,
    }
}

#[cfg(int_128)]
#[inline]
pub unsafe fn mpz_cmp_u128(op1: *const mpz_t, op2: u128) -> c_int {
    if (*op1).size > 2 {
        return 1;
    }
    if (*op1).size < 0 {
        return -1;
    }
    let abs1 = mpz_get_abs_u128(op1);
    ord_int(abs1.cmp(&op2))
}

#[cfg(int_128)]
#[inline]
pub unsafe fn mpz_cmp_i128(op1: *const mpz_t, op2: i128) -> c_int {
    if (*op1).size > 2 {
        return 1;
    }
    if (*op1).size < -2 {
        return -1;
    }
    let neg1 = (*op1).size < 0;
    let abs1 = mpz_get_abs_u128(op1);
    let (neg2, abs2) = op2.neg_abs();
    match (neg1, neg2) {
        (false, false) => ord_int(abs1.cmp(&abs2)),
        (false, true) => 1,
        (true, false) => -1,
        (true, true) => ord_int(abs2.cmp(&abs1)),
    }
}

#[inline]
pub unsafe fn mpz_cmp_u64(op1: *const mpz_t, op2: u64) -> c_int {
    if (*op1).size > 1 {
        return 1;
    }
    if (*op1).size < 0 {
        return -1;
    }
    let abs1 = mpz_get_abs_u64(op1);
    ord_int(abs1.cmp(&op2))
}

#[inline]
pub unsafe fn mpz_cmp_i64(op1: *const mpz_t, op2: i64) -> c_int {
    if (*op1).size > 1 {
        return 1;
    }
    if (*op1).size < -1 {
        return -1;
    }
    let neg1 = (*op1).size < 0;
    let abs1 = mpz_get_abs_u64(op1);
    let (neg2, abs2) = op2.neg_abs();
    match (neg1, neg2) {
        (false, false) => ord_int(abs1.cmp(&abs2)),
        (false, true) => 1,
        (true, false) => -1,
        (true, true) => ord_int(abs2.cmp(&abs1)),
    }
}

#[inline]
pub unsafe fn mpz_cmp_u32(op1: *const mpz_t, op2: u32) -> c_int {
    match (*op1).size {
        0 if op2 == 0 => 0,
        0 => -1,
        size if size < 0 => -1,
        1 => ord_int(limb(op1, 0).cmp(&u64::from(op2))),
        _ => 1,
    }
}

#[inline]
pub unsafe fn mpz_cmp_i32(op1: *const mpz_t, op2: i32) -> c_int {
    let neg1 = (*op1).size < 0;
    match (*op1).size {
        0 => ord_int(0.cmp(&op2)),
        -1 | 1 => {
            let abs1 = limb(op1, 0);
            let (neg2, abs2) = op2.neg_abs();
            let abs2 = u64::from(abs2);
            match (neg1, neg2) {
                (false, false) => ord_int(abs1.cmp(&abs2)),
                (false, true) => 1,
                (true, false) => -1,
                (true, true) => ord_int(abs2.cmp(&abs1)),
            }
        }
        _ if neg1 => -1,
        _ => 1,
    }
}

#[inline]
pub unsafe fn mpz_fits_u32(op: *const mpz_t) -> bool {
    match (*op).size {
        0 => true,
        1 => limb(op, 0) <= u64::from(u32::MAX),
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_fits_i32(op: *const mpz_t) -> bool {
    match (*op).size {
        0 => true,
        1 => limb(op, 0) <= u64::from(i32::MAX as u32),
        -1 => limb(op, 0) <= u64::from(i32::MIN as u32),
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_fits_u64(op: *const mpz_t) -> bool {
    match (*op).size {
        0 | 1 => true,
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_fits_i64(op: *const mpz_t) -> bool {
    match (*op).size {
        0 => true,
        1 => limb(op, 0) <= i64::MAX as u64,
        -1 => limb(op, 0) <= i64::MIN as u64,
        _ => false,
    }
}

#[cfg(int_128)]
#[inline]
pub unsafe fn mpz_fits_u128(op: *const mpz_t) -> bool {
    match (*op).size {
        0 | 1 | 2 => true,
        _ => false,
    }
}

#[cfg(int_128)]
#[inline]
pub unsafe fn mpz_fits_i128(op: *const mpz_t) -> bool {
    match (*op).size {
        0 | 1 | -1 => true,
        2 => limb(op, 1) <= i64::MAX as u64,
        -2 => {
            limb(op, 1) < i64::MIN as u64
                || (limb(op, 1) == i64::MIN as u64 && limb(op, 0) == 0)
        }
        _ => false,
    }
}
