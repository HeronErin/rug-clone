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

#[cfg(int_128)]
use ext::gmp::mpz_set_i128;
use ext::gmp::{mpz_limb, mpz_limb_mut, mpz_set_i64, ord_int};
use gmp_mpfr_sys::gmp::{self, mpz_t};
use misc::NegAbs;
#[cfg(int_128)]
use std::i128;
use std::os::raw::c_int;
use std::{i32, i64, u32, u64};

#[cfg(int_128)]
#[inline]
pub fn set_u128(rop: &mut Integer, u: u128) {
    if u == 0 {
        set_0(rop);
    } else if u <= u128::from(u32::MAX) {
        set_nonzero(rop, u as u32);
    } else if u <= u128::from(u64::MAX) {
        unsafe {
            if rop.inner().alloc < 2 {
                gmp::_mpz_realloc(rop.as_raw_mut(), 2);
            }
            rop.inner_mut().size = 2;
            *limb_mut(rop, 0) = u as u32;
            *limb_mut(rop, 1) = (u >> 32) as u32;
        }
    } else if u <= 0xffff_ffff_ffff_ffff_ffff_ffff {
        unsafe {
            if rop.inner().alloc < 3 {
                gmp::_mpz_realloc(rop.as_raw_mut(), 3);
            }
            rop.inner_mut().size = 3;
            *limb_mut(rop, 0) = u as u32;
            *limb_mut(rop, 1) = (u >> 32) as u32;
            *limb_mut(rop, 2) = (u >> 64) as u32;
        }
    } else {
        unsafe {
            if rop.inner().alloc < 4 {
                gmp::_mpz_realloc(rop.as_raw_mut(), 4);
            }
            rop.inner_mut().size = 4;
            *limb_mut(rop, 0) = u as u32;
            *limb_mut(rop, 1) = (u >> 32) as u32;
            *limb_mut(rop, 2) = (u >> 64) as u32;
            *limb_mut(rop, 3) = (u >> 96) as u32;
        }
    }
}

#[inline]
pub fn set_u64(rop: &mut Integer, u: u64) {
    if u == 0 {
        set_0(rop);
    } else if u <= u64::from(u32::MAX) {
        set_nonzero(rop, u as u32);
    } else {
        unsafe {
            if rop.inner().alloc < 2 {
                gmp::_mpz_realloc(rop.as_raw_mut(), 2);
            }
            rop.inner_mut().size = 2;
            *limb_mut(rop, 0) = u as u32;
            *limb_mut(rop, 1) = (u >> 32) as u32;
        }
    }
}

#[inline]
pub fn set_u32(rop: &mut Integer, u: u32) {
    if u == 0 {
        set_0(rop);
    } else {
        set_nonzero(rop, u);
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
pub fn init_set_u64(rop: &mut Integer, u: u64) {
    unsafe {
        gmp::mpz_init2(rop.as_raw_mut(), 64);
    }
    set_u64(rop, u);
}

#[inline]
pub fn init_set_i64(rop: &mut Integer, i: i64) {
    unsafe {
        gmp::mpz_init2(rop.as_raw_mut(), 64);
    }
    set_i64(rop, i);
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

#[cfg(int_128)]
#[inline]
pub unsafe fn mpz_get_abs_u128(op: *const mpz_t) -> u128 {
    match (*op).size {
        0 => 0,
        -1 | 1 => u128::from(mpz_limb(op, 0)),
        -2 | 2 => {
            u128::from(mpz_limb(op, 1)) << 32 | u128::from(mpz_limb(op, 0))
        }
        -3 | 3 => {
            u128::from(mpz_limb(op, 2)) << 64
                | u128::from(mpz_limb(op, 1)) << 32
                | u128::from(mpz_limb(op, 0))
        }
        _ => {
            u128::from(mpz_limb(op, 3)) << 96
                | u128::from(mpz_limb(op, 2)) << 64
                | u128::from(mpz_limb(op, 1)) << 32
                | u128::from(mpz_limb(op, 0))
        }
    }
}

#[inline]
pub unsafe fn mpz_get_abs_u64(op: *const mpz_t) -> u64 {
    match (*op).size {
        0 => 0,
        -1 | 1 => u64::from(mpz_limb(op, 0)),
        _ => u64::from(mpz_limb(op, 1)) << 32 | u64::from(mpz_limb(op, 0)),
    }
}

#[inline]
pub unsafe fn mpz_get_abs_u32(op: *const mpz_t) -> u32 {
    match (*op).size {
        0 => 0,
        _ => mpz_limb(op, 0),
    }
}

#[cfg(int_128)]
#[inline]
pub unsafe fn mpz_cmp_u128(op1: *const mpz_t, op2: u128) -> c_int {
    if (*op1).size > 4 {
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
    if (*op1).size > 4 {
        return 1;
    }
    if (*op1).size < -4 {
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
    if (*op1).size > 2 {
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
    if (*op1).size > 2 {
        return 1;
    }
    if (*op1).size < -2 {
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
    if (*op1).size > 1 {
        return 1;
    }
    if (*op1).size < 0 {
        return -1;
    }
    let abs1 = mpz_get_abs_u32(op1);
    ord_int(abs1.cmp(&op2))
}

#[inline]
pub unsafe fn mpz_cmp_i32(op1: *const mpz_t, op2: i32) -> c_int {
    if (*op1).size > 1 {
        return 1;
    }
    if (*op1).size < -1 {
        return -1;
    }
    let neg1 = (*op1).size < 0;
    let abs1 = mpz_get_abs_u32(op1);
    let (neg2, abs2) = op2.neg_abs();
    match (neg1, neg2) {
        (false, false) => ord_int(abs1.cmp(&abs2)),
        (false, true) => 1,
        (true, false) => -1,
        (true, true) => ord_int(abs2.cmp(&abs1)),
    }
}

#[inline]
pub fn fits_u32(op: &Integer) -> bool {
    match op.inner().size {
        0 | 1 => true,
        _ => false,
    }
}

#[inline]
pub fn fits_i32(op: &Integer) -> bool {
    match op.inner().size {
        0 => true,
        1 => (unsafe { limb(op, 0) }) <= i32::MAX as u32,
        -1 => (unsafe { limb(op, 0) }) <= i32::MIN as u32,
        _ => false,
    }
}

#[inline]
pub fn fits_u64(op: &Integer) -> bool {
    match op.inner().size {
        0 | 1 | 2 => true,
        _ => false,
    }
}

#[inline]
pub fn fits_i64(op: &Integer) -> bool {
    match op.inner().size {
        0 | 1 | -1 => true,
        2 => (unsafe { limb(op, 1) }) <= i32::MAX as u32,
        -2 => {
            (unsafe { limb(op, 1) }) < i32::MIN as u32
                || ((unsafe { limb(op, 1) }) == i32::MIN as u32
                    && (unsafe { limb(op, 0) }) == 0)
        }
        _ => false,
    }
}

#[cfg(int_128)]
#[inline]
pub fn fits_u128(op: &Integer) -> bool {
    match op.inner().size {
        0 | 1 | 2 | 3 | 4 => true,
        _ => false,
    }
}

#[cfg(int_128)]
#[inline]
pub fn fits_i128(op: &Integer) -> bool {
    match op.inner().size {
        0 | 1 | -1 | 2 | -2 | 3 | -3 => true,
        4 => (unsafe { limb(op, 3) }) <= i32::MAX as u32,
        -4 => {
            (unsafe { limb(op, 3) }) < i32::MIN as u32
                || ((unsafe { limb(op, 3) }) == i32::MIN as u32
                    && (unsafe { limb(op, 2) }) == 0
                    && (unsafe { limb(op, 1) }) == 0
                    && (unsafe { limb(op, 0) }) == 0)
        }
        _ => false,
    }
}
