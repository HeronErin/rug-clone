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

use ext::gmp::{limb, limb_mut, ord_int, mpz_set_i64};
use gmp_mpfr_sys::gmp::{self, mpz_t};
use std::{i32, i64};
use std::os::raw::c_int;

#[inline]
pub unsafe fn mpz_set_u64(rop: *mut mpz_t, u: u64) {
    if u == 0 {
        (*rop).size = 0;
    } else if u <= 0xffff_ffff {
        (*rop).size = 1;
        *limb_mut(rop, 0) = u as u32;
    } else {
        gmp::_mpz_realloc(rop, 2);
        (*rop).size = 2;
        *limb_mut(rop, 0) = u as u32;
        *limb_mut(rop, 1) = (u >> 32) as u32;
    }
}

#[inline]
pub unsafe fn mpz_set_u32(rop: *mut mpz_t, u: u32) {
    if u == 0 {
        (*rop).size = 0;
    } else {
        (*rop).size = 1;
        *limb_mut(rop, 0) = u;
    }
}

#[inline]
pub unsafe fn mpz_init_set_u64(rop: *mut mpz_t, u: u64) {
    gmp::mpz_init(rop);
    mpz_set_u64(rop, u);
}

#[inline]
pub unsafe fn mpz_init_set_i64(rop: *mut mpz_t, i: i64) {
    gmp::mpz_init(rop);
    mpz_set_i64(rop, i);
}

#[inline]
pub unsafe fn mpz_get_abs_u64(op: *const mpz_t) -> u64 {
    match (*op).size {
        0 => 0,
        -1 | 1 => limb(op, 0) as u64,
        _ => (limb(op, 1) as u64) << 32 | limb(op, 0) as u64,
    }
}

#[inline]
pub unsafe fn mpz_get_abs_u32(op: *const mpz_t) -> u32 {
    match (*op).size {
        0 => 0,
        _ => limb(op, 0),
    }
}

#[inline]
pub unsafe fn mpz_cmp_u64(op1: *const mpz_t, op2: u64) -> c_int {
    match (*op1).size {
        0 if op2 == 0 => 0,
        0 => -1,
        size if size < 0 => -1,
        1 => ord_int((limb(op1, 0) as u64).cmp(&op2)),
        2 => {
            let op1_u = (limb(op1, 1) as u64) << 32 | limb(op1, 0) as u64;
            ord_int(op1_u.cmp(&op2))
        }
        _ => 1,
    }
}

#[inline]
pub unsafe fn mpz_cmp_i64(op1: *const mpz_t, op2: i64) -> c_int {
    let neg1 = (*op1).size < 0;
    let mag1 = match (*op1).size {
        0 => 0,
        -1 | 1 => limb(op1, 0) as u64,
        -2 | 2 => (limb(op1, 1) as u64) << 32 | limb(op1, 0) as u64,
        _ => return if neg1 { -1 } else { 1 },
    };
    let mag2 = op2.wrapping_abs() as u64;
    match (neg1, op2 < 0) {
        (false, false) => ord_int(mag1.cmp(&mag2)),
        (false, true) => 1,
        (true, false) => -1,
        (true, true) => ord_int(mag2.cmp(&mag1)),
    }
}

#[inline]
pub unsafe fn mpz_cmp_u32(op1: *const mpz_t, op2: u32) -> c_int {
    match (*op1).size {
        0 if op2 == 0 => 0,
        0 => -1,
        size if size < 0 => -1,
        1 => ord_int(limb(op1, 0).cmp(&op2)),
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
            let mag2 = op2.wrapping_abs() as u32;
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
pub unsafe fn mpz_fits_u32(op: *const mpz_t) -> bool {
    match (*op).size {
        0 | 1 => true,
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_fits_i32(op: *const mpz_t) -> bool {
    match (*op).size {
        0 => true,
        1 => limb(op, 0) <= i32::MAX as u32,
        -1 => limb(op, 0) <= i32::MIN as u32,
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_fits_u64(op: *const mpz_t) -> bool {
    match (*op).size {
        0 | 1 | 2 => true,
        _ => false,
    }
}

#[inline]
pub unsafe fn mpz_fits_i64(op: *const mpz_t) -> bool {
    match (*op).size {
        0 | 1 | -1 => true,
        2 => limb(op, 1) <= i32::MAX as u32,
        -2 => {
            limb(op, 1) < i32::MIN as u32
                || (limb(op, 1) == i32::MIN as u32 && limb(op, 0) == 0)
        }
        _ => false,
    }
}

#[cfg(feature = "rational")]
pub use self::rational::*;
#[cfg(feature = "rational")]
mod rational {
    use super::*;
    use gmp_mpfr_sys::gmp::mpq_t;
    use rational::SmallRational;

    #[inline]
    pub unsafe fn mpq_cmp_u32(op1: *const mpq_t, n2: u32, d2: u32) -> c_int {
        gmp::mpq_cmp_ui(op1, n2, d2)
    }

    #[inline]
    pub unsafe fn mpq_cmp_u64(op1: *const mpq_t, n2: u64, d2: u64) -> c_int {
        let small = SmallRational::from((n2, d2));
        gmp::mpq_cmp(op1, (*small).inner())
    }

    #[inline]
    pub unsafe fn mpq_cmp_i64(op1: *const mpq_t, n2: i64, d2: u64) -> c_int {
        let small = SmallRational::from((n2, d2));
        gmp::mpq_cmp(op1, (*small).inner())
    }
}
