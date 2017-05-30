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

pub unsafe fn mpz_tdiv_qr_check_0(q: *mut mpz_t,
                                  r: *mut mpz_t,
                                  dividend: *const mpz_t,
                                  divisor: *const mpz_t) {
    assert_ne!(gmp::mpz_sgn(divisor), 0, "division by zero");
    gmp::mpz_tdiv_qr(q, r, dividend, divisor);
}

pub unsafe fn mpz_divexact_check_0(q: *mut mpz_t,
                                   dividend: *const mpz_t,
                                   divisor: *const mpz_t) {
    assert_ne!(gmp::mpz_sgn(divisor), 0, "division by zero");
    gmp::mpz_divexact(q, dividend, divisor);
}

pub unsafe fn mpz_tdiv_q_check_0(q: *mut mpz_t,
                                 dividend: *const mpz_t,
                                 divisor: *const mpz_t) {
    assert_ne!(gmp::mpz_sgn(divisor), 0, "division by zero");
    gmp::mpz_tdiv_q(q, dividend, divisor);
}

pub unsafe fn mpz_tdiv_r_check_0(q: *mut mpz_t,
                                 dividend: *const mpz_t,
                                 divisor: *const mpz_t) {
    assert_ne!(gmp::mpz_sgn(divisor), 0, "division by zero");
    gmp::mpz_tdiv_r(q, dividend, divisor);
}

pub unsafe fn mpz_tdiv_q_ui_check_0(q: *mut mpz_t,
                                    dividend: *const mpz_t,
                                    divisor: c_ulong) {
    assert_ne!(divisor, 0, "division by zero");
    gmp::mpz_tdiv_q_ui(q, dividend, divisor);
}

pub unsafe fn mpz_ui_tdiv_q_check_0(q: *mut mpz_t,
                                    dividend: c_ulong,
                                    divisor: *const mpz_t) {
    let sgn_divisor = gmp::mpz_sgn(divisor);
    assert_ne!(sgn_divisor, 0, "division by zero");
    if gmp::mpz_cmpabs_ui(divisor, dividend) > 0 {
        gmp::mpz_set_ui(q, 0);
    } else {
        let ui = dividend / gmp::mpz_get_ui(divisor);
        gmp::mpz_set_ui(q, ui);
        if sgn_divisor < 0 {
            gmp::mpz_neg(q, q);
        }
    }
}

pub unsafe fn mpz_tdiv_r_ui_check_0(q: *mut mpz_t,
                                    dividend: *const mpz_t,
                                    divisor: c_ulong) {
    assert_ne!(divisor, 0, "division by zero");
    gmp::mpz_tdiv_r_ui(q, dividend, divisor);
}

pub unsafe fn mpz_ui_tdiv_r_check_0(q: *mut mpz_t,
                                    dividend: c_ulong,
                                    divisor: *const mpz_t) {
    assert_ne!(gmp::mpz_sgn(divisor), 0, "division by zero");
    if gmp::mpz_cmpabs_ui(divisor, dividend) > 0 {
        gmp::mpz_set_ui(q, dividend);
    } else {
        let ui = dividend % gmp::mpz_get_ui(divisor);
        gmp::mpz_set_ui(q, ui);
    }
}

pub unsafe fn mpz_tdiv_q_si_check_0(q: *mut mpz_t,
                                    dividend: *const mpz_t,
                                    divisor: c_long) {
    let neg = divisor < 0;
    mpz_tdiv_q_ui_check_0(q, dividend, divisor.wrapping_abs() as c_ulong);
    if neg {
        gmp::mpz_neg(q, q);
    }
}

pub unsafe fn mpz_si_tdiv_q_check_0(q: *mut mpz_t,
                                    dividend: c_long,
                                    divisor: *const mpz_t) {
    let neg = dividend < 0;
    mpz_ui_tdiv_q_check_0(q, dividend.wrapping_abs() as c_ulong, divisor);
    if neg {
        gmp::mpz_neg(q, q);
    }
}

pub unsafe fn mpz_tdiv_r_si_check_0(q: *mut mpz_t,
                                    dividend: *const mpz_t,
                                    divisor: c_long) {
    mpz_tdiv_r_ui_check_0(q, dividend, divisor.wrapping_abs() as c_ulong);
}

pub unsafe fn mpz_si_tdiv_r_check_0(q: *mut mpz_t,
                                    dividend: c_long,
                                    divisor: *const mpz_t) {
    let neg = dividend < 0;
    mpz_ui_tdiv_r_check_0(q, dividend.wrapping_abs() as c_ulong, divisor);
    if neg {
        gmp::mpz_neg(q, q);
    }
}

pub unsafe fn mpz_invert_check_0(inv: *mut mpz_t,
                                 n: *const mpz_t,
                                 m: *const mpz_t)
                                 -> c_int {
    assert_ne!(gmp::mpz_sgn(m), 0, "division by zero");
    gmp::mpz_invert(inv, n, m)
}

pub unsafe fn mpz_add_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    if op2 >= 0 {
        gmp::mpz_add_ui(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpz_sub_ui(rop, op1, op2.wrapping_neg() as c_ulong);
    }
}

pub unsafe fn mpz_sub_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    if op2 >= 0 {
        gmp::mpz_sub_ui(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpz_add_ui(rop, op1, op2.wrapping_neg() as c_ulong);
    }
}

pub unsafe fn mpz_si_sub(rop: *mut mpz_t, op1: c_long, op2: *const mpz_t) {
    if op1 >= 0 {
        gmp::mpz_ui_sub(rop, op1 as c_ulong, op2);
    } else {
        gmp::mpz_neg(rop, op2);
        gmp::mpz_sub_ui(rop, rop, op1.wrapping_neg() as c_ulong);
    }
}

pub unsafe fn mpz_lshift_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    if op2 >= 0 {
        gmp::mpz_mul_2exp(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpz_fdiv_q_2exp(rop, op1, op2.wrapping_neg() as c_ulong);
    }
}

pub unsafe fn mpz_rshift_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    if op2 >= 0 {
        gmp::mpz_fdiv_q_2exp(rop, op1, op2 as c_ulong);
    } else {
        gmp::mpz_mul_2exp(rop, op1, op2.wrapping_neg() as c_ulong);
    }
}

pub unsafe fn bitand_ui(rop: *mut mpz_t, op1: *const mpz_t, op2: c_ulong) {
    assert!(mem::size_of::<c_long>() <= mem::size_of::<gmp::limb_t>());
    let lop2 = op2 as gmp::limb_t;
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
    assert!(mem::size_of::<c_long>() <= mem::size_of::<gmp::limb_t>());
    let lop2 = op2 as gmp::limb_t;
    match (*op1).size.cmp(&0) {
        Ordering::Equal => {
            if op2 == 0 {
                (*rop).size = 0;
            } else {
                *rop.limb_mut(0) = lop2;
                (*rop).size = 1;
            }
        }
        Ordering::Greater => {
            gmp::mpz_set(rop, op1);
            *rop.limb_mut(0) |= lop2;
        }
        Ordering::Less => {
            gmp::mpz_com(rop, op1);
            *rop.limb_mut(0) &= !lop2;
            if (*rop).size == 1 && rop.limb(0) == 0 {
                (*rop).size = 0;
            }
            gmp::mpz_com(rop, rop);
        }
    }
}

pub unsafe fn bitxor_ui(rop: *mut mpz_t, op1: *const mpz_t, op2: c_ulong) {
    assert!(mem::size_of::<c_long>() <= mem::size_of::<gmp::limb_t>());
    let lop2 = op2 as gmp::limb_t;
    match (*op1).size.cmp(&0) {
        Ordering::Equal => {
            if op2 == 0 {
                (*rop).size = 0;
            } else {
                *rop.limb_mut(0) = lop2;
                (*rop).size = 1;
            }
        }
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
    assert!(mem::size_of::<c_long>() <= mem::size_of::<gmp::limb_t>());
    let lop2 = if op2 >= 0 {
        op2 as gmp::limb_t
    } else {
        !(!op2 as gmp::limb_t)
    };
    match (*op1).size.cmp(&0) {
        Ordering::Equal => {
            (*rop).size = 0;
        }
        Ordering::Greater if op2 >= 0 => {
            *rop.limb_mut(0) = op1.limb(0) & lop2;
            (*rop).size = if rop.limb(0) == 0 { 0 } else { 1 }
        }
        Ordering::Greater => {
            gmp::mpz_set(rop, op1);
            *rop.limb_mut(0) &= lop2;
            if (*rop).size == 1 && rop.limb(0) == 0 {
                (*rop).size = 0;
            }
        }
        Ordering::Less if op2 >= 0 => {
            *rop.limb_mut(0) = op1.limb(0).wrapping_neg() & lop2;
            (*rop).size = if rop.limb(0) == 0 { 0 } else { 1 }
        }
        Ordering::Less => {
            gmp::mpz_com(rop, op1);
            *rop.limb_mut(0) |= !lop2;
            if (*rop).size == 0 && !lop2 != 0 {
                (*rop).size = 1;
            }
            gmp::mpz_com(rop, rop);
        }
    }
}

pub unsafe fn bitor_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    assert!(mem::size_of::<c_long>() <= mem::size_of::<gmp::limb_t>());
    let lop2 = if op2 >= 0 {
        op2 as gmp::limb_t
    } else {
        !(!op2 as gmp::limb_t)
    };
    match (*op1).size.cmp(&0) {
        Ordering::Equal => {
            gmp::mpz_set_si(rop, op2);
        }
        Ordering::Greater if op2 >= 0 => {
            gmp::mpz_set(rop, op1);
            *rop.limb_mut(0) |= lop2;
        }
        Ordering::Greater => {
            *rop.limb_mut(0) = !op1.limb(0) & !lop2;
            (*rop).size = if rop.limb(0) == 0 { 0 } else { 1 };
            gmp::mpz_com(rop, rop);
        }
        Ordering::Less if op2 >= 0 => {
            gmp::mpz_com(rop, op1);
            *rop.limb_mut(0) &= !lop2;
            if (*rop).size == 1 && rop.limb(0) == 0 {
                (*rop).size = 0;
            }
            gmp::mpz_com(rop, rop);
        }
        Ordering::Less => {
            *rop.limb_mut(0) = op1.limb(0).wrapping_sub(1) & !lop2;
            (*rop).size = if rop.limb(0) == 0 { 0 } else { 1 };
            gmp::mpz_com(rop, rop);
        }
    }
}

pub unsafe fn bitxor_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    assert!(mem::size_of::<c_long>() <= mem::size_of::<gmp::limb_t>());
    let lop2 = if op2 >= 0 {
        op2 as gmp::limb_t
    } else {
        !(!op2 as gmp::limb_t)
    };
    match (*op1).size.cmp(&0) {
        Ordering::Equal => {
            gmp::mpz_set_si(rop, op2);
        }
        Ordering::Greater if op2 >= 0 => {
            gmp::mpz_set(rop, op1);
            *rop.limb_mut(0) ^= lop2;
            if (*rop).size == 1 && rop.limb(0) == 0 {
                (*rop).size = 0;
            }
        }
        Ordering::Greater => {
            gmp::mpz_set(rop, op1);
            *rop.limb_mut(0) ^= !lop2;
            if (*rop).size == 1 && rop.limb(0) == 0 {
                (*rop).size = 0;
            }
            gmp::mpz_com(rop, rop);
        }
        Ordering::Less if op2 >= 0 => {
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
        Ordering::Less => {
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
        }
    }
}

pub unsafe fn mpz_get_abs_u64(op: *const mpz_t) -> u64 {
    match (*op).size {
        0 => 0,
        -1 | 1 => op.limb(0) as u64,
        _ if gmp::LIMB_BITS >= 64 => op.limb(0) as u64,
        _ if gmp::LIMB_BITS == 32 => {
            op.limb(0) as u64 | ((op.limb(1) as u64) << 32)
        }
        _ => unreachable!(),
    }
}

pub unsafe fn mpz_cmp_u64(op1: *const mpz_t, op2: u64) -> c_int {
    if gmp::LIMB_BITS >= 64 {
        match (*op1).size {
            0 => if op2 == 0 { 0 } else { -1 },
            neg if neg < 0 => -1,
            1 => {
                match op1.limb(0).cmp(&(op2 as gmp::limb_t)) {
                    Ordering::Less => -1,
                    Ordering::Equal => 0,
                    Ordering::Greater => 1,
                }
            }
            _ => 1,
        }
    } else if gmp::LIMB_BITS == 32 {
        let val = match (*op1).size {
            0 => return if op2 == 0 { 0 } else { -1 },
            neg if neg < 0 => return -1,
            1 => op1.limb(0) as u64,
            2 => op1.limb(0) as u64 | ((op1.limb(1) as u64) << 32),
            _ => return 1,
        };
        match val.cmp(&op2) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    } else {
        unreachable!()
    }
}

pub unsafe fn mpz_cmp_i64(op1: *const mpz_t, op2: i64) -> c_int {
    let ord = if gmp::LIMB_BITS >= 64 {
        match (*op1).size {
            0 => 0.cmp(&op2),
            size @ -1 | size @ 1 => {
                let mag = op1.limb(0);
                if size < 0 {
                    if op2 >= 0 {
                        return -1;
                    }
                    // both are negative
                    (op2.wrapping_neg() as u64 as gmp::limb_t).cmp(&mag)
                } else {
                    if op2 < 0 {
                        return 1;
                    }
                    // both are positive
                    mag.cmp(&(op2 as gmp::limb_t))
                }
            }
            neg if neg < 0 => return -1,
            _ => return 1,
        }
    } else if gmp::LIMB_BITS == 32 {
        let (sign, mag) = match (*op1).size {
            0 => (false, 0),
            size @ -1 | size @ 1 => (size < 0, op1.limb(0) as u64),
            size @ -2 | size @ 2 => {
                (size < 0, op1.limb(0) as u64 | ((op1.limb(1) as u64) << 32))
            }
            neg if neg < 0 => return -1,
            _ => return 1,
        };
        if sign {
            if op2 >= 0 {
                return -1;
            }
            // both are negative
            (op2.wrapping_neg() as u64).cmp(&mag)
        } else {
            if op2 < 0 {
                return 1;
            }
            // both are positive
            mag.cmp(&(op2 as u64))
        }
    } else {
        unreachable!()
    };
    match ord {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}

pub unsafe fn mpz_fits_u32(op: *const mpz_t) -> bool {
    match (*op).size {
        0 => true,
        1 if gmp::LIMB_BITS >= 32 => op.limb(0) <= u32::MAX as gmp::limb_t,
        _ if gmp::LIMB_BITS >= 32 => false,
        _ => unreachable!(),
    }
}

pub unsafe fn mpz_fits_i32(op: *const mpz_t) -> bool {
    match (*op).size {
        0 => true,
        1 if gmp::LIMB_BITS >= 32 => {
            op.limb(0) <= i32::MAX as u32 as gmp::limb_t
        }
        -1 if gmp::LIMB_BITS >= 32 => {
            op.limb(0) <= i32::MIN as u32 as gmp::limb_t
        }
        _ if gmp::LIMB_BITS >= 32 => false,
        _ => unreachable!(),
    }
}

pub unsafe fn mpz_fits_u64(op: *const mpz_t) -> bool {
    match (*op).size {
        0 => true,
        1 if gmp::LIMB_BITS >= 64 => op.limb(0) <= u64::MAX as gmp::limb_t,
        1 if gmp::LIMB_BITS == 32 => true,
        2 if gmp::LIMB_BITS >= 64 => false,
        2 if gmp::LIMB_BITS == 32 => true,
        _ if gmp::LIMB_BITS >= 32 => false,
        _ => unreachable!(),
    }
}

pub unsafe fn mpz_fits_i64(op: *const mpz_t) -> bool {
    match (*op).size {
        0 => true,
        1 if gmp::LIMB_BITS >= 64 => {
            op.limb(0) <= i64::MAX as u64 as gmp::limb_t
        }
        -1 if gmp::LIMB_BITS >= 64 => {
            op.limb(0) <= i64::MIN as u64 as gmp::limb_t
        }
        1 | -1 if gmp::LIMB_BITS == 32 => true,
        2 | -2 if gmp::LIMB_BITS >= 64 => false,
        2 if gmp::LIMB_BITS == 32 => {
            op.limb(1) <= i32::MAX as u32 as gmp::limb_t
        }
        -2 if gmp::LIMB_BITS == 32 => {
            op.limb(1) <= i32::MIN as u32 as gmp::limb_t
        }
        _ if gmp::LIMB_BITS >= 32 => false,
        _ => unreachable!(),
    }
}

pub unsafe fn mpz_addmul_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    if op2 >= 0 {
        gmp::mpz_addmul_ui(rop, op1, op2 as c_ulong)
    } else {
        gmp::mpz_submul_ui(rop, op1, op2.wrapping_neg() as c_ulong)
    }
}

pub unsafe fn mpz_submul_si(rop: *mut mpz_t, op1: *const mpz_t, op2: c_long) {
    if op2 >= 0 {
        gmp::mpz_submul_ui(rop, op1, op2 as c_ulong)
    } else {
        gmp::mpz_addmul_ui(rop, op1, op2.wrapping_neg() as c_ulong)
    }
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
    unsafe fn limb(self, index: c_int) -> gmp::limb_t {
        *((*self).d.offset(index as isize))
    }
}

trait LimbMut {
    unsafe fn limb_mut(self, index: c_int) -> *mut gmp::limb_t;
}

impl LimbMut for *mut mpz_t {
    unsafe fn limb_mut(self, index: c_int) -> *mut gmp::limb_t {
        (*self).d.offset(index as isize)
    }
}
