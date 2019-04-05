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
use ext::xmpz;
use gmp_mpfr_sys::gmp;
use misc::NegAbs;
use rational::SmallRational;
use std::cmp::Ordering;
use std::mem;
use std::os::raw::c_int;
use {Integer, Rational};

macro_rules! wrap {
    (fn $fn:ident($($op:ident),* $(; $param:ident: $T:ty)*) -> $deleg:path) => {
        #[inline]
        pub fn $fn(
            rop: &mut Rational,
            $($op: Option<&Rational>,)*
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

#[inline]
pub fn set(rop: &mut Rational, op: Option<&Rational>) {
    if let Some(op) = op {
        unsafe {
            gmp::mpq_set(rop.as_raw_mut(), op.as_raw());
        }
    }
}

#[inline]
pub unsafe fn clear(rop: &mut Rational) {
    gmp::mpq_clear(rop.as_raw_mut());
}

#[inline]
fn process_int_rat<F>(
    rint: Option<&mut Integer>,
    rrat: Option<&mut Rational>,
    op: Option<&Rational>,
    f: F,
) where
    F: FnOnce(&mut Integer, Option<&Integer>, &Integer),
{
    let (onum, oden) = match op {
        Some(r) => (Some(r.numer()), Some(r.denom())),
        None => (None, None),
    };
    if let Some(rrat) = rrat {
        let (rn, rd) = unsafe { rrat.as_mut_numer_denom_no_canonicalization() };
        f(rn, onum, oden.unwrap_or(rd));
        xmpz::set_1(rd);
    } else if let Some(rint) = rint {
        f(rint, onum, oden.expect("no denominator"));
    } else {
        panic!("no numerator");
    }
}

#[inline]
pub fn signum(
    rint: Option<&mut Integer>,
    rrat: Option<&mut Rational>,
    op: Option<&Rational>,
) {
    process_int_rat(rint, rrat, op, |r, n, _| xmpz::signum(r, n))
}

#[inline]
pub fn trunc(
    rint: Option<&mut Integer>,
    rrat: Option<&mut Rational>,
    op: Option<&Rational>,
) {
    process_int_rat(rint, rrat, op, |r, n, d| xmpz::tdiv_q(r, n, Some(d)));
}

#[inline]
pub fn ceil(
    rint: Option<&mut Integer>,
    rrat: Option<&mut Rational>,
    op: Option<&Rational>,
) {
    process_int_rat(rint, rrat, op, |r, n, d| {
        // use tdiv_q rather than cdiv_q to let GMP not keep remainder
        if xmpz::is_1(d) {
            xmpz::set(r, n);
        } else {
            let neg = n.unwrap_or(r).cmp0() == Ordering::Less;
            xmpz::tdiv_q(r, n, Some(d));
            if !neg {
                xmpz::add_u32(r, None, 1);
            }
        }
    });
}

#[inline]
pub fn floor(
    rint: Option<&mut Integer>,
    rrat: Option<&mut Rational>,
    op: Option<&Rational>,
) {
    process_int_rat(rint, rrat, op, |r, n, d| {
        // use tdiv_q rather than fdiv_q to let GMP not keep remainder
        if xmpz::is_1(d) {
            xmpz::set(r, n);
        } else {
            let neg = n.unwrap_or(r).cmp0() == Ordering::Less;
            xmpz::tdiv_q(r, n, Some(d));
            if neg {
                xmpz::sub_u32(r, None, 1);
            }
        }
    });
}

pub fn round(
    rint: Option<&mut Integer>,
    rrat: Option<&mut Rational>,
    op: Option<&Rational>,
) {
    process_int_rat(rint, rrat, op, |r, n, d| {
        // The remainder cannot be larger than the divisor, but we
        // allocate an extra limb because the GMP docs suggest we should.
        let limbs = cast::cast::<_, usize>(d.inner().size.abs()) + 1;
        let bits = limbs
            .checked_mul(cast::cast::<_, usize>(gmp::LIMB_BITS))
            .expect("overflow");
        let mut rem = Integer::with_capacity(bits);
        xmpz::tdiv_qr(r, &mut rem, n, Some(d));
        if xmpz::round_away(&rem, d) {
            if rem.cmp0() == Ordering::Less {
                // negative number
                xmpz::sub_u32(r, None, 1);
            } else {
                // positive number
                xmpz::add_u32(r, None, 1);
            }
        }
    });
}

#[inline]
pub fn inv(rop: &mut Rational, op: Option<&Rational>) {
    assert_ne!(op.unwrap_or(rop).cmp0(), Ordering::Equal, "division by zero");
    unsafe {
        gmp::mpq_inv(rop.as_raw_mut(), op.unwrap_or(rop).as_raw());
    }
}

#[inline]
pub fn trunc_fract(fract: &mut Rational, op: Option<&Rational>) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) =
        unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    xmpz::tdiv_r(fract_num, op_num, Some(fract_den));
}

#[inline]
pub fn ceil_fract(fract: &mut Rational, op: Option<&Rational>) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) =
        unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    xmpz::cdiv_r(fract_num, op_num, Some(fract_den));
}

#[inline]
pub fn floor_fract(fract: &mut Rational, op: Option<&Rational>) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) =
        unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    xmpz::fdiv_r(fract_num, op_num, Some(fract_den));
}

pub fn round_fract(fract: &mut Rational, op: Option<&Rational>) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) =
        unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    xmpz::tdiv_r(fract_num, op_num, Some(fract_den));
    if xmpz::round_away(fract_num, fract_den) {
        if fract_num.cmp0() == Ordering::Less {
            // negative number
            xmpz::add(fract_num, None, Some(fract_den));
        } else {
            // positive number
            xmpz::sub(fract_num, None, Some(fract_den));
        }
    }
}

#[inline]
pub fn square(rop: &mut Rational, op: Option<&Rational>) {
    unsafe {
        let (rop_num, rop_den) = rop.as_mut_numer_denom_no_canonicalization();
        let op_num = op.map(Rational::numer);
        let op_den = op.map(Rational::denom);
        xmpz::square(rop_num, op_num);
        xmpz::square(rop_den, op_den);
    }
}

wrap! { fn neg(op) -> gmp::mpq_neg }
wrap! { fn abs(op) -> gmp::mpq_abs }
wrap! { fn add(op1, op2) -> gmp::mpq_add }
wrap! { fn sub(op1, op2) -> gmp::mpq_sub }
wrap! { fn mul(op1, op2) -> gmp::mpq_mul }
wrap! { fn div(op1, op2) -> gmp::mpq_div }
wrap! { fn mul_2exp(op1; op2: u32) -> gmp::mpq_mul_2exp }
wrap! { fn div_2exp(op1; op2: u32) -> gmp::mpq_div_2exp }

#[inline]
pub fn set_0(rop: &mut Rational) {
    unsafe {
        let (num, den) = rop.as_mut_numer_denom_no_canonicalization();
        xmpz::set_0(num);
        xmpz::set_1(den);
    }
}

#[inline]
pub fn lshift_i32(rop: &mut Rational, op1: Option<&Rational>, op2: i32) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        mul_2exp(rop, op1, op2_abs);
    } else {
        div_2exp(rop, op1, op2_abs);
    }
}

#[inline]
pub fn rshift_i32(rop: &mut Rational, op1: Option<&Rational>, op2: i32) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    if !op2_neg {
        div_2exp(rop, op1, op2_abs);
    } else {
        mul_2exp(rop, op1, op2_abs);
    }
}

#[inline]
pub fn pow_u32(rop: &mut Rational, op1: Option<&Rational>, op2: u32) {
    unsafe {
        let (rop_num, rop_den) = rop.as_mut_numer_denom_no_canonicalization();
        let op1_num = op1.map(Rational::numer);
        let op1_den = op1.map(Rational::denom);
        xmpz::pow_u32(rop_num, op1_num, op2);
        xmpz::pow_u32(rop_den, op1_den, op2);
    }
}

#[inline]
pub fn pow_i32(rop: &mut Rational, op1: Option<&Rational>, op2: i32) {
    let (op2_neg, op2_abs) = op2.neg_abs();
    pow_u32(rop, op1, op2_abs);
    if !op2_neg {
        inv(rop, None);
    }
}

#[inline]
pub fn trunc_fract_whole(
    fract: &mut Rational,
    trunc: &mut Integer,
    op: Option<&Rational>,
) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) =
        unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    unsafe {
        gmp::mpz_tdiv_qr(
            trunc.as_raw_mut(),
            fract_num.as_raw_mut(),
            op_num.unwrap_or(fract_num).as_raw(),
            fract_den.as_raw(),
        );
    }
}

#[inline]
pub fn ceil_fract_whole(
    fract: &mut Rational,
    ceil: &mut Integer,
    op: Option<&Rational>,
) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) =
        unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    unsafe {
        gmp::mpz_cdiv_qr(
            ceil.as_raw_mut(),
            fract_num.as_raw_mut(),
            op_num.unwrap_or(fract_num).as_raw(),
            fract_den.as_raw(),
        );
    }
}

#[inline]
pub fn floor_fract_whole(
    fract: &mut Rational,
    floor: &mut Integer,
    op: Option<&Rational>,
) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) =
        unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    unsafe {
        gmp::mpz_fdiv_qr(
            floor.as_raw_mut(),
            fract_num.as_raw_mut(),
            op_num.unwrap_or(fract_num).as_raw(),
            fract_den.as_raw(),
        );
    }
}

pub fn round_fract_whole(
    fract: &mut Rational,
    round: &mut Integer,
    op: Option<&Rational>,
) {
    let op_num = op.map(Rational::numer);
    let op_den = op.map(Rational::denom);
    let (fract_num, fract_den) =
        unsafe { fract.as_mut_numer_denom_no_canonicalization() };
    xmpz::set(fract_den, op_den);
    unsafe {
        gmp::mpz_tdiv_qr(
            round.as_raw_mut(),
            fract_num.as_raw_mut(),
            op_num.unwrap_or(fract_num).as_raw(),
            fract_den.as_raw(),
        );
    }
    if xmpz::round_away(fract_num, fract_den) {
        if fract_num.cmp0() == Ordering::Less {
            // negative number
            xmpz::sub_u32(round, None, 1);
            xmpz::add(fract_num, None, Some(fract_den));
        } else {
            // positive number
            xmpz::add_u32(round, None, 1);
            xmpz::sub(fract_num, None, Some(fract_den));
        }
    }
}

#[inline]
fn ord(o: c_int) -> Ordering {
    o.cmp(&0)
}

#[inline]
pub fn cmp(op1: &Rational, op2: &Rational) -> Ordering {
    ord(unsafe { gmp::mpq_cmp(op1.as_raw(), op2.as_raw()) })
}

#[inline]
pub fn equal(op1: &Rational, op2: &Rational) -> bool {
    (unsafe { gmp::mpq_equal(op1.as_raw(), op2.as_raw()) }) != 0
}

#[inline]
pub fn cmp_z(op1: &Rational, op2: &Integer) -> Ordering {
    ord(unsafe { gmp::mpq_cmp_z(op1.as_raw(), op2.as_raw()) })
}

#[inline]
pub fn cmp_u32(op1: &Rational, n2: u32, d2: u32) -> Ordering {
    ord(unsafe { gmp::mpq_cmp_ui(op1.as_raw(), n2.into(), d2.into()) })
}

#[inline]
pub fn cmp_i32(op1: &Rational, n2: i32, d2: u32) -> Ordering {
    ord(unsafe { gmp::mpq_cmp_si(op1.as_raw(), n2.into(), d2.into()) })
}

#[inline]
pub fn cmp_u64(op1: &Rational, n2: u64, d2: u64) -> Ordering {
    if let Some(n2) = cast::checked_cast(n2) {
        if let Some(d2) = cast::checked_cast(d2) {
            return ord(unsafe { gmp::mpq_cmp_ui(op1.as_raw(), n2, d2) });
        }
    }
    let small = SmallRational::from((n2, d2));
    ord(unsafe { gmp::mpq_cmp(op1.as_raw(), (*small).as_raw()) })
}

#[inline]
pub fn cmp_i64(op1: &Rational, n2: i64, d2: u64) -> Ordering {
    if let Some(n2) = cast::checked_cast(n2) {
        if let Some(d2) = cast::checked_cast(d2) {
            return ord(unsafe { gmp::mpq_cmp_si(op1.as_raw(), n2, d2) });
        }
    }
    let small = SmallRational::from((n2, d2));
    ord(unsafe { gmp::mpq_cmp(op1.as_raw(), (*small).as_raw()) })
}

#[inline]
pub fn cmp_u128(op1: &Rational, n2: u128, d2: u128) -> Ordering {
    if let Some(n2) = cast::checked_cast(n2) {
        if let Some(d2) = cast::checked_cast(d2) {
            return ord(unsafe { gmp::mpq_cmp_ui(op1.as_raw(), n2, d2) });
        }
    }
    let small = SmallRational::from((n2, d2));
    ord(unsafe { gmp::mpq_cmp(op1.as_raw(), (*small).as_raw()) })
}

#[inline]
pub fn cmp_i128(op1: &Rational, n2: i128, d2: u128) -> Ordering {
    if let Some(n2) = cast::checked_cast(n2) {
        if let Some(d2) = cast::checked_cast(d2) {
            return ord(unsafe { gmp::mpq_cmp_si(op1.as_raw(), n2, d2) });
        }
    }
    let small = SmallRational::from((n2, d2));
    ord(unsafe { gmp::mpq_cmp(op1.as_raw(), (*small).as_raw()) })
}

pub fn cmp_finite_d(op1: &Rational, op2: f64) -> Ordering {
    let num1 = op1.numer();
    let den1 = op1.denom();
    let den1_bits = den1.significant_bits();
    // cmp(num1, op2 * den1)
    let cmp;
    unsafe {
        let mut op2_f = mem::uninitialized();
        gmp::mpf_init2(&mut op2_f, 53);
        gmp::mpf_set_d(&mut op2_f, op2);
        let mut rhs = mem::uninitialized();
        gmp::mpf_init2(&mut rhs, cast::cast(den1_bits + 53));
        gmp::mpf_set_z(&mut rhs, den1.as_raw());
        gmp::mpf_mul(&mut rhs, &rhs, &op2_f);
        cmp = -gmp::mpf_cmp_z(&rhs, num1.as_raw());
        gmp::mpf_clear(&mut rhs);
        gmp::mpf_clear(&mut op2_f);
    }
    ord(cmp)
}
