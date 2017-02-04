// Copyright © 2016–2017 University of Malta

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

use gmp_mpfr_sys::gmp;
use rugint::{Assign, DivFromAssign, Integer, NegAssign, Pow, PowAssign,
             SubFromAssign};
use std::cmp::Ordering;
use std::ffi::{CStr, CString};
use std::fmt;
use std::i32;
use std::mem;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl,
               ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::os::raw::c_void;
use std::ptr;
use std::str::FromStr;

/// An arbitrary-precision rational number.
///
/// A rational number is made up of a numerator `Integer` and
/// denominator `Integer`. After rational number functions, the number
/// is always in canonical form, that is, the denominator is always
/// greater than zero, and there are no common factors. Zero is stored
/// as 0/1.
///
/// # Examples
///
/// ```rust
/// extern crate rugint;
/// extern crate rugrat;
///
/// use rugint::Integer;
/// use rugrat::Rational;
///
/// fn main() {
///     let r = Rational::from((-12, 15));
///     let (num, den) = r.into_numer_denom();
///     assert!(num == -4);
///     assert!(den == 5);
///     let one = Rational::from((num, Integer::from(-4)));
///     assert!(one == 1);
/// }
/// ```
pub struct Rational {
    inner: gmp::mpq_t,
}

impl Drop for Rational {
    fn drop(&mut self) {
        unsafe {
            gmp::mpq_clear(&mut self.inner);
        }
    }
}

impl Default for Rational {
    fn default() -> Rational {
        Rational::new()
    }
}

impl Clone for Rational {
    fn clone(&self) -> Rational {
        let mut ret = Rational::new();
        ret.assign(self);
        ret
    }

    fn clone_from(&mut self, source: &Rational) {
        self.assign(source);
    }
}

impl Rational {
    /// Constructs a new arbitrary-precision rational number with value 0.
    pub fn new() -> Rational {
        let mut inner: gmp::mpq_t = unsafe { mem::uninitialized() };
        unsafe {
            gmp::mpq_init(&mut inner);
        }
        Rational { inner: inner }
    }

    /// Converts `self` to an `f64`, rounding towards zero.
    pub fn to_f64(&self) -> f64 {
        unsafe { gmp::mpq_get_d(&self.inner) }
    }

    /// Converts `self` to an `f32`, rounding towards zero.
    pub fn to_f32(&self) -> f32 {
        self.to_f64() as f32
    }

    /// Borrows the numerator.
    pub fn numer(&self) -> &Integer {
        unsafe {
            let ptr = gmp::mpq_numref(&self.inner as *const _ as *mut _);
            &*(ptr as *const Integer)
        }
    }

    /// Borrows the denominator.
    pub fn denom(&self) -> &Integer {
        unsafe {
            let ptr = gmp::mpq_denref(&self.inner as *const _ as *mut _);
            &*(ptr as *const Integer)
        }
    }

    /// Borrows the numerator and denominator.
    pub fn as_numer_denom(&self) -> (&Integer, &Integer) {
        (self.numer(), self.denom())
    }

    /// Borrows the numerator and denominator mutably. The number is
    /// canonicalized when the borrow ends. The denominator must not
    /// be zero when the borrow ends.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    ///
    /// let mut r = Rational::from((3, 5));
    /// {
    ///     let mut num_den = r.as_mut_numer_denom();
    ///     // change r from 3/5 to 4/8, which is equal to 1/2
    ///     *num_den.0 += 1;
    ///     *num_den.1 += 3;
    ///     // borrow ends here
    /// }
    /// let num_den = r.as_numer_denom();
    /// assert!(*num_den.0 == 1 && *num_den.1 == 2);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero when the borrow ends.
    pub fn as_mut_numer_denom(&mut self) -> MutNumerDenom {
        unsafe {
            let numer_ptr = gmp::mpq_numref(&mut self.inner);
            let denom_ptr = gmp::mpq_denref(&mut self.inner);
            MutNumerDenom(&mut *(numer_ptr as *mut Integer),
                          &mut *(denom_ptr as *mut Integer))
        }
    }

    /// Converts `self` into numerator and denominator integers,
    /// consuming `self`.
    pub fn into_numer_denom(mut self) -> (Integer, Integer) {
        let (mut numer, mut denom) = unsafe { mem::uninitialized() };
        {
            let self_numer_denom = self.as_mut_numer_denom();
            mem::swap(&mut numer, self_numer_denom.0);
            mem::swap(&mut denom, self_numer_denom.1);
            // do not canonicalize uninitialized values
            mem::forget(self_numer_denom);
        }
        mem::forget(self);
        (numer, denom)
    }

    /// Computes the absolute value of `self`
    pub fn abs(&mut self) -> &mut Rational {
        unsafe {
            gmp::mpq_abs(&mut self.inner, &self.inner);
        }
        self
    }

    /// Computes the reciprocal of `self`.
    ///
    /// # Panics
    ///
    /// Panics if the value is zero.
    pub fn recip(&mut self) -> &mut Rational {
        assert!(self.sign() != Ordering::Equal, "division by zero");
        unsafe {
            gmp::mpq_inv(&mut self.inner, &self.inner);
        }
        self
    }

    /// Returns `Less` if `self` is less than zero,
    /// `Greater` if `self` is greater than zero,
    /// or `Equal` if `self` is equal to zero.
    pub fn sign(&self) -> Ordering {
        self.numer().sign()
    }

    /// Returns a string representation of `self` for the specified
    /// `radix`.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn to_string_radix(&self, radix: i32) -> String {
        self.make_string(radix, false, "")
    }

    /// Parses a `Rational` number.
    ///
    /// See the [corresponding assignment](#method.assign_str_radix).
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn from_str_radix(src: &str, radix: i32) -> Result<Rational, ()> {
        let mut r = Rational::new();
        r.assign_str_radix(src, radix)?;
        Ok(r)
    }

    /// Parses a `Rational` number from a string.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// let mut r = Rational::new();
    /// let ret = r.assign_str("1/0");
    /// assert!(ret.is_err());
    /// r.assign_str("24/2").unwrap();
    /// let (num, den) = r.as_numer_denom();
    /// assert!(*num == 12);
    /// assert!(*den == 1);
    /// ```
    pub fn assign_str(&mut self, src: &str) -> Result<(), ()> {
        let c_str = CString::new(src).map_err(|_| ())?;
        let err =
            unsafe { gmp::mpq_set_str(&mut self.inner, c_str.as_ptr(), 0) };
        if err != 0 || *self.denom() == 0 {
            self.assign(0);
            return Err(());
        }
        unsafe {
            gmp::mpq_canonicalize(&mut self.inner);
        }
        Ok(())
    }

    /// Parses a `Rational` number from a string with the specified
    /// radix.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::Rational;
    /// let mut r = Rational::new();
    /// r.assign_str_radix("ff/a", 16).unwrap();
    /// assert!(r == (255, 10));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix(&mut self,
                            src: &str,
                            radix: i32)
                            -> Result<(), ()> {
        assert!(radix >= 2 && radix <= 36, "radix out of range");
        let c_str = CString::new(src).map_err(|_| ())?;
        let err =
            unsafe { gmp::mpq_set_str(&mut self.inner, c_str.as_ptr(), radix) };
        if err != 0 || *self.denom() == 0 {
            self.assign(0);
            return Err(());
        }
        unsafe {
            gmp::mpq_canonicalize(&mut self.inner);
        }
        Ok(())
    }
}

impl FromStr for Rational {
    type Err = ();

    /// Parses a `Rational` number.
    ///
    /// See the [corresponding assignment](#method.assign_str).
    fn from_str(src: &str) -> Result<Rational, ()> {
        let mut r = Rational::new();
        r.assign_str(src)?;
        Ok(r)
    }
}

macro_rules! from_lifetime_a {
    { $d:expr, $t:ty } => {
        impl<'a> From<$t> for Rational {
            /// Constructs a `Rational` number from
            #[doc=$d]
            fn from(t: $t) -> Rational {
                let mut ret = Rational::new();
                ret.assign(t);
                ret
            }
        }
    };
}

macro_rules! from {
    { $d:expr, $t:ty } => {
        impl From<$t> for Rational {
            /// Constructs a `Rational` number from
            #[doc=$d]
            fn from(t: $t) -> Rational {
                let mut ret = Rational::new();
                ret.assign(t);
                ret
            }
        }
    };
}

from_lifetime_a! { "another `Rational` number.", &'a Rational }

impl From<Integer> for Rational {
    /// Constructs a `Rational` number from an `Integer`.
    ///
    /// This constructor allocates one new `Integer` and reuses the
    /// allocation for `val`.
    fn from(val: Integer) -> Rational {
        Rational::from((val, 1.into()))
    }
}

from_lifetime_a! { "an `Integer`.", &'a Integer }

impl From<(Integer, Integer)> for Rational {
    /// Constructs a `Rational` number from a numerator `Integer` and
    /// denominator `Integer`.
    ///
    /// This constructor does not allocate, as it reuses the `Integer`
    /// components.
    ///
    /// Panics
    ///
    /// Panics if the denominator is zero.
    fn from((mut num, mut den): (Integer, Integer)) -> Rational {
        assert!(den.sign() != Ordering::Equal, "division by zero");
        let mut dst: Rational = unsafe { mem::uninitialized() };
        {
            let num_den = dst.as_mut_numer_denom();
            mem::swap(&mut num, num_den.0);
            mem::swap(&mut den, num_den.1);
        }
        mem::forget(num);
        mem::forget(den);
        dst
    }
}

from_lifetime_a! { "a numerator `Integer` and denominator `Integer`.",
                    (&'a Integer, &'a Integer) }

from! { "a `u32`.", u32 }
from! { "an `i32`.", i32 }
from! { "an `f64`, losing no precision.\n\n\
         # Panics\n\n\
         Panics if `t` is a NaN or infinite.", f64 }
from! { "an `f32`, losing no precision.\n\n\
         # Panics\n\n\
         Panics if `t` is a NaN or infinite.", f32 }
from! { "a numerator `u32` and denominator `u32`.\n\n\
         # Panics\n\n\
         Panics if the denominator is zero.", (u32, u32) }
from! { "a numerator `i32` and denominator `u32`.\n\n\
         # Panics\n\n\
         Panics if the denominator is zero.", (i32, u32) }
from! { "a numerator `u32` and denominator `i32`.\n\n\
         # Panics\n\n\
         Panics if the denominator is zero.", (u32, i32) }
from! { "a numerator `i32` and denominator `i32`.\n\n\
         # Panics\n\n\
         Panics if the denominator is zero.", (i32, i32) }

macro_rules! assign_move {
    { $d:expr, $t:ty } => {
        impl Assign<$t> for Rational {
            /// Assigns from
            #[doc=$d]
            fn assign(&mut self, other: $t) {
                self.assign(&other);
            }
        }
    };
}

impl<'a> Assign<&'a Rational> for Rational {
    /// Assigns from another `Rational` number.
    fn assign(&mut self, other: &'a Rational) {
        unsafe {
            gmp::mpq_set(&mut self.inner, &other.inner);
        }
    }
}

assign_move! { "another `Rational` number.", Rational }

impl<'a> Assign<&'a Integer> for Rational {
    /// Assigns from an `Integer`.
    fn assign(&mut self, val: &'a Integer) {
        unsafe {
            gmp::mpq_set_z(&mut self.inner, integer_inner(val));
        }
    }
}

assign_move! { "an `Integer`.", Integer }

macro_rules! assign_frac {
    { $d:expr, $t1:ty, $t2:ty } => {
        impl Assign<($t1, $t2)> for Rational {
            /// Assigns from
            #[doc=$d]
            ///
            /// # Panics
            ///
            /// Panics if the denominator is zero.
            fn assign(&mut self, (num, den): ($t1, $t2)) {
                let num_den = self.as_mut_numer_denom();
                num_den.0.assign(num);
                num_den.1.assign(den);
            }
        }
    };
}

assign_frac! { "a numerator `Integer` and a denominator `Integer`.",
                Integer, Integer }

impl<'a> Assign<(&'a Integer, &'a Integer)> for Rational {
    /// Assigns from a numerator `Integer` and a denominator `Integer`.
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero.
    fn assign(&mut self, (num, den): (&Integer, &Integer)) {
        let num_den = self.as_mut_numer_denom();
        num_den.0.assign(num);
        num_den.1.assign(den);
    }
}

impl Assign<u32> for Rational {
    /// Assigns from a `u32`.
    fn assign(&mut self, val: u32) {
        self.assign((val, 1u32));
    }
}

impl Assign<i32> for Rational {
    /// Assigns from an `i32`.
    fn assign(&mut self, val: i32) {
        self.assign((val, 1i32));
    }
}

impl Assign<f64> for Rational {
    /// Assigns from an `f64`, losing no precision.
    ///
    /// # Panics
    ///
    /// Panics if `f` is a NaN or infinite.
    fn assign(&mut self, f: f64) {
        assert!(!f.is_nan());
        assert!(!f.is_infinite());
        unsafe {
            gmp::mpq_set_d(&mut self.inner, f);
        }
    }
}

impl Assign<f32> for Rational {
    /// Assigns from an `f32`, losing no precision.
    ///
    /// # Panics
    ///
    /// Panics if `f` is a NaN or infinite.
    fn assign(&mut self, f: f32) {
        self.assign(f as f64);
    }
}

assign_frac! { "a numerator `u32` and a denominator `u32`.", u32, u32 }
assign_frac! { "a numerator `i32` and a denominator `u32`.", i32, u32 }
assign_frac! { "a numerator `u32` and a denominator `i32`.", u32, i32 }
assign_frac! { "a numerator `i32` and a denominator `i32`.", i32, i32 }

impl<'a> Assign<&'a Rational> for Integer {
    /// Assigns from a `Rational` number, rounding towards zero.
    fn assign(&mut self, val: &'a Rational) {
        unsafe {
            gmp::mpz_set_q(integer_inner_mut(self), &val.inner);
        }
    }
}

impl<'a> Assign<Rational> for Integer {
    /// Assigns from a `Rational` number, rounding towards zero.
    fn assign(&mut self, val: Rational) {
        self.assign(&val);
    }
}

macro_rules! arith_op {
    {
        $imp:ident $method:ident,
        $imp_assign:ident $method_assign:ident,
        $func:path
    } => {
        impl<'a> $imp<&'a Rational> for Rational {
            type Output = Rational;
            fn $method(mut self, op: &'a Rational) -> Rational {
                self.$method_assign(op);
                self
            }
        }

        impl $imp<Rational> for Rational {
            type Output = Rational;
            fn $method(self, op: Rational) -> Rational {
                self.$method(&op)
            }
        }

        impl<'a> $imp_assign<&'a Rational> for Rational {
            fn $method_assign(&mut self, op: &'a Rational) {
                unsafe {
                    $func(&mut self.inner, &self.inner, &op.inner);
                }
            }
        }

        impl $imp_assign<Rational> for Rational {
            fn $method_assign(&mut self, op: Rational) {
                self.add_assign(&op);
            }
        }
    };
}

macro_rules! arith_noncommut_op {
    {
        $imp:ident $method:ident,
        $imp_assign:ident $method_assign:ident,
        $imp_from_assign:ident $method_from_assign:ident,
        $func:path
    } => {
        arith_op! { $imp $method, $imp_assign $method_assign, $func }

        impl<'a> $imp_from_assign<&'a Rational> for Rational {
            fn $method_from_assign(&mut self, lhs: &'a Rational) {
                unsafe {
                    $func(&mut self.inner, &lhs.inner, &self.inner);
                }
            }
        }

        impl $imp_from_assign<Rational> for Rational {
            fn $method_from_assign(&mut self, lhs: Rational) {
                self.$method_from_assign(&lhs);
            }
        }

    };
}

arith_op! { Add add, AddAssign add_assign, gmp::mpq_add }
arith_noncommut_op! { Sub sub, SubAssign sub_assign,
                      SubFromAssign sub_from_assign, gmp::mpq_sub }
arith_op! { Mul mul, MulAssign mul_assign, gmp::mpq_mul }
arith_noncommut_op! { Div div, DivAssign div_assign,
                      DivFromAssign div_from_assign, gmp::mpq_div }

impl Neg for Rational {
    type Output = Rational;
    fn neg(mut self) -> Rational {
        self.neg_assign();
        self
    }
}

impl NegAssign for Rational {
    fn neg_assign(&mut self) {
        unsafe {
            gmp::mpq_neg(&mut self.inner, &self.inner);
        }
    }
}

impl Shl<u32> for Rational {
    type Output = Rational;
    /// Multiplies `self` by 2 to the power of `op`.
    fn shl(mut self, op: u32) -> Rational {
        self.shl_assign(op);
        self
    }
}

impl ShlAssign<u32> for Rational {
    /// Multiplies `self` by 2 to the power of `op`.
    fn shl_assign(&mut self, op: u32) {
        unsafe {
            gmp::mpq_mul_2exp(&mut self.inner, &self.inner, op.into());
        }
    }
}

impl Shr<u32> for Rational {
    type Output = Rational;
    /// Divides `self` by 2 to the power of `op`.
    fn shr(mut self, op: u32) -> Rational {
        self.shr_assign(op);
        self
    }
}

impl ShrAssign<u32> for Rational {
    /// Divides `self` by 2 to the power of `op`.
    fn shr_assign(&mut self, op: u32) {
        unsafe {
            gmp::mpq_div_2exp(&mut self.inner, &self.inner, op.into());
        }
    }
}

impl Shl<i32> for Rational {
    type Output = Rational;
    /// Multiplies `self` by 2 to the power of `op`.
    fn shl(self, op: i32) -> Rational {
        if op >= 0 {
            self.shl(op as u32)
        } else {
            self.shr(op.wrapping_neg() as u32)
        }
    }
}

impl ShlAssign<i32> for Rational {
    /// Multiplies `self` by 2 to the power of `op`.
    fn shl_assign(&mut self, op: i32) {
        if op >= 0 {
            self.shl_assign(op as u32);
        } else {
            self.shr_assign(op.wrapping_neg() as u32);
        }
    }
}

impl Shr<i32> for Rational {
    type Output = Rational;
    /// Divides `self` by 2 to the power of `op`.
    fn shr(self, op: i32) -> Rational {
        if op >= 0 {
            self.shr(op as u32)
        } else {
            self.shl(op.wrapping_neg() as u32)
        }
    }
}

impl ShrAssign<i32> for Rational {
    /// Divides `self` by 2 to the power of `op`.
    fn shr_assign(&mut self, op: i32) {
        if op >= 0 {
            self.shr_assign(op as u32);
        } else {
            self.shl_assign(op.wrapping_neg() as u32);
        }
    }
}

impl Pow<u32> for Rational {
    type Output = Rational;
    fn pow(mut self, op: u32) -> Rational {
        self.pow_assign(op);
        self
    }
}

impl PowAssign<u32> for Rational {
    fn pow_assign(&mut self, op: u32) {
        let num_den = self.as_mut_numer_denom();
        num_den.0.pow_assign(op);
        num_den.1.pow_assign(op);
    }
}

impl Pow<i32> for Rational {
    type Output = Rational;
    fn pow(mut self, op: i32) -> Rational {
        self.pow_assign(op);
        self
    }
}

impl PowAssign<i32> for Rational {
    fn pow_assign(&mut self, op: i32) {
        let uop = if op < 0 {
            self.recip();
            (op.wrapping_neg() as u32).into()
        } else {
            (op as u32).into()
        };
        let num_den = self.as_mut_numer_denom();
        num_den.0.pow_assign(uop);
        num_den.1.pow_assign(uop);
    }
}

impl Eq for Rational {}

impl Ord for Rational {
    fn cmp(&self, other: &Rational) -> Ordering {
        let ord = unsafe { gmp::mpq_cmp(&self.inner, &other.inner) };
        ord.cmp(&0)
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Rational) -> bool {
        unsafe { gmp::mpq_equal(&self.inner, &other.inner) != 0 }
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

macro_rules! cmp {
    { $t:ty, $eval:expr } => {
        impl PartialEq<$t> for Rational {
            fn eq(&self, other: &$t) -> bool {
                self.partial_cmp(other) == Some(Ordering::Equal)
            }
        }

        impl PartialOrd<$t> for Rational {
            fn partial_cmp(&self, other: &$t) -> Option<Ordering> {
                Some($eval(&self.inner, other))
            }
        }

        impl PartialEq<Rational> for $t {
            fn eq(&self, other: &Rational) -> bool {
                other.eq(self)
            }
        }

        impl PartialOrd<Rational> for $t {
            fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
                match other.partial_cmp(self) {
                    Some(x) => Some(x.reverse()),
                    None => None,
                }
            }
        }
    }
}

cmp! { Integer, |r, t| unsafe { gmp::mpq_cmp_z(r, integer_inner(t)).cmp(&0) } }
cmp! { u32, |r, t: &u32| unsafe { gmp::mpq_cmp_ui(r, (*t).into(), 1).cmp(&0) } }
cmp! { i32, |r, t: &i32| unsafe { gmp::mpq_cmp_si(r, (*t).into(), 1).cmp(&0) } }

cmp! { (u32, u32), |r, t: &(u32, u32)| {
    assert!(t.1 != 0, "division by zero");
    unsafe { gmp::mpq_cmp_ui(r, t.0.into(), t.1.into()).cmp(&0) }
} }
cmp! { (i32, u32), |r, t: &(i32, u32)| {
    let mut num = (t.0.wrapping_abs() as u32).into();
    let mut den = t.1.into();
    let limbs_rat = unsafe { single_limbs((&mut num, &mut den), t.0 < 0) };
    unsafe { gmp::mpq_cmp(r, &limbs_rat).cmp(&0) }
} }
cmp! { (u32, i32), |r, t: &(u32, i32)| {
    let mut num = t.0.into();
    let mut den = (t.1.wrapping_abs() as u32).into();
    let limbs_rat = unsafe { single_limbs((&mut num, &mut den), t.1 < 0) };
    unsafe {gmp::mpq_cmp(r, &limbs_rat).cmp(&0) }
} }
cmp! { (i32, i32), |r, t: &(i32, i32)| {
    let mut num = (t.0.wrapping_abs() as u32).into();
    let mut den = (t.1.wrapping_abs() as u32).into();
    let neg = (t.0 < 0) != (t.1 < 0);
    let limbs_rat = unsafe { single_limbs((&mut num, &mut den), neg) };
    unsafe { gmp::mpq_cmp(r, &limbs_rat).cmp(&0) }
} }

impl Rational {
    fn make_string(&self, radix: i32, to_upper: bool, prefix: &str) -> String {
        assert!(radix >= 2 && radix <= 36, "radix out of range");
        let s;
        let cstr = unsafe {
            s = gmp::mpq_get_str(ptr::null_mut(), radix.into(), &self.inner);
            assert!(!s.is_null());
            CStr::from_ptr(s)
        };
        let mut chars = cstr.to_str().unwrap().chars();
        let mut buf = String::new();
        let mut c = chars.next();
        if c == Some('-') {
            buf.push('-');
            c = chars.next();
        }
        buf.push_str(prefix);
        if let Some(x) = c {
            buf.push(x);
        }
        for c in chars {
            buf.push(c);
        }
        unsafe {
            let mut free = None;
            gmp::get_memory_functions(ptr::null_mut(),
                                      ptr::null_mut(),
                                      &mut free);
            let free = free.unwrap();
            let free_len = cstr.to_bytes().len() + 1;
            free(s as *mut c_void, free_len);
        }
        if to_upper {
            buf = buf.to_uppercase();
        }
        buf
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string_radix(10))
    }
}

impl fmt::Debug for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.make_string(16, false, "0x"))
    }
}

impl fmt::Binary for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let prefix = if f.alternate() { "0b" } else { "" };
        write!(f, "{}", self.make_string(2, false, prefix))
    }
}

impl fmt::Octal for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let prefix = if f.alternate() { "0o" } else { "" };
        write!(f, "{}", self.make_string(8, false, prefix))
    }
}

impl fmt::LowerHex for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let prefix = if f.alternate() { "0x" } else { "" };
        write!(f, "{}", self.make_string(16, false, prefix))
    }
}

impl fmt::UpperHex for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let prefix = if f.alternate() { "0X" } else { "" };
        write!(f, "{}", self.make_string(16, true, prefix))
    }
}

/// Used to borrow the numerator and denominator of a
/// [`Rational`](struct.Rational.html) number mutably.
///
/// The `Rational` number is canonicalized when the borrow ends. See
/// the [`Rational::as_mut_numer_denom()`]
/// (struct.Rational.html#method.as_mut_numer_denom) method.
pub struct MutNumerDenom<'a>(pub &'a mut Integer, pub &'a mut Integer);

impl<'a> Drop for MutNumerDenom<'a> {
    fn drop(&mut self) {
        assert!(self.1.sign() != Ordering::Equal, "division by zero");
        unsafe {
            let rat_num = integer_inner_mut(self.0);
            let rat_den = integer_inner_mut(self.1);
            let mut canon: gmp::mpq_t = mem::uninitialized();
            let canon_num_ptr = gmp::mpq_numref(&mut canon);
            let canon_den_ptr = gmp::mpq_denref(&mut canon);
            mem::swap(rat_num, &mut *canon_num_ptr);
            mem::swap(rat_den, &mut *canon_den_ptr);
            gmp::mpq_canonicalize(&mut canon);
            mem::swap(rat_num, &mut *canon_num_ptr);
            mem::swap(rat_den, &mut *canon_den_ptr);
            mem::forget(canon);
        }
    }
}

fn integer_inner(z: &Integer) -> &gmp::mpz_t {
    let ptr = z as *const _ as *const gmp::mpz_t;
    unsafe { &*ptr }
}

// This is unsafe as it returns a structure which can be used to break
// the state of z.
unsafe fn integer_inner_mut(z: &mut Integer) -> &mut gmp::mpz_t {
    let ptr = z as *mut _ as *mut gmp::mpz_t;
    &mut *ptr
}

// The return struct has pointers to the given limbs, so no
// deallocation must take place. This function panics if limbs.1 is 0,
// so there is no need to check before calling it.
unsafe fn single_limbs(limbs: (&mut gmp::limb_t, &mut gmp::limb_t),
                       neg: bool)
                       -> gmp::mpq_t {
    assert!(*limbs.1 != 0, "division by zero");
    let mut ret = mem::uninitialized();
    *gmp::mpq_numref(&mut ret) = gmp::mpz_t {
        alloc: 1,
        d: limbs.0,
        size: if *limbs.0 == 0 {
            0
        } else if neg {
            -1
        } else {
            1
        },
    };
    *gmp::mpq_denref(&mut ret) = gmp::mpz_t {
        alloc: 1,
        d: limbs.1,
        size: 1,
    };
    gmp::mpq_canonicalize(&mut ret);
    ret
}

#[cfg(test)]
mod tests {
    use rational::*;
    use std::{i32, u32};

    #[test]
    fn check_cmp_frac() {
        let zero = Rational::new();
        let u = [0, 1, 100, u32::MAX];
        let s = [i32::MIN, -100, -1, 0, 1, 100, i32::MAX];
        for &n in &u {
            for &d in &u {
                if d != 0 {
                    let ans = 0.partial_cmp(&n);
                    assert!(zero.partial_cmp(&(n, d)) == ans);
                    assert!(zero.partial_cmp(&Rational::from((n, d))) == ans);
                }
            }
            for &d in &s {
                if d != 0 {
                    let mut ans = 0.partial_cmp(&n);
                    if d < 0 {
                        ans = ans.map(Ordering::reverse);
                    }
                    assert!(zero.partial_cmp(&(n, d)) == ans);
                    assert!(zero.partial_cmp(&Rational::from((n, d))) == ans);
                }
            }
        }
        for &n in &s {
            for &d in &u {
                if d != 0 {
                    let ans = 0.partial_cmp(&n);
                    assert!(zero.partial_cmp(&(n, d)) == ans);
                    assert!(zero.partial_cmp(&Rational::from((n, d))) == ans);
                }
            }
            for &d in &s {
                if d != 0 {
                    let mut ans = 0.partial_cmp(&n);
                    if d < 0 {
                        ans = ans.map(Ordering::reverse);
                    }
                    assert!(zero.partial_cmp(&(n, d)) == ans);
                    assert!(zero.partial_cmp(&Rational::from((n, d))) == ans);
                }
            }
        }
    }

    #[test]
    fn check_no_nails() {
        // we assume no nail bits when we use limbs
        assert!(gmp::NAIL_BITS == 0);
        assert!(gmp::NUMB_BITS == gmp::LIMB_BITS);
        assert!(gmp::NUMB_BITS as usize == 8 * mem::size_of::<gmp::limb_t>());
    }
}
