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
    data: gmp::mpq_t,
}

fn raw(q: &Rational) -> &gmp::mpq_t {
    &q.data
}

fn raw_mut(q: &mut Rational) -> &mut gmp::mpq_t {
    &mut q.data
}

impl Rational {
    fn num_raw(&self) -> &gmp::mpz_t {
        &raw(self).num
    }

    fn den_raw(&self) -> &gmp::mpz_t {
        &raw(self).den
    }

    fn num_den_raw(&self) -> (&gmp::mpz_t, &gmp::mpz_t) {
        let r = raw(self);
        (&r.num, &r.den)
    }

    fn num_raw_mut(&mut self) -> &mut gmp::mpz_t {
        &mut raw_mut(self).num
    }

    fn den_raw_mut(&mut self) -> &mut gmp::mpz_t {
        &mut raw_mut(self).den
    }

    fn num_den_raw_mut(&mut self) -> (&mut gmp::mpz_t, &mut gmp::mpz_t) {
        let r = raw_mut(self);
        (&mut r.num, &mut r.den)
    }
}

fn integer_unraw(r: &gmp::mpz_t) -> &Integer {
    let ptr = r as *const _ as *const Integer;
    unsafe { &*ptr }
}

fn integer_unraw_mut(r: &mut gmp::mpz_t) -> &mut Integer {
    let ptr = r as *mut _ as *mut Integer;
    unsafe { &mut *ptr }
}

impl Drop for Rational {
    fn drop(&mut self) {
        unsafe {
            gmp::mpq_clear(raw_mut(self));
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
        unsafe {
            let mut data: gmp::mpq_t = mem::uninitialized();
            gmp::mpq_init(&mut data);
            Rational { data: data }
        }
    }

    /// Converts `self` to an `f64`, rounding towards zero.
    pub fn to_f64(&self) -> f64 {
        unsafe { gmp::mpq_get_d(raw(self)) }
    }

    /// Converts `self` to an `f32`, rounding towards zero.
    pub fn to_f32(&self) -> f32 {
        self.to_f64() as f32
    }

    /// Borrows the numerator.
    pub fn numer(&self) -> &Integer {
        integer_unraw(self.num_raw())
    }

    /// Borrows the denominator.
    pub fn denom(&self) -> &Integer {
        integer_unraw(self.den_raw())
    }

    /// Borrows the numerator and denominator.
    pub fn as_numer_denom(&self) -> (&Integer, &Integer) {
        let (num, den) = self.num_den_raw();
        (integer_unraw(num), integer_unraw(den))
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
        let (num, den) = self.num_den_raw_mut();
        MutNumerDenom(integer_unraw_mut(num), integer_unraw_mut(den))
    }

    /// Converts `self` into numerator and denominator integers,
    /// consuming `self`.
    pub fn into_numer_denom(self) -> (Integer, Integer) {
        let (mut num, mut den) = unsafe { mem::uninitialized() };
        *integer_raw_mut(&mut num) = *self.num_raw();
        *integer_raw_mut(&mut den) = *self.den_raw();
        mem::forget(self);
        (num, den)
    }

    /// Computes the absolute value of `self`
    pub fn abs(&mut self) -> &mut Rational {
        unsafe {
            gmp::mpq_abs(raw_mut(self), raw(self));
        }
        self
    }

    /// Computes the reciprocal of `self`.
    pub fn recip(&mut self) -> &mut Rational {
        unsafe {
            gmp::mpq_inv(raw_mut(self), raw(self));
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
        let err = unsafe { gmp::mpq_set_str(raw_mut(self), c_str.as_ptr(), 0) };
        if err != 0 || *self.denom() == 0 {
            self.assign(0);
            return Err(());
        }
        unsafe {
            gmp::mpq_canonicalize(raw_mut(self));
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
            unsafe { gmp::mpq_set_str(raw_mut(self), c_str.as_ptr(), radix) };
        if err != 0 || *self.denom() == 0 {
            self.assign(0);
            return Err(());
        }
        unsafe {
            gmp::mpq_canonicalize(raw_mut(self));
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
    /// Constructs a `Rational` number from an `Integer`. This
    /// constructor allocates one `Integer` for the denominator and
    /// reuses `val` for the numerator.
    fn from(val: Integer) -> Rational {
        Rational::from((val, 1.into()))
    }
}

from_lifetime_a! { "an `Integer`.", &'a Integer }

impl From<(Integer, Integer)> for Rational {
    /// Constructs a `Rational` number from a numerator `Integer` and
    /// denominator `Integer`. This constructor does not allocate, as
    /// it reuses the `Integer` components.
    ///
    /// Panics
    ///
    /// Panics if the denominator is zero.
    fn from((num, den): (Integer, Integer)) -> Rational {
        assert!(den != 0);
        let mut dst: Rational = unsafe { mem::uninitialized() };
        *dst.num_raw_mut() = *integer_raw(&num);
        *dst.den_raw_mut() = *integer_raw(&den);
        mem::forget(num);
        mem::forget(den);
        unsafe {
            gmp::mpq_canonicalize(raw_mut(&mut dst));
        }
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
from! { "a numerator `u32` and denominator `u32`.", (u32, u32) }
from! { "a numerator `i32` and denominator `u32`.", (i32, u32) }
from! { "a numerator `i32` and denominator `i32`.", (i32, i32) }

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
            gmp::mpq_set(raw_mut(self), raw(other));
        }
    }
}

assign_move! { "another `Rational` number.", Rational }

impl<'a> Assign<&'a Integer> for Rational {
    /// Assigns from an `Integer`.
    fn assign(&mut self, val: &'a Integer) {
        unsafe {
            gmp::mpq_set_z(raw_mut(self), integer_raw(val));
        }
    }
}

assign_move! { "an `Integer`.", Integer }

impl Assign<(Integer, Integer)> for Rational {
    /// Assigns from a numerator `Integer` and a denominator `Integer`.
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero.
    fn assign(&mut self, (num, den): (Integer, Integer)) {
        assert!(den != 0);
        integer_unraw_mut(self.num_raw_mut()).assign(num);
        integer_unraw_mut(self.den_raw_mut()).assign(den);
        unsafe {
            gmp::mpq_canonicalize(raw_mut(self));
        }
    }
}

impl<'a> Assign<(&'a Integer, &'a Integer)> for Rational {
    /// Assigns from a numerator `Integer` and a denominator `Integer`.
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero.
    fn assign(&mut self, (num, den): (&Integer, &Integer)) {
        assert!(*den != 0);
        integer_unraw_mut(self.num_raw_mut()).assign(num);
        integer_unraw_mut(self.den_raw_mut()).assign(den);
        unsafe {
            gmp::mpq_canonicalize(raw_mut(self));
        }
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
            gmp::mpq_set_d(raw_mut(self), f);
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

impl Assign<(u32, u32)> for Rational {
    /// Assigns from a numerator `u32` and a denominator `u32`.
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero.
    fn assign(&mut self, (num, den): (u32, u32)) {
        assert!(den != 0);
        unsafe {
            gmp::mpq_set_ui(raw_mut(self), num.into(), den.into());
            gmp::mpq_canonicalize(raw_mut(self));
        }
    }
}

impl Assign<(i32, u32)> for Rational {
    /// Assigns from a numerator `i32` and a denominator `u32`.
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero.
    fn assign(&mut self, (num, den): (i32, u32)) {
        assert!(den != 0);
        unsafe {
            gmp::mpq_set_si(raw_mut(self), num.into(), den.into());
            gmp::mpq_canonicalize(raw_mut(self));
        }
    }
}

impl Assign<(i32, i32)> for Rational {
    /// Assigns from a numerator `i32` and a denominator `i32`.
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero.
    fn assign(&mut self, (num, den): (i32, i32)) {
        if den > 0 {
            self.assign((num, den as u32));
        } else if num > i32::MIN {
            self.assign((-num, den.wrapping_neg() as u32))
        } else {
            self.assign((i32::MIN as u32, den.wrapping_neg() as u32))
        }
    }
}

impl<'a> Assign<&'a Rational> for Integer {
    /// Assigns from a `Rational` number, rounding towards zero.
    fn assign(&mut self, val: &'a Rational) {
        unsafe {
            gmp::mpz_set_q(integer_raw_mut(self), raw(val));
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
    ($imp:ident $method:ident,
     $imp_assign:ident $method_assign:ident,
     $func:path) => {
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
                    $func(raw_mut(self), raw(self), raw(op));
                }
            }
        }

        impl $imp_assign<Rational> for Rational {
            fn $method_assign(&mut self, op: Rational) {
                self.add_assign(&op);
            }
        }
    }
}

arith_op! { Add add, AddAssign add_assign, gmp::mpq_add }
arith_op! { Sub sub, SubAssign sub_assign, gmp::mpq_sub }
arith_op! { Mul mul, MulAssign mul_assign, gmp::mpq_mul }
arith_op! { Div div, DivAssign div_assign, gmp::mpq_div }

impl SubFromAssign for Rational {
    fn sub_from_assign(&mut self, lhs: Rational) {
        self.sub_from_assign(&lhs);
    }
}

impl<'a> SubFromAssign<&'a Rational> for Rational {
    fn sub_from_assign(&mut self, lhs: &Rational) {
        unsafe {
            gmp::mpq_sub(raw_mut(self), raw(lhs), raw(self));
        }
    }
}

impl DivFromAssign for Rational {
    fn div_from_assign(&mut self, lhs: Rational) {
        self.div_from_assign(&lhs);
    }
}

impl<'a> DivFromAssign<&'a Rational> for Rational {
    fn div_from_assign(&mut self, lhs: &Rational) {
        unsafe {
            gmp::mpq_div(raw_mut(self), raw(lhs), raw(self));
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
            gmp::mpq_mul_2exp(raw_mut(self), raw(self), op.into());
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
            gmp::mpq_div_2exp(raw_mut(self), raw(self), op.into());
        }
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
        integer_unraw_mut(self.num_raw_mut()).pow_assign(uop);
        integer_unraw_mut(self.den_raw_mut()).pow_assign(uop);
    }
}

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
            gmp::mpq_neg(raw_mut(self), raw(self));
        }
    }
}

impl Eq for Rational {}

impl Ord for Rational {
    fn cmp(&self, other: &Rational) -> Ordering {
        let ord = unsafe { gmp::mpq_cmp(raw(self), raw(other)) };
        ord.cmp(&0)
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Rational) -> bool {
        unsafe { gmp::mpq_equal(raw(self), raw(other)) != 0 }
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
                Some($eval(raw(self), other))
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

cmp! { Integer, |r, t| unsafe { gmp::mpq_cmp_z(r, integer_raw(t)).cmp(&0) } }
cmp! { u32, |r, t: &u32| unsafe { gmp::mpq_cmp_ui(r, (*t).into(), 1).cmp(&0) } }
cmp! { i32, |r, t: &i32| unsafe { gmp::mpq_cmp_si(r, (*t).into(), 1).cmp(&0) } }

cmp! { (u32, u32), |r, t: &(u32, u32)| unsafe {
    gmp::mpq_cmp_ui(r, t.0.into(), t.1.into()).cmp(&0)
} }
cmp! { (i32, u32), |r, t: &(i32, u32)| unsafe {
    gmp::mpq_cmp_si(r, t.0.into(), t.1.into()).cmp(&0)
} }

cmp! { (i32, i32), |r, t: &(i32, i32)| unsafe {
    if t.1 > 0 {
        gmp::mpq_cmp_si(r, t.0.into(), (t.1 as u32).into()).cmp(&0)
    } else if t.0 > i32::MIN {
        gmp::mpq_cmp_si(r, (-t.0).into(), (t.1.wrapping_neg() as u32).into())
            .cmp(&0)
    } else {
        gmp::mpq_cmp_ui(r,
                        (i32::MIN as u32).into(),
                        (t.1.wrapping_neg() as u32).into())
            .cmp(&0)
    }
} }

impl Rational {
    fn make_string(&self, radix: i32, to_upper: bool, prefix: &str) -> String {
        assert!(radix >= 2 && radix <= 36, "radix out of range");
        let s;
        let cstr;
        unsafe {
            s = gmp::mpq_get_str(ptr::null_mut(), radix.into(), raw(self));
            assert!(!s.is_null());
            cstr = CStr::from_ptr(s);
        }
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
        assert!(*self.1 != 0);
        let rat_num = integer_raw_mut(self.0);
        let rat_den = integer_raw_mut(self.1);
        let mut canon: gmp::mpq_t = unsafe { mem::uninitialized() };
        canon.num = *rat_num;
        canon.den = *rat_den;
        unsafe {
            gmp::mpq_canonicalize(&mut canon);
        }
        *rat_num = canon.num;
        *rat_den = canon.den;
        mem::forget(canon);
    }
}

fn integer_raw(z: &Integer) -> &gmp::mpz_t {
    let ptr = z as *const _ as *const gmp::mpz_t;
    unsafe { &*ptr }
}

fn integer_raw_mut(z: &mut Integer) -> &mut gmp::mpz_t {
    let ptr = z as *mut _ as *mut gmp::mpz_t;
    unsafe { &mut *ptr }
}
