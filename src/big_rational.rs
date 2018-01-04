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

use {Assign, Integer};
use big_integer;
use cast::cast;
use ext::gmp as xgmp;
use gmp_mpfr_sys::gmp::{self, mpq_t};
use inner::{Inner, InnerMut};
use misc;
use ops::AssignInto;
use std::cmp::Ordering;
use std::error::Error;
use std::ffi::CStr;
use std::i32;
use std::marker::PhantomData;
use std::mem;
use std::ops::Deref;
use std::ptr;

/// An arbitrary-precision rational number.
///
/// A rational number is made up of a numerator
/// [`Integer`](struct.Integer.html) and denominator
/// [`Integer`](struct.Integer.html). After rational number functions,
/// the number is always in canonical form, that is, the denominator
/// is always greater than zero, and there are no common factors. Zero
/// is stored as 0/1.
///
/// # Examples
///
/// ```rust
/// use rug::Rational;
/// let r = Rational::from((-12, 15));
/// let recip = Rational::from(r.recip_ref());
/// assert_eq!(recip, (-5, 4));
/// assert_eq!(recip.to_f32(), -1.25);
/// // The numerator and denominator are stored in canonical form.
/// let (num, den) = r.into_numer_denom();
/// assert_eq!(num, -4);
/// assert_eq!(den, 5);
/// ```
///
/// The `Rational` type supports various functions. Most methods have
/// three versions: one that consumes the operand, one that mutates
/// the operand, and one that borrows the operand.
///
/// ```rust
/// use rug::Rational;
///
/// // 1. consume the operand
/// let a = Rational::from((-15, 2));
/// let abs_a = a.abs();
/// assert_eq!(abs_a, (15, 2));
///
/// // 2. mutate the operand
/// let mut b = Rational::from((-17, 2));
/// b.abs_mut();
/// assert_eq!(b, (17, 2));
///
/// // 3. borrow the operand
/// let c = Rational::from((-19, 2));
/// let r = c.abs_ref();
/// let abs_c = Rational::from(r);
/// assert_eq!(abs_c, (19, 2));
/// // c was not consumed
/// assert_eq!(c, (-19, 2));
/// ```
pub struct Rational {
    inner: mpq_t,
}

macro_rules! rat_op_int {
    {
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $($param: $T),*) -> Integer {
            unsafe {
                let num = gmp::mpq_numref(self.inner_mut());
                $func(num, self.inner(), $($param.into()),*);
                // not canonicalized, so do not exit unsafe before consuming
                self.into_numer_denom().0
            }
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $($param: $T),*) {
            unsafe {
                let num_mut = gmp::mpq_numref(self.inner_mut());
                let den_mut = gmp::mpq_denref(self.inner_mut());
                $func(num_mut, self.inner(), $($param.into()),*);
                xgmp::mpz_set_1(den_mut);
            }
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref(&self, $($param: $T),*) -> $Ref {
            $Ref {
                ref_self: self,
                $($param,)*
            }
        }
    }
}

macro_rules! ref_rat_op_int {
    {
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $($param:ident: $T:ty),* }
    } => {
         $(#[$attr_ref])*
        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            ref_self: &'a Rational,
            $($param: $T,)*
        }

        impl<'a> AssignInto<Integer> for $Ref<'a> {
            #[inline]
            fn assign_into(self, dst: &mut Integer) {
                unsafe {
                    $func(
                        dst.inner_mut(),
                        self.ref_self.inner(),
                        $(self.$param.into(),)*
                    );
                }
            }
        }

        from_assign_into! { $Ref<'r> => Integer }
    }
}

macro_rules! rat_op_rat_int {
    {
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($int:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Ref:ident;
    } => {
        $(#[$attr])*
        #[inline]
        pub fn $method(
            mut self,
            mut $int: Integer,
            $($param: $T,)*
        ) -> (Rational, Integer) {
            self.$method_mut(&mut $int);
            (self, $int)
        }

        $(#[$attr_mut])*
        #[inline]
        pub fn $method_mut(&mut self, $int: &mut Integer, $($param: $T),*) {
            unsafe {
                $func(
                    self.inner_mut(),
                    $int.inner_mut(),
                    self.inner(),
                    $($param.into()),*
                );
            }
        }

        $(#[$attr_ref])*
        #[inline]
        pub fn $method_ref(&self, $($param: $T),*) -> $Ref {
            $Ref {
                ref_self: self,
                $($param,)*
            }
        }
    }
}

macro_rules! ref_rat_op_rat_int {
    {
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Ref:ident { $($param:ident: $T:ty),* }
    } => {
         $(#[$attr_ref])*
        #[derive(Clone, Copy)]
        pub struct $Ref<'a> {
            ref_self: &'a Rational,
            $($param: $T,)*
        }

        impl<'a, 'b, 'c>
            AssignInto<(&'a mut Rational, &'b mut Integer)> for $Ref<'c>
        {
            #[inline]
            fn assign_into(
                self,
                dst: &mut (&'a mut Rational, &'b mut Integer),
            ) {
                unsafe {
                    $func(
                        dst.0.inner_mut(),
                        dst.1.inner_mut(),
                        self.ref_self.inner(),
                        $(self.$param.into(),)*
                    );
                }
            }
        }

        impl<'a> From<$Ref<'a>> for (Rational, Integer) {
            #[inline]
            fn from(src: $Ref<'a>) -> Self {
                let mut dst = <Self as Default>::default();
                src.assign_into(&mut (&mut dst.0, &mut dst.1));
                dst
            }
        }
    }
}

impl Rational {
    /// Constructs a new arbitrary-precision rational number with
    /// value 0.
    ///
    /// # Examples
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::new();
    /// assert_eq!(r, 0);
    /// ```
    #[inline]
    pub fn new() -> Rational {
        unsafe {
            let mut ret: Rational = mem::uninitialized();
            gmp::mpq_init(ret.inner_mut());
            ret
        }
    }

    /// Creates a `Rational` from an `f32` if it is finite, losing no
    /// precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use std::f32;
    /// let r = Rational::from_f32(-17125e-3).unwrap();
    /// assert_eq!(r, "-17125/1000".parse::<Rational>().unwrap());
    /// let inf = Rational::from_f32(f32::INFINITY);
    /// assert!(inf.is_none());
    /// ```
    #[inline]
    pub fn from_f32(val: f32) -> Option<Rational> {
        Rational::from_f64(val.into())
    }

    /// Creates a `Rational` from an `f64` if it is finite, losing no
    /// precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use std::f64;
    /// let r = Rational::from_f64(-17125e-3).unwrap();
    /// assert_eq!(r, "-17125/1000".parse::<Rational>().unwrap());
    /// let inf = Rational::from_f64(f64::INFINITY);
    /// assert!(inf.is_none());
    /// ```
    #[inline]
    pub fn from_f64(val: f64) -> Option<Rational> {
        if val.is_finite() {
            let mut r = Rational::new();
            r.assign_f64(val).unwrap();
            Some(r)
        } else {
            None
        }
    }

    /// Parses a `Rational` number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r1 = Rational::from_str_radix("ff/a", 16).unwrap();
    /// assert_eq!(r1, (255, 10));
    /// let r2 = Rational::from_str_radix("+ff0/a0", 16).unwrap();
    /// assert_eq!(r2, (0xff0, 0xa0));
    /// assert_eq!(*r2.numer(), 51);
    /// assert_eq!(*r2.denom(), 2);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn from_str_radix(
        src: &str,
        radix: i32,
    ) -> Result<Rational, ParseRationalError> {
        let mut r = Rational::new();
        r.assign_str_radix(src, radix)?;
        Ok(r)
    }

    /// Checks if a `Rational` number can be parsed.
    ///
    /// If this method does not return an error, neither will any
    /// other function that parses a `Rational` number. If this method
    /// returns an error, the other functions will return the same
    /// error.
    ///
    /// The string must contain a numerator, and may contain a
    /// denominator; the numerator and denominator are separated with
    /// a `'/'`. The numerator can start with an optional minus or
    /// plus sign.
    ///
    /// Whitespace is not allowed anywhere in the string, including in
    /// the beginning and end and around the `'/'`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    ///
    /// let valid1 = Rational::valid_str_radix("12/23", 4);
    /// let r1 = Rational::from(valid1.unwrap());
    /// assert_eq!(r1, (2 + 4 * 1, 3 + 4 * 2));
    /// let valid2 = Rational::valid_str_radix("12/yz", 36);
    /// let r2 = Rational::from(valid2.unwrap());
    /// assert_eq!(r2, (2 + 36 * 1, 35 + 36 * 34));
    ///
    /// let invalid = Rational::valid_str_radix("12 / 23", 4);
    /// let invalid_f = Rational::from_str_radix("12 / 23", 4);
    /// assert_eq!(invalid.unwrap_err(), invalid_f.unwrap_err());
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn valid_str_radix(
        src: &str,
        radix: i32,
    ) -> Result<ValidRational, ParseRationalError> {
        use self::ParseErrorKind as Kind;
        use self::ParseRationalError as Error;

        assert!(radix >= 2 && radix <= 36, "radix out of range");
        let bytes = src.as_bytes();
        let (skip_plus, iter) = match bytes.get(0) {
            Some(&b'+') => (&bytes[1..], bytes[1..].iter()),
            Some(&b'-') => (bytes, bytes[1..].iter()),
            _ => (bytes, bytes.iter()),
        };
        let mut got_digit = false;
        let mut denom = false;
        let mut denom_non_zero = false;
        for b in iter {
            if *b == b'/' {
                if denom {
                    return Err(Error {
                        kind: Kind::TooManySlashes,
                    });
                }
                if !got_digit {
                    return Err(Error {
                        kind: Kind::NumerNoDigits,
                    });
                }
                got_digit = false;
                denom = true;
                continue;
            }
            let digit_value = match *b {
                b'0'...b'9' => *b - b'0',
                b'a'...b'z' => *b - b'a' + 10,
                b'A'...b'Z' => *b - b'A' + 10,
                _ => Err(Error {
                    kind: Kind::InvalidDigit,
                })?,
            };
            if digit_value >= cast::<_, u8>(radix) {
                return Err(Error {
                    kind: Kind::InvalidDigit,
                });
            }
            got_digit = true;
            if denom && digit_value > 0 {
                denom_non_zero = true;
            }
        }
        if !got_digit && denom {
            return Err(Error {
                kind: Kind::DenomNoDigits,
            });
        } else if !got_digit {
            return Err(Error {
                kind: Kind::NoDigits,
            });
        }
        if denom && !denom_non_zero {
            return Err(Error {
                kind: Kind::DenomZero,
            });
        }
        let v = ValidRational {
            bytes: skip_plus,
            radix,
        };
        Ok(v)
    }

    /// Converts to an [`Integer`](struct.Integer.html), rounding
    /// towards zero.
    ///
    /// Note that this method does not consume `self`, and allocates a
    /// new `Integer`. If `self` can be consumed, you should use
    /// [`trunc`](#method.trunc) instead.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let pos = Rational::from((139, 10));
    /// let posi = pos.to_integer();
    /// assert_eq!(posi, 13);
    /// let neg = Rational::from((-139, 10));
    /// let negi = neg.to_integer();
    /// assert_eq!(negi, -13);
    /// ```
    #[inline]
    pub fn to_integer(&self) -> Integer {
        Integer::from(self.trunc_ref())
    }

    /// Converts to an [`Integer`](struct.Integer.html) inside `i`,
    /// rounding towards zero.
    #[inline]
    #[deprecated(since = "0.9.2",
                 note = "use `trunc_ref` instead; `r.copy_to_integer(&mut i)` \
                         can be replaced with `i.assign(r.trunc_ref())`.")]
    pub fn copy_to_integer(&self, i: &mut Integer) {
        i.assign(self.trunc_ref());
    }

    /// Converts to an `f32`, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use rug::rational::SmallRational;
    /// use std::f32;
    /// let min = Rational::from_f32(f32::MIN).unwrap();
    /// let minus_small = min - &*SmallRational::from((7, 2));
    /// // minus_small is truncated to f32::MIN
    /// assert_eq!(minus_small.to_f32(), f32::MIN);
    /// let times_three_two = minus_small * &*SmallRational::from((3, 2));
    /// // times_three_two is too small
    /// assert_eq!(times_three_two.to_f32(), f32::NEG_INFINITY);
    /// ```
    #[inline]
    pub fn to_f32(&self) -> f32 {
        misc::trunc_f64_to_f32(self.to_f64())
    }

    /// Converts to an `f64`, rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use rug::rational::SmallRational;
    /// use std::f64;
    ///
    /// // An `f64` has 53 bits of precision.
    /// let exact = 0x1f_1234_5678_9aff_u64;
    /// let den = 0x1000_u64;
    /// let r = Rational::from((exact, den));
    /// assert_eq!(r.to_f64(), exact as f64 / den as f64);
    ///
    /// // large has 56 ones
    /// let large = 0xff_1234_5678_9aff_u64;
    /// // trunc has 53 ones followed by 3 zeros
    /// let trunc = 0xff_1234_5678_9af8_u64;
    /// let j = Rational::from((large, den));
    /// assert_eq!(j.to_f64(), trunc as f64 / den as f64);
    ///
    /// let max = Rational::from_f64(f64::MAX).unwrap();
    /// let plus_small = max + &*SmallRational::from((7, 2));
    /// // plus_small is truncated to f64::MAX
    /// assert_eq!(plus_small.to_f64(), f64::MAX);
    /// let times_three_two = plus_small * &*SmallRational::from((3, 2));
    /// // times_three_two is too large
    /// assert_eq!(times_three_two.to_f64(), f64::INFINITY);
    /// ```
    #[inline]
    pub fn to_f64(&self) -> f64 {
        unsafe { gmp::mpq_get_d(self.inner()) }
    }

    /// Returns a string representation for the specified `radix`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r1 = Rational::from(0);
    /// assert_eq!(r1.to_string_radix(10), "0");
    /// let r2 = Rational::from((15, 5));
    /// assert_eq!(r2.to_string_radix(10), "3");
    /// let r3 = Rational::from((10, -6));
    /// assert_eq!(r3.to_string_radix(10), "-5/3");
    /// assert_eq!(r3.to_string_radix(5), "-10/3");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn to_string_radix(&self, radix: i32) -> String {
        let mut s = String::new();
        append_to_string(&mut s, self, radix, false);
        s
    }

    /// Assigns from an `f32` if it is finite, losing no precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use std::f32;
    /// let mut r = Rational::new();
    /// let ret = r.assign_f32(12.75);
    /// assert!(ret.is_ok());
    /// assert_eq!(r, (1275, 100));
    /// let ret = r.assign_f32(f32::NAN);
    /// assert!(ret.is_err());
    /// assert_eq!(r, (1275, 100));
    /// ```
    #[inline]
    pub fn assign_f32(&mut self, val: f32) -> Result<(), ()> {
        self.assign_f64(val.into())
    }

    /// Assigns from an `f64` if it is finite, losing no precision.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let mut r = Rational::new();
    /// let ret = r.assign_f64(12.75);
    /// assert!(ret.is_ok());
    /// assert_eq!(r, (1275, 100));
    /// let ret = r.assign_f64(1.0 / 0.0);
    /// assert!(ret.is_err());
    /// assert_eq!(r, (1275, 100));
    /// ```
    #[inline]
    pub fn assign_f64(&mut self, val: f64) -> Result<(), ()> {
        if val.is_finite() {
            unsafe {
                gmp::mpq_set_d(self.inner_mut(), val);
            }
            Ok(())
        } else {
            Err(())
        }
    }

    /// Parses a `Rational` number from a string.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let mut r = Rational::new();
    /// let ret = r.assign_str("1/0");
    /// assert!(ret.is_err());
    /// r.assign_str("-24/2").unwrap();
    /// assert_eq!(*r.numer(), -12);
    /// assert_eq!(*r.denom(), 1);
    /// ```
    #[inline]
    pub fn assign_str(&mut self, src: &str) -> Result<(), ParseRationalError> {
        self.assign_str_radix(src, 10)
    }

    /// Parses a `Rational` number from a string with the specified
    /// radix.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let mut r = Rational::new();
    /// r.assign_str_radix("ff/a", 16).unwrap();
    /// assert_eq!(r, (255, 10));
    /// r.assign_str_radix("+ff0/a0", 16).unwrap();
    /// assert_eq!(r, (255, 10));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    #[inline]
    pub fn assign_str_radix(
        &mut self,
        src: &str,
        radix: i32,
    ) -> Result<(), ParseRationalError> {
        self.assign(Rational::valid_str_radix(src, radix)?);
        Ok(())
    }

    #[cfg(feature = "raw")]
    /// Creates a `Rational` from an initialized GMP rational number.
    ///
    /// # Safety
    ///
    /// * The value must be initialized.
    /// * The `gmp_mpfr_sys::gmp::mpq_t` type can be considered as a
    ///   kind of pointer, so there can be can multiple copies of it.
    ///   Since this function takes over ownership, no other copies of
    ///   the passed value should exist.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate gmp_mpfr_sys;
    /// extern crate rug;
    /// use gmp_mpfr_sys::gmp;
    /// use rug::Rational;
    /// use std::mem;
    /// fn main() {
    ///     let r = unsafe {
    ///         let mut q = mem::uninitialized();
    ///         gmp::mpq_init(&mut q);
    ///         gmp::mpq_set_si(&mut q, -145, 10);
    ///         gmp::mpq_canonicalize(&mut q);
    ///         // q is initialized and unique
    ///         Rational::from_raw(q)
    ///     };
    ///     assert_eq!(r, (-145, 10));
    ///     // since r is a Rational now, deallocation is automatic
    /// }
    /// ```
    #[inline]
    pub unsafe fn from_raw(raw: mpq_t) -> Rational {
        Rational { inner: raw }
    }

    #[cfg(feature = "raw")]
    /// Converts a `Rational` into a GMP rational number.
    ///
    /// The returned object should be freed to avoid memory leaks.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate gmp_mpfr_sys;
    /// extern crate rug;
    /// use gmp_mpfr_sys::gmp;
    /// use rug::Rational;
    /// fn main() {
    ///     let r = Rational::from((-145, 10));
    ///     let mut q = r.into_raw();
    ///     unsafe {
    ///         let d = gmp::mpq_get_d(&q);
    ///         assert_eq!(d, -14.5);
    ///         // free object to prevent memory leak
    ///         gmp::mpq_clear(&mut q);
    ///     }
    /// }
    /// ```
    #[inline]
    pub fn into_raw(self) -> mpq_t {
        let ret = self.inner;
        mem::forget(self);
        ret
    }

    #[cfg(feature = "raw")]
    /// Returns a pointer to the internal GMP rational number.
    ///
    /// The returned pointer will be valid for as long as `self` is
    /// valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate gmp_mpfr_sys;
    /// extern crate rug;
    /// use gmp_mpfr_sys::gmp;
    /// use rug::Rational;
    /// fn main() {
    ///     let r = Rational::from((-145, 10));
    ///     let q_ptr = r.as_raw();
    ///     unsafe {
    ///         let d = gmp::mpq_get_d(q_ptr);
    ///         assert_eq!(d, -14.5);
    ///     }
    ///     // r is still valid
    ///     assert_eq!(r, (-145, 10));
    /// }
    /// ```
    #[inline]
    pub fn as_raw(&self) -> *const mpq_t {
        self.inner()
    }

    #[cfg(feature = "raw")]
    /// Returns an unsafe mutable pointer to the internal GMP rational
    /// number.
    ///
    /// The returned pointer will be valid for as long as `self` is
    /// valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate gmp_mpfr_sys;
    /// extern crate rug;
    /// use gmp_mpfr_sys::gmp;
    /// use rug::Rational;
    /// fn main() {
    ///     let mut r = Rational::from((-145, 10));
    ///     let q_ptr = r.as_raw_mut();
    ///     unsafe {
    ///         gmp::mpq_inv(q_ptr, q_ptr);
    ///     }
    ///     assert_eq!(r, (-10, 145));
    /// }
    /// ```
    #[inline]
    pub fn as_raw_mut(&mut self) -> *mut mpq_t {
        unsafe { self.inner_mut() }
    }

    /// Borrows the numerator as an `Integer`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// assert_eq!(*r.numer(), -3)
    /// ```
    #[inline]
    pub fn numer(&self) -> &Integer {
        unsafe { &*(gmp::mpq_numref_const(self.inner()) as *const _) }
    }

    /// Borrows the denominator as an
    /// [`Integer`](struct.Integer.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// assert_eq!(*r.denom(), 5);
    /// ```
    #[inline]
    pub fn denom(&self) -> &Integer {
        unsafe { &*(gmp::mpq_denref_const(self.inner()) as *const _) }
    }

    /// Borrows the numerator and denominator as
    /// [`Integer`](struct.Integer.html) values.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// let (num, den) = r.as_numer_denom();
    /// assert_eq!(*num, -3);
    /// assert_eq!(*den, 5);
    /// ```
    #[inline]
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
    /// use rug::Rational;
    ///
    /// let mut r = Rational::from((3, 5));
    /// {
    ///     let mut num_den = r.as_mut_numer_denom();
    ///     // change r from 3/5 to 4/8, which is equal to 1/2
    ///     *num_den.num() += 1;
    ///     *num_den.den() += 3;
    ///     // borrow ends here
    /// }
    /// let num_den = r.as_numer_denom();
    /// assert_eq!(*num_den.0, 1);
    /// assert_eq!(*num_den.1, 2);
    /// ```
    ///
    /// If the mutable value is leaked, the denominator is lost when
    /// the borrow ends.
    ///
    /// ```rust
    /// use rug::Rational;
    /// use std::mem;
    ///
    /// let mut r = Rational::from((3, 5));
    /// {
    ///     let mut num_den = r.as_mut_numer_denom();
    ///     // try change r from 3/5 to 4/8
    ///     *num_den.num() += 1;
    ///     *num_den.den() += 3;
    ///     // forget num_den, so no canonicalization takes place
    ///     mem::forget(num_den)
    ///     // borrow ends here, but nothing happens
    /// }
    /// // because of the leak, 4/8 has become 4/1
    /// let num_den = r.as_numer_denom();
    /// assert_eq!(*num_den.0, 4);
    /// assert_eq!(*num_den.1, 1);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero when the borrow ends.
    pub fn as_mut_numer_denom(&mut self) -> MutNumerDenom {
        // We swap in a denominator of 1 so that if the
        // `MutNumerDenom` is leaked, we don't end up with a
        // non-canonical rational number.
        unsafe {
            let numer_ptr = gmp::mpq_numref(self.inner_mut());
            let denom_ptr = gmp::mpq_denref(self.inner_mut());
            let mut acting_denom = Integer::from(1);
            mem::swap(acting_denom.inner_mut(), &mut *denom_ptr);
            MutNumerDenom {
                num: &mut *(numer_ptr as *mut Integer),
                den_place: &mut *(denom_ptr as *mut Integer),
                den_actual: acting_denom,
            }
        }
    }

    /// Borrows the numerator and denominator mutably without
    /// canonicalizing aftwerwards.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not canonicalize the
    /// rational number when the borrow ends. The rest of the library
    /// assumes that `Rational` structures keep their numerators and
    /// denominators in canonical form.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    ///
    /// let mut r = Rational::from((3, 5));
    /// {
    ///     let (num, den) = unsafe {
    ///         r.as_mut_numer_denom_no_canonicalization()
    ///     };
    ///     // Add one to r by adding den to num. Since num and den
    ///     // are relatively prime, r remains in canonical form.
    ///     *num += &*den;
    /// }
    /// assert_eq!(r, (8, 5));
    /// ```
    #[inline]
    pub unsafe fn as_mut_numer_denom_no_canonicalization(
        &mut self,
    ) -> (&mut Integer, &mut Integer) {
        (
            &mut *(gmp::mpq_numref(self.inner_mut()) as *mut _),
            &mut *(gmp::mpq_denref(self.inner_mut()) as *mut _),
        )
    }

    /// Converts into numerator and denominator integers.
    ///
    /// This function reuses the allocated memory and does not
    /// allocate any new memory.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// let (num, den) = r.into_numer_denom();
    /// assert_eq!(num, -3);
    /// assert_eq!(den, 5);
    /// ```
    #[inline]
    pub fn into_numer_denom(self) -> (Integer, Integer) {
        let (mut numer, mut denom) = unsafe { mem::uninitialized() };
        unsafe {
            ptr::copy_nonoverlapping(self.numer(), &mut numer, 1);
            ptr::copy_nonoverlapping(self.denom(), &mut denom, 1);
        }
        mem::forget(self);
        (numer, denom)
    }

    /// Borrows a negated copy of the `Rational` number.
    ///
    /// The returned object implements `Deref<Rational>.
    ///
    /// This method performs a shallow copy and negates it, and
    /// negation does not change the allocated data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::from((7, 11));
    /// let neg_r = r.as_neg();
    /// assert_eq!(*neg_r, (-7, 11));
    /// // methods taking &self can be used on the returned object
    /// let reneg_r = neg_r.as_neg();
    /// assert_eq!(*reneg_r, (7, 11));
    /// assert_eq!(*reneg_r, r);
    /// ```
    #[inline]
    pub fn as_neg(&self) -> BorrowRational {
        let mut ret = BorrowRational {
            inner: self.inner,
            phantom: PhantomData,
        };
        let size = self.numer().inner().size.checked_neg().expect("overflow");
        unsafe {
            (*gmp::mpq_numref(&mut ret.inner)).size = size;
        }
        ret
    }

    /// Borrows an absolute copy of the `Rational` number.
    ///
    /// The returned object implements `Deref<Rational>`.
    ///
    /// This method performs a shallow copy and possibly negates it,
    /// and negation does not change the allocated data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::from((-7, 11));
    /// let abs_r = r.as_abs();
    /// assert_eq!(*abs_r, (7, 11));
    /// // methods taking &self can be used on the returned object
    /// let reabs_r = abs_r.as_abs();
    /// assert_eq!(*reabs_r, (7, 11));
    /// assert_eq!(*reabs_r, *abs_r);
    /// ```
    #[inline]
    pub fn as_abs(&self) -> BorrowRational {
        let mut ret = BorrowRational {
            inner: self.inner,
            phantom: PhantomData,
        };
        let size = self.numer().inner().size.checked_abs().expect("overflow");
        unsafe {
            (*gmp::mpq_numref(&mut ret.inner)).size = size;
        }
        ret
    }

    /// Borrows a reciprocal copy of the `Rational` number.
    ///
    /// The returned object implements `Deref<Rational>`.
    ///
    /// This method performs some shallow copying, swapping numerator
    /// and denominator and making sure the sign is in the numerator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::from((-7, 11));
    /// let recip_r = r.as_recip();
    /// assert_eq!(*recip_r, (-11, 7));
    /// // methods taking &self can be used on the returned object
    /// let rerecip_r = recip_r.as_recip();
    /// assert_eq!(*rerecip_r, (-7, 11));
    /// assert_eq!(*rerecip_r, r);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the value is zero.
    pub fn as_recip(&self) -> BorrowRational {
        assert_ne!(self.cmp0(), Ordering::Equal, "division by zero");
        let mut ret = BorrowRational {
            inner: unsafe { mem::uninitialized() },
            phantom: PhantomData,
        };
        let (ret_num, ret_den) = unsafe {
            let num = &mut *gmp::mpq_numref(&mut ret.inner);
            let den = &mut *gmp::mpq_denref(&mut ret.inner);
            ptr::copy_nonoverlapping(self.denom().inner(), num, 1);
            ptr::copy_nonoverlapping(self.numer().inner(), den, 1);
            (num, den)
        };
        if self.cmp0() == Ordering::Less {
            ret_num.size = ret_num.size.checked_neg().expect("overflow");
            ret_den.size = ret_den.size.checked_neg().expect("overflow");
        }
        ret
    }

    /// Returns the same result as `self.cmp(&0)`, but is faster.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use std::cmp::Ordering;
    /// assert_eq!(Rational::from((-5, 7)).cmp0(), Ordering::Less);
    /// assert_eq!(Rational::from(0).cmp0(), Ordering::Equal);
    /// assert_eq!(Rational::from((5, 7)).cmp0(), Ordering::Greater);
    /// ```
    pub fn cmp0(&self) -> Ordering {
        self.numer().cmp0()
    }

    #[doc(hidden)]
    #[deprecated(since = "0.8.0", note = "renamed to `cmp0`")]
    #[inline]
    pub fn sign(&self) -> Ordering {
        self.cmp0()
    }

    math_op1! {
        gmp::mpq_abs;
        /// Computes the absolute value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let r = Rational::from((-100, 17));
        /// let abs = r.abs();
        /// assert_eq!(abs, (100, 17));
        /// ```
        fn abs();
        /// Computes the absolute value.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let mut r = Rational::from((-100, 17));
        /// r.abs_mut();
        /// assert_eq!(r, (100, 17));
        /// ```
        fn abs_mut;
        /// Computes the absolute value.
        ///
        /// The returned object implements
        /// [`AssignInto<Rational>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let r = Rational::from((-100, 17));
        /// let r_ref = r.abs_ref();
        /// let abs = Rational::from(r_ref);
        /// assert_eq!(abs, (100, 17));
        /// ```
        fn abs_ref -> AbsRef;
    }
    rat_op_int! {
        xgmp::mpq_signum;
        /// Computes the signum.
        ///
        /// * 0 if the value is zero
        /// * 1 if the value is positive
        /// * −1 if the value is negative
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let r = Rational::from((-100, 17));
        /// let signum = r.signum();
        /// assert_eq!(signum, -1);
        /// ```
        fn signum();
        /// Computes the signum.
        ///
        /// * 0 if the value is zero
        /// * 1 if the value is positive
        /// * −1 if the value is negative
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let mut r = Rational::from((-100, 17));
        /// r.signum_mut();
        /// assert_eq!(r, -1);
        /// ```
        fn signum_mut;
        /// Computes the signum.
        ///
        /// * 0 if the value is zero
        /// * 1 if the value is positive
        /// * −1 if the value is negative
        ///
        /// # Examples
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// ```rust
        /// use rug::{Integer, Rational};
        /// let r = Rational::from((-100, 17));
        /// let r_ref = r.signum_ref();
        /// let signum = Integer::from(r_ref);
        /// assert_eq!(signum, -1);
        /// ```
        fn signum_ref -> SignumRef;
    }

    /// Clamps the value within the specified bounds.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let min = (-3, 2);
    /// let max = (3, 2);
    /// let too_small = Rational::from((-5, 2));
    /// let clamped1 = too_small.clamp(&min, &max);
    /// assert_eq!(clamped1, (-3, 2));
    /// let in_range = Rational::from((1, 2));
    /// let clamped2 = in_range.clamp(&min, &max);
    /// assert_eq!(clamped2, (1, 2));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the maximum value is less than the minimum value.
    #[inline]
    pub fn clamp<'a, 'b, Min, Max>(
        mut self,
        min: &'a Min,
        max: &'b Max,
    ) -> Rational
    where
        Rational: PartialOrd<Min>
            + PartialOrd<Max>
            + Assign<&'a Min>
            + Assign<&'b Max>,
    {
        self.clamp_mut(min, max);
        self
    }

    /// Clamps the value within the specified bounds.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let min = (-3, 2);
    /// let max = (3, 2);
    /// let mut too_small = Rational::from((-5, 2));
    /// too_small.clamp_mut(&min, &max);
    /// assert_eq!(too_small, (-3, 2));
    /// let mut in_range = Rational::from((1, 2));
    /// in_range.clamp_mut(&min, &max);
    /// assert_eq!(in_range, (1, 2));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the maximum value is less than the minimum value.
    pub fn clamp_mut<'a, 'b, Min, Max>(&mut self, min: &'a Min, max: &'b Max)
    where
        Rational: PartialOrd<Min>
            + PartialOrd<Max>
            + Assign<&'a Min>
            + Assign<&'b Max>,
    {
        if (&*self).lt(min) {
            self.assign(min);
            assert!(!(&*self).gt(max), "minimum larger than maximum");
        } else if (&*self).gt(max) {
            self.assign(max);
            assert!(!(&*self).lt(min), "minimum larger than maximum");
        }
    }

    /// Clamps the value within the specified bounds.
    ///
    /// The returned object implements
    /// [`AssignInto<Rational>`](../ops/trait.AssignInto.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let min = (-3, 2);
    /// let max = (3, 2);
    /// let too_small = Rational::from((-5, 2));
    /// let r1 = too_small.clamp_ref(&min, &max);
    /// let clamped1 = Rational::from(r1);
    /// assert_eq!(clamped1, (-3, 2));
    /// let in_range = Rational::from((1, 2));
    /// let r2 = in_range.clamp_ref(&min, &max);
    /// let clamped2 = Rational::from(r2);
    /// assert_eq!(clamped2, (1, 2));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the maximum value is less than the minimum value.
    #[inline]
    pub fn clamp_ref<'a, Min, Max>(
        &'a self,
        min: &'a Min,
        max: &'a Max,
    ) -> ClampRef<'a, Min, Max>
    where
        Rational: PartialOrd<Min>
            + PartialOrd<Max>
            + Assign<&'a Min>
            + Assign<&'a Max>,
    {
        ClampRef {
            ref_self: self,
            min,
            max,
        }
    }

    math_op1! {
        xgmp::mpq_inv_check;
        /// Computes the reciprocal.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let r = Rational::from((-100, 17));
        /// let recip = r.recip();
        /// assert_eq!(recip, (-17, 100));
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if the value is zero.
        fn recip();
        /// Computes the reciprocal.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let mut r = Rational::from((-100, 17));
        /// r.recip_mut();
        /// assert_eq!(r, (-17, 100));
        /// ```
        ///
        /// # Panics
        ///
        /// Panics if the value is zero.
        fn recip_mut;
        /// Computes the reciprocal.
        ///
        /// The returned object implements
        /// [`AssignInto<Rational>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let r = Rational::from((-100, 17));
        /// let r_ref = r.recip_ref();
        /// let recip = Rational::from(r_ref);
        /// assert_eq!(recip, (-17, 100));
        /// ```
        fn recip_ref -> RecipRef;
    }
    rat_op_int! {
        xgmp::mpq_trunc;
        /// Rounds the number towards zero and returns it as an
        /// [`Integer`](struct.Integer.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -3.7
        /// let r1 = Rational::from((-37, 10));
        /// let i1 = r1.trunc();
        /// assert_eq!(i1, -3);
        /// // 3.3
        /// let r2 = Rational::from((33, 10));
        /// let i2 = r2.trunc();
        /// assert_eq!(i2, 3);
        /// ```
        fn trunc();
        /// Rounds the number towards zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Rational};
        /// // -3.7
        /// let mut r = Rational::from((-37, 10));
        /// r.trunc_mut();
        /// assert_eq!(r, -3);
        /// // 3.3
        /// r.assign((33, 10));
        /// r.trunc_mut();
        /// assert_eq!(r, 3);
        /// ```
        fn trunc_mut;
        /// Rounds the number towards zero.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer, Rational};
        /// let mut trunc = Integer::new();
        /// // -3.7
        /// let r1 = Rational::from((-37, 10));
        /// trunc.assign(r1.trunc_ref());
        /// assert_eq!(trunc, -3);
        /// // 3.3
        /// let r2 = Rational::from((33, 10));
        /// trunc.assign(r2.trunc_ref());
        /// assert_eq!(trunc, 3);
        /// ```
        fn trunc_ref -> TruncRef;
    }

    /// Computes the fractional part of the number.
    #[deprecated(since = "0.9.0", note = "renamed to `rem_trunc`")]
    #[inline]
    pub fn fract(self) -> Rational {
        self.rem_trunc()
    }

    /// Computes the fractional part of the number.
    #[deprecated(since = "0.9.0", note = "renamed to `rem_trunc_mut`")]
    #[inline]
    pub fn fract_mut(&mut self) {
        self.rem_trunc_mut();
    }

    /// Computes the fractional part of the number.
    #[deprecated(since = "0.9.0", note = "renamed to `rem_trunc_ref`")]
    #[inline]
    pub fn fract_ref(&self) -> RemTruncRef {
        self.rem_trunc_ref()
    }

    math_op1! {
        xgmp::mpq_trunc_fract;
        /// Computes the fractional part of the number.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -100/17 = -5 - 15/17
        /// let r = Rational::from((-100, 17));
        /// let rem = r.rem_trunc();
        /// assert_eq!(rem, (-15, 17));
        /// ```
        fn rem_trunc();
        /// Computes the fractional part of the number.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -100/17 = -5 - 15/17
        /// let mut r = Rational::from((-100, 17));
        /// r.rem_trunc_mut();
        /// assert_eq!(r, (-15, 17));
        /// ```
        fn rem_trunc_mut;
        /// Computes the fractional part of the number.
        ///
        /// The returned object implements
        /// [`AssignInto<Rational>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -100/17 = -5 - 15/17
        /// let r = Rational::from((-100, 17));
        /// let r_ref = r.rem_trunc_ref();
        /// let rem = Rational::from(r_ref);
        /// assert_eq!(rem, (-15, 17));
        /// ```
        fn rem_trunc_ref -> RemTruncRef;
    }
    rat_op_rat_int! {
        xgmp::mpq_trunc_fract_whole;
        /// Computes the fractional and truncated parts of the number.
        ///
        /// The initial value of `trunc` is ignored.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Integer, Rational};
        /// // -100/17 = -5 - 15/17
        /// let r = Rational::from((-100, 17));
        /// let (fract, trunc) = r.fract_trunc(Integer::new());
        /// assert_eq!(fract, (-15, 17));
        /// assert_eq!(trunc, -5);
        /// ```
        fn fract_trunc(trunc);
        /// Computes the fractional and truncated parts of the number.
        ///
        /// The initial value of `trunc` is ignored.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Integer, Rational};
        /// // -100/17 = -5 - 15/17
        /// let mut r = Rational::from((-100, 17));
        /// let mut whole = Integer::new();
        /// r.fract_trunc_mut(&mut whole);
        /// assert_eq!(r, (-15, 17));
        /// assert_eq!(whole, -5);
        /// ```
        fn fract_trunc_mut;
        /// Computes the fractional and truncated parts of the number.
        ///
        /// The returned object implements
        /// [`AssignInto<(&mut Rational, &mut Integer)>`][at].
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer, Rational};
        /// // -100/17 = -5 - 15/17
        /// let r = Rational::from((-100, 17));
        /// let r_ref = r.fract_trunc_ref();
        /// let (mut fract, mut trunc) = (Rational::new(), Integer::new());
        /// (&mut fract, &mut trunc).assign(r_ref);
        /// assert_eq!(fract, (-15, 17));
        /// assert_eq!(trunc, -5);
        /// ```
        ///
        /// [at]: (../ops/trait.AssignInto.html)
        fn fract_trunc_ref -> FractTruncRef;
    }
    rat_op_int! {
        xgmp::mpq_ceil;
        /// Rounds the number upwards (towards plus infinity) and returns
        /// it as an [`Integer`](struct.Integer.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -3.7
        /// let r1 = Rational::from((-37, 10));
        /// let i1 = r1.ceil();
        /// assert_eq!(i1, -3);
        /// // 3.3
        /// let r2 = Rational::from((33, 10));
        /// let i2 = r2.ceil();
        /// assert_eq!(i2, 4);
        /// ```
        fn ceil();
        /// Rounds the number upwards (towards plus infinity).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Rational};
        /// // -3.7
        /// let mut r = Rational::from((-37, 10));
        /// r.ceil_mut();
        /// assert_eq!(r, -3);
        /// // 3.3
        /// r.assign((33, 10));
        /// r.ceil_mut();
        /// assert_eq!(r, 4);
        /// ```
        fn ceil_mut;
        /// Rounds the number upwards (towards plus infinity).
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer, Rational};
        /// let mut ceil = Integer::new();
        /// // -3.7
        /// let r1 = Rational::from((-37, 10));
        /// ceil.assign(r1.ceil_ref());
        /// assert_eq!(ceil, -3);
        /// // 3.3
        /// let r2 = Rational::from((33, 10));
        /// ceil.assign(r2.ceil_ref());
        /// assert_eq!(ceil, 4);
        /// ```
        fn ceil_ref -> CeilRef;
    }
    math_op1! {
        xgmp::mpq_ceil_fract;
        /// Computes the non-positive remainder after rounding up.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // 100/17 = 6 - 2/17
        /// let r = Rational::from((100, 17));
        /// let rem = r.rem_ceil();
        /// assert_eq!(rem, (-2, 17));
        /// ```
        fn rem_ceil();
        /// Computes the non-positive remainder after rounding up.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // 100/17 = 6 - 2/17
        /// let mut r = Rational::from((100, 17));
        /// r.rem_ceil_mut();
        /// assert_eq!(r, (-2, 17));
        /// ```
        fn rem_ceil_mut;
        /// Computes the non-positive remainder after rounding up.
        ///
        /// The returned object implements
        /// [`AssignInto<Rational>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // 100/17 = 6 - 2/17
        /// let r = Rational::from((100, 17));
        /// let r_ref = r.rem_ceil_ref();
        /// let rem = Rational::from(r_ref);
        /// assert_eq!(rem, (-2, 17));
        /// ```
        fn rem_ceil_ref -> RemCeilRef;
    }
    rat_op_rat_int! {
        xgmp::mpq_ceil_fract_whole;
        /// Computes the fractional and ceil parts of the number.
        ///
        /// The fractional part cannot greater than zero. The initial
        /// value of `ceil` is ignored.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Integer, Rational};
        /// // 100/17 = 6 - 2/17
        /// let r = Rational::from((100, 17));
        /// let (fract, ceil) = r.fract_ceil(Integer::new());
        /// assert_eq!(fract, (-2, 17));
        /// assert_eq!(ceil, 6);
        /// ```
        fn fract_ceil(ceil);
        /// Computes the fractional and ceil parts of the number.
        ///
        /// The fractional part cannot be greater than zero. The initial
        /// value of `ceil` is ignored.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Integer, Rational};
        /// // 100/17 = 6 - 2/17
        /// let mut r = Rational::from((100, 17));
        /// let mut ceil = Integer::new();
        /// r.fract_ceil_mut(&mut ceil);
        /// assert_eq!(r, (-2, 17));
        /// assert_eq!(ceil, 6);
        /// ```
        fn fract_ceil_mut;
        /// Computes the fractional and ceil parts of the number.
        ///
        /// The fractional part cannot be greater than zero.
        ///
        /// The returned object implements
        /// [`AssignInto<(&mut Rational, &mut Integer)>`][at].
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer, Rational};
        /// // 100/17 = 6 - 2/17
        /// let r = Rational::from((100, 17));
        /// let r_ref = r.fract_ceil_ref();
        /// let (mut fract, mut ceil) = (Rational::new(), Integer::new());
        /// (&mut fract, &mut ceil).assign(r_ref);
        /// assert_eq!(fract, (-2, 17));
        /// assert_eq!(ceil, 6);
        /// ```
        ///
        /// [at]: (../ops/trait.AssignInto.html)
        fn fract_ceil_ref -> FractCeilRef;
    }
    rat_op_int! {
        xgmp::mpq_floor;
        /// Rounds the number downwards (towards minus infinity) and
        /// returns it as an [`Integer`](struct.Integer.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -3.7
        /// let r1 = Rational::from((-37, 10));
        /// let i1 = r1.floor();
        /// assert_eq!(i1, -4);
        /// // 3.3
        /// let r2 = Rational::from((33, 10));
        /// let i2 = r2.floor();
        /// assert_eq!(i2, 3);
        /// ```
        fn floor();
        /// Rounds the number downwards (towards minus infinity).
        ///
        /// ```rust
        /// use rug::{Assign, Rational};
        /// // -3.7
        /// let mut r = Rational::from((-37, 10));
        /// r.floor_mut();
        /// assert_eq!(r, -4);
        /// // 3.3
        /// r.assign((33, 10));
        /// r.floor_mut();
        /// assert_eq!(r, 3);
        /// ```
        fn floor_mut;
        /// Rounds the number downwards (towards minus infinity).
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer, Rational};
        /// let mut floor = Integer::new();
        /// // -3.7
        /// let r1 = Rational::from((-37, 10));
        /// floor.assign(r1.floor_ref());
        /// assert_eq!(floor, -4);
        /// // 3.3
        /// let r2 = Rational::from((33, 10));
        /// floor.assign(r2.floor_ref());
        /// assert_eq!(floor, 3);
        /// ```
        fn floor_ref -> FloorRef;
    }
    math_op1! {
        xgmp::mpq_floor_fract;
        /// Computes the non-negative remainder after rounding down.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -100/17 = -6 + 2/17
        /// let r = Rational::from((-100, 17));
        /// let rem = r.rem_floor();
        /// assert_eq!(rem, (2, 17));
        /// ```
        fn rem_floor();
        /// Computes the non-negative remainder after rounding down.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -100/17 = -6 + 2/17
        /// let mut r = Rational::from((-100, 17));
        /// r.rem_floor_mut();
        /// assert_eq!(r, (2, 17));
        /// ```
        fn rem_floor_mut;
        /// Computes the non-negative remainder after rounding down.
        ///
        /// The returned object implements
        /// [`AssignInto<Rational>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -100/17 = -6 + 2/17
        /// let r = Rational::from((-100, 17));
        /// let r_ref = r.rem_floor_ref();
        /// let rem = Rational::from(r_ref);
        /// assert_eq!(rem, (2, 17));
        /// ```
        fn rem_floor_ref -> RemFloorRef;
    }
    rat_op_rat_int! {
        xgmp::mpq_floor_fract_whole;
        /// Computes the fractional and floor parts of the number.
        ///
        /// The fractional part cannot be negative. The initial value of
        /// `floor` is ignored.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Integer, Rational};
        /// // -100/17 = -6 + 2/17
        /// let r = Rational::from((-100, 17));
        /// let (fract, floor) = r.fract_floor(Integer::new());
        /// assert_eq!(fract, (2, 17));
        /// assert_eq!(floor, -6);
        /// ```
        fn fract_floor(floor);
        /// Computes the fractional and floor parts of the number.
        ///
        /// The fractional part cannot be negative. The initial value of
        /// `floor` is ignored.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Integer, Rational};
        /// // -100/17 = -6 + 2/17
        /// let mut r = Rational::from((-100, 17));
        /// let mut floor = Integer::new();
        /// r.fract_floor_mut(&mut floor);
        /// assert_eq!(r, (2, 17));
        /// assert_eq!(floor, -6);
        /// ```
        fn fract_floor_mut;
        /// Computes the fractional and floor parts of the number.
        ///
        /// The fractional part cannot be negative.
        ///
        /// The returned object implements
        /// [`AssignInto<(&mut Rational, &mut Integer)>`][at].
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer, Rational};
        /// // -100/17 = -6 + 2/17
        /// let r = Rational::from((-100, 17));
        /// let r_ref = r.fract_floor_ref();
        /// let (mut fract, mut floor) = (Rational::new(), Integer::new());
        /// (&mut fract, &mut floor).assign(r_ref);
        /// assert_eq!(fract, (2, 17));
        /// assert_eq!(floor, -6);
        /// ```
        ///
        /// [at]: (../ops/trait.AssignInto.html)
        fn fract_floor_ref -> FractFloorRef;
    }
    rat_op_int! {
        xgmp::mpq_round;
        /// Rounds the number to the nearest integer and returns it as an
        /// [`Integer`](struct.Integer.html).
        ///
        /// When the number lies exactly between two integers, it is
        /// rounded away from zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -3.5
        /// let r1 = Rational::from((-35, 10));
        /// let i1 = r1.round();
        /// assert_eq!(i1, -4);
        /// // 3.7
        /// let r2 = Rational::from((37, 10));
        /// let i2 = r2.round();
        /// assert_eq!(i2, 4);
        /// ```
        fn round();
        /// Rounds the number to the nearest integer.
        ///
        /// When the number lies exactly between two integers, it is
        /// rounded away from zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Rational};
        /// // -3.5
        /// let mut r = Rational::from((-35, 10));
        /// r.round_mut();
        /// assert_eq!(r, -4);
        /// // 3.7
        /// r.assign((37, 10));
        /// r.round_mut();
        /// assert_eq!(r, 4);
        /// ```
        fn round_mut;
        /// Rounds the number to the nearest integer.
        ///
        /// When the number lies exactly between two integers, it is
        /// rounded away from zero.
        ///
        /// The returned object implements
        /// [`AssignInto<Integer>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer, Rational};
        /// let mut round = Integer::new();
        /// // -3.5
        /// let r1 = Rational::from((-35, 10));
        /// round.assign(r1.round_ref());
        /// assert_eq!(round, -4);
        /// // 3.7
        /// let r2 = Rational::from((37, 10));
        /// round.assign(r2.round_ref());
        /// assert_eq!(round, 4);
        /// ```
        fn round_ref -> RoundRef;
    }
    math_op1! {
        xgmp::mpq_round_fract;
        /// Computes the remainder after rounding to the nearest
        /// integer.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -3.5 = -4 + 0.5 = -4 + 1/2
        /// let r1 = Rational::from((-35, 10));
        /// let rem1 = r1.rem_round();
        /// assert_eq!(rem1, (1, 2));
        /// // 3.7 = 4 - 0.3 = 4 - 3/10
        /// let r2 = Rational::from((37, 10));
        /// let rem2 = r2.rem_round();
        /// assert_eq!(rem2, (-3, 10));
        /// ```
        fn rem_round();
        /// Computes the remainder after rounding to the nearest
        /// integer.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -3.5 = -4 + 0.5 = -4 + 1/2
        /// let mut r1 = Rational::from((-35, 10));
        /// r1.rem_round_mut();
        /// assert_eq!(r1, (1, 2));
        /// // 3.7 = 4 - 0.3 = 4 - 3/10
        /// let mut r2 = Rational::from((37, 10));
        /// r2.rem_round_mut();
        /// assert_eq!(r2, (-3, 10));
        /// ```
        fn rem_round_mut;
        /// Computes the remainder after rounding to the nearest
        /// integer.
        ///
        /// The returned object implements
        /// [`AssignInto<Rational>`](../ops/trait.AssignInto.html).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -3.5 = -4 + 0.5 = -4 + 1/2
        /// let r1 = Rational::from((-35, 10));
        /// let r_ref1 = r1.rem_round_ref();
        /// let rem1 = Rational::from(r_ref1);
        /// assert_eq!(rem1, (1, 2));
        /// // 3.7 = 4 - 0.3 = 4 - 3/10
        /// let r2 = Rational::from((37, 10));
        /// let r_ref2 = r2.rem_round_ref();
        /// let rem2 = Rational::from(r_ref2);
        /// assert_eq!(rem2, (-3, 10));
        /// ```
        fn rem_round_ref -> RemRoundRef;
    }
    rat_op_rat_int! {
        xgmp::mpq_round_fract_whole;
        /// Computes the fractional and rounded parts of the number.
        ///
        /// The fractional part is positive when the number is rounded
        /// down and negative when the number is rounded up. When the
        /// number lies exactly between two integers, it is rounded away
        /// from zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Integer, Rational};
        /// // -3.5 = -4 + 0.5 = -4 + 1/2
        /// let r1 = Rational::from((-35, 10));
        /// let (fract1, round1) = r1.fract_round(Integer::new());
        /// assert_eq!(fract1, (1, 2));
        /// assert_eq!(round1, -4);
        /// // 3.7 = 4 - 0.3 = 4 - 3/10
        /// let r2 = Rational::from((37, 10));
        /// let (fract2, round2) = r2.fract_round(Integer::new());
        /// assert_eq!(fract2, (-3, 10));
        /// assert_eq!(round2, 4);
        /// ```
        fn fract_round(round);
        /// Computes the fractional and round parts of the number.
        ///
        /// The fractional part is positive when the number is rounded
        /// down and negative when the number is rounded up. When the
        /// number lies exactly between two integers, it is rounded away
        /// from zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Integer, Rational};
        /// // -3.5 = -4 + 0.5 = -4 + 1/2
        /// let mut r1 = Rational::from((-35, 10));
        /// let mut round1 = Integer::new();
        /// r1.fract_round_mut(&mut round1);
        /// assert_eq!(r1, (1, 2));
        /// assert_eq!(round1, -4);
        /// // 3.7 = 4 - 0.3 = 4 - 3/10
        /// let mut r2 = Rational::from((37, 10));
        /// let mut round2 = Integer::new();
        /// r2.fract_round_mut(&mut round2);
        /// assert_eq!(r2, (-3, 10));
        /// assert_eq!(round2, 4);
        /// ```
        fn fract_round_mut;
        /// Computes the fractional and round parts of the number.
        ///
        /// The fractional part is positive when the number is rounded
        /// down and negative when the number is rounded up. When the
        /// number lies exactly between two integers, it is rounded away
        /// from zero.
        ///
        /// The returned object implements
        /// [`AssignInto<(&mut Rational, &mut Integer)>`][at].
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Assign, Integer, Rational};
        /// // -3.5 = -4 + 0.5 = -4 + 1/2
        /// let r1 = Rational::from((-35, 10));
        /// let r_ref1 = r1.fract_round_ref();
        /// let (mut fract1, mut round1) = (Rational::new(), Integer::new());
        /// (&mut fract1, &mut round1).assign(r_ref1);
        /// assert_eq!(fract1, (1, 2));
        /// assert_eq!(round1, -4);
        /// // 3.7 = 4 - 0.3 = 4 - 3/10
        /// let r2 = Rational::from((37, 10));
        /// let r_ref2 = r2.fract_round_ref();
        /// let (mut fract2, mut round2) = (Rational::new(), Integer::new());
        /// (&mut fract2, &mut round2).assign(r_ref2);
        /// assert_eq!(fract2, (-3, 10));
        /// assert_eq!(round2, 4);
        /// ```
        ///
        /// [at]: (../ops/trait.AssignInto.html)
        fn fract_round_ref -> FractRoundRef;
    }
}

ref_math_op1! { Rational; gmp::mpq_abs; struct AbsRef {} }
ref_rat_op_int! { xgmp::mpq_signum; struct SignumRef {} }

#[derive(Clone, Copy)]
pub struct ClampRef<'a, Min, Max>
where
    Rational: PartialOrd<Min>
        + PartialOrd<Max>
        + Assign<&'a Min>
        + Assign<&'a Max>,
    Min: 'a,
    Max: 'a,
{
    ref_self: &'a Rational,
    min: &'a Min,
    max: &'a Max,
}

impl<'a, Min, Max> AssignInto<Rational> for ClampRef<'a, Min, Max>
where
    Rational: PartialOrd<Min>
        + PartialOrd<Max>
        + Assign<&'a Min>
        + Assign<&'a Max>,
    Min: 'a,
    Max: 'a,
{
    #[inline]
    fn assign_into(self, dst: &mut Rational) {
        if self.ref_self.lt(self.min) {
            dst.assign(self.min);
            assert!(!(&*dst).gt(self.max), "minimum larger than maximum");
        } else if self.ref_self.gt(self.max) {
            dst.assign(self.max);
            assert!(!(&*dst).lt(self.min), "minimum larger than maximum");
        } else {
            dst.assign(self.ref_self);
        }
    }
}

impl<'a, Min, Max> From<ClampRef<'a, Min, Max>> for Rational
where
    Rational: PartialOrd<Min>
        + PartialOrd<Max>
        + Assign<&'a Min>
        + Assign<&'a Max>,
    Min: 'a,
    Max: 'a,
{
    #[inline]
    fn from(src: ClampRef<'a, Min, Max>) -> Self {
        let mut dst = Rational::new();
        src.assign_into(&mut dst);
        dst
    }
}

ref_math_op1! { Rational; xgmp::mpq_inv_check; struct RecipRef {} }
ref_rat_op_int! { xgmp::mpq_trunc; struct TruncRef {} }
ref_math_op1! { Rational; xgmp::mpq_trunc_fract; struct RemTruncRef {} }
ref_rat_op_rat_int! { xgmp::mpq_trunc_fract_whole; struct FractTruncRef {} }
ref_rat_op_int! { xgmp::mpq_ceil; struct CeilRef {} }
ref_math_op1! { Rational; xgmp::mpq_ceil_fract; struct RemCeilRef {} }
ref_rat_op_rat_int! { xgmp::mpq_ceil_fract_whole; struct FractCeilRef {} }
ref_rat_op_int! { xgmp::mpq_floor; struct FloorRef {} }
ref_math_op1! { Rational; xgmp::mpq_floor_fract; struct RemFloorRef {} }
ref_rat_op_rat_int! { xgmp::mpq_floor_fract_whole; struct FractFloorRef {} }
ref_rat_op_int! { xgmp::mpq_round; struct RoundRef {} }
ref_math_op1! { Rational; xgmp::mpq_round_fract; struct RemRoundRef {} }
ref_rat_op_rat_int! { xgmp::mpq_round_fract_whole; struct FractRoundRef {} }

#[derive(Clone, Copy)]
pub struct BorrowRational<'a> {
    inner: mpq_t,
    phantom: PhantomData<&'a Rational>,
}

impl<'a> Deref for BorrowRational<'a> {
    type Target = Rational;
    #[inline]
    fn deref(&self) -> &Rational {
        let ptr = (&self.inner) as *const _ as *const _;
        unsafe { &*ptr }
    }
}

pub fn append_to_string(
    s: &mut String,
    r: &Rational,
    radix: i32,
    to_upper: bool,
) {
    let (num, den) = r.as_numer_denom();
    let is_whole = *den == 1;
    let cap_for_den_nul = if is_whole {
        1
    } else {
        big_integer::req_chars(den, radix, 2)
    };
    let cap = big_integer::req_chars(num, radix, cap_for_den_nul);
    s.reserve(cap);
    big_integer::append_to_string(s, num, radix, to_upper);
    if !is_whole {
        s.push('/');
        big_integer::append_to_string(s, den, radix, to_upper);
    }
}

/// A validated string that can always be converted to a `Rational`.
///
/// See the [`Rational::valid_str_radix`][valid] method.
///
/// # Examples
///
/// ```rust
/// use rug::Rational;
/// use rug::rational::ValidRational;
/// // This string is correct in radix 10, it cannot fail.
/// let s = "123/456";
/// let valid: ValidRational = match Rational::valid_str_radix(s, 10) {
///     Ok(valid) => valid,
///     Err(_) => unreachable!(),
/// };
/// let r = Rational::from(valid);
/// assert_eq!(r, (123, 456));
/// ```
///
/// [valid]: ../struct.Rational.html#method.valid_str_radix
#[derive(Clone, Debug)]
pub struct ValidRational<'a> {
    bytes: &'a [u8],
    radix: i32,
}

impl<'a> AssignInto<Rational> for ValidRational<'a> {
    #[inline]
    fn assign_into(self, dst: &mut Rational) {
        let mut v = Vec::<u8>::with_capacity(self.bytes.len() + 1);
        v.extend_from_slice(self.bytes);
        v.push(0);
        let err = unsafe {
            let c_str = CStr::from_bytes_with_nul_unchecked(&v);
            gmp::mpq_set_str(dst.inner_mut(), c_str.as_ptr(), cast(self.radix))
        };
        assert_eq!(err, 0);
        unsafe {
            gmp::mpq_canonicalize(dst.inner_mut());
        }
    }
}

impl<'a> From<ValidRational<'a>> for Rational {
    #[inline]
    fn from(src: ValidRational<'a>) -> Self {
        let mut dst = Rational::new();
        src.assign_into(&mut dst);
        dst
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// An error which can be returned when parsing a `Rational` number.
///
/// # Examples
///
/// ```rust
/// use rug::Rational;
/// use rug::rational::ParseRationalError;
/// // This string is not a rational number.
/// let s = "something completely different (_!_!_)";
/// let error: ParseRationalError = match Rational::valid_str_radix(s, 4) {
///     Ok(_) => unreachable!(),
///     Err(error) => error,
/// };
/// println!("Parse error: {:?}", error);
/// ```
pub struct ParseRationalError {
    kind: ParseErrorKind,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum ParseErrorKind {
    InvalidDigit,
    NoDigits,
    NumerNoDigits,
    DenomNoDigits,
    TooManySlashes,
    DenomZero,
}

impl Error for ParseRationalError {
    fn description(&self) -> &str {
        use self::ParseErrorKind::*;
        match self.kind {
            InvalidDigit => "invalid digit found in string",
            NoDigits => "string has no digits",
            NumerNoDigits => "string has no digits for numerator",
            DenomNoDigits => "string has no digits for denominator",
            TooManySlashes => "more than one / found in string",
            DenomZero => "string has zero denominator",
        }
    }
}

/// Used to borrow the numerator and denominator of a
/// [`Rational`](../struct.Rational.html) number mutably.
///
/// The [`Rational`](../struct.Rational.html) number is canonicalized
/// when the borrow ends.
///
/// See the [`Rational::as_mut_numer_denom`][mutnumden] method.
///
/// # Examples
///
/// ```rust
/// use rug::Rational;
///
/// let mut r = Rational::from((3, 5));
/// {
///     let mut num_den = r.as_mut_numer_denom();
///     // change r from 3/5 to 4/8, which is equal to 1/2
///     *num_den.num() += 1;
///     *num_den.den() += 3;
///     // borrow ends here
/// }
/// let num_den = r.as_numer_denom();
/// assert_eq!(*num_den.0, 1);
/// assert_eq!(*num_den.1, 2);
/// ```
///
/// [mutnumden]: ../struct.Rational.html#method.as_mut_numer_denom
pub struct MutNumerDenom<'a> {
    num: &'a mut Integer,
    den_place: &'a mut Integer,
    den_actual: Integer,
}

impl<'a> MutNumerDenom<'a> {
    /// Gets the mutable numerator.
    #[inline]
    pub fn num(&mut self) -> &mut Integer {
        self.num
    }
    /// Gets the mutable denominator.
    #[inline]
    pub fn den(&mut self) -> &mut Integer {
        &mut self.den_actual
    }
    /// Gets the mutable numerator and denominator.
    #[inline]
    pub fn num_den(&mut self) -> (&mut Integer, &mut Integer) {
        (self.num, &mut self.den_actual)
    }
}

impl<'a> Drop for MutNumerDenom<'a> {
    #[inline]
    fn drop(&mut self) {
        assert_ne!(self.den_actual.cmp0(), Ordering::Equal, "division by zero");
        // We can finally place the actual denominator in its
        // proper place inside the rational number.
        mem::swap(&mut self.den_actual, self.den_place);
        unsafe {
            let rat_num = self.num.inner_mut();
            let rat_den = self.den_place.inner_mut();
            let mut canon: mpq_t = mem::uninitialized();
            let canon_num_ptr = gmp::mpq_numref(&mut canon);
            let canon_den_ptr = gmp::mpq_denref(&mut canon);
            ptr::copy_nonoverlapping(rat_num, &mut *canon_num_ptr, 1);
            ptr::copy_nonoverlapping(rat_den, &mut *canon_den_ptr, 1);
            gmp::mpq_canonicalize(&mut canon);
            ptr::copy_nonoverlapping(&*canon_num_ptr, rat_num, 1);
            ptr::copy_nonoverlapping(&*canon_den_ptr, rat_den, 1);
        }
    }
}

impl Inner for Rational {
    type Output = mpq_t;
    #[inline]
    fn inner(&self) -> &mpq_t {
        &self.inner
    }
}

impl InnerMut for Rational {
    #[inline]
    unsafe fn inner_mut(&mut self) -> &mut mpq_t {
        &mut self.inner
    }
}
