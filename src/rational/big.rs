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
use ext::gmp as xgmp;
use gmp_mpfr_sys::gmp::{self, mpq_t};
use inner::{Inner, InnerMut};
use integer::big as big_integer;
use misc;
use std::cmp::Ordering;
use std::error::Error;
use std::ffi::CString;
use std::i32;
use std::marker::PhantomData;
use std::mem;
use std::ops::{Add, AddAssign, Deref, Mul, MulAssign};
use std::ptr;
use {Assign, Integer};

/**
An arbitrary-precision rational number.

A `Rational` number is made up of a numerator [`Integer`] and
denominator [`Integer`]. After `Rational` number functions, the number
is always in canonical form, that is the denominator is always greater
than zero, and there are no common factors. Zero is stored as 0/1.

# Examples

```rust
use rug::Rational;
let r = Rational::from((-12, 15));
let recip = Rational::from(r.recip_ref());
assert_eq!(recip, (-5, 4));
assert_eq!(recip.to_f32(), -1.25);
// The numerator and denominator are stored in canonical form.
let (num, den) = r.into_numer_denom();
assert_eq!(num, -4);
assert_eq!(den, 5);
```

The `Rational` number type supports various functions. Most methods
have three versions:

 1. The first method consumes the operand.
 2. The second method has a “`_mut`” suffix and mutates the operand.
 3. The third method has a “`_ref`” suffix and borrows the operand.
    The returned item is an [incomplete-computation value][icv] that
    can be assigned to a `Rational` number.

```rust
use rug::Rational;

// 1. consume the operand
let a = Rational::from((-15, 2));
let abs_a = a.abs();
assert_eq!(abs_a, (15, 2));

// 2. mutate the operand
let mut b = Rational::from((-17, 2));
b.abs_mut();
assert_eq!(b, (17, 2));

// 3. borrow the operand
let c = Rational::from((-19, 2));
let r = c.abs_ref();
let abs_c = Rational::from(r);
assert_eq!(abs_c, (19, 2));
// c was not consumed
assert_eq!(c, (-19, 2));
```

[`Integer`]: struct.Integer.html
[icv]: index.html#incomplete-computation-values
*/
#[cfg_attr(repr_transparent, repr(transparent))]
pub struct Rational {
    inner: mpq_t,
}

fn _static_assertions() {
    static_assert_size!(Rational, mpq_t);
    static_assert_size!(BorrowRational, mpq_t);
}

macro_rules! rat_op_int {
    (
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($($param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Incomplete:ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(mut self, $($param: $T),*) -> Rational {
            self.$method_mut($($param),*);
            self
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
        pub fn $method_ref(&self, $($param: $T),*) -> $Incomplete {
            $Incomplete {
                ref_self: self,
                $($param,)*
            }
        }
    };
}

macro_rules! ref_rat_op_int {
    (
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Incomplete:ident { $($param:ident: $T:ty),* }
    ) => {
         $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a Rational,
            $($param: $T,)*
        }

        impl<'a> Assign<$Incomplete<'a>> for Integer {
            #[inline]
            fn assign(&mut self, src: $Incomplete) {
                unsafe {
                    $func(
                        self.inner_mut(),
                        src.ref_self.inner(),
                        $(src.$param.into(),)*
                    );
                }
            }
        }

        from_assign! { $Incomplete<'r> => Integer }
    };
}

macro_rules! rat_op_rat_int {
    (
        $func:path;
        $(#[$attr:meta])*
        fn $method:ident($int:ident $(, $param:ident: $T:ty),*);
        $(#[$attr_mut:meta])*
        fn $method_mut:ident;
        $(#[$attr_ref:meta])*
        fn $method_ref:ident -> $Incomplete:ident;
    ) => {
        $(#[$attr])*
        #[inline]
        pub fn $method(
            mut self,
            mut $int: Integer,
            $($param: $T,)*
        ) -> (Self, Integer) {
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
        pub fn $method_ref(&self, $($param: $T),*) -> $Incomplete {
            $Incomplete {
                ref_self: self,
                $($param,)*
            }
        }
    };
}

macro_rules! ref_rat_op_rat_int {
    (
        $func:path;
        $(#[$attr_ref:meta])*
        struct $Incomplete:ident { $($param:ident: $T:ty),* }
    ) => {
         $(#[$attr_ref])*
        #[derive(Debug)]
        pub struct $Incomplete<'a> {
            ref_self: &'a Rational,
            $($param: $T,)*
        }

        impl<'a, 'b, 'c>
            Assign<$Incomplete<'a>> for (&'b mut Rational, &'c mut Integer)
        {
            #[inline]
            fn assign(&mut self, src: $Incomplete) {
                unsafe {
                    $func(
                        self.0.inner_mut(),
                        self.1.inner_mut(),
                        src.ref_self.inner(),
                        $(src.$param.into(),)*
                    );
                }
            }
        }

        impl<'a> Assign<$Incomplete<'a>> for (Rational, Integer) {
            #[inline]
            fn assign(&mut self, src: $Incomplete) {
                <(&mut Rational, &mut Integer) as Assign<$Incomplete>>::assign(
                    &mut (&mut self.0, &mut self.1),
                    src,
                );
            }
        }

        impl<'a> From<$Incomplete<'a>> for (Rational, Integer) {
            #[inline]
            fn from(src: $Incomplete) -> Self {
                let mut dst = <Self as Default>::default();
                <Self as Assign<$Incomplete>>::assign(&mut dst, src);
                dst
            }
        }
    };
}

impl Rational {
    /// Constructs a new arbitrary-precision [`Rational`] number with
    /// value 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::new();
    /// assert_eq!(r, 0);
    /// ```
    ///
    /// [`Rational`]: struct.Rational.html
    #[inline]
    pub fn new() -> Self {
        unsafe {
            let mut ret: Rational = mem::uninitialized();
            gmp::mpq_init(ret.inner_mut());
            ret
        }
    }

    /// Creates a [`Rational`] number from an initialized
    /// [GMP rational number][`mpq_t`].
    ///
    /// # Safety
    ///
    ///   * The value must be initialized.
    ///   * The [`gmp_mpfr_sys::gmp::mpq_t`][`mpq_t`] type can be
    ///     considered as a kind of pointer, so there can be multiple
    ///     copies of it. Since this function takes over ownership, no
    ///     other copies of the passed value should exist.
    ///   * The numerator and denominator must be in canonical form,
    ///     as the rest of the library assumes that they are. Most GMP
    ///     functions leave the rational number in canonical form, but
    ///     assignment functions do not. Check the
    ///     [GMP documentation][gmp mpq] for details.
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
    ///
    /// [`Rational`]: struct.Rational.html
    /// [`mpq_t`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/struct.mpq_t.html
    /// [gmp mpq]: https://tspiteri.gitlab.io/gmp-mpfr-sys/gmp/Rational-Number-Functions.html#index-Rational-number-functions
    #[inline]
    pub unsafe fn from_raw(raw: mpq_t) -> Self {
        Rational { inner: raw }
    }

    /// Converts a [`Rational`] number into a
    /// [GMP rational number][`mpq_t`].
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
    ///
    /// [`Rational`]: struct.Rational.html
    /// [`mpq_t`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/struct.mpq_t.html
    #[inline]
    pub fn into_raw(self) -> mpq_t {
        let ret = self.inner;
        mem::forget(self);
        ret
    }

    /// Returns a pointer to the inner [GMP rational number][`mpq_t`].
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
    ///
    /// [`mpq_t`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/struct.mpq_t.html
    #[inline]
    pub fn as_raw(&self) -> *const mpq_t {
        self.inner()
    }

    /// Returns an unsafe mutable pointer to the inner
    /// [GMP rational number][`mpq_t`].
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
    ///
    /// [`mpq_t`]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/gmp/struct.mpq_t.html
    #[inline]
    pub fn as_raw_mut(&mut self) -> *mut mpq_t {
        unsafe { self.inner_mut() }
    }

    /// Creates a [`Rational`] number from an [`f32`] if it is
    /// [finite][`f32::is_finite`], losing no precision.
    ///
    /// If the compiler supports [`TryFrom`], this conversion can also
    /// be performed using `Rational::try_from(value)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use std::f32;
    /// // -17.125 can be stored exactly as f32
    /// let r = Rational::from_f32(-17.125).unwrap();
    /// assert_eq!(r, (-17125, 1000));
    /// let inf = Rational::from_f32(f32::INFINITY);
    /// assert!(inf.is_none());
    /// ```
    ///
    /// [`Rational`]: struct.Rational.html
    /// [`TryFrom`]: https://doc.rust-lang.org/nightly/std/convert/trait.TryFrom.html
    /// [`f32::is_finite`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html#method.is_finite
    /// [`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
    #[inline]
    pub fn from_f32(value: f32) -> Option<Self> {
        Rational::from_f64(value.into())
    }

    /// Creates a [`Rational`] number from an [`f64`] if it is
    /// [finite][`f64::is_finite`], losing no precision.
    ///
    /// If the compiler supports [`TryFrom`], this conversion can also
    /// be performed using `Rational::try_from(value)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use std::f64;
    /// // -17.125 can be stored exactly as f64
    /// let r = Rational::from_f64(-17.125).unwrap();
    /// assert_eq!(r, (-17125, 1000));
    /// let inf = Rational::from_f64(f64::INFINITY);
    /// assert!(inf.is_none());
    /// ```
    ///
    /// [`Rational`]: struct.Rational.html
    /// [`TryFrom`]: https://doc.rust-lang.org/nightly/std/convert/trait.TryFrom.html
    /// [`f64::is_finite`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
    /// [`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
    #[inline]
    pub fn from_f64(value: f64) -> Option<Self> {
        if value.is_finite() {
            let mut r = Rational::new();
            r.assign_f64(value).unwrap();
            Some(r)
        } else {
            None
        }
    }

    /// Parses a [`Rational`] number.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
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
    /// [`Rational`]: struct.Rational.html
    #[inline]
    pub fn from_str_radix(
        src: &str,
        radix: i32,
    ) -> Result<Self, ParseRationalError> {
        Ok(Rational::from(Rational::parse_radix(src, radix)?))
    }

    /// Parses a decimal string slice ([`&str`][str]) or byte slice
    /// ([`&[u8]`][slice]) into a [`Rational`] number.
    ///
    /// [`Assign<Src> for Rational`][`Assign`] and
    /// [`From<Src> for Rational`][`From`] are implemented with the
    /// unwrapped returned [incomplete-computation value][icv] as
    /// `Src`.
    ///
    /// The string must contain a numerator, and may contain a
    /// denominator; the numerator and denominator are separated with
    /// a “`/`”. The numerator can start with an optional minus or
    /// plus sign.
    ///
    /// ASCII whitespace is ignored everywhere in the string.
    /// Underscores are ignored anywhere except before the first digit
    /// of the numerator and between the “`/`” and the the first digit
    /// of the denominator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    ///
    /// let valid1 = Rational::parse("-12/23");
    /// let r1 = Rational::from(valid1.unwrap());
    /// assert_eq!(r1, (-12, 23));
    /// let valid2 = Rational::parse("+ 12 / 23");
    /// let r2 = Rational::from(valid2.unwrap());
    /// assert_eq!(r2, (12, 23));
    ///
    /// let invalid = Rational::parse("12/");
    /// assert!(invalid.is_err());
    /// ```
    ///
    /// [`Assign`]: trait.Assign.html
    /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
    /// [`Rational`]: struct.Rational.html
    /// [icv]: index.html#incomplete-computation-values
    /// [slice]: https://doc.rust-lang.org/nightly/std/primitive.slice.html
    /// [str]: https://doc.rust-lang.org/nightly/std/primitive.str.html
    #[inline]
    pub fn parse<S>(src: S) -> Result<ParseIncomplete, ParseRationalError>
    where
        S: AsRef<[u8]>,
    {
        parse(src.as_ref(), 10)
    }

    /// Parses a string slice ([`&str`][str]) or byte slice
    /// ([`&[u8]`][slice]) into a [`Rational`] number.
    ///
    /// [`Assign<Src> for Rational`][`Assign`] and
    /// [`From<Src> for Rational`][`From`] are implemented with the
    /// unwrapped returned [incomplete-computation value][icv] as
    /// `Src`.
    ///
    /// The string must contain a numerator, and may contain a
    /// denominator; the numerator and denominator are separated with
    /// a “`/`”. The numerator can start with an optional minus or
    /// plus sign.
    ///
    /// ASCII whitespace is ignored everywhere in the string.
    /// Underscores are ignored anywhere except before the first digit
    /// of the numerator and between the “`/`” and the the first digit
    /// of the denominator.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    ///
    /// let valid1 = Rational::parse_radix("12/23", 4);
    /// let r1 = Rational::from(valid1.unwrap());
    /// assert_eq!(r1, (2 + 4 * 1, 3 + 4 * 2));
    /// let valid2 = Rational::parse_radix("12 / yz", 36);
    /// let r2 = Rational::from(valid2.unwrap());
    /// assert_eq!(r2, (2 + 36 * 1, 35 + 36 * 34));
    ///
    /// let invalid = Rational::parse_radix("12/", 10);
    /// assert!(invalid.is_err());
    /// ```
    ///
    /// [`Assign`]: trait.Assign.html
    /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
    /// [`Rational`]: struct.Rational.html
    /// [icv]: index.html#incomplete-computation-values
    /// [slice]: https://doc.rust-lang.org/nightly/std/primitive.slice.html
    /// [str]: https://doc.rust-lang.org/nightly/std/primitive.str.html
    #[inline]
    pub fn parse_radix<S>(
        src: S,
        radix: i32,
    ) -> Result<ParseIncomplete, ParseRationalError>
    where
        S: AsRef<[u8]>,
    {
        parse(src.as_ref(), radix)
    }

    /// Converts to an [`f32`], rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rational::SmallRational;
    /// use rug::Rational;
    /// use std::f32;
    /// let min = Rational::from_f32(f32::MIN).unwrap();
    /// let minus_small = min - &*SmallRational::from((7, 2));
    /// // minus_small is truncated to f32::MIN
    /// assert_eq!(minus_small.to_f32(), f32::MIN);
    /// let times_three_two = minus_small * &*SmallRational::from((3, 2));
    /// // times_three_two is too small
    /// assert_eq!(times_three_two.to_f32(), f32::NEG_INFINITY);
    /// ```
    ///
    /// [`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
    #[inline]
    pub fn to_f32(&self) -> f32 {
        misc::trunc_f64_to_f32(self.to_f64())
    }

    /// Converts to an [`f64`], rounding towards zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rational::SmallRational;
    /// use rug::Rational;
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
    ///
    /// [`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
    #[inline]
    pub fn to_f64(&self) -> f64 {
        unsafe { gmp::mpq_get_d(self.inner()) }
    }

    /// Returns a string representation for the specified `radix`.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
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
    #[inline]
    pub fn to_string_radix(&self, radix: i32) -> String {
        let mut s = String::new();
        append_to_string(&mut s, self, radix, false);
        s
    }

    /// Assigns from an [`f32`] if it is [finite][`f32::is_finite`],
    /// losing no precision.
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
    ///
    /// [`f32::is_finite`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html#method.is_finite
    /// [`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
    #[inline]
    pub fn assign_f32(&mut self, val: f32) -> Result<(), ()> {
        self.assign_f64(val.into())
    }

    /// Assigns from an [`f64`] if it is [finite][`f64::is_finite`],
    /// losing no precision.
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
    ///
    /// [`f64::is_finite`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html#method.is_finite
    /// [`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
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

    /// Creates a new [`Rational`] number from a numerator and
    /// denominator without canonicalizing aftwerwards.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not canonicalize the
    /// [`Rational`] number. The caller must ensure that the numerator
    /// and denominator are in canonical form, as the rest of the
    /// library assumes that they are.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    ///
    /// // -3 / 5 is in canonical form
    /// let r = unsafe { Rational::from_canonical(-3, 5) };
    /// assert_eq!(r, (-3, 5));
    /// ```
    ///
    /// [`Rational`]: struct.Rational.html
    pub unsafe fn from_canonical<Num, Den>(num: Num, den: Den) -> Self
    where
        Integer: From<Num> + From<Den>,
    {
        let mut dst: Rational = mem::uninitialized();
        {
            let (dnum, dden) = dst.as_mut_numer_denom_no_canonicalization();
            ptr::write(dnum, Integer::from(num));
            ptr::write(dden, Integer::from(den));
        }
        dst
    }

    /// Assigns to the numerator and denominator without
    /// canonicalizing aftwerwards.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not canonicalize the
    /// [`Rational`] number after the assignment. The caller must
    /// ensure that the numerator and denominator are in canonical
    /// form, as the rest of the library assumes that they are.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    ///
    /// let mut r = Rational::new();
    /// // -3 / 5 is in canonical form
    /// unsafe {
    ///     r.assign_canonical(-3, 5);
    /// }
    /// assert_eq!(r, (-3, 5));
    /// ```
    ///
    /// [`Rational`]: struct.Rational.html
    pub unsafe fn assign_canonical<Num, Den>(&mut self, num: Num, den: Den)
    where
        Integer: Assign<Num> + Assign<Den>,
    {
        let (dst_num, dst_den) = self.as_mut_numer_denom_no_canonicalization();
        dst_num.assign(num);
        dst_den.assign(den);
    }

    /// Borrows the numerator as an [`Integer`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// assert_eq!(*r.numer(), -3)
    /// ```
    ///
    /// [`Integer`]: struct.Integer.html
    #[inline]
    pub fn numer(&self) -> &Integer {
        unsafe { &*cast_ptr!(gmp::mpq_numref_const(self.inner()), Integer) }
    }

    /// Borrows the denominator as an [`Integer`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let r = Rational::from((12, -20));
    /// // r will be canonicalized to -3 / 5
    /// assert_eq!(*r.denom(), 5);
    /// ```
    ///
    /// [`Integer`]: struct.Integer.html
    #[inline]
    pub fn denom(&self) -> &Integer {
        unsafe { &*cast_ptr!(gmp::mpq_denref_const(self.inner()), Integer) }
    }

    /// Calls a function with mutable references to the numerator and
    /// denominator, then canonicalizes the number.
    ///
    /// The denominator must not be zero when the function returns.
    ///
    /// # Panics
    ///
    /// Panics if the denominator is zero when the function returns.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// let mut r = Rational::from((3, 5));
    /// r.mutate_numer_denom(|num, den| {
    ///     // change r from 3/5 to 4/8, which is equal to 1/2
    ///     *num += 1;
    ///     *den += 3;
    /// });
    /// assert_eq!(*r.numer(), 1);
    /// assert_eq!(*r.denom(), 2);
    /// ```
    ///
    /// This method does not check that the numerator and denominator
    /// are in canonical form before calling `func`. This means that
    /// this method can be used to canonicalize the number after some
    /// unsafe methods that do not leave the number in cononical form.
    ///
    /// ```rust
    /// use rug::Rational;
    /// let mut r = Rational::from((3, 5));
    /// unsafe {
    ///     // leave r in non-canonical form
    ///     *r.as_mut_numer_denom_no_canonicalization().0 += 1;
    ///     *r.as_mut_numer_denom_no_canonicalization().1 -= 13;
    /// }
    /// // At this point, r is still not canonical: 4 / -8
    /// assert_eq!(*r.numer(), 4);
    /// assert_eq!(*r.denom(), -8);
    /// r.mutate_numer_denom(|_, _| {});
    /// // Now r is in canonical form: -1 / 2
    /// assert_eq!(*r.numer(), -1);
    /// assert_eq!(*r.denom(), 2);
    /// ```
    pub fn mutate_numer_denom<F>(&mut self, func: F)
    where
        F: FnOnce(&mut Integer, &mut Integer),
    {
        unsafe {
            let numer_ptr =
                cast_ptr_mut!(gmp::mpq_numref(self.inner_mut()), Integer);
            let denom_ptr =
                cast_ptr_mut!(gmp::mpq_denref(self.inner_mut()), Integer);
            func(&mut *numer_ptr, &mut *denom_ptr);
            assert_ne!(
                self.denom().cmp0(),
                Ordering::Equal,
                "division by zero"
            );
            gmp::mpq_canonicalize(self.inner_mut());
        }
    }

    /// Borrows the numerator and denominator mutably without
    /// canonicalizing aftwerwards.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not canonicalize the
    /// [`Rational`] number when the borrow ends. The caller must
    /// ensure that the numerator and denominator are left in
    /// canonical form, as the rest of the library assumes that they
    /// are.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    ///
    /// let mut r = Rational::from((3, 5));
    /// {
    ///     let (num, den) = unsafe { r.as_mut_numer_denom_no_canonicalization() };
    ///     // Add one to r by adding den to num. Since num and den
    ///     // are relatively prime, r remains in canonical form.
    ///     *num += &*den;
    /// }
    /// assert_eq!(r, (8, 5));
    /// ```
    ///
    /// This method can also be used to group some operations before
    /// canonicalization. This is usually not beneficial, as early
    /// canonicalization usually means subsequent arithmetic
    /// operations have less work to do.
    ///
    /// ```rust
    /// use rug::Rational;
    /// let mut r = Rational::from((3, 5));
    /// unsafe {
    ///     // first operation: add 1 to numerator
    ///     *r.as_mut_numer_denom_no_canonicalization().0 += 1;
    ///     // second operation: subtract 13 from denominator
    ///     *r.as_mut_numer_denom_no_canonicalization().1 -= 13;
    /// }
    /// // At this point, r is still not canonical: 4 / -8
    /// assert_eq!(*r.numer(), 4);
    /// assert_eq!(*r.denom(), -8);
    /// r.mutate_numer_denom(|_, _| {});
    /// // Now r is in canonical form: -1 / 2
    /// assert_eq!(*r.numer(), -1);
    /// assert_eq!(*r.denom(), 2);
    /// ```
    ///
    /// [`Rational`]: struct.Rational.html
    #[inline]
    pub unsafe fn as_mut_numer_denom_no_canonicalization(
        &mut self,
    ) -> (&mut Integer, &mut Integer) {
        (
            &mut *cast_ptr_mut!(gmp::mpq_numref(self.inner_mut()), Integer),
            &mut *cast_ptr_mut!(gmp::mpq_denref(self.inner_mut()), Integer),
        )
    }

    /// Converts into numerator and denominator [`Integer`] values.
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
    ///
    /// [`Integer`]: struct.Integer.html
    #[inline]
    pub fn into_numer_denom(self) -> (Integer, Integer) {
        let raw = self.into_raw();
        unsafe {
            let num = ptr::read(gmp::mpq_numref_const(&raw));
            let den = ptr::read(gmp::mpq_denref_const(&raw));
            (Integer::from_raw(num), Integer::from_raw(den))
        }
    }

    /// Borrows a negated copy of the [`Rational`] number.
    ///
    /// The returned object implements
    /// [`Deref<Target = Rational>`][`Deref`].
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
    ///
    /// [`Deref`]: https://doc.rust-lang.org/nightly/std/ops/trait.Deref.html
    /// [`Rational`]: struct.Rational.html
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

    /// Borrows an absolute copy of the [`Rational`] number.
    ///
    /// The returned object implements
    /// [`Deref<Target = Rational>`][`Deref`].
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
    ///
    /// [`Deref`]: https://doc.rust-lang.org/nightly/std/ops/trait.Deref.html
    /// [`Rational`]: struct.Rational.html
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

    /// Borrows a reciprocal copy of the [`Rational`] number.
    ///
    /// The returned object implements
    /// [`Deref<Target = Rational>`][`Deref`].
    ///
    /// This method performs some shallow copying, swapping numerator
    /// and denominator and making sure the sign is in the numerator.
    ///
    /// # Panics
    ///
    /// Panics if the value is zero.
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
    /// [`Deref`]: https://doc.rust-lang.org/nightly/std/ops/trait.Deref.html
    /// [`Rational`]: struct.Rational.html
    pub fn as_recip(&self) -> BorrowRational {
        assert_ne!(self.cmp0(), Ordering::Equal, "division by zero");
        let mut inner: mpq_t = unsafe { mem::uninitialized() };
        unsafe {
            let mut dst_num = ptr::read(self.denom().inner());
            let mut dst_den = ptr::read(self.numer().inner());
            if dst_den.size < 0 {
                dst_den.size = dst_den.size.wrapping_neg();
                dst_num.size = dst_num.size.checked_neg().expect("overflow");
            }
            ptr::write(gmp::mpq_numref(&mut inner), dst_num);
            ptr::write(gmp::mpq_denref(&mut inner), dst_den);
        }
        BorrowRational {
            inner,
            phantom: PhantomData,
        }
    }

    /// Returns the same result as [`self.cmp(&0.into())`][`cmp`], but
    /// is faster.
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
    ///
    /// [`cmp`]: https://doc.rust-lang.org/nightly/std/cmp/trait.Ord.html#tymethod.cmp
    #[inline]
    pub fn cmp0(&self) -> Ordering {
        self.numer().cmp0()
    }

    /// Compares the absolute values.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    /// use std::cmp::Ordering;
    /// let a = Rational::from((-23, 10));
    /// let b = Rational::from((-47, 5));
    /// assert_eq!(a.cmp(&b), Ordering::Greater);
    /// assert_eq!(a.cmp_abs(&b), Ordering::Less);
    /// ```
    #[inline]
    pub fn cmp_abs(&self, other: &Self) -> Ordering {
        self.as_abs().cmp(&*other.as_abs())
    }

    /// Adds a list of [`Rational`] values.
    ///
    /// [`Assign<Src> for Rational`][`Assign`],
    /// [`From<Src> for Rational`][`From`],
    /// [`AddAssign<Src> for Rational`][`AddAssign`] and
    /// [`Add<Src> for Rational`][`Add`] are implemented with the
    /// returned [incomplete-computation value][icv] as `Src`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    ///
    /// let values = [
    ///     Rational::from((5, 2)),
    ///     Rational::from((-100_000, 7)),
    ///     Rational::from(-4),
    /// ];
    ///
    /// let r = Rational::sum(values.iter());
    /// let sum = Rational::from(r);
    /// let expected = (5 * 7 - 100_000 * 2 - 4 * 14, 14);
    /// assert_eq!(sum, expected);
    /// ```
    ///
    /// [`AddAssign`]: https://doc.rust-lang.org/nightly/std/ops/trait.AddAssign.html
    /// [`Add`]: https://doc.rust-lang.org/nightly/std/ops/trait.Add.html
    /// [`Assign`]: trait.Assign.html
    /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
    /// [`Rational`]: struct.Rational.html
    /// [icv]: index.html#incomplete-computation-values
    #[inline]
    pub fn sum<'a, I>(values: I) -> SumIncomplete<'a, I>
    where
        I: Iterator<Item = &'a Self>,
    {
        SumIncomplete { values }
    }

    /// Finds the dot product of a list of [`Rational`] value pairs.
    ///
    /// [`Assign<Src> for Rational`][`Assign`],
    /// [`From<Src> for Rational`][`From`],
    /// [`AddAssign<Src> for Rational`][`AddAssign`] and
    /// [`Add<Src> for Rational`][`Add`] are implemented with the
    /// returned [incomplete-computation value][icv] as `Src`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    ///
    /// let a = [Rational::from((270, 7)), Rational::from((-11, 10))];
    /// let b = [Rational::from(7), Rational::from((1, 2))];
    ///
    /// let r = Rational::dot(a.iter().zip(b.iter()));
    /// let dot = Rational::from(r);
    /// let expected = (270 * 20 - 11, 20);
    /// assert_eq!(dot, expected);
    /// ```
    ///
    /// [`AddAssign`]: https://doc.rust-lang.org/nightly/std/ops/trait.AddAssign.html
    /// [`Add`]: https://doc.rust-lang.org/nightly/std/ops/trait.Add.html
    /// [`Assign`]: trait.Assign.html
    /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
    /// [`Rational`]: struct.Rational.html
    /// [icv]: index.html#incomplete-computation-values
    #[inline]
    pub fn dot<'a, I>(values: I) -> DotIncomplete<'a, I>
    where
        I: Iterator<Item = (&'a Self, &'a Self)>,
    {
        DotIncomplete { values }
    }

    /// Multiplies a list of [`Rational`] values.
    ///
    /// [`Assign<Src> for Rational`][`Assign`],
    /// [`From<Src> for Rational`][`From`],
    /// [`MulAssign<Src> for Rational`][`MulAssign`] and
    /// [`Mul<Src> for Rational`][`Mul`] are implemented with the
    /// returned [incomplete-computation value][icv] as `Src`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Rational;
    ///
    /// let values = [
    ///     Rational::from((5, 2)),
    ///     Rational::from((-100_000, 7)),
    ///     Rational::from(-4),
    /// ];
    ///
    /// let r = Rational::product(values.iter());
    /// let product = Rational::from(r);
    /// let expected = (5 * -100_000 * -4, 2 * 7);
    /// assert_eq!(product, expected);
    /// ```
    ///
    /// [`Assign`]: trait.Assign.html
    /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
    /// [`MulAssign`]: https://doc.rust-lang.org/nightly/std/ops/trait.MulAssign.html
    /// [`Mul`]: https://doc.rust-lang.org/nightly/std/ops/trait.Mul.html
    /// [`Rational`]: struct.Rational.html
    /// [icv]: index.html#incomplete-computation-values
    #[inline]
    pub fn product<'a, I>(values: I) -> ProductIncomplete<'a, I>
    where
        I: Iterator<Item = &'a Self>,
    {
        ProductIncomplete { values }
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
        /// [`Assign<Src> for Rational`][`Assign`] and
        /// [`From<Src> for Rational`][`From`] are implemented with
        /// the returned [incomplete-computation value][icv] as `Src`.
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
        ///
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn abs_ref -> AbsIncomplete;
    }
    rat_op_int! {
        xgmp::mpq_signum;
        /// Computes the signum.
        ///
        ///   * 0 if the value is zero
        ///   * 1 if the value is positive
        ///   * −1 if the value is negative
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
        ///   * 0 if the value is zero
        ///   * 1 if the value is positive
        ///   * −1 if the value is negative
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
        ///   * 0 if the value is zero
        ///   * 1 if the value is positive
        ///   * −1 if the value is negative
        ///
        /// [`Assign<Src> for Integer`][`Assign`],
        /// [`Assign<Src> for Rational`][`Assign`],
        /// [`From<Src> for Integer`][`From`] and
        /// [`From<Src> for Rational`][`From`] are implemented with
        /// the returned [incomplete-computation value][icv] as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::{Integer, Rational};
        /// let r = Rational::from((-100, 17));
        /// let r_ref = r.signum_ref();
        /// let signum = Integer::from(r_ref);
        /// assert_eq!(signum, -1);
        /// ```
        ///
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn signum_ref -> SignumIncomplete;
    }

    /// Clamps the value within the specified bounds.
    ///
    /// # Panics
    ///
    /// Panics if the maximum value is less than the minimum value.
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
    #[inline]
    pub fn clamp<'a, 'b, Min, Max>(mut self, min: &'a Min, max: &'b Max) -> Self
    where
        Self: PartialOrd<Min>
            + PartialOrd<Max>
            + Assign<&'a Min>
            + Assign<&'b Max>,
    {
        self.clamp_mut(min, max);
        self
    }

    /// Clamps the value within the specified bounds.
    ///
    /// # Panics
    ///
    /// Panics if the maximum value is less than the minimum value.
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
    pub fn clamp_mut<'a, 'b, Min, Max>(&mut self, min: &'a Min, max: &'b Max)
    where
        Self: PartialOrd<Min>
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
    /// [`Assign<Src> for Rational`][`Assign`] and
    /// [`From<Src> for Rational`][`From`] are implemented with the
    /// returned [incomplete-computation value][icv] as `Src`.
    ///
    /// # Panics
    ///
    /// Panics if the maximum value is less than the minimum value.
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
    /// [`Assign`]: trait.Assign.html
    /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
    /// [icv]: index.html#incomplete-computation-values
    #[inline]
    pub fn clamp_ref<'a, Min, Max>(
        &'a self,
        min: &'a Min,
        max: &'a Max,
    ) -> ClampIncomplete<'a, Min, Max>
    where
        Self: PartialOrd<Min>
            + PartialOrd<Max>
            + Assign<&'a Min>
            + Assign<&'a Max>,
    {
        ClampIncomplete {
            ref_self: self,
            min,
            max,
        }
    }

    math_op1! {
        xgmp::mpq_inv_check;
        /// Computes the reciprocal.
        ///
        /// # Panics
        ///
        /// Panics if the value is zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let r = Rational::from((-100, 17));
        /// let recip = r.recip();
        /// assert_eq!(recip, (-17, 100));
        /// ```
        fn recip();
        /// Computes the reciprocal.
        ///
        /// This method never reallocates or copies the heap data. It
        /// simply swaps the allocated data of the numerator and
        /// denominator and makes sure the denominator is stored as
        /// positive.
        ///
        /// # Panics
        ///
        /// Panics if the value is zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let mut r = Rational::from((-100, 17));
        /// r.recip_mut();
        /// assert_eq!(r, (-17, 100));
        /// ```
        fn recip_mut;
        /// Computes the reciprocal.
        ///
        /// [`Assign<Src> for Rational`][`Assign`] and
        /// [`From<Src> for Rational`][`From`] are implemented with
        /// the returned [incomplete-computation value][icv] as `Src`.
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
        ///
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn recip_ref -> RecipIncomplete;
    }
    rat_op_int! {
        xgmp::mpq_trunc;
        /// Rounds the number towards zero.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -3.7
        /// let r1 = Rational::from((-37, 10));
        /// let trunc1 = r1.trunc();
        /// assert_eq!(trunc1, -3);
        /// // 3.3
        /// let r2 = Rational::from((33, 10));
        /// let trunc2 = r2.trunc();
        /// assert_eq!(trunc2, 3);
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
        /// [`Assign<Src> for Integer`][`Assign`],
        /// [`Assign<Src> for Rational`][`Assign`],
        /// [`From<Src> for Integer`][`From`] and
        /// [`From<Src> for Rational`][`From`] are implemented with
        /// the returned [incomplete-computation value][icv] as `Src`.
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
        ///
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn trunc_ref -> TruncIncomplete;
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
        /// [`Assign<Src> for Rational`][`Assign`] and
        /// [`From<Src> for Rational`][`From`] are implemented with
        /// the returned [incomplete-computation value][icv] as `Src`.
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
        ///
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn rem_trunc_ref -> RemTruncIncomplete;
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
        /// [`Assign<Src> for (Rational, Integer)`][`Assign`],
        /// [`Assign<Src> for (&mut Rational, &mut Integer)`][`Assign`]
        /// and [`From<Src> for (Rational, Integer)`][`From`] are
        /// implemented with the returned
        /// [incomplete-computation value][icv] as `Src`.
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
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn fract_trunc_ref -> FractTruncIncomplete;
    }
    rat_op_int! {
        xgmp::mpq_ceil;
        /// Rounds the number upwards (towards plus infinity).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -3.7
        /// let r1 = Rational::from((-37, 10));
        /// let ceil1 = r1.ceil();
        /// assert_eq!(ceil1, -3);
        /// // 3.3
        /// let r2 = Rational::from((33, 10));
        /// let ceil2 = r2.ceil();
        /// assert_eq!(ceil2, 4);
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
        /// [`Assign<Src> for Integer`][`Assign`],
        /// [`Assign<Src> for Rational`][`Assign`],
        /// [`From<Src> for Integer`][`From`] and
        /// [`From<Src> for Rational`][`From`] are implemented with
        /// the returned [incomplete-computation value][icv] as `Src`.
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
        ///
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn ceil_ref -> CeilIncomplete;
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
        /// [`Assign<Src> for Rational`][`Assign`] and
        /// [`From<Src> for Rational`][`From`] are implemented with
        /// the returned [incomplete-computation value][icv] as `Src`.
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
        ///
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn rem_ceil_ref -> RemCeilIncomplete;
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
        /// [`Assign<Src> for (Rational, Integer)`][`Assign`],
        /// [`Assign<Src> for (&mut Rational, &mut Integer)`][`Assign`]
        /// and [`From<Src> for (Rational, Integer)`][`From`] are
        /// implemented with the returned
        /// [incomplete-computation value][icv] as `Src`.
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
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn fract_ceil_ref -> FractCeilIncomplete;
    }
    rat_op_int! {
        xgmp::mpq_floor;
        /// Rounds the number downwards (towards minus infinity).
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// // -3.7
        /// let r1 = Rational::from((-37, 10));
        /// let floor1 = r1.floor();
        /// assert_eq!(floor1, -4);
        /// // 3.3
        /// let r2 = Rational::from((33, 10));
        /// let floor2 = r2.floor();
        /// assert_eq!(floor2, 3);
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
        /// [`Assign<Src> for Integer`][`Assign`],
        /// [`Assign<Src> for Rational`][`Assign`],
        /// [`From<Src> for Integer`][`From`] and
        /// [`From<Src> for Rational`][`From`] are implemented with
        /// the returned [incomplete-computation value][icv] as `Src`.
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
        ///
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn floor_ref -> FloorIncomplete;
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
        /// [`Assign<Src> for Rational`][`Assign`] and
        /// [`From<Src> for Rational`][`From`] are implemented with
        /// the returned [incomplete-computation value][icv] as `Src`.
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
        ///
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn rem_floor_ref -> RemFloorIncomplete;
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
        /// [`Assign<Src> for (Rational, Integer)`][`Assign`],
        /// [`Assign<Src> for (&mut Rational, &mut Integer)`][`Assign`]
        /// and [`From<Src> for (Rational, Integer)`][`From`] are
        /// implemented with the returned
        /// [incomplete-computation value][icv] as `Src`.
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
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn fract_floor_ref -> FractFloorIncomplete;
    }
    rat_op_int! {
        xgmp::mpq_round;
        /// Rounds the number to the nearest integer.
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
        /// let round1 = r1.round();
        /// assert_eq!(round1, -4);
        /// // 3.7
        /// let r2 = Rational::from((37, 10));
        /// let round2 = r2.round();
        /// assert_eq!(round2, 4);
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
        /// [`Assign<Src> for Integer`][`Assign`],
        /// [`Assign<Src> for Rational`][`Assign`],
        /// [`From<Src> for Integer`][`From`] and
        /// [`From<Src> for Rational`][`From`] are implemented with
        /// the returned [incomplete-computation value][icv] as `Src`.
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
        ///
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn round_ref -> RoundIncomplete;
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
        /// [`Assign<Src> for Rational`][`Assign`] and
        /// [`From<Src> for Rational`][`From`] are implemented with
        /// the returned [incomplete-computation value][icv] as `Src`.
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
        ///
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn rem_round_ref -> RemRoundIncomplete;
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
        /// [`Assign<Src> for (Rational, Integer)`][`Assign`],
        /// [`Assign<Src> for (&mut Rational, &mut Integer)`][`Assign`]
        /// and [`From<Src> for (Rational, Integer)`][`From`] are
        /// implemented with the returned
        /// [incomplete-computation value][icv] as `Src`.
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
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn fract_round_ref -> FractRoundIncomplete;
    }
    math_op1! {
        xgmp::mpq_square;
        /// Computes the square.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let r = Rational::from((-13, 2));
        /// let square = r.square();
        /// assert_eq!(square, (169, 4));
        /// ```
        fn square();
        /// Computes the square.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let mut r = Rational::from((-13, 2));
        /// r.square_mut();
        /// assert_eq!(r, (169, 4));
        /// ```
        fn square_mut;
        /// Computes the square.
        ///
        /// [`Assign<Src> for Rational`][`Assign`] and
        /// [`From<Src> for Rational`][`From`] are implemented with
        /// the returned [incomplete-computation value][icv] as `Src`.
        ///
        /// # Examples
        ///
        /// ```rust
        /// use rug::Rational;
        /// let r = Rational::from((-13, 2));
        /// assert_eq!(Rational::from(r.square_ref()), (169, 4));
        /// ```
        ///
        /// [`Assign`]: trait.Assign.html
        /// [`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
        /// [icv]: index.html#incomplete-computation-values
        fn square_ref -> SquareIncomplete;
    }
}

#[derive(Debug)]
pub struct SumIncomplete<'a, I>
where
    I: Iterator<Item = &'a Rational>,
{
    values: I,
}

impl<'a, I> Assign<SumIncomplete<'a, I>> for Rational
where
    I: Iterator<Item = &'a Self>,
{
    fn assign(&mut self, mut src: SumIncomplete<'a, I>) {
        match src.values.next() {
            Some(first) => {
                self.assign(first);
            }
            None => {
                self.assign(0u32);
                return;
            }
        }
        self.add_assign(src);
    }
}

impl<'a, I> From<SumIncomplete<'a, I>> for Rational
where
    I: Iterator<Item = &'a Self>,
{
    fn from(mut src: SumIncomplete<'a, I>) -> Self {
        let mut dst = match src.values.next() {
            Some(first) => first.clone(),
            None => return Rational::new(),
        };
        dst.add_assign(src);
        dst
    }
}

impl<'a, I> Add<SumIncomplete<'a, I>> for Rational
where
    I: Iterator<Item = &'a Self>,
{
    type Output = Self;
    #[inline]
    fn add(mut self, rhs: SumIncomplete<'a, I>) -> Self {
        self.add_assign(rhs);
        self
    }
}

impl<'a, I> AddAssign<SumIncomplete<'a, I>> for Rational
where
    I: Iterator<Item = &'a Self>,
{
    fn add_assign(&mut self, src: SumIncomplete<'a, I>) {
        for i in src.values {
            self.add_assign(i);
        }
    }
}

#[derive(Debug)]
pub struct DotIncomplete<'a, I>
where
    I: Iterator<Item = (&'a Rational, &'a Rational)>,
{
    values: I,
}

impl<'a, I> Assign<DotIncomplete<'a, I>> for Rational
where
    I: Iterator<Item = (&'a Rational, &'a Rational)>,
{
    fn assign(&mut self, mut src: DotIncomplete<'a, I>) {
        match src.values.next() {
            Some(first) => {
                self.assign(first.0 * first.1);
            }
            None => {
                self.assign(0u32);
                return;
            }
        }
        self.add_assign(src);
    }
}

impl<'a, I> From<DotIncomplete<'a, I>> for Rational
where
    I: Iterator<Item = (&'a Rational, &'a Rational)>,
{
    fn from(mut src: DotIncomplete<'a, I>) -> Self {
        let mut dst = match src.values.next() {
            Some(first) => Rational::from(first.0 * first.1),
            None => return Rational::new(),
        };
        dst.add_assign(src);
        dst
    }
}

impl<'a, I> Add<DotIncomplete<'a, I>> for Rational
where
    I: Iterator<Item = (&'a Rational, &'a Rational)>,
{
    type Output = Self;
    #[inline]
    fn add(mut self, rhs: DotIncomplete<'a, I>) -> Self {
        self.add_assign(rhs);
        self
    }
}

impl<'a, I> AddAssign<DotIncomplete<'a, I>> for Rational
where
    I: Iterator<Item = (&'a Rational, &'a Rational)>,
{
    fn add_assign(&mut self, src: DotIncomplete<'a, I>) {
        let mut mul = Rational::new();
        for i in src.values {
            #[cfg_attr(
                feature = "cargo-clippy", allow(suspicious_op_assign_impl)
            )]
            mul.assign(i.0 * i.1);
            AddAssign::add_assign(self, &mul);
        }
    }
}

#[derive(Debug)]
pub struct ProductIncomplete<'a, I>
where
    I: Iterator<Item = &'a Rational>,
{
    values: I,
}

impl<'a, I> Assign<ProductIncomplete<'a, I>> for Rational
where
    I: Iterator<Item = &'a Self>,
{
    fn assign(&mut self, mut src: ProductIncomplete<'a, I>) {
        match src.values.next() {
            Some(first) => {
                self.assign(first);
            }
            None => {
                self.assign(1u32);
                return;
            }
        }
        self.mul_assign(src);
    }
}

impl<'a, I> From<ProductIncomplete<'a, I>> for Rational
where
    I: Iterator<Item = &'a Self>,
{
    fn from(mut src: ProductIncomplete<'a, I>) -> Self {
        let mut dst = match src.values.next() {
            Some(first) => first.clone(),
            None => return Rational::from(1),
        };
        dst.mul_assign(src);
        dst
    }
}

impl<'a, I> Mul<ProductIncomplete<'a, I>> for Rational
where
    I: Iterator<Item = &'a Self>,
{
    type Output = Self;
    #[inline]
    fn mul(mut self, rhs: ProductIncomplete<'a, I>) -> Self {
        self.mul_assign(rhs);
        self
    }
}

impl<'a, I> MulAssign<ProductIncomplete<'a, I>> for Rational
where
    I: Iterator<Item = &'a Self>,
{
    fn mul_assign(&mut self, mut src: ProductIncomplete<'a, I>) {
        let mut other = match src.values.next() {
            Some(next) => Rational::from(&*self * next),
            None => return,
        };
        loop {
            match src.values.next() {
                Some(next) => {
                    self.assign(&other * next);
                }
                None => {
                    self.assign(other);
                    return;
                }
            }
            match src.values.next() {
                Some(next) => {
                    other.assign(&*self * next);
                }
                None => {
                    return;
                }
            }
            if self.cmp0() == Ordering::Equal {
                return;
            }
        }
    }
}

ref_math_op1! { Rational; gmp::mpq_abs; struct AbsIncomplete {} }
ref_rat_op_int! { xgmp::mpq_signum; struct SignumIncomplete {} }

#[derive(Debug)]
pub struct ClampIncomplete<'a, Min, Max>
where
    Rational:
        PartialOrd<Min> + PartialOrd<Max> + Assign<&'a Min> + Assign<&'a Max>,
    Min: 'a,
    Max: 'a,
{
    ref_self: &'a Rational,
    min: &'a Min,
    max: &'a Max,
}

impl<'a, Min, Max> Assign<ClampIncomplete<'a, Min, Max>> for Rational
where
    Self: PartialOrd<Min> + PartialOrd<Max> + Assign<&'a Min> + Assign<&'a Max>,
    Min: 'a,
    Max: 'a,
{
    #[inline]
    fn assign(&mut self, src: ClampIncomplete<'a, Min, Max>) {
        if src.ref_self.lt(src.min) {
            self.assign(src.min);
            assert!(!(&*self).gt(src.max), "minimum larger than maximum");
        } else if src.ref_self.gt(src.max) {
            self.assign(src.max);
            assert!(!(&*self).lt(src.min), "minimum larger than maximum");
        } else {
            self.assign(src.ref_self);
        }
    }
}

impl<'a, Min, Max> From<ClampIncomplete<'a, Min, Max>> for Rational
where
    Self: PartialOrd<Min> + PartialOrd<Max> + Assign<&'a Min> + Assign<&'a Max>,
    Min: 'a,
    Max: 'a,
{
    #[inline]
    fn from(src: ClampIncomplete<'a, Min, Max>) -> Self {
        let mut dst = Rational::new();
        dst.assign(src);
        dst
    }
}

ref_math_op1! { Rational; xgmp::mpq_inv_check; struct RecipIncomplete {} }
ref_rat_op_int! { xgmp::mpq_trunc; struct TruncIncomplete {} }
ref_math_op1! { Rational; xgmp::mpq_trunc_fract; struct RemTruncIncomplete {} }
ref_rat_op_rat_int! {
    xgmp::mpq_trunc_fract_whole; struct FractTruncIncomplete {}
}
ref_rat_op_int! { xgmp::mpq_ceil; struct CeilIncomplete {} }
ref_math_op1! { Rational; xgmp::mpq_ceil_fract; struct RemCeilIncomplete {} }
ref_rat_op_rat_int! {
    xgmp::mpq_ceil_fract_whole; struct FractCeilIncomplete {}
}
ref_rat_op_int! { xgmp::mpq_floor; struct FloorIncomplete {} }
ref_math_op1! { Rational; xgmp::mpq_floor_fract; struct RemFloorIncomplete {} }
ref_rat_op_rat_int! {
    xgmp::mpq_floor_fract_whole; struct FractFloorIncomplete {}
}
ref_rat_op_int! { xgmp::mpq_round; struct RoundIncomplete {} }
ref_math_op1! { Rational; xgmp::mpq_round_fract; struct RemRoundIncomplete {} }
ref_rat_op_rat_int! {
    xgmp::mpq_round_fract_whole; struct FractRoundIncomplete {}
}
ref_math_op1! { Rational; xgmp::mpq_square; struct SquareIncomplete {} }

#[derive(Debug)]
#[cfg_attr(repr_transparent, repr(transparent))]
pub struct BorrowRational<'a> {
    inner: mpq_t,
    phantom: PhantomData<&'a Rational>,
}

impl<'a> Deref for BorrowRational<'a> {
    type Target = Rational;
    #[inline]
    fn deref(&self) -> &Rational {
        let ptr = cast_ptr!(&self.inner, Rational);
        unsafe { &*ptr }
    }
}

pub(crate) fn append_to_string(
    s: &mut String,
    r: &Rational,
    radix: i32,
    to_upper: bool,
) {
    let (num, den) = (r.numer(), r.denom());
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

#[derive(Debug)]
pub struct ParseIncomplete {
    c_string: CString,
    radix: i32,
}

impl Assign<ParseIncomplete> for Rational {
    #[inline]
    fn assign(&mut self, src: ParseIncomplete) {
        unsafe {
            let err = gmp::mpq_set_str(
                self.inner_mut(),
                src.c_string.as_ptr(),
                cast(src.radix),
            );
            assert_eq!(err, 0);
            gmp::mpq_canonicalize(self.inner_mut());
        }
    }
}

impl From<ParseIncomplete> for Rational {
    #[inline]
    fn from(src: ParseIncomplete) -> Self {
        let mut dst = Rational::new();
        dst.assign(src);
        dst
    }
}

fn parse(
    bytes: &[u8],
    radix: i32,
) -> Result<ParseIncomplete, ParseRationalError> {
    use self::ParseErrorKind as Kind;
    use self::ParseRationalError as Error;

    assert!(radix >= 2 && radix <= 36, "radix out of range");
    let bradix: u8 = cast(radix);
    let small_bound = b'a' - 10 + bradix;
    let capital_bound = b'A' - 10 + bradix;
    let digit_bound = b'0' + bradix;

    let mut v = Vec::with_capacity(bytes.len() + 1);
    let mut has_sign = false;
    let mut has_digits = false;
    let mut denom = false;
    let mut division_by_zero = false;
    for &b in bytes {
        if b == b'/' {
            if denom {
                return Err(Error {
                    kind: Kind::TooManySlashes,
                });
            }
            if !has_digits {
                return Err(Error {
                    kind: Kind::NumerNoDigits,
                });
            }
            v.push(b'/');
            has_digits = false;
            denom = true;
            division_by_zero = true;
            continue;
        }
        let valid_digit = match b {
            b'+' if !denom && !has_sign && !has_digits => {
                has_sign = true;
                continue;
            }
            b'-' if !denom && !has_sign && !has_digits => {
                v.push(b'-');
                has_sign = true;
                continue;
            }
            b'_' if has_digits => continue,
            b' ' | b'\t' | b'\n' | 0x0b | 0x0c | 0x0d => continue,

            _ if b >= b'a' => b < small_bound,
            _ if b >= b'A' => b < capital_bound,
            b'0'...b'9' => b < digit_bound,
            _ => false,
        };
        if !valid_digit {
            return Err(Error {
                kind: Kind::InvalidDigit,
            });
        }
        v.push(b);
        has_digits = true;
        division_by_zero = division_by_zero && b == b'0';
    }
    if !has_digits {
        return Err(Error {
            kind: if denom {
                Kind::DenomNoDigits
            } else {
                Kind::NoDigits
            },
        });
    }
    if division_by_zero {
        return Err(Error {
            kind: Kind::DenomZero,
        });
    }
    // we've only added b'-' and digits, so we know there are no nuls
    let c_string = unsafe { CString::from_vec_unchecked(v) };
    Ok(ParseIncomplete { c_string, radix })
}

#[derive(Debug)]
/**
An error which can be returned when parsing a [`Rational`] number.

See the [`Rational::parse_radix`] method for details on what strings
are accepted.

# Examples

```rust
use rug::rational::ParseRationalError;
use rug::Rational;
// This string is not a rational number.
let s = "something completely different (_!_!_)";
let error: ParseRationalError = match Rational::parse_radix(s, 4) {
    Ok(_) => unreachable!(),
    Err(error) => error,
};
println!("Parse error: {:?}", error);
```

[`Rational::parse_radix`]: ../struct.Rational.html#method.parse_radix
[`Rational`]: ../struct.Rational.html
*/
pub struct ParseRationalError {
    kind: ParseErrorKind,
}

#[derive(Debug)]
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
