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

use {Assign, DivFromAssign, NegAssign, NotAssign, Pow, PowAssign,
     SubFromAssign};
use gmp_mpfr_sys::gmp;

#[cfg(feature = "random")]
use rand::Rng;
use std::cmp::Ordering;
use std::ffi::{CStr, CString};
use std::fmt;
use std::mem;
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor,
               BitXorAssign, Div, DivAssign, Mul, MulAssign, Neg, Not, Rem,
               RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};
#[cfg(feature = "random")]
use std::os::raw::{c_int, c_long};
use std::os::raw::c_void;
use std::ptr;
#[cfg(feature = "random")]
use std::slice;
use std::str::FromStr;
use std::u32;

/// An arbitrary-precision integer.
///
/// Standard arithmetic operations, bitwise operations and comparisons
/// are supported. In standard arithmetic operations such as addition,
/// you can mix `Integer` and primitive integer types; the result will
/// be an `Integer`.
///
/// Internally the integer is not stored using two's-complement
/// representation, however, for bitwise operations and shifts, the
/// functionality is the same as if the representation was using two's
/// complement.
///
/// # Examples
///
/// ```rust
/// use rugint::Integer;
///
/// let mut i = Integer::from(1) << 1000;
/// // i is now 1000000... (1000 zeros)
/// assert!(i.significant_bits() == 1001);
/// assert!(i.find_one(0) == Some(1000));
/// i -= 1;
/// // i is now 111111... (1000 ones)
/// assert!(i.count_ones() == Some(1000));
///
/// let a = Integer::from(0xf00d);
/// let all_ones_xor_a = Integer::from(-1) ^ &a;
/// // a is unchanged as we borrowed it
/// let complement_a = !a;
/// // now a has been moved, so this would cause an error:
/// // assert!(a > 0);
/// assert!(all_ones_xor_a == complement_a);
/// assert!(complement_a == -0xf00e);
/// assert!(format!("{:x}", complement_a) == "-f00e");
/// ```
pub struct Integer {
    data: gmp::mpz_t,
}

fn raw(z: &Integer) -> &gmp::mpz_t {
    &z.data
}

fn raw_mut(z: &mut Integer) -> &mut gmp::mpz_t {
    &mut z.data
}

impl Drop for Integer {
    fn drop(&mut self) {
        unsafe {
            gmp::mpz_clear(raw_mut(self));
        }
    }
}

impl Default for Integer {
    fn default() -> Integer {
        Integer::new()
    }
}

impl Clone for Integer {
    fn clone(&self) -> Integer {
        let mut ret = Integer::new();
        ret.assign(self);
        ret
    }

    fn clone_from(&mut self, source: &Integer) {
        self.assign(source);
    }
}

impl Integer {
    /// Constructs a new arbitrary-precision integer with value 0.
    pub fn new() -> Integer {
        unsafe {
            let mut data: gmp::mpz_t = mem::uninitialized();
            gmp::mpz_init(&mut data);
            Integer { data: data }
        }
    }

    /// Converts to a `u32`.
    /// If the value is too large for the target type,
    /// only the least-significant bits are returned.
    pub fn to_u32(&self) -> u32 {
        unsafe { gmp::mpz_get_ui(raw(self)) as u32 }
    }

    /// Converts to an `i32`.
    /// If the value is too large for the target type,
    /// only the least-significant bits are returned.
    pub fn to_i32(&self) -> i32 {
        unsafe { gmp::mpz_get_si(raw(self)) as i32 }
    }

    /// Converts to an `f64` rounding towards zero.
    pub fn to_f64(&self) -> f64 {
        unsafe { gmp::mpz_get_d(raw(self)) }
    }

    /// Converts to an `f32` rounding towards zero.
    pub fn to_f32(&self) -> f32 {
        self.to_f64() as f32
    }

    /// Computes the quotient and remainder of `self` divided by
    /// `divisor. The remainder is stored in `divisor`.
    pub fn div_rem(&mut self, divisor: &mut Integer) {
        unsafe {
            gmp::mpz_tdiv_qr(raw_mut(self),
                             raw_mut(divisor),
                             raw(self),
                             raw(divisor))
        };
    }

    /// Computes the absolute value of `self`.
    pub fn abs(&mut self) -> &mut Integer {
        unsafe {
            gmp::mpz_abs(raw_mut(self), raw(self));
        }
        self
    }

    /// Divides `self` by `other`. This is much faster than normal
    /// division, but produces correct results only when the division
    /// is exact.
    ///
    /// # Panics
    ///
    /// Panics if `other` is zero.
    pub fn div_exact(&mut self, other: &Integer) -> &mut Integer {
        assert!(*other != 0);
        unsafe {
            gmp::mpz_divexact(raw_mut(self), raw(self), raw(other));
        }
        self
    }

    /// Returns `true` if `self` is divisible by `other`.
    pub fn is_divisible(&self, other: &Integer) -> bool {
        unsafe { gmp::mpz_divisible_p(raw(self), raw(other)) != 0 }
    }

    /// Returns `true` if `self` is congruent to `c` modulo `d`, that
    /// is, if there exists a `q` such that `self == c + q * d`.
    /// Unlike other division functions, `d` can be zero.
    pub fn is_congruent(&self, c: &Integer, d: &Integer) -> bool {
        unsafe { gmp::mpz_congruent_p(raw(self), raw(c), raw(d)) != 0 }
    }

    /// Computes the `n`th root of `self` and truncates the result.
    pub fn root(&mut self, n: u32) -> &mut Integer {
        unsafe {
            gmp::mpz_root(raw_mut(self), raw(self), n.into());
        }
        self
    }

    /// Computes the `n`th root of `self` and returns the truncated
    /// root and the remainder.  The remainder is `self` minus the
    /// truncated root raised to the power of `n`.
    /// The remainder is stored in `buf`.
    pub fn root_rem(&mut self, buf: &mut Integer, n: u32) {
        unsafe {
            gmp::mpz_rootrem(raw_mut(self), raw_mut(buf), raw(self), n.into());
        }
    }

    /// Computes the square root of `self` and truncates the result.
    pub fn sqrt(&mut self) -> &mut Integer {
        unsafe {
            gmp::mpz_sqrt(raw_mut(self), raw(self));
        }
        self
    }

    /// Computes the square root of `self` and returns the truncated
    /// root and the remainder.  The remainder is `self` minus the
    /// truncated root squared.
    /// The remainder is stored in `buf`.
    pub fn sqrt_rem(&mut self, buf: &mut Integer) {
        unsafe {
            gmp::mpz_sqrtrem(raw_mut(self), raw_mut(buf), raw(self));
        }
    }

    /// Returns `true` if `self` is a perfect power.
    pub fn is_perfect_power(&self) -> bool {
        unsafe { gmp::mpz_perfect_power_p(raw(self)) != 0 }
    }

    /// Returns `true` if `self` is a perfect square.
    pub fn is_perfect_square(&self) -> bool {
        unsafe { gmp::mpz_perfect_square_p(raw(self)) != 0 }
    }

    /// Finds the greatest common divisor. The result is always
    /// positive except when both inputs are zero.
    pub fn gcd(&mut self, other: &Integer) -> &mut Integer {
        unsafe {
            gmp::mpz_gcd(raw_mut(self), raw(self), raw(other));
        }
        self
    }

    /// Finds the least common multiple. The result is always positive
    /// except when one or both inputs are zero.
    pub fn lcm(&mut self, other: &Integer) -> &mut Integer {
        unsafe {
            gmp::mpz_lcm(raw_mut(self), raw(self), raw(other));
        }
        self
    }

    /// Finds the inverse of `self` modulo `m` if an inverse exists.
    ///
    /// # Panics
    ///
    /// Panics if `m` is zero.
    pub fn invert(&mut self, m: &Integer) -> Option<&mut Integer> {
        assert!(*m != 0);
        let exists =
            unsafe { gmp::mpz_invert(raw_mut(self), raw(self), raw(m)) != 0 };
        if exists { Some(self) } else { None }
    }

    /// Computes the factorial of `n`.
    /// The value of `self` is ignored.
    pub fn set_factorial(&mut self, n: u32) -> &mut Integer {
        unsafe {
            gmp::mpz_fac_ui(raw_mut(self), n.into());
        }
        self
    }

    /// Computes the double factorial of `n`.
    /// The value of `self` is ignored.
    pub fn set_factorial_2(&mut self, n: u32) -> &mut Integer {
        unsafe {
            gmp::mpz_2fac_ui(raw_mut(self), n.into());
        }
        self
    }

    /// Computes the `m`-multi factorial of `n`.
    /// The value of `self` is ignored.
    pub fn set_factorial_m(&mut self, n: u32, m: u32) -> &mut Integer {
        unsafe {
            gmp::mpz_mfac_uiui(raw_mut(self), n.into(), m.into());
        }
        self
    }

    /// Computes the primorial of `n`.
    /// The value of `self` is ignored.
    pub fn set_primorial(&mut self, n: u32) -> &mut Integer {
        unsafe {
            gmp::mpz_primorial_ui(raw_mut(self), n.into());
        }
        self
    }

    /// Computes the binomial coefficient `self` over `k`.
    pub fn binomial(&mut self, k: u32) -> &mut Integer {
        unsafe {
            gmp::mpz_bin_ui(raw_mut(self), raw(self), k.into());
        }
        self
    }

    /// Computes the binomial coefficient `n` over `k`.
    /// The value of `self` is ignored.
    pub fn set_binomial(&mut self, n: u32, k: u32) -> &mut Integer {
        unsafe {
            gmp::mpz_bin_uiui(raw_mut(self), n.into(), k.into());
        }
        self
    }

    /// Compares the absolute values of `self` and `other`.
    pub fn cmp_abs(&self, other: &Integer) -> Ordering {
        unsafe { gmp::mpz_cmpabs(raw(self), raw(other)).cmp(&0) }
    }

    /// Returns the same result as self.cmp(0), but is faster.
    pub fn sign(&self) -> Ordering {
        raw(self).size.cmp(&0)
    }

    /// Returns the number of bits required to represent the absolute
    /// value of `self`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    ///
    /// let i = Integer::from(0);
    /// assert!(i.significant_bits() == 0);
    /// let i = Integer::from(4);
    /// assert!(i.significant_bits() == 3);
    /// let i = Integer::from(7);
    /// assert!(i.significant_bits() == 3);
    /// ```
    pub fn significant_bits(&self) -> u32 {
        let bits = unsafe { gmp::mpz_sizeinbase(raw(self), 2) };
        if bits > u32::MAX as usize {
            panic!("overflow");
        }
        // sizeinbase returns 1 if number is 0
        if bits == 1 && *self == 0 {
            0
        } else {
            bits as u32
        }
    }

    /// Returns the number of ones in `self` if the value >= 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// assert!(Integer::from(0).count_ones() == Some(0));
    /// assert!(Integer::from(15).count_ones() == Some(4));
    /// assert!(Integer::from(-1).count_ones() == None);
    /// ```
    pub fn count_ones(&self) -> Option<u32> {
        bitcount_to_u32(unsafe { gmp::mpz_popcount(raw(self)) })
    }

    /// Retuns the Hamming distance between `self` and `other` if they
    /// have the same sign.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let i = Integer::from(-1);
    /// assert!(Integer::from(0).ham_dist(&i) == None);
    /// assert!(Integer::from(-1).ham_dist(&i) == Some(0));
    /// assert!(Integer::from(-13).ham_dist(&i) == Some(2));
    /// ```
    pub fn ham_dist(&self, other: &Integer) -> Option<u32> {
        bitcount_to_u32(unsafe { gmp::mpz_hamdist(raw(self), raw(other)) })
    }

    /// Returns the location of the first zero, starting at `start`.
    /// If the bit at location `start` is zero, returns `start`.
    ///
    /// ```rust
    /// use rugint::Integer;
    /// assert!(Integer::from(-2).find_zero(0) == Some(0));
    /// assert!(Integer::from(-2).find_zero(1) == None);
    /// assert!(Integer::from(15).find_zero(0) == Some(4));
    /// assert!(Integer::from(15).find_zero(20) == Some(20));
    pub fn find_zero(&self, start: u32) -> Option<u32> {
        bitcount_to_u32(unsafe { gmp::mpz_scan0(raw(self), start.into()) })
    }

    /// Returns the location of the first one, starting at `start`.
    /// If the bit at location `start` is one, returns `start`.
    ///
    /// ```rust
    /// use rugint::Integer;
    /// assert!(Integer::from(1).find_one(0) == Some(0));
    /// assert!(Integer::from(1).find_one(1) == None);
    /// assert!(Integer::from(-16).find_one(0) == Some(4));
    /// assert!(Integer::from(-16).find_one(20) == Some(20));
    pub fn find_one(&self, start: u32) -> Option<u32> {
        bitcount_to_u32(unsafe { gmp::mpz_scan1(raw(self), start.into()) })
    }

    /// Sets the bit at location `index` to 1 if `val` is `true` or 0
    /// if `val` is `false`.
    pub fn set_bit(&mut self, index: u32, val: bool) -> &mut Integer {
        unsafe {
            if val {
                gmp::mpz_setbit(raw_mut(self), index.into());
            } else {
                gmp::mpz_clrbit(raw_mut(self), index.into());
            }
        }
        self
    }

    /// Returns `true` if the bit at location `index` is 1 or `false`
    /// if the bit is 0.
    pub fn get_bit(&self, index: u32) -> bool {
        unsafe { gmp::mpz_tstbit(raw(self), index.into()) != 0 }
    }

    /// Toggles the bit at location `index`.
    pub fn invert_bit(&mut self, index: u32) -> &mut Integer {
        unsafe {
            gmp::mpz_combit(raw_mut(self), index.into());
        }
        self
    }

    #[cfg(feature = "random")]
    /// Generates a random number with a specified maximum number of
    /// bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rand;
    /// extern crate rugint;
    /// use rugint::Integer;
    /// fn main() {
    ///     let mut rng = rand::thread_rng();
    ///     let mut i = Integer::new();
    ///     i.assign_random_bits(0, &mut rng);
    ///     assert!(i == 0);
    ///     i.assign_random_bits(80, &mut rng);
    ///     assert!(i.significant_bits() <= 80);
    /// }
    /// ```
    pub fn assign_random_bits<R: Rng>(&mut self, bits: u32, rng: &mut R) {
        self.assign(0);
        if bits == 0 {
            return;
        }
        let limb_size = 8 * mem::size_of::<gmp::limb_t>() as u32;
        // limb_size is known at compile time for constant folding,
        // but we can still check once against gmp run time constant.
        assert!(limb_size == unsafe { gmp::bits_per_limb as u32 });
        let whole_limbs = (bits / limb_size) as usize;
        let extra_bits = bits % limb_size;
        // Avoid conditions and overflow, equivalent to:
        // let total_limbs = whole_limbs + if extra_bits == 0 { 0 } else { 1 };
        let total_limbs = whole_limbs +
                          ((extra_bits + limb_size - 1) / limb_size) as usize;
        let limbs = unsafe {
            if (raw(self).alloc as usize) < total_limbs {
                gmp::_mpz_realloc(raw_mut(self), total_limbs as c_long);
            }
            slice::from_raw_parts_mut(raw_mut(self).d, total_limbs)
        };
        let mut limbs_used: c_int = 0;
        for (i, limb) in limbs.iter_mut().enumerate() {
            let mut val: gmp::limb_t = rng.gen();
            if i == whole_limbs {
                val &= ((1 as gmp::limb_t) << extra_bits) - 1;
            }
            if val != 0 {
                limbs_used = i as c_int + 1;
            }
            *limb = val;
        }
        raw_mut(self).size = limbs_used;
    }

    #[cfg(feature = "random")]
    /// Generates a non-negative random number below the given
    /// boundary value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rand;
    /// extern crate rugint;
    /// use rugint::Integer;
    /// fn main() {
    ///     let mut rng = rand::thread_rng();
    ///     let bound = Integer::from(15);
    ///     let mut random = bound.clone();
    ///     random.random_below(&mut rng);
    ///     println!("0 <= {} < {}", random, bound);
    ///     assert!(random < bound);
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the boundary value is less than or equal to zero.
    pub fn random_below<R: Rng>(&mut self, rng: &mut R) -> &mut Integer {
        assert!(self.sign() == Ordering::Greater);
        let bits = self.significant_bits();
        let limb_size = 8 * mem::size_of::<gmp::limb_t>() as u32;
        // limb_size is known at compile time for constant folding,
        // but we can still check once against gmp run time constant.
        assert!(limb_size == unsafe { gmp::bits_per_limb as u32 });
        let whole_limbs = (bits / limb_size) as usize;
        let extra_bits = bits % limb_size;
        // Avoid conditions and overflow, equivalent to:
        // let total_limbs = whole_limbs + if extra_bits == 0 { 0 } else { 1 };
        let total_limbs = whole_limbs +
                          ((extra_bits + limb_size - 1) / limb_size) as usize;
        let limbs =
            unsafe { slice::from_raw_parts_mut(raw_mut(self).d, total_limbs) };
        // if the random number is >= bound, restart
        'restart: loop {
            let mut limbs_used: c_int = 0;
            let mut still_equal = true;
            'next_limb: for i in (0..total_limbs).rev() {
                let mut val: gmp::limb_t = rng.gen();
                if i == whole_limbs {
                    val &= ((1 as gmp::limb_t) << extra_bits) - 1;
                }
                if limbs_used == 0 && val != 0 {
                    limbs_used = i as c_int + 1;
                }
                if still_equal {
                    if val > limbs[i] {
                        continue 'restart;
                    }
                    if val == limbs[i] {
                        continue 'next_limb;
                    }
                    still_equal = false;
                }
                limbs[i] = val;
            }
            if !still_equal {
                raw_mut(self).size = limbs_used;
                return self;
            }
        }
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

    /// Parses an `Integer`.
    ///
    /// See the [corresponding assignment](#method.assign_str_radix).
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn from_str_radix(src: &str, radix: i32) -> Result<Integer, ()> {
        let mut i = Integer::new();
        i.assign_str_radix(src, radix)?;
        Ok(i)
    }

    /// Parses an `Integer` from a string.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// i.assign_str("123").unwrap();
    /// assert!(i == 123);
    /// let ret = i.assign_str("bad");
    /// assert!(ret.is_err());
    /// ```
    pub fn assign_str(&mut self, src: &str) -> Result<(), ()> {
        let c_str = CString::new(src).map_err(|_| ())?;
        let err = unsafe { gmp::mpz_set_str(raw_mut(self), c_str.as_ptr(), 0) };
        if err == 0 {
            Ok(())
        } else {
            self.assign(0);
            Err(())
        }
    }

    /// Parses an `Integer` from a string with the specified radix.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugint::Integer;
    /// let mut i = Integer::new();
    /// i.assign_str_radix("ff", 16).unwrap();
    /// assert!(i == 255);
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
        let err = unsafe {
            gmp::mpz_set_str(raw_mut(self), c_str.as_ptr(), radix.into())
        };
        if err == 0 {
            Ok(())
        } else {
            self.assign(0);
            Err(())
        }
    }
}

impl FromStr for Integer {
    type Err = ();

    /// Parses an `Integer`.
    ///
    /// See the [corresponding assignment](#method.assign_str).
    fn from_str(src: &str) -> Result<Integer, ()> {
        let mut i = Integer::new();
        i.assign_str(src)?;
        Ok(i)
    }
}

macro_rules! from_borrow {
    { $d: expr, $t:ty } => {
        impl<'a> From<&'a $t> for Integer {
            /// Constructs an `Integer` from
            #[doc=$d]
            fn from(t: &$t) -> Integer {
                let mut ret = Integer::new();
                ret.assign(t);
                ret
            }
        }
    };
}

macro_rules! from {
    { $d: expr, $t:ty } => {
        impl From<$t> for Integer {
            /// Constructs an `Integer` from
            #[doc=$d]
            fn from(t: $t) -> Integer {
                let mut ret = Integer::new();
                ret.assign(t);
                ret
            }
        }
    };
}

from_borrow! { "another `Integer`.", Integer }
from! { "a `u32`.", u32 }
from! { "an `i32`.", i32 }

impl<'a> Assign<&'a Integer> for Integer {
    /// Assigns from another `Integer`.
    fn assign(&mut self, other: &'a Integer) {
        unsafe {
            gmp::mpz_set(raw_mut(self), raw(other));
        }
    }
}

impl<'a> Assign<Integer> for Integer {
    /// Assigns from another `Integer`.
    fn assign(&mut self, other: Integer) {
        self.assign(&other);
    }
}

impl Assign<u32> for Integer {
    /// Assigns from a `u32`.
    fn assign(&mut self, val: u32) {
        unsafe { gmp::mpz_set_ui(raw_mut(self), val.into()) }
    }
}

impl Assign<i32> for Integer {
    /// Assigns from an `i32`.
    fn assign(&mut self, val: i32) {
        unsafe { gmp::mpz_set_si(raw_mut(self), val.into()) }
    }
}

impl Assign<f64> for Integer {
    /// Assigns from an `f64`, rounding towards zero.
    fn assign(&mut self, val: f64) {
        unsafe {
            gmp::mpz_set_d(raw_mut(self), val);
        }
    }
}

impl Assign<f32> for Integer {
    /// Assigns from an `f32`, rounding towards zero.
    fn assign(&mut self, val: f32) {
        self.assign(val as f64);
    }
}

macro_rules! arith_integer {
    ($imp:ident $method:ident,
     $imp_assign:ident $method_assign:ident,
     $func:path) => {
        impl<'a> $imp<&'a Integer> for Integer {
            type Output = Integer;
            fn $method(mut self, op: &'a Integer) -> Integer {
                $imp_assign::<&'a Integer>::$method_assign(&mut self, op);
                self
            }
        }

        impl $imp<Integer> for Integer {
            type Output = Integer;
            fn $method(self, op: Integer) -> Integer {
                self.$method(&op)
            }
        }

        impl<'a> $imp_assign<&'a Integer> for Integer {
            fn $method_assign(&mut self, op: &'a Integer) {
                unsafe {
                    $func(raw_mut(self), raw(self), raw(op));
                }
            }
        }

        impl $imp_assign<Integer> for Integer {
            fn $method_assign(&mut self, op: Integer) {
                self.$method_assign(&op);
            }
        }
    };
}

arith_integer! { Add add, AddAssign add_assign, gmp::mpz_add }
arith_integer! { Sub sub, SubAssign sub_assign, gmp::mpz_sub }
arith_integer! { Mul mul, MulAssign mul_assign, gmp::mpz_mul }
arith_integer! { Div div, DivAssign div_assign, gmp::mpz_tdiv_q }
arith_integer! { Rem rem, RemAssign rem_assign, gmp::mpz_tdiv_r }

impl SubFromAssign for Integer {
    fn sub_from_assign(&mut self, lhs: Integer) {
        self.sub_from_assign(&lhs);
    }
}

impl<'a> SubFromAssign<&'a Integer> for Integer {
    fn sub_from_assign(&mut self, lhs: &Integer) {
        unsafe {
            gmp::mpz_sub(raw_mut(self), raw(lhs), raw(self));
        }
    }
}

impl DivFromAssign for Integer {
    fn div_from_assign(&mut self, lhs: Integer) {
        self.div_from_assign(&lhs);
    }
}

impl<'a> DivFromAssign<&'a Integer> for Integer {
    fn div_from_assign(&mut self, lhs: &Integer) {
        unsafe {
            gmp::mpz_tdiv_q(raw_mut(self), raw(lhs), raw(self));
        }
    }
}

macro_rules! arith_prim_for_integer {
    ($imp:ident $method:ident,
     $imp_assign:ident $method_assign:ident,
     $t:ty,
     $func:path) => {
        impl $imp<$t> for Integer {
            type Output = Integer;
            fn $method(mut self, op: $t) -> Integer {
                self.$method_assign(op);
                self
            }
        }

        impl $imp_assign<$t> for Integer {
            fn $method_assign(&mut self, op: $t) {
                unsafe {
                    $func(raw_mut(self), raw(self), op.into());
                }
            }
        }
    };
}

macro_rules! arith_prim_non_commut {
    ($imp:ident $method:ident,
     $imp_assign:ident $method_assign:ident,
     $imp_from_assign:ident $method_from_assign:ident,
     $t:ty,
     $func:path,
     $func_from:path) => {
        arith_prim_for_integer! {
            $imp $method,
            $imp_assign $method_assign,
            $t,
            $func
        }

        impl $imp<Integer> for $t {
            type Output = Integer;
            fn $method(self, mut op: Integer) -> Integer {
                op.$method_from_assign(self);
                op
            }
        }

        impl<'a> $imp<&'a Integer> for $t {
            type Output = Integer;
            fn $method(self, op: &'a Integer) -> Integer {
                self.$method(op.clone())
            }
        }

        impl $imp_from_assign<$t> for Integer {
            fn $method_from_assign(&mut self, lhs: $t) {
                unsafe {
                    $func_from(raw_mut(self), lhs.into(), raw(self));
                }
            }
        }
    };
}

macro_rules! arith_prim_commut {
    ($imp:ident $method:ident,
     $imp_assign:ident $method_assign:ident,
     $t:ty,
     $func:path) => {
        arith_prim_for_integer! {
            $imp $method,
            $imp_assign $method_assign,
            $t,
            $func
        }

        impl $imp<Integer> for $t {
            type Output = Integer;
            fn $method(self, op: Integer) -> Integer {
                op.$method(self)
            }
        }

        impl<'a> $imp<&'a Integer> for $t {
            type Output = Integer;
            fn $method(self, op: &'a Integer) -> Integer {
                self.$method(op.clone())
            }
        }
    };
}

arith_prim_commut! { Add add, AddAssign add_assign, u32, gmp::mpz_add_ui }
arith_prim_non_commut! { Sub sub, SubAssign sub_assign,
                         SubFromAssign sub_from_assign,
                         u32, gmp::mpz_sub_ui, gmp::mpz_ui_sub }
arith_prim_commut! { Mul mul, MulAssign mul_assign, u32, gmp::mpz_mul_ui }
arith_prim_commut! { Mul mul, MulAssign mul_assign, i32, gmp::mpz_mul_si }
arith_prim_for_integer! { Div div, DivAssign div_assign, u32,
                          gmp::mpz_tdiv_q_ui }
arith_prim_for_integer! { Rem rem, RemAssign rem_assign, u32,
                          gmp::mpz_tdiv_r_ui }
arith_prim_for_integer! { Shl shl, ShlAssign shl_assign, u32,
                          gmp::mpz_mul_2exp }
arith_prim_for_integer! { Shr shr, ShrAssign shr_assign, u32,
                          gmp::mpz_fdiv_q_2exp }
arith_prim_for_integer! { Pow pow, PowAssign pow_assign, u32,
                          gmp::mpz_pow_ui }

impl Neg for Integer {
    type Output = Integer;
    fn neg(mut self) -> Integer {
        self.neg_assign();
        self
    }
}

impl NegAssign for Integer {
    fn neg_assign(&mut self) {
        unsafe {
            gmp::mpz_neg(raw_mut(self), raw(self));
        }
    }
}

impl Eq for Integer {}

impl Ord for Integer {
    fn cmp(&self, other: &Integer) -> Ordering {
        let ord = unsafe { gmp::mpz_cmp(raw(self), raw(other)) };
        ord.cmp(&0)
    }
}

impl PartialEq for Integer {
    fn eq(&self, other: &Integer) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl PartialOrd for Integer {
    fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<f64> for Integer {
    fn partial_cmp(&self, other: &f64) -> Option<Ordering> {
        if other.is_nan() {
            None
        } else {
            let ord = unsafe { gmp::mpz_cmp_d(raw(self), *other) };
            Some(ord.cmp(&0))
        }
    }
}

impl PartialEq<f64> for Integer {
    fn eq(&self, other: &f64) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

impl PartialOrd<Integer> for f64 {
    fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
        match other.partial_cmp(self) {
            None => None,
            Some(x) => Some(x.reverse()),
        }
    }
}

impl PartialEq<Integer> for f64 {
    fn eq(&self, other: &Integer) -> bool {
        other.eq(self)
    }
}

impl PartialOrd<f32> for Integer {
    fn partial_cmp(&self, other: &f32) -> Option<Ordering> {
        let o = *other as f64;
        self.partial_cmp(&o)
    }
}

impl PartialEq<f32> for Integer {
    fn eq(&self, other: &f32) -> bool {
        let o = *other as f64;
        self.eq(&o)
    }
}

impl PartialEq<Integer> for f32 {
    fn eq(&self, other: &Integer) -> bool {
        other.eq(self)
    }
}

impl PartialOrd<Integer> for f32 {
    fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
        match other.partial_cmp(self) {
            None => None,
            Some(x) => Some(x.reverse()),
        }
    }
}

macro_rules! cmp_int {
    { $t:ty, $func:path } => {
        impl PartialOrd<$t> for Integer {
            fn partial_cmp(&self, other: &$t) -> Option<Ordering> {
                let ord = unsafe { $func(raw(self), (*other).into()) };
                Some(ord.cmp(&0))
            }
        }

        impl PartialEq<$t> for Integer {
            fn eq(&self, other: &$t) -> bool {
                self.partial_cmp(other) == Some(Ordering::Equal)
            }
        }

        impl PartialOrd<Integer> for $t {
            fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
                match other.partial_cmp(self) {
                    Some(x) => Some(x.reverse()),
                    None => None,
                }
            }
        }

        impl PartialEq<Integer> for $t {
            fn eq(&self, other: &Integer) -> bool {
                other.eq(self)
            }
        }
    };
}

cmp_int! { u32, gmp::mpz_cmp_ui }
cmp_int! { i32, gmp::mpz_cmp_si }

macro_rules! bit {
    ($Tr:ident $method:ident,
     $TrAssign:ident $method_assign:ident,
     $func:path) => {
        impl<'a> $Tr<&'a Integer> for Integer {
            type Output = Integer;
            fn $method(mut self, op: &'a Integer) -> Integer {
                self.$method_assign(op);
                self
            }
        }

        impl $Tr for Integer {
            type Output = Integer;
            fn $method(self, op: Integer) -> Integer {
                self.$method(&op)
            }
        }

        impl<'a> $TrAssign<&'a Integer> for Integer {
            fn $method_assign(&mut self, op: &'a Integer) {
                unsafe {
                    $func(raw_mut(self), raw(self), raw(op));
                }
            }
        }

        impl $TrAssign<Integer> for Integer {
            fn $method_assign(&mut self, op: Integer) {
                self.$method_assign(&op);
            }
        }
    };
}

bit! { BitAnd bitand, BitAndAssign bitand_assign, gmp::mpz_and }
bit! { BitOr bitor, BitOrAssign bitor_assign, gmp::mpz_ior }
bit! { BitXor bitxor, BitXorAssign bitxor_assign, gmp::mpz_xor }

impl Not for Integer {
    type Output = Integer;
    fn not(mut self) -> Integer {
        self.not_assign();
        self
    }
}

impl NotAssign for Integer {
    fn not_assign(&mut self) {
        unsafe {
            gmp::mpz_com(raw_mut(self), raw(self));
        }
    }
}

impl Integer {
    fn make_string(&self, radix: i32, to_upper: bool, prefix: &str) -> String {
        assert!(radix >= 2 && radix <= 36, "radix out of range");
        let s;
        let cstr;
        unsafe {
            s = gmp::mpz_get_str(ptr::null_mut(), radix.into(), raw(self));
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

impl fmt::Display for Integer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string_radix(10))
    }
}

impl fmt::Debug for Integer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.make_string(16, false, "0x"))
    }
}

impl fmt::Binary for Integer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let prefix = if f.alternate() { "0b" } else { "" };
        write!(f, "{}", self.make_string(2, false, prefix))
    }
}

impl fmt::Octal for Integer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let prefix = if f.alternate() { "0o" } else { "" };
        write!(f, "{}", self.make_string(8, false, prefix))
    }
}

impl fmt::LowerHex for Integer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let prefix = if f.alternate() { "0x" } else { "" };
        write!(f, "{}", self.make_string(16, false, prefix))
    }
}

impl fmt::UpperHex for Integer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let prefix = if f.alternate() { "0X" } else { "" };
        write!(f, "{}", self.make_string(16, true, prefix))
    }
}

fn bitcount_to_u32(bits: gmp::bitcnt_t) -> Option<u32> {
    let max: gmp::bitcnt_t = !0;
    if bits == max {
        None
    } else if bits > u32::MAX as gmp::bitcnt_t {
        panic!("overflow")
    } else {
        Some(bits as u32)
    }
}
