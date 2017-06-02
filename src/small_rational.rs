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

use Rational;
use gmp_mpfr_sys::gmp;
use rugint::Assign;
use std::mem;
use std::ops::Deref;
use std::os::raw::c_int;
use std::sync::atomic::{AtomicPtr, Ordering};

/// A small rational number that does not require any memory
/// allocation.
///
/// This can be useful when you have a numerator and denominator that
/// are 32-bit or 64-bit integers and you need a reference to a
/// `Rational`.
///
/// Although no allocation is required, setting the value of a
/// `SmallRational` does require some computation, as the numerator
/// and denominator need to be canonicalized.
///
/// The `SmallRational` type can be coerced to a `Rational`, as it
/// implements `Deref` with a `Rational` target.
///
/// # Examples
///
/// ```rust
/// use rugrat::{Rational, SmallRational};
/// // `a` requires a heap allocation
/// let mut a = Rational::from((100, 13));
/// // `b` can reside on the stack
/// let b = SmallRational::from((-100, 21));
/// a /= &*b;
/// assert_eq!(*a.numer(), -21);
/// assert_eq!(*a.denom(), 13);
/// ```
#[repr(C)]
pub struct SmallRational {
    num: Mpz,
    den: Mpz,
    num_limbs: [gmp::limb_t; LIMBS_IN_SMALL_INTEGER],
    den_limbs: [gmp::limb_t; LIMBS_IN_SMALL_INTEGER],
}

const LIMBS_IN_SMALL_INTEGER: usize = 64 / gmp::LIMB_BITS as usize;

#[repr(C)]
pub struct Mpz {
    alloc: c_int,
    size: c_int,
    d: AtomicPtr<gmp::limb_t>,
}

impl Default for SmallRational {
    fn default() -> SmallRational {
        SmallRational::new()
    }
}

impl SmallRational {
    /// Creates a `SmallRational` with value 0.
    pub fn new() -> SmallRational {
        let mut ret = SmallRational {
            num: Mpz {
                size: 0,
                alloc: LIMBS_IN_SMALL_INTEGER as c_int,
                d: Default::default(),
            },
            den: Mpz {
                size: 1,
                alloc: LIMBS_IN_SMALL_INTEGER as c_int,
                d: Default::default(),
            },
            num_limbs: [0; LIMBS_IN_SMALL_INTEGER],
            den_limbs: [0; LIMBS_IN_SMALL_INTEGER],
        };
        ret.den_limbs[0] = 1;
        ret
    }

    /// Creates a `SmallRational` from a 32-bit numerator and
    /// denominator, assuming they are in canonical form.
    ///
    /// # Safety
    ///
    /// This function is unsafe because
    ///
    /// * it does not check that the denominator is not zero, and
    ///
    /// * it does not canonicalize the numerator and denominator.
    ///
    /// The rest of the library assumes that `SmallRational` and
    /// `Rational` structures keep their numerators and denominators
    /// canonicalized.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::SmallRational;
    /// let from_unsafe = unsafe {
    ///     SmallRational::from_canonicalized_32(true, 13, 10)
    /// };
    /// // from_safe is canonicalized to the same form as from_unsafe
    /// let from_safe = SmallRational::from((130, -100));
    /// assert_eq!(from_unsafe.numer(), from_safe.numer());
    /// assert_eq!(from_unsafe.denom(), from_safe.denom());
    /// ```
    pub unsafe fn from_canonicalized_32(
        neg: bool,
        num: u32,
        den: u32,
    ) -> SmallRational {
        let mut ret = SmallRational::new();
        if num != 0 {
            ret.assign_canonicalized_32(neg, num, den);
        }
        ret
    }

    /// Creates a `SmallRational` from a 64-bit numerator and
    /// denominator, assuming they are in canonical form.
    ///
    /// # Safety
    ///
    /// This function is unsafe because
    ///
    /// * it does not check that the denominator is not zero, and
    ///
    /// * it does not canonicalize the numerator and denominator.
    ///
    /// The rest of the library assumes that `SmallRational` and
    /// `Rational` structures keep their numerators and denominators
    /// canonicalized.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::SmallRational;
    /// let from_unsafe = unsafe {
    ///     SmallRational::from_canonicalized_64(true, 13, 10)
    /// };
    /// // from_safe is canonicalized to the same form as from_unsafe
    ///
    /// let from_safe = SmallRational::from((130, -100));
    /// assert_eq!(from_unsafe.numer(), from_safe.numer());
    /// assert_eq!(from_unsafe.denom(), from_safe.denom());
    /// ```
    pub unsafe fn from_canonicalized_64(
        neg: bool,
        num: u64,
        den: u64,
    ) -> SmallRational {
        let mut ret = SmallRational::new();
        if num != 0 {
            ret.assign_canonicalized_64(neg, num, den);
        }
        ret
    }

    /// Sets a `SmallRational` to a 32-bit numerator and denominator,
    /// assuming they are in canonical form.
    ///
    /// # Safety
    ///
    /// This function is unsafe because
    ///
    /// * it does not check that the denominator is not zero, and
    ///
    /// * it does not canonicalize the numerator and denominator.
    ///
    /// The rest of the library assumes that `SmallRational` and
    /// `Rational` structures keep their numerators and denominators
    /// canonicalized.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::SmallRational;
    /// let mut from_unsafe = SmallRational::new();
    /// unsafe {
    ///     from_unsafe.assign_canonicalized_32(true, 13, 10)
    /// };
    /// // from_safe is canonicalized to the same form as from_unsafe
    /// let from_safe = SmallRational::from((130, -100));
    /// assert_eq!(from_unsafe.numer(), from_safe.numer());
    /// assert_eq!(from_unsafe.denom(), from_safe.denom());
    /// ```
    pub unsafe fn assign_canonicalized_32(
        &mut self,
        neg: bool,
        num: u32,
        den: u32,
    ) {
        self.num.size = if neg { -1 } else { 1 };
        self.num_limbs[0] = num as gmp::limb_t;
        self.den.size = 1;
        self.den_limbs[0] = den as gmp::limb_t;
    }

    /// Sets a `SmallRational` to a 64-bit numerator and denominator,
    /// assuming they are in canonical form.
    ///
    /// # Safety
    ///
    /// This function is unsafe because
    ///
    /// * it does not check that the denominator is not zero, and
    ///
    /// * it does not canonicalize the numerator and denominator.
    ///
    /// The rest of the library assumes that `SmallRational` and
    /// `Rational` structures keep their numerators and denominators
    /// canonicalized.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugrat::SmallRational;
    /// let mut from_unsafe = SmallRational::new();
    /// unsafe {
    ///     from_unsafe.assign_canonicalized_64(true, 13, 10)
    /// };
    /// // from_safe is canonicalized to the same form as from_unsafe
    /// let from_safe = SmallRational::from((130, -100));
    /// assert_eq!(from_unsafe.numer(), from_safe.numer());
    /// assert_eq!(from_unsafe.denom(), from_safe.denom());
    /// ```
    pub unsafe fn assign_canonicalized_64(
        &mut self,
        neg: bool,
        num: u64,
        den: u64,
    ) {
        match gmp::LIMB_BITS {
            64 => {
                self.num.size = if neg { -1 } else { 1 };
                self.num_limbs[0] = num as gmp::limb_t;
                self.den.size = 1;
                self.den_limbs[0] = den as gmp::limb_t;
            }
            32 => {
                if num <= 0xffff_ffff {
                    self.num.size = if neg { -1 } else { 1 };
                    self.num_limbs[0] = num as u32 as gmp::limb_t;
                } else {
                    self.num.size = if neg { -2 } else { 2 };
                    self.num_limbs[0] = num as u32 as gmp::limb_t;
                    self.num_limbs[1 + 0] = (num >> 32) as u32 as gmp::limb_t;
                }
                if den <= 0xffff_ffff {
                    self.den.size = 1;
                    self.den_limbs[0] = den as u32 as gmp::limb_t;
                } else {
                    self.den.size = 2;
                    self.den_limbs[0] = den as u32 as gmp::limb_t;
                    self.den_limbs[1 + 0] = (den >> 32) as u32 as gmp::limb_t;
                }
            }
            _ => {
                unreachable!();
            }
        }
    }

    fn set_num_den_32(&mut self, neg: bool, num: u32, den: u32) {
        assert_ne!(den, 0, "division by zero");
        if num == 0 {
            self.num.size = 0;
            self.den.size = 1;
            self.den_limbs[0] = 1;
            return;
        }
        unsafe {
            self.assign_canonicalized_32(neg, num, den);
        }
        self.update_d();
        unsafe {
            gmp::mpq_canonicalize((&mut self.num) as *mut _ as *mut _);
        }
    }

    fn set_num_den_64(&mut self, neg: bool, num: u64, den: u64) {
        assert_ne!(den, 0, "division by zero");
        if num == 0 {
            self.num.size = 0;
            self.den.size = 1;
            self.den_limbs[0] = 1;
            return;
        }
        unsafe {
            self.assign_canonicalized_64(neg, num, den);
        }
        self.update_d();
        unsafe {
            gmp::mpq_canonicalize((&mut self.num) as *mut _ as *mut _);
        }
    }

    fn update_d(&self) {
        // sanity check
        assert_eq!(mem::size_of::<Mpz>(), mem::size_of::<gmp::mpz_t>());
        // Since this is borrowed, the limbs won't move around, and we
        // can set the d fields.
        let num_d = &self.num_limbs[0] as *const _ as *mut _;
        self.num.d.store(num_d, Ordering::Relaxed);
        let den_d = &self.den_limbs[0] as *const _ as *mut _;
        self.den.d.store(den_d, Ordering::Relaxed);
    }
}

impl Deref for SmallRational {
    type Target = Rational;
    fn deref(&self) -> &Rational {
        self.update_d();
        let ptr = (&self.num) as *const _ as *const _;
        unsafe { &*ptr }
    }
}

impl<T> From<T> for SmallRational
where
    SmallRational: Assign<T>,
{
    fn from(val: T) -> SmallRational {
        let mut ret = SmallRational::new();
        ret.assign(val);
        ret
    }
}

impl Assign<i32> for SmallRational {
    fn assign(&mut self, num: i32) {
        unsafe {
            self.assign_canonicalized_32(num < 0, num.wrapping_abs() as u32, 1);
        }
    }
}

impl Assign<i64> for SmallRational {
    fn assign(&mut self, num: i64) {
        unsafe {
            self.assign_canonicalized_64(num < 0, num.wrapping_abs() as u64, 1);
        }
    }
}

impl Assign<u32> for SmallRational {
    fn assign(&mut self, num: u32) {
        unsafe {
            self.assign_canonicalized_32(false, num, 1);
        }
    }
}

impl Assign<u64> for SmallRational {
    fn assign(&mut self, num: u64) {
        unsafe {
            self.assign_canonicalized_64(false, num, 1);
        }
    }
}

impl Assign<(i32, i32)> for SmallRational {
    fn assign(&mut self, (num, den): (i32, i32)) {
        let num_neg = num < 0;
        let den_neg = den < 0;
        self.set_num_den_32(
            num_neg != den_neg,
            num.wrapping_abs() as u32,
            den.wrapping_abs() as u32,
        );
    }
}

impl Assign<(i64, i64)> for SmallRational {
    fn assign(&mut self, (num, den): (i64, i64)) {
        let num_neg = num < 0;
        let den_neg = den < 0;
        self.set_num_den_64(
            num_neg != den_neg,
            num.wrapping_abs() as u64,
            den.wrapping_abs() as u64,
        );
    }
}

impl Assign<(i32, u32)> for SmallRational {
    fn assign(&mut self, (num, den): (i32, u32)) {
        self.set_num_den_32(num < 0, num.wrapping_abs() as u32, den);
    }
}

impl Assign<(i64, u64)> for SmallRational {
    fn assign(&mut self, (num, den): (i64, u64)) {
        self.set_num_den_64(num < 0, num.wrapping_abs() as u64, den);
    }
}

impl Assign<(u32, i32)> for SmallRational {
    fn assign(&mut self, (num, den): (u32, i32)) {
        self.set_num_den_32(den < 0, num, den.wrapping_abs() as u32);
    }
}

impl Assign<(u64, i64)> for SmallRational {
    fn assign(&mut self, (num, den): (u64, i64)) {
        self.set_num_den_64(den < 0, num, den.wrapping_abs() as u64);
    }
}

impl Assign<(u32, u32)> for SmallRational {
    fn assign(&mut self, (num, den): (u32, u32)) {
        self.set_num_den_32(false, num, den);
    }
}

impl Assign<(u64, u64)> for SmallRational {
    fn assign(&mut self, (num, den): (u64, u64)) {
        self.set_num_den_64(false, num, den);
    }
}
