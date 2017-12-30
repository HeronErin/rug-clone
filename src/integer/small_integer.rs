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

use {Assign, Integer};

use gmp_mpfr_sys::gmp::{self, mpz_t};
use std::mem;
use std::ops::Deref;
use std::os::raw::c_int;
use std::sync::atomic::{AtomicPtr, Ordering};

#[repr(C)]
/// A small integer that does not require any memory allocation.
///
/// This can be useful when you have a `u64`, `i64`, `u32` or `i32`
/// but need a reference to an [`Integer`](../struct.Integer.html).
///
/// If there are functions that take a `u32` or `i32` directly instead
/// of an [`Integer`](../struct.Integer.html) reference, using them can
/// still be faster than using a `SmallInteger`; the functions would
/// still need to check for the size of an `Integer` obtained using
/// `SmallInteger`.
///
/// The `SmallInteger` type can be coerced to an
/// [`Integer`](../struct.Integer.html), as it implements
/// `Deref<Integer>`.
///
/// # Examples
///
/// ```rust
/// use rug::Integer;
/// use rug::integer::SmallInteger;
/// // `a` requires a heap allocation
/// let mut a = Integer::from(250);
/// // `b` can reside on the stack
/// let b = SmallInteger::from(-100);
/// a.lcm_mut(&b);
/// assert_eq!(a, 500);
/// // another computation:
/// a.lcm_mut(&SmallInteger::from(30));
/// assert_eq!(a, 1500);
/// ```
pub struct SmallInteger {
    inner: Mpz,
    limbs: [gmp::limb_t; LIMBS_IN_SMALL_INTEGER],
}

#[cfg(gmp_limb_bits_64)]
const LIMBS_IN_SMALL_INTEGER: usize = 1;
#[cfg(gmp_limb_bits_32)]
const LIMBS_IN_SMALL_INTEGER: usize = 2;

#[repr(C)]
pub struct Mpz {
    alloc: c_int,
    size: c_int,
    d: AtomicPtr<gmp::limb_t>,
}

impl Default for SmallInteger {
    #[inline]
    fn default() -> SmallInteger {
        SmallInteger::new()
    }
}

impl SmallInteger {
    /// Creates a `SmallInteger` with value 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::SmallInteger;
    /// let i = SmallInteger::new();
    /// // Borrow i as if it were Integer.
    /// assert_eq!(*i, 0);
    /// ```
    #[inline]
    pub fn new() -> SmallInteger {
        SmallInteger {
            inner: Mpz {
                size: 0,
                alloc: LIMBS_IN_SMALL_INTEGER as c_int,
                d: Default::default(),
            },
            limbs: [0; LIMBS_IN_SMALL_INTEGER],
        }
    }

    /// Returns a mutable reference to an
    /// [`Integer`](../struct.Integer.html) for simple operations that
    /// do not need to allocate more space for the number.
    ///
    /// # Safety
    ///
    /// It is undefined behaviour to perform operations that
    /// reallocate the internal data of the referenced
    /// [`Integer`](../struct.Integer.html) or to swap it with another
    /// number.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Assign;
    /// use rug::integer::SmallInteger;
    /// let mut i = SmallInteger::from(1u64);
    /// let capacity = i.capacity();
    /// // another u64 will not require a reallocation
    /// unsafe {
    ///     i.as_nonreallocating_mut().assign(2u64);
    /// }
    /// assert_eq!(*i, 2);
    /// assert_eq!(i.capacity(), capacity);
    /// ```
    #[inline]
    pub unsafe fn as_nonreallocating_mut(&mut self) -> &mut Integer {
        self.update_d();
        let ptr = (&mut self.inner) as *mut _ as *mut _;
        &mut *ptr
    }

    #[inline]
    fn update_d(&self) {
        // sanity check
        assert_eq!(mem::size_of::<Mpz>(), mem::size_of::<mpz_t>());
        // Since this is borrowed, the limbs won't move around, and we
        // can set the d field.
        let d = &self.limbs[0] as *const _ as *mut _;
        self.inner.d.store(d, Ordering::Relaxed);
    }
}

impl Deref for SmallInteger {
    type Target = Integer;
    #[inline]
    fn deref(&self) -> &Integer {
        self.update_d();
        let ptr = (&self.inner) as *const _ as *const _;
        unsafe { &*ptr }
    }
}

impl<T> From<T> for SmallInteger
where
    SmallInteger: Assign<T>,
{
    #[inline]
    fn from(val: T) -> SmallInteger {
        let mut ret = SmallInteger::new();
        ret.assign(val);
        ret
    }
}

impl Assign<i32> for SmallInteger {
    #[inline]
    fn assign(&mut self, val: i32) {
        self.assign(val.wrapping_abs() as u32);
        if val < 0 {
            self.inner.size = -self.inner.size;
        }
    }
}

impl Assign<i64> for SmallInteger {
    #[inline]
    fn assign(&mut self, val: i64) {
        self.assign(val.wrapping_abs() as u64);
        if val < 0 {
            self.inner.size = -self.inner.size;
        }
    }
}

impl Assign<u32> for SmallInteger {
    #[inline]
    fn assign(&mut self, val: u32) {
        if val == 0 {
            self.inner.size = 0;
        } else {
            self.inner.size = 1;
            self.limbs[0] = val.into();
        }
    }
}

impl Assign<u64> for SmallInteger {
    #[inline]
    fn assign(&mut self, val: u64) {
        #[cfg(gmp_limb_bits_64)]
        {
            if val == 0 {
                self.inner.size = 0;
            } else {
                self.inner.size = 1;
                self.limbs[0] = val as gmp::limb_t;
            }
        }
        #[cfg(gmp_limb_bits_32)]
        {
            if val == 0 {
                self.inner.size = 0;
            } else if val <= 0xffff_ffff {
                self.inner.size = 1;
                self.limbs[0] = val as u32 as gmp::limb_t;
            } else {
                self.inner.size = 2;
                self.limbs[0] = val as u32 as gmp::limb_t;
                self.limbs[1] = (val >> 32) as u32 as gmp::limb_t;
            }
        }
    }
}
