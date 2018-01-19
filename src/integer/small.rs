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

use cast::cast;
use gmp_mpfr_sys::gmp::{self, mpz_t};
use std::mem;
use std::ops::Deref;
use std::os::raw::c_int;
use std::sync::atomic::{AtomicPtr, Ordering};

/// A small integer that does not require any memory allocation.
///
/// This can be useful when you have a primitive integer type such as
/// `u64` or `i8`, but need a reference to an
/// [`Integer`](../struct.Integer.html).
///
/// If there are functions that take a `u32` or `i32` directly instead
/// of an [`Integer`](../struct.Integer.html) reference, using them can
/// still be faster than using a `SmallInteger`; the functions would
/// still need to check for the size of an `Integer` obtained using
/// `SmallInteger`.
///
/// The `SmallInteger` type can be coerced to an
/// [`Integer`](../struct.Integer.html), as it implements
/// `Deref<Target = Integer>`.
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
#[derive(Clone)]
#[repr(C)]
pub struct SmallInteger {
    inner: Mpz,
    limbs: [gmp::limb_t; LIMBS_IN_SMALL_INTEGER],
}

#[cfg(gmp_limb_bits_64)]
pub const LIMBS_IN_SMALL_INTEGER: usize = 1;
#[cfg(gmp_limb_bits_32)]
pub const LIMBS_IN_SMALL_INTEGER: usize = 2;

// Zero alloc means d is already set, so do nothing in update_d().
// This is useful for SmallRational implementation.
#[repr(C)]
pub struct Mpz {
    pub alloc: c_int,
    pub size: c_int,
    pub d: AtomicPtr<gmp::limb_t>,
}

impl Clone for Mpz {
    fn clone(&self) -> Mpz {
        Mpz {
            alloc: self.alloc,
            size: self.size,
            d: AtomicPtr::new(self.d.load(Ordering::Relaxed)),
        }
    }
}

impl Default for SmallInteger {
    #[inline]
    fn default() -> Self {
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
    pub fn new() -> Self {
        SmallInteger {
            inner: Mpz {
                size: 0,
                alloc: cast(LIMBS_IN_SMALL_INTEGER),
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
    ///     i.as_nonreallocating_integer().assign(2u64);
    /// }
    /// assert_eq!(*i, 2);
    /// assert_eq!(i.capacity(), capacity);
    /// ```
    #[inline]
    pub unsafe fn as_nonreallocating_integer(&mut self) -> &mut Integer {
        self.update_d();
        let ptr = (&mut self.inner) as *mut _ as *mut _;
        &mut *ptr
    }

    // Zero alloc means d is already set, so do nothing.
    #[inline]
    fn update_d(&self) {
        // sanity check
        assert_eq!(mem::size_of::<Mpz>(), mem::size_of::<mpz_t>());
        if self.inner.alloc != 0 {
            // Since this is borrowed, the limbs won't move around, and we
            // can set the d field.
            let d = &self.limbs[0] as *const _ as *mut _;
            self.inner.d.store(d, Ordering::Relaxed);
        }
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

macro_rules! signed {
    { $I:ty, $U:ty } => {
        impl Assign<$I> for SmallInteger {
            #[inline]
            fn assign(&mut self, val: $I) {
                self.assign(val.wrapping_abs() as $U);
                if val < 0 {
                    self.inner.size = -self.inner.size;
                }
            }
        }

        from_assign! { $I => SmallInteger }
    }
}

macro_rules! one_limb {
    { $U:ty } => {
        impl Assign<$U> for SmallInteger {
            #[inline]
            fn assign(&mut self, val: $U) {
                self.update_d();
                if val == 0 {
                    self.inner.size = 0;
                } else {
                    self.inner.size = 1;
                    unsafe {
                        *self.inner.d.load(Ordering::Relaxed) = val.into();
                    }
                }
            }
        }

        from_assign! { $U => SmallInteger }
    }
}

signed! { i8, u8 }
signed! { i16, u16 }
signed! { i32, u32 }
signed! { i64, u64 }
signed! { isize, usize }

one_limb! { u8 }
one_limb! { u16 }
one_limb! { u32 }

#[cfg(gmp_limb_bits_64)]
one_limb! { u64 }

#[cfg(gmp_limb_bits_32)]
impl Assign<u64> for SmallInteger {
    #[inline]
    fn assign(&mut self, val: u64) {
        self.update_d();
        if val == 0 {
            self.inner.size = 0;
        } else if val <= 0xffff_ffff {
            self.inner.size = 1;
            unsafe {
                *self.inner.d.load(Ordering::Relaxed) = cast(val as u32);
            }
        } else {
            self.inner.size = 2;
            unsafe {
                *self.inner.d.load(Ordering::Relaxed) = cast(val as u32);
                *self.inner.d.load(Ordering::Relaxed).offset(1) =
                    cast((val >> 32) as u32);
            }
        }
    }
}

#[cfg(gmp_limb_bits_32)]
from_assign! { u64 => SmallInteger }

impl Assign<usize> for SmallInteger {
    #[inline]
    fn assign(&mut self, val: usize) {
        #[cfg(target_pointer_width = "32")]
        {
            self.assign(val as u32);
        }
        #[cfg(target_pointer_width = "64")]
        {
            self.assign(val as u64);
        }
    }
}

from_assign! { usize => SmallInteger }

impl<'a> Assign<&'a Self> for SmallInteger {
    #[inline]
    fn assign(&mut self, other: &'a Self) {
        self.clone_from(other);
    }
}

impl<'a> Assign for SmallInteger {
    #[inline]
    fn assign(&mut self, other: Self) {
        mem::drop(mem::replace(self, other));
    }
}
