// Copyright © 2016–2022 Trevor Spiteri

// This program is free software: you can redistribute it and/or modify it under
// the terms of the GNU Lesser General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
// details.
//
// You should have received a copy of the GNU Lesser General Public License and
// a copy of the GNU General Public License along with this program. If not, see
// <https://www.gnu.org/licenses/>.

use crate::Float;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use gmp_mpfr_sys::mpfr::mpfr_t;

/// Used to get a reference to a [`Float`].
///
/// The struct implements <code>[Deref]\<[Target][Deref::Target] = [Float]></code>.
///
/// No memory is unallocated when this struct is dropped.
///
/// # Examples
///
/// ```rust
/// use rug::float::BorrowFloat;
/// use rug::Float;
/// let f = Float::with_val(53, 4.2);
/// let neg: BorrowFloat = f.as_neg();
/// // f is still valid
/// assert_eq!(f, 4.2);
/// assert_eq!(*neg, -4.2);
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct BorrowFloat<'a> {
    inner: ManuallyDrop<Float>,
    phantom: PhantomData<&'a Float>,
}

impl BorrowFloat<'_> {
    /// Create a borrow from a raw [MPFR floating-point number][mpfr_t].
    ///
    /// # Safety
    ///
    ///   * The value must be initialized.
    ///   * The [`mpfr_t`] type can be considered as a kind of pointer, so there
    ///     can be multiple copies of it. [`BorrowFloat`] cannot mutate the
    ///     value, so there can be other copies, but none of them are allowed to
    ///     mutate the value.
    ///   * The lifetime is obtained from the return type. The user must ensure
    ///     the value remains valid for the duration of the lifetime.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::float::BorrowFloat;
    /// use rug::Float;
    /// let f = Float::with_val(53, 4.2);
    /// // Safety: f.as_raw() is a valid pointer.
    /// let raw = unsafe { *f.as_raw() };
    /// // Safety: f is still valid when borrow is used.
    /// let borrow = unsafe { BorrowFloat::from_raw(raw) };
    /// assert_eq!(f, *borrow);
    /// ```
    pub unsafe fn from_raw<'a>(raw: mpfr_t) -> BorrowFloat<'a> {
        BorrowFloat {
            inner: ManuallyDrop::new(unsafe { Float::from_raw(raw) }),
            phantom: PhantomData,
        }
    }
}

impl Deref for BorrowFloat<'_> {
    type Target = Float;
    #[inline]
    fn deref(&self) -> &Float {
        &self.inner
    }
}
