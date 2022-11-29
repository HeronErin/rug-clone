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

use crate::Complex;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use gmp_mpfr_sys::mpc::mpc_t;

/// Used to get a reference to a [`Complex`] number.
///
/// The struct implements <code>[Deref]\<[Target][Deref::Target] = [Complex]></code>.
///
/// No memory is unallocated when this struct is dropped.
///
/// # Examples
///
/// ```rust
/// use rug::complex::BorrowComplex;
/// use rug::Complex;
/// let c = Complex::with_val(53, (4.2, -2.3));
/// let neg: BorrowComplex = c.as_neg();
/// // c is still valid
/// assert_eq!(c, (4.2, -2.3));
/// assert_eq!(*neg, (-4.2, 2.3));
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct BorrowComplex<'a> {
    inner: ManuallyDrop<Complex>,
    phantom: PhantomData<&'a Complex>,
}

impl BorrowComplex<'_> {
    /// Create a borrow from a raw [MPC complex number][mpc_t].
    ///
    /// # Safety
    ///
    ///   * The value must be initialized.
    ///   * The [`mpc_t`] type can be considered as a kind of pointer, so there
    ///     can be multiple copies of it. [`BorrowComplex`] cannot mutate the
    ///     value, so there can be other copies, but none of them are allowed to
    ///     mutate the value.
    ///   * The lifetime is obtained from the return type. The user must ensure
    ///     the value remains valid for the duration of the lifetime.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::complex::BorrowComplex;
    /// use rug::Complex;
    /// let c = Complex::with_val(53, (4.2, -2.3));
    /// // Safety: c.as_raw() is a valid pointer.
    /// let raw = unsafe { *c.as_raw() };
    /// // Safety: c is still valid when borrow is used.
    /// let borrow = unsafe { BorrowComplex::from_raw(raw) };
    /// assert_eq!(c, *borrow);
    /// ```
    // unsafe because the lifetime is obtained from return type
    pub unsafe fn from_raw<'a>(raw: mpc_t) -> BorrowComplex<'a> {
        BorrowComplex {
            inner: ManuallyDrop::new(unsafe { Complex::from_raw(raw) }),
            phantom: PhantomData,
        }
    }
}

impl Deref for BorrowComplex<'_> {
    type Target = Complex;
    #[inline]
    fn deref(&self) -> &Complex {
        &self.inner
    }
}
