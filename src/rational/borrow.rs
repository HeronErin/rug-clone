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

use crate::Rational;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use gmp_mpfr_sys::gmp::mpq_t;

/// Used to get a reference to a [`Rational`] number.
///
/// The struct implements <code>[Deref]\<[Target][Deref::Target] = [Rational]></code>.
///
/// No memory is unallocated when this struct is dropped.
///
/// # Examples
///
/// ```rust
/// use rug::rational::BorrowRational;
/// use rug::Rational;
/// let r = Rational::from((42, 3));
/// let neg: BorrowRational = r.as_neg();
/// // r is still valid
/// assert_eq!(r, (42, 3));
/// assert_eq!(*neg, (-42, 3));
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct BorrowRational<'a> {
    inner: ManuallyDrop<Rational>,
    phantom: PhantomData<&'a Rational>,
}

impl BorrowRational<'_> {
    /// Create a borrow from a raw [GMP rational number][mpq_t].
    ///
    /// # Safety
    ///
    ///   * The value must be initialized.
    ///   * The [`mpq_t`] type can be considered as a kind of pointer, so there
    ///     can be multiple copies of it. [`BorrowRational`] cannot mutate the
    ///     value, so there can be other copies, but none of them are allowed to
    ///     mutate the value.
    ///   * The lifetime is obtained from the return type. The user must ensure
    ///     the value remains valid for the duration of the lifetime.
    ///   * The numerator and denominator must be in canonical form, as the rest
    ///     of the library assumes that they are. Most GMP functions leave the
    ///     rational number in canonical form, but assignment functions do not.
    ///     Check the [GMP documentation][gmp mpq] for details.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::rational::BorrowRational;
    /// use rug::Rational;
    /// let r = Rational::from((42, 3));
    /// // Safety: r.as_raw() is a valid pointer.
    /// let raw = unsafe { *r.as_raw() };
    /// // Safety: r is still valid when borrow is used.
    /// let borrow = unsafe { BorrowRational::from_raw(raw) };
    /// assert_eq!(r, *borrow);
    /// ```
    ///
    /// [gmp mpq]: gmp_mpfr_sys::C::GMP::Rational_Number_Functions#index-Rational-number-functions
    pub const unsafe fn from_raw<'a>(raw: mpq_t) -> BorrowRational<'a> {
        BorrowRational {
            inner: ManuallyDrop::new(Rational { inner: raw }),
            phantom: PhantomData,
        }
    }
}

impl Deref for BorrowRational<'_> {
    type Target = Rational;
    #[inline]
    fn deref(&self) -> &Rational {
        &self.inner
    }
}
