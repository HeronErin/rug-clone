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

use crate::Integer;
use core::borrow::Borrow;
use core::convert::AsRef;
use core::fmt::{
    Binary, Debug, Display, Formatter, LowerHex, Octal, Pointer, Result as FmtResult, UpperHex,
};
#[cfg(feature = "float")]
use core::fmt::{LowerExp, UpperExp};
use core::marker::PhantomData;
use core::ops::Deref;
use gmp_mpfr_sys::gmp::mpz_t;

/// Used to get a reference to an [`Integer`].
///
/// The struct implements <code>[Deref]\<[Target][Deref::Target] = [Integer]></code>.
///
/// No memory is unallocated when this struct is dropped.
///
/// # Examples
///
/// ```rust
/// use rug::integer::BorrowInteger;
/// use rug::Integer;
/// let i = Integer::from(42);
/// let neg: BorrowInteger = i.as_neg();
/// // i is still valid
/// assert_eq!(i, 42);
/// assert_eq!(*neg, -42);
/// ```
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct BorrowInteger<'a> {
    inner: mpz_t,
    phantom: PhantomData<&'a Integer>,
}

impl<'a> BorrowInteger<'a> {
    /// Create a borrow from a raw [GMP integer][mpz_t].
    ///
    /// # Safety
    ///
    ///   * The value must be initialized.
    ///   * The [`mpz_t`] type can be considered as a kind of pointer, so there
    ///     can be multiple copies of it. [`BorrowInteger`] cannot mutate the
    ///     value, so there can be other copies, but none of them are allowed to
    ///     mutate the value.
    ///   * The lifetime is obtained from the return type. The user must ensure
    ///     the value remains valid for the duration of the lifetime.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::integer::BorrowInteger;
    /// use rug::Integer;
    /// let i = Integer::from(42);
    /// // Safety: i.as_raw() is a valid pointer.
    /// let raw = unsafe { *i.as_raw() };
    /// // Safety: i is still valid when borrow is used.
    /// let borrow = unsafe { BorrowInteger::from_raw(raw) };
    /// assert_eq!(i, *borrow);
    /// ```
    #[inline]
    pub const unsafe fn from_raw(raw: mpz_t) -> BorrowInteger<'a> {
        BorrowInteger {
            inner: raw,
            phantom: PhantomData,
        }
    }
}

impl Deref for BorrowInteger<'_> {
    type Target = Integer;
    #[inline]
    fn deref(&self) -> &Integer {
        let ptr = cast_ptr!(&self.inner, Integer);
        // Safety: the inner pointer is valid for the duration of the lifetime.
        unsafe { &*ptr }
    }
}

impl Borrow<Integer> for BorrowInteger<'_> {
    #[inline]
    fn borrow(&self) -> &Integer {
        self
    }
}

impl AsRef<Integer> for BorrowInteger<'_> {
    #[inline]
    fn as_ref(&self) -> &Integer {
        self
    }
}

impl Pointer for BorrowInteger<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Pointer::fmt(&&**self, f)
    }
}

impl Display for BorrowInteger<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Display::fmt(&**self, f)
    }
}

impl Debug for BorrowInteger<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Debug::fmt(&**self, f)
    }
}

impl Binary for BorrowInteger<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Binary::fmt(&**self, f)
    }
}

impl Octal for BorrowInteger<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Octal::fmt(&**self, f)
    }
}

impl LowerHex for BorrowInteger<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        LowerHex::fmt(&**self, f)
    }
}

impl UpperHex for BorrowInteger<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        UpperHex::fmt(&**self, f)
    }
}

#[cfg(feature = "float")]
impl LowerExp for BorrowInteger<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        LowerExp::fmt(&**self, f)
    }
}

#[cfg(feature = "float")]
impl UpperExp for BorrowInteger<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        UpperExp::fmt(&**self, f)
    }
}

// Safety: mpz_t is thread safe as guaranteed by the GMP library.
unsafe impl Send for BorrowInteger<'_> {}
unsafe impl Sync for BorrowInteger<'_> {}
