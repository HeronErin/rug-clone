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

use crate::float::OrdFloat;
use crate::Float;
use core::borrow::Borrow;
use core::convert::AsRef;
use core::fmt::{
    Binary, Debug, Display, Formatter, LowerExp, LowerHex, Octal, Pointer, Result as FmtResult,
    UpperExp, UpperHex,
};
use core::marker::PhantomData;
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
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct BorrowFloat<'a> {
    inner: mpfr_t,
    phantom: PhantomData<&'a Float>,
}

impl<'a> BorrowFloat<'a> {
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
    pub const unsafe fn from_raw(raw: mpfr_t) -> BorrowFloat<'a> {
        BorrowFloat {
            inner: raw,
            phantom: PhantomData,
        }
    }
}

impl Deref for BorrowFloat<'_> {
    type Target = Float;
    #[inline]
    fn deref(&self) -> &Float {
        let ptr = cast_ptr!(&self.inner, Float);
        // Safety: the inner pointer is valid for the duration of the lifetime.
        unsafe { &*ptr }
    }
}

impl Borrow<Float> for BorrowFloat<'_> {
    #[inline]
    fn borrow(&self) -> &Float {
        self
    }
}

impl AsRef<Float> for BorrowFloat<'_> {
    #[inline]
    fn as_ref(&self) -> &Float {
        self
    }
}

impl AsRef<OrdFloat> for BorrowFloat<'_> {
    #[inline]
    fn as_ref(&self) -> &OrdFloat {
        self.as_ord()
    }
}

impl Pointer for BorrowFloat<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Pointer::fmt(&&**self, f)
    }
}

impl Display for BorrowFloat<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Display::fmt(&**self, f)
    }
}

impl Debug for BorrowFloat<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Debug::fmt(&**self, f)
    }
}

impl Binary for BorrowFloat<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Binary::fmt(&**self, f)
    }
}

impl Octal for BorrowFloat<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        Octal::fmt(&**self, f)
    }
}

impl LowerHex for BorrowFloat<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        LowerHex::fmt(&**self, f)
    }
}

impl UpperHex for BorrowFloat<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        UpperHex::fmt(&**self, f)
    }
}

impl LowerExp for BorrowFloat<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        LowerExp::fmt(&**self, f)
    }
}

impl UpperExp for BorrowFloat<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        UpperExp::fmt(&**self, f)
    }
}

// Safety: mpfr_t is thread safe as guaranteed by the MPFR library.
unsafe impl Send for BorrowFloat<'_> {}
unsafe impl Sync for BorrowFloat<'_> {}
