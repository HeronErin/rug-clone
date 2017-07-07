// Copyright © 2017 University of Malta

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

use Complex;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

/// A complex number that supports ordering and hashing.
///
/// For ordering, the real part has precedence over the imaginary
/// part. Negative zero is ordered as less than positive zero. All
/// NaNs are ordered as equal and as greater than infinity, with the
/// NaN sign ignored.
///
/// # Examples
///
/// ```rust
/// use rug::Complex;
/// use rug::complex::OrdComplex;
/// use rug::float::Special;
/// use std::cmp::Ordering;
///
/// let nan_c = Complex::with_val(53, (Special::Nan, Special::Nan));
/// let nan = OrdComplex::from(nan_c);
/// assert_eq!(nan.cmp(&nan), Ordering::Equal);
///
/// let one_neg0_c = Complex::with_val(53, (1, Special::NegZero));
/// let one_neg0 = OrdComplex::from(one_neg0_c);
/// let one_pos0_c = Complex::with_val(53, (1, Special::Zero));
/// let one_pos0 = OrdComplex::from(one_pos0_c);
/// assert_eq!(one_neg0.cmp(&one_pos0), Ordering::Less);
///
/// let zero_inf_s = (Special::Zero, Special::Infinity);
/// let zero_inf_c = Complex::with_val(53, zero_inf_s);
/// let zero_inf = OrdComplex::from(zero_inf_c);
/// assert_eq!(one_pos0.cmp(&zero_inf), Ordering::Greater);
/// ```
#[derive(Clone, Debug, Default)]
pub struct OrdComplex {
    inner: Complex,
}

impl OrdComplex {
    /// Extracts the underlying [`Complex`](../struct.Complex.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Complex;
    /// use rug::complex::OrdComplex;
    /// let c = Complex::with_val(53, (1.5, 2.5));
    /// let ord = OrdComplex::from(c);
    /// let c_ref = ord.as_complex();
    /// let (re, im) = c_ref.as_real_imag();
    /// assert_eq!(*re, 1.5);
    /// assert_eq!(*im, 2.5);
    pub fn as_complex(&self) -> &Complex {
        &self.inner
    }
}

impl Hash for OrdComplex {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let (re, im) = self.inner.as_real_imag();
        let (re, im) = (re.as_ord(), im.as_ord());
        re.hash(state);
        im.hash(state);
    }
}

impl PartialEq for OrdComplex {
    #[inline]
    fn eq(&self, other: &OrdComplex) -> bool {
        let (re, im) = self.inner.as_real_imag();
        let (re, im) = (re.as_ord(), im.as_ord());
        let (other_re, other_im) = other.inner.as_real_imag();
        let (other_re, other_im) = (other_re.as_ord(), other_im.as_ord());
        re.eq(other_re) && im.eq(other_im)
    }
}

impl Eq for OrdComplex {}

impl PartialOrd for OrdComplex {
    #[inline]
    fn partial_cmp(&self, other: &OrdComplex) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OrdComplex {
    #[inline]
    fn cmp(&self, other: &OrdComplex) -> Ordering {
        let (re, im) = self.inner.as_real_imag();
        let (re, im) = (re.as_ord(), im.as_ord());
        let (other_re, other_im) = other.inner.as_real_imag();
        let (other_re, other_im) = (other_re.as_ord(), other_im.as_ord());
        match re.cmp(other_re) {
            Ordering::Equal => im.cmp(other_im),
            not_equal => not_equal,
        }
    }
}

impl From<Complex> for OrdComplex {
    fn from(c: Complex) -> OrdComplex {
        OrdComplex { inner: c }
    }
}
