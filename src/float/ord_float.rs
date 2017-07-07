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

use Float;
use gmp_mpfr_sys::gmp;
use inner::Inner;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::slice;

/// A float that supports ordering and hashing.
///
/// Negative zero is ordered as less than positive zero. All NaNs are
/// ordered as equal and as greater than infinity, with the NaN sign
/// ignored.
///
/// # Examples
///
/// ```rust
/// use rug::Float;
/// use rug::float::{OrdFloat, Special};
/// use std::cmp::Ordering;
///
/// let nan_f = Float::with_val(53, Special::Nan);
/// let nan = OrdFloat::from(nan_f);
/// assert_eq!(nan.cmp(&nan), Ordering::Equal);
///
/// let inf_f = Float::with_val(53, Special::Infinity);
/// let inf = OrdFloat::from(inf_f);
/// assert_eq!(nan.cmp(&inf), Ordering::Greater);
///
/// let zero_f = Float::with_val(53, Special::Zero);
/// let zero = OrdFloat::from(zero_f);
/// let neg_zero_f = Float::with_val(53, Special::NegZero);
/// let neg_zero = OrdFloat::from(neg_zero_f);
/// assert_eq!(zero.cmp(&neg_zero), Ordering::Greater);
/// ```
#[derive(Clone, Debug, Default)]
pub struct OrdFloat {
    inner: Float,
}

impl OrdFloat {
    /// Extracts the underlying [`Float`](../struct.Float.html).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rug::Float;
    /// use rug::float::OrdFloat;
    /// let f = Float::with_val(53, 1.5);
    /// let ord = OrdFloat::from(f);
    /// let f_ref = ord.as_float();
    /// assert_eq!(f_ref.to_f64(), 1.5);
    pub fn as_float(&self) -> &Float {
        &self.inner
    }
}

impl Hash for OrdFloat {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let s = &self.inner;
        s.get_exp().hash(state);
        if s.is_nan() {
            return;
        }
        s.is_sign_negative().hash(state);
        if s.is_infinite() {
            return;
        }
        let prec = s.prec();
        assert_eq!(prec as usize as u32, prec);
        let prec = prec as usize;
        let mut limbs = prec / gmp::LIMB_BITS as usize;
        // MPFR keeps unused bits set to zero, so use whole of last limb
        if prec % gmp::LIMB_BITS as usize > 0 {
            limbs += 1;
        };
        let slice = unsafe { slice::from_raw_parts(s.inner().d, limbs) };
        slice.hash(state);
    }
}

impl PartialEq for OrdFloat {
    #[inline]
    fn eq(&self, other: &OrdFloat) -> bool {
        let s = &self.inner;
        let o = &other.inner;
        if s.is_nan() {
            o.is_nan()
        } else if s.is_zero() {
            o.is_zero() && s.is_sign_negative() == o.is_sign_negative()
        } else {
            s.eq(o)
        }
    }
}

impl Eq for OrdFloat {}

impl PartialOrd for OrdFloat {
    #[inline]
    fn partial_cmp(&self, other: &OrdFloat) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for OrdFloat {
    #[inline]
    fn cmp(&self, other: &OrdFloat) -> Ordering {
        let s = &self.inner;
        let o = &other.inner;
        if s.is_nan() {
            if o.is_nan() {
                Ordering::Equal
            } else {
                Ordering::Greater
            }
        } else if s.is_zero() && o.is_zero() {
            match (s.is_sign_negative(), o.is_sign_negative()) {
                (false, true) => Ordering::Greater,
                (true, false) => Ordering::Less,
                _ => Ordering::Equal,
            }
        } else {
            s.partial_cmp(o).unwrap()
        }
    }
}

impl From<Float> for OrdFloat {
    fn from(f: Float) -> OrdFloat {
        OrdFloat { inner: f }
    }
}
