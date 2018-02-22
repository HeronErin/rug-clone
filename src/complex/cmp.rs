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

use {Complex, Float};
#[cfg(feature = "integer")]
use Integer;
#[cfg(feature = "rational")]
use Rational;
use std::i32;

impl PartialEq for Complex {
    #[inline]
    fn eq(&self, other: &Complex) -> bool {
        self.real().eq(other.real()) && self.imag().eq(other.imag())
    }
}

macro_rules! eq_re_im {
    ($Re: ty; $($Im: ty)*) => { $(
        impl PartialEq<($Re, $Im)> for Complex {
            #[inline]
            fn eq(&self, other: &($Re, $Im)) -> bool {
                self.real().eq(&other.0) && self.imag().eq(&other.1)
            }
        }

        impl PartialEq<Complex> for ($Re, $Im) {
            #[inline]
            fn eq(&self, other: &Complex) -> bool {
                other.real().eq(&self.0) && other.imag().eq(&self.1)
            }
        }
    )* };
}

macro_rules! eq_re {
    ($($Re: ty)*) => { $(
        impl PartialEq<$Re> for Complex {
            #[inline]
            fn eq(&self, other: &$Re) -> bool {
                self.imag().is_zero() && self.real().eq(other)
            }
        }

        impl PartialEq<Complex> for $Re {
            #[inline]
            fn eq(&self, other: &Complex) -> bool {
                other.imag().is_zero() && other.real().eq(self)
            }
        }

        #[cfg(feature = "integer")]
        eq_re_im! { $Re; Integer }
        #[cfg(feature = "rational")]
        eq_re_im! { $Re; Rational }
        eq_re_im! { $Re; Float }
        eq_re_im! { $Re; i8 i16 i32 i64 isize u8 u16 u32 u64 usize f32 f64 }
    )* };
}

#[cfg(feature = "integer")]
eq_re! { Integer }
#[cfg(feature = "rational")]
eq_re! { Rational }
eq_re! { Float }
eq_re! { i8 i16 i32 i64 isize u8 u16 u32 u64 usize f32 f64 }
