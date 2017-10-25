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

impl<T, U> PartialEq<(T, U)> for Complex
where
    Float: PartialEq<T>,
    Float: PartialEq<U>,
{
    #[inline]
    fn eq(&self, other: &(T, U)) -> bool {
        self.real().eq(&other.0) && self.imag().eq(&other.1)
    }
}

macro_rules! eq_tuple {
    { $T:ty, $U:ty } => {
        impl PartialEq<Complex> for ($T, $U) {
            #[inline]
            fn eq(&self, other: &Complex) -> bool {
                self.0.eq(other.real()) && self.1.eq(other.imag())
            }
        }
    }
}

macro_rules! eq {
    { $T:ty } => {
        #[cfg(feature = "integer")]
        eq_tuple! { $T, Integer }
        #[cfg(feature = "rational")]
        eq_tuple! { $T, Rational }
        eq_tuple! { $T, Float }
        eq_tuple! { $T, u32 }
        eq_tuple! { $T, i32 }
        eq_tuple! { $T, f64 }
        eq_tuple! { $T, f32 }

        impl PartialEq<$T> for Complex {
            #[inline]
            fn eq(&self, other: &$T) -> bool {
                self.real().eq(other) && self.imag().is_zero()
            }
        }

        impl PartialEq<Complex> for $T {
            #[inline]
            fn eq(&self, other: &Complex) -> bool {
                self.eq(other.real()) && other.imag().is_zero()
            }
        }
    }
}

#[cfg(feature = "integer")]
eq! { Integer }
#[cfg(feature = "rational")]
eq! { Rational }
eq! { Float }
eq! { u32 }
eq! { i32 }
eq! { f64 }
eq! { f32 }
