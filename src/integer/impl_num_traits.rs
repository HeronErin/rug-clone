// Copyright © 2016–2021 Trevor Spiteri

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

use crate::{ext::xmpz, integer::ParseIntegerError, ops::Pow, Integer};
use az::{CheckedCast, UnwrappedCast};
use core::cmp::Ordering;
use num_traits::{
    cast::{FromPrimitive, ToPrimitive},
    identities::{One, Zero},
    ops::mul_add::{MulAdd, MulAddAssign},
    pow::Pow as NumPow,
    sign::Signed,
    Num,
};

impl Zero for Integer {
    #[inline]
    fn zero() -> Self {
        Integer::new()
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.cmp0() == Ordering::Equal
    }

    #[inline]
    fn set_zero(&mut self) {
        xmpz::set_0(self);
    }
}

impl One for Integer {
    #[inline]
    fn one() -> Self {
        Integer::from(1u8)
    }

    #[inline]
    fn set_one(&mut self) {
        xmpz::set_1(self);
    }

    #[inline]
    fn is_one(&self) -> bool {
        xmpz::is_1(self)
    }
}

impl Num for Integer {
    type FromStrRadixErr = ParseIntegerError;

    #[inline]
    fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntegerError> {
        Integer::from_str_radix(src, radix.unwrapped_cast())
    }
}

impl Signed for Integer {
    #[inline]
    fn abs(&self) -> Self {
        self.abs_ref().into()
    }

    #[inline]
    fn abs_sub(&self, other: &Self) -> Self {
        if *self <= *other {
            Integer::new()
        } else {
            (self - other).into()
        }
    }

    #[inline]
    fn signum(&self) -> Self {
        self.signum_ref().into()
    }

    #[inline]
    fn is_positive(&self) -> bool {
        self.cmp0() == Ordering::Greater
    }

    #[inline]
    fn is_negative(&self) -> bool {
        self.cmp0() == Ordering::Less
    }
}

impl<Rhs> NumPow<Rhs> for Integer
where
    Integer: Pow<Rhs, Output = Integer>,
{
    type Output = Integer;

    #[inline]
    fn pow(self, rhs: Rhs) -> Self::Output {
        Pow::pow(self, rhs)
    }
}

impl MulAdd for Integer {
    type Output = Integer;

    #[inline]
    fn mul_add(self, a: Integer, b: Integer) -> Integer {
        &self * &a + b
    }
}

impl MulAddAssign for Integer {
    #[inline]
    fn mul_add_assign(&mut self, a: Integer, b: Integer) {
        *self = &*self * &a + b
    }
}

impl MulAdd<&Integer, &Integer> for Integer {
    type Output = Integer;

    #[inline]
    fn mul_add(self, a: &Integer, b: &Integer) -> Integer {
        self * a + b
    }
}

impl MulAddAssign<&Integer, &Integer> for Integer {
    #[inline]
    fn mul_add_assign(&mut self, a: &Integer, b: &Integer) {
        *self *= a;
        *self += b;
    }
}

impl ToPrimitive for Integer {
    #[inline]
    fn to_i64(&self) -> Option<i64> {
        self.checked_cast()
    }
    #[inline]
    fn to_u64(&self) -> Option<u64> {
        self.checked_cast()
    }
    #[inline]
    fn to_isize(&self) -> Option<isize> {
        self.checked_cast()
    }
    #[inline]
    fn to_i8(&self) -> Option<i8> {
        self.checked_cast()
    }
    #[inline]
    fn to_i16(&self) -> Option<i16> {
        self.checked_cast()
    }
    #[inline]
    fn to_i32(&self) -> Option<i32> {
        self.checked_cast()
    }
    #[inline]
    fn to_i128(&self) -> Option<i128> {
        self.checked_cast()
    }
    #[inline]
    fn to_usize(&self) -> Option<usize> {
        self.checked_cast()
    }
    #[inline]
    fn to_u8(&self) -> Option<u8> {
        self.checked_cast()
    }
    #[inline]
    fn to_u16(&self) -> Option<u16> {
        self.checked_cast()
    }
    #[inline]
    fn to_u32(&self) -> Option<u32> {
        self.checked_cast()
    }
    #[inline]
    fn to_u128(&self) -> Option<u128> {
        self.checked_cast()
    }
    #[inline]
    fn to_f32(&self) -> Option<f32> {
        Some(self.to_f32())
    }
    #[inline]
    fn to_f64(&self) -> Option<f64> {
        Some(self.to_f64())
    }
}

impl FromPrimitive for Integer {
    #[inline]
    fn from_i64(n: i64) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_u64(n: u64) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_isize(n: isize) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_i8(n: i8) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_i16(n: i16) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_i32(n: i32) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_i128(n: i128) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_usize(n: usize) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_u8(n: u8) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_u16(n: u16) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_u32(n: u32) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_u128(n: u128) -> Option<Self> {
        Some(n.into())
    }
    #[inline]
    fn from_f32(n: f32) -> Option<Self> {
        Self::from_f32(n)
    }
    #[inline]
    fn from_f64(n: f64) -> Option<Self> {
        Self::from_f64(n)
    }
}
