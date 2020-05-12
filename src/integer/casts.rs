// Copyright © 2016–2020 University of Malta

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
// this program. If not, see <https://www.gnu.org/licenses/>.

use crate::{ext::xmpz, Integer};
use az::{Cast, CheckedCast, OverflowingCast, SaturatingCast, WrappingCast};
use core::cmp::Ordering;

macro_rules! cast_int {
    ($Prim:ty, $fits:path, $get_abs:path) => {
        impl Cast<Integer> for $Prim {
            #[inline]
            fn cast(self) -> Integer {
                Integer::from(self)
            }
        }

        impl Cast<$Prim> for Integer {
            #[inline]
            fn cast(self) -> $Prim {
                (&self).cast()
            }
        }
        impl Cast<$Prim> for &'_ Integer {
            #[inline]
            fn cast(self) -> $Prim {
                let (wrapped, overflow) = self.overflowing_cast();
                debug_assert!(!overflow, "overflow");
                wrapped
            }
        }
        impl CheckedCast<$Prim> for Integer {
            #[inline]
            fn checked_cast(self) -> Option<$Prim> {
                (&self).checked_cast()
            }
        }
        impl CheckedCast<$Prim> for &'_ Integer {
            #[inline]
            fn checked_cast(self) -> Option<$Prim> {
                if $fits(self) {
                    Some(self.wrapping_cast())
                } else {
                    None
                }
            }
        }
        impl SaturatingCast<$Prim> for Integer {
            #[inline]
            fn saturating_cast(self) -> $Prim {
                (&self).saturating_cast()
            }
        }
        impl SaturatingCast<$Prim> for &'_ Integer {
            #[inline]
            fn saturating_cast(self) -> $Prim {
                if $fits(self) {
                    self.wrapping_cast()
                } else if self.cmp0() == Ordering::Less {
                    <$Prim>::min_value()
                } else {
                    <$Prim>::max_value()
                }
            }
        }
        impl WrappingCast<$Prim> for Integer {
            #[inline]
            fn wrapping_cast(self) -> $Prim {
                (&self).wrapping_cast()
            }
        }
        impl WrappingCast<$Prim> for &'_ Integer {
            #[inline]
            fn wrapping_cast(self) -> $Prim {
                let val = $get_abs(self);
                if self.cmp0() == Ordering::Less {
                    val.wrapping_neg()
                } else {
                    val
                }
                .wrapping_cast()
            }
        }
        impl OverflowingCast<$Prim> for Integer {
            #[inline]
            fn overflowing_cast(self) -> ($Prim, bool) {
                (&self).overflowing_cast()
            }
        }
        impl OverflowingCast<$Prim> for &'_ Integer {
            #[inline]
            fn overflowing_cast(self) -> ($Prim, bool) {
                (self.wrapping_cast(), !$fits(self))
            }
        }
    };
}

impl Cast<Integer> for bool {
    #[inline]
    fn cast(self) -> Integer {
        if self {
            Integer::from(1u32)
        } else {
            Integer::new()
        }
    }
}

cast_int! { i8, xmpz::fits_i8, xmpz::get_abs_u8 }
cast_int! { i16, xmpz::fits_i16, xmpz::get_abs_u16 }
cast_int! { i32, xmpz::fits_i32, xmpz::get_abs_u32 }
cast_int! { i64, xmpz::fits_i64, xmpz::get_abs_u64 }
cast_int! { i128, xmpz::fits_i128, xmpz::get_abs_u128 }
#[cfg(target_pointer_width = "32")]
cast_int! { isize, xmpz::fits_i32, xmpz::get_abs_u32 }
#[cfg(target_pointer_width = "64")]
cast_int! { isize, xmpz::fits_i64, xmpz::get_abs_u64 }
cast_int! { u8, xmpz::fits_u8, xmpz::get_abs_u8 }
cast_int! { u16, xmpz::fits_u16, xmpz::get_abs_u16 }
cast_int! { u32, xmpz::fits_u32, xmpz::get_abs_u32 }
cast_int! { u64, xmpz::fits_u64, xmpz::get_abs_u64 }
cast_int! { u128, xmpz::fits_u128, xmpz::get_abs_u128 }
#[cfg(target_pointer_width = "32")]
cast_int! { usize, xmpz::fits_u32, xmpz::get_abs_u32 }
#[cfg(target_pointer_width = "64")]
cast_int! { usize, xmpz::fits_u64, xmpz::get_abs_u64 }

#[cfg(test)]
mod tests {
    use crate::Integer;
    use az::{
        Az, Cast, CheckedAs, CheckedCast, OverflowingAs, OverflowingCast, SaturatingAs,
        SaturatingCast, WrappingAs, WrappingCast,
    };
    use core::{borrow::Borrow, fmt::Debug};

    #[test]
    fn check_bool() {
        let zero = Integer::new();
        let one = Integer::from(1);
        assert_eq!(false.az::<Integer>(), zero);
        assert_eq!(true.az::<Integer>(), one);
    }

    fn check_there_and_back<T>(min: T, max: T)
    where
        T: Copy + Debug + Eq + Cast<Integer>,
        for<'a> &'a Integer:
            Cast<T> + CheckedCast<T> + SaturatingCast<T> + WrappingCast<T> + OverflowingCast<T>,
    {
        let min_int: Integer = min.az::<Integer>();
        let max_int: Integer = max.az::<Integer>();
        assert_eq!(min_int.borrow().az::<T>(), min);
        assert_eq!(max_int.borrow().az::<T>(), max);
        assert_eq!(min_int.borrow().checked_as::<T>(), Some(min));
        assert_eq!(max_int.borrow().checked_as::<T>(), Some(max));
        assert_eq!(min_int.borrow().saturating_as::<T>(), min);
        assert_eq!(max_int.borrow().saturating_as::<T>(), max);
        assert_eq!(min_int.borrow().wrapping_as::<T>(), min);
        assert_eq!(max_int.borrow().wrapping_as::<T>(), max);
        assert_eq!(min_int.borrow().overflowing_as::<T>(), (min, false));
        assert_eq!(max_int.borrow().overflowing_as::<T>(), (max, false));

        let too_small: Integer = min_int - 1;
        let too_large: Integer = max_int + 1;
        assert_eq!(too_small.borrow().checked_as::<T>(), None);
        assert_eq!(too_large.borrow().checked_as::<T>(), None);
        assert_eq!(too_small.borrow().saturating_as::<T>(), min);
        assert_eq!(too_large.borrow().saturating_as::<T>(), max);
        assert_eq!(too_small.borrow().wrapping_as::<T>(), max);
        assert_eq!(too_large.borrow().wrapping_as::<T>(), min);
        assert_eq!(too_small.borrow().overflowing_as::<T>(), (max, true));
        assert_eq!(too_large.borrow().overflowing_as::<T>(), (min, true));
    }

    #[test]
    fn check_integers() {
        check_there_and_back(i8::min_value(), i8::max_value());
        check_there_and_back(i16::min_value(), i16::max_value());
        check_there_and_back(i32::min_value(), i32::max_value());
        check_there_and_back(i64::min_value(), i64::max_value());
        check_there_and_back(i128::min_value(), i128::max_value());
        check_there_and_back(isize::min_value(), isize::max_value());
        check_there_and_back(u8::min_value(), u8::max_value());
        check_there_and_back(u16::min_value(), u16::max_value());
        check_there_and_back(u32::min_value(), u32::max_value());
        check_there_and_back(u64::min_value(), u64::max_value());
        check_there_and_back(u128::min_value(), u128::max_value());
        check_there_and_back(usize::min_value(), usize::max_value());
    }
}
