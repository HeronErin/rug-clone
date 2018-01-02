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

use std::mem;

/// Casts into the destination if the value fits, otherwise panics.
///
/// Floats are rounded towards zero when cast into integers.
///
/// # Panics
///
/// * If a NaN is cast into an integer type.
/// * If the value does not fit in the destination integer type.
pub trait Cast<Dst> {
    fn cast(self) -> Dst;
}

/// Casts into the destination if the value fits.
///
/// Floats are rounded towards zero when cast into integers.
pub trait CheckedCast<Dst> {
    fn checked_cast(self) -> Option<Dst>;
}

/// Casts into the destination, wrapping integers around if the value
/// does not fit.
///
/// Floats are rounded towards zero when cast into integers.
pub trait WrappingCast<Dst> {
    fn wrapping_cast(self) -> Dst;
}

#[inline]
#[allow(unused)]
pub fn cast<Src, Dst>(src: Src) -> Dst
where
    Src: Cast<Dst>,
{
    src.cast()
}

#[inline]
#[allow(unused)]
pub fn checked_cast<Src, Dst>(src: Src) -> Option<Dst>
where
    Src: CheckedCast<Dst>,
{
    src.checked_cast()
}

#[inline]
#[allow(unused)]
pub fn wrapping_cast<Src, Dst>(src: Src) -> Dst
where
    Src: WrappingCast<Dst>,
{
    src.wrapping_cast()
}

macro_rules! cast_int_to_int {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl Cast<$Dst> for $Src {
            #[inline]
            fn cast(self) -> $Dst {
                <$Src as CheckedCast<$Dst>>::checked_cast(self)
                    .expect("overflow")
            }
        }
    )* }
}

macro_rules! cast_float_to_int {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl Cast<$Dst> for $Src {
            #[inline]
            fn cast(self) -> $Dst {
                assert!(!self.is_nan(), "NaN");
                <$Src as CheckedCast<$Dst>>::checked_cast(self)
                    .expect("overflow")
            }
        }
    )* }
}

macro_rules! cast_as {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl Cast<$Dst> for $Src {
            #[allow(unknown_lints, cast_lossless)]
            #[inline]
            fn cast(self) -> $Dst {
                self as $Dst
            }
        }
    )* }
}

macro_rules! cast_int {
    { $($Src:ty)* } => { $(
        cast_int_to_int! { $Src => i8 i16 i32 i64 isize }
        cast_int_to_int! { $Src => u8 u16 u32 u64 usize }
        cast_as! { $Src => f32 f64 }
    )* }
}

macro_rules! cast_float {
    { $($Src:ty)* } => { $(
        cast_float_to_int! { $Src => i8 i16 i32 i64 isize }
        cast_float_to_int! { $Src => u8 u16 u32 u64 usize }
        cast_as! { $Src => f32 f64 }
    )* }
}

cast_int! { i8 i16 i32 i64 isize }
cast_int! { u8 u16 u32 u64 usize }
cast_float! { f32 f64 }

macro_rules! checked_same_signedness {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl CheckedCast<$Dst> for $Src {
            #[allow(unknown_lints, cast_lossless)]
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                let dst = self as $Dst;
                if self == dst as $Src {
                    Some(dst)
                } else {
                    None
                }
            }
        }
    )* }
}

macro_rules! checked_signed_to_unsigned {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl CheckedCast<$Dst> for $Src {
            #[allow(unknown_lints, cast_lossless)]
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                let dst = self as $Dst;
                if self >= 0 && self == dst as $Src {
                    Some(dst)
                } else {
                    None
                }
            }
        }
    )* }
}

macro_rules! checked_unsigned_to_signed {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl CheckedCast<$Dst> for $Src {
            #[allow(unknown_lints, cast_lossless)]
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                let dst = self as $Dst;
                if dst >= 0 && self == dst as $Src {
                    Some(dst)
                } else {
                    None
                }
            }
        }
    )* }
}

macro_rules! checked_float_via {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl CheckedCast<$Dst> for $Src {
            #[allow(unknown_lints, cast_lossless)]
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                let f = Float::from(self);
                if !f.fits {
                    return None;
                }
                if f.neg {
                    let i = f.wrapped as i64;
                    if i < 0 {
                        return None
                    }
                    let i = -i;
                    <i64 as CheckedCast<$Dst>>::checked_cast(i)
                } else {
                    <u64 as CheckedCast<$Dst>>::checked_cast(f.wrapped)
                }
            }
        }
    )* }
}

macro_rules! checked_as {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl CheckedCast<$Dst> for $Src {
            #[allow(unknown_lints, cast_lossless)]
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                Some(self as $Dst)
            }
        }
    )* }
}

macro_rules! checked_signed {
    { $($Src:ty)* } => { $(
        checked_same_signedness! { $Src => i8 i16 i32 i64 isize }
        checked_signed_to_unsigned! { $Src => u8 u16 u32 u64 usize }
        checked_as! { $Src => f32 f64 }
    )* }
}

macro_rules! checked_unsigned {
    { $($Src:ty)* } => { $(
        checked_unsigned_to_signed! { $Src => i8 i16 i32 i64 isize }
        checked_same_signedness! { $Src => u8 u16 u32 u64 usize }
        checked_as! { $Src => f32 f64 }
    )* }
}

macro_rules! checked_float {
    { $($Src:ty)* } => { $(
        checked_float_via! { $Src => i8 i16 i32 i64 isize }
        checked_float_via! { $Src => u8 u16 u32 u64 usize }
        checked_as! { $Src => f32 f64 }
    )* }
}

checked_signed! { i8 i16 i32 i64 isize }
checked_unsigned! { u8 u16 u32 u64 usize }
checked_float! { f32 f64 }

macro_rules! wrapping_as {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl WrappingCast<$Dst> for $Src {
            #[allow(unknown_lints, cast_lossless)]
            #[inline]
            fn wrapping_cast(self) -> $Dst {
                self as $Dst
            }
        }
    )* }
}

macro_rules! wrapping_float_via {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl WrappingCast<$Dst> for $Src {
            #[inline]
            fn wrapping_cast(self) -> $Dst {
                let f = Float::from(self);
                let u = f.wrapped;
                let n = if f.neg { u.wrapping_neg() } else { u };
                n as $Dst
            }
        }
    )* }
}

macro_rules! wrapping_int {
    { $($Src:ty)* } => { $(
        wrapping_as! { $Src => i8 i16 i32 i64 isize }
        wrapping_as! { $Src => u8 u16 u32 u64 usize }
        wrapping_as! { $Src => f32 f64 }
    )* }
}

macro_rules! wrapping_float {
    { $($Src:ty)* } => { $(
        wrapping_float_via! { $Src => i8 i16 i32 i64 isize }
        wrapping_float_via! { $Src => u8 u16 u32 u64 usize }
        wrapping_as! { $Src => f32 f64 }
    )* }
}

wrapping_int! { i8 i16 i32 i64 isize u8 u16 u32 u64 usize }
wrapping_float! { f32 f64 }

struct Float {
    neg: bool,
    fits: bool,
    wrapped: u64,
}

impl From<f32> for Float {
    fn from(src: f32) -> Float {
        const EXP_BITS: i32 = 8;
        const MANT_BITS: i32 = 23;
        const SIGN_MASK: u32 = 1 << (EXP_BITS + MANT_BITS);
        const EXP_MASK: u32 = ((1 << EXP_BITS) - 1) << MANT_BITS;
        const MANT_MASK: u32 = (1 << MANT_BITS) - 1;
        const EXP_BIAS: i32 = (1 << (EXP_BITS - 1)) - 1;

        let u: u32 = unsafe { mem::transmute(src) };
        let neg = (u & SIGN_MASK) != 0;
        let biased_exp = u & EXP_MASK;
        let mant = u & MANT_MASK;

        // check for zero
        if biased_exp == 0 && mant == 0 {
            return Float {
                neg,
                fits: true,
                wrapped: 0,
            };
        }
        // check for infinity or nan
        if biased_exp == EXP_MASK {
            return Float {
                neg,
                fits: false,
                wrapped: 0,
            };
        }

        let shift = (biased_exp >> MANT_BITS) as i32 - EXP_BIAS - MANT_BITS;
        // Do not return early if shift == -MANT_BITS, as there is implicit one.
        if shift < -MANT_BITS {
            return Float {
                neg,
                fits: true,
                wrapped: 0,
            };
        }
        if shift >= 64 {
            return Float {
                neg,
                fits: false,
                wrapped: 0,
            };
        }

        // Add implicit one. (Subnormals have already returned early.)
        let significand = u64::from(mant) | (1 << MANT_BITS);
        if shift < 0 {
            return Float {
                neg,
                fits: true,
                wrapped: significand >> -shift,
            };
        }
        let wrapped = significand << shift;
        let fits = (wrapped >> shift) == significand;
        Float { neg, fits, wrapped }
    }
}

impl From<f64> for Float {
    fn from(src: f64) -> Float {
        const EXP_BITS: i32 = 11;
        const MANT_BITS: i32 = 52;
        const SIGN_MASK: u64 = 1 << (EXP_BITS + MANT_BITS);
        const EXP_MASK: u64 = ((1 << EXP_BITS) - 1) << MANT_BITS;
        const MANT_MASK: u64 = (1 << MANT_BITS) - 1;
        const EXP_BIAS: i32 = (1 << (EXP_BITS - 1)) - 1;

        let u: u64 = unsafe { mem::transmute(src) };
        let neg = (u & SIGN_MASK) != 0;
        let biased_exp = u & EXP_MASK;
        let mant = u & MANT_MASK;

        // check for zero
        if biased_exp == 0 && mant == 0 {
            return Float {
                neg,
                fits: true,
                wrapped: 0,
            };
        }
        // check for infinity or nan
        if biased_exp == EXP_MASK {
            return Float {
                neg,
                fits: false,
                wrapped: 0,
            };
        }

        let shift = (biased_exp >> MANT_BITS) as i32 - EXP_BIAS - MANT_BITS;
        // Do not return early if shift == -MANT_BITS, as there is implicit one.
        if shift < -MANT_BITS {
            return Float {
                neg,
                fits: true,
                wrapped: 0,
            };
        }
        if shift >= 64 {
            return Float {
                neg,
                fits: false,
                wrapped: 0,
            };
        }

        // Add implicit one. (Subnormals have already returned early.)
        let significand = mant | (1 << MANT_BITS);
        if shift < 0 {
            return Float {
                neg,
                fits: true,
                wrapped: significand >> -shift,
            };
        }
        let wrapped = significand << shift;
        let fits = (wrapped >> shift) == significand;
        Float { neg, fits, wrapped }
    }
}

#[cfg(test)]
mod tests {
    use super::{checked_cast, wrapping_cast};

    fn f32(sig: f32, exp: i32) -> f32 {
        sig * (exp as f32).exp2()
    }

    fn f64(sig: f64, exp: i32) -> f64 {
        sig * (exp as f64).exp2()
    }

    #[test]
    fn checked_to_smaller_size() {
        assert_eq!(checked_cast::<i16, i8>(-0x0100), None);
        assert_eq!(checked_cast::<i16, i8>(-0x0081), None);
        assert_eq!(checked_cast::<i16, i8>(-0x0080), Some(-0x80));
        assert_eq!(checked_cast::<i16, i8>(-0x0001), Some(-0x01));
        assert_eq!(checked_cast::<i16, i8>(0x0000), Some(0x00));
        assert_eq!(checked_cast::<i16, i8>(0x007f), Some(0x7f));
        assert_eq!(checked_cast::<i16, i8>(0x0080), None);
        assert_eq!(checked_cast::<i16, i8>(0x00ff), None);
        assert_eq!(checked_cast::<i16, i8>(0x0100), None);

        assert_eq!(checked_cast::<i16, u8>(-0x0100), None);
        assert_eq!(checked_cast::<i16, u8>(-0x0081), None);
        assert_eq!(checked_cast::<i16, u8>(-0x0080), None);
        assert_eq!(checked_cast::<i16, u8>(-0x0001), None);
        assert_eq!(checked_cast::<i16, u8>(0x0000), Some(0x00));
        assert_eq!(checked_cast::<i16, u8>(0x007f), Some(0x7f));
        assert_eq!(checked_cast::<i16, u8>(0x0080), Some(0x80));
        assert_eq!(checked_cast::<i16, u8>(0x00ff), Some(0xff));
        assert_eq!(checked_cast::<i16, u8>(0x0100), None);

        assert_eq!(checked_cast::<u16, i8>(0x0000), Some(0x00));
        assert_eq!(checked_cast::<u16, i8>(0x007f), Some(0x7f));
        assert_eq!(checked_cast::<u16, i8>(0x0080), None);
        assert_eq!(checked_cast::<u16, i8>(0x00ff), None);
        assert_eq!(checked_cast::<u16, i8>(0x0100), None);

        assert_eq!(checked_cast::<u16, u8>(0x0000), Some(0x00));
        assert_eq!(checked_cast::<u16, u8>(0x007f), Some(0x7f));
        assert_eq!(checked_cast::<u16, u8>(0x0080), Some(0x80));
        assert_eq!(checked_cast::<u16, u8>(0x00ff), Some(0xff));
        assert_eq!(checked_cast::<u16, u8>(0x0100), None);
    }

    #[test]
    fn checked_to_same_size() {
        assert_eq!(checked_cast::<i8, i8>(-0x80), Some(-0x80));
        assert_eq!(checked_cast::<i8, i8>(-0x01), Some(-0x01));
        assert_eq!(checked_cast::<i8, i8>(0x00), Some(0x00));
        assert_eq!(checked_cast::<i8, i8>(0x7f), Some(0x7f));

        assert_eq!(checked_cast::<i8, u8>(-0x80), None);
        assert_eq!(checked_cast::<i8, u8>(-0x01), None);
        assert_eq!(checked_cast::<i8, u8>(0x00), Some(0x00));
        assert_eq!(checked_cast::<i8, u8>(0x7f), Some(0x7f));

        assert_eq!(checked_cast::<u8, i8>(0x00), Some(0x00));
        assert_eq!(checked_cast::<u8, i8>(0x7f), Some(0x7f));
        assert_eq!(checked_cast::<u8, i8>(0x80), None);
        assert_eq!(checked_cast::<u8, i8>(0xff), None);

        assert_eq!(checked_cast::<u8, u8>(0x00), Some(0x00));
        assert_eq!(checked_cast::<u8, u8>(0x7f), Some(0x7f));
        assert_eq!(checked_cast::<u8, u8>(0x80), Some(0x80));
        assert_eq!(checked_cast::<u8, u8>(0xff), Some(0xff));
    }

    #[test]
    fn checked_to_larger_size() {
        assert_eq!(checked_cast::<i8, i16>(-0x80), Some(-0x0080));
        assert_eq!(checked_cast::<i8, i16>(-0x01), Some(-0x0001));
        assert_eq!(checked_cast::<i8, i16>(0x00), Some(0x0000));
        assert_eq!(checked_cast::<i8, i16>(0x7f), Some(0x007f));

        assert_eq!(checked_cast::<i8, u16>(-0x80), None);
        assert_eq!(checked_cast::<i8, u16>(-0x01), None);
        assert_eq!(checked_cast::<i8, u16>(0x00), Some(0x0000));
        assert_eq!(checked_cast::<i8, u16>(0x7f), Some(0x007f));

        assert_eq!(checked_cast::<u8, i16>(0x00), Some(0x0000));
        assert_eq!(checked_cast::<u8, i16>(0x7f), Some(0x007f));
        assert_eq!(checked_cast::<u8, i16>(0x80), Some(0x0080));
        assert_eq!(checked_cast::<u8, i16>(0xff), Some(0x00ff));

        assert_eq!(checked_cast::<u8, u16>(0x00), Some(0x0000));
        assert_eq!(checked_cast::<u8, u16>(0x7f), Some(0x007f));
        assert_eq!(checked_cast::<u8, u16>(0x80), Some(0x0080));
        assert_eq!(checked_cast::<u8, u16>(0xff), Some(0x00ff));
    }

    #[test]
    fn checked_floats() {
        assert_eq!(
            checked_cast::<u64, f32>(0xffff_ffff_ffff_ffff_u64),
            Some(f32(1.0, 64))
        );
        assert_eq!(checked_cast::<f32, u64>(f32(1.0, 64)), None);
        assert_eq!(
            checked_cast::<f32, u64>(f32(1.0, 64) - f32(1.0, 40)),
            Some(0xffff_ff00_0000_0000_u64)
        );

        assert_eq!(checked_cast::<f32, u8>(0.0), Some(0));
        assert_eq!(checked_cast::<f32, i16>(-1.0 / 0.0), None);
        assert_eq!(checked_cast::<f32, u32>(1.0 / 0.0), None);
        assert_eq!(checked_cast::<f32, i64>(0.0 / 0.0), None);

        assert_eq!(checked_cast::<f32, i8>(-129.0), None);
        assert_eq!(checked_cast::<f32, i8>(-128.9), Some(-128));
        assert_eq!(checked_cast::<f32, i8>(-128.0), Some(-128));
        assert_eq!(checked_cast::<f32, i8>(-1.0), Some(-1));
        assert_eq!(checked_cast::<f32, i8>(127.0), Some(127));
        assert_eq!(checked_cast::<f32, i8>(127.9), Some(127));
        assert_eq!(checked_cast::<f32, i8>(128.0), None);

        assert_eq!(checked_cast::<_, u64>(f32(1.5, 52)), Some(3 << 51));
        assert_eq!(checked_cast::<_, i64>(f64(-1.5, 52)), Some(-3 << 51));
        assert_eq!(checked_cast::<_, u64>(f32(-1.5, 2)), None);
        assert_eq!(checked_cast::<_, i64>(f64(1.5, -1)), Some(0));
        assert_eq!(checked_cast::<_, u64>(f32(1.1, -40)), Some(0));
        assert_eq!(checked_cast::<_, i64>(f32(-1.1, -40)), Some(0));

        assert_eq!(checked_cast::<_, u64>(f32(1.5, 32)), Some(3 << 31));
        assert_eq!(checked_cast::<_, u32>(f32(1.5, 32)), None);
    }

    #[test]
    fn wrapping_to_smaller_size() {
        assert_eq!(wrapping_cast::<i16, i8>(-0x0100), 0x00);
        assert_eq!(wrapping_cast::<i16, i8>(-0x0081), 0x7f);
        assert_eq!(wrapping_cast::<i16, i8>(-0x0080), -0x80);
        assert_eq!(wrapping_cast::<i16, i8>(-0x0001), -0x01);
        assert_eq!(wrapping_cast::<i16, i8>(0x0000), 0x00);
        assert_eq!(wrapping_cast::<i16, i8>(0x007f), 0x7f);
        assert_eq!(wrapping_cast::<i16, i8>(0x0080), -0x80);
        assert_eq!(wrapping_cast::<i16, i8>(0x00ff), -0x01);
        assert_eq!(wrapping_cast::<i16, i8>(0x0100), 0x00);

        assert_eq!(wrapping_cast::<i16, u8>(-0x0100), 0x00);
        assert_eq!(wrapping_cast::<i16, u8>(-0x0081), 0x7f);
        assert_eq!(wrapping_cast::<i16, u8>(-0x0080), 0x80);
        assert_eq!(wrapping_cast::<i16, u8>(-0x0001), 0xff);
        assert_eq!(wrapping_cast::<i16, u8>(0x0000), 0x00);
        assert_eq!(wrapping_cast::<i16, u8>(0x007f), 0x7f);
        assert_eq!(wrapping_cast::<i16, u8>(0x0080), 0x80);
        assert_eq!(wrapping_cast::<i16, u8>(0x00ff), 0xff);
        assert_eq!(wrapping_cast::<i16, u8>(0x0100), 0x00);

        assert_eq!(wrapping_cast::<u16, i8>(0x0000), 0x00);
        assert_eq!(wrapping_cast::<u16, i8>(0x007f), 0x7f);
        assert_eq!(wrapping_cast::<u16, i8>(0x0080), -0x80);
        assert_eq!(wrapping_cast::<u16, i8>(0x00ff), -0x01);
        assert_eq!(wrapping_cast::<u16, i8>(0x0100), 0x00);

        assert_eq!(wrapping_cast::<u16, u8>(0x0000), 0x00);
        assert_eq!(wrapping_cast::<u16, u8>(0x007f), 0x7f);
        assert_eq!(wrapping_cast::<u16, u8>(0x0080), 0x80);
        assert_eq!(wrapping_cast::<u16, u8>(0x00ff), 0xff);
        assert_eq!(wrapping_cast::<u16, u8>(0x0100), 0x00);
    }

    #[test]
    fn wrapping_to_same_size() {
        assert_eq!(wrapping_cast::<i8, i8>(-0x80), -0x80);
        assert_eq!(wrapping_cast::<i8, i8>(-0x01), -0x01);
        assert_eq!(wrapping_cast::<i8, i8>(0x00), 0x00);
        assert_eq!(wrapping_cast::<i8, i8>(0x7f), 0x7f);

        assert_eq!(wrapping_cast::<i8, u8>(-0x80), 0x80);
        assert_eq!(wrapping_cast::<i8, u8>(-0x01), 0xff);
        assert_eq!(wrapping_cast::<i8, u8>(0x00), 0x00);
        assert_eq!(wrapping_cast::<i8, u8>(0x7f), 0x7f);

        assert_eq!(wrapping_cast::<u8, i8>(0x00), 0x00);
        assert_eq!(wrapping_cast::<u8, i8>(0x7f), 0x7f);
        assert_eq!(wrapping_cast::<u8, i8>(0x80), -0x80);
        assert_eq!(wrapping_cast::<u8, i8>(0xff), -0x01);

        assert_eq!(wrapping_cast::<u8, u8>(0x00), 0x00);
        assert_eq!(wrapping_cast::<u8, u8>(0x7f), 0x7f);
        assert_eq!(wrapping_cast::<u8, u8>(0x80), 0x80);
        assert_eq!(wrapping_cast::<u8, u8>(0xff), 0xff);
    }

    #[test]
    fn wrapping_to_larger_size() {
        assert_eq!(wrapping_cast::<i8, i16>(-0x80), -0x0080);
        assert_eq!(wrapping_cast::<i8, i16>(-0x01), -0x0001);
        assert_eq!(wrapping_cast::<i8, i16>(0x00), 0x0000);
        assert_eq!(wrapping_cast::<i8, i16>(0x7f), 0x007f);

        assert_eq!(wrapping_cast::<i8, u16>(-0x80), 0xff80);
        assert_eq!(wrapping_cast::<i8, u16>(-0x01), 0xffff);
        assert_eq!(wrapping_cast::<i8, u16>(0x00), 0x0000);
        assert_eq!(wrapping_cast::<i8, u16>(0x7f), 0x007f);

        assert_eq!(wrapping_cast::<u8, i16>(0x00), 0x0000);
        assert_eq!(wrapping_cast::<u8, i16>(0x7f), 0x007f);
        assert_eq!(wrapping_cast::<u8, i16>(0x80), 0x0080);
        assert_eq!(wrapping_cast::<u8, i16>(0xff), 0x00ff);

        assert_eq!(wrapping_cast::<u8, u16>(0x00), 0x0000);
        assert_eq!(wrapping_cast::<u8, u16>(0x7f), 0x007f);
        assert_eq!(wrapping_cast::<u8, u16>(0x80), 0x0080);
        assert_eq!(wrapping_cast::<u8, u16>(0xff), 0x00ff);
    }

    #[test]
    fn wrapping_floats() {
        assert_eq!(
            wrapping_cast::<u64, f32>(0xffff_ffff_ffff_ffff_u64),
            f32(1.0, 64)
        );
        assert_eq!(wrapping_cast::<f32, u64>(f32(1.0, 64)), 0);
        assert_eq!(
            wrapping_cast::<f32, u64>(f32(1.0, 64) - f32(1.0, 40)),
            0xffff_ff00_0000_0000_u64
        );

        assert_eq!(wrapping_cast::<f32, u8>(0.0), 0);
        assert_eq!(wrapping_cast::<f32, i16>(-1.0 / 0.0), 0);
        assert_eq!(wrapping_cast::<f32, u32>(1.0 / 0.0), 0);
        assert_eq!(wrapping_cast::<f32, i64>(0.0 / 0.0), 0);

        assert_eq!(wrapping_cast::<f32, i8>(-129.0), 127);
        assert_eq!(wrapping_cast::<f32, i8>(-128.9), -128);
        assert_eq!(wrapping_cast::<f32, i8>(-128.0), -128);
        assert_eq!(wrapping_cast::<f32, i8>(-1.0), -1);
        assert_eq!(wrapping_cast::<f32, i8>(127.0), 127);
        assert_eq!(wrapping_cast::<f32, i8>(127.9), 127);
        assert_eq!(wrapping_cast::<f32, i8>(128.0), -128);

        assert_eq!(wrapping_cast::<_, u64>(f32(1.5, 52)), 3 << 51);
        assert_eq!(wrapping_cast::<_, i64>(f64(-1.5, 52)), -3 << 51);
        assert_eq!(wrapping_cast::<_, u64>(f32(-1.5, 2)), -6i64 as u64);
        assert_eq!(wrapping_cast::<_, i64>(f64(1.5, -1)), 0);
        assert_eq!(wrapping_cast::<_, u64>(f32(1.1, -40)), 0);
        assert_eq!(wrapping_cast::<_, i64>(f32(-1.1, -40)), 0);

        assert_eq!(wrapping_cast::<_, u64>(f32(1.5, 32)), 3 << 31);
        assert_eq!(wrapping_cast::<_, u32>(f32(1.5, 32)), 1 << 31);
    }
}
