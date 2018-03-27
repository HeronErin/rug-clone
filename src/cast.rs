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

#![allow(dead_code)]

/**
Casts into the destination if the value fits, otherwise panics.

Floats are rounded towards zero when cast into integers.

# Panics

* If a NaN is cast into an integer type.
* If the value does not fit in the destination integer type.
*/
pub trait Cast<Dst> {
    fn cast(self) -> Dst;
}

/**
Casts into the destination if the value fits.

Floats are rounded towards zero when cast into integers.
*/
pub trait CheckedCast<Dst> {
    fn checked_cast(self) -> Option<Dst>;
}

/**
Casts into the destination, wrapping integers around if the value
does not fit.

Floats are rounded towards zero when cast into integers.
*/
pub trait WrappingCast<Dst> {
    fn wrapping_cast(self) -> Dst;
}

#[inline]
pub fn cast<Src, Dst>(src: Src) -> Dst
where
    Src: Cast<Dst>,
{
    src.cast()
}

#[inline]
pub fn checked_cast<Src, Dst>(src: Src) -> Option<Dst>
where
    Src: CheckedCast<Dst>,
{
    src.checked_cast()
}

#[inline]
pub fn wrapping_cast<Src, Dst>(src: Src) -> Dst
where
    Src: WrappingCast<Dst>,
{
    src.wrapping_cast()
}

macro_rules! cast_int_to_int {
    ($Src: ty => $($Dst: ty)*) => { $(
        impl Cast<$Dst> for $Src {
            #[inline]
            fn cast(self) -> $Dst {
                <$Src as CheckedCast<$Dst>>::checked_cast(self)
                    .expect("overflow")
            }
        }
    )* };
}

macro_rules! cast_float_to_int {
    ($Src: ty => $($Dst: ty)*) => { $(
        impl Cast<$Dst> for $Src {
            #[inline]
            fn cast(self) -> $Dst {
                assert!(!self.is_nan(), "NaN");
                <$Src as CheckedCast<$Dst>>::checked_cast(self)
                    .expect("overflow")
            }
        }
    )* };
}

macro_rules! cast_as {
    ($Src: ty => $($Dst: ty)*) => { $(
        impl Cast<$Dst> for $Src {
            #[allow(unknown_lints, cast_lossless)]
            #[inline]
            fn cast(self) -> $Dst {
                self as $Dst
            }
        }
    )* };
}

macro_rules! cast_int {
    ($($Src: ty)*) => { $(
        cast_int_to_int! { $Src => i8 i16 i32 i64 isize }
        #[cfg(int_128)]
        cast_int_to_int! { $Src => i128 }
        cast_int_to_int! { $Src => u8 u16 u32 u64 usize }
        #[cfg(int_128)]
        cast_int_to_int! { $Src => u128 }
        cast_as! { $Src => f32 f64 }
    )* };
}

macro_rules! cast_float {
    ($($Src: ty)*) => { $(
        cast_float_to_int! { $Src => i8 i16 i32 i64 isize }
        #[cfg(int_128)]
        cast_float_to_int! { $Src => i128 }
        cast_float_to_int! { $Src => u8 u16 u32 u64 usize }
        #[cfg(int_128)]
        cast_float_to_int! { $Src => u128 }
        cast_as! { $Src => f32 f64 }
    )* };
}

cast_int! { i8 i16 i32 i64 isize }
#[cfg(int_128)]
cast_int! { i128 }
cast_int! { u8 u16 u32 u64 usize }
#[cfg(int_128)]
cast_int! { u128 }
cast_float! { f32 f64 }

macro_rules! checked_same_signedness {
    ($Src: ty => $($Dst: ty)*) => { $(
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
    )* };
}

macro_rules! checked_signed_to_unsigned {
    ($Src: ty => $($Dst: ty)*) => { $(
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
    )* };
}

macro_rules! checked_unsigned_to_signed {
    ($Src: ty => $($Dst: ty)*) => { $(
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
    )* };
}

macro_rules! checked_float_via {
    ($Src: ty, $ViaU: ty, $ViaI: ty => $($Dst: ty)*) => { $(
        impl CheckedCast<$Dst> for $Src {
            #[allow(unknown_lints, cast_lossless)]
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                let f = <Float<$ViaU, bool> as From<$Src>>::from(self);
                if !f.fits {
                    return None;
                }
                if f.neg {
                    let i = f.wrapped as $ViaI;
                    if i < 0 {
                        return None
                    }
                    let i = -i;
                    <$ViaI as CheckedCast<$Dst>>::checked_cast(i)
                } else {
                    <$ViaU as CheckedCast<$Dst>>::checked_cast(f.wrapped)
                }
            }
        }
    )* };
}

macro_rules! checked_as {
    ($Src: ty => $($Dst: ty)*) => { $(
        impl CheckedCast<$Dst> for $Src {
            #[allow(unknown_lints, cast_lossless)]
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                Some(self as $Dst)
            }
        }
    )* };
}

macro_rules! checked_signed {
    ($($Src: ty)*) => { $(
        checked_same_signedness! { $Src => i8 i16 i32 i64 isize }
        #[cfg(int_128)]
        checked_same_signedness! { $Src => i128 }
        checked_signed_to_unsigned! { $Src => u8 u16 u32 u64 usize }
        #[cfg(int_128)]
        checked_signed_to_unsigned! { $Src => u128 }
        checked_as! { $Src => f32 f64 }
    )* };
}

macro_rules! checked_unsigned {
    ($($Src: ty)*) => { $(
        checked_unsigned_to_signed! { $Src => i8 i16 i32 i64 isize }
        #[cfg(int_128)]
        checked_unsigned_to_signed! { $Src => i128 }
        checked_same_signedness! { $Src => u8 u16 u32 u64 usize }
        #[cfg(int_128)]
        checked_same_signedness! { $Src => u128 }
        checked_as! { $Src => f32 f64 }
    )* };
}

checked_signed! { i8 i16 i32 i64 isize }
#[cfg(int_128)]
checked_signed! { i128 }
checked_unsigned! { u8 u16 u32 u64 usize }
#[cfg(int_128)]
checked_unsigned! { u128 }

checked_float_via! { f32, u32, i32 => i8 i16 i32 }
checked_float_via! { f32, u64, i64 => i64 }
#[cfg(target_pointer_width = "32")]
checked_float_via! { f32, u32, i32 => isize }
#[cfg(target_pointer_width = "64")]
checked_float_via! { f32, u64, i64 => isize }
#[cfg(int_128)]
checked_float_via! { f32, u128, i128 => i128 }
checked_float_via! { f32, u32, i32 => u8 u16 u32 }
checked_float_via! { f32, u64, i64 => u64 }
#[cfg(target_pointer_width = "32")]
checked_float_via! { f32, u32, i32 => usize }
#[cfg(target_pointer_width = "64")]
checked_float_via! { f32, u64, i64 => usize }
#[cfg(int_128)]
checked_float_via! { f32, u128, i128 => u128 }
checked_as! { f32 => f32 f64 }

checked_float_via! { f64, u64, i64 => i8 i16 i32 i64 isize }
#[cfg(int_128)]
checked_float_via! { f64, u128, i128 => i128 }
checked_float_via! { f64, u64, i64 => u8 u16 u32 u64 usize }
#[cfg(int_128)]
checked_float_via! { f64, u128, i128 => u128 }
checked_as! { f64 => f32 f64 }

macro_rules! wrapping_as {
    ($Src: ty => $($Dst: ty)*) => { $(
        impl WrappingCast<$Dst> for $Src {
            #[allow(unknown_lints, cast_lossless)]
            #[inline]
            fn wrapping_cast(self) -> $Dst {
                self as $Dst
            }
        }
    )* };
}

macro_rules! wrapping_float_via {
    ($Src: ty, $Via: ty => $($Dst: ty)*) => { $(
        impl WrappingCast<$Dst> for $Src {
            #[inline]
            fn wrapping_cast(self) -> $Dst {
                let f = <Float<$Via, ()> as From<$Src>>::from(self);
                let u = f.wrapped;
                let n = if f.neg { u.wrapping_neg() } else { u };
                n as $Dst
            }
        }
    )* };
}

macro_rules! wrapping_int {
    ($($Src: ty)*) => { $(
        wrapping_as! { $Src => i8 i16 i32 i64 isize }
        #[cfg(int_128)]
        wrapping_as! { $Src => i128 }
        wrapping_as! { $Src => u8 u16 u32 u64 usize }
        #[cfg(int_128)]
        wrapping_as! { $Src => u128 }
        wrapping_as! { $Src => f32 f64 }
    )* };
}

wrapping_int! { i8 i16 i32 i64 isize }
#[cfg(int_128)]
wrapping_int! { i128 }
wrapping_int! { u8 u16 u32 u64 usize }
#[cfg(int_128)]
wrapping_int! { u128 }

wrapping_float_via! { f32, u32 => i8 i16 i32 }
wrapping_float_via! { f32, u64 => i64 }
#[cfg(target_pointer_width = "32")]
wrapping_float_via! { f32, u32 => isize }
#[cfg(target_pointer_width = "64")]
wrapping_float_via! { f32, u64 => isize }
#[cfg(int_128)]
wrapping_float_via! { f32, u128 => i128 }
wrapping_float_via! { f32, u32 => u8 u16 u32 }
wrapping_float_via! { f32, u64 => u64 }
#[cfg(target_pointer_width = "32")]
wrapping_float_via! { f32, u32 => usize }
#[cfg(target_pointer_width = "64")]
wrapping_float_via! { f32, u64 => usize }
#[cfg(int_128)]
wrapping_float_via! { f32, u128 => u128 }
wrapping_as! { f32 => f32 f64 }

wrapping_float_via! { f64, u64 => i8 i16 i32 i64 isize }
#[cfg(int_128)]
wrapping_float_via! { f64, u128 => i128 }
wrapping_float_via! { f64, u64 => u8 u16 u32 u64 usize }
#[cfg(int_128)]
wrapping_float_via! { f64, u128 => u128 }
wrapping_as! { f64 => f32 f64 }

struct Float<Uns, Fit> {
    neg: bool,
    fits: Fit,
    wrapped: Uns,
}

trait YesNo: Sized {
    fn yes_no() -> (Self, Self);
}
impl YesNo for bool {
    #[inline]
    fn yes_no() -> (bool, bool) {
        (true, false)
    }
}
impl YesNo for () {
    #[inline]
    fn yes_no() -> ((), ()) {
        ((), ())
    }
}

macro_rules! from_for_float {
    (
        $Src: ty, $Uns: ty, $exp_bits: expr, $mant_bits: expr;
        $($Fit: ty, $Dst: ty, $dst_bits: expr);*
    ) => { $(
        impl From<$Src> for Float<$Dst, $Fit> {
            fn from(src: $Src) -> Self {
                const EXP_BITS: i32 = $exp_bits;
                const MANT_BITS: i32 = $mant_bits;
                const OUT_BITS: i32 = $dst_bits;
                const SIGN_MASK: $Uns = 1 << (EXP_BITS + MANT_BITS);
                const EXP_MASK: $Uns = ((1 << EXP_BITS) - 1) << MANT_BITS;
                const MANT_MASK: $Uns = (1 << MANT_BITS) - 1;
                const EXP_BIAS: i32 = (1 << (EXP_BITS - 1)) - 1;

                let (fits_yes, fits_no) = <$Fit as YesNo>::yes_no();

                let u: $Uns = unsafe { ::std::mem::transmute(src) };
                let neg = (u & SIGN_MASK) != 0;
                let biased_exp = u & EXP_MASK;
                let shift = (biased_exp >> MANT_BITS) as i32
                    - (EXP_BIAS + MANT_BITS);

                // Check if the magnitude is smaller than one. Do not return
                // early if shift == -MANT_BITS, as there is implicit one.
                if shift < -MANT_BITS {
                    return Float {
                        neg,
                        fits: fits_yes,
                        wrapped: 0,
                    };
                }

                // Check if the least significant bit will be in a $dst. This
                // condition handles infinites and NaNs too.
                if shift >= OUT_BITS {
                    return Float {
                        neg,
                        fits: fits_no,
                        wrapped: 0,
                    };
                }

                // Add implicit one.
                let significand = <$Dst as From<$Uns>>::from(u & MANT_MASK)
                    | (1 << MANT_BITS);
                let (fits, wrapped) = if shift < 0 {
                    (fits_yes, significand >> -shift)
                } else {
                    let wrapped = significand << shift;
                    let fits = if fits_yes == fits_no
                        || (wrapped >> shift) == significand
                    {
                        fits_yes
                    } else {
                        fits_no
                    };
                    (fits, wrapped)
                };
                Float { neg, fits, wrapped }
            }
        }
    )* };
}

from_for_float! {
    f32, u32, 8, 23;
    bool, u32, 32;
    (), u32, 32;
    bool, u64, 64;
    (), u64, 64
}
#[cfg(int_128)]
from_for_float! {
    f32, u32, 8, 23;
    bool, u128, 128;
    (), u128, 128
}
from_for_float! {
    f64, u64, 11, 52;
    bool, u64, 64;
    (), u64, 64
}
#[cfg(int_128)]
from_for_float! {
    f64, u64, 11, 52;
    bool, u128, 128;
    (), u128, 128
}

// TODO: 128 bit
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

        assert_eq!(
            checked_cast::<_, u64>(f32(1.5, 63)),
            Some(3 << 62)
        );
        assert_eq!(checked_cast::<_, i64>(f32(-1.5, 63)), None);
        assert_eq!(
            checked_cast::<_, u64>(f32(1.5, 62)),
            Some(3 << 61)
        );
        assert_eq!(
            checked_cast::<_, i64>(f64(-1.5, 62)),
            Some(-3 << 61)
        );
        assert_eq!(checked_cast::<_, u64>(f32(-1.5, 2)), None);
        assert_eq!(checked_cast::<_, i64>(f64(1.5, -1)), Some(0));
        assert_eq!(checked_cast::<_, u64>(f32(1.1, -40)), Some(0));
        assert_eq!(checked_cast::<_, i64>(f32(-1.1, -40)), Some(0));

        assert_eq!(
            checked_cast::<_, u64>(f32(1.5, 32)),
            Some(3 << 31)
        );
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
        assert_eq!(
            wrapping_cast::<_, u64>(f32(-1.5, 2)),
            -6i64 as u64
        );
        assert_eq!(wrapping_cast::<_, i64>(f64(1.5, -1)), 0);
        assert_eq!(wrapping_cast::<_, u64>(f32(1.1, -40)), 0);
        assert_eq!(wrapping_cast::<_, i64>(f32(-1.1, -40)), 0);

        assert_eq!(wrapping_cast::<_, u64>(f32(1.5, 32)), 3 << 31);
        assert_eq!(wrapping_cast::<_, u32>(f32(1.5, 32)), 1 << 31);
    }
}
