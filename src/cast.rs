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

pub trait CheckedCast<Dst> {
    fn checked_cast(self) -> Option<Dst>;
}

macro_rules! same_signedness {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl CheckedCast<$Dst> for $Src {
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

macro_rules! signed_to_unsigned {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl CheckedCast<$Dst> for $Src {
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

macro_rules! unsigned_to_signed {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl CheckedCast<$Dst> for $Src {
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

macro_rules! float_to_integer {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl CheckedCast<$Dst> for $Src {
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                if !self.is_finite() {
                    return None;
                }
                let trunc = self.trunc();
                if trunc >= <$Dst>::min_value() as $Src
                    && trunc <= <$Dst>::max_value() as $Src
                {
                    Some(trunc as $Dst)
                } else {
                    None
                }
            }
        }
    )* }
}

macro_rules! always_works {
    { $Src:ty => $($Dst:ty)* } => { $(
        impl CheckedCast<$Dst> for $Src {
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                Some(self as $Dst)
            }
        }
    )* }
}

macro_rules! signed_to {
    { $($Src:ty)* } => { $(
        same_signedness! { $Src => i8 i16 i32 i64 isize }
        signed_to_unsigned! { $Src => u8 u16 u32 u64 usize }
        always_works! { $Src => f32 f64 }
    )*}
}

macro_rules! unsigned_to {
    { $($Src:ty)* } => { $(
        unsigned_to_signed! { $Src => i8 i16 i32 i64 isize }
        same_signedness! { $Src => u8 u16 u32 u64 usize }
        always_works! { $Src => f32 f64 }
    )*}
}

macro_rules! float_to {
    { $($Src:ty)* } => { $(
        float_to_integer! { $Src => i8 i16 i32 i64 isize }
        float_to_integer! { $Src => u8 u16 u32 u64 usize }
        always_works! { $Src => f32 f64 }
    )*}
}

signed_to! { i8 i16 i32 i64 isize }
unsigned_to! { u8 u16 u32 u64 usize }
float_to! { f32 f64 }

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
pub fn cast<Src, Dst>(src: Src) -> Dst
where
    Src: CheckedCast<Dst>,
{
    src.checked_cast().expect("overflow")
}

#[cfg(test)]
mod tests {
    use cast::checked_cast;

    #[test]
    fn to_smaller_size() {
        assert_eq!(checked_cast::<i16, i8>(-256), None);
        assert_eq!(checked_cast::<i16, i8>(-128), Some(-128));
        assert_eq!(checked_cast::<i16, i8>(-1), Some(-1));
        assert_eq!(checked_cast::<i16, i8>(0), Some(0));
        assert_eq!(checked_cast::<i16, i8>(127), Some(127));
        assert_eq!(checked_cast::<i16, i8>(128), None);
        assert_eq!(checked_cast::<i16, i8>(255), None);
        assert_eq!(checked_cast::<i16, i8>(256), None);

        assert_eq!(checked_cast::<i16, u8>(-256), None);
        assert_eq!(checked_cast::<i16, u8>(-128), None);
        assert_eq!(checked_cast::<i16, u8>(-1), None);
        assert_eq!(checked_cast::<i16, u8>(0), Some(0));
        assert_eq!(checked_cast::<i16, u8>(127), Some(127));
        assert_eq!(checked_cast::<i16, u8>(128), Some(128));
        assert_eq!(checked_cast::<i16, u8>(255), Some(255));
        assert_eq!(checked_cast::<i16, u8>(256), None);

        assert_eq!(checked_cast::<u16, i8>(0), Some(0));
        assert_eq!(checked_cast::<u16, i8>(127), Some(127));
        assert_eq!(checked_cast::<u16, i8>(128), None);
        assert_eq!(checked_cast::<u16, i8>(255), None);
        assert_eq!(checked_cast::<u16, i8>(256), None);

        assert_eq!(checked_cast::<u16, u8>(0), Some(0));
        assert_eq!(checked_cast::<u16, u8>(127), Some(127));
        assert_eq!(checked_cast::<u16, u8>(128), Some(128));
        assert_eq!(checked_cast::<u16, u8>(255), Some(255));
        assert_eq!(checked_cast::<u16, u8>(256), None);
    }

    #[test]
    fn to_same_size() {
        assert_eq!(checked_cast::<i8, i8>(-128), Some(-128));
        assert_eq!(checked_cast::<i8, i8>(-1), Some(-1));
        assert_eq!(checked_cast::<i8, i8>(0), Some(0));
        assert_eq!(checked_cast::<i8, i8>(127), Some(127));

        assert_eq!(checked_cast::<i8, u8>(-128), None);
        assert_eq!(checked_cast::<i8, u8>(-1), None);
        assert_eq!(checked_cast::<i8, u8>(0), Some(0));
        assert_eq!(checked_cast::<i8, u8>(127), Some(127));

        assert_eq!(checked_cast::<u8, i8>(0), Some(0));
        assert_eq!(checked_cast::<u8, i8>(127), Some(127));
        assert_eq!(checked_cast::<u8, i8>(128), None);
        assert_eq!(checked_cast::<u8, i8>(255), None);

        assert_eq!(checked_cast::<u8, u8>(0), Some(0));
        assert_eq!(checked_cast::<u8, u8>(127), Some(127));
        assert_eq!(checked_cast::<u8, u8>(128), Some(128));
        assert_eq!(checked_cast::<u8, u8>(255), Some(255));
    }

    #[test]
    fn to_larger_size() {
        assert_eq!(checked_cast::<i8, i16>(-128), Some(-128));
        assert_eq!(checked_cast::<i8, i16>(-1), Some(-1));
        assert_eq!(checked_cast::<i8, i16>(0), Some(0));
        assert_eq!(checked_cast::<i8, i16>(127), Some(127));

        assert_eq!(checked_cast::<i8, u16>(-128), None);
        assert_eq!(checked_cast::<i8, u16>(-1), None);
        assert_eq!(checked_cast::<i8, u16>(0), Some(0));
        assert_eq!(checked_cast::<i8, u16>(127), Some(127));

        assert_eq!(checked_cast::<u8, i16>(0), Some(0));
        assert_eq!(checked_cast::<u8, i16>(127), Some(127));
        assert_eq!(checked_cast::<u8, i16>(128), Some(128));
        assert_eq!(checked_cast::<u8, i16>(255), Some(255));

        assert_eq!(checked_cast::<u8, u16>(0), Some(0));
        assert_eq!(checked_cast::<u8, u16>(127), Some(127));
        assert_eq!(checked_cast::<u8, u16>(128), Some(128));
        assert_eq!(checked_cast::<u8, u16>(255), Some(255));
    }

    #[test]
    fn floats() {
        assert!(checked_cast::<u64, f32>(0xffff_ffff_ffff_ffff_u64).is_some());

        assert_eq!(checked_cast::<f32, i8>(-1.0 / 0.0), None);
        assert_eq!(checked_cast::<f32, i8>(-129.0), None);
        assert_eq!(checked_cast::<f32, i8>(-128.9), Some(-128));
        assert_eq!(checked_cast::<f32, i8>(-128.0), Some(-128));
        assert_eq!(checked_cast::<f32, i8>(-1.0), Some(-1));
        assert_eq!(checked_cast::<f32, i8>(0.0), Some(0));
        assert_eq!(checked_cast::<f32, i8>(127.0), Some(127));
        assert_eq!(checked_cast::<f32, i8>(127.9), Some(127));
        assert_eq!(checked_cast::<f32, i8>(128.0), None);
        assert_eq!(checked_cast::<f32, i8>(1.0 / 0.0), None);
        assert_eq!(checked_cast::<f32, i8>(0.0 / 0.0), None);
    }
}
