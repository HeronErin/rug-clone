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

use cast::cast;
use ext::mpfr as xmpfr;
use float::big::{self, ordering1, raw_round};
use float::{Constant, ParseFloatError, Round, Special};
use gmp_mpfr_sys::mpfr;
use inner::{Inner, InnerMut};
use ops::AssignRound;
#[cfg(all(try_from, feature = "rational"))]
use rational::TryFromFloatError;
use std::cmp::Ordering;
#[cfg(all(try_from, feature = "rational"))]
use std::convert::TryFrom;
use std::fmt::{
    self, Binary, Debug, Display, Formatter, LowerExp, LowerHex, Octal,
    UpperExp, UpperHex,
};
use std::mem;
use std::os::raw::{c_long, c_ulong};
use std::{i32, u32};
#[cfg(feature = "integer")]
use Integer;
#[cfg(feature = "rational")]
use Rational;
use {Assign, Float};

impl Clone for Float {
    #[inline]
    fn clone(&self) -> Float {
        let mut ret = Float::new(self.prec());
        ret.assign(self);
        ret
    }

    #[inline]
    fn clone_from(&mut self, source: &Float) {
        unsafe {
            mpfr::set_prec(self.inner_mut(), cast(source.prec()));
        }
        self.assign(source);
    }
}

impl Drop for Float {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            mpfr::clear(self.inner_mut());
        }
    }
}

impl Display for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Debug for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl LowerExp for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl UpperExp for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, true, "")
    }
}

impl Binary for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b")
    }
}

impl Octal for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o")
    }
}

impl LowerHex for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x")
    }
}

impl UpperHex for Float {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x")
    }
}

impl<T> Assign<T> for Float
where
    Self: AssignRound<T, Round = Round, Ordering = Ordering>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        self.assign_round(src, Round::Nearest);
    }
}

impl AssignRound<Constant> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: Constant, round: Round) -> Ordering {
        let ret = unsafe {
            match src {
                Constant::Log2 => {
                    mpfr::const_log2(self.inner_mut(), raw_round(round))
                }
                Constant::Pi => {
                    mpfr::const_pi(self.inner_mut(), raw_round(round))
                }
                Constant::Euler => {
                    mpfr::const_euler(self.inner_mut(), raw_round(round))
                }
                Constant::Catalan => {
                    mpfr::const_catalan(self.inner_mut(), raw_round(round))
                }
                _ => unreachable!(),
            }
        };
        ordering1(ret)
    }
}

assign_round_deref! { Constant => Float }

impl AssignRound<Special> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: Special, _round: Round) -> Ordering {
        const EXP_MAX: c_long = ((!0 as c_ulong) >> 1) as c_long;
        const EXP_ZERO: c_long = 0 - EXP_MAX;
        const EXP_NAN: c_long = 1 - EXP_MAX;
        const EXP_INF: c_long = 2 - EXP_MAX;
        unsafe {
            let ptr = self.inner_mut();
            match src {
                Special::Zero => {
                    (*ptr).sign = 1;
                    (*ptr).exp = EXP_ZERO;
                }
                Special::NegZero => {
                    (*ptr).sign = -1;
                    (*ptr).exp = EXP_ZERO;
                }
                Special::Infinity => {
                    (*ptr).sign = 1;
                    (*ptr).exp = EXP_INF;
                }
                Special::NegInfinity => {
                    (*ptr).sign = -1;
                    (*ptr).exp = EXP_INF;
                }
                Special::Nan => {
                    (*ptr).sign = 1;
                    (*ptr).exp = EXP_NAN;
                }
                _ => unreachable!(),
            }
        }
        Ordering::Equal
    }
}

assign_round_deref! { Special => Float }

impl AssignRound for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: Float, round: Round) -> Ordering {
        if self.prec() == src.prec() {
            mem::drop(mem::replace(self, src));
            Ordering::Equal
        } else {
            <Float as AssignRound<&Float>>::assign_round(self, &src, round)
        }
    }
}

impl<'a> AssignRound<&'a Float> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: &Float, round: Round) -> Ordering {
        let ret = unsafe {
            mpfr::set(self.inner_mut(), src.inner(), raw_round(round))
        };
        ordering1(ret)
    }
}

#[cfg(feature = "integer")]
macro_rules! assign {
    ($T:ty, $func:path) => {
        impl<'a> AssignRound<&'a $T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round(&mut self, src: &$T, round: Round) -> Ordering {
                let ret = unsafe {
                    $func(self.inner_mut(), src.inner(), raw_round(round))
                };
                ordering1(ret)
            }
        }

        impl AssignRound<$T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round(&mut self, src: $T, round: Round) -> Ordering {
                <Float as AssignRound<&$T>>::assign_round(self, &src, round)
            }
        }
    };
}

#[cfg(feature = "integer")]
assign! { Integer, mpfr::set_z }
#[cfg(feature = "rational")]
assign! { Rational, mpfr::set_q }

macro_rules! conv_ops {
    ($T:ty, $set:path) => {
        impl AssignRound<$T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round(&mut self, src: $T, round: Round) -> Ordering {
                let ret = unsafe {
                    $set(self.inner_mut(), src.into(), raw_round(round))
                };
                ordering1(ret)
            }
        }

        assign_round_deref! { $T => Float }
    };
}

macro_rules! conv_ops_cast {
    ($New:ty, $Existing:ty) => {
        impl AssignRound<$New> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round(&mut self, src: $New, round: Round) -> Ordering {
                <Float as AssignRound<$Existing>>::assign_round(
                    self,
                    cast(src),
                    round,
                )
            }
        }

        assign_round_deref! { $New => Float }
    };
}

conv_ops! { i8, mpfr::set_si }
conv_ops! { i16, mpfr::set_si }
conv_ops! { i32, mpfr::set_si }
conv_ops! { i64, mpfr::set_sj }
#[cfg(target_pointer_width = "32")]
conv_ops_cast! { isize, i32 }
#[cfg(target_pointer_width = "64")]
conv_ops_cast! { isize, i64 }
#[cfg(int_128)]
conv_ops! { i128, xmpfr::set_i128 }

conv_ops! { u8, mpfr::set_ui }
conv_ops! { u16, mpfr::set_ui }
conv_ops! { u32, mpfr::set_ui }
conv_ops! { u64, mpfr::set_uj }
#[cfg(target_pointer_width = "32")]
conv_ops_cast! { usize, u32 }
#[cfg(target_pointer_width = "64")]
conv_ops_cast! { usize, u64 }
#[cfg(int_128)]
conv_ops! { u128, xmpfr::set_u128 }

conv_ops! { f32, xmpfr::set_f32 }
conv_ops! { f64, xmpfr::set_f64 }

#[cfg(all(try_from, feature = "rational"))]
impl TryFrom<Float> for Rational {
    type Error = TryFromFloatError;
    fn try_from(value: Float) -> Result<Self, TryFromFloatError> {
        TryFrom::try_from(&value)
    }
}

#[cfg(all(try_from, feature = "rational"))]
impl<'a> TryFrom<&'a Float> for Rational {
    type Error = TryFromFloatError;
    fn try_from(value: &Float) -> Result<Self, TryFromFloatError> {
        value.to_rational().ok_or(TryFromFloatError { _unused: () })
    }
}

fn fmt_radix(
    flt: &Float,
    fmt: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
) -> fmt::Result {
    let mut s = String::new();
    big::append_to_string(
        &mut s,
        flt,
        radix,
        fmt.precision(),
        Round::Nearest,
        to_upper,
    );
    let (neg, buf) = if s.starts_with('-') {
        (true, &s[1..])
    } else {
        (false, &s[..])
    };
    let prefix = if flt.is_finite() { prefix } else { "" };
    fmt.pad_integral(!neg, prefix, buf)
}

impl Display for ParseFloatError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

unsafe impl Send for Float {}
unsafe impl Sync for Float {}

#[cfg(test)]
mod tests {
    use float::Round;
    use ops::AssignRound;
    use std::cmp::Ordering;
    use {Assign, Float};

    #[test]
    fn check_assign() {
        let mut f = Float::with_val(4, 1.0);
        assert_eq!(f, 1.0);

        let other = Float::with_val(53, 14.75);
        let mut dir = f.assign_round(&other, Round::Nearest);
        assert_eq!(f, 15.0);
        assert_eq!(dir, Ordering::Greater);

        dir = f.assign_round(14.25, Round::Nearest);
        assert_eq!(f, 14.0);
        assert_eq!(dir, Ordering::Less);

        f.assign(other);
        assert_eq!(f, 15.0);
    }

    #[cfg(all(try_from, feature = "rational"))]
    #[test]
    fn check_fallible_conversions() {
        use float::Special;
        use std::convert::TryFrom;
        use {Float, Rational};
        let large = [
            Float::with_val(20, Special::Zero),
            Float::with_val(20, Special::NegZero),
            Float::with_val(20, Special::Infinity),
            Float::with_val(20, Special::NegInfinity),
            Float::with_val(20, Special::Nan),
            Float::with_val(20, 1),
            Float::with_val(20, -1),
            Float::with_val(20, 999999e100),
            Float::with_val(20, 999999e-100),
            Float::with_val(20, -999999e100),
            Float::with_val(20, -999999e-100),
        ];
        for f in &large {
            let r = Rational::try_from(f);
            assert_eq!(r.is_ok(), f.is_finite());
            if let Ok(r) = r {
                assert_eq!(r, *f);
            }
        }
    }
}
