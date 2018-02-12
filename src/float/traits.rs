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

use {Assign, Float};
#[cfg(feature = "integer")]
use Integer;
#[cfg(feature = "rational")]
use Rational;
use cast::cast;
use ext::mpfr as xmpfr;
use float::{Constant, OrdFloat, ParseFloatError, Round, Special};
use float::big::{self, raw_round, ordering1};
use gmp_mpfr_sys::mpfr;
use inner::{Inner, InnerMut};
use ops::AssignRound;
use std::{i32, u32};
use std::cmp::Ordering;
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerExp, LowerHex,
               Octal, UpperExp, UpperHex};
use std::mem;
use std::os::raw::{c_long, c_ulong};

impl Clone for Float {
    #[inline]
    fn clone(&self) -> Float {
        let mut ret = Float::new(self.prec());
        ret.assign(self);
        ret
    }

    #[inline]
    fn clone_from(&mut self, source: &Float) {
        self.set_prec(source.prec());
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

impl From<OrdFloat> for Float {
    fn from(ord: OrdFloat) -> Self {
        unsafe { mem::transmute(ord) }
    }
}

impl Display for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Debug for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl LowerExp for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl UpperExp for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, true, "")
    }
}

impl Binary for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b")
    }
}

impl Octal for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o")
    }
}

impl LowerHex for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x")
    }
}

impl UpperHex for Float {
    #[inline]
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

impl<T> Assign<T> for (Float, Ordering)
where
    for<'a, 'b> (&'a mut Float, &'b mut Ordering): AssignRound<
        T,
        Round = Round,
        Ordering = Ordering,
    >,
{
    #[inline]
    fn assign(&mut self, src: T) {
        (&mut self.0, &mut self.1).assign_round(src, Round::Nearest);
    }
}

impl<T> AssignRound<T> for (Float, Ordering)
where
    for<'a, 'b> (&'a mut Float, &'b mut Ordering): AssignRound<
        T,
        Round = Round,
        Ordering = Ordering,
    >,
{
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: T, round: Round) -> Ordering {
        (&mut self.0, &mut self.1).assign_round(src, round)
    }
}

impl<'a, 'b, T> Assign<T> for (&'a mut Float, &'b mut Ordering)
where
    Self: AssignRound<T, Round = Round, Ordering = Ordering>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        self.assign_round(src, Round::Nearest);
    }
}

impl<T> Assign<T> for (Float, Float)
where
    for<'a, 'b> (&'a mut Float, &'b mut Float): AssignRound<
        T,
        Round = Round,
        Ordering = (Ordering, Ordering),
    >,
{
    #[inline]
    fn assign(&mut self, src: T) {
        (&mut self.0, &mut self.1).assign_round(src, Round::Nearest);
    }
}

impl<'a, 'b, T> Assign<T> for (&'a mut Float, &'b mut Float)
where
    Self: AssignRound<T, Round = Round, Ordering = (Ordering, Ordering)>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        self.assign_round(src, Round::Nearest);
    }
}

impl<T> AssignRound<T> for (Float, Float)
where
    for<'a, 'b> (&'a mut Float, &'b mut Float): AssignRound<
        T,
        Round = Round,
        Ordering = (Ordering, Ordering),
    >,
{
    type Round = Round;
    type Ordering = (Ordering, Ordering);
    #[inline]
    fn assign_round(&mut self, src: T, round: Round) -> (Ordering, Ordering) {
        (&mut self.0, &mut self.1).assign_round(src, round)
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
            }
        };
        ordering1(ret)
    }
}

assign_round_deref!{ Constant => Float }

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
            };
        }
        Ordering::Equal
    }
}

assign_round_deref!{ Special => Float }

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
    fn assign_round(&mut self, src: &'a Float, round: Round) -> Ordering {
        let ret = unsafe {
            mpfr::set(self.inner_mut(), src.inner(), raw_round(round))
        };
        ordering1(ret)
    }
}

#[cfg(feature = "integer")]
macro_rules! assign {
    { $T:ty, $func:path } => {
        impl<'a> AssignRound<&'a $T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round(&mut self, src: &'a $T, round: Round) -> Ordering {
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
            fn assign_round(&mut self, src: $T, round: Round,) -> Ordering {
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
    { $T:ty, $set:path } => {
        impl AssignRound<$T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round(&mut self, src: $T, round: Round,) -> Ordering {
                let ret = unsafe {
                    $set(self.inner_mut(), src.into(), raw_round(round))
                };
                ordering1(ret)
            }
        }

        assign_round_deref!{ $T => Float }
    }
}

macro_rules! conv_ops_cast {
    { $New:ty, $Existing:ty } => {
        impl AssignRound<$New> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round(&mut self, src: $New, round: Round,) -> Ordering {
                <Float as AssignRound<$Existing>>::assign_round(
                    self,
                    cast(src),
                    round
                )
            }
        }

        assign_round_deref!{ $New => Float }
    }
}

conv_ops!{ i8, mpfr::set_si }
conv_ops!{ i16, mpfr::set_si }
conv_ops!{ i32, mpfr::set_si }
conv_ops!{ i64, xmpfr::set_i64 }
#[cfg(target_pointer_width = "32")]
conv_ops_cast! { isize, i32 }
#[cfg(target_pointer_width = "64")]
conv_ops_cast! { isize, i64 }

conv_ops!{ u8, mpfr::set_ui }
conv_ops!{ u16, mpfr::set_ui }
conv_ops!{ u32, mpfr::set_ui }
conv_ops!{ u64, xmpfr::set_u64 }
#[cfg(target_pointer_width = "32")]
conv_ops_cast! { usize, u32 }
#[cfg(target_pointer_width = "64")]
conv_ops_cast! { usize, u64 }

conv_ops!{ f32, xmpfr::set_f32 }
conv_ops!{ f64, xmpfr::set_f64 }

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
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

unsafe impl Send for Float {}
unsafe impl Sync for Float {}
