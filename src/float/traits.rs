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

use {Assign, Float};
#[cfg(feature = "integer")]
use Integer;
#[cfg(feature = "rational")]
use Rational;
use big_float::{self, rraw, ordering1};
use ext::mpfr as xmpfr;
use float::{Constant, OrdFloat, ParseFloatError, Round, Special};
use gmp_mpfr_sys::mpfr;
use inner::{Inner, InnerMut};
use misc;
use ops::{AssignRound, AssignRoundTo, AssignTo};
use std::{i32, u32};
use std::cmp::Ordering;
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerExp, LowerHex,
               Octal, UpperExp, UpperHex};
use std::mem;
use std::os::raw::{c_long, c_ulong};

impl Default for Float {
    #[inline]
    fn default() -> Float {
        Float::new(53)
    }
}

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
    fn from(ord: OrdFloat) -> Float {
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
    T: AssignRoundTo<Float, Round = Round, Ordering = Ordering>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_round_to(self, Round::Nearest);
    }
}

impl<T> AssignRound<T> for Float
where
    T: AssignRoundTo<Float, Round = Round, Ordering = Ordering>,
{
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: T, round: Round) -> Ordering {
        src.assign_round_to(self, round)
    }
}

impl<T> Assign<T> for Result<Float, Float>
where
    T: for<'a> AssignTo<Result<&'a mut Float, &'a mut Float>>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        let ok = {
            let mut m = self.as_mut();
            src.assign_to(&mut m);
            m.is_ok()
        };
        if self.is_ok() != ok {
            misc::result_swap(self);
        }
    }
}

impl<'a, T> Assign<T> for Result<&'a mut Float, &'a mut Float>
where
    T: AssignTo<Self>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_to(self);
    }
}

impl<T> Assign<T> for (Float, Ordering)
where
    T: for<'a, 'b> AssignRoundTo<
        (&'a mut Float, &'b mut Ordering),
        Round = Round,
        Ordering = Ordering,
    >,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_round_to(&mut (&mut self.0, &mut self.1), Round::Nearest);
    }
}

impl<T> AssignRound<T> for (Float, Ordering)
where
    T: for<'a, 'b> AssignRoundTo<
        (&'a mut Float, &'b mut Ordering),
        Round = Round,
        Ordering = Ordering,
    >,
{
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: T, round: Round) -> Ordering {
        src.assign_round_to(&mut (&mut self.0, &mut self.1), round)
    }
}

impl<'a, 'b, T> Assign<T> for (&'a mut Float, &'b mut Ordering)
where
    T: AssignRoundTo<Self, Round = Round, Ordering = Ordering>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_round_to(self, Round::Nearest);
    }
}

impl<'a, 'b, T> AssignRound<T> for (&'a mut Float, &'b mut Ordering)
where
    T: AssignRoundTo<Self, Round = Round, Ordering = Ordering>,
{
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, src: T, round: Round) -> Ordering {
        src.assign_round_to(self, round)
    }
}

impl<T> Assign<T> for (Float, Float)
where
    T: for<'a, 'b> AssignRoundTo<
        (&'a mut Float, &'b mut Float),
        Round = Round,
        Ordering = (Ordering, Ordering),
    >,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_round_to(&mut (&mut self.0, &mut self.1), Round::Nearest);
    }
}

impl<'a, 'b, T> Assign<T> for (&'a mut Float, &'b mut Float)
where
    T: AssignRoundTo<Self, Round = Round, Ordering = (Ordering, Ordering)>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_round_to(self, Round::Nearest);
    }
}

impl<T> AssignRound<T> for (Float, Float)
where
    T: for<'a, 'b> AssignRoundTo<
        (&'a mut Float, &'b mut Float),
        Round = Round,
        Ordering = (Ordering, Ordering),
    >,
{
    type Round = Round;
    type Ordering = (Ordering, Ordering);
    #[inline]
    fn assign_round(&mut self, src: T, round: Round) -> (Ordering, Ordering) {
        src.assign_round_to(&mut (&mut self.0, &mut self.1), round)
    }
}

impl<'a, 'b, T> AssignRound<T> for (&'a mut Float, &'b mut Float)
where
    T: AssignRoundTo<Self, Round = Round, Ordering = (Ordering, Ordering)>,
{
    type Round = Round;
    type Ordering = (Ordering, Ordering);
    #[inline]
    fn assign_round(&mut self, src: T, round: Round) -> (Ordering, Ordering) {
        src.assign_round_to(self, round)
    }
}

impl AssignRoundTo<Float> for Constant {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round_to(self, dst: &mut Float, round: Round) -> Ordering {
        let ret = unsafe {
            match self {
                Constant::Log2 => {
                    mpfr::const_log2(dst.inner_mut(), rraw(round))
                }
                Constant::Pi => mpfr::const_pi(dst.inner_mut(), rraw(round)),
                Constant::Euler => {
                    mpfr::const_euler(dst.inner_mut(), rraw(round))
                }
                Constant::Catalan => {
                    mpfr::const_catalan(dst.inner_mut(), rraw(round))
                }
            }
        };
        ordering1(ret)
    }
}

assign_round_to!{ Constant => Float }

impl AssignRoundTo<Float> for Special {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round_to(self, dst: &mut Float, _round: Round) -> Ordering {
        unsafe {
            const EXP_MAX: c_long = ((!0 as c_ulong) >> 1) as c_long;
            const EXP_ZERO: c_long = 0 - EXP_MAX;
            const EXP_NAN: c_long = 1 - EXP_MAX;
            const EXP_INF: c_long = 2 - EXP_MAX;
            match self {
                Special::Zero => {
                    let ptr = dst.inner_mut();
                    (*ptr).sign = 1;
                    (*ptr).exp = EXP_ZERO;
                }
                Special::NegZero => {
                    let ptr = dst.inner_mut();
                    (*ptr).sign = -1;
                    (*ptr).exp = EXP_ZERO;
                }
                Special::Infinity => {
                    let ptr = dst.inner_mut();
                    (*ptr).sign = 1;
                    (*ptr).exp = EXP_INF;
                }
                Special::NegInfinity => {
                    let ptr = dst.inner_mut();
                    (*ptr).sign = -1;
                    (*ptr).exp = EXP_INF;
                }
                Special::Nan => {
                    let ptr = dst.inner_mut();
                    (*ptr).sign = 1;
                    (*ptr).exp = EXP_NAN;
                }
            };
        }
        Ordering::Equal
    }
}

assign_round_to!{ Special => Float }

macro_rules! assign {
    { $T:ty, $func:path } => {
        impl<'a> AssignRoundTo<Float> for &'a $T {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round_to(
                self,
                dst: &mut Float,
                round: Round
            ) -> Ordering {
                let ret = unsafe {
                    $func(dst.inner_mut(), self.inner(), rraw(round))
                };
                ordering1(ret)
            }
        }

        impl AssignRoundTo<Float> for $T {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round_to(self, dst: &mut Float, round: Round) -> Ordering
            {
                <&$T as AssignRoundTo<Float>>::assign_round_to(
                    &self,
                    dst,
                    round,
                )
            }
        }
    };
}

assign! { Float, mpfr::set }
#[cfg(feature = "integer")]
assign! { Integer, mpfr::set_z }
#[cfg(feature = "rational")]
assign! { Rational, mpfr::set_q }

macro_rules! conv_ops {
    { $T:ty, $set:path } => {
        impl AssignRoundTo<Float> for $T {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round_to(self, dst: &mut Float, round: Round) -> Ordering
            {
                let ret = unsafe {
                    $set(dst.inner_mut(), self.into(), rraw(round))
                };
                ordering1(ret)
            }
        }

        assign_round_to!{ $T => Float }
    }
}

conv_ops!{ i32, mpfr::set_si }
conv_ops!{ i64, xmpfr::set_i64 }
conv_ops!{ u32, mpfr::set_ui }
conv_ops!{ u64, xmpfr::set_u64 }
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
    big_float::append_to_string(
        &mut s,
        flt,
        radix,
        fmt.precision(),
        Round::Nearest,
        to_upper,
    );
    if !flt.is_finite() {
        return fmt.pad(&s);
    }
    let (neg, buf) = if s.starts_with('-') {
        (true, &s[1..])
    } else {
        (false, &s[..])
    };
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
