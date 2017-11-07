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
use big_float::{make_string, rraw, ordering1};
use ext::mpfr as xmpfr;
use float::{Constant, OrdFloat, ParseFloatError, Round, Special};
use gmp_mpfr_sys::mpfr;
use inner::{Inner, InnerMut};
use ops::AssignRound;
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
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl Debug for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", true)
    }
}

impl LowerExp for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl UpperExp for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, true, "", false)
    }
}

impl Binary for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b", false)
    }
}

impl Octal for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o", false)
    }
}

impl LowerHex for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x", false)
    }
}

impl UpperHex for Float {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x", false)
    }
}

impl<T> Assign<T> for Float
where
    Float: AssignRound<T, Round = Round, Ordering = Ordering>,
{
    #[inline]
    fn assign(&mut self, rhs: T) {
        self.assign_round(rhs, Round::Nearest);
    }
}

impl AssignRound<Constant> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, rhs: Constant, round: Round) -> Ordering {
        let ret = unsafe {
            match rhs {
                Constant::Log2 => {
                    mpfr::const_log2(self.inner_mut(), rraw(round))
                }
                Constant::Pi => mpfr::const_pi(self.inner_mut(), rraw(round)),
                Constant::Euler => {
                    mpfr::const_euler(self.inner_mut(), rraw(round))
                }
                Constant::Catalan => {
                    mpfr::const_catalan(self.inner_mut(), rraw(round))
                }
            }
        };
        ordering1(ret)
    }
}

impl AssignRound<Special> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, rhs: Special, _round: Round) -> Ordering {
        unsafe {
            const EXP_MAX: c_long = ((!0 as c_ulong) >> 1) as c_long;
            const EXP_ZERO: c_long = 0 - EXP_MAX;
            const EXP_INF: c_long = 2 - EXP_MAX;
            match rhs {
                Special::Zero => {
                    let ptr = self.inner_mut();
                    (*ptr).sign = 1;
                    (*ptr).exp = EXP_ZERO;
                }
                Special::NegZero => {
                    let ptr = self.inner_mut();
                    (*ptr).sign = -1;
                    (*ptr).exp = EXP_ZERO;
                }
                Special::Infinity => {
                    let ptr = self.inner_mut();
                    (*ptr).sign = 1;
                    (*ptr).exp = EXP_INF;
                }
                Special::NegInfinity => {
                    let ptr = self.inner_mut();
                    (*ptr).sign = -1;
                    (*ptr).exp = EXP_INF;
                }
                Special::Nan => mpfr::set_nan(self.inner_mut()),
            };
        }
        Ordering::Equal
    }
}

assign_round_ref!{ Float: Constant }
assign_round_ref!{ Float: Special }

macro_rules! assign {
    { $T:ty, $func:path } => {
        impl<'a> AssignRound<&'a $T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round(
                &mut self,
                rhs: &'a $T,
                round: Round
            ) -> Ordering {
                let ret = unsafe {
                    $func(self.inner_mut(), rhs.inner(), rraw(round))
                };
                ordering1(ret)
            }
        }

        impl AssignRound<$T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round(&mut self, rhs: $T, round: Round) -> Ordering {
                self.assign_round(&rhs, round)
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
        impl AssignRound<$T> for Float {
            type Round = Round;
            type Ordering = Ordering;
            #[inline]
            fn assign_round(&mut self, val: $T, round: Round) -> Ordering {
                let ret = unsafe {
                    $set(self.inner_mut(), val.into(), rraw(round))
                };
                ordering1(ret)
            }
        }

        assign_round_ref!{ Float: $T }
    }
}

conv_ops! { i32, mpfr::set_si }

impl AssignRound<i64> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, rhs: i64, round: Round) -> Ordering {
        let ret = unsafe { xmpfr::set_i64(self.inner_mut(), rhs, rraw(round)) };
        ordering1(ret)
    }
}

assign_round_ref! { Float: i64 }

conv_ops! { u32, mpfr::set_ui }

impl AssignRound<u64> for Float {
    type Round = Round;
    type Ordering = Ordering;
    #[inline]
    fn assign_round(&mut self, rhs: u64, round: Round) -> Ordering {
        let ret = unsafe { xmpfr::set_u64(self.inner_mut(), rhs, rraw(round)) };
        ordering1(ret)
    }
}

assign_round_ref! { Float: u64 }
conv_ops! { f32, xmpfr::set_f32 }
conv_ops! { f64, mpfr::set_d }

fn fmt_radix(
    flt: &Float,
    f: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
    show_neg_zero: bool,
) -> fmt::Result {
    let s = make_string(flt, radix, f.precision(), Round::Nearest, to_upper);
    if !flt.is_finite() {
        return f.pad(&s);
    }
    let (neg, buf) = if s.starts_with('-') {
        (true, &s[1..])
    } else {
        (
            show_neg_zero && flt.is_zero() && flt.is_sign_negative(),
            &s[..],
        )
    };
    f.pad_integral(!neg, prefix, buf)
}

impl Display for ParseFloatError {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

unsafe impl Send for Float {}
unsafe impl Sync for Float {}
