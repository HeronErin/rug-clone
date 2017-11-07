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

use {Assign, Complex, Float};
#[cfg(feature = "integer")]
use Integer;
#[cfg(feature = "rational")]
use Rational;
use big_complex::{Ordering2, Round2, ordering2, rraw2};
use complex::{OrdComplex, ParseComplexError};
use float::{Constant, Round, Special};
use gmp_mpfr_sys::mpc;
use inner::{Inner, InnerMut};
use ops::AssignRound;
#[allow(unused_imports)]
use std::ascii::AsciiExt;
use std::cmp::Ordering;
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerExp, LowerHex,
               Octal, UpperExp, UpperHex};
use std::i32;
use std::mem;
use std::ptr;

impl Clone for Complex {
    #[inline]
    fn clone(&self) -> Complex {
        let prec = self.prec();
        let mut ret = Complex::new(prec);
        ret.assign(self);
        ret
    }

    #[inline]
    fn clone_from(&mut self, source: &Complex) {
        self.assign(source);
    }
}

impl Default for Complex {
    #[inline]
    fn default() -> Complex {
        Complex::new(53)
    }
}

impl Drop for Complex {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            mpc::clear(self.inner_mut());
        }
    }
}

impl From<(Float, Float)> for Complex {
    /// Constructs a `Complex` number from a real
    /// [`Float`](struct.Float.html) and imaginary
    /// [`Float`](struct.Float.html).
    ///
    /// This constructor does not allocate, as it reuses the
    /// [`Float`](struct.Float.html) components.
    #[inline]
    fn from((real, imag): (Float, Float)) -> Complex {
        let mut dst: Complex = unsafe { mem::uninitialized() };
        unsafe {
            let real_imag = dst.as_mut_real_imag();
            ptr::copy_nonoverlapping(&real, real_imag.0, 1);
            ptr::copy_nonoverlapping(&imag, real_imag.1, 1);
        }
        mem::forget(real);
        mem::forget(imag);
        dst
    }
}

impl From<OrdComplex> for Complex {
    #[inline]
    fn from(ord: OrdComplex) -> Complex {
        unsafe { mem::transmute(ord) }
    }
}

impl Display for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl Debug for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", true)
    }
}

impl LowerExp for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl UpperExp for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, true, "", false)
    }
}

impl Binary for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b", false)
    }
}

impl Octal for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o", false)
    }
}

impl LowerHex for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x", false)
    }
}

impl UpperHex for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x", false)
    }
}

impl<T> Assign<T> for Complex
where
    Complex: AssignRound<T, Round = Round2, Ordering = Ordering2>,
{
    #[inline]
    fn assign(&mut self, other: T) {
        self.assign_round(other, Default::default());
    }
}

impl AssignRound<Complex> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, other: Complex, round: Round2) -> Ordering2 {
        self.assign_round(&other, round)
    }
}

impl<'a> AssignRound<&'a Complex> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, other: &Complex, round: Round2) -> Ordering2 {
        let ret =
            unsafe { mpc::set(self.inner_mut(), other.inner(), rraw2(round)) };
        ordering2(ret)
    }
}

macro_rules! assign_real {
    { $T:ty } => {
        impl<'a> AssignRound<&'a $T> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            #[inline]
            fn assign_round(
                &mut self,
                other: &'a $T,
                round: Round2,
            ) -> Ordering2 {
                let (real, imag) = self.as_mut_real_imag();
                let ord1 = real.assign_round(other, round.0);
                let ord2 = imag.assign_round(0, round.1);
                (ord1, ord2)
            }
        }

        impl AssignRound<$T> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            #[inline]
            fn assign_round(&mut self, other: $T, round: Round2) -> Ordering2 {
                let (real, imag) = self.as_mut_real_imag();
                let ord1 = real.assign_round(other, round.0);
                let ord2 = imag.assign_round(0, round.1);
                (ord1, ord2)
            }
        }
    };
}

#[cfg(feature = "integer")]
assign_real! { Integer }
#[cfg(feature = "rational")]
assign_real! { Rational }
assign_real! { Float }
assign_real! { Special }
assign_real! { Constant }
assign_real! { i32 }
assign_real! { i64 }
assign_real! { u32 }
assign_real! { u64 }
assign_real! { f32 }
assign_real! { f64 }

impl<T, U> AssignRound<(T, U)> for Complex
where
    Float: AssignRound<T, Round = Round, Ordering = Ordering>
        + AssignRound<U, Round = Round, Ordering = Ordering>,
{
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, rhs: (T, U), round: Round2) -> Ordering2 {
        let (real, imag) = self.as_mut_real_imag();
        let ord1 = real.assign_round(rhs.0, round.0);
        let ord2 = imag.assign_round(rhs.1, round.1);
        (ord1, ord2)
    }
}

impl<'a, T, U> AssignRound<&'a (T, U)> for Complex
where
    Float: AssignRound<&'a T, Round = Round, Ordering = Ordering>
        + AssignRound<&'a U, Round = Round, Ordering = Ordering>,
{
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, rhs: &'a (T, U), round: Round2) -> Ordering2 {
        let (real, imag) = self.as_mut_real_imag();
        let ord1 = real.assign_round(&rhs.0, round.0);
        let ord2 = imag.assign_round(&rhs.1, round.1);
        (ord1, ord2)
    }
}

fn fmt_radix(
    c: &Complex,
    fmt: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
    show_neg_zero: bool,
) -> fmt::Result {
    let (real, imag) = c.as_real_imag();
    let mut buf = String::from("(");
    fmt_float(&mut buf, real, fmt, radix, to_upper, prefix, show_neg_zero);
    buf.push(' ');
    fmt_float(&mut buf, imag, fmt, radix, to_upper, prefix, show_neg_zero);
    buf.push(')');
    let count = buf.chars().count();
    let padding = match fmt.width() {
        Some(width) if width > count => width - count,
        _ => return fmt.write_str(&buf),
    };
    let mut fill_buf = String::with_capacity(4);
    fill_buf.push(fmt.fill());
    for _ in 0..padding {
        fmt.write_str(&fill_buf)?;
    }
    fmt.write_str(&buf)
}

fn fmt_float(
    buf: &mut String,
    flt: &Float,
    fmt: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
    show_neg_zero: bool,
) {
    let show_neg_zero = show_neg_zero || fmt.sign_plus();
    let mut s = flt.to_string_radix(radix, fmt.precision());
    let minus = s.starts_with('-')
        || (show_neg_zero && flt.is_zero() && flt.is_sign_negative());
    if minus {
        buf.push('-');
    } else if fmt.sign_plus() {
        buf.push('+');
    }
    if fmt.alternate() {
        buf.push_str(prefix);
    }
    if to_upper && flt.is_finite() {
        s.make_ascii_uppercase();
    }
    buf.push_str(if s.starts_with('-') { &s[1..] } else { &s });
}

impl Display for ParseComplexError {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

unsafe impl Send for Complex {}
unsafe impl Sync for Complex {}
