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

use {Assign, Complex, Float};
use big_complex::{self, Ordering2, Round2, ordering2, raw_round2};
use complex::{OrdComplex, ParseComplexError};
use float::{Round, Special};
use gmp_mpfr_sys::mpc;
use inner::{Inner, InnerMut};
use misc;
use ops::{AssignRound, AssignRoundInto};
#[allow(unused_imports)]
use std::ascii::AsciiExt;
use std::cmp::Ordering;
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerExp, LowerHex,
               Octal, UpperExp, UpperHex};
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

impl<Re> From<Re> for Complex
where
    Float: From<Re>,
{
    #[inline]
    fn from(re: Re) -> Self {
        let real = Float::from(re);
        let imag = Float::new(real.prec());
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

impl<Re, Im> From<(Re, Im)> for Complex
where
    Float: From<Re> + From<Im>,
{
    #[inline]
    fn from((re, im): (Re, Im)) -> Self {
        let real = Float::from(re);
        let imag = Float::from(im);
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
    fn from(ord: OrdComplex) -> Self {
        unsafe { mem::transmute(ord) }
    }
}

impl Display for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Debug for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl LowerExp for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl UpperExp for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, true, "")
    }
}

impl Binary for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b")
    }
}

impl Octal for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o")
    }
}

impl LowerHex for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x")
    }
}

impl UpperHex for Complex {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x")
    }
}

impl<T> Assign<T> for Complex
where
    T: AssignRoundInto<Complex, Round = Round2, Ordering = Ordering2>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_round_into(self, Default::default());
    }
}

impl<T> AssignRound<T> for Complex
where
    T: AssignRoundInto<Complex, Round = Round2, Ordering = Ordering2>,
{
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: T, round: Round2) -> Ordering2 {
        src.assign_round_into(self, round)
    }
}

impl<T> Assign<T> for Result<Complex, Complex>
where
    for<'a> Result<&'a mut Complex, &'a mut Complex>: Assign<T>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        let ok = {
            let mut m = self.as_mut();
            m.assign(src);
            m.is_ok()
        };
        if self.is_ok() != ok {
            misc::result_swap(self);
        }
    }
}

impl<'a, 'b, T> Assign<T> for (&'a mut Complex, &'b mut Complex)
where
    T: AssignRoundInto<Self, Round = Round2, Ordering = (Ordering2, Ordering2)>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        src.assign_round_into(self, Default::default());
    }
}

impl<T> AssignRound<T> for (Complex, Complex)
where
    T: for<'a, 'b> AssignRoundInto<
        (&'a mut Complex, &'b mut Complex),
        Round = Round2,
        Ordering = (Ordering2, Ordering2),
    >,
{
    type Round = Round2;
    type Ordering = (Ordering2, Ordering2);
    #[inline]
    fn assign_round(
        &mut self,
        src: T,
        round: Round2,
    ) -> (Ordering2, Ordering2) {
        src.assign_round_into(&mut (&mut self.0, &mut self.1), round)
    }
}

impl<'a, 'b, T> AssignRound<T> for (&'a mut Complex, &'b mut Complex)
where
    T: AssignRoundInto<Self, Round = Round2, Ordering = (Ordering2, Ordering2)>,
{
    type Round = Round2;
    type Ordering = (Ordering2, Ordering2);
    #[inline]
    fn assign_round(
        &mut self,
        src: T,
        round: Round2,
    ) -> (Ordering2, Ordering2) {
        src.assign_round_into(self, round)
    }
}

impl AssignRoundInto<Complex> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round_into(self, dst: &mut Complex, round: Round2) -> Ordering2 {
        <&Complex as AssignRoundInto<Complex>>::assign_round_into(
            &self,
            dst,
            round,
        )
    }
}

impl<'a> AssignRoundInto<Complex> for &'a Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round_into(self, dst: &mut Complex, round: Round2) -> Ordering2 {
        let ret = unsafe {
            mpc::set(dst.inner_mut(), self.inner(), raw_round2(round))
        };
        ordering2(ret)
    }
}

impl<Re> AssignRoundInto<Complex> for Re
where
    Float: AssignRound<Re, Round = Round, Ordering = Ordering>,
{
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round_into(self, dst: &mut Complex, round: Round2) -> Ordering2 {
        let (real, imag) = dst.as_mut_real_imag();
        (
            <Float as AssignRound<Re>>::assign_round(real, self, round.0),
            <Float as AssignRound<Special>>::assign_round(
                imag,
                Special::Zero,
                round.1,
            ),
        )
    }
}

impl<Re, Im> AssignRoundInto<Complex> for (Re, Im)
where
    Float: AssignRound<Re, Round = Round, Ordering = Ordering>
        + AssignRound<Im, Round = Round, Ordering = Ordering>,
{
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round_into(self, dst: &mut Complex, round: Round2) -> Ordering2 {
        let (real, imag) = dst.as_mut_real_imag();
        (
            real.assign_round(self.0, round.0),
            imag.assign_round(self.1, round.1),
        )
    }
}

impl<'a, Re, Im> AssignRoundInto<Complex> for &'a (Re, Im)
where
    Float: AssignRound<&'a Re, Round = Round, Ordering = Ordering>
        + AssignRound<&'a Im, Round = Round, Ordering = Ordering>,
{
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round_into(self, dst: &mut Complex, round: Round2) -> Ordering2 {
        let (real, imag) = dst.as_mut_real_imag();
        (
            real.assign_round(&self.0, round.0),
            imag.assign_round(&self.1, round.1),
        )
    }
}

fn fmt_radix(
    c: &Complex,
    fmt: &mut Formatter,
    radix: i32,
    to_upper: bool,
    prefix: &str,
) -> fmt::Result {
    let mut s = String::new();
    big_complex::append_to_string(
        &mut s,
        c,
        radix,
        fmt.precision(),
        (Round::Nearest, Round::Nearest),
        (
            to_upper,
            fmt.sign_plus(),
            if fmt.alternate() { prefix } else { "" },
        ),
    );
    // s is ascii only, so just take len for character count
    let count = s.len();
    let padding = match fmt.width() {
        Some(width) if width > count => width - count,
        _ => return fmt.write_str(&s),
    };
    let mut fill_buf = String::with_capacity(4);
    fill_buf.push(fmt.fill());
    for _ in 0..padding {
        fmt.write_str(&fill_buf)?;
    }
    fmt.write_str(&s)
}

impl Display for ParseComplexError {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

unsafe impl Send for Complex {}
unsafe impl Sync for Complex {}
