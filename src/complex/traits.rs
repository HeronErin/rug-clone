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

use complex::big::{self, ordering2, raw_round2, Ordering2, Round2};
use complex::ParseComplexError;
use float::{Round, Special};
use gmp_mpfr_sys::mpc;
use inner::{Inner, InnerMut};
use ops::AssignRound;
#[allow(deprecated, unused_imports)]
use std::ascii::AsciiExt;
use std::cmp::Ordering;
use std::fmt::{
    self, Binary, Debug, Display, Formatter, LowerExp, LowerHex, Octal,
    UpperExp, UpperHex,
};
use std::mem;
use std::ptr;
use {Assign, Complex, Float};

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
        let mut dst: Complex = unsafe { mem::uninitialized() };
        unsafe {
            let (real, imag) = dst.as_mut_real_imag();
            ptr::write(real, Float::from(re));
            ptr::write(imag, Float::new(real.prec()));
        }
        dst
    }
}

impl<Re, Im> From<(Re, Im)> for Complex
where
    Float: From<Re> + From<Im>,
{
    #[inline]
    fn from((re, im): (Re, Im)) -> Self {
        let mut dst: Complex = unsafe { mem::uninitialized() };
        unsafe {
            let (real, imag) = dst.as_mut_real_imag();
            ptr::write(real, Float::from(re));
            ptr::write(imag, Float::from(im));
        }
        dst
    }
}

impl Display for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl Debug for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl LowerExp for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "")
    }
}

impl UpperExp for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, true, "")
    }
}

impl Binary for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b")
    }
}

impl Octal for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o")
    }
}

impl LowerHex for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x")
    }
}

impl UpperHex for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x")
    }
}

impl<T> Assign<T> for Complex
where
    Self: AssignRound<T, Round = Round2, Ordering = Ordering2>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        self.assign_round(src, Default::default());
    }
}

impl AssignRound for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: Complex, round: Round2) -> Ordering2 {
        let (dst_real, dst_imag) = self.as_mut_real_imag();
        let (src_real, src_imag) = src.into_real_imag();
        let real_ord = if dst_real.prec() == src_real.prec() {
            mem::drop(mem::replace(dst_real, src_real));
            Ordering::Equal
        } else {
            dst_real.assign_round(src_real, round.0)
        };
        let imag_ord = if dst_imag.prec() == src_imag.prec() {
            mem::drop(mem::replace(dst_imag, src_imag));
            Ordering::Equal
        } else {
            dst_imag.assign_round(src_imag, round.1)
        };
        (real_ord, imag_ord)
    }
}

impl<'a> AssignRound<&'a Complex> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: &Complex, round: Round2) -> Ordering2 {
        let ret = unsafe {
            mpc::set(self.inner_mut(), src.inner(), raw_round2(round))
        };
        ordering2(ret)
    }
}

impl<Re> AssignRound<Re> for Complex
where
    Float: AssignRound<Re, Round = Round, Ordering = Ordering>,
{
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: Re, round: Round2) -> Ordering2 {
        let real_ord = self.mut_real().assign_round(src, round.0);
        <Float as Assign<Special>>::assign(self.mut_imag(), Special::Zero);
        (real_ord, Ordering::Equal)
    }
}

impl<Re, Im> AssignRound<(Re, Im)> for Complex
where
    Float: AssignRound<Re, Round = Round, Ordering = Ordering>
        + AssignRound<Im, Round = Round, Ordering = Ordering>,
{
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: (Re, Im), round: Round2) -> Ordering2 {
        let real_ord = self.mut_real().assign_round(src.0, round.0);
        let imag_ord = self.mut_imag().assign_round(src.1, round.1);
        (real_ord, imag_ord)
    }
}

impl<'a, Re, Im> AssignRound<&'a (Re, Im)> for Complex
where
    Float: AssignRound<&'a Re, Round = Round, Ordering = Ordering>
        + AssignRound<&'a Im, Round = Round, Ordering = Ordering>,
{
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: &'a (Re, Im), round: Round2) -> Ordering2 {
        let real_ord = self.mut_real().assign_round(&src.0, round.0);
        let imag_ord = self.mut_imag().assign_round(&src.1, round.1);
        (real_ord, imag_ord)
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
    big::append_to_string(
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
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

unsafe impl Send for Complex {}
unsafe impl Sync for Complex {}
