// Copyright © 2017 University of Malta

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

use gmp_mpfr_sys::gmp;
use gmp_mpfr_sys::mpc;
use gmp_mpfr_sys::mpfr;
#[cfg(feature = "random")]
use rand::Rng;
use rugflo::{self, AddRound, AssignRound, Constant, DivRound, Float,
             FromRound, MulRound, PowRound, Round, ShlRound, ShrRound,
             Special, SubRound};
use rugint::{Assign, DivFromAssign, Integer, NegAssign, Pow, PowAssign,
             PowFromAssign, SubFromAssign};
use rugrat::Rational;
use std::ascii::AsciiExt;
use std::cmp::Ordering;
use std::error::Error;
use std::fmt::{self, Binary, Debug, Display, Formatter, LowerExp, LowerHex,
               Octal, UpperExp, UpperHex};
use std::i32;
use std::mem;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl,
               ShlAssign, Shr, ShrAssign, Sub, SubAssign};
use std::os::raw::{c_int, c_long, c_ulong};
use std::ptr;

type Round2 = (Round, Round);
const NEAREST: Round2 = (Round::Nearest, Round::Nearest);

type Ordering2 = (Ordering, Ordering);

/// A multi-precision complex number.
/// The precision has to be set during construction.
///
/// There are two versions of most methods:
///
/// 1. The first rounds the returned or stored `Complex` number to the
///    [nearest](enum.Round.html#variant.Nearest) representable value.
/// 2. The second applies the specified [rounding
///    methods](../rugflo/enum.Round.html) for the real and imaginary parts, and
///    returns the rounding directions for both:
///    * `Ordering::Less` if the returned/stored part is less than
///      the exact result,
///    * `Ordering::Equal` if the returned/stored part is equal to
///      the exact result,
///    * `Ordering::Greater` if the returned/stored part is greater
///      than the exact result,
///
/// # Note on `Round::AwayFromZero`
///
/// For `Complex` numbers, `Round::AwayFromZero` is not implemented,
/// and trying to use it will start a panic.

pub struct Complex {
    inner: mpc::mpc_t,
}

impl Drop for Complex {
    fn drop(&mut self) {
        unsafe {
            mpc::clear(self.inner_mut());
        }
    }
}

impl Clone for Complex {
    fn clone(&self) -> Complex {
        let prec = self.prec();
        let mut ret = Complex::new(prec);
        ret.assign(self);
        ret
    }

    fn clone_from(&mut self, source: &Complex) {
        self.assign(source);
    }
}

impl Complex {
    /// Create a new complex number with the specified precisions for
    /// the real and imaginary parts and with value 0.
    ///
    /// # Panics
    ///
    /// Panics if `prec.0` or `prec.1` is out of the allowed range.
    pub fn new(prec: (u32, u32)) -> Complex {
        assert!(prec.0 >= rugflo::prec_min() && prec.0 <= rugflo::prec_max() &&
                prec.1 >= rugflo::prec_min() &&
                prec.1 <= rugflo::prec_max(),
                "precision out of range");
        unsafe {
            let mut inner: mpc::mpc_t = mem::uninitialized();
            mpc::init3(&mut inner,
                       prec.0 as mpfr::prec_t,
                       prec.1 as mpfr::prec_t);
            let real = mpc::realref(&mut inner);
            let imag = mpc::imagref(&mut inner);
            mpfr::set_zero(real, 0);
            mpfr::set_zero(imag, 0);
            Complex { inner: inner }
        }
    }

    /// Returns the precision of the real and imaginary parts.
    pub fn prec(&self) -> (u32, u32) {
        (self.real().prec(), self.imag().prec())
    }

    /// Sets the precision of the real and imaginary parts exactly,
    /// rounding to the nearest.
    ///
    /// # Panics
    ///
    /// Panics if `prec.0` or `prec.1` is out of the allowed range.
    pub fn set_prec(&mut self, prec: (u32, u32)) {
        let (real, imag) = self.as_mut_real_imag();
        real.set_prec(prec.0);
        imag.set_prec(prec.1);
    }

    /// Sets the precision of the real and imaginary parts exactly,
    /// applying the specified rounding method.
    ///
    /// # Panics
    ///
    /// Panics if `prec.0` or `prec.1` is out of the allowed range.
    pub fn set_prec_round(&mut self,
                          prec: (u32, u32),
                          round: Round2)
                          -> Ordering2 {
        let (real, imag) = self.as_mut_real_imag();
        (real.set_prec_round(prec.0, round.0),
         imag.set_prec_round(prec.1, round.1))
    }

    /// Borrows the real part.
    pub fn real(&self) -> &Float {
        unsafe {
            let ptr = mpc::realref(self.inner() as *const _ as *mut _);
            &*(ptr as *const Float)
        }
    }

    /// Borrows the imaginary part.
    pub fn imag(&self) -> &Float {
        unsafe {
            let ptr = mpc::imagref(self.inner() as *const _ as *mut _);
            &*(ptr as *const Float)
        }
    }

    /// Borrows the real part mutably.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rugint;
    /// extern crate rugcom;
    /// use rugint::Assign;
    /// use rugcom::Complex;
    ///
    /// fn main() {
    ///     let mut c = Complex::from(((1, 2), (53, 53)));
    ///     assert!(c == (1, 2));
    ///     c.mut_real().assign(12.5);
    ///     *c.mut_imag() += 12;
    ///     assert!(c == (12.5, 14));
    /// }
    /// ```
    pub fn mut_real(&mut self) -> &mut Float {
        unsafe {
            let ptr = mpc::realref(self.inner_mut());
            &mut *(ptr as *mut Float)
        }
    }

    /// Borrows the imaginary part mutably.
    ///
    /// See the example for [`mut_real()`](#method.mut_real).
    pub fn mut_imag(&mut self) -> &mut Float {
        unsafe {
            let ptr = mpc::imagref(self.inner_mut());
            &mut *(ptr as *mut Float)
        }
    }

    /// Borrows the real and imaginary parts.
    pub fn as_real_imag(&self) -> (&Float, &Float) {
        (self.real(), self.imag())
    }

    /// Borrows the real and imaginary parts mutably.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugcom::Complex;
    ///
    /// let mut c = Complex::from(((1, 2), (53, 53)));
    /// {
    ///     let mut real_imag = c.as_mut_real_imag();
    ///     *real_imag.0 += 3;
    ///     *real_imag.1 += 4;
    ///     // borrow ends here
    /// }
    /// let (real, imag) = c.as_real_imag();
    /// assert!(*real == 4 && *imag == 6);
    /// ```
    pub fn as_mut_real_imag(&mut self) -> (&mut Float, &mut Float) {
        unsafe {
            let real_ptr = mpc::realref(self.inner_mut());
            let imag_ptr = mpc::imagref(self.inner_mut());
            (&mut *(real_ptr as *mut Float), &mut *(imag_ptr as *mut Float))
        }
    }

    /// Converts `self` into real and imaginary `Float` values,
    /// consuming `self`.
    pub fn into_real_imag(mut self) -> (Float, Float) {
        let (mut real, mut imag) = unsafe { mem::uninitialized() };
        unsafe {
            let real_imag = self.as_mut_real_imag();
            ptr::copy_nonoverlapping(real_imag.0, &mut real, 1);
            ptr::copy_nonoverlapping(real_imag.1, &mut imag, 1);
        }
        mem::forget(self);
        (real, imag)
    }
}

macro_rules! math_op1 {
    {
        $(#[$attr:meta])* fn $method:ident;
        $(#[$attr_round:meta])* fn $method_round:ident;
        $(#[$attr_hold:meta])* fn $method_hold:ident -> $Hold:ident;
        $func:path $(, $param:ident: $T:ty)*
    } => {
        impl Complex {
            $(#[$attr])*
            pub fn $method(&mut self $(, $param: $T)*) -> &mut Complex {
                self.$method_round($($param,)* NEAREST);
                self
            }

            $(#[$attr_round])*
            pub fn $method_round(&mut self, $($param: $T,)* round: Round2)
                                 -> Ordering2 {
                ordering2(unsafe {
                    $func(self.inner_mut(),
                          self.inner(),
                          $($param.into(),)* rraw2(round))
                })
            }

            $(#[$attr_hold])*
            pub fn $method_hold<'a>(&'a self $(, $param: $T)*) -> $Hold<'a> {
                $Hold {
                    val: self,
                    $($param: $param,)*
                }
            }
        }

        $(#[$attr_hold])*
        pub struct $Hold<'a> {
            val: &'a Complex,
            $($param: $T,)*
        }

        impl<'a> AssignRound<$Hold<'a>> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;

            fn assign_round(&mut self, src: $Hold<'a>, round: Round2)
                            -> Ordering2 {
                ordering2(unsafe {
                    $func(self.inner_mut(),
                          src.val.inner(),
                          $(src.$param.into(),)* rraw2(round))
                })
            }
        }
    };
}

math_op1! {
    /// Computes a projection onto the Riemann sphere, rounding to the
    /// nearest.
    fn proj;
    /// Computes a projection onto the Riemann sphere, applying the
    /// specified rounding method.
    fn proj_round;
    /// Holds a computation of the projection onto the Riemann sphere.
    fn proj_hold -> ProjHold;
    mpc::proj
}
math_op1! {
    /// Computes the square, rounding to the nearest.
    fn square;
    /// Computes the square, applying the specified rounding method.
    fn square_round;
    /// Holds the computation of the square.
    fn square_hold -> SquareHold;
    mpc::sqr
}
math_op1! {
    /// Computes the square root, rounding to the nearest.
    fn sqrt;
    /// Computes the square root, applying the specified rounding
    /// method.
    fn sqrt_round;
    /// Holds the computation of the square root.
    fn sqrt_hold -> SqrtHold;
    mpc::sqrt
}
math_op1! {
    /// Computes the complex conjugate, rounding to the nearest.
    fn conjugate;
    /// Computes the complex conjugate, applying the specified
    /// rounding method.
    fn conjugate_round;
    /// Holds the computation of the complex conjugate.
    fn conjugate_hold -> ConjugateHold;
    mpc::conj
}

impl Complex {
    /// Holds the computation of the absolute value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rugflo;
    /// extern crate rugcom;
    /// use rugflo::{Float, Special};
    /// use rugcom::Complex;
    ///
    /// fn main() {
    ///     let c1 = Complex::from(((30, 40), (53, 53)));
    ///     assert!(Float::from((c1.abs_hold(), 53)) == 50);
    ///     let c2 = Complex::from(((12, Special::Infinity), (53, 53)));
    ///     assert!(Float::from((c2.abs_hold(), 53)).is_infinite());
    /// }
    /// ```
    pub fn abs_hold<'a>(&'a self) -> AbsHold<'a> {
        AbsHold { val: self }
    }
}

/// Holds the computation of the absolute value.
pub struct AbsHold<'a> {
    val: &'a Complex,
}

impl<'a> AssignRound<AbsHold<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, src: AbsHold<'a>, round: Round) -> Ordering {
        unsafe { mpc::abs(self.inner_mut(), src.val.inner(), rraw(round)) }
            .cmp(&0)
    }
}

impl Complex {
    /// Computes the argument, rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// extern crate rugint;
    /// extern crate rugflo;
    /// extern crate rugcom;
    /// use rugint::Assign;
    /// use rugflo::{Float, Special};
    /// use rugcom::Complex;
    /// use std::f64;
    ///
    /// fn main() {
    ///     // f has precision 53, just like f64, so PI constants match.
    ///     let mut arg = Float::new(53);
    ///     let c_pos = Complex::from((1, (53, 53)));
    ///     arg.assign(c_pos.arg_hold());
    ///     assert!(arg.is_zero());
    ///     let c_neg = Complex::from((-1.3, (53, 53)));
    ///     arg.assign(c_neg.arg_hold());
    ///     assert!(arg == f64::consts::PI);
    ///     let c_pi_4 = Complex::from(((1.333, 1.333), (53, 53)));
    ///     arg.assign(c_pi_4.arg_hold());
    ///     assert!(arg == f64::consts::FRAC_PI_4);

    ///     // Special values are handled like atan2 in IEEE 754-2008.
    ///     // Examples for real, imag set to plus, minus zero below:
    ///     let mut zero = Complex::new((53, 53));
    ///     zero.assign((Special::Zero, Special::Zero));
    ///     arg.assign(zero.arg_hold());
    ///     assert!(arg.is_zero() && !arg.get_sign());
    ///     zero.assign((Special::Zero, Special::MinusZero));
    ///     arg.assign(zero.arg_hold());
    ///     assert!(arg.is_zero() && arg.get_sign());
    ///     zero.assign((Special::MinusZero, Special::Zero));
    ///     arg.assign(zero.arg_hold());
    ///     assert!(arg == f64::consts::PI);
    ///     zero.assign((Special::MinusZero, Special::MinusZero));
    ///     arg.assign(zero.arg_hold());
    ///     assert!(arg == -f64::consts::PI);
    /// }
    /// ```
    pub fn arg_hold<'a>(&'a self) -> ArgHold<'a> {
        ArgHold { val: self }
    }
}

/// Holds the computation of the argument.
pub struct ArgHold<'a> {
    val: &'a Complex,
}

impl<'a> AssignRound<ArgHold<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, src: ArgHold<'a>, round: Round) -> Ordering {
        unsafe { mpc::arg(self.inner_mut(), src.val.inner(), rraw(round)) }
            .cmp(&0)
    }
}

math_op1! {
    /// Multiplies the complex number by *i*, rounding to the nearest.
    fn mul_i;
    /// Multiplies the complex number by *i*, applying the specified
    /// rounding method.
    fn mul_i_round;
    /// Holds the multiplicateion of the complex number by *i*.
    fn mul_i_hold -> MulIHold;
    mul_i,
    negative: bool
}
unsafe fn mul_i(rop: *mut mpc::mpc_t,
                op: *const mpc::mpc_t,
                neg: bool,
                rnd: mpc::rnd_t)
                -> c_int {
    mpc::mul_i(rop, op, if neg { -1 } else { 0 }, rnd)
}

math_op1! {
    /// Computes the reciprocal, rounding to the nearest.
    fn recip;
    /// Computes the reciprocal, applying the specified rounding
    /// method.
    fn recip_round;
    /// Holds the computation of the reciprocal.
    fn recip_hold -> RecipHold;
    recip
}
unsafe fn recip(rop: *mut mpc::mpc_t,
                op: *const mpc::mpc_t,
                rnd: mpc::rnd_t)
                -> c_int {
    mpc::ui_div(rop, 1, op, rnd)
}

impl Complex {
    /// Computes the norm, that is the square of the absolute value,
    /// rounding to the nearest.
    pub fn norm_hold<'a>(&'a self) -> NormHold<'a> {
        NormHold { val: self }
    }
}

/// Holds the computation of the norm.
pub struct NormHold<'a> {
    val: &'a Complex,
}

impl<'a> AssignRound<NormHold<'a>> for Float {
    type Round = Round;
    type Ordering = Ordering;
    fn assign_round(&mut self, src: NormHold<'a>, round: Round) -> Ordering {
        unsafe { mpc::norm(self.inner_mut(), src.val.inner(), rraw(round)) }
            .cmp(&0)
    }
}

math_op1! {
    /// Computes the natural logarithm, rounding to the nearest.
    fn ln;
    /// Computes the natural logarithm, applying the specified
    /// rounding method.
    fn ln_round;
    /// Holds the computation of the natural logarithm;
    fn ln_hold -> LnHold;
    mpc::log
}
math_op1! {
    /// Computes the logarithm to base 10, rounding to the nearest.
    fn log10;
    /// Computes the logarithm to base 10, applying the specified
    /// rounding method.
    fn log10_round;
    /// Holds the compuration of the logarithm to base 10.
    fn log10_hold -> Log10Hold;
    mpc::log10
}
math_op1! {
    /// Computes the exponential, rounding to the nearest.
    fn exp;
    /// Computes the exponential, applying the specified rounding
    /// method.
    fn exp_round;
    /// Holds the computation of the exponential.
    fn exp_hold -> ExpHold;
    mpc::exp
}
math_op1! {
    /// Computes the sine, rounding to the nearest.
    fn sin;
    /// Computes the sine, applying the specified rounding method.
    fn sin_round;
    /// Holds the computation of the sine.
    fn sin_hold -> SinHold;
    mpc::sin
}
math_op1! {
    /// Computes the cosine, rounding to the nearest.
    fn cos;
    /// Computes the cosine, applying the specified rounding method.
    fn cos_round;
    /// Holds the computation of the cosine.
    fn cos_hold -> CosHold;
    mpc::cos
}

impl Complex {
    /// Computes the sine and cosine of `self`, rounding to the
    /// nearest. The sine is stored in `self` and keeps its precision,
    /// while the cosine is stored in `cos` keeping its precision.
    pub fn sin_cos(&mut self, cos: &mut Complex) {
        self.sin_cos_round(cos, NEAREST);
    }

    /// Computes the sine and cosine of `self`, applying the specified
    /// rounding methods. The sine is stored in `self` and keeps its
    /// precision, while the cosine is stored in `buf` keeping its
    /// precision.
    pub fn sin_cos_round(&mut self,
                         cos: &mut Complex,
                         round: Round2)
                         -> (Ordering2, Ordering2) {
        let ord = unsafe {
            mpc::sin_cos(self.inner_mut(),
                         cos.inner_mut(),
                         self.inner(),
                         rraw2(round),
                         rraw2(round))
        };
        (ordering2(mpc::INEX1(ord)), ordering2(mpc::INEX2(ord)))
    }

    /// Computes the cosine and sine of `self`, rounding to the
    /// nearest. The cosine is stored in `self` and keeps its
    /// precision, while the sine is stored in `sin` keeping its
    /// precision.
    pub fn cos_sin(&mut self, sin: &mut Complex) {
        self.cos_sin_round(sin, NEAREST);
    }

    /// Computes the cosine and sine of `self`, applying the specified
    /// rounding methods. The cosine is stored in `self` and keeps its
    /// precision, while the sine is stored in `sin` keeping its
    /// precision.
    pub fn cos_sin_round(&mut self,
                         sin: &mut Complex,
                         round: Round2)
                         -> (Ordering2, Ordering2) {
        let ord = unsafe {
            mpc::sin_cos(sin.inner_mut(),
                         self.inner_mut(),
                         self.inner(),
                         rraw2(round),
                         rraw2(round))
        };
        (ordering2(mpc::INEX2(ord)), ordering2(mpc::INEX1(ord)))
    }

    /// Computes the sine and cosine of `val`, rounding to the
    /// nearest. The sine is stored in `self` and keeps its precision,
    /// while the cosine is stored in `cos` keeping its precision.
    pub fn assign_sin_cos(&mut self, cos: &mut Complex, val: &Complex) {
        self.assign_sin_cos_round(cos, val, NEAREST);
    }

    /// Computes the sine and cosine of `val`, applying the specified
    /// rounding method. The sine is stored in `self` and keeps its
    /// precision, while the cosine is stored in `cos` keeping its
    /// precision.
    pub fn assign_sin_cos_round(&mut self,
                                cos: &mut Complex,
                                val: &Complex,
                                round: Round2)
                                -> (Ordering2, Ordering2) {
        let ord = unsafe {
            mpc::sin_cos(self.inner_mut(),
                         cos.inner_mut(),
                         val.inner(),
                         rraw2(round),
                         rraw2(round))
        };
        (ordering2(mpc::INEX1(ord)), ordering2(mpc::INEX2(ord)))
    }
}

math_op1! {
    /// Computes the tangent, rounding to the nearest.
    fn tan;
    /// Computes the tangent, applying the specified rounding method.
    fn tan_round;
    /// Holds the computation of the tangent.
    fn tan_hold -> TanHold;
    mpc::tan
}
math_op1! {
    /// Computes the hyperbolic sine, rounding to the nearest.
    fn sinh;
    /// Computes the hyperbolic sine, applying the specified rounding
    /// method.
    fn sinh_round;
    /// Holds the computation of the hyperbolic sine.
    fn sinh_hold -> SinhHold;
    mpc::sinh
}
math_op1! {
    /// Computes the hyperbolic cosine, rounding to the nearest.
    fn cosh;
    /// Computes the hyperbolic cosine, applying the specified rounding
    /// method.
    fn cosh_round;
    /// Holds the computation of the hyperbolic cosine.
    fn cosh_hold -> CoshHold;
    mpc::cosh
}
math_op1! {
    /// Computes the hyperbolic tangent, rounding to the nearest.
    fn tanh;
    /// Computes the hyperbolic tangent, applying the specified
    /// rounding method.
    fn tanh_round;
    /// Holds the computation of the hyperbolic tangent.
    fn tanh_hold -> TanhHold;
    mpc::tanh
}
math_op1! {
    /// Computes the inverse sine, rounding to the nearest.
    fn asin;
    /// Computes the inverse sine, applying the specified rounding
    /// method.
    fn asin_round;
    /// Holds the computation of the inverse sine.
    fn asin_hold -> AsinHold;
    mpc::asin
}
math_op1! {
    /// Computes the inverse cosine, rounding to the nearest.
    fn acos;
    /// Computes the inverse cosine, applying the specified rounding
    /// method.
    fn acos_round;
    /// Holds the computation of the inverse cosine.
    fn acos_hold -> AcosHold;
    mpc::acos
}
math_op1! {
    /// Computes the inverse tangent, rounding to the nearest.
    fn atan;
    /// Computes the inverse tangent, applying the specified rounding
    /// method.
    fn atan_round;
    /// Holds the computation of the inverse tangent.
    fn atan_hold -> AtanHold;
    mpc::atan
}
math_op1! {
    /// Computes the inverse hyperbolic sine, rounding to the nearest.
    fn asinh;
    /// Computes the inverse hyperbolic sine, applying the specified
    /// rounding method.
    fn asinh_round;
    /// Holds the computation of the inverse hyperboic sine.
    fn asinh_hold -> AsinhHold;
    mpc::asinh
}
math_op1! {
    /// Computes the inverse hyperbolic cosine, rounding to the
    /// nearest.
    fn acosh;
    /// Computes the inverse hyperbolic cosine, applying the specified
    /// rounding method.
    fn acosh_round;
    /// Holds the computation of the inverse hyperbolic cosine.
    fn acosh_hold -> AcoshHold;
    mpc::acosh
}
math_op1! {
    /// Computes the inverse hyperbolic tangent, rounding to the
    /// nearest.
    fn atanh;
    /// Computes the inverse hyperbolic tangent, applying the
    /// specified rounding method.
    fn atanh_round;
    /// Holds the computation of the inverse hyperbolic tangent.
    fn atanh_hold -> AtanhHold;
    mpc::atanh
}

impl Complex {
    #[cfg(feature = "random")]
    /// Generates a random complex number with both the real and
    /// imaginary parts in the range `0 <= n < 1`.
    ///
    /// This is equivalent to calling
    /// [`assign_random_bits_round(rng, (Round::Nearest, Round::Nearest))`]
    /// (#method.assign_random_bits_round).
    pub fn assign_random_bits<R: Rng>(&mut self, rng: &mut R) {
        self.assign_random_bits_round(rng, NEAREST);
    }

    #[cfg(feature = "random")]
    /// Generates a random complex number with both the real and
    /// imaginary parts in the range `0 <= n < 1`.
    ///
    /// This is equivalent to calling
    /// [`assign_random_bits_round(rng, round.0)`]
    /// (../rugflo/struct.Float.html#method.assign_random_bits_round)
    /// on the real part, and the same with `round.1` on the
    /// imaginary part.
    pub fn assign_random_bits_round<R: Rng>(&mut self,
                                            rng: &mut R,
                                            round: Round2)
                                            -> Ordering2 {
        let (real, imag) = self.as_mut_real_imag();
        (real.assign_random_bits_round(rng, round.0),
         imag.assign_random_bits_round(rng, round.1))
    }

    #[cfg(feature = "random")]
    /// Generates a random complex number, rounding to the nearest.
    ///
    /// Both the real and imaginary parts are in the continuous range
    /// `0 <= n < 1`. After rounding, the value may be equal to one.
    /// Calling this method is equivalent to calling
    /// [`assign_random_cont_round(rng, (Round::Nearest, Round::Nearest))`]
    /// (#method.assign_random_cont_round).
    pub fn assign_random_cont<R: Rng>(&mut self, rng: &mut R) {
        self.assign_random_cont_round(rng, NEAREST);
    }

    #[cfg(feature = "random")]
    /// Generates a random complex number, applying the specified
    /// rounding method.
    ///
    /// Both the real and imaginary parts are in the continuous range
    /// `0 <= n < 1`. After rounding, the value may be equal to one.
    /// Calling this method is equivalent to calling
    /// [`assign_random_cont_round(rng, round.0)`]
    /// (../rugflo/struct.Float.html#method.assign_random_bits_round)
    /// on the real part, and the same with `round.1` on the
    /// imaginary part.
    pub fn assign_random_cont_round<R: Rng>(&mut self,
                                            rng: &mut R,
                                            round: Round2)
                                            -> Ordering2 {
        let (real, imag) = self.as_mut_real_imag();
        (real.assign_random_cont_round(rng, round.0),
         imag.assign_random_cont_round(rng, round.1))
    }

    /// Returns a string representation of `self` for the specified
    /// `radix` rounding to the nearest.
    ///
    /// The exponent is encoded in decimal. The output string will have
    /// enough precision such that reading it again will give the exact
    /// same number.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn to_string_radix(&self,
                           radix: i32,
                           num_digits: Option<usize>)
                           -> String {
        self.to_string_radix_round(radix, num_digits, NEAREST)
    }

    /// Returns a string representation of `self` for the specified
    /// `radix` applying the specified rounding method.
    ///
    /// The exponent is encoded in decimal. The output string will have
    /// enough precision such that reading it again will give the exact
    /// same number.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn to_string_radix_round(&self,
                                 radix: i32,
                                 num_digits: Option<usize>,
                                 round: Round2)
                                 -> String {
        let mut buf = String::from("(");
        buf += &self.real()
                    .to_string_radix_round(radix, num_digits, round.0);
        buf.push(' ');
        buf += &self.imag()
                    .to_string_radix_round(radix, num_digits, round.0);
        buf.push(')');
        buf
    }

    /// Parses a `Complex` number with the specified precision,
    /// rounding to the nearest.
    ///
    /// See the [corresponding assignment](#method.assign_str).
    pub fn from_str(src: &str,
                    prec: (u32, u32))
                    -> Result<Complex, ParseComplexError> {
        let mut val = Complex::new(prec);
        val.assign_str(src)?;
        Ok(val)
    }

    /// Parses a `Complex` number with the specified radix and
    /// precision, rounding to the nearest.
    ///
    /// See the [corresponding assignment](#method.assign_str_radix).
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn from_str_radix(src: &str,
                          radix: i32,
                          prec: (u32, u32))
                          -> Result<Complex, ParseComplexError> {
        let mut val = Complex::new(prec);
        val.assign_str_radix(src, radix)?;
        Ok(val)
    }

    /// Parses a `Complex` number with the specified precision,
    /// applying the specified rounding.
    ///
    /// See the [corresponding assignment](#method.assign_str_round).
    pub fn from_str_round
        (src: &str,
         prec: (u32, u32),
         round: Round2)
         -> Result<(Complex, Ordering2), ParseComplexError> {
        let mut val = Complex::new(prec);
        let ord = val.assign_str_round(src, round)?;
        Ok((val, ord))
    }

    /// Parses a `Complex` number with the specified radix and
    /// precision, applying the specified rounding.
    ///
    /// See the [corresponding assignment](#method.assign_str_radix_round).
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn from_str_radix_round
        (src: &str,
         radix: i32,
         prec: (u32, u32),
         round: Round2)
         -> Result<(Complex, Ordering2), ParseComplexError> {
        let mut val = Complex::new(prec);
        let ord = val.assign_str_radix_round(src, radix, round)?;
        Ok((val, ord))
    }

    /// Parses a `Complex` number from a string, rounding to the
    /// nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugcom::Complex;
    /// let mut c = Complex::new((53, 53));
    /// c.assign_str("(12.5e2 2.5e-1)").unwrap();
    /// assert!(*c.real() == 12.5e2);
    /// assert!(*c.imag() == 2.5e-1);
    /// let ret = c.assign_str("bad");
    /// assert!(ret.is_err());
    /// ```
    pub fn assign_str(&mut self, src: &str) -> Result<(), ParseComplexError> {
        self.assign_str_radix(src, 10)
    }

    /// Parses a `Complex` number from a string with the specified
    /// radix, rounding to the nearest.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rugcom::Complex;
    /// let mut c = Complex::new((53, 53));
    /// c.assign_str_radix("f.f", 16).unwrap();
    /// assert!(*c.real() == 15.9375);
    /// assert!(*c.imag() == 0);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix(&mut self,
                            src: &str,
                            radix: i32)
                            -> Result<(), ParseComplexError> {
        self.assign_str_radix_round(src, radix, NEAREST).map(|_| ())
    }

    /// Parses a `Complex` number from a string, applying the specified
    /// rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// extern crate rugflo;
    /// extern crate rugcom;
    /// use rugflo::Round;
    /// use rugcom::Complex;
    /// use std::cmp::Ordering;
    ///
    /// fn main() {
    ///     let mut c = Complex::new((4, 4));
    ///     let round = (Round::Down, Round::Up);
    ///     let dir = c.assign_str_round("(14.1 14.2)", round).unwrap();
    ///     assert!(*c.real() == 14);
    ///     assert!(*c.imag() == 15);
    ///     assert!(dir == (Ordering::Less, Ordering::Greater));
    /// }
    /// ```
    pub fn assign_str_round(&mut self,
                            src: &str,
                            round: Round2)
                            -> Result<Ordering2, ParseComplexError> {
        self.assign_str_radix_round(src, 10, round)
    }

    /// Parses a `Complex` number from a string with the specified
    /// radix, applying the specified rounding.
    ///
    /// Examples
    ///
    /// ```rust
    /// extern crate rugflo;
    /// extern crate rugcom;
    /// use rugflo::Round;
    /// use rugcom::Complex;
    /// use std::cmp::Ordering;
    ///
    /// fn main() {
    ///     let mut c = Complex::new((4, 4));
    ///     let round = (Round::Nearest, Round::Nearest);
    ///     let dir = c.assign_str_radix_round("(c.c c.1)", 16, round).unwrap();
    ///     assert!(*c.real() == 13);
    ///     assert!(*c.imag() == 12);
    ///     assert!(dir == (Ordering::Greater, Ordering::Less));
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn assign_str_radix_round(&mut self,
                                  src: &str,
                                  radix: i32,
                                  round: Round2)
                                  -> Result<Ordering2, ParseComplexError> {
        match check_str_radix(src, radix)? {
            PossibleFromStr::Real(r) => {
                let real_ord = self.mut_real()
                    .assign_str_radix_round(r, radix, round.0)
                    .unwrap();
                self.mut_imag().assign(Special::Zero);
                Ok((real_ord, Ordering::Equal))
            }
            PossibleFromStr::Complex(r, i) => {
                let real_ord = self.mut_real()
                    .assign_str_radix_round(r, radix, round.0)
                    .unwrap();
                let imag_ord = self.mut_imag()
                    .assign_str_radix_round(i, radix, round.1)
                    .unwrap();
                Ok((real_ord, imag_ord))
            }
        }
    }

    /// Checks if a `Complex` number can be parsed.
    ///
    /// If this method does not return an error, neither will any
    /// other function that parses a `Complex` number. If this method
    /// returns an error, the other functions will return the same
    /// error.
    ///
    /// # Panics
    ///
    /// Panics if `radix` is less than 2 or greater than 36.
    pub fn valid_str_radix(src: &str,
                           radix: i32)
                           -> Result<(), ParseComplexError> {
        check_str_radix(src, radix).map(|_| ())
    }
}

enum PossibleFromStr<'a> {
    Real(&'a str),
    Complex(&'a str, &'a str),
}

fn check_str_radix(src: &str,
                   radix: i32)
                   -> Result<PossibleFromStr, ParseComplexError> {
    use self::ParseComplexError as Error;
    use self::ParseErrorKind as Kind;

    if src.starts_with('(') {
        let space = src.find(' ').ok_or(Error { kind: Kind::MissingSpace })?;
        let real_str = &src[1..space];
        if Float::valid_str_radix(real_str, radix).is_err() {
            return Err(Error { kind: Kind::InvalidRealFloat });
        }
        let real_rest = &src[space + 1..];
        let close = real_rest
            .find(')')
            .ok_or(Error { kind: Kind::MissingClose })?;
        let imag_str = &real_rest[0..close];
        if Float::valid_str_radix(imag_str, radix).is_err() {
            return Err(Error { kind: Kind::InvalidImagFloat });
        }
        if close != real_rest.len() - 1 {
            return Err(Error { kind: Kind::CloseNotLast });
        }
        Ok(PossibleFromStr::Complex(real_str, imag_str))
    } else {
        if Float::valid_str_radix(src, radix).is_err() {
            return Err(Error { kind: Kind::InvalidFloat });
        }
        Ok(PossibleFromStr::Real(src))
    }
}

impl From<(Float, Float)> for Complex {
    /// Constructs a `Complex` number from a real `Float` and
    /// imaginary `Float`.
    ///
    /// This constructor does not allocate, as it reuses the `Float`
    /// components.
    fn from((real, imag): (Float, Float)) -> Complex {
        let mut dst: Complex = unsafe { mem::uninitialized() };
        unsafe {
            let mut real_imag = dst.as_mut_real_imag();
            ptr::copy_nonoverlapping(&real, real_imag.0, 1);
            ptr::copy_nonoverlapping(&imag, real_imag.1, 1);
        }
        mem::forget(real);
        mem::forget(imag);
        dst
    }
}

impl<T> From<(T, (i32, i32))> for Complex
    where Complex: From<(T, (u32, u32))>
{
    fn from((t, prec): (T, (i32, i32))) -> Complex {
        assert!(prec.0 >= rugflo::prec_min() as i32,
                "precision out of range");
        assert!(prec.1 >= rugflo::prec_min() as i32,
                "precision out of range");
        Complex::from((t, (prec.0 as u32, prec.1 as u32)))
    }
}

impl<T> FromRound<T, (i32, i32)> for Complex
    where Complex: FromRound<T,
                             (u32, u32),
                             Round = Round2,
                             Ordering = Ordering2>
{
    type Round = Round2;
    type Ordering = Ordering2;
    fn from_round(t: T,
                  prec: (i32, i32),
                  round: Round2)
                  -> (Complex, Ordering2) {
        assert!(prec.0 >= rugflo::prec_min() as i32,
                "precision out of range");
        assert!(prec.1 >= rugflo::prec_min() as i32,
                "precision out of range");
        Complex::from_round(t, (prec.0 as u32, prec.1 as u32), round)
    }
}

impl<T> From<(T, (i32, u32))> for Complex
    where Complex: From<(T, (u32, u32))>
{
    fn from((t, prec): (T, (i32, u32))) -> Complex {
        assert!(prec.0 >= rugflo::prec_min() as i32,
                "precision out of range");
        Complex::from((t, (prec.0 as u32, prec.1)))
    }
}

impl<T> FromRound<T, (i32, u32)> for Complex
    where Complex: FromRound<T,
                             (u32, u32),
                             Round = Round2,
                             Ordering = Ordering2>
{
    type Round = Round2;
    type Ordering = Ordering2;
    fn from_round(t: T,
                  prec: (i32, u32),
                  round: Round2)
                  -> (Complex, Ordering2) {
        assert!(prec.0 >= rugflo::prec_min() as i32,
                "precision out of range");
        Complex::from_round(t, (prec.0 as u32, prec.1), round)
    }
}

impl<T> From<(T, (u32, i32))> for Complex
    where Complex: From<(T, (u32, u32))>
{
    fn from((t, prec): (T, (u32, i32))) -> Complex {
        assert!(prec.1 >= rugflo::prec_min() as i32,
                "precision out of range");
        Complex::from((t, (prec.0, prec.1 as u32)))
    }
}

impl<T> FromRound<T, (u32, i32)> for Complex
    where Complex: FromRound<T,
                             (u32, u32),
                             Round = Round2,
                             Ordering = Ordering2>
{
    type Round = Round2;
    type Ordering = Ordering2;
    fn from_round(t: T,
                  prec: (u32, i32),
                  round: Round2)
                  -> (Complex, Ordering2) {
        assert!(prec.1 >= rugflo::prec_min() as i32,
                "precision out of range");
        Complex::from_round(t, (prec.0, prec.1 as u32), round)
    }
}

impl<T> From<(T, (u32, u32))> for Complex
    where Complex: FromRound<T, (u32, u32), Round = Round2>
{
    fn from((t, prec): (T, (u32, u32))) -> Complex {
        Complex::from_round(t, prec, NEAREST).0
    }
}

impl<T> FromRound<T, (u32, u32)> for Complex
    where Complex: AssignRound<T, Round = Round2, Ordering = Ordering2>
{
    type Round = Round2;
    type Ordering = Ordering2;
    fn from_round(t: T,
                  prec: (u32, u32),
                  round: Round2)
                  -> (Complex, Ordering2) {
        let mut ret = Complex::new(prec);
        let ord = ret.assign_round(t, round);
        (ret, ord)
    }
}

impl<T> Assign<T> for Complex
    where Complex: AssignRound<T, Round = Round2, Ordering = Ordering2>
{
    fn assign(&mut self, other: T) {
        self.assign_round(other, NEAREST);
    }
}

impl<'a> AssignRound<&'a Complex> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;

    fn assign_round(&mut self, other: &Complex, round: Round2) -> Ordering2 {
        let ord =
            unsafe { mpc::set(self.inner_mut(), other.inner(), rraw2(round)) };
        ordering2(ord)
    }
}

impl AssignRound<Complex> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;

    fn assign_round(&mut self, other: Complex, round: Round2) -> Ordering2 {
        self.assign_round(&other, round)
    }
}

impl<T, U> AssignRound<(T, U)> for Complex
    where Float: AssignRound<T, Round = Round, Ordering = Ordering>,
          Float: AssignRound<U, Round = Round, Ordering = Ordering>
{
    type Round = Round2;
    type Ordering = Ordering2;
    fn assign_round(&mut self, other: (T, U), round: Round2) -> Ordering2 {
        let (real, imag) = self.as_mut_real_imag();
        let ord1 = real.assign_round(other.0, round.0);
        let ord2 = imag.assign_round(other.1, round.1);
        (ord1, ord2)
    }
}

macro_rules! assign_ref {
    { $($T:ty)* } => {
        $(
            impl<'a> AssignRound<&'a $T> for Complex {
                type Round = Round2;
                type Ordering = Ordering2;
                fn assign_round(&mut self, other: &'a $T, round: Round2)
                                -> Ordering2 {
                    let (real, imag) = self.as_mut_real_imag();
                    let ord1 = real.assign_round(other, round.0);
                    let ord2 = imag.assign_round(0, round.1);
                    (ord1, ord2)
                }
            }
        )*
    };
}

macro_rules! assign {
    { $($T:ty)* } => {
        $(
            impl AssignRound<$T> for Complex {
                type Round = Round2;
                type Ordering = Ordering2;
                fn assign_round(&mut self, other: $T, round: Round2)
                                -> Ordering2 {
                    let (real, imag) = self.as_mut_real_imag();
                    let ord1 = real.assign_round(other, round.0);
                    let ord2 = imag.assign_round(0, round.1);
                    (ord1, ord2)
                }
            }
        )*
    };
}

assign_ref! { Integer Rational Float }
assign! { Integer Rational Float Special Constant u32 i32 f64 f32 }

impl Neg for Complex {
    type Output = Complex;
    fn neg(mut self) -> Complex {
        self.neg_assign();
        self
    }
}

impl NegAssign for Complex {
    fn neg_assign(&mut self) {
        unsafe {
            mpc::neg(self.inner_mut(), self.inner(), rraw2(NEAREST));
        }
    }
}

impl<'a> Neg for &'a Complex {
    type Output = NegHold<'a>;
    fn neg(self) -> NegHold<'a> {
        NegHold { val: self }
    }
}

/// Holds a negation.
pub struct NegHold<'a> {
    val: &'a Complex,
}

impl<'a> AssignRound<NegHold<'a>> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    fn assign_round(&mut self, src: NegHold<'a>, round: Round2) -> Ordering2 {
        ordering2(unsafe {
                      mpc::neg(self.inner_mut(), src.val.inner(), rraw2(round))
                  })
    }
}

macro_rules! arith_binary {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $T:ty,
        $func:path,
        $Hold:ident
    } => {
        impl<'a> $Imp<&'a $T> for Complex {
            type Output = Complex;
            fn $method(self, op: &'a $T) -> Complex {
                self.$method_round(op, NEAREST).0
            }
        }

        impl<'a> $ImpRound<&'a $T> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(mut self, rhs: &'a $T, round: Round2)
                             -> (Complex, Ordering2) {
                let ord = ordering2(unsafe {
                    $func(self.inner_mut(),
                          self.inner(),
                          rhs.inner(),
                          rraw2(round))
                });
                (self, ord)
            }
        }

        impl $Imp<$T> for Complex {
            type Output = Complex;
            fn $method(self, op: $T) -> Complex {
                self.$method_round(op, NEAREST).0
            }
        }

        impl $ImpRound<$T> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, rhs: $T, round: Round2)
                             -> (Complex, Ordering2) {
                self.$method_round(&rhs, round)
            }
        }

        impl<'a> $Imp<&'a $T> for &'a Complex {
            type Output = $Hold<'a>;
            fn $method(self, rhs: &'a $T) -> $Hold<'a> {
                $Hold {
                    lhs: self,
                    rhs: OwnBorrow::Borrow(rhs),
                }
            }
        }

        impl<'a> $ImpAssign<&'a $T> for Complex {
            fn $method_assign(&mut self, rhs: &'a $T) {
                unsafe {
                    $func(self.inner_mut(),
                          self.inner(),
                          rhs.inner(),
                          rraw2(NEAREST));
                }
            }
        }

        impl $ImpAssign<$T> for Complex {
            fn $method_assign(&mut self, rhs: $T) {
                self.$method_assign(&rhs);
            }
        }

        /// Holds an operation.
        pub struct $Hold<'a> {
            lhs: &'a Complex,
            rhs: OwnBorrow<'a, $T>,
        }

        impl<'a> AssignRound<$Hold<'a>> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            fn assign_round(&mut self, src: $Hold, round: Round2) -> Ordering2 {
                ordering2(unsafe {
                    $func(self.inner_mut(),
                          src.lhs.inner(),
                          src.rhs.inner(),
                          rraw2(round))
                })
            }
        }
    };
}

macro_rules! arith_commut_complex {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $func:path,
        $Hold:ident
    } => {
        arith_binary! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            Complex,
            $func,
            $Hold
        }

        impl<'a> $Imp<Complex> for &'a Complex {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl<'a> $ImpRound<Complex> for &'a Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, rhs: Complex, round: Round2)
                             -> (Complex, Ordering2) {
                rhs.$method_round(self, round)
            }
        }
    }
}

macro_rules! arith_noncommut_complex {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $ImpFromAssign:ident $method_from_assign:ident,
        $func:path,
        $Hold:ident
    } => {
        arith_binary! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            Complex,
            $func,
            $Hold
        }

        impl<'a> $Imp<Complex> for &'a Complex {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl<'a> $ImpRound<Complex> for &'a Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, mut rhs: Complex, round: Round2)
                             -> (Complex, Ordering2) {
                let ord = ordering2(unsafe {
                    $func(rhs.inner_mut(),
                          self.inner(),
                          rhs.inner(),
                          rraw2(round))
                });
                (rhs, ord)
            }
        }

        impl<'a> $ImpFromAssign<&'a Complex> for Complex {
            fn $method_from_assign(&mut self, lhs: &Complex) {
                unsafe {
                    $func(self.inner_mut(),
                          lhs.inner(),
                          self.inner(),
                          rraw2(NEAREST));
                }
            }
        }

        impl $ImpFromAssign for Complex {
            fn $method_from_assign(&mut self, lhs: Complex) {
                self.$method_from_assign(&lhs);
            }
        }
    }
}

macro_rules! arith_forward {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $T:ty,
        $func:path,
        $Hold:ident
    } => {
        arith_binary! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Hold
        }

        impl<'a> $Imp<$T> for &'a Complex {
            type Output = $Hold<'a>;
            fn $method(self, rhs: $T) -> $Hold<'a> {
                $Hold {
                    lhs: self,
                    rhs: OwnBorrow::Own(rhs),
                }
            }
        }
    };
}

macro_rules! arith_commut {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $T:ty,
        $func:path,
        $Hold:ident
    } => {
        arith_forward! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Hold
        }

        impl<'a> $Imp<Complex> for &'a $T {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl<'a> $ImpRound<Complex> for &'a $T {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, rhs: Complex, round: Round2)
                             -> (Complex, Ordering2) {
                rhs.$method_round(self, round)
            }
        }

        impl $Imp<Complex> for $T {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl $ImpRound<Complex> for $T {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, rhs: Complex, round: Round2)
                             -> (Complex, Ordering2) {
                rhs.$method_round(self, round)
            }
        }

        impl<'a> $Imp<&'a Complex> for &'a $T {
            type Output = $Hold<'a>;
            fn $method(self, rhs: &'a Complex) -> $Hold<'a> {
                rhs.$method(self)
            }
        }

        impl<'a> $Imp<&'a Complex> for $T {
            type Output = $Hold<'a>;
            fn $method(self, rhs: &'a Complex) -> $Hold<'a> {
                rhs.$method(self)
            }
        }
    };
}

macro_rules! arith_noncommut {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $ImpFromAssign:ident $method_from_assign:ident,
        $T:ty,
        $func:path,
        $func_from:path,
        $Hold:ident,
        $HoldFrom:ident
    } => {
        arith_forward! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Hold
        }

        impl<'a> $Imp<Complex> for &'a $T {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl<'a> $ImpRound<Complex> for &'a $T {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, mut rhs: Complex, round: Round2)
                             -> (Complex, Ordering2) {
                let ord = ordering2(unsafe {
                    $func_from(rhs.inner_mut(),
                               self.inner(),
                               rhs.inner(),
                               rraw2(round))
                });
                (rhs, ord)
            }
        }

        impl $Imp<Complex> for $T {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl $ImpRound<Complex> for $T {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, rhs: Complex, round: Round2)
                             -> (Complex, Ordering2) {
                (&self).$method_round(rhs, round)
            }
        }

        impl<'a> $Imp<&'a Complex> for &'a $T {
            type Output = $HoldFrom<'a>;
            fn $method(self, rhs: &'a Complex) -> $HoldFrom<'a> {
                $HoldFrom {
                    lhs: OwnBorrow::Borrow(self),
                    rhs: rhs,
                }
            }
        }

        impl<'a> $Imp<&'a Complex> for $T {
            type Output = $HoldFrom<'a>;
            fn $method(self, rhs: &'a Complex) -> $HoldFrom<'a> {
                $HoldFrom {
                    lhs: OwnBorrow::Own(self),
                    rhs: rhs,
                }
            }
        }

        impl<'a> $ImpFromAssign<&'a $T> for Complex {
            fn $method_from_assign(&mut self, lhs: &'a $T) {
                unsafe {
                    $func_from(self.inner_mut(),
                               lhs.inner(),
                               self.inner(),
                               rraw2(NEAREST));
                }
            }
        }

        impl $ImpFromAssign<$T> for Complex {
            fn $method_from_assign(&mut self, lhs: $T) {
                self.$method_from_assign(&lhs);
            }
        }

        /// Holds an operation.
        pub struct $HoldFrom<'a> {
            lhs: OwnBorrow<'a, $T>,
            rhs: &'a Complex,
        }

        impl<'a> AssignRound<$HoldFrom<'a>> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            fn assign_round(&mut self, src: $HoldFrom, round: Round2)
                            -> Ordering2 {
                ordering2(unsafe {
                    $func_from(self.inner_mut(),
                               src.lhs.inner(),
                               src.rhs.inner(),
                               rraw2(round))
                })
            }
        }
    };
}

arith_commut_complex! {
    Add add, AddRound add_round, AddAssign add_assign, mpc::add, AddHold
}
arith_noncommut_complex! {
    Sub sub,
    SubRound sub_round,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    mpc::sub,
    SubHold
}
arith_commut_complex! {
    Mul mul, MulRound mul_round, MulAssign mul_assign, mpc::mul, MulHold
}
arith_noncommut_complex! {
    Div div,
    DivRound div_round,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    mpc::div,
    DivHold
}
arith_noncommut_complex! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    PowFromAssign pow_from_assign,
    mpc::pow,
    PowHold
}

arith_commut! {
    Add add,
    AddRound add_round,
    AddAssign add_assign,
    Float,
    mpc::add_fr,
    AddHoldFloat
}
arith_noncommut! {
    Sub sub,
    SubRound sub_round,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    Float,
    mpc::sub_fr,
    mpc::fr_sub,
    SubHoldFloat,
    SubFromHoldFloat
}
arith_commut! {
    Mul mul,
    MulRound mul_round,
    MulAssign mul_assign,
    Float,
    mpc::mul_fr,
    MulHoldFloat
}
arith_noncommut! {
    Div div,
    DivRound div_round,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    Float,
    mpc::div_fr,
    mpc::fr_div,
    DivHoldFloat,
    DivFromHoldFloat
}
arith_forward! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    Float,
    mpc::pow_fr,
    PowHoldFloat
}
arith_forward! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    Integer,
    mpc::pow_z,
    PowHoldInteger
}

macro_rules! arith_prim {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $T:ty,
        $func:path,
        $Hold:ident
    } => {
        impl $Imp<$T> for Complex {
            type Output = Complex;
            fn $method(self, rhs: $T) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl $ImpRound<$T> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(mut self, rhs: $T, round: Round2)
                             -> (Complex, Ordering2) {
                let ord = ordering2(unsafe {
                    $func(self.inner_mut(),
                          self.inner(),
                          rhs.into(),
                          rraw2(round))
                });
                (self, ord)
            }
        }

        impl<'a> $Imp<$T> for &'a Complex {
            type Output = $Hold<'a>;
            fn $method(self, rhs: $T) -> $Hold<'a> {
                $Hold {
                    lhs: self,
                    rhs: rhs,
                }
            }
        }

        impl $ImpAssign<$T> for Complex {
            fn $method_assign(&mut self, rhs: $T) {
                unsafe {
                    $func(self.inner_mut(),
                          self.inner(),
                          rhs.into(),
                          rraw2(NEAREST));
                }
            }
        }

        /// Holds an operation.
        pub struct $Hold<'a> {
            lhs: &'a Complex,
            rhs: $T,
        }

        impl<'a> AssignRound<$Hold<'a>> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            fn assign_round(&mut self, src: $Hold, round: Round2) -> Ordering2 {
                ordering2(unsafe {
                    $func(self.inner_mut(),
                          src.lhs.inner(),
                          src.rhs.into(),
                          rraw2(round))
                })
            }
        }
    };
}

macro_rules! arith_prim_commut {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $T:ty,
        $func:path,
        $Hold:ident
    }=> {
        arith_prim! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Hold
        }

        impl $Imp<Complex> for $T {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl $ImpRound<Complex> for $T {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, rhs: Complex, round: Round2)
                             -> (Complex, Ordering2) {
                rhs.$method_round(self, round)
            }
        }

        impl<'a> $Imp<&'a Complex> for $T {
            type Output = $Hold<'a>;
            fn $method(self, rhs: &'a Complex) -> $Hold<'a> {
                rhs.$method(self)
            }
        }
    };
}

macro_rules! arith_prim_noncommut {
    {
        $Imp:ident $method:ident,
        $ImpRound:ident $method_round:ident,
        $ImpAssign:ident $method_assign:ident,
        $ImpFromAssign:ident $method_from_assign:ident,
        $T:ty,
        $func:path,
        $func_from:path,
        $Hold:ident,
        $HoldFrom:ident
    } => {
        arith_prim! {
            $Imp $method,
            $ImpRound $method_round,
            $ImpAssign $method_assign,
            $T,
            $func,
            $Hold
        }

        impl $Imp<Complex> for $T {
            type Output = Complex;
            fn $method(self, rhs: Complex) -> Complex {
                self.$method_round(rhs, NEAREST).0
            }
        }

        impl $ImpRound<Complex> for $T {
            type Round = Round2;
            type Ordering = Ordering2;
            type Output = Complex;
            fn $method_round(self, mut rhs: Complex, round: Round2)
                             -> (Complex, Ordering2) {
                let ord = ordering2(unsafe {
                    $func_from(rhs.inner_mut(),
                               self.into(),
                               rhs.inner(),
                               rraw2(round))
                });
                (rhs, ord)
            }
        }

        impl<'a> $Imp<&'a Complex> for $T {
            type Output = $HoldFrom<'a>;
            fn $method(self, rhs: &'a Complex) -> $HoldFrom<'a> {
                $HoldFrom {
                    lhs: self,
                    rhs: rhs,
                }
            }
        }

        impl $ImpFromAssign<$T> for Complex {
            fn $method_from_assign(&mut self, lhs: $T) {
                unsafe {
                    $func_from(self.inner_mut(),
                               lhs.into(),
                               self.inner(),
                               rraw2(NEAREST));
                }
            }
        }

        /// Holds an operation.
        pub struct $HoldFrom<'a> {
            lhs: $T,
            rhs: &'a Complex,
        }

        impl<'a> AssignRound<$HoldFrom<'a>> for Complex {
            type Round = Round2;
            type Ordering = Ordering2;
            fn assign_round(&mut self, src: $HoldFrom, round: Round2)
                            -> Ordering2 {
                ordering2(unsafe {
                    $func_from(self.inner_mut(),
                               src.lhs.into(),
                               src.rhs.inner(),
                               rraw2(round))
                })
            }
        }
    };
}

arith_prim_commut! {
    Add add,
    AddRound add_round,
    AddAssign add_assign,
    u32,
    mpc::add_ui,
    AddHoldU32
}
arith_prim_noncommut! {
    Sub sub,
    SubRound sub_round,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    u32,
    mpc::sub_ui,
    ui_sub,
    SubHoldU32,
    SubFromHoldU32
}
arith_prim_commut! {
    Mul mul,
    MulRound mul_round,
    MulAssign mul_assign,
    u32,
    mpc::mul_ui,
    MulHoldU32
}
arith_prim_noncommut! {
    Div div,
    DivRound div_round,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    u32,
    mpc::div_ui,
    mpc::ui_div,
    DivHoldU32,
    DivFromHoldU32
}
arith_prim_commut! {
    Add add,
    AddRound add_round,
    AddAssign add_assign,
    i32,
    add_si,
    AddHoldI32
}
arith_prim_noncommut! {
    Sub sub,
    SubRound sub_round,
    SubAssign sub_assign,
    SubFromAssign sub_from_assign,
    i32,
    sub_si,
    si_sub,
    SubHoldI32,
    SubFromHoldI32
}
arith_prim_commut! {
    Mul mul,
    MulRound mul_round,
    MulAssign mul_assign,
    i32,
    mpc::mul_si,
    MulHoldI32
}
arith_prim_noncommut! {
    Div div,
    DivRound div_round,
    DivAssign div_assign,
    DivFromAssign div_from_assign,
    i32,
    div_si,
    si_div,
    DivHoldI32,
    DivFromHoldI32
}

unsafe fn ui_sub(x: *mut mpc::mpc_t,
                 y: c_ulong,
                 z: *const mpc::mpc_t,
                 r: mpc::rnd_t)
                 -> c_int {
    let mz = z as *mut _;
    let (r_re, r_im) = rnd_re_im(r);
    let re = mpfr::ui_sub(mpc::realref(x), y, mpc::realref(mz), r_re);
    let re = match re.cmp(&0) {
        Ordering::Less => 2,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    };
    let im = mpfr::ui_sub(mpc::imagref(x), 0, mpc::imagref(mz), r_im);
    let im = match im.cmp(&0) {
        Ordering::Less => 8,
        Ordering::Equal => 0,
        Ordering::Greater => 4,
    };
    re | im
}

unsafe fn add_si(x: *mut mpc::mpc_t,
                 y: *const mpc::mpc_t,
                 z: c_long,
                 r: mpc::rnd_t)
                 -> c_int {
    if z < 0 {
        mpc::sub_ui(x, y, z.wrapping_neg() as c_ulong, r)
    } else {
        mpc::add_ui(x, y, z as c_ulong, r)
    }
}

unsafe fn sub_si(x: *mut mpc::mpc_t,
                 y: *const mpc::mpc_t,
                 z: c_long,
                 r: mpc::rnd_t)
                 -> c_int {
    if z < 0 {
        mpc::add_ui(x, y, z.wrapping_neg() as c_ulong, r)
    } else {
        mpc::sub_ui(x, y, z as c_ulong, r)
    }
}

unsafe fn si_sub(x: *mut mpc::mpc_t,
                 y: c_long,
                 z: *const mpc::mpc_t,
                 r: mpc::rnd_t)
                 -> c_int {
    let mz = z as *mut _;
    let (r_re, r_im) = rnd_re_im(r);
    let re = mpfr::si_sub(mpc::realref(x), y, mpc::realref(mz), r_re);
    let re = match re.cmp(&0) {
        Ordering::Less => 2,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    };
    let im = mpfr::ui_sub(mpc::imagref(x), 0, mpc::imagref(mz), r_im);
    let im = match im.cmp(&0) {
        Ordering::Less => 8,
        Ordering::Equal => 0,
        Ordering::Greater => 4,
    };
    re | im
}

unsafe fn div_si(x: *mut mpc::mpc_t,
                 y: *const mpc::mpc_t,
                 z: c_long,
                 r: mpc::rnd_t)
                 -> c_int {
    let my = y as *mut _;
    let (r_re, r_im) = rnd_re_im(r);
    let re = mpfr::div_si(mpc::realref(x), mpc::realref(my), z, r_re);
    let re = match re.cmp(&0) {
        Ordering::Less => 2,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    };
    let im = mpfr::div_si(mpc::imagref(x), mpc::imagref(my), z, r_im);
    let im = match im.cmp(&0) {
        Ordering::Less => 8,
        Ordering::Equal => 0,
        Ordering::Greater => 4,
    };
    re | im
}

unsafe fn si_div(x: *mut mpc::mpc_t,
                 y: c_long,
                 z: *const mpc::mpc_t,
                 r: mpc::rnd_t)
                 -> c_int {
    let prec = mem::size_of::<c_long>() as u32 * 8;
    let mut dividend = Complex::new((prec, prec));
    mpc::set_si(dividend.inner_mut(), y, rraw2(NEAREST));
    mpc::div(x, dividend.inner(), z, r)
}

arith_prim! {
    Shl shl,
    ShlRound shl_round,
    ShlAssign shl_assign,
    u32,
    mpc::mul_2ui,
    ShlHoldU32
}
arith_prim! {
    Shr shr,
    ShrRound shr_round,
    ShrAssign shr_assign,
    u32,
    mpc::div_2ui,
    ShrHoldU32
}
arith_prim! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    u32,
    mpc::pow_ui,
    PowHoldU32
}
arith_prim! {
    Shl shl,
    ShlRound shl_round,
    ShlAssign shl_assign,
    i32,
    mpc::mul_2si,
    ShlHoldI32
}
arith_prim! {
    Shr shr,
    ShrRound shr_round,
    ShrAssign shr_assign,
    i32,
    mpc::div_2si,
    ShrHoldI32
}
arith_prim! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    i32,
    mpc::pow_si,
    PowHoldI32
}
arith_prim! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    f64,
    mpc::pow_d,
    PowHoldF64
}
arith_prim! {
    Pow pow,
    PowRound pow_round,
    PowAssign pow_assign,
    f32,
    pow_single,
    PowHoldF32
}

unsafe fn pow_single(x: *mut mpc::mpc_t,
                     y: *const mpc::mpc_t,
                     z: f32,
                     r: mpc::rnd_t)
                     -> c_int {
    mpc::pow_d(x, y, z as f64, r)
}

impl PartialEq for Complex {
    fn eq(&self, other: &Complex) -> bool {
        self.real().eq(other.real()) && self.imag().eq(other.imag())
    }
}

impl<T, U> PartialEq<(T, U)> for Complex
    where Float: PartialEq<T>,
          Float: PartialEq<U>
{
    fn eq(&self, other: &(T, U)) -> bool {
        self.real().eq(&other.0) && self.imag().eq(&other.1)
    }
}

macro_rules! partial_eq {
    { $($T:ty)* } => {
        $(
            impl PartialEq<$T> for Complex {
                fn eq(&self, other: &$T) -> bool {
                    self.real().eq(other) && self.imag().is_zero()
                }
            }
        )*
    };
}

partial_eq! { Integer Rational Float u32 i32 f64 f32 }

fn fmt_radix(c: &Complex,
             fmt: &mut Formatter,
             radix: i32,
             to_upper: bool,
             prefix: &str,
             show_neg_zero: bool)
             -> fmt::Result {
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

fn fmt_float(buf: &mut String,
             flt: &Float,
             fmt: &mut Formatter,
             radix: i32,
             to_upper: bool,
             prefix: &str,
             show_neg_zero: bool) {
    let show_neg_zero = show_neg_zero || fmt.sign_plus();
    let mut s = flt.to_string_radix(radix, fmt.precision());
    if s.starts_with('-') ||
       (show_neg_zero && flt.is_zero() && flt.get_sign()) {
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

impl Display for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl Debug for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", true)
    }
}

impl LowerExp for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, false, "", false)
    }
}

impl UpperExp for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 10, true, "", false)
    }
}

impl Binary for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 2, false, "0b", false)
    }
}

impl Octal for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 8, false, "0o", false)
    }
}

impl LowerHex for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, false, "0x", false)
    }
}

impl UpperHex for Complex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fmt_radix(self, f, 16, true, "0x", false)
    }
}


#[derive(Clone, Debug, Eq, PartialEq)]
/// An error which can be returned when parsing a `Complex` number.
pub struct ParseComplexError {
    kind: ParseErrorKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ParseErrorKind {
    InvalidFloat,
    InvalidRealFloat,
    InvalidImagFloat,
    MissingSpace,
    MissingClose,
    CloseNotLast,
}

impl Error for ParseComplexError {
    fn description(&self) -> &str {
        use self::ParseErrorKind::*;
        match self.kind {
            InvalidFloat => "string is not a valid float",
            InvalidRealFloat => "real part of string is not a valid float",
            InvalidImagFloat => "imaginary part of string is not a valid float",
            MissingSpace => "string has no space after opening bracket",
            MissingClose => "string has no closing bracket",
            CloseNotLast => "string has more characters after closing bracket",
        }
    }
}

impl Display for ParseComplexError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

fn rraw(round: Round) -> mpfr::rnd_t {
    match round {
        Round::Nearest => mpfr::rnd_t::RNDN,
        Round::Zero => mpfr::rnd_t::RNDZ,
        Round::Up => mpfr::rnd_t::RNDU,
        Round::Down => mpfr::rnd_t::RNDD,
        Round::AwayFromZero => mpfr::rnd_t::RNDA,
    }
}

fn rraw2(round: Round2) -> mpc::rnd_t {
    match (round.0, round.1) {
        (Round::Nearest, Round::Nearest) => mpc::RNDNN,
        (Round::Nearest, Round::Zero) => mpc::RNDNZ,
        (Round::Nearest, Round::Up) => mpc::RNDNU,
        (Round::Nearest, Round::Down) => mpc::RNDND,
        (Round::Zero, Round::Nearest) => mpc::RNDZN,
        (Round::Zero, Round::Zero) => mpc::RNDZZ,
        (Round::Zero, Round::Up) => mpc::RNDZU,
        (Round::Zero, Round::Down) => mpc::RNDZD,
        (Round::Up, Round::Nearest) => mpc::RNDUN,
        (Round::Up, Round::Zero) => mpc::RNDUZ,
        (Round::Up, Round::Up) => mpc::RNDUU,
        (Round::Up, Round::Down) => mpc::RNDUD,
        (Round::Down, Round::Nearest) => mpc::RNDDN,
        (Round::Down, Round::Zero) => mpc::RNDDZ,
        (Round::Down, Round::Up) => mpc::RNDDU,
        (Round::Down, Round::Down) => mpc::RNDDD,
        (Round::AwayFromZero, _) |
        (_, Round::AwayFromZero) => unimplemented!(),
    }
}

fn rnd_re_im(r: mpc::rnd_t) -> (mpfr::rnd_t, mpfr::rnd_t) {
    let re = match r & 0x0f {
        0 => mpfr::rnd_t::RNDN,
        1 => mpfr::rnd_t::RNDZ,
        2 => mpfr::rnd_t::RNDU,
        3 => mpfr::rnd_t::RNDD,
        4 => mpfr::rnd_t::RNDA,
        5 => mpfr::rnd_t::RNDF,
        _ => mpfr::rnd_t::RNDNA,
    };
    let im = match r >> 4 {
        0 => mpfr::rnd_t::RNDN,
        1 => mpfr::rnd_t::RNDZ,
        2 => mpfr::rnd_t::RNDU,
        3 => mpfr::rnd_t::RNDD,
        4 => mpfr::rnd_t::RNDA,
        5 => mpfr::rnd_t::RNDF,
        _ => mpfr::rnd_t::RNDNA,
    };
    (re, im)
}

fn ordering2(ord: c_int) -> (Ordering, Ordering) {
    // ord == first + 4 * second
    let first = mpc::INEX_RE(ord).cmp(&0);
    let second = mpc::INEX_IM(ord).cmp(&0);
    (first, second)
}

trait Inner {
    type Output;
    fn inner(&self) -> &Self::Output;
}

trait InnerMut: Inner {
    unsafe fn inner_mut(&mut self) -> &mut Self::Output;
}

impl Inner for Complex {
    type Output = mpc::mpc_t;
    fn inner(&self) -> &mpc::mpc_t {
        &self.inner
    }
}

impl InnerMut for Complex {
    unsafe fn inner_mut(&mut self) -> &mut mpc::mpc_t {
        &mut self.inner
    }
}

impl Inner for Float {
    type Output = mpfr::mpfr_t;
    fn inner(&self) -> &mpfr::mpfr_t {
        let ptr = self as *const _ as *const mpfr::mpfr_t;
        unsafe { &*ptr }
    }
}

impl InnerMut for Float {
    unsafe fn inner_mut(&mut self) -> &mut mpfr::mpfr_t {
        let ptr = self as *mut _ as *mut mpfr::mpfr_t;
        &mut *ptr
    }
}

impl Inner for Integer {
    type Output = gmp::mpz_t;
    fn inner(&self) -> &gmp::mpz_t {
        let ptr = self as *const _ as *const gmp::mpz_t;
        unsafe { &*ptr }
    }
}

enum OwnBorrow<'a, T>
    where T: 'a
{
    Own(T),
    Borrow(&'a T),
}

impl<'a, T> Inner for OwnBorrow<'a, T>
    where T: Inner
{
    type Output = <T as Inner>::Output;
    fn inner(&self) -> &Self::Output {
        match *self {
            OwnBorrow::Own(ref o) => o.inner(),
            OwnBorrow::Borrow(b) => b.inner(),
        }
    }
}

#[cfg(test)]
mod tests {
    use complex::*;
    use std::f64;

    #[test]
    fn check_from_str() {
        let mut c = Complex::new((53, 53));
        c.assign_str("(+0 -0)").unwrap();
        assert!(c == (0, 0));
        assert!(!c.real().get_sign());
        assert!(c.imag().get_sign());
        c.assign_str("(5 6)").unwrap();
        assert!(c == (5, 6));
        c.assign_str_radix("(50 60)", 8).unwrap();
        assert!(c == (0o50, 0o60));
        c.assign_str_radix("33", 16).unwrap();
        assert!(c == (0x33, 0));

        let bad_strings = [("(0,0)", None),
                           ("(0 0 )", None),
                           ("( 0 0)", None),
                           ("( 0)", None),
                           ("(0 )", None),
                           (" ( 2)", None),
                           ("+(1 1)", None),
                           ("-(1. 1.)", None),
                           ("(1 1@1a(", Some(16)),
                           ("(8 9)", Some(9))];
        for &(s, radix) in bad_strings.into_iter() {
            assert!(Complex::valid_str_radix(s, radix.unwrap_or(10)).is_err());
        }
        let good_strings =
            [("(inf -@inf@)", 10, f64::INFINITY, f64::NEG_INFINITY),
             ("(+0e99 1.)", 2, 0.0, 1.0),
             ("-9.9e1", 10, -99.0, 0.0)];
        for &(s, radix, r, i) in good_strings.into_iter() {
            assert!(Complex::from_str_radix(s, radix, (53, 53)).unwrap() ==
                    (r, i));
        }
    }


    #[test]
    fn check_formatting() {
        let mut c = Complex::new((53, 53));
        c.assign((Special::Zero, Special::MinusZero));
        assert!(format!("{}", c) == "(0.0 0.0)");
        assert!(format!("{:?}", c) == "(0.0 -0.0)");
        assert!(format!("{:+}", c) == "(+0.0 -0.0)");
        c.assign((2.7, f64::NEG_INFINITY));
        assert!(format!("{:.2}", c) == "(2.7e0 -inf)");
        assert!(format!("{:+.8}", c) == "(+2.7000000e0 -inf)");
        assert!(format!("{:.4e}", c) == "(2.700e0 -inf)");
        assert!(format!("{:.4E}", c) == "(2.700E0 -inf)");
        assert!(format!("{:16.2}", c) == "    (2.7e0 -inf)");
        c.assign((3.5, 11));
        assert!(format!("{:.4b}", c) == "(1.110e1 1.011e3)");
        assert!(format!("{:#.4b}", c) == "(0b1.110e1 0b1.011e3)");
        assert!(format!("{:.4o}", c) == "(3.400e0 1.300e1)");
        assert!(format!("{:#.4o}", c) == "(0o3.400e0 0o1.300e1)");
        assert!(format!("{:.2x}", c) == "(3.8@0 b.0@0)");
        assert!(format!("{:#.2x}", c) == "(0x3.8@0 0xb.0@0)");
        assert!(format!("{:.2X}", c) == "(3.8@0 B.0@0)");
        assert!(format!("{:#.2X}", c) == "(0x3.8@0 0xB.0@0)");
    }

    #[test]
    fn check_no_nails() {
        // we assume no nail bits when we use limbs
        assert!(gmp::NAIL_BITS == 0);
        assert!(gmp::NUMB_BITS == gmp::LIMB_BITS);
        assert!(gmp::NUMB_BITS as usize == 8 * mem::size_of::<gmp::limb_t>());
    }
}
