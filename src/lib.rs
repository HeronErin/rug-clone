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

//! Crate `rug`.

#![warn(missing_docs)]
#![doc(test(attr(deny(warnings))))]

extern crate gmp_mpfr_sys;

#[macro_use]
mod macros;
mod inner;

pub mod ops;
pub mod rand;

mod integer;
#[cfg(feature = "rational")]
mod rational;
#[cfg(feature = "float")]
mod float;
#[cfg(feature = "complex")]
mod complex;

#[cfg(feature = "complex")]
pub use complex::{Complex, ParseComplexError, Prec, SmallComplex, ValidComplex};
#[cfg(feature = "float")]
pub use float::{Constant, Float, ParseFloatError, Round, SmallFloat, Special,
                ValidFloat, exp_max, exp_min, prec_max, prec_min};
pub use integer::{Integer, IsPrime, ParseIntegerError, SmallInteger,
                  ValidInteger};
pub use ops::{Assign, AssignRound, FromRound};
#[cfg(feature = "rational")]
pub use rational::{MutNumerDenom, ParseRationalError, Rational, SmallRational,
                   ValidRational};
