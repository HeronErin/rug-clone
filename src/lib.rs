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

//! # Multiple-precision complex numbers
//!
//! The `rugcom` crate provides multiple-precision complex numbers
//! using [GNU MPC](http://www.multiprecision.org/), a library for the
//! arithmetic of complex numbers with arbitrarily high precision and
//! correct rounding of the result. It can be helpful to refer to the
//! documentation at the
//! [MPC](http://www.multiprecision.org/index.php?prog=mpc&page=html)
//! page.
//!
//! This crate is free software: you can redistribute it and/or modify
//! it under the terms of the GNU Lesser General Public License as
//! published by the Free Software Foundation, either version 3 of the
//! License, or (at your option) any later version.
//!
//! See the [LGPL](https://www.gnu.org/licenses/lgpl-3.0.en.html) and
//! [GPL](https://www.gnu.org/licenses/gpl-3.0.html) for details.
//!
//! This crate is one of a group of four crates:
//!
//! * [`rugint`](https://tspiteri.gitlab.io/gmp-mpfr/rugint/)
//!   provides arbitrary-precision integers based on GMP.
//! * [`rugrat`](https://tspiteri.gitlab.io/gmp-mpfr/rugrat/)
//!   provides arbitrary-precision rational number based on GMP.
//! * [`rugflo`](https://tspiteri.gitlab.io/gmp-mpfr/rugflo/)
//!   provides arbitrary-precision floating-point numbers based on MPFR.
//! * [`rugcom`](https://tspiteri.gitlab.io/gmp-mpfr/rugcom/)
//!   provides arbitrary-precision complex numbers based on MPC.
//!
//! ## Basic use
//!
//! The crate provides the [`Complex`](./struct.Complex.html) type,
//! which holds a multiple-precision complex number.
//!
//! ## Examples
//!
//! ```rust
//! extern crate rugint;
//! extern crate rugcom;
//! use rugint::Assign;
//! use rugcom::Complex;
//!
//! fn main() {
//!     // Create complex number with 16 bits of precision.
//!     let mut com = Complex::new((16, 16));
//!     // Assign the complex value 1.5 + 3.5i
//!     com.assign((1.5, 3.5));
//!     assert!(*com.real() == 1.5);
//!     assert!(*com.imag() == 3.5);
//! }
//! ```
//!
//! ## Usage
//!
//! To use `rugcom` in your crate, add `extern crate rugcom;` to the
//! crate root and add `rugcom` as a dependency in `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rugcom = "0.1.3"
//! ```
//!
//! The `rugcom` crate depends on the low-level bindings in the
//! [`gmp-mpfr-sys`](https://tspiteri.gitlab.io/gmp-mpfr/gmp_mpfr_sys/)
//! crate. This should be transparent on GNU/Linux and macOS, but may
//! need some work on Windows. See
//! [`gmp-mpfr-sys`](https://tspiteri.gitlab.io/gmp-mpfr/gmp_mpfr_sys/)
//! for some details.
//!
//! ### Optional feature
//!
//! The `rugcom` crate has an optional feature `random` to enable
//! random number generation. The `random` feature has a build
//! dependency on the `rand` crate. The feature is enabled by default;
//! to disable it add this to `Cargo.toml`:
//!
//! ```toml
//! [dependencies.rugcom]
//! version = "0.1.3"
//! default-features = false
//! ```

extern crate gmp_mpfr_sys;
#[cfg(feature = "random")]
extern crate rand;
extern crate rugint;
extern crate rugrat;
extern crate rugflo;

mod complex;

pub use complex::{Complex, ParseComplexError};
