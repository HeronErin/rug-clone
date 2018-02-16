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

//! # Arbitrary-precision numbers
//!
//! The Rug crate provides integers and floating-point numbers with
//! arbitrary precision and correct rounding. Its main features are
//!
//! * bignum [integers][rug int] with arbitrary precision,
//! * bignum [rational numbers][rug rat] with arbitrary precision,
//! * multi-precision [floating-point numbers][rug flo] with correct
//!   rounding, and
//! * multi-precision [complex numbers][rug com] with correct
//!   rounding.
//!
//! This crate is free software: you can redistribute it and/or modify
//! it under the terms of the GNU Lesser General Public License as
//! published by the Free Software Foundation, either version 3 of the
//! License, or (at your option) any later version. See the full text
//! of the [GNU LGPL][lgpl] and [GNU GPL][gpl] for details.
//!
//! ## Version 1.0.0 coming soon
//!
//! Version 0.10.0 is meant to be the last release before version
//! 1.0.0. Unless some major issue is discovered, version 1.0.0 will
//! be like version 0.10.0 with all the deprecated items removed.
//!
//! ## Getting started
//!
//! ### Setting up the crate
//!
//! To use Rug in your crate, add it as a dependency inside
//! [*Cargo.toml*][cargo deps]:
//!
//! ```toml
//! [dependencies]
//! rug = "0.10.0"
//! ```
//!
//! This crate depends on the low-level bindings in the
//! [gmp-mpfr-sys crate][sys crate] which needs some setup to build;
//! the [gmp-mpfr-sys documentation][sys] has some details on usage
//! under [GNU/Linux][sys gnu], [macOS][sys mac] and
//! [Windows][sys win].
//!
//! You also need to declare Rug by adding this to your crate root:
//!
//! ```rust
//! extern crate rug;
//! # fn main() {}
//! ```
//!
//! More details are available in the [Crate usage](#crate-usage)
//! section below.
//!
//! ### Basic example
//!
//! For many operations, you can use the arbitrary-precision types
//! such as [`Integer`][rug int] like you use primitive types such as
//! [`i32`][rust i32]. The main difference is that the Rug types do
//! not implement [`Copy`][rust copy]. This is because they store
//! their digits in the heap, not on the stack, and copying them could
//! involve an expensive deep copy.
//!
//! This code uses the [`Integer`][rug int] type:
//!
//! ```rust
//! extern crate rug;
//! # #[cfg(feature = "integer")]
//! use rug::{Assign, Integer};
//!
//! fn main() {
//! # #[cfg(feature = "integer")] {
//!     let mut int = Integer::new();
//!     assert_eq!(int, 0);
//!     int.assign(14);
//!     assert_eq!(int, 14);
//!     int.assign(Integer::parse("12_345_678_901_234_567_890").unwrap());
//!     assert!(int > 100_000_000);
//!     let hex_160 = "ffff0000ffff0000ffff0000ffff0000ffff0000";
//!     int.assign(Integer::parse_radix(hex_160, 16).unwrap());
//!     assert_eq!(int.significant_bits(), 160);
//!     int = (int >> 128) - 1;
//!     assert_eq!(int, 0xfffe_ffff_u32);
//! # }
//! }
//! ```
//!
//! Some points from this example follow:
//!
//! * [`Integer::new()`][rug int new] creates a new
//!   [`Integer`][rug int] intialized to zero.
//! * To assign values to Rug types, we use the
//!   [`Assign`][rug assign] trait and its method
//!   [`assign`][rug assign assign]. We do not use the
//!   [assignment operator `=`][rust assignment] as that would move
//!   the left-hand-side operand, which would have the same type.
//! * Arbitrary precision numbers can hold numbers that are too large
//!   to fit in a primitive type. To assign such a number to the large
//!   types, we use strings rather than primitives; in the example
//!   this is done using both [`Integer::parse`][rug int parse] and
//!   [`Integer::parse_radix`][rug int parseradix].
//! * We can compare Rug types with primitive types or with other Rug
//!   types using the normal comparison operators, for example
//!   `int > 100_000_000_000`.
//! * Most arithmetic operations are supported with Rug types and
//!   primitive types on either side of the operator, for example
//!   `int >> 128`.
//!
//! ## Operators
//!
//! With Rust primitive types, arithmetic operators usually operate on
//! two values of the same type, for example `12i32 + 5i32`. Unlike
//! primitive types, conversion to and from Rug types can be
//! expensive, so the arithmetic operators are overloaded to work on
//! many combinations of Rug types and primitives.
//!
//! When at least one operand is an owned Rug type, the operation will
//! consume that type and return a Rug type. For example
//!
//! ```rust
//! # #[cfg(feature = "integer")] {
//! use rug::Integer;
//! let a = Integer::from(10);
//! let b = 5 - a;
//! assert_eq!(b, 5 - 10);
//! # }
//! ```
//!
//! Here `a` is consumed by the subtraction, and `b` is an owned
//! [`Integer`][rug int].
//!
//! If on the other hand there are no owned Rug types and there are
//! references instead, the returned value is not the final value, but
//! an intermediate value. For example
//!
//! ```rust
//! # #[cfg(feature = "integer")] {
//! use rug::Integer;
//! let (a, b) = (Integer::from(10), Integer::from(20));
//! let intermediate = &a - &b;
//! // This would fail to compile: assert_eq!(intermediate, -10);
//! let sub = Integer::from(intermediate);
//! assert_eq!(sub, -10);
//! # }
//! ```
//!
//! Here `a` and `b` are not consumed, and `intermediate` is not the
//! final value. It still needs to be converted or assigned into an
//! [`Integer`][rug int]. The reason is explained in the
//! [next](#intermediate-values) section.
//!
//! ## Intermediate values
//!
//! There are two main reasons why operations like `&a - &b` do not
//! return a Rug type:
//!
//! 1. Sometimes we need to assign the result to an object that
//!    already exists. Since Rug types require memory allocations,
//!    this can help reduce the number of allocations.
//! 2. For the [`Float`][rug flo] type, we need to know the precision
//!    when we create a value, and the operation itself cannot convey
//!    information about what precision is desired for the result. The
//!    same holds for the [`Complex`][rug com] type.
//!
//! There are two things that can be done with intermediate values:
//!
//! 1. Assign them using the [`Assign`][rug assign] trait or a similar
//!    trait, for example
//!    [`int.assign(intermediate)`][rug assign assign] and
//!    [`float.assign_round(intermediate, Round::Up)`][rug assr assr].
//! 2. Convert them to the final value using the [`From`][rust from]
//!    trait or a similar method, for example
//!    [`Integer::from(intermediate)`][rust from from] and
//!    [`Float::with_val(53, intermediate)`][rug flo withval].
//!
//! Let us consider a couple of examples.
//!
//! ```rust
//! # #[cfg(feature = "integer")] {
//! use rug::{Assign, Integer};
//! let mut buffer = Integer::new();
//! // ... buffer can be used and reused ...
//! let (a, b) = (Integer::from(10), Integer::from(20));
//! let intermediate = &a - &b;
//! buffer.assign(intermediate);
//! assert_eq!(buffer, -10);
//! # }
//! ```
//!
//! Here the assignment from `intermediate` into `buffer` does not
//! require an allocation unless the result does not fit in the
//! current capacity of `buffer`. If `&a - &b` returns an
//! [`Integer`][rug int] instead, then an allocation takes place even
//! if it is not necessary.
//!
//! ```rust
//! # #[cfg(feature = "float")] {
//! use rug::Float;
//! use rug::float::Constant;
//! // x has a precision of 10 bits, y has a precision of 50 bits
//! let x = Float::with_val(10, 180);
//! let y = Float::with_val(50, Constant::Pi);
//! let intermediate = &x / &y;
//! // z has a precision of 45 bits
//! let z = Float::with_val(45, intermediate);
//! assert!(57.295 < z && z < 57.296);
//! # }
//! ```
//!
//! The precision to use for the result depends on the requirements of
//! the algorithm being implemented. Here `c` is created with a
//! precision of 45.
//!
//! In these two examples, we could have left out the `intermediate`
//! variables altogether and used `buffer.assign(&a - &b)` and
//! `Float::with_val(45, &x / &y)` directly.
//!
//! Many operations can return intermediate values:
//!
//! * unary operators applied to references, for example `-&int`;
//! * binary operators applied to two references, for example
//!   `&int1 + &int2`;
//! * binary operators applied to a primitive and a reference, for
//!   example `&int * 10`;
//! * methods that take a reference, for example
//!   [`int.abs_ref()`][rug int absref];
//! * methods that take two references, for example
//!   [`int1.div_rem_ref(&int2)`][rug int divremref];
//! * string parsing, for example
//!   [`Integer::parse("12")`][rug int parse];
//! * and more…
//!
//! These operations return objects that can be stored in temporary
//! variables like `intermediate` in the last few examples. However,
//! the names of the types are not public, and consequently, the
//! intermediate values cannot be for example stored in a struct. If
//! you need to store the value in a struct, convert it to its final
//! type and value.
//!
//! As an example, the [documentation][rug int negref] for the
//! [`Neg`][rust neg] implementation of the reference
//! [`&Integer`][rug int] shows a return type called
//! [`NegRef`][rug int negref], but the name is blacked out and not
//! linkable in the documentation, as the intermediate type cannot be
//! named. The intermediate types obtained by operating on references
//! are named similar to `NegRef`, that is `OpRef` where `Op`
//! indicates what the operation is.
//!
//! ## Crate usage
//!
//! The Rug crate requires rustc version 1.18.0 or later.
//!
//! This crate depends on the low-level bindings in the
//! [gmp-mpfr-sys crate][sys crate], which provides Rust FFI
//! bindings for:
//!
//! * the [GNU Multiple Precision Arithmetic Library][gmp] (GMP),
//! * the [GNU MPFR Library][mpfr], a library for multiple-precision
//!   floating-point computations, and
//! * [GNU MPC][mpc], a library for the arithmetic of complex numbers
//!   with arbitrarily high precision.
//!
//! It can be helpful to refer to the documentation of the
//! [gmp-mpfr-sys crate][sys] and of the [GMP][gmp doc],
//! [MPFR][mpfr doc] and [MPC][mpc doc] libraries.
//!
//! ### Optional features
//!
//! The Rug crate has six optional features:
//!
//! 1. `integer`, enabled by default. Required for the
//!    [`Integer`][rug int] type and its supporting features.
//! 2. `rational`, enabled by default. Required for the
//!    [`Rational`][rug rat] type and its supporting features. This
//!    feature requires the `integer` feature.
//! 3. `float`, enabled by default. Required for the
//!    [`Float`][rug flo] type and its supporting features.
//! 4. `complex`, enabled by default. Required for the
//!    [`Complex`][rug flo] type and its supporting features. This
//!    feature requires the `float` feature.
//! 5. `rand`, enabled by default. Required for the
//!    [`RandState`][rug rand] type and its supporting features. This
//!    feature requires the `integer` feature.
//! 6. `serde`, disabled by default. This provides serialization
//!    support for the [`Integer`][rug int], [`Rational`][rug rat],
//!    [`Float`][rug flo] and [`Complex`][rug com] types, providing
//!    that they are enabled.
//!
//! The first five optional features are enabled by default; to use
//! features selectively, you can add the dependency like this to
//! [*Cargo.toml*][cargo deps]:
//!
//! ```toml
//! [dependencies.rug]
//! version = "0.10.0"
//! default-features = false
//! features = ["integer", "float", "rand"]
//! ```
//!
//! Here only the `integer`, `float` and `rand` features are enabled.
//! If none of the features are selected, the
//! [gmp-mpfr-sys crate][sys] is not required and thus not enabled. In
//! that case, only the [`Assign`][rug assign] trait and some
//! [other traits][rug ops] are provided by the crate.
//!
//! [cargo deps]: https://doc.rust-lang.org/cargo/guide/dependencies.html
//! [gmp doc]: https://tspiteri.gitlab.io/gmp-mpfr-sys/gmp/index.html
//! [gmp]: https://gmplib.org/
//! [gpl]: https://www.gnu.org/licenses/gpl-3.0.html
//! [lgpl]: https://www.gnu.org/licenses/lgpl-3.0.en.html
//! [mpc doc]: https://tspiteri.gitlab.io/gmp-mpfr-sys/mpc/index.html
//! [mpc]: http://www.multiprecision.org/
//! [mpfr doc]: https://tspiteri.gitlab.io/gmp-mpfr-sys/mpfr/index.html
//! [mpfr]: http://www.mpfr.org/
//! [rug assign assign]: trait.Assign.html#tymethod.assign
//! [rug assign]: trait.Assign.html
//! [rug assr assr]: ops/trait.AssignRound.html#tymethod.assign_round
//! [rug assr]: ops/trait.AssignRound.html
//! [rug com]: struct.Complex.html
//! [rug flo withval]: struct.Float.html#method.with_val
//! [rug flo]: struct.Float.html
//! [rug int absref]: struct.Integer.html#method.abs_ref
//! [rug int divremref]: struct.Integer.html#method.div_rem_ref
//! [rug int negref]: struct.Integer.html#impl-Neg-1
//! [rug int new]: struct.Integer.html#method.new
//! [rug int parse]: struct.Integer.html#method.parse
//! [rug int parseradix]: struct.Integer.html#method.parse_radix
//! [rug int]: struct.Integer.html
//! [rug ops]: ops/index.html
//! [rug rand]: rand/struct.RandState.html
//! [rug rat]: struct.Rational.html
//! [rust assignment]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#assignment-expressions
//! [rust copy]: https://doc.rust-lang.org/std/marker/trait.Copy.html
//! [rust from from]: https://doc.rust-lang.org/std/convert/trait.From.html#tymethod.from
//! [rust from]: https://doc.rust-lang.org/std/convert/trait.From.html
//! [rust i32]: https://doc.rust-lang.org/std/primitive.i32.html
//! [rust neg]: https://doc.rust-lang.org/std/ops/trait.Neg.html
//! [sys crate]: https://crates.io/crates/gmp-mpfr-sys
//! [sys gnu]: https://docs.rs/gmp-mpfr-sys/^1.1.0/gmp_mpfr_sys/index.html#building-on-gnulinux
//! [sys mac]: https://docs.rs/gmp-mpfr-sys/^1.1.0/gmp_mpfr_sys/index.html#building-on-macos
//! [sys win]: https://docs.rs/gmp-mpfr-sys/^1.1.0/gmp_mpfr_sys/index.html#building-on-windows
//! [sys]: https://docs.rs/gmp-mpfr-sys/^1.1.0/gmp_mpfr_sys/index.html
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/rug/0.10.0")]
#![doc(test(attr(deny(warnings))))]

#[cfg(any(feature = "integer", feature = "float"))]
extern crate gmp_mpfr_sys;

#[cfg(all(test, feature = "serde",
          any(feature = "integer", feature = "float")))]
extern crate bincode;
#[cfg(all(test, feature = "serde",
          any(feature = "integer", feature = "float")))]
extern crate byteorder;
#[cfg(all(feature = "serde", any(feature = "integer", feature = "float")))]
extern crate serde;
#[cfg(all(test, feature = "serde",
          any(feature = "integer", feature = "float")))]
#[macro_use]
extern crate serde_json;
#[cfg(all(test, feature = "serde",
          any(feature = "integer", feature = "float")))]
extern crate serde_test;

#[macro_use]
mod macros;
mod cast;
mod ext;
mod inner;
#[cfg(any(feature = "integer", feature = "float"))]
mod misc;
#[cfg(all(feature = "serde", any(feature = "integer", feature = "float")))]
mod serdeize;

/// Assigns to a number from another value.
///
/// # Examples
///
/// ```rust
/// use rug::Assign;
/// struct I(i32);
/// impl Assign<i16> for I {
///     fn assign(&mut self, rhs: i16) {
///         self.0 = rhs as i32;
///     }
/// }
/// let mut i = I(0);
/// i.assign(42_i16);
/// assert_eq!(i.0, 42);
/// ```
pub trait Assign<Src = Self> {
    /// Peforms the assignement.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "integer")] {
    /// use rug::{Assign, Integer};
    /// let mut i = Integer::from(15);
    /// assert_eq!(i, 15);
    /// i.assign(23);
    /// assert_eq!(i, 23);
    /// # }
    /// ```
    fn assign(&mut self, src: Src);
}

pub mod ops;
mod ops_prim;

#[cfg(feature = "integer")]
pub mod integer;
#[cfg(feature = "integer")]
pub use integer::big::Integer;

#[cfg(feature = "rational")]
pub mod rational;
#[cfg(feature = "rational")]
pub use rational::big::Rational;

#[cfg(feature = "float")]
pub mod float;
#[cfg(feature = "float")]
pub use float::big::Float;

#[cfg(feature = "complex")]
pub mod complex;
#[cfg(feature = "complex")]
pub use complex::big::Complex;

#[cfg(feature = "rand")]
pub mod rand;

#[cfg(test)]
#[cfg(any(feature = "integer", feature = "float"))]
mod tests {
    #[cfg(feature = "float")]
    use std::{f32, f64};
    use std::{i32, i64, u32, u64};

    pub const U32: &[u32] = &[0, 1, 1000, 1001, i32::MAX as u32 + 1, u32::MAX];
    pub const I32: &[i32] =
        &[i32::MIN, -1001, -1000, -1, 0, 1, 1000, 1001, i32::MAX];
    pub const U64: &[u64] = &[
        0,
        1,
        1000,
        1001,
        i32::MAX as u64 + 1,
        u32::MAX as u64 + 1,
        u64::MAX,
    ];
    pub const I64: &[i64] = &[
        i64::MIN,
        -(u32::MAX as i64) - 1,
        i32::MIN as i64 - 1,
        -1001,
        -1000,
        -1,
        0,
        1,
        1000,
        1001,
        i32::MAX as i64 + 1,
        u32::MAX as i64 + 1,
        i64::MAX,
    ];
    #[cfg(feature = "float")]
    pub const F32: &[f32] = &[
        -f32::NAN,
        f32::NEG_INFINITY,
        f32::MIN,
        -12.0e30,
        -2.0,
        -1.0,
        -f32::MIN_POSITIVE,
        -0.0,
        0.0,
        f32::MIN_POSITIVE,
        1.0,
        2.0,
        12.0e30,
        f32::MAX,
        f32::INFINITY,
        f32::NAN,
    ];
    #[cfg(feature = "float")]
    pub const F64: &[f64] = &[
        -f64::NAN,
        f64::NEG_INFINITY,
        f64::MIN,
        -12.0e43,
        -2.0,
        -1.0,
        -f64::MIN_POSITIVE,
        -0.0,
        0.0,
        f64::MIN_POSITIVE,
        1.0,
        2.0,
        12.0e43,
        f64::MAX,
        f64::INFINITY,
        f64::NAN,
    ];
}
