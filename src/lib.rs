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
//! Rug provides integers and floating-point numbers with arbitrary
//! precision and correct rounding. Its main features are
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
//! 1.0.0. Unless some issue is discovered, version 1.0.0 will be like
//! version 0.10.0 with all the deprecated items removed.
//!
//! ## Quick example
//!
//! For many operations, you can use the arbitrary-precision types
//! such as [`Integer`][rug int] like you use primitive types such as
//! [`i32`][rust i32]. However Rug types do not implement
//! [`Copy`][rust copy]. This is because they store their digits in
//! the heap, not on the stack, and copying them could involve an
//! expensive deep copy.
//!
//! This code uses the [`Integer`][rug int] type:
//!
//! ```rust
//! # #[cfg(feature = "integer")] {
//! use rug::{Assign, Integer};
//! let mut int = Integer::new();
//! assert_eq!(int, 0);
//! int.assign(14);
//! assert_eq!(int, 14);
//!
//! let decimal = "98_765_432_109_876_543_210";
//! int.assign(Integer::parse(decimal).unwrap());
//! assert!(int > 100_000_000);
//!
//! let hex_160 = "ffff0000ffff0000ffff0000ffff0000ffff0000";
//! int.assign(Integer::parse_radix(hex_160, 16).unwrap());
//! assert_eq!(int.significant_bits(), 160);
//! int = (int >> 128) - 1;
//! assert_eq!(int, 0xfffe_ffff_u32);
//! # }
//! ```
//!
//! * [`Integer::new()`][rug int new] creates a new
//!   [`Integer`][rug int] intialized to zero.
//! * To assign values to Rug types, we use the [`Assign`][rug assign]
//!   trait and its method [`assign`][rug assign assign]. We do not
//!   use the [assignment operator `=`][rust assignment] as that would
//!   drop the left-hand-side operand and replace it with the
//!   right-hand-side operand, which is not what we want here.
//! * Arbitrary precision numbers can hold numbers that are too large
//!   to fit in a primitive type. To assign such a number to the large
//!   types, we use strings rather than primitives; in the example
//!   this is done using [`Integer::parse`][rug int parse] and
//!   [`Integer::parse_radix`][rug int parseradix].
//! * We can compare Rug types to primitive types or to other Rug
//!   types using the normal comparison operators, for example
//!   `int > 100_000_000_000`.
//! * Most arithmetic operations are supported with Rug types and
//!   primitive types on either side of the operator, for example
//!   `int >> 128`.
//!
//! ## Using with primitive types
//!
//! With Rust primitive types, arithmetic operators usually operate on
//! two values of the same type, for example `12i32 + 5i32`. Unlike
//! primitive types, conversion to and from Rug types can be
//! expensive, so the arithmetic operators are overloaded to work on
//! many combinations of Rug types and primitives. The following are
//! provided:
//!
//! 1. Where they make sense, all arithmetic operators are overloaded
//!    to work with Rug types and the primitives [`i32`][rust i32],
//!    [`u32`][rust u32], [`f32`][rust f32] and [`f64`][rust f64].
//! 2. Where they make sense, conversions using the
//!    [`From`][rust from] trait and assignments using the
//!    [`Assign`][rug assign] trait are supported for all the
//!    primitives in 1 above as well as the other primitives
//!    [`i8`][rust i8], [`i16`][rust i16], [`i64`][rust i64],
//!    [`isize`][rust isize], [`u8`][rust u8], [`u16`][rust u16],
//!    [`u64`][rust u64] and [`usize`][rust usize].
//! 3. Comparisons between Rug types and all the primitives listed in
//!    1 and 2 above are supported.
//! 4. For [`Rational`][rug rat] numbers, conversions and comparisons
//!    are also supported for tuples containing two integer
//!    primitives: the first is the numerator and the second is the
//!    denominator which must not be zero. The two primitives do not
//!    need to be of the same type.
//! 5. For [`Complex`][rug com] numbers, conversions are also
//!    supported for tuples containing two primitives: the first is
//!    the real part and the second is the imaginary part. The two
//!    primitives do not need to be of the same type.
//!
//! ## Operators
//!
//! Operators are overloaded to work on Rug types alone or on a
//! combination of Rug types and Rust primitives. When at least one
//! operand is an owned Rug type, the operation will consume that type
//! and return a Rug type. For example
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
//! an incomplete computation value. For example
//!
//! ```rust
//! # #[cfg(feature = "integer")] {
//! use rug::Integer;
//! let (a, b) = (Integer::from(10), Integer::from(20));
//! let incomplete = &a - &b;
//! // This would fail to compile: assert_eq!(incomplete, -10);
//! let sub = Integer::from(incomplete);
//! assert_eq!(sub, -10);
//! # }
//! ```
//!
//! Here `a` and `b` are not consumed, and `incomplete` is not the
//! final value. It still needs to be converted or assigned into an
//! [`Integer`][rug int]. This is covered in more detail in the
//! [*Incomplete computation values*](#incomplete-computation-values)
//! section.
//!
//! ### Shifting operations
//!
//! The left shift `<<` and right shift `>>` operators support
//! shifting by negative values, for example `a << 5` is equivalent to
//! `a >> -5`.
//!
//! The shifting operators are also supported for the
//! [`Float`][rug flo] and [`Complex`][rug com] types, where they are
//! equivalent to multiplication or division by a power of two. Only
//! the exponent of the value is affected; the mantissa is unchanged.
//!
//! ### Exponentiation
//!
//! Exponentiation (raising to a power) does not have a dedicated
//! operator in Rust. In order to perform exponentiation of Rug types,
//! the [`Pow`][rug pow] trait has to be brought in scope, for example
//!
//! ```rust
//! # #[cfg(feature = "integer")] {
//! use rug::Integer;
//! use rug::ops::Pow;
//! let base = Integer::from(10);
//! let power = base.pow(5);
//! assert_eq!(power, 100_000);
//! # }
//! ```
//!
//! ### Compound assignments to right-hand-side operands
//!
//! Traits are provided for compound assignment to right-hand-side
//! operands. This can be useful for non-commutative operations like
//! subtraction. The names of the traits and their methods are similar
//! to Rust compound assignment traits, with the suffix `Assign`
//! replaced with `From`. For example the counterpart to
//! [`SubAssign`][rust subassign] is [`SubFrom`][rug subfrom]:
//!
//! ```rust
//! # #[cfg(feature = "integer")] {
//! use rug::Integer;
//! use rug::ops::SubFrom;
//! let mut rhs = Integer::from(10);
//! // set rhs = 100 - rhs
//! rhs.sub_from(100);
//! assert_eq!(rhs, 90);
//! # }
//! ```
//!
//! ## Incomplete computation values
//!
//! There are two main reasons why operations like `&a - &b` do not
//! perform a complete computation and return a Rug type:
//!
//! 1. Sometimes we need to assign the result to an object that
//!    already exists. Since Rug types require memory allocations,
//!    this can help reduce the number of allocations. (While the
//!    allocations might not affect performance noticeably for
//!    computationally intensive functions, they can have a much more
//!    significant effect on faster functions like addition.)
//! 2. For the [`Float`][rug flo] type, we need to know the precision
//!    when we create a value, and the operation itself does not
//!    convey information about what precision is desired for the
//!    result. The same holds for the [`Complex`][rug com] type.
//!
//! There are two things that can be done with incomplete computatin
//! values:
//!
//! 1. Assign them to an existing object without unnecessary
//!    allocations. This is usually achieved using the
//!    [`Assign`][rug assign] trait or a similar method, for example
//!    [`int.assign(incomplete)`][rug assign assign] and
//!    [`float.assign_round(incomplete, Round::Up)`][rug assr assr].
//! 2. Convert them to the final value using the [`From`][rust from]
//!    trait or a similar method, for example
//!    [`Integer::from(incomplete)`][rust from from] and
//!    [`Float::with_val(53, incomplete)`][rug flo withval].
//!
//! Let us consider a couple of examples.
//!
//! ```rust
//! # #[cfg(feature = "integer")] {
//! use rug::{Assign, Integer};
//! let mut buffer = Integer::new();
//! // ... buffer can be used and reused ...
//! let (a, b) = (Integer::from(10), Integer::from(20));
//! let incomplete = &a - &b;
//! buffer.assign(incomplete);
//! assert_eq!(buffer, -10);
//! # }
//! ```
//!
//! Here the assignment from `incomplete` into `buffer` does not
//! require an allocation unless the result does not fit in the
//! current capacity of `buffer`. And even then, the reallocation
//! would take place before the computation, so no copies are
//! involved. If `&a - &b` returned an [`Integer`][rug int] instead,
//! then an allocation would take place even if it is not necessary.
//!
//! ```rust
//! # #[cfg(feature = "float")] {
//! use rug::Float;
//! use rug::float::Constant;
//! // x has a precision of 10 bits
//! let x = Float::with_val(10, 180);
//! // y has a precision of 50 bits
//! let y = Float::with_val(50, Constant::Pi);
//! let incomplete = &x / &y;
//! // z has a precision of 45 bits
//! let z = Float::with_val(45, incomplete);
//! assert!(57.295 < z && z < 57.296);
//! # }
//! ```
//!
//! The precision to use for the result depends on the requirements of
//! the algorithm being implemented. Here `z` is created with a
//! precision of 45.
//!
//! In these two examples, we could have left out the `incomplete`
//! variables altogether and used `buffer.assign(&a - &b)` and
//! `Float::with_val(45, &x / &y)` directly.
//!
//! Many operations can return incomplete computation values:
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
//! variables like `incomplete` in the last few examples. However, the
//! names of the types are not public, and consequently, the
//! incomplete computation values cannot be for example stored in a
//! struct. If you need to store the value in a struct, convert it to
//! its final type and value.
//!
//! ## Using Rug
//!
//! Rug is available on [crates.io][rug crate]. To use Rug in your
//! crate, add it as a dependency inside [*Cargo.toml*][cargo deps]:
//!
//! ```toml
//! [dependencies]
//! rug = "0.10.0"
//! ```
//!
//! You also need to declare it by adding this to your crate root
//! (usually *lib.rs* or *main.rs*):
//!
//! ```rust
//! extern crate rug;
//! # fn main() {}
//! ```
//!
//! Rug requires rustc version 1.18.0 or later.
//!
//! Rug also depends on the low-level bindings in the
//! [gmp-mpfr-sys crate][sys crate] which needs some setup to build;
//! the [gmp-mpfr-sys documentation][sys] has some details on usage
//! under [GNU/Linux][sys gnu], [macOS][sys mac] and
//! [Windows][sys win].
//!
//! ## Optional features
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
//!    that they are enabled. This features requires the
//!    [serde crate][serde crate].
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
//! [rug crate]: https://crates.io/crates/rug
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
//! [rug pow]: ops/trait.Pow.html
//! [rug rand]: rand/struct.RandState.html
//! [rug rat]: struct.Rational.html
//! [rug subfrom]: ops/trait.SubFrom.html
//! [rust assignment]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#assignment-expressions
//! [rust copy]: https://doc.rust-lang.org/std/marker/trait.Copy.html
//! [rust f32]: https://doc.rust-lang.org/std/primitive.f32.html
//! [rust f64]: https://doc.rust-lang.org/std/primitive.f64.html
//! [rust from from]: https://doc.rust-lang.org/std/convert/trait.From.html#tymethod.from
//! [rust from]: https://doc.rust-lang.org/std/convert/trait.From.html
//! [rust i16]: https://doc.rust-lang.org/std/primitive.i16.html
//! [rust i32]: https://doc.rust-lang.org/std/primitive.i32.html
//! [rust i64]: https://doc.rust-lang.org/std/primitive.i64.html
//! [rust i8]: https://doc.rust-lang.org/std/primitive.i8.html
//! [rust isize]: https://doc.rust-lang.org/std/primitive.isize.html
//! [rust neg]: https://doc.rust-lang.org/std/ops/trait.Neg.html
//! [rust subassign]: https://doc.rust-lang.org/std/ops/trait.SubAssign.html
//! [rust u16]: https://doc.rust-lang.org/std/primitive.u16.html
//! [rust u32]: https://doc.rust-lang.org/std/primitive.u32.html
//! [rust u64]: https://doc.rust-lang.org/std/primitive.u64.html
//! [rust u8]: https://doc.rust-lang.org/std/primitive.u8.html
//! [rust usize]: https://doc.rust-lang.org/std/primitive.usize.html
//! [serde crate]: https://crates.io/crates/serde
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
