# Arbitrary-precision numbers

Rug provides integers and floating-point numbers with arbitrary
precision and correct rounding. Its main features are

* bignum [integers][`Integer`] with arbitrary precision,
* bignum [rational numbers][`Rational`] with arbitrary precision,
* multi-precision [floating-point numbers][`Float`] with correct
  rounding, and
* multi-precision [complex numbers][`Complex`] with correct rounding.

Rug is a high-level interface to the following [GNU] libraries:

* [GMP] for integers and rational numbers,
* [MPFR] for floating-point numbers, and
* [MPC] for complex numbers.

Rug is free software: you can redistribute it and/or modify it under
the terms of the GNU Lesser General Public License as published by the
Free Software Foundation, either version 3 of the License, or (at your
option) any later version. See the full text of the [GNU LGPL] and
[GNU GPL] for details.

## What’s new

### Version 1.2.0 news

* The implementations of [`Sum`] and [`Product`] for [`Integer`] and
  [`Rational`] were generalized to accept more types of iterator
  items.
* New methods [`Integer::keep_signed_bits`],
  [`Integer::keep_signed_bits_mut`] and
  [`Integer::keep_signed_bits_ref`] were added.
* New methods [`Integer::sum`] and [`Rational::sum`] were added.
* New methods [`Integer::dot`], [`Rational::dot`], [`Float::dot`] and
  [`Complex::dot`] were added.

[`Complex::dot`]: https://docs.rs/rug/~1.2/rug/struct.Complex.html#method.dot
[`Float::dot`]: https://docs.rs/rug/~1.2/rug/struct.Float.html#method.dot
[`Integer::dot`]: https://docs.rs/rug/~1.2/rug/struct.Integer.html#method.dot
[`Integer::keep_signed_bits_mut`]: https://docs.rs/rug/~1.2/rug/struct.Integer.html#method.keep_signed_bits_mut
[`Integer::keep_signed_bits_ref`]: https://docs.rs/rug/~1.2/rug/struct.Integer.html#method.keep_signed_bits_ref
[`Integer::keep_signed_bits`]: https://docs.rs/rug/~1.2/rug/struct.Integer.html#method.keep_signed_bits
[`Integer::sum`]: https://docs.rs/rug/~1.2/rug/struct.Integer.html#method.sum
[`Product`]: https://doc.rust-lang.org/nightly/std/iter/trait.Product.html
[`Rational::dot`]: https://docs.rs/rug/~1.2/rug/struct.Rational.html#method.dot
[`Rational::sum`]: https://docs.rs/rug/~1.2/rug/struct.Rational.html#method.sum
[`Sum`]: https://doc.rust-lang.org/nightly/std/iter/trait.Sum.html

### Version 1.1.0 news

* Support for [`i128`] and [`u128`] conversions and comparisons was
  added, conditional on compiler support.
* Conditional on compiler support, [`TryFrom`] conversions were
  implemented for conversions
  * from [`Integer`] values to integer primitives,
  * from floating-point primitives to [`Rational`] numbers, and
  * from [`Float`] values to [`Rational`] numbers.
* A new [`Float::get_significand`] method was added.
* New methods [`Float::u_pow_u`] and [`Float::i_pow_u`] were added.
* New methods [`from_digits`], [`to_digits`], [`assign_digits`],
  [`write_digits`] and [`significant_digits`] were added to
  [`Integer`], providing reading from and writing to slices of
  unsigned integer primitives.

[`Float::get_significand`]: https://docs.rs/rug/~1.1/rug/struct.Float.html#method.get_significand
[`Float::i_pow_u`]: https://docs.rs/rug/~1.1/rug/struct.Float.html#method.i_pow_u
[`Float::u_pow_u`]: https://docs.rs/rug/~1.1/rug/struct.Float.html#method.u_pow_u
[`TryFrom`]: https://doc.rust-lang.org/nightly/std/convert/trait.TryFrom.html
[`assign_digits`]: https://docs.rs/rug/~1.1/rug/struct.Integer.html#method.assign_digits
[`from_digits`]: https://docs.rs/rug/~1.1/rug/struct.Integer.html#method.from_digits
[`significant_digits`]: https://docs.rs/rug/~1.1/rug/struct.Integer.html#method.significant_digits
[`to_digits`]: https://docs.rs/rug/~1.1/rug/struct.Integer.html#method.to_digits
[`write_digits`]: https://docs.rs/rug/~1.1/rug/struct.Integer.html#method.write_digits

### Other releases

Details on other releases can be found in [*RELEASES.md*].

## Quick example

```rust
use rug::{Assign, Integer};
let mut int = Integer::new();
assert_eq!(int, 0);
int.assign(14);
assert_eq!(int, 14);

let decimal = "98_765_432_109_876_543_210";
int.assign(Integer::parse(decimal).unwrap());
assert!(int > 100_000_000);

let hex_160 = "ffff0000ffff0000ffff0000ffff0000ffff0000";
int.assign(Integer::parse_radix(hex_160, 16).unwrap());
assert_eq!(int.significant_bits(), 160);
int = (int >> 128) - 1;
assert_eq!(int, 0xfffe_ffff_u32);
```

* [`Integer::new()`][`Integer::new`] creates a new [`Integer`]
  intialized to zero.
* To assign values to Rug types, we use the [`Assign`] trait and its
  method [`assign`][`Assign::assign`]. We do not use the
  [assignment operator `=`][assignment] as that would drop the
  left-hand-side operand and replace it with a right-hand-side operand
  of the same type, which is not what we want here.
* Arbitrary precision numbers can hold numbers that are too large to
  fit in a primitive type. To assign such a number to the large types,
  we use strings rather than primitives; in the example this is done
  using [`Integer::parse`] and [`Integer::parse_radix`].
* We can compare Rug types to primitive types or to other Rug types
  using the normal comparison operators, for example
  `int > 100_000_000`.
* Most arithmetic operations are supported with Rug types and
  primitive types on either side of the operator, for example
  `int >> 128`.

## Using with primitive types

With Rust primitive types, arithmetic operators usually operate on two
values of the same type, for example `12i32 + 5i32`. Unlike primitive
types, conversion to and from Rug types can be expensive, so the
arithmetic operators are overloaded to work on many combinations of
Rug types and primitives. The following are provided:

1. Where they make sense, all arithmetic operators are overloaded to
   work with Rug types and the primitives [`i32`], [`u32`], [`f32`]
   and [`f64`].
2. Where they make sense, conversions using the [`From`] trait and
   assignments using the [`Assign`] trait are supported for all the
   primitives in 1 above as well as the other primitives [`i8`],
   [`i16`], [`i64`], [`isize`], [`u8`], [`u16`], [`u64`] and
   [`usize`]. This also applies to [`i128`] and [`u128`] if they are
   supported by the compiler.
3. Comparisons between Rug types and all the primitives listed in 1
   and 2 above are supported.
4. For [`Rational`] numbers, conversions and comparisons are also
   supported for tuples containing two integer primitives: the first
   is the numerator and the second is the denominator which must not
   be zero. The two primitives do not need to be of the same type.
5. For [`Complex`] numbers, conversions and comparisons are also
   supported for tuples containing two primitives: the first is the
   real part and the second is the imaginary part. The two primitives
   do not need to be of the same type.

## Operators

Operators are overloaded to work on Rug types alone or on a
combination of Rug types and Rust primitives. When at least one
operand is an owned value of a Rug type, the operation will consume
that value and return a value of the Rug type. For example

```rust
use rug::Integer;
let a = Integer::from(10);
let b = 5 - a;
assert_eq!(b, 5 - 10);
```

Here `a` is consumed by the subtraction, and `b` is an owned
[`Integer`].

If on the other hand there are no owned Rug types and there are
references instead, the returned value is not the final value, but an
incomplete-computation value. For example

```rust
use rug::Integer;
let (a, b) = (Integer::from(10), Integer::from(20));
let incomplete = &a - &b;
// This would fail to compile: assert_eq!(incomplete, -10);
let sub = Integer::from(incomplete);
assert_eq!(sub, -10);
```

Here `a` and `b` are not consumed, and `incomplete` is not the final
value. It still needs to be converted or assigned into an [`Integer`].
This is covered in more detail in the
[*Incomplete-computation values*] section.

### Shifting operations

The left shift `<<` and right shift `>>` operators support shifting by
negative values, for example `a << 5` is equivalent to `a >> -5`.

The shifting operators are also supported for the [`Float`] and
[`Complex`] number types, where they are equivalent to multiplication
or division by a power of two. Only the exponent of the value is
affected; the mantissa is unchanged.

### Exponentiation

Exponentiation (raising to a power) does not have a dedicated operator
in Rust. In order to perform exponentiation of Rug types, the [`Pow`]
trait has to be brought into scope, for example

```rust
use rug::Integer;
use rug::ops::Pow;
let base = Integer::from(10);
let power = base.pow(5);
assert_eq!(power, 100_000);
```

### Compound assignments to right-hand-side operands

Traits are provided for compound assignment to right-hand-side
operands. This can be useful for non-commutative operations like
subtraction. The names of the traits and their methods are similar to
Rust compound assignment traits, with the suffix “`Assign`” replaced
with “`From`”. For example the counterpart to [`SubAssign`] is
[`SubFrom`]:

```rust
use rug::Integer;
use rug::ops::SubFrom;
let mut rhs = Integer::from(10);
// set rhs = 100 - rhs
rhs.sub_from(100);
assert_eq!(rhs, 90);
```

## Incomplete-computation values

There are two main reasons why operations like `&a - &b` do not
perform a complete computation and return a Rug type:

1. Sometimes we need to assign the result to an object that already
   exists. Since Rug types require memory allocations, this can help
   reduce the number of allocations. (While the allocations might not
   affect performance noticeably for computationally intensive
   functions, they can have a much more significant effect on faster
   functions like addition.)
2. For the [`Float`] and [`Complex`] number types, we need to know the
   precision when we create a value, and the operation itself does not
   convey information about what precision is desired for the result.

There are two things that can be done with incomplete-computation
values:

1. Assign them to an existing object without unnecessary allocations.
   This is usually achieved using the [`Assign`] trait or a similar
   method, for example [`int.assign(incomplete)`][`Assign::assign`]
   and [`float.assign_round(incomplete, Round::Up)`][`assign_round`].
2. Convert them to the final value using the [`From`] trait or a
   similar method, for example
   [`Integer::from(incomplete)`][`From::from`] and
   [`Float::with_val(53, incomplete)`][`Float::with_val`].

Let us consider a couple of examples.

```rust
use rug::{Assign, Integer};
let mut buffer = Integer::new();
// ... buffer can be used and reused ...
let (a, b) = (Integer::from(10), Integer::from(20));
let incomplete = &a - &b;
buffer.assign(incomplete);
assert_eq!(buffer, -10);
```

Here the assignment from `incomplete` into `buffer` does not require
an allocation unless the result does not fit in the current capacity
of `buffer`. If `&a - &b` returned an [`Integer`] instead, then an
allocation would take place even if it is not necessary.

```rust
use rug::Float;
use rug::float::Constant;
// x has a precision of 10 bits
let x = Float::with_val(10, 180);
// y has a precision of 50 bits
let y = Float::with_val(50, Constant::Pi);
let incomplete = &x / &y;
// z has a precision of 45 bits
let z = Float::with_val(45, incomplete);
assert!(57.295 < z && z < 57.296);
```

The precision to use for the result depends on the requirements of the
algorithm being implemented. Here `z` is created with a precision
of 45.

Many operations can return incomplete-computation values:

* unary operators applied to references, for example `-&int`;
* binary operators applied to two references, for example
  `&int1 + &int2`;
* binary operators applied to a primitive and a reference, for example
  `&int * 10`;
* methods that take a reference, for example
  [`int.abs_ref()`][`Integer::abs_ref`];
* methods that take two references, for example
  [`int1.gcd_ref(&int2)`][`Integer::gcd_ref`];
* string parsing, for example
  [`Integer::parse("12")`][`Integer::parse`];
* and more.

These operations return objects that can be stored in temporary
variables like `incomplete` in the last few examples. However, the
names of the types are not public, and consequently, the
incomplete-computation values cannot be for example stored in a
struct. If you need to store the value in a struct, convert it to its
final type and value.

## Using Rug

Rug is available on [crates.io][rug crate]. To use Rug in your crate,
add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
rug = "1.0"
```

You also need to declare it by adding this to your crate root (usually
*lib.rs* or *main.rs*):

```rust
extern crate rug;
```

Rug requires rustc version 1.18.0 or later.

Rug also depends on the [GMP], [MPFR] and [MPC] libraries through the
low-level FFI bindings in the [gmp-mpfr-sys crate][sys crate], which
needs some setup to build; the [gmp-mpfr-sys documentation][sys] has
some details on usage under [GNU/Linux][sys gnu], [macOS][sys mac] and
[Windows][sys win].

## Optional features

The Rug crate has six optional features:

1. `integer`, enabled by default. Required for the [`Integer`] type
   and its supporting features.
2. `rational`, enabled by default. Required for the [`Rational`]
   number type and its supporting features. This feature requires the
   `integer` feature.
3. `float`, enabled by default. Required for the [`Float`] type and
   its supporting features.
4. `complex`, enabled by default. Required for the [`Complex`] number
   type and its supporting features. This feature requires the `float`
   feature.
5. `rand`, enabled by default. Required for the [`RandState`] type and
   its supporting features. This feature requires the `integer`
   feature.
6. `serde`, disabled by default. This provides serialization support
   for the [`Integer`], [`Rational`], [`Float`] and [`Complex`] number
   types, providing that they are enabled. This feature requires the
   [serde crate].

The first five optional features are enabled by default; to use
features selectively, you can add the dependency like this to
[*Cargo.toml*]:

```toml
[dependencies.rug]
version = "1.0"
default-features = false
features = ["integer", "float", "rand"]
```

Here only the `integer`, `float` and `rand` features are enabled. If
none of the features are selected, the [gmp-mpfr-sys crate][sys] is
not required and thus not enabled. In that case, only the [`Assign`]
trait and the traits that are in the [`ops`] module are provided by
the crate.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*Incomplete-computation values*]: #incomplete-computation-values
[*RELEASES.md*]: https://gitlab.com/tspiteri/rug/blob/master/RELEASES.md
[GMP]: https://gmplib.org/
[GNU GPL]: https://www.gnu.org/licenses/gpl-3.0.html
[GNU LGPL]: https://www.gnu.org/licenses/lgpl-3.0.en.html
[GNU]: https://www.gnu.org/
[MPC]: http://www.multiprecision.org/mpc/
[MPFR]: http://www.mpfr.org/
[`Assign::assign`]: https://docs.rs/rug/~1.1/rug/trait.Assign.html#tymethod.assign
[`Assign`]: https://docs.rs/rug/~1.1/rug/trait.Assign.html
[`Complex`]: https://docs.rs/rug/~1.1/rug/struct.Complex.html
[`Float::with_val`]: https://docs.rs/rug/~1.1/rug/struct.Float.html#method.with_val
[`Float`]: https://docs.rs/rug/~1.1/rug/struct.Float.html
[`From::from`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html#tymethod.from
[`From`]: https://doc.rust-lang.org/nightly/std/convert/trait.From.html
[`Integer::abs_ref`]: https://docs.rs/rug/~1.1/rug/struct.Integer.html#method.abs_ref
[`Integer::gcd_ref`]: https://docs.rs/rug/~1.1/rug/struct.Integer.html#method.gcd_ref
[`Integer::new`]: https://docs.rs/rug/~1.1/rug/struct.Integer.html#method.new
[`Integer::parse_radix`]: https://docs.rs/rug/~1.1/rug/struct.Integer.html#method.parse_radix
[`Integer::parse`]: https://docs.rs/rug/~1.1/rug/struct.Integer.html#method.parse
[`Integer`]: https://docs.rs/rug/~1.1/rug/struct.Integer.html
[`Pow`]: https://docs.rs/rug/~1.1/rug/ops/trait.Pow.html
[`RandState`]: https://docs.rs/rug/~1.1/rug/rand/struct.RandState.html
[`Rational`]: https://docs.rs/rug/~1.1/rug/struct.Rational.html
[`SubAssign`]: https://doc.rust-lang.org/nightly/std/ops/trait.SubAssign.html
[`SubFrom`]: https://docs.rs/rug/~1.1/rug/ops/trait.SubFrom.html
[`assign_round`]: https://docs.rs/rug/~1.1/rug/ops/trait.AssignRound.html#tymethod.assign_round
[`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
[`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
[`ops`]: https://docs.rs/rug/~1.1/rug/ops/index.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
[assignment]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#assignment-expressions
[rug crate]: https://crates.io/crates/rug
[serde crate]: https://crates.io/crates/serde
[sys crate]: https://crates.io/crates/gmp-mpfr-sys
[sys gnu]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/index.html#building-on-gnulinux
[sys mac]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/index.html#building-on-macos
[sys win]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/index.html#building-on-windows
[sys]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/index.html
