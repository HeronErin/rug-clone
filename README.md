# Arbitrary-precision numbers

Rug provides integers and floating-point numbers with arbitrary
precision and correct rounding. Its main features are

* bignum [integers][rug int] with arbitrary precision,
* bignum [rational numbers][rug rat] with arbitrary precision,
* multi-precision [floating-point numbers][rug flo] with correct
  rounding, and
* multi-precision [complex numbers][rug com] with correct rounding.

This crate is free software: you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version. See the full text of the
[GNU LGPL][lgpl] and [GNU GPL][gpl] for details.

## Version 1.0.0 coming soon

Version 0.10.0 is meant to be the last release before version 1.0.0.
Unless some issue is discovered, version 1.0.0 will be like version
0.10.0 with all the deprecated items removed.

## Quick example

For many operations, you can use the arbitrary-precision types such as
[`Integer`][rug int] like you use primitive types such as
[`i32`][rust i32]. However Rug types do not implement
[`Copy`][rust copy]. This is because they store their digits in the
heap, not on the stack, and copying them could involve an expensive
deep copy.

This code uses the [`Integer`][rug int] type:

```rust
use rug::{Assign, Integer};
let mut int = Integer::new();
assert_eq!(int, 0);
int.assign(14);
assert_eq!(int, 14);
let decimal = "12_345_678_901_234_567_890";
int.assign(Integer::parse(decimal).unwrap());
assert!(int > 100_000_000);
let hex_160 = "ffff0000ffff0000ffff0000ffff0000ffff0000";
int.assign(Integer::parse_radix(hex_160, 16).unwrap());
assert_eq!(int.significant_bits(), 160);
int = (int >> 128) - 1;
assert_eq!(int, 0xfffe_ffff_u32);
```

* [`Integer::new()`][rug int new] creates a new [`Integer`][rug int]
  intialized to zero.
* To assign values to Rug types, we use the [`Assign`][rug assign]
  trait and its method [`assign`][rug assign assign]. We do not use
  the [assignment operator `=`][rust assignment] as that would move
  the left-hand-side operand, which would need to have the same type.
* Arbitrary precision numbers can hold numbers that are too large to
  fit in a primitive type. To assign such a number to the large types,
  we use strings rather than primitives; in the example this is done
  using [`Integer::parse`][rug int parse] and
  [`Integer::parse_radix`][rug int parseradix].
* We can compare Rug types to primitive types or to other Rug types
  using the normal comparison operators, for example
  `int > 100_000_000_000`.
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
   work with Rug types and the primitives [`i32`][rust i32],
   [`u32`][rust u32], [`f32`][rust f32] and [`f64`][rust f64].
2. Where they make sense, conversions using the [`From`][rust from]
   trait and assignments using the [`Assign`][rug assign] trait are
   supported for all the primitives in 1 above as well as the other
   primitives [`i8`][rust i8], [`i16`][rust i16], [`i64`][rust i64],
   [`isize`][rust isize], [`u8`][rust u8], [`u16`][rust u16],
   [`u64`][rust u64] and [`usize`][rust usize].
3. Comparisons between Rug types and all the primitives listed in
   1 and 2 above are supported.
4. For [`Rational`][rug rat] numbers, operations are also supported
   for tuples containing two primitives: the first is the numerator
   and the second is the denominator which cannot be zero. The two
   primitives do not need to have the same type.
5. For [`Complex`][rug com] numbers, operations are also supported for
   tuples containing two primitives: the first is the real part and
   the second is the imaginary part. The two primitives do not need to
   have the same type.

## Operators

Operators are overloaded to work on Rug types alone or on a
combination of Rug types and Rust primitives. When at least one
operand is an owned Rug type, the operation will consume that type and
return a Rug type. For example

```rust
use rug::Integer;
let a = Integer::from(10);
let b = 5 - a;
assert_eq!(b, 5 - 10);
```

Here `a` is consumed by the subtraction, and `b` is an owned
[`Integer`][rug int].

If on the other hand there are no owned Rug types and there are
references instead, the returned value is not the final value, but an
incomplete computation value. For example

```rust
use rug::Integer;
let (a, b) = (Integer::from(10), Integer::from(20));
let incomplete = &a - &b;
// This would fail to compile: assert_eq!(incomplete, -10);
let sub = Integer::from(incomplete);
assert_eq!(sub, -10);
```

Here `a` and `b` are not consumed, and `incomplete` is not the final
value. It still needs to be converted or assigned into an
[`Integer`][rug int]. The reason is explained in the section about
[incomplete computation values](#incomplete-computation-values).

The left shift `<<` and right shift `>>` operators support shifting by
negative values, for example `a << 5` is equivalent to `a >> -5`. The
shifting operators are also supported for the [`Float`][rug flo] and
[`Complex`][rug com] types, where they are equivalent to
multiplication or division by a power of two.

## Incomplete computation values

There are two main reasons why operations like `&a - &b` do not
perform a complete computation and return a Rug type:

1. Sometimes we need to assign the result to an object that already
   exists. Since Rug types require memory allocations, this can help
   reduce the number of allocations.
2. For the [`Float`][rug flo] type, we need to know the precision when
   we create a value, and the operation itself does not convey
   information about what precision is desired for the result. The
   same holds for the [`Complex`][rug com] type.

There are two things that can be done with incomplete computation
values:

1. Assign them to an existing object without unnecessary allocations.
   This is usually achieved using the [`Assign`][rug assign] trait or
   a similar method, for example
   [`int.assign(incomplete)`][rug assign assign] and
   [`float.assign_round(incomplete, Round::Up)`][rug assr assr].
2. Convert them to the final value using the [`From`][rust from] trait
   or a similar method, for example
   [`Integer::from(incomplete)`][rust from from] and
   [`Float::with_val(53, incomplete)`][rug flo withval].

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
of `buffer`. And even then, the reallocation would take place before
the computation, so no copies are involved. If `&a - &b` returned an
[`Integer`][rug int] instead, then an allocation would take place even
if it is not necessary.

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
algorithm being implemented. Here `z` is created with a precision of
45.

In these two examples, we could have left out the `incomplete`
variables altogether and used `buffer.assign(&a - &b)` and
`Float::with_val(45, &x / &y)` directly.

Many operations can return incomplete computation values:

* unary operators applied to references, for example `-&int`;
* binary operators applied to two references, for example
  `&int1 + &int2`;
* binary operators applied to a primitive and a reference, for example
  `&int * 10`;
* methods that take a reference, for example
  [`int.abs_ref()`][rug int absref];
* methods that take two references, for example
  [`int1.div_rem_ref(&int2)`][rug int divremref];
* string parsing, for example [`Integer::parse("12")`][rug int parse];
* and more…

These operations return objects that can be stored in temporary
variables like `incomplete` in the last few examples. However, the
names of the types are not public, and consequently, the incomplete
computation values cannot be for example stored in a struct. If you
need to store the value in a struct, convert it to its final type and
value.

## Using Rug

Rug is available on [crates.io][rug crate]. To use Rug in your crate,
add it as a dependency inside [*Cargo.toml*][cargo deps]:

```toml
[dependencies]
rug = "0.10.0"
```

You also need to declare it by adding this to your crate root (usually
*lib.rs* or *main.rs*):

```rust
extern crate rug;
```

Rug requires rustc version 1.18.0 or later.

Rug also depends on the low-level bindings in the
[gmp-mpfr-sys crate][sys crate] which needs some setup to build; the
[gmp-mpfr-sys documentation][sys] has some details on usage under
[GNU/Linux][sys gnu], [macOS][sys mac] and [Windows][sys win].

## Optional features

The Rug crate has six optional features:

1. `integer`, enabled by default. Required for the
   [`Integer`][rug int] type and its supporting features.
2. `rational`, enabled by default. Required for the
   [`Rational`][rug rat] type and its supporting features. This
   feature requires the `integer` feature.
3. `float`, enabled by default. Required for the [`Float`][rug flo]
   type and its supporting features.
4. `complex`, enabled by default. Required for the
   [`Complex`][rug flo] type and its supporting features. This feature
   requires the `float` feature.
5. `rand`, enabled by default. Required for the
   [`RandState`][rug rand] type and its supporting features. This
   feature requires the `integer` feature.
6. `serde`, disabled by default. This provides serialization support
   for the [`Integer`][rug int], [`Rational`][rug rat],
   [`Float`][rug flo] and [`Complex`][rug com] types, providing that
   they are enabled. This feature requires the
   [serde crate][serde crate].

The first five optional features are enabled by default; to use
features selectively, you can add the dependency like this to
[*Cargo.toml*][cargo deps]:

```toml
[dependencies.rug]
version = "0.10.0"
default-features = false
features = ["integer", "float", "rand"]
```

Here only the `integer`, `float` and `rand` features are enabled. If
none of the features are selected, the [gmp-mpfr-sys crate][sys] is
not required and thus not enabled. In that case, only the
[`Assign`][rug assign] trait and some [other traits][rug ops] are
provided by the crate.

[cargo deps]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[gmp doc]: https://tspiteri.gitlab.io/gmp-mpfr-sys/gmp/index.html
[gmp]: https://gmplib.org/
[gpl]: https://www.gnu.org/licenses/gpl-3.0.html
[lgpl]: https://www.gnu.org/licenses/lgpl-3.0.en.html
[mpc doc]: https://tspiteri.gitlab.io/gmp-mpfr-sys/mpc/index.html
[mpc]: http://www.multiprecision.org/
[mpfr doc]: https://tspiteri.gitlab.io/gmp-mpfr-sys/mpfr/index.html
[mpfr]: http://www.mpfr.org/
[rug assign assign]: https://docs.rs/rug/0.10.0/rug/trait.Assign.html#tymethod.assign
[rug assign]: https://docs.rs/rug/0.10.0/rug/trait.Assign.html
[rug assr assr]: https://docs.rs/rug/0.10.0/rug/ops/trait.AssignRound.html#tymethod.assign_round
[rug assr]: https://docs.rs/rug/0.10.0/rug/ops/trait.AssignRound.html
[rug com]: https://docs.rs/rug/0.10.0/rug/struct.Complex.html
[rug crate]: https://crates.io/crates/rug
[rug flo withval]: https://docs.rs/rug/0.10.0/rug/struct.Float.html#method.with_val
[rug flo]: https://docs.rs/rug/0.10.0/rug/struct.Float.html
[rug int absref]: https://docs.rs/rug/0.10.0/rug/struct.Integer.html#method.abs_ref
[rug int divremref]: https://docs.rs/rug/0.10.0/rug/struct.Integer.html#method.div_rem_ref
[rug int negref]: https://docs.rs/rug/0.10.0/rug/struct.Integer.html#impl-Neg-1
[rug int new]: https://docs.rs/rug/0.10.0/rug/struct.Integer.html#method.new
[rug int parse]: https://docs.rs/rug/0.10.0/rug/struct.Integer.html#method.parse
[rug int parseradix]: https://docs.rs/rug/0.10.0/rug/struct.Integer.html#method.parse_radix
[rug int]: https://docs.rs/rug/0.10.0/rug/struct.Integer.html
[rug ops]: https://docs.rs/rug/0.10.0/rug/ops/index.html
[rug rand]: https://docs.rs/rug/0.10.0/rug/rand/struct.RandState.html
[rug rat]: https://docs.rs/rug/0.10.0/rug/struct.Rational.html
[rust assignment]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#assignment-expressions
[rust copy]: https://doc.rust-lang.org/std/marker/trait.Copy.html
[rust f32]: https://doc.rust-lang.org/std/primitive.f32.html
[rust f64]: https://doc.rust-lang.org/std/primitive.f64.html
[rust from from]: https://doc.rust-lang.org/std/convert/trait.From.html#tymethod.from
[rust from]: https://doc.rust-lang.org/std/convert/trait.From.html
[rust i16]: https://doc.rust-lang.org/std/primitive.i16.html
[rust i32]: https://doc.rust-lang.org/std/primitive.i32.html
[rust i64]: https://doc.rust-lang.org/std/primitive.i64.html
[rust i8]: https://doc.rust-lang.org/std/primitive.i8.html
[rust isize]: https://doc.rust-lang.org/std/primitive.isize.html
[rust neg]: https://doc.rust-lang.org/std/ops/trait.Neg.html
[rust u16]: https://doc.rust-lang.org/std/primitive.u16.html
[rust u32]: https://doc.rust-lang.org/std/primitive.u32.html
[rust u64]: https://doc.rust-lang.org/std/primitive.u64.html
[rust u8]: https://doc.rust-lang.org/std/primitive.u8.html
[rust usize]: https://doc.rust-lang.org/std/primitive.usize.html
[serde crate]: https://crates.io/crates/serde
[sys crate]: https://crates.io/crates/gmp-mpfr-sys
[sys gnu]: https://docs.rs/gmp-mpfr-sys/^1.1.0/gmp_mpfr_sys/index.html#building-on-gnulinux
[sys mac]: https://docs.rs/gmp-mpfr-sys/^1.1.0/gmp_mpfr_sys/index.html#building-on-macos
[sys win]: https://docs.rs/gmp-mpfr-sys/^1.1.0/gmp_mpfr_sys/index.html#building-on-windows
[sys]: https://docs.rs/gmp-mpfr-sys/^1.1.0/gmp_mpfr_sys/index.html
