# Arbitrary-precision numbers

The Rug crate provides integers and floating-point numbers with
arbitrary precision and correct rounding. Its main features are

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

## Getting started

### Setting up the crate

To use Rug in your crate, add it as a dependency inside
[*Cargo.toml*][cargo deps]:

```toml
[dependencies]
rug = "0.9.3"
```

This crate depends on the low-level bindings in the
[gmp-mpfr-sys crate][sys crate] which needs some setup to build; the
[gmp-mpfr-sys documentation][sys] has some details on usage under
[GNU/Linux][sys gnu], [macOS][sys mac] and [Windows][sys win].

You also need to declare Rug by adding this to your crate root:

```rust
extern crate rug;
```

More details are available in the [Crate usage](#crate-usage) section
below.

### Basic example

For many operations, you can use the arbitrary-precision types such as
[`Integer`][rug int] like you use primitive types such as
[`i32`][rust i32]. The main difference is that the Rug types do not
implement [`Copy`][rust copy]. This is because they store their digits
in the heap, not on the stack, and copying them could involve an
expensive deep copy.

This code uses the [`Integer`][rug int] type:

```rust
extern crate rug;
use rug::{Assign, Integer};

fn main() {
    let mut int = Integer::new();
    assert_eq!(int, 0);
    int.assign(14);
    assert_eq!(int, 14);
    int.assign(Integer::parse("12_345_678_901_234_567_890").unwrap());
    assert!(int > 100_000_000);
    let hex_160 = "ffff0000ffff0000ffff0000ffff0000ffff0000";
    int.assign(Integer::parse_radix(hex_160, 16).unwrap());
    assert_eq!(int.significant_bits(), 160);
    int = (int >> 128) - 1;
    assert_eq!(int, 0xfffe_ffff_u32);
}
```

Some points from this example follow:

* [`Integer::new()`][rug int new] creates a new [`Integer`][rug int]
  intialized to zero.
* To assign values to Rug types, we use the [`Assign`][rug assign]
  trait and its method [`assign`][rug assign assign]. We do not use
  the [assignment operator `=`][rust assignment] as that would move
  the left-hand-side operand, which would have the same type.
* Arbitrary precision numbers can hold numbers that are too large to
  fit in a primitive type. To assign such a number to the large types,
  we use strings rather than primitives; in the example this is done
  using both [`Integer::parse`][rug int parse] and
  [`Integer::parse_radix`][rug int parseradix].
* We can compare Rug types with primitive types or with other Rug
  types using the normal comparison operators, for example
  `int > 100_000_000_000`.
* Most arithmetic operations are supported with Rug types and
  primitive types on either side of the operator, for example
  `int >> 128`.

## Operators

With Rust primitive types, arithmetic operators usually operate on two
values of the same type, for example `12i32 + 5i32`. Unlike primitive
types, conversion to and from Rug types can be expensive, so the
arithmetic operators are overloaded to work on many combinations of
Rug types and primitives.

When at least one operand is an owned Rug type, the operation will
consume that type and return a Rug type. For example

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
intermediate value. For example

```rust
use rug::Integer;
let (a, b) = (Integer::from(10), Integer::from(20));
let intermediate = &a - &b;
// This would fail to compile: assert_eq!(intermediate, -10);
let sub = Integer::from(intermediate);
assert_eq!(sub, -10);
```

Here `a` and `b` are not consumed, and `intermediate` is not the final
value. It still needs to be converted or assigned into an
[`Integer`][rug int]. The reason is explained in the
[next](#intermediate-values) section.

## Intermediate values

There are two main reasons why operations like `&a - &b` do not return
a Rug type:

1. Sometimes we need to assign the result to an object that already
   exists. Since Rug types require memory allocations, this can help
   reduce the number of allocations.
2. For the [`Float`][rug flo] type, we need to know the precision when
   we create a value, and the operation itself cannot convey
   information about what precision is desired for the result. The
   same holds for the [`Complex`][rug com] type.

There are two things that can be done with intermediate values:

1. Assign them using the [`Assign`][rug assign] trait or a similar
   trait, for example [`int.assign(intermediate)`][rug assign assign]
   and [`float.assign_round(intermediate, Round::Up)`][rug assr assr].
2. Convert them to the final value using the [`From`][rust from] trait
   or a similar method, for example
   [`Integer::from(intermediate)`][rust from from] and
   [`Float::with_val(53, intermediate)`][rug flo withval].

Let us consider a couple of examples.

```rust
use rug::{Assign, Integer};
let mut buffer = Integer::new();
// ... buffer can be used and reused ...
let (a, b) = (Integer::from(10), Integer::from(20));
let intermediate = &a - &b;
buffer.assign(intermediate);
assert_eq!(buffer, -10);
```

Here the assignment from `intermediate` into `buffer` does not require
an allocation unless the result does not fit in the current capacity
of `buffer`. If `&a - &b` returns an [`Integer`][rug int] instead,
then an allocation takes place even if it is not necessary.

```rust
use rug::Float;
use rug::float::Constant;
// x has a precision of 10 bits, y has a precision of 50 bits
let x = Float::with_val(10, 180);
let y = Float::with_val(50, Constant::Pi);
let intermediate = &x / &y;
// z has a precision of 45 bits
let z = Float::with_val(45, intermediate);
assert!(57.295 < z && z < 57.296);
```

The precision to use for the result depends on the requirements of the
algorithm being implemented. Here `c` is created with a precision of
45.

In these two examples, we could have left out the `intermediate`
variables altogether and used `buffer.assign(&a - &b)` and
`Float::with_val(45, &x / &y)` directly.

Many operations can return intermediate values:

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
variables like `intermediate` in the last few examples. However, the
names of the types are not public, and consequently, the intermediate
values cannot be for example stored in a struct. If you need to store
the value in a struct, convert it to its final type and value.

As an example, the [documentation][rug int negref] for the
[`Neg`][rust neg] implementation of the reference
[`&Integer`][rug int] shows a return type called
[`NegRef`][rug int negref], but the name is blacked out and not
linkable in the documentation, as the intermediate type cannot be
named. Most of the intermediate values are called similar to `NegRef`,
that is `OpRef` where `Op` indicates what the operation is.

## Crate usage

The Rug crate requires rustc version 1.18.0 or later.

This crate depends on the low-level bindings in the
[gmp-mpfr-sys crate][sys crate], which provides Rust FFI bindings for:

* the [GNU Multiple Precision Arithmetic Library][gmp] (GMP),
* the [GNU MPFR Library][mpfr], a library for multiple-precision
  floating-point computations, and
* [GNU MPC][mpc], a library for the arithmetic of complex numbers with
  arbitrarily high precision.

It can be helpful to refer to the documentation of the
[gmp-mpfr-sys crate][sys] and of the [GMP][gmp doc], [MPFR][mpfr doc]
and [MPC][mpc doc] libraries.

### Optional features

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
   they are enabled.

The first five optional features are enabled by default; to use
features selectively, you can add the dependency like this to
[*Cargo.toml*][cargo deps]:

```toml
[dependencies.rug]
version = "0.9.3"
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
[rug assign assign]: https://docs.rs/rug/0.9.3/rug/trait.Assign.html#tymethod.assign
[rug assign]: https://docs.rs/rug/0.9.3/rug/trait.Assign.html
[rug assr assr]: https://docs.rs/rug/0.9.3/rug/ops/trait.AssignRound.html#tymethod.assign_round
[rug assr]: https://docs.rs/rug/0.9.3/rug/ops/trait.AssignRound.html
[rug com]: https://docs.rs/rug/0.9.3/rug/struct.Complex.html
[rug flo withval]: https://docs.rs/rug/0.9.3/rug/struct.Float.html#method.with_val
[rug flo]: https://docs.rs/rug/0.9.3/rug/struct.Float.html
[rug int absref]: https://docs.rs/rug/0.9.3/rug/struct.Integer.html#method.abs_ref
[rug int divremref]: https://docs.rs/rug/0.9.3/rug/struct.Integer.html#method.div_rem_ref
[rug int negref]: https://docs.rs/rug/0.9.3/rug/struct.Integer.html#impl-Neg-1
[rug int new]: https://docs.rs/rug/0.9.3/rug/struct.Integer.html#method.new
[rug int parse]: https://docs.rs/rug/0.9.3/rug/struct.Integer.html#method.parse
[rug int parseradix]: https://docs.rs/rug/0.9.3/rug/struct.Integer.html#method.parse_radix
[rug int]: https://docs.rs/rug/0.9.3/rug/struct.Integer.html
[rug ops]: https://docs.rs/rug/0.9.3/rug/ops/index.html
[rug rand]: https://docs.rs/rug/0.9.3/rug/rand/struct.RandState.html
[rug rat]: https://docs.rs/rug/0.9.3/rug/struct.Rational.html
[rust assignment]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#assignment-expressions
[rust copy]: https://doc.rust-lang.org/std/marker/trait.Copy.html
[rust from from]: https://doc.rust-lang.org/std/convert/trait.From.html#tymethod.from
[rust from]: https://doc.rust-lang.org/std/convert/trait.From.html
[rust i32]: https://doc.rust-lang.org/std/primitive.i32.html
[rust neg]: https://doc.rust-lang.org/std/ops/trait.Neg.html
[sys crate]: https://crates.io/crates/gmp-mpfr-sys
[sys gnu]: https://docs.rs/gmp-mpfr-sys/^1.1.0/gmp_mpfr_sys/index.html#building-on-gnulinux
[sys mac]: https://docs.rs/gmp-mpfr-sys/^1.1.0/gmp_mpfr_sys/index.html#building-on-macos
[sys win]: https://docs.rs/gmp-mpfr-sys/^1.1.0/gmp_mpfr_sys/index.html#building-on-windows
[sys]: https://docs.rs/gmp-mpfr-sys/^1.1.0/gmp_mpfr_sys/index.html
