<!-- Copyright © 2016–2019 University of Malta -->

<!-- Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved. This file is offered
as-is, without any warranty. -->

# Arbitrary-precision numbers

Rug provides integers and floating-point numbers with arbitrary
precision and correct rounding:

  * [`Integer`] is a bignum integer with arbitrary precision,
  * [`Rational`] is a bignum rational number with arbitrary precision,
  * [`Float`] is a multi-precision floating-point number with correct
    rounding, and
  * [`Complex`] is a multi-precision complex number with correct
    rounding.

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

### Version 1.6.0 news (unreleased)

  * Arithmetic operator implementations for [`i8`], [`i16`], [`i64`],
    [`i128`], [`u8`], [`u16`], [`u64`] and [`u128`] were added to the
    existing implementations for [`i32`] and [`u32`].
  * The function [`float::free_cache`] was added.
  * [`ThreadRandState`] and [`ThreadRandGen`] were added to the
    [`rand`] module to enable the use of custom random generators that
    are not [`Send`] and [`Sync`].
  * Methods which take [`ThreadRandState`] were added to match all the
    methods which take [`RandState`] in the numeric types.

[`RandState`]: https://docs.rs/rug/~1.6/rug/rand/struct.RandState.html
[`Send`]: https://doc.rust-lang.org/nightly/std/marker/trait.Send.html
[`Sync`]: https://doc.rust-lang.org/nightly/std/marker/trait.Sync.html
[`ThreadRandGen`]: https://docs.rs/rug/~1.6/rug/rand/trait.ThreadRandGen.html
[`ThreadRandState`]: https://docs.rs/rug/~1.6/rug/rand/struct.ThreadRandState.html
[`float::free_cache`]: https://docs.rs/rug/~1.6/rug/float/fn.free_cache.html
[`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
[`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
[`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
[`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
[`rand`]: https://docs.rs/rug/~1.6/rug/rand/index.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html

### Version 1.5.2 news (2019-07-26)

  * Bug fix:
    <code>[Pow][`Pow`]<[i32][`i32`]> for [Rational][`Rational`]</code>
    was returning the reciprocal of the correct result.

[`Pow`]: https://docs.rs/rug/~1.5/rug/ops/trait.Pow.html
[`Rational`]: https://docs.rs/rug/~1.5/rug/struct.Rational.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html

### Version 1.5.1 news (2019-07-10)

  * Bug fix: a memory leak in conversions of [`Float`] to string was
    fixed ([issue 11]).

[issue 11]: https://gitlab.com/tspiteri/rug/issues/11

### Version 1.5.0 news (2019-07-04)

  * The method [`Integer::assign_digits_unaligned`] was added to
    enable reading digits from unaligned memory.
  * The method [`Integer::write_digits_unaligned`] was added to enable
    writing digits to unaligned and uninitialized memory.
  * The methods [`Float::u_exp`] and [`Float::i_exp`] were added.
  * The method [`Complex::abs_round`] was added.
  * The documentation examples on [`from_raw`] methods now use
    [`MaybeUninit`] instead of [`mem::uninitialized`].

[`Complex::abs_round`]: https://docs.rs/rug/~1.5/rug/struct.Complex.html#method.abs_round
[`Float::i_exp`]: https://docs.rs/rug/~1.5/rug/struct.Float.html#method.i_exp
[`Float::u_exp`]: https://docs.rs/rug/~1.5/rug/struct.Float.html#method.u_exp
[`Integer::assign_digits_unaligned`]: https://docs.rs/rug/~1.5/rug/struct.Integer.html#method.assign_digits_unaligned
[`Integer::write_digits_unaligned`]: https://docs.rs/rug/~1.5/rug/struct.Integer.html#method.write_digits_unaligned
[`MaybeUninit`]: https://doc.rust-lang.org/nightly/std/mem/union.MaybeUninit.html
[`from_raw`]: https://docs.rs/rug/~1.5/rug/struct.Integer.html#method.from_raw
[`mem::uninitialized`]: https://doc.rust-lang.org/nightly/std/mem/fn.uninitialized.html

### Version 1.4.0 news (2019-04-24)

  * Rug now requires rustc version 1.31.0 or later.
  * The method [`RandState::as_raw`] was fixed to take `&self` instead
    of `&mut self`.
  * [`float::prec_min`] and [`float::prec_max`] are now const
    functions.
  * Methods [`Float::copysign`], [`Float::copysign_mut`] and
    [`Float::copysign_ref`] were added.

[`Float::copysign_mut`]: https://docs.rs/rug/~1.5/rug/struct.Float.html#method.copysign_mut
[`Float::copysign_ref`]: https://docs.rs/rug/~1.5/rug/struct.Float.html#method.copysign_ref
[`Float::copysign`]: https://docs.rs/rug/~1.5/rug/struct.Float.html#method.copysign
[`RandState::as_raw`]: https://docs.rs/rug/~1.5/rug/rand/struct.RandState.html#method.as_raw
[`float::prec_max`]: https://docs.rs/rug/~1.5/rug/float/fn.prec_max.html
[`float::prec_min`]: https://docs.rs/rug/~1.5/rug/float/fn.prec_min.html

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
    left-hand-side operand and replace it with a right-hand-side
    operand of the same type, which is not what we want here.
  * Arbitrary precision numbers can hold numbers that are too large to
    fit in a primitive type. To assign such a number to the large
    types, we use strings rather than primitives; in the example this
    is done using [`Integer::parse`] and [`Integer::parse_radix`].
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
Rug types and primitives. More details are available in the
[documentation][primitive types].

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
This is covered in more detail in the documentation’s
[*Incomplete-computation values*] section.

More details on operators are available in the
[documentation][operators].

## Using Rug

Rug is available on [crates.io][rug crate]. To use Rug in your crate,
add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
rug = "1.5"
```

Rug requires rustc version 1.31.0 or later.

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
    type and its supporting features. This feature requires the
    `float` feature.
 5. `rand`, enabled by default. Required for the [`RandState`] type
    and its supporting features. This feature requires the `integer`
    feature.
 6. `serde`, disabled by default. This provides serialization support
    for the [`Integer`], [`Rational`], [`Float`] and [`Complex`]
    number types, providing that they are enabled. This feature
    requires the [serde crate].

The first five optional features are enabled by default; to use
features selectively, you can add the dependency like this to
[*Cargo.toml*]:

```toml
[dependencies.rug]
version = "1.5"
default-features = false
features = ["integer", "float", "rand"]
```

Here only the `integer`, `float` and `rand` features are enabled. If
none of the features are selected, the [gmp-mpfr-sys crate][sys crate]
is not required and thus not enabled. In that case, only the
[`Assign`] trait and the traits that are in the [`ops`] module are
provided by the crate.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*Incomplete-computation values*]: https://docs.rs/rug/~1.5/rug/index.html#incomplete-computation-values
[*RELEASES.md*]: https://gitlab.com/tspiteri/rug/blob/master/RELEASES.md
[GMP]: https://gmplib.org/
[GNU GPL]: https://www.gnu.org/licenses/gpl-3.0.html
[GNU LGPL]: https://www.gnu.org/licenses/lgpl-3.0.en.html
[GNU]: https://www.gnu.org/
[MPC]: http://www.multiprecision.org/mpc/
[MPFR]: https://www.mpfr.org/
[`Assign::assign`]: https://docs.rs/rug/~1.5/rug/trait.Assign.html#tymethod.assign
[`Assign`]: https://docs.rs/rug/~1.5/rug/trait.Assign.html
[`Complex`]: https://docs.rs/rug/~1.5/rug/struct.Complex.html
[`Float`]: https://docs.rs/rug/~1.5/rug/struct.Float.html
[`Integer::new`]: https://docs.rs/rug/~1.5/rug/struct.Integer.html#method.new
[`Integer::parse_radix`]: https://docs.rs/rug/~1.5/rug/struct.Integer.html#method.parse_radix
[`Integer::parse`]: https://docs.rs/rug/~1.5/rug/struct.Integer.html#method.parse
[`Integer`]: https://docs.rs/rug/~1.5/rug/struct.Integer.html
[`RandState`]: https://docs.rs/rug/~1.5/rug/rand/struct.RandState.html
[`Rational`]: https://docs.rs/rug/~1.5/rug/struct.Rational.html
[`ops`]: https://docs.rs/rug/~1.5/rug/ops/index.html
[assignment]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#assignment-expressions
[operators]: https://docs.rs/rug/~1.5/rug/index.html#operators
[primitive types]: https://docs.rs/rug/~1.5/rug/index.html#using-with-primitive-types
[rug crate]: https://crates.io/crates/rug
[serde crate]: https://crates.io/crates/serde
[sys crate]: https://crates.io/crates/gmp-mpfr-sys
[sys gnu]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/index.html#building-on-gnulinux
[sys mac]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/index.html#building-on-macos
[sys win]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/index.html#building-on-windows
[sys]: https://docs.rs/gmp-mpfr-sys/~1.1/gmp_mpfr_sys/index.html
