<!-- Copyright © 2016–2020 University of Malta -->

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

### Version 1.11.0 news (unreleased)

  * The [gmp-mpfr-sys][sys crate] dependency was updated to [version
    1.4][sys-1-4].

[sys-1-4]: https://docs.rs/gmp-mpfr-sys/~1.4/gmp_mpfr_sys/index.html

### Version 1.10.0 news (2020-07-23)

  * The [gmp-mpfr-sys][sys crate] dependency was updated to [version
    1.3][sys-1-3].
  * Now <code>[Option][`Option`]&lt;[Integer][int-1-10]&gt;</code> has
    the same size as [`Integer`][int-1-10]; and similar for
    [`Rational`][rat-1-10], [`Float`][flo-1-10],
    [`Complex`][com-1-10], [`RandState`][ras-1-10] and
    [`ThreadRandState`][trs-1-10].

[`Option`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html
[com-1-10]: https://docs.rs/rug/~1.10/rug/struct.Complex.html
[flo-1-10]: https://docs.rs/rug/~1.10/rug/struct.Float.html
[int-1-10]: https://docs.rs/rug/~1.10/rug/struct.Integer.html
[ras-1-10]: https://docs.rs/rug/~1.10/rug/rand/struct.RandState.html
[rat-1-10]: https://docs.rs/rug/~1.10/rug/struct.Rational.html
[sys-1-3]: https://docs.rs/gmp-mpfr-sys/~1.3/gmp_mpfr_sys/index.html
[trs-1-10]: https://docs.rs/rug/~1.10/rug/rand/struct.ThreadRandState.html

### Version 1.9.0 news (2020-06-01)

  * Displaying [`Float`][flo-1-9] and [`Complex`][com-1-9] numbers,
    and converting them to strings, now avoids outputting an exponent
    term if the radix point can be moved to the correct place without
    inserting any extra digits. For example `"42.0"` will be produced
    rather than `"4.20e1"` ([issue 18]). This change does not affect
    output when [`LowerExp`] (`"{:e}"` format) or [`UpperExp`]
    (`"{:E}"` format) is used.
  * New methods
    <code>[Float][flo-1-9]::[to\_sign\_string\_exp][flo-tsse-1-9]</code>
    and
    <code>[Float][flo-1-9]::[to\_sign\_string\_exp\_round][flo-tsser-1-9]</code>
    were added.
  * A new function
    <code>[float][flom-1-9]::[allowed\_exp\_range][flom-aer-1-9]</code>
    was added.
  * A new method
    <code>[Float][flo-1-9]::[clamp\_exp][flo-ce-1-9]</code> was added.
  * The following methods are now const functions:
      * <code>[Integer][int-1-9]::[from\_raw][int-fr-1-9]</code>,
        <code>[Rational][rat-1-9]::[from\_raw][rat-fr-1-9]</code>
  * The [*az* crate] is now a public dependency, and wrapping and
    checked casts to/from primitives and big numbers are provided
    through the traits of the crate.

#### Compatibility note

The output of [`Float`][flo-1-9] and [`Complex`][com-1-9] numbers was
changed as specified above.

[*az* crate]: https://crates.io/crates/az
[`LowerExp`]: https://doc.rust-lang.org/nightly/core/fmt/trait.LowerExp.html
[`UpperExp`]: https://doc.rust-lang.org/nightly/core/fmt/trait.UpperExp.html
[com-1-9]: https://docs.rs/rug/~1.9/rug/struct.Complex.html
[flo-1-9]: https://docs.rs/rug/~1.9/rug/struct.Float.html
[flo-ce-1-9]: https://docs.rs/rug/~1.9/rug/struct.Float.html#method.clamp_exp
[flo-tsse-1-9]: https://docs.rs/rug/~1.9/rug/struct.Float.html#method.to_sign_string_exp
[flo-tsser-1-9]: https://docs.rs/rug/~1.9/rug/struct.Float.html#method.to_sign_string_exp_round
[flom-1-9]: https://docs.rs/rug/~1.9/rug/float/index.html
[flom-aer-1-9]: https://docs.rs/rug/~1.9/rug/float/fn.allowed_exp_range.html
[int-1-9]: https://docs.rs/rug/~1.9/rug/struct.Integer.html
[int-fr-1-9]: https://docs.rs/rug/~1.9/rug/struct.Integer.html#method.from_raw
[issue 18]: https://gitlab.com/tspiteri/rug/-/issues/18
[rat-1-9]: https://docs.rs/rug/~1.9/rug/struct.Rational.html
[rat-fr-1-9]: https://docs.rs/rug/~1.9/rug/struct.Rational.html#method.from_raw

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

  * <code>[Integer][`Integer`]::[new][`new`]</code> creates a new
    [`Integer`] intialized to zero.
  * To assign values to Rug types, we use the [`Assign`] trait and its
    method [`Assign::assign`]. We do not use the
    [assignment operator `=`][assignment] as that would drop the
    left-hand-side operand and replace it with a right-hand-side
    operand of the same type, which is not what we want here.
  * Arbitrary precision numbers can hold numbers that are too large to
    fit in a primitive type. To assign such a number to the large
    types, we use strings rather than primitives; in the example this
    is done using <code>[Integer][`Integer`]::[parse][`parse`]</code>
    and
    <code>[Integer][`Integer`]::[parse_radix][`parse_radix`]</code>.
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
rug = "1.10"
```

Rug requires rustc version 1.37.0 or later.

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
version = "1.10"
default-features = false
features = ["integer", "float", "rand"]
```

Here only the `integer`, `float` and `rand` features are enabled. If
none of the features are selected, the [gmp-mpfr-sys crate][sys crate]
is not required and thus not enabled. In that case, only the
[`Assign`] trait and the traits that are in the [`ops`] module are
provided by the crate.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*Incomplete-computation values*]: https://docs.rs/rug/~1.10/rug/index.html#incomplete-computation-values
[*RELEASES.md*]: https://gitlab.com/tspiteri/rug/blob/master/RELEASES.md
[GMP]: https://gmplib.org/
[GNU GPL]: https://www.gnu.org/licenses/gpl-3.0.html
[GNU LGPL]: https://www.gnu.org/licenses/lgpl-3.0.en.html
[GNU]: https://www.gnu.org/
[MPC]: http://www.multiprecision.org/mpc/
[MPFR]: https://www.mpfr.org/
[`Assign::assign`]: https://docs.rs/rug/~1.10/rug/trait.Assign.html#tymethod.assign
[`Assign`]: https://docs.rs/rug/~1.10/rug/trait.Assign.html
[`Complex`]: https://docs.rs/rug/~1.10/rug/struct.Complex.html
[`Float`]: https://docs.rs/rug/~1.10/rug/struct.Float.html
[`Integer`]: https://docs.rs/rug/~1.10/rug/struct.Integer.html
[`RandState`]: https://docs.rs/rug/~1.10/rug/rand/struct.RandState.html
[`Rational`]: https://docs.rs/rug/~1.10/rug/struct.Rational.html
[`new`]: https://docs.rs/rug/~1.10/rug/struct.Integer.html#method.new
[`ops`]: https://docs.rs/rug/~1.10/rug/ops/index.html
[`parse_radix`]: https://docs.rs/rug/~1.10/rug/struct.Integer.html#method.parse_radix
[`parse`]: https://docs.rs/rug/~1.10/rug/struct.Integer.html#method.parse
[assignment]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#assignment-expressions
[operators]: https://docs.rs/rug/~1.10/rug/index.html#operators
[primitive types]: https://docs.rs/rug/~1.10/rug/index.html#using-with-primitive-types
[rug crate]: https://crates.io/crates/rug
[serde crate]: https://crates.io/crates/serde
[sys crate]: https://crates.io/crates/gmp-mpfr-sys
[sys gnu]: https://docs.rs/gmp-mpfr-sys/~1.4/gmp_mpfr_sys/index.html#building-on-gnulinux
[sys mac]: https://docs.rs/gmp-mpfr-sys/~1.4/gmp_mpfr_sys/index.html#building-on-macos
[sys win]: https://docs.rs/gmp-mpfr-sys/~1.4/gmp_mpfr_sys/index.html#building-on-windows
[sys]: https://docs.rs/gmp-mpfr-sys/~1.4/gmp_mpfr_sys/index.html
