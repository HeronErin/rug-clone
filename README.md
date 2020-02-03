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

### Version 1.8.0 news (unreleased)

  * The implementations
    <code>[AsRef][`AsRef`]&lt;[Float][flo-1-8]&gt;</code> and
    <code>[AsMut][`AsMut`]&lt;[Float][flo-1-8]&gt;</code> for
    [`OrdFloat`][of-1-8], and
    <code>[AsRef][`AsRef`]&lt;[OrdFloat][of-1-8]&gt;</code> for
    [`Float`][flo-1-8], were added.
  * The implementations
    <code>[AsRef][`AsRef`]&lt;[Complex][com-1-8]&gt;</code> and
    <code>[AsMut][`AsMut`]&lt;[Complex][com-1-8]&gt;</code> for
    [`OrdComplex`][oc-1-8], and
    <code>[AsRef][`AsRef`]&lt;[OrdComplex][oc-1-8]&gt;</code> for
    [`Complex`][com-1-8], were added.

[`AsMut`]: https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html
[`AsRef`]: https://doc.rust-lang.org/nightly/core/convert/trait.AsRef.html
[com-1-8]: https://docs.rs/rug/~1.8/rug/struct.Complex.html
[flo-1-8]: https://docs.rs/rug/~1.8/rug/struct.Float.html
[oc-1-8]: https://docs.rs/rug/~1.8/rug/complex/struct.OrdComplex.html
[of-1-8]: https://docs.rs/rug/~1.8/rug/float/struct.OrdFloat.html

### Version 1.7.0 news (2019-01-21)

  * The crate now requires rustc version 1.37.0 or later.
  * The [`RemAssignRound`][rar-1-7] and [`RemFromRound`][rfr-1-7]
    traits were added.
  * The [`Rem`], [`RemAssign`], [`RemFrom`][rf-1-7],
    [`RemAssignRound`][rar-1-7] and [`RemFromRound`][rfr-1-7] traits
    were implemented for [`Float`][flo-1-7].
  * Arithmetic operations with one [`Integer`][int-1-7] or integer
    primitive operand and one [`Rational`][rat-1-7] operand were
    added.
  * A new method
    <code>[Integer][int-1-7]::[div\_exact\_from][int-def-1-7]</code>
    was added.
  * New methods <code>[Integer][int-1-7]::[gcd\_u][int-gu-1-7]</code>,
	<code>[Integer][int-1-7]::[gcd\_u\_mut][int-gum-1-7]</code> and
	<code>[Integer][int-1-7]::[gcd\_u\_ref][int-gur-1-7]</code>were
	added.
  * New methods <code>[Integer][int-1-7]::[lcm\_u][int-lu-1-7]</code>,
	<code>[Integer][int-1-7]::[lcm\_u\_mut][int-lum-1-7]</code> and
	<code>[Integer][int-1-7]::[lcm\_u\_ref][int-lur-1-7]</code>were
	added.
  * New methods <code>[Float][flo-1-7]::[remainder][flo-r-1-7]</code>,
    <code>[Float][flo-1-7]::[remainder\_mut][flo-rm-1-7]</code>,
    <code>[Float][flo-1-7]::[remainder\_round][flo-rr-1-7]</code>,
    <code>[Float][flo-1-7]::[remainder\_from][flo-rf-1-7]</code>,
    <code>[Float][flo-1-7]::[remainder\_from\_round][flo-rfr-1-7]</code>
    and <code>[Float][flo-1-7]::[remainder\_ref][flo-rre-1-7]</code>
    were added.

Compatibility note
------------------

  * [`SmallInteger`][smi-1-7], [`SmallRational`][smr-1-7],
    [`SmallFloat`][smf-1-7] and [`SmallComplex`][smc-1-7] are no
    longer [`Sync`] to avoid the possibility of a [data race][dr-1-7].
    References obtained by dereferencing them, for example the
    <code>&amp;[Integer][int-1-7]</code> returned from
    <code>[SmallInteger][smi-1-7]::[deref][`deref`]</code>, are still
    [`Send`] and [`Sync`].

[`RemAssign`]: https://doc.rust-lang.org/nightly/core/ops/trait.RemAssign.html
[`Rem`]: https://doc.rust-lang.org/nightly/core/ops/trait.Rem.html
[`Send`]: https://doc.rust-lang.org/nightly/core/marker/trait.Send.html
[`Sync`]: https://doc.rust-lang.org/nightly/core/marker/trait.Sync.html
[`deref`]: https://doc.rust-lang.org/nightly/core/ops/trait.Deref.html#tymethod.deref
[dr-1-7]: https://internals.rust-lang.org/t/is-this-a-data-race/11582
[flo-1-7]: https://docs.rs/rug/~1.7/rug/struct.Float.html
[flo-r-1-7]: https://docs.rs/rug/~1.7/rug/struct.Float.html#method.remainder
[flo-rf-1-7]: https://docs.rs/rug/~1.7/rug/struct.Float.html#method.remainder_from
[flo-rfr-1-7]: https://docs.rs/rug/~1.7/rug/struct.Float.html#method.remainder_from_round
[flo-rm-1-7]: https://docs.rs/rug/~1.7/rug/struct.Float.html#method.remainder_mut
[flo-rr-1-7]: https://docs.rs/rug/~1.7/rug/struct.Float.html#method.remainder_round
[flo-rre-1-7]: https://docs.rs/rug/~1.7/rug/struct.Float.html#method.remainder_ref
[int-1-7]: https://docs.rs/rug/~1.7/rug/struct.Integer.html
[int-def-1-7]: https://docs.rs/rug/~1.7/rug/struct.Integer.html#method.div_exact_from
[int-gu-1-7]: https://docs.rs/rug/~1.7/rug/struct.Integer.html#method.gcd_u
[int-gum-1-7]: https://docs.rs/rug/~1.7/rug/struct.Integer.html#method.gcd_u_mut
[int-gur-1-7]: https://docs.rs/rug/~1.7/rug/struct.Integer.html#method.gcd_u_ref
[int-lu-1-7]: https://docs.rs/rug/~1.7/rug/struct.Integer.html#method.lcm_u
[int-lum-1-7]: https://docs.rs/rug/~1.7/rug/struct.Integer.html#method.lcm_u_mut
[int-lur-1-7]: https://docs.rs/rug/~1.7/rug/struct.Integer.html#method.lcm_u_ref
[rar-1-7]: https://docs.rs/rug/~1.7/rug/ops/trait.RemAssignRound.html
[rat-1-7]: https://docs.rs/rug/~1.7/rug/struct.Rational.html
[rf-1-7]: https://docs.rs/rug/~1.7/rug/ops/trait.RemFrom.html
[rfr-1-7]: https://docs.rs/rug/~1.7/rug/ops/trait.RemFromRound.html
[smc-1-7]: https://docs.rs/rug/~1.7/rug/complex/struct.SmallComplex.html
[smf-1-7]: https://docs.rs/rug/~1.7/rug/float/struct.SmallFloat.html
[smi-1-7]: https://docs.rs/rug/~1.7/rug/integer/struct.SmallInteger.html
[smr-1-7]: https://docs.rs/rug/~1.7/rug/rational/struct.SmallRational.html

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
rug = "1.7"
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
version = "1.7"
default-features = false
features = ["integer", "float", "rand"]
```

Here only the `integer`, `float` and `rand` features are enabled. If
none of the features are selected, the [gmp-mpfr-sys crate][sys crate]
is not required and thus not enabled. In that case, only the
[`Assign`] trait and the traits that are in the [`ops`] module are
provided by the crate.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*Incomplete-computation values*]: https://docs.rs/rug/~1.7/rug/index.html#incomplete-computation-values
[*RELEASES.md*]: https://gitlab.com/tspiteri/rug/blob/master/RELEASES.md
[GMP]: https://gmplib.org/
[GNU GPL]: https://www.gnu.org/licenses/gpl-3.0.html
[GNU LGPL]: https://www.gnu.org/licenses/lgpl-3.0.en.html
[GNU]: https://www.gnu.org/
[MPC]: http://www.multiprecision.org/mpc/
[MPFR]: https://www.mpfr.org/
[`Assign::assign`]: https://docs.rs/rug/~1.7/rug/trait.Assign.html#tymethod.assign
[`Assign`]: https://docs.rs/rug/~1.7/rug/trait.Assign.html
[`Complex`]: https://docs.rs/rug/~1.7/rug/struct.Complex.html
[`Float`]: https://docs.rs/rug/~1.7/rug/struct.Float.html
[`Integer`]: https://docs.rs/rug/~1.7/rug/struct.Integer.html
[`RandState`]: https://docs.rs/rug/~1.7/rug/rand/struct.RandState.html
[`Rational`]: https://docs.rs/rug/~1.7/rug/struct.Rational.html
[`new`]: https://docs.rs/rug/~1.7/rug/struct.Integer.html#method.new
[`ops`]: https://docs.rs/rug/~1.7/rug/ops/index.html
[`parse_radix`]: https://docs.rs/rug/~1.7/rug/struct.Integer.html#method.parse_radix
[`parse`]: https://docs.rs/rug/~1.7/rug/struct.Integer.html#method.parse
[assignment]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#assignment-expressions
[operators]: https://docs.rs/rug/~1.7/rug/index.html#operators
[primitive types]: https://docs.rs/rug/~1.7/rug/index.html#using-with-primitive-types
[rug crate]: https://crates.io/crates/rug
[serde crate]: https://crates.io/crates/serde
[sys crate]: https://crates.io/crates/gmp-mpfr-sys
[sys gnu]: https://docs.rs/gmp-mpfr-sys/~1.2/gmp_mpfr_sys/index.html#building-on-gnulinux
[sys mac]: https://docs.rs/gmp-mpfr-sys/~1.2/gmp_mpfr_sys/index.html#building-on-macos
[sys win]: https://docs.rs/gmp-mpfr-sys/~1.2/gmp_mpfr_sys/index.html#building-on-windows
[sys]: https://docs.rs/gmp-mpfr-sys/~1.2/gmp_mpfr_sys/index.html
