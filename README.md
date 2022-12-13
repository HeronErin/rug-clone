<!-- Copyright © 2016–2022 Trevor Spiteri -->

<!-- Copying and distribution of this file, with or without modification, are
permitted in any medium without royalty provided the copyright notice and this
notice are preserved. This file is offered as-is, without any warranty. -->

# Arbitrary-precision numbers

Rug provides integers and floating-point numbers with arbitrary precision and
correct rounding:

  * [`Integer`] is a bignum integer with arbitrary precision,
  * [`Rational`] is a bignum rational number with arbitrary precision,
  * [`Float`] is a multi-precision floating-point number with correct rounding,
    and
  * [`Complex`] is a multi-precision complex number with correct rounding.

Rug is a high-level interface to the following [GNU] libraries:

  * [GMP] for integers and rational numbers,
  * [MPFR] for floating-point numbers, and
  * [MPC] for complex numbers.

Rug is free software: you can redistribute it and/or modify it under the terms
of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version. See the full text of the [GNU LGPL] and [GNU GPL] for details.

## What’s new

### Version 1.19.0 news (unreleased)

  * The crate now requires rustc version 1.65.0 or later.
  * The [gmp-mpfr-sys][sys crate] dependency was updated to [version
    1.5][sys-1-5].
  * The following methods are now const functions:
      * <code>[Integer][int-1-19]::[as\_limbs][int-al-1-19]</code>
      * <code>[Integer][int-1-19]::[as\_neg][int-an-1-19]</code>,
        <code>[Integer][int-1-19]::[as\_abs][int-aa-1-19]</code>
      * <code>[Integer][int-1-19]::[is\_even][int-ie-1-19]</code>,
        <code>[Integer][int-1-19]::[is\_odd][int-io-1-19]</code>
      * <code>[Integer][int-1-19]::[cmp0][int-c-1-19]</code>
      * <code>[Rational][rat-1-19]::[into\_raw][rat-ir-1-19]</code>,
        <code>[Rational][rat-1-19]::[as\_raw][rat-ara-1-19]</code>
      * <code>[Rational][rat-1-19]::[numer][rat-n-1-19]</code>,
        <code>[Rational][rat-1-19]::[denom][rat-d-1-19]</code>
      * <code>[Rational][rat-1-19]::[into\_numer\_denom][rat-ind-1-19]</code>
      * <code>[Rational][rat-1-19]::[as\_neg][rat-an-1-19]</code>,
        <code>[Rational][rat-1-19]::[as\_abs][rat-aa-1-19]</code>,
        <code>[Rational][rat-1-19]::[as\_recip][rat-are-1-19]</code>
      * <code>[Rational][rat-1-19]::[cmp0][rat-c-1-19]</code>
      * <code>[Rational][rat-1-19]::[is\_integer][rat-ii-1-19]</code>
      * <code>[Float][flo-1-19]::[prec][flo-p-1-19]</code>,
      * <code>[Float][flo-1-19]::[from\_raw][flo-fr-1-19]</code>,
        <code>[Float][flo-1-19]::[into\_raw][flo-ir-1-19]</code>,
        <code>[Float][flo-1-19]::[as\_raw][flo-ar-1-19]</code>
      * <code>[Float][flo-1-19]::[as\_ord][flo-ao-1-19]</code>,
        <code>[Float][flo-1-19]::[as\_complex][flo-ac-1-19]</code>
      * <code>[Float][flo-1-19]::[is\_nan][flo-ina-1-19]</code>,
        <code>[Float][flo-1-19]::[is\_infinite][flo-ii-1-19]</code>,
        <code>[Float][flo-1-19]::[is\_finite][flo-if-1-19]</code>,
        <code>[Float][flo-1-19]::[is\_zero][flo-iz-1-19]</code>,
        <code>[Float][flo-1-19]::[is\_normal][flo-ino-1-19]</code>,
        <code>[Float][flo-1-19]::[classify][flo-cl-1-19]</code>
      * <code>[Float][flo-1-19]::[cmp0][flo-cm-1-19]</code>
      * <code>[Float][flo-1-19]::[get\_exp][flo-ge-1-19]</code>,
      * <code>[Float][flo-1-19]::[is\_sign\_positive][flo-isp-1-19]</code>,
        <code>[Float][flo-1-19]::[is\_sign\_negative][flo-isn-1-19]</code>
      * <code>[Complex][com-1-19]::[prec][com-p-1-19]</code>,
      * <code>[Complex][com-1-19]::[from\_raw][com-fr-1-19]</code>,
        <code>[Complex][com-1-19]::[into\_raw][com-ir-1-19]</code>,
        <code>[Complex][com-1-19]::[as\_raw][com-ar-1-19]</code>
      * <code>[Complex][com-1-19]::[real][com-r-1-19]</code>,
        <code>[Complex][com-1-19]::[imag][com-i-1-19]</code>
      * <code>[Complex][com-1-19]::[into\_real\_imag][com-iri-1-19]</code>
      * <code>[Complex][com-1-19]::[borrow\_real\_imag][com-bri-1-19]</code>
      * <code>[Complex][com-1-19]::[as\_ord][com-ao-1-19]</code>
      * <code>[Complex][com-1-19]::[eq0][com-e-1-19]</code>
  * [`BorrowInteger`][bi-1-19], [`BorrowRational`][br-1-19],
    [`BorrowFloat`][bf-1-19] and [`BorrowComplex`][bc-1-19] now implement many
    more traits, including [`Clone`] and [`Copy`].

[`Copy`]: https://doc.rust-lang.org/core/marker/trait.Copy.html
[bc-1-19]: https://docs.rs/rug/~1.19/rug/complex/struct.BorrowComplex.html
[bf-1-19]: https://docs.rs/rug/~1.19/rug/float/struct.BorrowFloat.html
[bi-1-19]: https://docs.rs/rug/~1.19/rug/integer/struct.BorrowInteger.html
[br-1-19]: https://docs.rs/rug/~1.19/rug/rational/struct.BorrowRational.html
[com-1-19]: https://docs.rs/rug/~1.19/rug/struct.Complex.html
[com-ao-1-19]: https://docs.rs/rug/~1.19/rug/struct.Complex.html#method.as_ord
[com-ar-1-19]: https://docs.rs/rug/~1.19/rug/struct.Complex.html#method.as_raw
[com-bri-1-19]: https://docs.rs/rug/~1.19/rug/struct.Complex.html#method.borrow_real_imag
[com-e-1-19]: https://docs.rs/rug/~1.19/rug/struct.Complex.html#method.eq0
[com-fr-1-19]: https://docs.rs/rug/~1.19/rug/struct.Complex.html#method.from_raw
[com-i-1-19]: https://docs.rs/rug/~1.19/rug/struct.Complex.html#method.imag
[com-ir-1-19]: https://docs.rs/rug/~1.19/rug/struct.Complex.html#method.into_raw
[com-iri-1-19]: https://docs.rs/rug/~1.19/rug/struct.Complex.html#method.into_real_imag
[com-p-1-19]: https://docs.rs/rug/~1.19/rug/struct.Complex.html#method.prec
[com-r-1-19]: https://docs.rs/rug/~1.19/rug/struct.Complex.html#method.real
[flo-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html
[flo-ac-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.as_complex
[flo-ao-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.as_ord
[flo-ar-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.as_raw
[flo-cl-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.classify
[flo-cm-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.cmp0
[flo-fr-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.from_raw
[flo-ge-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.get_exp
[flo-if-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.is_finite
[flo-ii-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.is_infinite
[flo-ina-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.is_nan
[flo-ino-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.is_normal
[flo-ir-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.into_raw
[flo-isn-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.is_sign_negative
[flo-isp-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.is_sign_positive
[flo-iz-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.is_zero
[flo-p-1-19]: https://docs.rs/rug/~1.19/rug/struct.Float.html#method.prec
[int-1-19]: https://docs.rs/rug/~1.19/rug/struct.Integer.html
[int-aa-1-19]: https://docs.rs/rug/~1.19/rug/struct.Integer.html#method.as_abs
[int-al-1-19]: https://docs.rs/rug/~1.19/rug/struct.Integer.html#method.as_limbs
[int-an-1-19]: https://docs.rs/rug/~1.19/rug/struct.Integer.html#method.as_neg
[int-c-1-19]: https://docs.rs/rug/~1.19/rug/struct.Integer.html#method.cmp0
[int-ie-1-19]: https://docs.rs/rug/~1.19/rug/struct.Integer.html#method.is_even
[int-io-1-19]: https://docs.rs/rug/~1.19/rug/struct.Integer.html#method.is_odd
[rat-1-19]: https://docs.rs/rug/~1.19/rug/struct.Rational.html
[rat-aa-1-19]: https://docs.rs/rug/~1.19/rug/struct.Rational.html#method.as_abs
[rat-an-1-19]: https://docs.rs/rug/~1.19/rug/struct.Rational.html#method.as_neg
[rat-ara-1-19]: https://docs.rs/rug/~1.19/rug/struct.Rational.html#method.as_raw
[rat-are-1-19]: https://docs.rs/rug/~1.19/rug/struct.Rational.html#method.as_recip
[rat-c-1-19]: https://docs.rs/rug/~1.19/rug/struct.Rational.html#method.cmp0
[rat-d-1-19]: https://docs.rs/rug/~1.19/rug/struct.Rational.html#method.denom
[rat-ii-1-19]: https://docs.rs/rug/~1.19/rug/struct.Rational.html#method.is_integer
[rat-ind-1-19]: https://docs.rs/rug/~1.19/rug/struct.Rational.html#method.into_numer_denom
[rat-ir-1-19]: https://docs.rs/rug/~1.19/rug/struct.Rational.html#method.into_raw
[rat-n-1-19]: https://docs.rs/rug/~1.19/rug/struct.Rational.html#method.numer
[sys-1-5]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/index.html

### Version 1.18.0 news (2022-11-17)

  * For the [`Integer`][int-1-18] struct, the methods
    [`gcd_cofactors`][int-gc-1-18], [`gcd_cofactors_mut`][int-gcm-1-18] and
    [`gcd_cofactors_ref`][int-gcr-1-18] were renamed to
    [`extended_gcd`][int-eg-1-18], [`extended_gcd_mut`][int-egm-1-18] and
    [`extended_gcd_ref`][int-egr-1-18]. The old method names are deprecated.
  * All error types now implement [`Clone`], [`Copy`], [`PartialEq`] and [`Eq`].
  * The [`IntegerExt64`][ie64-1-18] extension trait was added to support very
    large integers better on some 64-bit platforms.

[`Clone`]: https://doc.rust-lang.org/core/clone/trait.Clone.html
[`Copy`]: https://doc.rust-lang.org/core/marker/trait.Copy.html
[`Eq`]: https://doc.rust-lang.org/core/cmp/trait.Eq.html
[`PartialEq`]: https://doc.rust-lang.org/core/cmp/trait.PartialEq.html
[ie64-1-18]: https://docs.rs/rug/~1.18/rug/integer/trait.IntegerExt64.html
[int-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html
[int-eg-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.extended_gcd
[int-egm-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.extended_gcd_mut
[int-egr-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.extended_gcd_ref
[int-gc-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.gcd_cofactors
[int-gcm-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.gcd_cofactors_mut
[int-gcr-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.gcd_cofactors_ref

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

  * <code>[Integer][`Integer`]::[new][`new`]</code> creates a new [`Integer`]
    intialized to zero.
  * To assign values to Rug types, we use the [`Assign`] trait and its method
    [`Assign::assign`]. We do not use the [assignment operator `=`][assignment]
    as that would drop the left-hand-side operand and replace it with a
    right-hand-side operand of the same type, which is not what we want here.
  * Arbitrary precision numbers can hold numbers that are too large to fit in a
    primitive type. To assign such a number to the large types, we use strings
    rather than primitives; in the example this is done using
    <code>[Integer][`Integer`]::[parse][`parse`]</code> and
    <code>[Integer][`Integer`]::[parse_radix][`parse_radix`]</code>.
  * We can compare Rug types to primitive types or to other Rug types using the
    normal comparison operators, for example `int > 100_000_000`.
  * Most arithmetic operations are supported with Rug types and primitive types
    on either side of the operator, for example `int >> 128`.

## Using with primitive types

With Rust primitive types, arithmetic operators usually operate on two values of
the same type, for example `12i32 + 5i32`. Unlike primitive types, conversion to
and from Rug types can be expensive, so the arithmetic operators are overloaded
to work on many combinations of Rug types and primitives. More details are
available in the [documentation][primitive types].

## Operators

Operators are overloaded to work on Rug types alone or on a combination of Rug
types and Rust primitives. When at least one operand is an owned value of a Rug
type, the operation will consume that value and return a value of the Rug type.
For example

```rust
use rug::Integer;
let a = Integer::from(10);
let b = 5 - a;
assert_eq!(b, 5 - 10);
```

Here `a` is consumed by the subtraction, and `b` is an owned [`Integer`].

If on the other hand there are no owned Rug types and there are references
instead, the returned value is not the final value, but an
incomplete-computation value. For example

```rust
use rug::Integer;
let (a, b) = (Integer::from(10), Integer::from(20));
let incomplete = &a - &b;
// This would fail to compile: assert_eq!(incomplete, -10);
let sub = Integer::from(incomplete);
assert_eq!(sub, -10);
```

Here `a` and `b` are not consumed, and `incomplete` is not the final value. It
still needs to be converted or assigned into an [`Integer`]. This is covered in
more detail in the documentation’s [*Incomplete-computation values*] section.

More details on operators are available in the [documentation][operators].

## Using Rug

Rug is available on [crates.io][rug crate]. To use Rug in your crate, add it as
a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
rug = "1.18"
```

Rug requires rustc version 1.65.0 or later.

Rug also depends on the [GMP], [MPFR] and [MPC] libraries through the low-level
FFI bindings in the [gmp-mpfr-sys crate][sys crate], which needs some setup to
build; the [gmp-mpfr-sys documentation][sys] has some details on usage under
[GNU/Linux][sys gnu], [macOS][sys mac] and [Windows][sys win].

## Optional features

The Rug crate has six optional features:

 1. `integer`, enabled by default. Required for the [`Integer`] type and its
    supporting features.
 2. `rational`, enabled by default. Required for the [`Rational`] number type
    and its supporting features. This feature requires the `integer` feature.
 3. `float`, enabled by default. Required for the [`Float`] type and its
    supporting features.
 4. `complex`, enabled by default. Required for the [`Complex`] number type and
    its supporting features. This feature requires the `float` feature.
 5. `rand`, enabled by default. Required for the [`RandState`] type and its
    supporting features. This feature requires the `integer` feature.
 6. `serde`, disabled by default. This provides serialization support for the
    [`Integer`], [`Rational`], [`Float`] and [`Complex`] number types, providing
    that they are enabled. This feature requires the [serde crate].

The first five optional features are enabled by default; to use features
selectively, you can add the dependency like this to [*Cargo.toml*]:

```toml
[dependencies.rug]
version = "1.18"
default-features = false
features = ["integer", "float", "rand"]
```

Here only the `integer`, `float` and `rand` features are enabled. If none of the
features are selected, the [gmp-mpfr-sys crate][sys crate] is not required and
thus not enabled. In that case, only the [`Assign`] trait and the traits that
are in the [`ops`] module are provided by the crate.

## Experimental optional features

It is not considered a breaking change if the following experimental features
are removed. The removal of experimental features would however require a minor
version bump. Similarly, on a minor version bump, optional dependencies can be
updated to an incompatible newer version.

 1. `num-traits`, disabled by default. This implements some traits from the
    [*num-traits* crate] and the [*num-integer* crate].

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*Incomplete-computation values*]: https://docs.rs/rug/~1.18/rug/index.html#incomplete-computation-values
[*RELEASES.md*]: https://gitlab.com/tspiteri/rug/blob/master/RELEASES.md
[*num-integer* crate]: https://crates.io/crates/num-integer
[*num-traits* crate]: https://crates.io/crates/num-traits
[GMP]: https://gmplib.org/
[GNU GPL]: https://www.gnu.org/licenses/gpl-3.0.html
[GNU LGPL]: https://www.gnu.org/licenses/lgpl-3.0.en.html
[GNU]: https://www.gnu.org/
[MPC]: https://www.multiprecision.org/mpc/
[MPFR]: https://www.mpfr.org/
[`Assign::assign`]: https://docs.rs/rug/~1.18/rug/trait.Assign.html#tymethod.assign
[`Assign`]: https://docs.rs/rug/~1.18/rug/trait.Assign.html
[`Complex`]: https://docs.rs/rug/~1.18/rug/struct.Complex.html
[`Float`]: https://docs.rs/rug/~1.18/rug/struct.Float.html
[`Integer`]: https://docs.rs/rug/~1.18/rug/struct.Integer.html
[`RandState`]: https://docs.rs/rug/~1.18/rug/rand/struct.RandState.html
[`Rational`]: https://docs.rs/rug/~1.18/rug/struct.Rational.html
[`new`]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.new
[`ops`]: https://docs.rs/rug/~1.18/rug/ops/index.html
[`parse_radix`]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.parse_radix
[`parse`]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.parse
[assignment]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#assignment-expressions
[operators]: https://docs.rs/rug/~1.18/rug/index.html#operators
[primitive types]: https://docs.rs/rug/~1.18/rug/index.html#using-with-primitive-types
[rug crate]: https://crates.io/crates/rug
[serde crate]: https://crates.io/crates/serde
[sys crate]: https://crates.io/crates/gmp-mpfr-sys
[sys gnu]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/index.html#building-on-gnulinux
[sys mac]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/index.html#building-on-macos
[sys win]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/index.html#building-on-windows
[sys]: https://docs.rs/gmp-mpfr-sys/~1.5/gmp_mpfr_sys/index.html
