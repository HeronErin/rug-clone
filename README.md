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

### Version 1.18.0 news (unreleased)

  * For the [`Integer`] struct, the methods [`gcd_cofactors`][int-gc-1-18],
    [`gcd_cofactors_mut`][int-gcm-1-18] and [`gcd_cofactors_ref`][int-gcr-1-18]
    were renamed to [`extended_gcd`][int-eg-1-18],
    [`extended_gcd_mut`][int-egm-1-18] and [`extended_gcd_ref`][int-egr-1-18].
    The old method names are deprecated.
  * All error types now implement [`Clone`], [`Copy`], [`PartialEq`] and [`Eq`].
  * The [`IntegerExt64`][ie64-1-18] trait was added to support very large
    integers better on some 64-bit platforms.
  * The following methods were added to the [`Integer`][int-1-18] struct to
    support very large integers better on 64-bit systems.
    * [`is_divisible_u64`][int-idu-1-18], [`is_divisible_2pow_64`][int-id2-1-18]
    * [`is_congruent_u64`][int-icu-1-18], [`is_congruent_2pow_64`][int-ic2-1-18]
    * [`significant_bits_64`][int-signifb-1-18],
      [`signed_bits_64`][int-signedb-1-18]
    * [`count_ones_64`][int-co-1-18], [`count_zeros_64`][int-cz-1-18]
    * [`find_one_64`][int-fo-1-18], [`find_zero_64`][int-fz-1-18]
    * [`set_bit_64`][int-sb-1-18], [`get_bit_64`][int-gb-1-18],
      [`toggle_bit_64`][int-tb-1-18]
    * [`hamming_dist_64`][int-hd-1-18]
    * [`keep_bits_64`][int-kb-1-18], [`keep_bits_64_mut`][int-kbm-1-18],
      [`keep_bits_64_ref`][int-kbr-1-18]
    * [`keep_signed_bits_64`][int-ksb-1-18],
      [`keep_signed_bits_64_mut`][int-ksbm-1-18],
      [`keep_signed_bits_64_ref`][int-ksbr-1-18]
    * [`mod_u64`][int-mu-1-18]
    * [`div_exact_u64`][int-deu-1-18], [`div_exact_u64_mut`][int-deum-1-18],
      [`div_exact_u64_ref`][int-deur-1-18]
    * [`u64_pow_u64`][int-upu-1-18], [`i64_pow_u64`][int-ipu-1-18]
    * [`root_64`][int-r-1-18], [`root_64_mut`][int-rm-1-18],
      [`root_64_ref`][int-rr-1-18]
    * [`root_rem_64`][int-rre-1-18], [`root_rem_64_mut`][int-rrem-1-18],
      [`root_rem_64_ref`][int-rrer-1-18]
    * [`gcd_u64`][int-gu-1-18], [`gcd_u64_mut`][int-gum-1-18],
      [`gcd_u64_ref`][int-gur-1-18]
    * [`lcm_u64`][int-lu-1-18], [`lcm_u64_mut`][int-lum-1-18],
      [`lcm_u64_ref`][int-lur-1-18]
    * [`remove_factor_64`][int-rf-1-18], [`remove_factor_64_mut`][int-rfm-1-18],
      [`remove_factor_64_ref`][int-rfr-1-18]
    * [`factorial_64`][int-fact-1-18], [`factorial_2_64`][int-fact2-1-18],
      [`factorial_m_64`][int-factm-1-18], [`primorial_64`][int-p-1-18]
    * [`binomial_64`][int-bin-1-18], [`binomial_64_mut`][int-binm-1-18],
      [`binomial_64_ref`][int-binr-1-18], [`binomial_u64`][int-binu-1-18]
    * [`fibonacci_64`][int-fib-1-18], [`fibonacci_2_64`][int-fib2-1-18],
      [`lucas_64`][int-luc-1-18], [`lucas_2_64`][int-luc2-1-18]
    * [`random_bits_64`][int-rb-1-18]

[`Clone`]: https://doc.rust-lang.org/core/clone/trait.Clone.html
[`Copy`]: https://doc.rust-lang.org/core/marker/trait.Copy.html
[`Eq`]: https://doc.rust-lang.org/core/cmp/trait.Eq.html
[`PartialEq`]: https://doc.rust-lang.org/core/cmp/trait.PartialEq.html
[ie64-1-18]: https://docs.rs/rug/~1.18/rug/integer/trait.IntegerExt64.html
[int-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html
[int-bin-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.binomial_64
[int-binm-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.binomial_64_mut
[int-binr-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.binomial_64_ref
[int-binu-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.binomial_u64
[int-co-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.count_ones_64
[int-cz-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.count_zeros_64
[int-deu-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.div_exact_u64
[int-deum-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.div_exact_u64_mut
[int-deur-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.div_exact_u64_ref
[int-eg-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.extended_gcd
[int-egm-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.extended_gcd_mut
[int-egr-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.extended_gcd_ref
[int-fact-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.factorial_64
[int-fact2-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.factorial_2_64
[int-factm-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.factorial_m_64
[int-fib-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.fibonacci_64
[int-fib2-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.fibonacci_2_64
[int-fo-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.find_one_64
[int-fz-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.find_zero_64
[int-gb-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.get_bit_64
[int-gc-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.gcd_cofactors
[int-gcm-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.gcd_cofactors_mut
[int-gcr-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.gcd_cofactors_ref
[int-gu-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.gcd_u64
[int-gum-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.gcd_u64_mut
[int-gur-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.gcd_u64_ref
[int-hd-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.hamming_dist_64
[int-ic2-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.is_congruent_2pow_64
[int-icu-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.is_congruent_u64
[int-id2-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.is_divisible_2pow_64
[int-idu-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.is_divisible_u64
[int-ipu-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.i64_pow_u64
[int-kb-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.keep_bits_64
[int-kbm-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.keep_bits_mut_64
[int-kbr-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.keep_bits_ref_64
[int-ksb-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.keep_signed_bits_64
[int-ksbm-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.keep_signed_bits_mut_64
[int-ksbr-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.keep_signed_bits_ref_64
[int-lu-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.lcd_u64
[int-luc-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.lucas_64
[int-luc2-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.lucas_2_64
[int-lum-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.lcd_u64_mut
[int-lur-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.lcd_u64_ref
[int-mu-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.mod_u64
[int-p-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.primorial_64
[int-r-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.root_64
[int-rb-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.random_bits_64
[int-rf-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.remove_factor_64
[int-rfm-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#methoed.remove_factor_64_mut
[int-rfr-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.remove_factor_64_ref
[int-rm-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.root_64_mut
[int-rr-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.root_64_ref
[int-rre-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.root_rem_64
[int-rrem-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.root_rem_64_mut
[int-rrer-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.root_rem_64_ref
[int-sb-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.set_bit_64
[int-signedb-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.signed_bits_64
[int-signifb-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.significant_bits_64
[int-tb-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.toggle_bit_64
[int-upu-1-18]: https://docs.rs/rug/~1.18/rug/struct.Integer.html#method.u64_pow_u64

### Version 1.17.0 news (2022-08-06)

  * The new method
    <code>[Integer][int-1-17]::[assign\_bytes\_radix\_unchecked][int-abru-1-17]</code>
    was added ([issue 41]).
  * [`Integer`][int-1-17] now implements [`LowerExp`] and [`UpperExp`] for
    convenience by transparently converting the [`Integer`][int-1-17] to a
    [`Float`][flo-1-17] ([issue 42]).
  * Bug fix: the [`CompleteRound`][cr-1-17] trait is now implemented for
      * the value returned from
        <code>[Float][flo-1-17]::[mul\_add\_mul\_ref][flo-mamr-1-17]</code>
      * the value returned from
        <code>[Float][flo-1-17]::[mul\_sub\_mul\_ref][flo-msmr-1-17]</code>
  * The [`CompleteRound`][cr-1-17] trait is now also implemented for
      * the value returned from negating a reference to [`Float`][flo-1-17],
        that is
        <code>&lt;&amp;[Float][flo-1-17] as [Neg][`Neg`]>::[Output][NegOutput]</code>
      * the value returned from negating a reference to [`Complex`][com-1-17],
        that is
        <code>&lt;&amp;[Complex][com-1-17] as [Neg][`Neg`]>::[Output][NegOutput]</code>

[NegOutput]: https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html#associatedtype.Output
[`LowerExp`]: https://doc.rust-lang.org/nightly/core/fmt/trait.LowerExp.html
[`Neg`]: https://doc.rust-lang.org/nightly/core/ops/trait.Neg.html
[`UpperExp`]: https://doc.rust-lang.org/nightly/core/fmt/trait.UpperExp.html
[com-1-17]: https://docs.rs/rug/~1.17/rug/struct.Complex.html
[cr-1-17]: https://docs.rs/rug/~1.17/rug/ops/trait.CompleteRound.html
[flo-1-17]: https://docs.rs/rug/~1.17/rug/struct.Float.html
[flo-mamr-1-17]: https://docs.rs/rug/~1.17/rug/struct.Float.html#method.mul_add_mul_ref
[flo-msmr-1-17]: https://docs.rs/rug/~1.17/rug/struct.Float.html#method.mul_sub_mul_ref
[int-1-17]: https://docs.rs/rug/~1.17/rug/struct.Integer.html
[int-abru-1-17]: https://docs.rs/rug/~1.17/rug/struct.Integer.html#method.assign_bytes_radix_unchecked
[issue 41]: https://gitlab.com/tspiteri/rug/-/issues/41
[issue 42]: https://gitlab.com/tspiteri/rug/-/issues/42

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
rug = "1.17"
```

Rug requires rustc version 1.37.0 or later.

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
version = "1.17"
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
[*Incomplete-computation values*]: https://docs.rs/rug/~1.17/rug/index.html#incomplete-computation-values
[*RELEASES.md*]: https://gitlab.com/tspiteri/rug/blob/master/RELEASES.md
[*num-integer* crate]: https://crates.io/crates/num-integer
[*num-traits* crate]: https://crates.io/crates/num-traits
[GMP]: https://gmplib.org/
[GNU GPL]: https://www.gnu.org/licenses/gpl-3.0.html
[GNU LGPL]: https://www.gnu.org/licenses/lgpl-3.0.en.html
[GNU]: https://www.gnu.org/
[MPC]: http://www.multiprecision.org/mpc/
[MPFR]: https://www.mpfr.org/
[`Assign::assign`]: https://docs.rs/rug/~1.17/rug/trait.Assign.html#tymethod.assign
[`Assign`]: https://docs.rs/rug/~1.17/rug/trait.Assign.html
[`Complex`]: https://docs.rs/rug/~1.17/rug/struct.Complex.html
[`Float`]: https://docs.rs/rug/~1.17/rug/struct.Float.html
[`Integer`]: https://docs.rs/rug/~1.17/rug/struct.Integer.html
[`RandState`]: https://docs.rs/rug/~1.17/rug/rand/struct.RandState.html
[`Rational`]: https://docs.rs/rug/~1.17/rug/struct.Rational.html
[`new`]: https://docs.rs/rug/~1.17/rug/struct.Integer.html#method.new
[`ops`]: https://docs.rs/rug/~1.17/rug/ops/index.html
[`parse_radix`]: https://docs.rs/rug/~1.17/rug/struct.Integer.html#method.parse_radix
[`parse`]: https://docs.rs/rug/~1.17/rug/struct.Integer.html#method.parse
[assignment]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#assignment-expressions
[operators]: https://docs.rs/rug/~1.17/rug/index.html#operators
[primitive types]: https://docs.rs/rug/~1.17/rug/index.html#using-with-primitive-types
[rug crate]: https://crates.io/crates/rug
[serde crate]: https://crates.io/crates/serde
[sys crate]: https://crates.io/crates/gmp-mpfr-sys
[sys gnu]: https://docs.rs/gmp-mpfr-sys/~1.4/gmp_mpfr_sys/index.html#building-on-gnulinux
[sys mac]: https://docs.rs/gmp-mpfr-sys/~1.4/gmp_mpfr_sys/index.html#building-on-macos
[sys win]: https://docs.rs/gmp-mpfr-sys/~1.4/gmp_mpfr_sys/index.html#building-on-windows
[sys]: https://docs.rs/gmp-mpfr-sys/~1.4/gmp_mpfr_sys/index.html
