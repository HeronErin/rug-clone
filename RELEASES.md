<!-- Copyright © 2016–2019 University of Malta -->

<!-- Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved. This file is offered
as-is, without any warranty. -->

Verison 1.4.0 (unreleased)
==========================

  * The method `RandState::as_raw` was fixed to take `&self` instead
    of `&mut self`.
  * Add `Float::copysign` methods.

Version 1.3.0 (2019-01-26)
==========================

  * Add `SmallRational::assign_canonical`.

Version 1.2.3 (2019-01-21)
==========================

  * Fixed bug in `Integer::assign_digits`. (Thanks: Eric Scrivner)

Version 1.2.2 (2018-10-18)
==========================

  * Implement `NotAssign`, `BitAndFrom`, `BitOrFrom` and `BitXorFrom`
    for `bool`.
  * Implement `NegAssign` for `f32` and `f64`.

Version 1.2.1 (2018-08-16)
==========================

  * Add `bool` support to the `Integer::from_digits`,
    `Integer::assign_digits`, `Integer::significant_digits`,
    `Integer::to_digits` and `Integer::write_digits` methods.

Version 1.2.0 (2018-06-30)
==========================

  * Generalize implementations of `Sum` and `Product` for `Integer`
    and `Rational`.
  * Add `Integer::keep_signed_bits` methods.
  * Add `Integer::sum`, `Integer::dot` and `Integer::product` methods.
  * Add `Rational::sum`, `Rational::dot` and `Rational::product`
    methods.
  * Add `Float::dot` and `Complex::dot` methods.

Version 1.1.1 (2018-05-20)
==========================

  * Enable unstable `i128`, `u128` and `TryFrom` in nightly.

Version 1.1.0 (2018-04-23)
==========================

  * Add `i128` and `u128` support, conditional on compiler support.
  * Implement `TryFrom::<Integer>` and `TryFrom::<&Integer>` for
    integer primitives, conditional on compiler support.
  * Implement `TryFrom::<f32>`, `TryFrom::<f64>`, `TryFrom::<Float>`
    and `TryFrom::<&Float>` for `Rational`, conditional on compiler
    support.
  * Add `Float::get_significand` method.
  * Add `Float::u_pow_u` and `Float::i_pow_u` methods.
  * Add `Integer::from_digits`, `Integer::to_digits`,
    `Integer::assign_digits`, `Integer::write_digits` and
    `Integer::significant_digits` methods.

Version 1.0.2 (2018-04-09)
==========================

  * Bug fix: `Integer::reserve` was shrinking the allocation in some
    cases.
  * Bug fix: Change gmp-mpfr-sys dependency from caret to tilde, since
    Rug uses internal implementation details.

Version 1.0.1 (2018-03-10)
==========================

  * Add `Integer::is_power_of_two` method.
  * Add `Integer::signed_bits` method.
  * Add `Integer::secure_pow_mod` methods.
  * Add `Integer::div_rem_round` methods.
  * Add `Complex::eq0` method.
  * Improve documentation.

Version 1.0.0 (2018-03-03)
==========================

  * `Integer::invert_mut` and `Integer::pow_mod_mut` now return
    `Result<(), ()>` instead of `bool`.
  * `float::Round`, `float::Constant` and `float::Special` enums are
    now marked as non-exhaustive.
  * Remove all deprecated items.
  * Remove unsound blanket implementations constrained on
    `T where SmallInteger: Assign<T>` inside `SmallRational` and on
    `T where SmallFloat: Assign<T>` inside `SmallComplex`.

Version 0.10.0 (2018-02-17)
===========================

  * `Integer::invert_ref` and `Integer::pow_mod_ref` now return an
    `Option`, not an object that is assignable to `Result`.
  * `Float::random_bits` and `Complex::random_bits` are now assignable
    to the number values, not to `Result` objects.
  * `Rational::signum`, `Rational::trunc`, `Rational::ceil`,
    `Rational::floor` and `Rational::round` now return `Rational`.
  * `Complex::abs`, `Complex::arg` and `Complex::norm` now return
    `Complex`.
  * Remove `Default` implementations from all types of `Float` and
    `Complex`; now the precision always has to be specified.
  * Remove `Sum` and `Product` implementations for `Float` and
    `Complex`.
  * Remove `Clone` and `Copy` implementations from all incomplete
    computation types.
  * Revamp top-level crate documentation.
  * Add `Integer::parse` and `Rational::parse`, and deprecate
    `ValidInteger`, `ValidRational`, `valid_str_radix` methods, and
    `assign_str*` methods.
  * Add `Float::parse` and `Complex::parse`, and deprecate
    `ValidFloat`, `ValidComplex`, `from_str*` methods,
    `valid_str_radix` methods, and `assign_str*` methods.
  * Rename `Integer::gcd_coeffs*` methods to
    `Integer::gcd_cofactors*`.
  * `Integer::gcd_cofactors_ref` now supports computing only one
    cofactor.
  * Deprecate `Rational::to_integer` and `Rational::as_numer_denom`.
  * Deprecate `Rational::as_mut_numer_denom` and replace with
    `Rational::mutate_numer_denom`.
  * Deprecate `Complex::as_real_imag`.

Version 0.9.3 (2018-02-09)
==========================

  * Add `Integer::square` and `Rational::square` methods.
  * Add `Rational::cmp_abs` method.
  * Add `Float::sum` and `Complex::sum` methods.
  * Add `from_raw`, `into_raw`, `as_raw` and `as_raw_mut` to
    `RandState`.
  * Add `RandGen::boxed_clone` and `RandState::new_custom_boxed`, and
    thus support for cloning custom random generators.
  * Fix `Float::PartialOrd<f32>` (and `<f64>`) to return `None` when
    the primitive is NaN.

Version 0.9.2 (2018-01-12)
==========================

  * Require rustc version 1.18.0.
  * Require gmp-mpfr-sys version 1.1.0.
  * Deprecate most `assign_*` methods, and replace with static methods
    that return an assignable object.
  * Deprecate `Rational::copy_to_integer` method.
  * Add `Rational::assign_canonical` and `Rational::from_canonical`
    methods.
  * Add `Float::ln_u` method.
  * Add `Float::round_even` methods.
  * Add `Float::gamma_inc` methods.
  * Add `Float::random_normal` and `Float::random_exp` methods.
  * Deprecate `Float::assign_random_gaussian` methods.
  * Add `Complex::cmp_abs` method.
  * Add `Complex::root_of_unity` method.
  * Deprecate `SmallRational::from_canonicalized_*` methods and
    replace with `SmallRational::from_canonical` method.
  * Deprecate `SmallRational::assign_canonicalized_*` methods.
  * Add `as_nonreallocating_*` methods to `SmallInteger`,
    `SmallRational`, `SmallFloat` and `SmallComplex`.
  * Fix `SmallFloat::new` and `SmallComplex::new` to produce numbers
    with a precision of 53.
  * Deprecate and hide `float::Round::AwayFromZero`.
  * Add `Integer::signum`, `Rational::signum` and `Float::signum`
    methods.
  * Add missing conversion to/from and comparisons to primitive types.
  * Add `from_raw`, `into_raw`, `as_raw` and `as_raw_mut` to
    `Integer`, `Rational`, `Float` and `Complex`.
  * Add `Float::classify` method.
  * Add `Float::mul_add`, `Float::mul_sub`, `Float::mul_add_mul` and
    `Float::mul_sub_mul` methods.
  * Add `Complex::mul_add` and `Complex::mul_sub` methods.

Version 0.9.1 (2017-11-27)
==========================

  * Implement mathematical operations where operands include
    references to primitives.
  * Remove undefined behaviour: replace
    `mem::swap(&mut src, &mut uninitialized)` with
    `ptr::copy_nonoverlapping(&src, &mut uninitialized, 1)`.

Version 0.9.0 (2017-11-16)
==========================

  * Move `rug::float::AssignRound` to `rug::ops::AssignRound`.
  * `OrdFloat` now orders +NaN above +∞, while −NaN is still below −∞.
  * Change `Float::subnormalize` methods to require explicit minimum
    normal exponent.
  * Add `Float::subnormalize_ieee` methods to deduce exponent range
    from precision, like old `Float::subnormalize`. The new method
    also supports all IEEE 754-2008 precisions corresponding to k
    storage bits where k ≥ 128 and k is a multiple of 32.
  * Deprecate `Rational::fract` methods and replace with
    `Rational::rem_trunc` methods.
  * Add `Rational::rem_ceil` and `Rational::rem_floor` methods.
  * Add `Rational::rem_round` and `Rational::fract_round` methods.
  * Add `Float::next_toward`, `Float::next_up` and `Float::next_down`.
  * Add optional serde support.

Version 0.8.0 (2017-10-26)
==========================

  * Rename `Integer::sign`, `Rational::sign` and `Float::sign` methods
    as `Integer::cmp0`, `Rational::cmp0` and `Float::cmp0`.
  * Rename `Float::pos_diff` as `Float::positive_diff`.
  * Move `rug::AssignRound` to `rug::float::AssignRound`.
  * Add `Integer::clamp`, `Rational::clamp` and `Float::clamp`
    methods.
  * Add `Integer::div_rem_ceil`, `Integer::div_rem_floor` and
    `Integer::div_rem_euc` methods.
  * Add `DivRounding`, `DivRoundingAssign` and `DivRoundingFrom`
    traits, and their `Rem` counterparts, and implement them for
    `Integer`, and for combinations of `Integer` with `i32` or `u32`.
  * Add `Rational::fract_floor` and `Rational::fract_ceil` methods.

Version 0.7.0 (2017-09-30)
==========================

  * Fix swapped `Float::sin_cos_mut` and `Float::sin_cos_round`,
    `Float::sinh_cosh_mut` and `Float::sinh_cosh_round`, and
    `Float::trunc_fract_mut` and `Float::trunc_fract_round`.
  * Fix `Float::to_f32_round`.
  * Now `Float::subnormalize` only works for precisions defined in
    IEEE 754.
  * Add `Integer::gcd_coeffs` methods.

Version 0.6.0 (2017-08-09)
==========================

  * Requires rustc version 1.17.0.
  * Rename `Float::abs_diff` as `Float::pos_diff`.
  * Replace `Float::get_sign` with `Float::is_sign_positive` and
    `Float::is_sign_negative`.
  * Add various `as_neg`, `as_abs` and `as_conj` methods.
  * Add `OrdFloat` and `OrdComplex` for complete ordering.
