Version 0.9.2
=============

* Requires rustc version 1.18.0.
* Require `gmp-mpfr-sys` version 1.1.0.
* Deprecate most `assign_*` methods, and replace with static methods
  that return an object that implements `AssignInto` or
  `AssignRoundInto` instead.
* Deprecate `Rational::copy_to_integer` method.
* Add `Float::ln_u` method.
* Add `Float::round_even` methods.
* Add `Float::gamma_inc` methods.
* Add `Float::random_normal` and `Float::random_exp` methods.
* Deprecate `Float::assign_random_gaussian` methods.
* Add `Complex::cmp_abs` method.
* Add `Complex::root_of_unity` method.
* Rename `SmallRational::from_canonicalized_*` methods to
  `SmallRational::from_canonical_*`.
* Deprecate `SmallRational::assign_canonicalized_*` methods, and
  replace with `SmallRational::assign_canonical_*` static methods.
* Add `as_nonreallocating` functions to `SmallInteger`,
  `SmallRational`, `SmallFloat` and `SmallComplex`.
* Fix `SmallFloat::new` and `SmallComplex::new` to produce numbers
  with a precision of 53.
* Deprecate and hide `float::Round::AwayFromZero`.
* Add `Integer::signum`, `Rational::signum` and `Float::signum`
  methods.
* Add missing conversion to/from and comparisons to primitive types.
* Add `from_raw`, `into_raw`, `as_raw` and `as_raw_mut` to `Integer`,
  `Rational`, `Float` and `Complex`.
* Add `Float::classify` method.
* Add `Float::mul_add`, `Float::mul_sub`, `Float::mul_add_mul` and
  `Float::mul_sub_mul` methods.
* Add `Complex::mul_add` and `Complex::mul_sub` methods.

Version 0.9.1 (2017-11-27)
==========================

* Implement mathematical operations where operands include references
  to primitives.
* Remove undefined behaviour: replace
  `mem::swap(&mut src, &mut uninitialized)` with
  `ptr::copy_nonoverlapping(&src, &mut uninitialized, 1)`.

Version 0.9.0 (2017-11-16)
==========================

* Move `rug::float::AssignRound` to `rug::ops::AssignRound`.
* `OrdFloat` now orders +NaN above +∞, while −NaN is still below −∞.
* Change `Float::subnormalize` methods to require explicit minimum
  normal exponent.
* Add `Float::subnormalize_ieee` methods to deduce exponent range from
  precision, like old `Float::subnormalize`. The new method also
  supports all IEEE 754-2008 precisions corresponding to k storage
  bits where k ≥ 128 and k is a multiple of 32.
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
* Add `Integer::clamp`, `Rational::clamp` and `Float::clamp` methods.
* Add `Integer::div_rem_ceil`, `Integer::div_rem_floor` and
  `Integer::div_rem_euc` methods.
* Add `DivRounding`, `DivRoundingAssign` and `DivRoundingFrom` traits,
  and their `Rem` counterparts, and implement them for `Integer`, and
  for combinations of `Integer` with `i32` or `u32`.
* Add `Rational::fract_floor` and `Rational::fract_ceil` methods.

Version 0.7.0 (2017-09-30)
==========================

* Fix swapped `Float::sin_cos_mut` and `Float::sin_cos_round`,
  `Float::sinh_cosh_mut` and `Float::sinh_cosh_round`, and
  `Float::trunc_fract_mut` and `Float::trunc_fract_round`.
* Fix `Float::to_f32_round`.
* Now `Float::subnormalize` only works for precisions defined in IEEE
  754.
* Add `Integer::gcd_coeffs` methods.

Version 0.6.0 (2017-08-09)
==========================

* Requires rustc version 1.17.0.
* Rename `Float::abs_diff` as `Float::pos_diff`.
* Replace `Float::get_sign` with `Float::is_sign_positive` and
  `Float::is_sign_negative`.
* Add various `as_neg`, `as_abs` and `as_conj` methods.
* Add `OrdFloat` and `OrdComplex` for complete ordering.
