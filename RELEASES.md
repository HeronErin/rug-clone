Version 0.8.0 (not yet released)
================================

* Rename `Integer::sign`, `Rational::sign` and `Float::sign` methods
  as `Integer::cmp0`, `Rational::cmp0` and `Float::cmp0`.
* Move `rug::AssignRound` to `rug::float::AssignRound`.
* Add `Integer::clamp`, `Rational::clamp` and `Float::clamp` methods.
* Add `Integer::div_rem_ceil`, `Integer::div_rem_floor` and
  `Integer::div_rem_euc` methods.
* Add `DivRounding`, `DivRoundingAssign` and `DivRoundingFrom` traits,
  and their `Rem` counterparts, and implement them for `Integer`.

Version 0.7.0 (2017-30-09)
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
