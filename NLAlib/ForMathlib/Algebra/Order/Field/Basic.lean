/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The rational parametrisation of the circle

For every $t$ in an ordered field, $c = (1 - t^2) / (1 + t^2)$ and $s = 2t / (1 + t^2)$ satisfy
$c^2 + s^2 = 1$: the coefficients of a plane rotation as rational functions of one parameter.
Upstream candidate for `Mathlib.Algebra.Order.Field.Basic`.

## Main results

* `one_sub_sq_div_one_add_sq_sq_add_two_mul_div_one_add_sq_sq`: $c^2 + s^2 = 1$.
-/

@[expose] public section

/-- The rational parametrisation of the circle: $c = (1 - t^2) / (1 + t^2)$ and
$s = 2t / (1 + t^2)$ satisfy $c^2 + s^2 = 1$.
Port of `NLAlib.sq_rational_rotation_coefficients`. -/
theorem one_sub_sq_div_one_add_sq_sq_add_two_mul_div_one_add_sq_sq {K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] (t : K) :
    ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
  have hden : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring
