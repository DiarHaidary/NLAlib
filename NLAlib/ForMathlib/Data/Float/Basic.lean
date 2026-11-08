/-
Copyright (c) 2026 NumLean contributors and NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NumLean contributors, NLAlib contributors
-/
module

public import Init.Data.Float.Model.Unpacked.Round
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public meta import Mathlib.Tactic.Positivity.Core
public meta import Qq

/-!
# Constants and finite values of the Float model

Upstream candidates for the mathematical API of Lean core's floating-point model.
Adapted from the supplied NumLean archive, `NumLean/Data/Scalars/IEEE/Basic.lean`. The archive's
SHA-256 and licensing status, the earlier Mathlib search and the changes needed for Lean 4.33
are recorded in `docs/design/Finite-Precision-Arithmetic.md`. No NumLean dependency is imported.
General format lemmas state a two-exponent-bit assumption explicitly where needed; core 4.33
also permits one-bit layouts. These results concern logical arithmetic, not native execution cost.

## Main results

* `Float.Model.Format.unitRoundoff_pos`.
* `Float.Model.Format.minExponent_le_maxExponentBound`.
-/

@[expose] public section

namespace Float.Model.UnpackedFloat

/-- `x` is finite: neither infinite nor NaN. -/
def IsFinite (x : UnpackedFloat) : Prop := x.isFinite = true

instance (x : UnpackedFloat) : Decidable x.IsFinite :=
  instDecidableEqBool x.isFinite true

/-- The logical finiteness predicate is the Boolean finite-word test. -/
@[simp] theorem isFinite_eq_true_iff {x : UnpackedFloat} : x.isFinite = true ↔ x.IsFinite :=
  Iff.rfl

/-! ## Signs -/

/-- `±1`. -/
def Sign.toReal : Sign → ℝ
  | .negative => -1
  | .positive => 1

/-- The real value of either sign has absolute value one. -/
@[simp] theorem Sign.abs_toReal (s : Sign) : |s.toReal| = 1 := by cases s <;> simp [Sign.toReal]

/-- Multiplication of signs agrees with multiplication of their real values. -/
@[simp] theorem Sign.toReal_mul (s₁ s₂ : Sign) : (s₁ * s₂).toReal = s₁.toReal * s₂.toReal := by
  cases s₁ <;> cases s₂ <;> simp [Sign.toReal]

/-- Dividing signs agrees with multiplying them, since each sign is its own inverse. -/
theorem Sign.div_eq_mul (s₁ s₂ : Sign) : s₁ / s₂ = s₁ * s₂ := by
  cases s₁ <;> cases s₂ <;> rfl

/-- The real value of a quotient of signs is the product of their real values. -/
@[simp] theorem Sign.toReal_div (s₁ s₂ : Sign) : (s₁ / s₂).toReal = s₁.toReal * s₂.toReal := by
  rw [Sign.div_eq_mul, Sign.toReal_mul]

/-- Negating a sign negates its real value. -/
@[simp] theorem Sign.toReal_neg (s : Sign) : (-s).toReal = -s.toReal := by
  cases s <;> simp [Sign.toReal]

/-- Applying a sign to a natural mantissa agrees with real multiplication by the sign. -/
theorem Sign.cast_apply (s : Sign) (n : ℕ) : ((s.apply n : ℤ) : ℝ) = s.toReal * n := by
  cases s <;> simp [Sign.apply, Sign.toReal]

end Float.Model.UnpackedFloat

namespace Float.Model.Format

/-! ## Facts about a format -/

/-- Every core binary layout has at least two significand bits. -/
theorem two_le_mantissaBits (spec : Format) : 2 ≤ spec.mantissaBits
  := by
  have := spec.hm; unfold Format.mantissaBits; omega

/-- The rounding exponent is clamped below by the smallest subnormal exponent. -/
theorem targetExponent_eq (spec : Format) (T : ℤ) :
    spec.targetExponent T = max (T - spec.mantissaBits) spec.minExponent := rfl

/-- A binary layout with at least two exponent bits has a negative minimum exponent. -/
theorem minExponent_lt_zero (spec : Format) [Fact (2 ≤ spec.exponentBits)] :
    spec.minExponent < 0 := by
  have := (Fact.out (p := 2 ≤ spec.exponentBits))
  have : 2 ≤ 2 ^ (spec.exponentBits - 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h' : (2 : ℤ) ≤ 2 ^ (spec.exponentBits - 1) := by exact_mod_cast this
  have := two_le_mantissaBits spec
  unfold Format.minExponent; omega

/-- The smallest subnormal exponent in terms of exponent bias and stored fraction bits. -/
theorem minExponent_eq (spec : Format) [Fact (2 ≤ spec.exponentBits)] :
    spec.minExponent = 1 - ((spec.exponentBias : ℕ) : ℤ) - spec.mantissaBitsWithoutImplicit := by
  have := (Fact.out (p := 2 ≤ spec.exponentBits))
  have h1 : 1 ≤ 2 ^ (spec.exponentBits - 1) := Nat.one_le_two_pow
  simp only [Format.minExponent, Format.exponentBias, Format.mantissaBits]
  push_cast [h1]
  ring

/-! ## The constants of the standard model -/

/-- The unit roundoff of a format $\mathcal{F}$ with significand precision
$\operatorname{prec}(\mathcal{F})$ is
$2^{-\operatorname{prec}(\mathcal{F})}$. Correct normal rounding has relative error at most this
quantity. -/
noncomputable def unitRoundoff (spec : Format) : ℝ := 2 ^ (-(spec.mantissaBits : ℤ))

/-- Half the smallest positive subnormal of a format $\mathcal{F}$ with minimum exponent
$\operatorname{emin}(\mathcal{F})$: <!-- value Float.Model.Format.underflowBound \mathcal{F} -->
$2^{\operatorname{emin}(\mathcal{F})}/2$. This is the absolute allowance for gradual underflow. -/
noncomputable def underflowBound (spec : Format) : ℝ := 2 ^ spec.minExponent / 2

/-- A finite binary layout has positive unit roundoff. -/
theorem unitRoundoff_pos (spec : Format) : 0 < spec.unitRoundoff := by
  unfold unitRoundoff; positivity

/-- A finite binary layout has positive absolute underflow allowance. -/
theorem underflowBound_pos (spec : Format) : 0 < spec.underflowBound := by
  unfold underflowBound; positivity

/-- Unit roundoff is nonnegative. -/
theorem unitRoundoff_nonneg (spec : Format) : 0 ≤ spec.unitRoundoff := spec.unitRoundoff_pos.le

/-- The absolute underflow allowance is nonnegative. -/
theorem underflowBound_nonneg (spec : Format) : 0 ≤ spec.underflowBound :=
  spec.underflowBound_pos.le

/-- The upper exponent bound is <!-- value Float.Model.Format.maxExponentBound \mathcal{F} -->
$$2^{\operatorname{ebits}(\mathcal{F})}-2-
\operatorname{bias}(\mathcal{F})-(\operatorname{prec}(\mathcal{F})-1)\,.$$
Here $\operatorname{ebits}$ counts exponent bits and $\operatorname{bias}$ is their bias.
It is the largest finite significand exponent for layouts with at least two exponent bits;
one-bit layouts have no normal values. The value is $971$ for binary64 and $104$ for binary32. -/
def maxExponentBound (spec : Format) : ℤ :=
  ((2 ^ spec.exponentBits : ℕ) : ℤ) - 2 - spec.exponentBias - spec.mantissaBitsWithoutImplicit

/-- For a layout $\mathcal{F}$ with at least two exponent bits, the largest finite magnitude,
with precision
$\operatorname{prec}(\mathcal{F})$ and largest significand exponent
$\operatorname{emax}(\mathcal{F})$ is
$$(2^{\operatorname{prec}(\mathcal{F})}-1)2^{\operatorname{emax}(\mathcal{F})}\,.$$
This formula remains total for one-bit exponent layouts, where it need not be represented. -/
noncomputable def maxFinite (spec : Format) : ℝ := (2 ^ spec.mantissaBits - 1) * 2 ^
  spec.maxExponentBound

/-- The maximum-magnitude formula is positive for every core binary layout, including the
one-bit exponent layouts where it need not be a represented value. -/
theorem maxFinite_pos (spec : Format) : 0 < spec.maxFinite := by
  have hp : 0 < spec.mantissaBits := by simp only [Format.mantissaBits]; omega
  exact mul_pos (sub_pos.mpr (one_lt_pow₀ one_lt_two hp.ne')) (zpow_pos two_pos _)

/-- A layout with at least two exponent bits has a nonempty finite exponent interval. -/
theorem minExponent_le_maxExponentBound (spec : Format) [Fact (2 ≤ spec.exponentBits)] :
  spec.minExponent ≤ spec.maxExponentBound := by
  have := (Fact.out (p := 2 ≤ spec.exponentBits))
  have h4 : 4 ≤ 2 ^ spec.exponentBits := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) this
  have h := minExponent_eq spec
  unfold maxExponentBound
  omega

open Mathlib.Meta.Positivity Qq in
/-- `positivity` knows that the unit roundoff is positive. -/
@[positivity Format.unitRoundoff _]
meta def evalUnitRoundoff : PositivityExt where
  eval {u α} _zα pα? e :=
    match pα? with
    | none => pure .none
    | some _ => do
      match u, α, e with
      | 0, ~q(ℝ), ~q(Format.unitRoundoff $spec) =>
        assertInstancesCommute
        pure (.positive q(unitRoundoff_pos $spec))
      | _, _, _ => throwError "not Format.unitRoundoff"

open Mathlib.Meta.Positivity Qq in
/-- `positivity` knows that the underflow bound is positive. -/
@[positivity Format.underflowBound _]
meta def evalUnderflowBound : PositivityExt where
  eval {u α} _zα pα? e :=
    match pα? with
    | none => pure .none
    | some _ => do
      match u, α, e with
      | 0, ~q(ℝ), ~q(Format.underflowBound $spec) =>
        assertInstancesCommute
        pure (.positive q(underflowBound_pos $spec))
      | _, _, _ => throwError "not Format.underflowBound"

end Float.Model.Format
