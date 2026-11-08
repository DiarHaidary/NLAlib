/-
Copyright (c) 2026 NumLean contributors and NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NumLean contributors, NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Float.Operations

/-!
# Square-root rounding in the Float logical model

Upstream candidates for Lean core's floating-point model, adapted from the supplied NumLean
archive, `NumLean/Data/Scalars/IEEE/Sqrt.lean`. Its archive hash and licensing status are
recorded in `docs/design/Finite-Precision-Arithmetic.md`. No private package is imported.
The results describe core's logical square-root operation, with gradual underflow retained.

## Main results

* `Float.Model.UnpackedFloat.sqrt_isCanonical`.
* `Float.Model.UnpackedFloat.abs_toReal_sqrt_sub_le`.
* `Float.Model.UnpackedFloat.isNearestFloat_toReal_sqrt`.
-/

@[expose] public section

namespace Float.Model.UnpackedFloat

open Float.Model.BinaryRounding

variable {spec : Format}

/-- The accuracy computed by `sqrtCore` describes $\sqrt M$. -/
theorem ExtendedMantissa.approximates_sqrt (M : ℕ) :
    ExtendedMantissa.Approximates (ExtendedMantissa.ofMantissaAndAccuracy M.sqrt
      (if M - M.sqrt * M.sqrt = 0 then .exact
       else .inexact (if M - M.sqrt * M.sqrt ≤ M.sqrt then .lt else .gt))) (Real.sqrt M) := by
  set r := M.sqrt
  have h1 : r * r ≤ M := by have := Nat.sqrt_le' M; rwa [sq] at this
  have h2 : M < (r + 1) * (r + 1) := by
    have := Nat.lt_succ_sqrt' M; rwa [Nat.succ_eq_add_one, sq] at this
  have hle : (r : ℝ) ≤ Real.sqrt M := Real.le_sqrt_of_sq_le (by exact_mod_cast (by nlinarith : r
    ^ 2 ≤ M))
  have hlt : Real.sqrt M < r + 1 := by
    rw [Real.sqrt_lt' (by positivity)]; exact_mod_cast (by nlinarith : M < (r + 1) ^ 2)
  -- round bit: `r + ½ ≤ √M ↔ r < M - r²`
  have hround : (r : ℝ) + 1 / 2 ≤ Real.sqrt M ↔ r < M - r * r := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    constructor
    · intro h
      have : ((r * r + r : ℕ) : ℝ) < M := by push_cast; nlinarith
      have : r * r + r < M := by exact_mod_cast this
      omega
    · intro h
      have : r * r + r + 1 ≤ M := by omega
      have : ((r * r + r + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast this
      push_cast at this; nlinarith
  -- sticky bit: `√M ≠ r ∧ √M ≠ r + ½ ↔ M ≠ r²`
  have hsticky : (Real.sqrt M ≠ r ∧ Real.sqrt M ≠ r + 1 / 2) ↔ M - r * r ≠ 0 := by
    constructor
    · rintro ⟨h, -⟩ h0
      apply h
      have : M = r * r := by omega
      rw [this]; push_cast; exact Real.sqrt_mul_self (by positivity)
    · intro h0
      constructor
      · intro h
        have := Real.sq_sqrt (show (0 : ℝ) ≤ M by positivity)
        rw [h] at this
        have : M = r * r := by exact_mod_cast (by nlinarith : (M : ℝ) = r * r)
        omega
      · intro h
        have := Real.sq_sqrt (show (0 : ℝ) ≤ M by positivity)
        rw [h] at this
        -- `4 M = (2r+1)²` is odd
        have : (4 * M : ℝ) = (2 * r + 1) ^ 2 := by nlinarith
        have : 4 * M = (2 * r + 1) ^ 2 := by exact_mod_cast this
        have := congrArg (· % 2) this
        simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod] at this
  by_cases h0 : M - r * r = 0
  · simp only [h0, ↓reduceIte]
    refine ⟨hle, hlt, ?_, ?_⟩
    · change (false = true) ↔ (r : ℝ) + 1 / 2 ≤ Real.sqrt M
      rw [hround, h0]; simp
    · change (false = true) ↔ (Real.sqrt M ≠ r ∧ Real.sqrt M ≠ r + 1 / 2)
      rw [hsticky, h0]; simp
  · simp only [h0, ↓reduceIte]
    by_cases hr : M - r * r ≤ r
    · simp only [hr, ↓reduceIte]
      refine ⟨hle, hlt, ?_, ?_⟩ <;> simp only [ExtendedMantissa.ofMantissaAndAccuracy,
        Bool.false_eq_true, false_iff, true_iff, not_le]
      · by_contra hc; replace hc := le_of_not_gt hc; exact absurd (hround.mp hc) (by omega)
      · exact hsticky.mpr h0
    · simp only [hr, ↓reduceIte]
      refine ⟨hle, hlt, ?_, ?_⟩ <;> simp only [ExtendedMantissa.ofMantissaAndAccuracy, true_iff]
      · exact hround.mpr (by omega)
      · exact hsticky.mpr h0

/-- For a positive mantissa, the integer square-root core describes the exact real square
root at an exponent no larger than the target exponent. -/
theorem exists_approximates_sqrtCore (m : ℕ) (e : ℤ) (hm : 0 < m) :
    ∃ w : ℝ, ExtendedMantissa.Approximates (ExtendedMantissa.ofMantissaAndAccuracy (sqrtCore
    spec m e).1
        (sqrtCore spec m e).2.2) w ∧
      w * 2 ^ (sqrtCore spec m e).2.1 = Real.sqrt (m * 2 ^ e) ∧
      (sqrtCore spec m e).2.1 ≤ spec.targetExponent
        (totalExponent (sqrtCore spec m e).1 (sqrtCore spec m e).2.1) := by
  unfold sqrtCore
  simp only
  have hdiv : ∀ x : ℤ, x.ediv 2 = x / 2 := fun _ => rfl
  simp only [hdiv]
  generalize htg : min (e / 2) (spec.targetExponent ((totalExponent m e + 1) / 2)) = tgt
  have htg1 : tgt ≤ e / 2 := htg ▸ min_le_left _ _
  have htg2 : tgt ≤ spec.targetExponent ((totalExponent m e + 1) / 2) := htg ▸ min_le_right _ _
  generalize hk : (e - 2 * tgt).toNat = k
  have hk' : (k : ℤ) = e - 2 * tgt := by rw [← hk]; exact Int.toNat_of_nonneg (by omega)
  refine ⟨Real.sqrt ((m <<< k : ℕ) : ℝ), ExtendedMantissa.approximates_sqrt _, ?_, ?_⟩
  · have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have : (m : ℝ) * 2 ^ e = ((m <<< k : ℕ) : ℝ) * ((2 : ℝ) ^ tgt) ^ 2 := by
      rw [Nat.shiftLeft_eq]; push_cast
      rw [← zpow_natCast, hk', ← zpow_natCast, ← zpow_mul, mul_assoc, ← zpow_add₀ h2]
      congr 2; push_cast; ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  · have hp := Format.two_le_mantissaBits spec
    by_cases hlow : tgt ≤ spec.minExponent
    · exact le_trans hlow (le_max_right _ _)
    replace hlow := not_le.mp hlow
    have hD : tgt ≤ (totalExponent m e + 1) / 2 - spec.mantissaBits := by
      rw [Format.targetExponent_eq] at htg2
      rcases max_choice ((totalExponent m e + 1) / 2 - spec.mantissaBits) spec.minExponent with
    h | h
      · rwa [h] at htg2
      · rw [h] at htg2; omega
    rw [totalExponent_eq] at hD
    have hl := (Nat.log2_eq_iff hm.ne').mp rfl
    have hkb : 2 * spec.mantissaBits - 2 ≤ m.log2 + k := by omega
    have hM : 2 ^ (spec.mantissaBits - 1) * 2 ^ (spec.mantissaBits - 1) ≤ m <<< k := by
      rw [Nat.shiftLeft_eq, ← pow_add]
      calc 2 ^ (spec.mantissaBits - 1 + (spec.mantissaBits - 1)) ≤ 2 ^ (m.log2 + k) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ m.log2 * 2 ^ k := pow_add _ _ _
        _ ≤ m * 2 ^ k := Nat.mul_le_mul_right _ hl.1
    have hq : 2 ^ (spec.mantissaBits - 1) ≤ (m <<< k).sqrt := Nat.le_sqrt.mpr hM
    have hqpos : 0 < (m <<< k).sqrt := lt_of_lt_of_le (by positivity) hq
    have : spec.mantissaBits - 1 ≤ (m <<< k).sqrt.log2 := (Nat.le_log2 hqpos.ne').mpr hq
    rw [Format.targetExponent_eq, totalExponent_eq]
    apply le_max_of_le_left
    omega

private theorem sqrt_spec (x : UnpackedFloat) :
    IsCanonical spec (UnpackedFloat.sqrt spec x) ∧
    ((UnpackedFloat.sqrt spec x).IsFinite → x.IsFinite ∧
      |toReal (UnpackedFloat.sqrt spec x) - Real.sqrt (toReal x)|
        ≤ spec.unitRoundoff * Real.sqrt (toReal x)
          + spec.underflowBound) := by
  rcases x with s | _ | s | ⟨s, m, e, hm⟩
  · cases s <;> simp [UnpackedFloat.sqrt, IsCanonical, IsFinite, isFinite]
  · simp [UnpackedFloat.sqrt, IsCanonical, IsFinite, isFinite]
  · refine ⟨trivial, fun _ => ⟨rfl, ?_⟩⟩
    simp only [UnpackedFloat.sqrt, toReal, Real.sqrt_zero, sub_zero, abs_zero, mul_zero, zero_add]
    positivity
  · cases s
    · simp [UnpackedFloat.sqrt, IsCanonical, IsFinite, isFinite]
    · simp only [UnpackedFloat.sqrt]
      obtain ⟨w, hw, hwv, he⟩ := exists_approximates_sqrtCore (spec := spec) m e hm
      have hs := And.intro (roundWithAccuracy_isCanonical spec .positive _ _ _ w hw he)
        (abs_toReal_roundWithAccuracy_sub_le spec .positive _ _ _ w hw he)
      have hwm := hw.le
      rw [ofMantissaAndAccuracy_mantissa] at hwm
      have hh := div_pow_targetExponent_le_of_le_targetExponent spec _ _ w hwm he
      rw [hwv] at hs hh
      refine ⟨hs.1, fun _ => ⟨rfl, ?_⟩⟩
      have hv : toReal (.finite .positive m e hm) = m * 2 ^ e := by simp [toReal, Sign.toReal]
      rw [hv]
      simpa [Sign.toReal] using hs.2.trans hh

/-- The unpacked square-root operation always returns canonical data, including exceptional
values for invalid inputs. This does not assert finiteness after packing. -/
theorem sqrt_isCanonical (x : UnpackedFloat) :
    IsCanonical spec (UnpackedFloat.sqrt spec x) :=
  (sqrt_spec x).1

/-- A finite square root has a finite argument. -/
theorem isFinite_of_isFinite_sqrt (x : UnpackedFloat)
    (h : (UnpackedFloat.sqrt spec x).IsFinite) : x.IsFinite :=
  ((sqrt_spec x).2 h).1

/-- When the unpacked square root is finite, its error from the exact real square root is at
most relative allowance $2^{-p}$ plus absolute allowance $2^{e_{\min}}/2$, where $p$ is the
format precision and $e_{\min}$ its smallest significand exponent. Packing is separate. -/
theorem abs_toReal_sqrt_sub_le (x : UnpackedFloat)
    (h : (UnpackedFloat.sqrt spec x).IsFinite) :
    |toReal (UnpackedFloat.sqrt spec x) - Real.sqrt (toReal x)|
      ≤ spec.unitRoundoff * Real.sqrt (toReal x)
        + spec.underflowBound :=
  ((sqrt_spec x).2 h).2

/-- Finite nonnegative inputs have a finite unpacked square root, before packing. -/
theorem isFinite_sqrt_of_nonneg (x : UnpackedFloat) (hx : x.IsFinite)
    (ha : 0 ≤ toReal x) : (UnpackedFloat.sqrt spec x).IsFinite := by
  cases x with
  | notANumber => exact (Bool.noConfusion hx)
  | infinity s => exact (Bool.noConfusion hx)
  | zero s => rfl
  | finite s m e hm =>
    cases s with
    | positive => exact isFinite_roundWithAccuracy _ _ _ _ _
    | negative =>
      have hp : 0 < (m : ℝ) * (2 : ℝ) ^ e := mul_pos (by exact_mod_cast hm) (by positivity)
      simp only [toReal, Sign.toReal, neg_one_mul] at ha
      nlinarith

/-- The unpacked square root is a nearest lower-grid float of the real square root. -/
theorem isNearestFloat_toReal_sqrt (x : UnpackedFloat) (hx : x.IsFinite)
    (ha : 0 ≤ toReal x) :
    IsNearestFloat spec.mantissaBits spec.minExponent (Real.sqrt (toReal x))
      (toReal (UnpackedFloat.sqrt spec x)) := by
  cases x with
  | notANumber => exact (Bool.noConfusion hx)
  | infinity s => exact (Bool.noConfusion hx)
  | zero s => simpa only [UnpackedFloat.sqrt, toReal, Real.sqrt_zero] using
      (isNearestFloat_self (p := spec.mantissaBits) (emin := spec.minExponent) isBinaryFloat_zero)
  | finite s m e hm =>
    cases s with
    | negative =>
      have hp : 0 < (m : ℝ) * (2 : ℝ) ^ e := mul_pos (by exact_mod_cast hm) (by positivity)
      simp only [toReal, Sign.toReal, neg_one_mul] at ha
      nlinarith
    | positive =>
      obtain ⟨w, hw, hwv, he⟩ := exists_approximates_sqrtCore (spec := spec) m e hm
      have hn := isNearestFloat_toReal_roundWithAccuracy spec .positive _ _ _ w hw he
      rw [hwv] at hn
      simpa only [UnpackedFloat.sqrt, toReal, Sign.toReal, one_mul] using hn

/-- The unpacked square root of a finite nonnegative input has nonnegative real value. -/
theorem toReal_sqrt_nonneg (x : UnpackedFloat) (hx : x.IsFinite) (ha : 0 ≤ toReal x) :
    0 ≤ toReal (UnpackedFloat.sqrt spec x) := by
  exact (isNearestFloat_toReal_sqrt (spec := spec) x hx ha).ge_of_le
    isBinaryFloat_zero (Real.sqrt_nonneg _)

end Float.Model.UnpackedFloat
