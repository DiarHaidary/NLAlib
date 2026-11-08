/-
Copyright (c) 2026 NumLean contributors and NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NumLean contributors, NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Float.Basic
public import NLAlib.ForMathlib.Data.Float.Mantissa
public import NLAlib.ForMathlib.Data.Float.BinaryFormat
public import NLAlib.ForMathlib.Data.Nat.Log2

/-!
# Correct rounding in the Float logical model

Upstream candidates for the mathematical API of Lean core's floating-point model.
Adapted from the supplied NumLean archive, `NumLean/Data/Scalars/IEEE/Round.lean`. The archive's
SHA-256 and licensing status, the earlier Mathlib search and the changes needed for Lean 4.33
are recorded in `docs/design/Finite-Precision-Arithmetic.md`. No NumLean dependency is imported.
General format lemmas state a two-exponent-bit assumption explicitly where needed; core 4.33
also permits one-bit layouts. These results concern logical arithmetic, not native execution cost.

## Main results

* `Float.Model.UnpackedFloat.roundWithAccuracy_isCanonical`.
* `Float.Model.UnpackedFloat.abs_toReal_roundWithAccuracy_sub_le`.
* `Float.Model.UnpackedFloat.isNearestFloat_toReal_roundWithAccuracy`.
-/

@[expose] public section

namespace Float.Model.UnpackedFloat

open Float.Model.BinaryRounding

/-- The real value of an unpacked float; `0` for infinities and NaN. -/
noncomputable def toReal : UnpackedFloat → ℝ
  | .finite s m e _ => s.toReal * m * (2 : ℝ) ^ e
  | _ => 0

/-- The shape `pack` expects: exponent at least `minExponent`, at most `p` mantissa bits, and
exactly `p` bits unless the exponent is `minExponent` (subnormal). -/
def IsCanonical (spec : Format) : UnpackedFloat → Prop
  | .finite _ m e _ => spec.minExponent ≤ e ∧ m < 2 ^ spec.mantissaBits ∧
      (2 ^ (spec.mantissaBits - 1) ≤ m ∨ e = spec.minExponent)
  | _ => True

/-- The value of a canonical float is a float of the binary grid with `p = mantissaBits` and
`emin = minExponent`. -/
theorem isBinaryFloat_toReal {spec : Format} {x : UnpackedFloat} (hx : IsCanonical spec x) :
    IsBinaryFloat spec.mantissaBits spec.minExponent (toReal x) := by
  cases x with
  | finite s m e hm =>
    refine ⟨s.apply m, e, hx.1, ?_, ?_⟩
    · have : |s.apply m| = (m : ℤ) := by cases s <;> simp [Sign.apply]
      rw [this]
      exact_mod_cast hx.2.1
    · rw [Sign.cast_apply]
      simp only [toReal]
  | _ => exact isBinaryFloat_zero

/-- The total exponent is the binary logarithm of the mantissa plus one and the exponent. -/
theorem totalExponent_eq (m : ℕ) (e : ℤ) : totalExponent m e = (m.log2 : ℤ) + 1 + e := rfl

private theorem shiftRight_zero (em : ExtendedMantissa) : em >>> 0 = em := rfl

private theorem shiftRight_one (em : ExtendedMantissa) : em >>> 1 = em.shiftRightOne := rfl

/-- Second rounding stage: after rounding the mantissa to `r` at exponent `t`, renormalizing
is exact and canonical. -/
private theorem stage2 (spec : Format) (r : ℕ) (t : ℤ) (ht :
  spec.minExponent ≤ t)
    (hr : r ≤ 2 ^ spec.mantissaBits)
    (hlow : 2 ^ (spec.mantissaBits - 1) ≤ r ∨ (t = spec.minExponent ∧ r ≤ 2 ^ (spec.mantissaBits -
      1))) :
    let s₂ := (spec.targetExponent (totalExponent r t) - t).toNat
    let f := ((ExtendedMantissa.ofMantissaAndAccuracy r .exact) >>> s₂).mantissa
    (f : ℝ) * (2 : ℝ) ^ (t + s₂) = r * (2 : ℝ) ^ t ∧ (f = 0 ↔ r = 0) ∧
      (f ≠ 0 → spec.minExponent ≤ t + s₂ ∧ f < 2 ^ spec.mantissaBits ∧
        (2 ^ (spec.mantissaBits - 1) ≤ f ∨ t + s₂ = spec.minExponent)) := by
  intro s₂ f
  have hp := Format.two_le_mantissaBits spec
  set p := spec.mantissaBits with hpdef
  have hpow : (2 : ℕ) ^ p = 2 * 2 ^ (p - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hex : ExtendedMantissa.ofMantissaAndAccuracy r .exact = ⟨r, false, false⟩ := rfl
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · -- r = 0
    subst h0
    have : s₂ = 0 := by
      simp only [s₂, Format.targetExponent_eq, totalExponent_eq, Nat.log2_zero]
      omega
    simp only [f, this, hex, shiftRight_zero]
    simp
  have hl := (Nat.log2_eq_iff hpos.ne').mp rfl
  by_cases htop : r = 2 ^ p
  · -- mantissa overflowed to 2^p: shift once more
    have hlog : r.log2 = p := by rw [Nat.log2_eq_iff hpos.ne']; subst htop; constructor <;> [exact
      le_rfl; exact Nat.pow_lt_pow_succ (by norm_num)]
    have hs : s₂ = 1 := by
      simp only [s₂, Format.targetExponent_eq, totalExponent_eq, hlog]
      omega
    have hv := (ExtendedMantissa.approximates_exact r).shiftRight 1
    have hr2 : (r : ℝ) / 2 ^ 1 = ((2 ^ (p - 1) : ℕ) : ℝ) := by
      rw [htop, hpow]; push_cast; ring
    rw [hr2] at hv
    have hf : f = 2 ^ (p - 1) := by
      simp only [f, hex, hs]; exact hv.mantissa_eq_of_natCast
    refine ⟨?_, ?_, ?_⟩
    · rw [hf, hs, htop, hpow]; push_cast
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring
    · rw [hf]; constructor <;> intro h <;> [exact absurd h (by positivity); omega]
    · intro _
      rw [hf, hs]
      refine ⟨by omega, ?_, Or.inl le_rfl⟩
      rw [hpow]; have : 0 < 2 ^ (p - 1) := by positivity
      omega
  · -- no overflow: nothing to shift
    have hr' : r < 2 ^ p := lt_of_le_of_ne hr htop
    have hlog : r.log2 ≤ p - 1 := by
      have := (Nat.log2_lt hpos.ne').mpr (show r < 2 ^ (p - 1 + 1) by rwa [Nat.sub_add_cancel (by
        omega)])
      omega
    have hs : s₂ = 0 := by
      simp only [s₂, Format.targetExponent_eq, totalExponent_eq]
      rcases hlow with h | ⟨h1, h2⟩
      · have : r.log2 = p - 1 := by
          rw [Nat.log2_eq_iff hpos.ne']
          exact ⟨h, by rwa [Nat.sub_add_cancel (by omega)]⟩
        rw [this]; omega
      · omega
    have hf : f = r := by simp only [f, hex, hs, shiftRight_zero]
    refine ⟨by rw [hf, hs]; simp, by rw [hf], ?_⟩
    intro _
    rw [hf, hs]
    refine ⟨by simpa using ht, hr', ?_⟩
    rcases hlow with h | ⟨h1, _⟩
    · exact Or.inl h
    · right; simpa using h1

/-- The second half of `roundWithAccuracy`: renormalize the rounded mantissa `r` at `e₁`. -/
private def finish (spec : Format) (s : Sign) (r : ℕ) (e₁ : ℤ) : UnpackedFloat :=
  let (fem, fe) := shiftToTargetExponent spec r e₁ .exact
  if h : fem.mantissa = 0 then .zero s else .finite s fem.mantissa fe (Nat.pos_of_ne_zero h)

private theorem roundWithAccuracy_eq (spec : Format) (s : Sign) (m
  : ℕ) (e : ℤ) (acc : Accuracy) :
    roundWithAccuracy spec s m e acc =
      finish spec s (shiftToTargetExponent spec m e acc).1.roundedMantissa
        (shiftToTargetExponent spec m e acc).2 := rfl

private theorem finish_spec (spec : Format) (s : Sign) (r : ℕ) (t :
  ℤ) (ht : spec.minExponent ≤ t)
    (hr : r ≤ 2 ^ spec.mantissaBits)
    (hlow : 2 ^ (spec.mantissaBits - 1) ≤ r ∨ (t = spec.minExponent ∧ r ≤ 2 ^ (spec.mantissaBits -
      1))) :
    IsCanonical spec (finish spec s r t) ∧ toReal (finish spec s r t) = s.toReal * (r * 2 ^ t) := by
  have h2 := stage2 spec r t ht hr hlow
  simp only at h2
  obtain ⟨hval, hzero, hcan⟩ := h2
  unfold finish
  rcases hst : shiftToTargetExponent spec r t .exact with ⟨fem, fe⟩
  simp only [shiftToTargetExponent, shiftToExponent, Prod.mk.injEq] at hst
  obtain ⟨hfem, hfe⟩ := hst
  rw [hfem, hfe] at hval
  rw [hfem] at hzero
  rw [hfem, hfe] at hcan
  dsimp only
  by_cases h0 : fem.mantissa = 0
  · rw [dif_pos h0]
    have hr0 : r = 0 := hzero.mp h0
    refine ⟨trivial, ?_⟩
    simp [toReal, hr0]
  · rw [dif_neg h0]
    refine ⟨hcan h0, ?_⟩
    simp only [toReal]
    rw [mul_assoc, hval]

/-- Attaching an accuracy descriptor leaves the integral mantissa unchanged. -/
theorem ofMantissaAndAccuracy_mantissa (m : ℕ) (acc : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m acc).mantissa = m := by
  cases acc with
  | exact => rfl
  | inexact o => cases o <;> rfl

private theorem roundedMantissa_bounds (spec : Format)
    (m : ℕ) (e : ℤ) (acc : Accuracy) (w : ℝ)
    (hw : ExtendedMantissa.Approximates (ExtendedMantissa.ofMantissaAndAccuracy m acc) w)
    (he : e ≤ spec.targetExponent (totalExponent m e)) :
    let p := spec.mantissaBits
    let t := spec.targetExponent (totalExponent m e)
    let s₁ := (t - e).toNat
    let r := (ExtendedMantissa.ofMantissaAndAccuracy m acc >>> s₁).roundedMantissa
    r ≤ 2 ^ p ∧ (2 ^ (p - 1) ≤ r ∨ (t = spec.minExponent ∧ r ≤ 2 ^ (p - 1))) := by
  dsimp only
  have hp := Format.two_le_mantissaBits spec
  set p := spec.mantissaBits with hpdef
  set t := spec.targetExponent (totalExponent m e) with htdef
  have htmin : spec.minExponent ≤ t := le_max_right _ _
  have htT : totalExponent m e - p ≤ t := le_max_left _ _
  set s₁ := (t - e).toNat with hs₁def
  have hs₁ : (s₁ : ℤ) = t - e := Int.toNat_of_nonneg (by omega)
  have het : e + (s₁ : ℤ) = t := by omega
  set em₁ := ExtendedMantissa.ofMantissaAndAccuracy m acc >>> s₁
  have hv₁ : ExtendedMantissa.Approximates em₁ (w / 2 ^ s₁) := hw.shiftRight s₁
  set r := em₁.roundedMantissa with hrdef
  have hr := hv₁.abs_roundedMantissa_sub_le
  rw [abs_le] at hr
  have hl2 : m < 2 ^ (m.log2 + 1) := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · exact Nat.lt_log2_self
  have hwhi : w < ((2 ^ (m.log2 + 1) : ℕ) : ℝ) := by
    have := hw.lt; rw [ofMantissaAndAccuracy_mantissa] at this
    exact lt_of_lt_of_le this (by exact_mod_cast hl2)
  have h2s : (0 : ℝ) < 2 ^ s₁ := by positivity
  have hTt : (m.log2 : ℤ) + 1 + e - p ≤ t := htT
  -- bounds on the rounded mantissa
  have hrb : r ≤ 2 ^ p ∧ (2 ^ (p - 1) ≤ r ∨ (t = spec.minExponent ∧ r ≤ 2 ^ (p - 1))) := by
    by_cases hN : (m.log2 : ℤ) + 1 + e - p = t
    · -- normal range: s₁ + p = log₂ m + 1
      have hs : s₁ + p = m.log2 + 1 := by omega
      have hm0 : m ≠ 0 := by rintro rfl; rw [Nat.log2_zero] at hs; omega
      have hwlo : ((2 ^ m.log2 : ℕ) : ℝ) ≤ w := by
        have := hw.le; rw [ofMantissaAndAccuracy_mantissa] at this
        exact le_trans (by exact_mod_cast (Nat.log2_self_le hm0)) this
      have hlo : ((2 ^ (p - 1) : ℕ) : ℝ) ≤ w / 2 ^ s₁ := by
        rw [le_div_iff₀ h2s]
        have : (2 : ℝ) ^ (p - 1) * 2 ^ s₁ = 2 ^ m.log2 := by
          rw [← pow_add]; congr 1; omega
        push_cast at hwlo ⊢; linarith
      have hhi : w / 2 ^ s₁ < ((2 ^ p : ℕ) : ℝ) := by
        rw [div_lt_iff₀ h2s]
        have : (2 : ℝ) ^ p * 2 ^ s₁ = 2 ^ (m.log2 + 1) := by
          rw [← pow_add]; congr 1; omega
        push_cast at hwhi ⊢; linarith
      constructor
      · have : (r : ℝ) < ((2 ^ p : ℕ) : ℝ) + 1 := by linarith
        exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
      · left
        have : ((2 ^ (p - 1) : ℕ) : ℝ) < r + 1 := by linarith
        exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
    · -- subnormal range: t = minExponent and s₁ + p - 1 ≥ log₂ m + 1
      have htm : t = spec.minExponent := by
        have htmax : t = max (totalExponent m e - p) spec.minExponent := rfl
        rcases max_choice (totalExponent m e - p) spec.minExponent with h | h
        · exact absurd (htmax.trans h).symm hN
        · exact htmax.trans h
      have hs : m.log2 + 1 ≤ s₁ + (p - 1) := by omega
      have hhi : w / 2 ^ s₁ < ((2 ^ (p - 1) : ℕ) : ℝ) := by
        rw [div_lt_iff₀ h2s]
        have : (2 : ℝ) ^ (m.log2 + 1) ≤ 2 ^ (p - 1) * 2 ^ s₁ := by
          rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
        push_cast at hwhi ⊢; linarith
      have hr' : r ≤ 2 ^ (p - 1) := by
        have : (r : ℝ) < ((2 ^ (p - 1) : ℕ) : ℝ) + 1 := by linarith
        exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
      refine ⟨hr'.trans (Nat.pow_le_pow_right (by norm_num) (by omega)), Or.inr ⟨htm, hr'⟩⟩
  exact hrb

private theorem roundWithAccuracy_spec (spec : Format) (s : Sign)
  (m : ℕ) (e : ℤ) (acc : Accuracy)
    (w : ℝ) (hw : ExtendedMantissa.Approximates (ExtendedMantissa.ofMantissaAndAccuracy m acc) w)
    (he : e ≤ spec.targetExponent (totalExponent m e)) :
    IsCanonical spec (roundWithAccuracy spec s m e acc) ∧
    |toReal (roundWithAccuracy spec s m e acc) - s.toReal * (w * 2 ^ e)|
      ≤ (2 : ℝ) ^ (spec.targetExponent (totalExponent m e)) / 2 ∧
    IsNearestFloat spec.mantissaBits spec.minExponent (s.toReal * (w * 2 ^ e))
      (toReal (roundWithAccuracy spec s m e acc)) := by
  have hp := Format.two_le_mantissaBits spec
  set p := spec.mantissaBits with hpdef
  set t := spec.targetExponent (totalExponent m e) with htdef
  have htmin : spec.minExponent ≤ t := le_max_right _ _
  have htT : totalExponent m e - p ≤ t := le_max_left _ _
  set s₁ := (t - e).toNat with hs₁def
  have hs₁ : (s₁ : ℤ) = t - e := Int.toNat_of_nonneg (by omega)
  have het : e + (s₁ : ℤ) = t := by omega
  set em₁ := ExtendedMantissa.ofMantissaAndAccuracy m acc >>> s₁
  have hv₁ : ExtendedMantissa.Approximates em₁ (w / 2 ^ s₁) := hw.shiftRight s₁
  set r := em₁.roundedMantissa with hrdef
  have hr := hv₁.abs_roundedMantissa_sub_le
  rw [abs_le] at hr
  have hl2 : m < 2 ^ (m.log2 + 1) := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · exact Nat.lt_log2_self
  have hwhi : w < ((2 ^ (m.log2 + 1) : ℕ) : ℝ) := by
    have := hw.lt; rw [ofMantissaAndAccuracy_mantissa] at this
    exact lt_of_lt_of_le this (by exact_mod_cast hl2)
  have h2s : (0 : ℝ) < 2 ^ s₁ := by positivity
  have hTt : (m.log2 : ℤ) + 1 + e - p ≤ t := htT
  -- bounds on the rounded mantissa
  have hrb := roundedMantissa_bounds spec m e acc w hw he
  change r ≤ 2 ^ p ∧
    (2 ^ (p - 1) ≤ r ∨ (t = spec.minExponent ∧ r ≤ 2 ^ (p - 1))) at hrb
  have h2 := finish_spec spec s r (e + s₁) (het ▸ htmin) hrb.1 (by rw [het]; exact hrb.2)
  -- error at exponent t
  have herr : |(r : ℝ) * 2 ^ t - w * 2 ^ e| ≤ 2 ^ t / 2 := by
    have : (r : ℝ) * 2 ^ t - w * 2 ^ e = ((r : ℝ) - w / 2 ^ s₁) * 2 ^ t := by
      rw [← het, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
      field_simp
    rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ t)]
    have : |(r : ℝ) - w / 2 ^ s₁| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [(by positivity : (0 : ℝ) < 2 ^ t)]
  rw [roundWithAccuracy_eq]
  change IsCanonical spec (finish spec s r (e + s₁)) ∧
    |toReal (finish spec s r (e + s₁)) - s.toReal * (w * 2 ^ e)| ≤ 2 ^ t / 2 ∧
    IsNearestFloat p spec.minExponent (s.toReal * (w * 2 ^ e)) (toReal (finish spec s r (e + s₁)))
  have hbound : |toReal (finish spec s r (e + s₁)) - s.toReal * (w * 2 ^ e)| ≤ 2 ^ t / 2 := by
    rw [h2.2, het, ← mul_sub, abs_mul, Sign.abs_toReal, one_mul]
    exact herr
  refine ⟨h2.1, hbound, ?_⟩
  -- the lattice `2 ^ t ℤ` contains every float of magnitude below the exact value
  have hwm : (m : ℝ) ≤ w := by
    have := hw.le; rwa [ofMantissaAndAccuracy_mantissa] at this
  have habs : |s.toReal * (w * 2 ^ e)| = w * 2 ^ e := by
    rw [abs_mul, Sign.abs_toReal, one_mul,
      abs_of_nonneg (mul_nonneg ((Nat.cast_nonneg m).trans hwm) (by positivity))]
  have hlat : t = spec.minExponent ∨ (2 : ℝ) ^ (t + p - 1) ≤ |s.toReal * (w * 2 ^ e)| := by
    rcases max_choice (totalExponent m e - p) spec.minExponent with h | h
    · rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        exfalso
        have : t = totalExponent 0 e - p := h
        rw [totalExponent_eq] at this
        have he' : e ≤ t := het ▸ (by omega)
        simp at this
        omega
      · right
        have htp : t + p - 1 = (m.log2 : ℤ) + e := by
          have : t = totalExponent m e - p := h
          rw [totalExponent_eq] at this
          omega
        rw [habs, htp, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
        have h1 : (2 : ℝ) ^ m.log2 ≤ w :=
          le_trans (by exact_mod_cast (Nat.log2_self_le hpos.ne')) hwm
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    · left; exact h
  refine isNearestFloat_of_lattice (by omega) htmin hlat (isBinaryFloat_toReal h2.1)
    ⟨s.apply r, ?_⟩ hbound
  rw [h2.2, het, Sign.cast_apply]
  ring

/-- Rounding an extended mantissa that describes a real value produces canonical unpacked
data when the input exponent is no larger than the target exponent. -/
theorem roundWithAccuracy_isCanonical (spec : Format) (s : Sign) (m
  : ℕ) (e : ℤ) (acc : Accuracy)
    (w : ℝ) (hw : ExtendedMantissa.Approximates (ExtendedMantissa.ofMantissaAndAccuracy m acc) w)
    (he : e ≤ spec.targetExponent (totalExponent m e)) :
    IsCanonical spec (roundWithAccuracy spec s m e acc) :=
  (roundWithAccuracy_spec spec s m e acc w hw he).1

/-- `roundWithAccuracy` is within half a unit in the last place (at the target exponent) of the
exact value `s * (w * 2 ^ e)`. -/
theorem abs_toReal_roundWithAccuracy_sub_le (spec : Format) (s :
  Sign) (m : ℕ) (e : ℤ)
    (acc : Accuracy) (w : ℝ)
    (hw : ExtendedMantissa.Approximates (ExtendedMantissa.ofMantissaAndAccuracy m acc) w)
    (he : e ≤ spec.targetExponent (totalExponent m e)) :
    |(roundWithAccuracy spec s m e acc).toReal - s.toReal * (w * 2 ^ e)|
      ≤ (2 : ℝ) ^ (spec.targetExponent (totalExponent m e)) / 2 :=
  (roundWithAccuracy_spec spec s m e acc w hw he).2.1

/-- `roundWithAccuracy` is a nearest float of the exact value `s * (w * 2 ^ e)`. -/
theorem isNearestFloat_toReal_roundWithAccuracy (spec : Format) (s
  : Sign) (m : ℕ) (e : ℤ)
    (acc : Accuracy) (w : ℝ)
    (hw : ExtendedMantissa.Approximates (ExtendedMantissa.ofMantissaAndAccuracy m acc) w)
    (he : e ≤ spec.targetExponent (totalExponent m e)) :
    IsNearestFloat spec.mantissaBits spec.minExponent (s.toReal * (w * 2 ^ e))
      (toReal (roundWithAccuracy spec s m e acc)) :=
  (roundWithAccuracy_spec spec s m e acc w hw he).2.2

/-- Rounding always returns a finite unpacked value. Its exponent is not bounded above;
packing may still overflow to infinity. -/
theorem isFinite_roundWithAccuracy (spec : Format) (s : Sign) (m :
  ℕ) (e : ℤ) (acc : Accuracy) :
    (roundWithAccuracy spec s m e acc).IsFinite := by
  rw [roundWithAccuracy_eq]
  unfold finish
  dsimp only
  split <;> rfl

/-- An exact positive integral mantissa already at its target exponent rounds without error. -/
theorem toReal_roundWithAccuracy_exact (spec : Format) (s : Sign)
  (m : ℕ) (e : ℤ) (hm : 0 < m)
    (he : e = spec.targetExponent (totalExponent m e)) :
    toReal (roundWithAccuracy spec s m e .exact) = s.toReal * (m * 2 ^ e) := by
  have hp := Format.two_le_mantissaBits spec
  set p := spec.mantissaBits
  have hl := (Nat.log2_eq_iff hm.ne').mp rfl
  have htT : (m.log2 : ℤ) + 1 + e - p ≤ e := by
    have := le_max_left (totalExponent m e - p) spec.minExponent
    rw [← Format.targetExponent_eq, ← he] at this; exact this
  have hmin : spec.minExponent ≤ e := by
    have := le_max_right (totalExponent m e - p) spec.minExponent
    rw [← Format.targetExponent_eq, ← he] at this; exact this
  have hlog : m.log2 + 1 ≤ p := by omega
  have hmp : m < 2 ^ (p - 1 + 1) :=
    lt_of_lt_of_le hl.2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.sub_add_cancel (by omega)] at hmp
  have hlow : 2 ^ (p - 1) ≤ m ∨ (e = spec.minExponent ∧ m ≤ 2 ^ (p - 1)) := by
    by_cases hN : (m.log2 : ℤ) + 1 + e - p = e
    · left
      have : m.log2 = p - 1 := by omega
      rw [← this]; exact hl.1
    · right
      have htm : e = spec.minExponent := by
        have htmax : e = max (totalExponent m e - p) spec.minExponent := he
        rcases max_choice (totalExponent m e - p) spec.minExponent with h | h
        · exact absurd (htmax.trans h).symm hN
        · exact htmax.trans h
      refine ⟨htm, ?_⟩
      have : m.log2 + 1 ≤ p - 1 := by omega
      exact (lt_of_lt_of_le hl.2 (Nat.pow_le_pow_right (by norm_num) this)).le
  have h2 := finish_spec spec s m e hmin (le_trans hmp.le le_rfl) hlow
  rw [roundWithAccuracy_eq]
  have hs : (spec.targetExponent (totalExponent m e) - e).toNat = 0 := by omega
  have : shiftToTargetExponent spec m e .exact = (⟨m, false, false⟩, e) := by
    simp only [shiftToTargetExponent, shiftToExponent, hs, Nat.cast_zero, add_zero]
    rfl
  rw [this]
  exact h2.2


/-- Half a unit in the last place is bounded by relative rounding plus half-subnormal spacing. -/
theorem div_pow_targetExponent_le (spec : Format) (m : ℕ) (e : ℤ) (w : ℝ)
    (hm : 0 < m) (hw : (m : ℝ) ≤ w) :
    (2 : ℝ) ^ (spec.targetExponent (totalExponent m e)) / 2
      ≤ spec.unitRoundoff * (w * 2 ^ e) + spec.underflowBound := by
  have hl := (Nat.log2_eq_iff hm.ne').mp rfl
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hA : 0 ≤ spec.unitRoundoff * (w * 2 ^ e) := by
    have : (0 : ℝ) ≤ w := le_trans (Nat.cast_nonneg _) hw
    positivity
  rw [Format.targetExponent_eq]
  rcases max_choice (totalExponent m e - spec.mantissaBits) spec.minExponent with h | h
  · rw [h]
    have : (2 : ℝ) ^ (totalExponent m e - spec.mantissaBits) / 2
        = spec.unitRoundoff * ((2 : ℝ) ^ (m.log2 : ℕ) * 2 ^ e) := by
      rw [Format.unitRoundoff, totalExponent_eq, ← zpow_natCast, ← zpow_add₀ h2.ne',
        ← zpow_add₀ h2.ne', div_eq_iff h2.ne', ← zpow_add_one₀ h2.ne']
      congr 1; ring
    rw [this]
    have hm2 : (2 : ℝ) ^ (m.log2 : ℕ) ≤ w := le_trans (by exact_mod_cast hl.1) hw
    have : (2 : ℝ) ^ (m.log2 : ℕ) * 2 ^ e ≤ w * 2 ^ e :=
      mul_le_mul_of_nonneg_right hm2 (by positivity)
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ spec.unitRoundoff)
    have : (0 : ℝ) ≤ spec.underflowBound := by positivity
    linarith
  · rw [h]; unfold Format.underflowBound; linarith

/-- In the normal range, half an ulp is at most `2⁻ᵖ |v|`. -/
theorem div_pow_targetExponent_le_of_lt (spec : Format) (m : ℕ) (e : ℤ) (w : ℝ)
    (hm : 0 < m) (hw : (m : ℝ) ≤ w)
    (hn : spec.minExponent < spec.targetExponent (totalExponent m e)) :
    (2 : ℝ) ^ (spec.targetExponent (totalExponent m e)) / 2
      ≤ spec.unitRoundoff * (w * 2 ^ e) := by
  have hl := (Nat.log2_eq_iff hm.ne').mp rfl
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [Format.targetExponent_eq] at hn ⊢
  rcases max_choice (totalExponent m e - spec.mantissaBits) spec.minExponent with h | h
  · rw [h]
    have : (2 : ℝ) ^ (totalExponent m e - spec.mantissaBits) / 2
        = spec.unitRoundoff * ((2 : ℝ) ^ (m.log2 : ℕ) * 2 ^ e) := by
      rw [Format.unitRoundoff, totalExponent_eq, ← zpow_natCast, ← zpow_add₀ h2.ne',
        ← zpow_add₀ h2.ne', div_eq_iff h2.ne', ← zpow_add_one₀ h2.ne']
      congr 1; ring
    rw [this]
    have hm2 : (2 : ℝ) ^ (m.log2 : ℕ) ≤ w := le_trans (by exact_mod_cast hl.1) hw
    have : (2 : ℝ) ^ (m.log2 : ℕ) * 2 ^ e ≤ w * 2 ^ e :=
      mul_le_mul_of_nonneg_right hm2 (by positivity)
    exact mul_le_mul_of_nonneg_left this (by positivity)
  · rw [h] at hn; exact absurd hn (lt_irrefl _)

/-- `div_pow_targetExponent_le` without `0 < m`, for inputs at or below the target exponent. -/
theorem div_pow_targetExponent_le_of_le_targetExponent (spec : Format)
    (m : ℕ) (e : ℤ) (w : ℝ) (hw : (m : ℝ) ≤ w)
    (he : e ≤ spec.targetExponent (totalExponent m e)) :
    (2 : ℝ) ^ (spec.targetExponent (totalExponent m e)) / 2
      ≤ spec.unitRoundoff * (w * 2 ^ e) + spec.underflowBound := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    have hp := Format.two_le_mantissaBits spec
    have ht : spec.targetExponent (totalExponent 0 e) = spec.minExponent := by
      have := he
      rw [Format.targetExponent_eq, totalExponent_eq, Nat.log2_zero] at this ⊢
      rcases max_choice ((0 : ℕ) + 1 + e - spec.mantissaBits) spec.minExponent with h | h
      · rw [h] at this; push_cast at this; omega
      · exact h
    rw [ht]
    have : (0 : ℝ) ≤ w := by simpa using hw
    have : 0 ≤ spec.unitRoundoff * (w * 2 ^ e) := by positivity
    unfold Format.underflowBound
    linarith
  · exact div_pow_targetExponent_le spec m e w h hw

end Float.Model.UnpackedFloat
