/-
Copyright (c) 2026 NumLean contributors and NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NumLean contributors, NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Float.Pack

/-!
# Arithmetic accuracy of the Float logical model

Upstream candidates for the mathematical API of Lean core's floating-point model.
Adapted from the supplied NumLean archive, `NumLean/Data/Scalars/IEEE/Ops.lean`. The archive's
SHA-256 and licensing status, the earlier Mathlib search and the changes needed for Lean 4.33
are recorded in `docs/design/Finite-Precision-Arithmetic.md`. No NumLean dependency is imported.
General format lemmas state a two-exponent-bit assumption explicitly where needed; core 4.33
also permits one-bit layouts. These results concern logical arithmetic, not native execution cost.

## Main results

* `Float.Model.UnpackedFloat.abs_toReal_add_sub_le`.
* `Float.Model.UnpackedFloat.abs_toReal_mul_sub_le`.
* `Float.Model.UnpackedFloat.abs_toReal_div_sub_le`.
-/

@[expose] public section

namespace Float.Model.UnpackedFloat

open Float.Model.BinaryRounding

variable {spec : Format}

/-! ## `round` and `normalize` -/

/-- Exact inputs at an exponent `≥ minExponent` round with relative error `2⁻ᵖ`, no underflow
term (the underflow range is a fixed-point grid that contains the input). -/
private theorem round_spec (s : Sign) (m : ℕ) (e : ℤ) (hm : 0 < m) (he : spec.minExponent ≤ e) :
    IsCanonical spec (UnpackedFloat.round spec s m e) ∧
    |toReal (UnpackedFloat.round spec s m e) - s.toReal * (m * 2 ^ e)|
      ≤ spec.unitRoundoff * (m * 2 ^ e) ∧
    IsNearestFloat spec.mantissaBits spec.minExponent (s.toReal * (m * 2 ^ e))
      (toReal (UnpackedFloat.round spec s m e)) := by
  unfold UnpackedFloat.round decreaseExponent
  simp only
  generalize ht : spec.targetExponent (totalExponent m e) = t
  generalize hk : (e - t).toNat = k
  have hk' : (k : ℤ) = max (e - t) 0 := by rw [← hk]; omega
  have hm' : 0 < m <<< k := by rw [Nat.shiftLeft_eq]; positivity
  have htot : totalExponent (m <<< k) (e - k) = totalExponent m e := by
    rw [totalExponent_eq, totalExponent_eq, Nat.shiftLeft_eq, Nat.log2_mul_pow hm.ne']
    push_cast; ring
  have hval : ((m <<< k : ℕ) : ℝ) * (2 : ℝ) ^ (e - k) = m * 2 ^ e := by
    rw [Nat.shiftLeft_eq, zpow_sub₀ (by norm_num)]; push_cast
    rw [zpow_natCast]; field_simp
  have hle : e - k ≤ spec.targetExponent (totalExponent (m <<< k) (e - k)) := by
    rw [htot, ht]; omega
  have hspec := And.intro
    (roundWithAccuracy_isCanonical spec s (m <<< k) (e - k) .exact (m <<< k)
      (ExtendedMantissa.approximates_exact _) hle)
    (abs_toReal_roundWithAccuracy_sub_le spec s (m <<< k) (e - k) .exact (m <<< k)
      (ExtendedMantissa.approximates_exact _) hle)
  have hnear := isNearestFloat_toReal_roundWithAccuracy spec s (m <<< k) (e - k) .exact
    (m <<< k) (ExtendedMantissa.approximates_exact _) hle
  rw [hval] at hspec hnear
  refine ⟨hspec.1, ?_, hnear⟩
  by_cases hek : e - k = t
  · have := toReal_roundWithAccuracy_exact spec s (m <<< k) (e - k) hm' (by rw [htot, ht, hek])
    rw [this, hval, sub_self, abs_zero]
    positivity
  · refine hspec.2.trans ?_
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [Nat.shiftLeft_zero, Nat.cast_zero, sub_zero] at hspec ⊢
    rw [ht]
    have := div_pow_targetExponent_le_of_lt spec m e m hm le_rfl (by rw [ht]; omega)
    rwa [ht] at this
theorem round_isCanonical (s : Sign) (m : ℕ) (e : ℤ) (hm : 0 < m) (he : spec.minExponent ≤ e) :
    IsCanonical spec (UnpackedFloat.round spec s m e) :=
  (round_spec s m e hm he).1

theorem isFinite_round (s : Sign) (m : ℕ) (e : ℤ) :
    (UnpackedFloat.round spec s m e).IsFinite := by
  unfold UnpackedFloat.round; simp only; exact isFinite_roundWithAccuracy _ _ _ _ _

/-- Exact inputs at an exponent `≥ minExponent` round with relative error `2⁻ᵖ`, no underflow
term (the underflow range is a fixed-point grid that contains the input). -/
theorem abs_toReal_round_sub_le (s : Sign) (m : ℕ) (e : ℤ) (hm : 0 < m)
    (he : spec.minExponent ≤ e) :
    |toReal (UnpackedFloat.round spec s m e) - s.toReal * (m * 2 ^ e)|
      ≤ spec.unitRoundoff * (m * 2 ^ e) :=
  (round_spec s m e hm he).2.1

/-- Exact inputs at an exponent `≥ minExponent` round to a nearest float of the format. -/
theorem isNearestFloat_toReal_round (s : Sign) (m : ℕ) (e : ℤ) (hm : 0 < m)
    (he : spec.minExponent ≤ e) :
    IsNearestFloat spec.mantissaBits spec.minExponent (s.toReal * (m * 2 ^ e))
      (toReal (UnpackedFloat.round spec s m e)) :=
  (round_spec s m e hm he).2.2
private theorem normalize_spec (M : ℤ) (e : ℤ) (zs : Sign) (he : spec.minExponent ≤ e) :
    IsCanonical spec (UnpackedFloat.normalize spec M e zs) ∧
    |toReal (UnpackedFloat.normalize spec M e zs) - (M : ℝ) * 2 ^ e|
      ≤ spec.unitRoundoff * |(M : ℝ) * 2 ^ e| ∧
    IsNearestFloat spec.mantissaBits spec.minExponent ((M : ℝ) * 2 ^ e)
      (toReal (UnpackedFloat.normalize spec M e zs)) := by
  unfold UnpackedFloat.normalize
  rcases lt_trichotomy M 0 with h | h | h
  · rw [Int.compare_eq_lt.mpr h]
    have hpos : 0 < (-M).toNat := by omega
    have := round_spec (spec := spec) .negative (-M).toNat e hpos he
    have hc : (((-M).toNat : ℕ) : ℝ) = -M := by
      have : ((-M).toNat : ℤ) = -M := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [hc] at this
    have hv : Sign.negative.toReal * (-(M : ℝ) * 2 ^ e) = (M : ℝ) * 2 ^ e := by
      simp [Sign.toReal]
    refine ⟨this.1, ?_, by simpa only [hv] using this.2.2⟩
    have habs : |(M : ℝ) * 2 ^ e| = -M * 2 ^ e := by
      rw [abs_of_neg (mul_neg_of_neg_of_pos (by exact_mod_cast h) (by positivity : (0 : ℝ) < 2 ^
        e))]; ring
    rw [habs]
    convert this.2.1 using 2
    simp [Sign.toReal]
  · subst h; rw [Int.compare_eq_eq.mpr rfl]
    exact ⟨trivial, by simp [toReal], by
      simpa [toReal] using isNearestFloat_self (p := spec.mantissaBits)
        (emin := spec.minExponent) isBinaryFloat_zero⟩
  · rw [Int.compare_eq_gt.mpr h]
    have hpos : 0 < M.toNat := by omega
    have := round_spec (spec := spec) .positive M.toNat e hpos he
    have hc : ((M.toNat : ℕ) : ℝ) = M := by
      have : (M.toNat : ℤ) = M := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [hc] at this
    have hv : Sign.positive.toReal * ((M : ℝ) * 2 ^ e) = (M : ℝ) * 2 ^ e := by
      simp [Sign.toReal]
    refine ⟨this.1, ?_, by simpa only [hv] using this.2.2⟩
    rw [abs_of_pos (mul_pos (by exact_mod_cast h) (by positivity : (0 : ℝ) < 2 ^ e))]
    convert this.2.1 using 2
    simp [Sign.toReal]

theorem isFinite_normalize (M : ℤ) (e : ℤ) (zs : Sign) :
    (UnpackedFloat.normalize spec M e zs).IsFinite := by
  unfold UnpackedFloat.normalize
  split
  · exact isFinite_roundWithAccuracy _ _ _ _ _
  · rfl
  · exact isFinite_roundWithAccuracy _ _ _ _ _
theorem normalize_isCanonical (M : ℤ) (e : ℤ) (zs : Sign) (he : spec.minExponent ≤ e) :
    IsCanonical spec (UnpackedFloat.normalize spec M e zs) :=
  (normalize_spec M e zs he).1
theorem abs_toReal_normalize_sub_le (M : ℤ) (e : ℤ) (zs : Sign) (he : spec.minExponent ≤ e) :
    |toReal (UnpackedFloat.normalize spec M e zs) - (M : ℝ) * 2 ^ e|
      ≤ spec.unitRoundoff * |(M : ℝ) * 2 ^ e| :=
  (normalize_spec M e zs he).2.1

/-- `normalize` returns a nearest float of the exact value `M · 2^e`. -/
theorem isNearestFloat_toReal_normalize (M : ℤ) (e : ℤ) (zs : Sign)
    (he : spec.minExponent ≤ e) :
    IsNearestFloat spec.mantissaBits spec.minExponent ((M : ℝ) * 2 ^ e)
      (toReal (UnpackedFloat.normalize spec M e zs)) :=
  (normalize_spec M e zs he).2.2



/-! ## Arithmetic -/
theorem shift_val (m : ℕ) (e t : ℤ) (h : t ≤ e) :
    ((m <<< (e - t).toNat : ℕ) : ℝ) * (2 : ℝ) ^ t = m * 2 ^ e := by
  rw [Nat.shiftLeft_eq]; push_cast
  rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), mul_assoc, ← zpow_add₀ (by norm_num)]
  congr 2; ring

/-- Aligning two finite floats to the smaller exponent and adding the signed integer mantissas
gives the exact sum. -/
theorem toReal_aligned_add (s₁ : Sign) (m₁ : ℕ) (e₁ : ℤ) (hm₁ : 0 < m₁) (s₂ : Sign) (m₂ : ℕ)
    (e₂ : ℤ) (hm₂ : 0 < m₂) :
    (((s₁.apply ↑(decreaseExponent m₁ e₁ (min e₁ e₂)).1 +
        s₂.apply ↑(decreaseExponent m₂ e₂ (min e₁ e₂)).1 : ℤ) : ℝ)) * 2 ^ (min e₁ e₂)
      = toReal (.finite s₁ m₁ e₁ hm₁) + toReal (.finite s₂ m₂ e₂ hm₂) := by
  simp only [decreaseExponent, Int.cast_add, Sign.cast_apply, toReal]
  rw [add_mul, mul_assoc, mul_assoc, shift_val _ _ _ (min_le_left _ _),
    shift_val _ _ _ (min_le_right _ _), mul_assoc, mul_assoc]
private theorem add_spec (x y : UnpackedFloat)
    (hx : IsCanonical spec x) (hy : IsCanonical spec y) :
    IsCanonical spec (UnpackedFloat.add spec x y) ∧
    ((UnpackedFloat.add spec x y).IsFinite → x.IsFinite ∧ y.IsFinite ∧
      |toReal (UnpackedFloat.add spec x y) - (toReal x + toReal y)|
        ≤ spec.unitRoundoff * |toReal x + toReal y| ∧
      IsNearestFloat spec.mantissaBits spec.minExponent (toReal x + toReal y)
        (toReal (UnpackedFloat.add spec x y))) := by
  cases x <;> cases y <;> simp only [UnpackedFloat.add]
  case finite.finite s₁ m₁ e₁ hm₁ s₂ m₂ e₂ hm₂ =>
    have := normalize_spec (spec := spec) (s₁.apply ↑(decreaseExponent m₁ e₁ (min e₁ e₂)).1 +
        s₂.apply ↑(decreaseExponent m₂ e₂ (min e₁ e₂)).1) (min e₁ e₂) .positive
      (le_min hx.1 hy.1)
    rw [toReal_aligned_add _ _ _ hm₁ _ _ _ hm₂] at this
    exact ⟨this.1, fun _ => ⟨rfl, rfl, this.2.1, this.2.2⟩⟩
  all_goals (try split) <;>
    simp only [IsCanonical, IsFinite, isFinite, Bool.false_eq_true, toReal, add_zero, sub_self,
    abs_zero, mul_zero, Std.le_refl, true_and, false_and, and_self, imp_self, zero_add,
    zero_sub, abs_neg, abs_mul, Sign.abs_toReal, Nat.abs_cast, one_mul, abs_zpow, Nat.abs_ofNat,
    and_false, forall_const]
  all_goals first
    | exact isNearestFloat_self isBinaryFloat_zero
    | exact ⟨hx, by positivity, isNearestFloat_self (isBinaryFloat_toReal hx)⟩
    | exact ⟨hy, by positivity, isNearestFloat_self (isBinaryFloat_toReal hy)⟩

/-- Finite operands give a finite result (before packing, so without overflow). -/
theorem isFinite_add_of_isFinite (x y : UnpackedFloat) (hx : x.IsFinite) (hy : y.IsFinite) :
    (UnpackedFloat.add spec x y).IsFinite := by
  cases x <;> cases y <;>
    first
    | (simp [IsFinite, isFinite] at hx; done)
    | (simp [IsFinite, isFinite] at hy; done)
    | (simp only [UnpackedFloat.add]
       first
       | exact isFinite_normalize _ _ _
       | assumption
       | (split <;> rfl))
theorem add_isCanonical (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) : IsCanonical spec (UnpackedFloat.add spec x y) :=
  (add_spec x y hx hy).1

/-- A finite result has finite operands. -/
theorem isFinite_of_isFinite_add (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) (h : (UnpackedFloat.add spec x y).IsFinite) :
    x.IsFinite ∧ y.IsFinite :=
  let h := (add_spec x y hx hy).2 h
  ⟨h.1, h.2.1⟩
theorem abs_toReal_add_sub_le (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) (h : (UnpackedFloat.add spec x y).IsFinite) :
    |toReal (UnpackedFloat.add spec x y) - (toReal x + toReal y)|
      ≤ spec.unitRoundoff * |toReal x + toReal y| :=
  ((add_spec x y hx hy).2 h).2.2.1

/-- A finite result of `add` is a nearest float of the exact result. -/
theorem isNearestFloat_toReal_add (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) (h : (UnpackedFloat.add spec x y).IsFinite) :
    IsNearestFloat spec.mantissaBits spec.minExponent (toReal x + toReal y)
      (toReal (UnpackedFloat.add spec x y)) :=
  ((add_spec x y hx hy).2 h).2.2.2


theorem neg_isCanonical (x : UnpackedFloat) (hx : IsCanonical spec x) :
    IsCanonical spec x.neg := by
  cases x <;> simp only [UnpackedFloat.neg, IsCanonical] at hx ⊢
  all_goals exact hx

theorem isFinite_neg (x : UnpackedFloat) : x.neg.IsFinite ↔ x.IsFinite := by
  cases x <;> simp [UnpackedFloat.neg, IsFinite, isFinite]

theorem toReal_neg (x : UnpackedFloat) : toReal x.neg = -toReal x := by
  cases x <;> simp [UnpackedFloat.neg, toReal]

/-- `sub` is `add` of the negation, in every case: core's `sub` is `add` with `y`'s sign flipped. -/
theorem sub_eq_add_neg (x y : UnpackedFloat) :
    UnpackedFloat.sub spec x y = UnpackedFloat.add spec x y.neg := by
  cases x <;> cases y <;> simp only [UnpackedFloat.sub, UnpackedFloat.add, UnpackedFloat.neg]
  case finite.finite _ _ _ _ s₂ _ _ _ =>
    cases s₂ <;> simp [Sign.apply, _root_.sub_eq_add_neg]

/-- Finite operands give a finite result (before packing, so without overflow). -/
theorem isFinite_sub_of_isFinite (x y : UnpackedFloat) (hx : x.IsFinite) (hy : y.IsFinite) :
    (UnpackedFloat.sub spec x y).IsFinite := by
  rw [sub_eq_add_neg]
  exact isFinite_add_of_isFinite x y.neg hx ((isFinite_neg y).2 hy)
theorem sub_isCanonical (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) : IsCanonical spec (UnpackedFloat.sub spec x y) := by
  rw [sub_eq_add_neg]
  exact add_isCanonical x y.neg hx (neg_isCanonical y hy)

/-- A finite result has finite operands. -/
theorem isFinite_of_isFinite_sub (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) (h : (UnpackedFloat.sub spec x y).IsFinite) :
    x.IsFinite ∧ y.IsFinite := by
  rw [sub_eq_add_neg] at h
  have := isFinite_of_isFinite_add x y.neg hx (neg_isCanonical y hy) h
  exact ⟨this.1, (isFinite_neg y).1 this.2⟩
theorem abs_toReal_sub_sub_le (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) (h : (UnpackedFloat.sub spec x y).IsFinite) :
    |toReal (UnpackedFloat.sub spec x y) - (toReal x - toReal y)|
      ≤ spec.unitRoundoff * |toReal x - toReal y| := by
  rw [sub_eq_add_neg] at h ⊢
  have := abs_toReal_add_sub_le x y.neg hx (neg_isCanonical y hy) h
  rwa [toReal_neg, ← _root_.sub_eq_add_neg] at this

/-- A finite result of `sub` is a nearest float of the exact result. -/
theorem isNearestFloat_toReal_sub (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) (h : (UnpackedFloat.sub spec x y).IsFinite) :
    IsNearestFloat spec.mantissaBits spec.minExponent (toReal x - toReal y)
      (toReal (UnpackedFloat.sub spec x y)) := by
  rw [sub_eq_add_neg] at h ⊢
  have := isNearestFloat_toReal_add x y.neg hx (neg_isCanonical y hy) h
  rwa [toReal_neg, ← _root_.sub_eq_add_neg] at this


/-- Multiplying two finite values, not necessarily canonical, when the exponent of the product
is low enough: the result is canonical, within the standard model of the exact product, and a
nearest float of it. -/
private theorem mul_finite_spec (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) (s₁ s₂ : Sign) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂)
    (he : e₁ + e₂ ≤ spec.targetExponent (totalExponent (m₁ * m₂) (e₁ + e₂))) :
    let r := UnpackedFloat.mul spec (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂)
    IsCanonical spec r ∧
    |toReal r - toReal (.finite s₁ m₁ e₁ hm₁) * toReal (.finite s₂ m₂ e₂ hm₂)|
      ≤ spec.unitRoundoff *
          |toReal (.finite s₁ m₁ e₁ hm₁) * toReal (.finite s₂ m₂ e₂ hm₂)|
        + spec.underflowBound ∧
    IsNearestFloat spec.mantissaBits spec.minExponent
      (toReal (.finite s₁ m₁ e₁ hm₁) * toReal (.finite s₂ m₂ e₂ hm₂)) (toReal r) := by
  intro r
  simp only [r, UnpackedFloat.mul]
  have hs := And.intro
    (roundWithAccuracy_isCanonical spec (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) .exact
      ((m₁ * m₂ : ℕ) : ℝ) (ExtendedMantissa.approximates_exact _) he)
    (abs_toReal_roundWithAccuracy_sub_le spec (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) .exact
      ((m₁ * m₂ : ℕ) : ℝ) (ExtendedMantissa.approximates_exact _) he)
  have hnear := isNearestFloat_toReal_roundWithAccuracy spec (s₁ * s₂) (m₁ * m₂) (e₁ + e₂)
    .exact ((m₁ * m₂ : ℕ) : ℝ) (ExtendedMantissa.approximates_exact _) he
  have hh := div_pow_targetExponent_le_of_le_targetExponent spec (m₁ * m₂) (e₁ + e₂) _ le_rfl he
  have hv : toReal (.finite s₁ m₁ e₁ hm₁) * toReal (.finite s₂ m₂ e₂ hm₂)
      = (s₁ * s₂).toReal * (((m₁ * m₂ : ℕ) : ℝ) * 2 ^ (e₁ + e₂)) := by
    simp only [toReal, Sign.toReal_mul, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; push_cast; ring
  have habs : |toReal (.finite s₁ m₁ e₁ hm₁) * toReal (.finite s₂ m₂ e₂ hm₂)|
      = ((m₁ * m₂ : ℕ) : ℝ) * 2 ^ (e₁ + e₂) := by
    rw [hv, abs_mul, Sign.abs_toReal, one_mul, abs_of_nonneg (by positivity)]
  refine ⟨hs.1, ?_, by rwa [hv]⟩
  rw [habs, hv]
  exact hs.2.trans hh
theorem mul_finite_isCanonical (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) (s₁ s₂ : Sign) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂)
    (he : e₁ + e₂ ≤ spec.targetExponent (totalExponent (m₁ * m₂) (e₁ + e₂))) :
    IsCanonical spec (UnpackedFloat.mul spec (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂)) :=
  (mul_finite_spec m₁ m₂ e₁ e₂ s₁ s₂ hm₁ hm₂ he).1

/-- Multiplying two finite values, not necessarily canonical, when the exponent of the product
is low enough. -/
theorem abs_toReal_mul_finite_sub_le (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) (s₁ s₂ : Sign) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂)
    (he : e₁ + e₂ ≤ spec.targetExponent (totalExponent (m₁ * m₂) (e₁ + e₂))) :
    |toReal (UnpackedFloat.mul spec (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂))
        - toReal (.finite s₁ m₁ e₁ hm₁) * toReal (.finite s₂ m₂ e₂ hm₂)|
      ≤ spec.unitRoundoff *
          |toReal (.finite s₁ m₁ e₁ hm₁) * toReal (.finite s₂ m₂ e₂ hm₂)|
        + spec.underflowBound :=
  (mul_finite_spec m₁ m₂ e₁ e₂ s₁ s₂ hm₁ hm₂ he).2.1

private theorem mul_spec [Fact (2 ≤ spec.exponentBits)] (x y : UnpackedFloat)
    (hx : IsCanonical spec x) (hy : IsCanonical spec y) :
    IsCanonical spec (UnpackedFloat.mul spec x y) ∧
    ((UnpackedFloat.mul spec x y).IsFinite → x.IsFinite ∧ y.IsFinite ∧
      |toReal (UnpackedFloat.mul spec x y) - toReal x * toReal y|
        ≤ spec.unitRoundoff * |toReal x * toReal y|
          + spec.underflowBound ∧
      IsNearestFloat spec.mantissaBits spec.minExponent (toReal x * toReal y)
        (toReal (UnpackedFloat.mul spec x y))) := by
  cases x <;> cases y <;> simp only [UnpackedFloat.mul]
  case finite.finite s₁ m₁ e₁ hm₁ s₂ m₂ e₂ hm₂ =>
    have he : e₁ + e₂ ≤ spec.targetExponent (totalExponent (m₁ * m₂) (e₁ + e₂)) := by
      obtain ⟨h1, -, h1''⟩ := hx
      obtain ⟨h2, -, h2''⟩ := hy
      have hp := Format.two_le_mantissaBits spec
      have hneg := Format.minExponent_lt_zero spec
      rw [Format.targetExponent_eq, totalExponent_eq]
      rcases h1'' with h | h
      · have : spec.mantissaBits - 1 ≤ (m₁ * m₂).log2 :=
          (Nat.le_log2 (by positivity)).mpr (le_trans h (Nat.le_mul_of_pos_right _ hm₂))
        apply le_max_of_le_left; omega
      · rcases h2'' with h' | h'
        · have : spec.mantissaBits - 1 ≤ (m₁ * m₂).log2 :=
            (Nat.le_log2 (by positivity)).mpr (le_trans h' (Nat.le_mul_of_pos_left _ hm₁))
          apply le_max_of_le_left; omega
        · apply le_max_of_le_right; omega
    obtain ⟨hc, herr, hnear⟩ := mul_finite_spec m₁ m₂ e₁ e₂ s₁ s₂ hm₁ hm₂ he
    exact ⟨hc, fun _ => ⟨rfl, rfl, herr, hnear⟩⟩
  all_goals
    simp only [IsCanonical, IsFinite, isFinite, Bool.false_eq_true, toReal, mul_zero, sub_self,
    abs_zero, zero_add, false_and, and_self, imp_self, true_and, zero_mul, and_false,
    forall_const]
  all_goals exact ⟨by positivity, isNearestFloat_self isBinaryFloat_zero⟩

/-- Finite operands give a finite result (before packing, so without overflow). -/
theorem isFinite_mul_of_isFinite (x y : UnpackedFloat) (hx : x.IsFinite) (hy : y.IsFinite) :
    (UnpackedFloat.mul spec x y).IsFinite := by
  cases x <;> cases y <;>
    first
    | (simp [IsFinite, isFinite] at hx; done)
    | (simp [IsFinite, isFinite] at hy; done)
    | (simp only [UnpackedFloat.mul]
       first
       | exact isFinite_roundWithAccuracy _ _ _ _ _
       | assumption)

theorem mul_isCanonical [Fact (2 ≤ spec.exponentBits)] (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) : IsCanonical spec (UnpackedFloat.mul spec x y) :=
  (mul_spec x y hx hy).1

/-- A finite result has finite operands. -/
theorem isFinite_of_isFinite_mul [Fact (2 ≤ spec.exponentBits)] (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) (h : (UnpackedFloat.mul spec x y).IsFinite) :
    x.IsFinite ∧ y.IsFinite :=
  let h := (mul_spec x y hx hy).2 h
  ⟨h.1, h.2.1⟩

theorem abs_toReal_mul_sub_le [Fact (2 ≤ spec.exponentBits)] (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) (h : (UnpackedFloat.mul spec x y).IsFinite) :
    |toReal (UnpackedFloat.mul spec x y) - toReal x * toReal y|
      ≤ spec.unitRoundoff * |toReal x * toReal y|
        + spec.underflowBound :=
  ((mul_spec x y hx hy).2 h).2.2.1

/-- A finite result of `mul` is a nearest float of the exact product. -/
theorem isNearestFloat_toReal_mul [Fact (2 ≤ spec.exponentBits)] (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) (h : (UnpackedFloat.mul spec x y).IsFinite) :
    IsNearestFloat spec.mantissaBits spec.minExponent (toReal x * toReal y)
      (toReal (UnpackedFloat.mul spec x y)) :=
  ((mul_spec x y hx hy).2 h).2.2.2



theorem exists_approximates_divCore (m₁ : ℕ) (e₁ : ℤ) (m₂ : ℕ) (e₂ : ℤ) (hm₁ : 0 < m₁) (hm₂ : 0 <
  m₂) :
    ∃ w : ℝ, ExtendedMantissa.Approximates (ExtendedMantissa.ofMantissaAndAccuracy (divCore spec
      m₁ e₁ m₂ e₂).1
        (divCore spec m₁ e₁ m₂ e₂).2.2) w ∧
      w * 2 ^ (divCore spec m₁ e₁ m₂ e₂).2.1 = (m₁ * 2 ^ e₁) / (m₂ * 2 ^ e₂) ∧
      (divCore spec m₁ e₁ m₂ e₂).2.1 ≤ spec.targetExponent
        (totalExponent (divCore spec m₁ e₁ m₂ e₂).1 (divCore spec m₁ e₁ m₂ e₂).2.1) := by
  unfold divCore
  simp only
  generalize htg : min (e₁ - e₂) (spec.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂))
    = tgt
  have htg1 : tgt ≤ e₁ - e₂ := htg ▸ min_le_left _ _
  have htg2 : tgt ≤ spec.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂) :=
    htg ▸ min_le_right _ _
  generalize hk : (e₁ - e₂ - tgt).toNat = k
  have hk' : (k : ℤ) = e₁ - e₂ - tgt := by rw [← hk]; exact Int.toNat_of_nonneg (by omega)
  have hd : (0 : ℝ) < m₂ := by exact_mod_cast hm₂
  refine ⟨(m₁ <<< k / m₂ : ℕ) + ((m₁ <<< k % m₂ : ℕ) : ℝ) / m₂,
    ExtendedMantissa.approximates_ofFraction _ _ _ (Nat.mod_lt _ hm₂), ?_, ?_⟩
  · have : ((m₁ <<< k / m₂ : ℕ) : ℝ) + ((m₁ <<< k % m₂ : ℕ) : ℝ) / m₂ = (m₁ * 2 ^ k : ℕ) / m₂ := by
      rw [← Nat.shiftLeft_eq]
      field_simp
      exact_mod_cast (Nat.div_add_mod' (m₁ <<< k) m₂)
    rw [this]
    push_cast
    rw [← zpow_natCast, hk']
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    field_simp
    simp only [← zpow_add₀ h2]
    congr 1; ring
  · -- enough quotient bits
    have hp := Format.two_le_mantissaBits spec
    by_cases hlow : tgt ≤ spec.minExponent
    · exact le_trans hlow (le_max_right _ _)
    replace hlow := not_le.mp hlow
    have hD : tgt ≤ totalExponent m₁ e₁ - totalExponent m₂ e₂ - spec.mantissaBits := by
      rw [Format.targetExponent_eq] at htg2
      rcases max_choice (totalExponent m₁ e₁ - totalExponent m₂ e₂ - spec.mantissaBits)
        spec.minExponent with h | h
      · rwa [h] at htg2
      · rw [h] at htg2; omega
    rw [totalExponent_eq, totalExponent_eq] at hD
    have hl1 := (Nat.log2_eq_iff hm₁.ne').mp rfl
    have hl2 := (Nat.log2_eq_iff hm₂.ne').mp rfl
    -- m₁ 2^k ≥ 2^(p-1) m₂
    have hkb : m₂.log2 + spec.mantissaBits ≤ m₁.log2 + 1 + k := by omega
    have hq : 2 ^ (spec.mantissaBits - 1) ≤ m₁ <<< k / m₂ := by
      rw [Nat.le_div_iff_mul_le hm₂, Nat.shiftLeft_eq]
      calc 2 ^ (spec.mantissaBits - 1) * m₂ ≤ 2 ^ (spec.mantissaBits - 1) * 2 ^ (m₂.log2 + 1) :=
            Nat.mul_le_mul_left _ hl2.2.le
        _ = 2 ^ (spec.mantissaBits + m₂.log2) := by rw [← pow_add]; congr 1; omega
        _ ≤ 2 ^ (m₁.log2 + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ m₁.log2 * 2 ^ k := pow_add _ _ _
        _ ≤ m₁ * 2 ^ k := Nat.mul_le_mul_right _ hl1.1
    have hqpos : 0 < m₁ <<< k / m₂ := lt_of_lt_of_le (by positivity) hq
    have : spec.mantissaBits - 1 ≤ (m₁ <<< k / m₂).log2 := (Nat.le_log2 hqpos.ne').mpr hq
    rw [Format.targetExponent_eq, totalExponent_eq]
    apply le_max_of_le_left
    omega

/-- Dividing two finite values (no canonicity needed). -/
private theorem div_finite_spec (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) (s₁ s₂ : Sign) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) :
    let r := UnpackedFloat.div spec (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂)
    IsCanonical spec r ∧
    |toReal r - toReal (.finite s₁ m₁ e₁ hm₁) / toReal (.finite s₂ m₂ e₂ hm₂)|
      ≤ spec.unitRoundoff *
          |toReal (.finite s₁ m₁ e₁ hm₁) / toReal (.finite s₂ m₂ e₂ hm₂)|
        + spec.underflowBound := by
  intro r
  simp only [r, UnpackedFloat.div]
  obtain ⟨w, hw, hwv, he⟩ := exists_approximates_divCore (spec := spec) m₁ e₁ m₂ e₂ hm₁ hm₂
  have hs := And.intro (roundWithAccuracy_isCanonical spec (s₁ / s₂) _ _ _ w hw he)
    (abs_toReal_roundWithAccuracy_sub_le spec (s₁ / s₂) _ _ _ w hw he)
  have hwm := hw.le
  rw [ofMantissaAndAccuracy_mantissa] at hwm
  have hh := div_pow_targetExponent_le_of_le_targetExponent spec _ _ w hwm he
  rw [hwv] at hs hh
  have hv : toReal (.finite s₁ m₁ e₁ hm₁) / toReal (.finite s₂ m₂ e₂ hm₂)
      = (s₁ / s₂).toReal * ((m₁ * 2 ^ e₁) / (m₂ * 2 ^ e₂)) := by
    simp only [toReal, Sign.toReal_div]
    have : s₂.toReal * s₂.toReal = 1 := by cases s₂ <;> simp [Sign.toReal]
    field_simp
    cases s₂ <;> cases s₁ <;> simp [Sign.toReal]
  have habs : |toReal (.finite s₁ m₁ e₁ hm₁) / toReal (.finite s₂ m₂ e₂ hm₂)|
      = (m₁ * 2 ^ e₁) / (m₂ * 2 ^ e₂) := by
    rw [hv, abs_mul, Sign.abs_toReal, one_mul, abs_of_nonneg (by positivity)]
  refine ⟨hs.1, ?_⟩
  rw [habs, hv]
  exact hs.2.trans hh
theorem div_finite_isCanonical (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) (s₁ s₂ : Sign) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) :
    IsCanonical spec (UnpackedFloat.div spec (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂)) :=
  (div_finite_spec m₁ m₂ e₁ e₂ s₁ s₂ hm₁ hm₂).1

/-- Dividing two finite values (no canonicity needed). -/
theorem abs_toReal_div_finite_sub_le (m₁ m₂ : ℕ) (e₁ e₂ : ℤ) (s₁ s₂ : Sign) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) :
    |toReal (UnpackedFloat.div spec (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂))
        - toReal (.finite s₁ m₁ e₁ hm₁) / toReal (.finite s₂ m₂ e₂ hm₂)|
      ≤ spec.unitRoundoff *
          |toReal (.finite s₁ m₁ e₁ hm₁) / toReal (.finite s₂ m₂ e₂ hm₂)|
        + spec.underflowBound :=
  (div_finite_spec m₁ m₂ e₁ e₂ s₁ s₂ hm₁ hm₂).2
private theorem div_spec (x y : UnpackedFloat)
    (hx : IsCanonical spec x) (hy : IsCanonical spec y) :
    IsCanonical spec (UnpackedFloat.div spec x y) ∧
    (x.IsFinite → y.IsFinite → (UnpackedFloat.div spec x y).IsFinite →
      |toReal (UnpackedFloat.div spec x y) - toReal x / toReal y|
        ≤ spec.unitRoundoff * |toReal x / toReal y|
          + spec.underflowBound) := by
  cases x <;> cases y <;> simp only [UnpackedFloat.div]
  case finite.finite s₁ m₁ e₁ hm₁ s₂ m₂ e₂ hm₂ =>
    exact ⟨div_finite_isCanonical m₁ m₂ e₁ e₂ s₁ s₂ hm₁ hm₂,
      fun _ _ _ => abs_toReal_div_finite_sub_le m₁ m₂ e₁ e₂ s₁ s₂ hm₁ hm₂⟩
  all_goals
    simp only [IsCanonical, IsFinite, isFinite, Bool.false_eq_true, toReal, div_zero, sub_self,
    abs_zero, mul_zero, zero_add, IsEmpty.forall_iff, implies_true, and_self,
    zero_div, forall_const, true_and]
  all_goals positivity
theorem div_isCanonical (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) : IsCanonical spec (UnpackedFloat.div spec x y) :=
  (div_spec x y hx hy).1
theorem abs_toReal_div_sub_le (x y : UnpackedFloat)
    (hx : IsCanonical spec x)
    (hy : IsCanonical spec y) (hxf : x.IsFinite) (hyf : y.IsFinite)
    (h : (UnpackedFloat.div spec x y).IsFinite) :
    |toReal (UnpackedFloat.div spec x y) - toReal x / toReal y|
      ≤ spec.unitRoundoff * |toReal x / toReal y|
        + spec.underflowBound :=
  (div_spec x y hx hy).2 hxf hyf h

/-! ## Packing results -/

theorem unpack_pack_of_isFinite [Fact (2 ≤ spec.exponentBits)] {r : UnpackedFloat}
    (hr : IsCanonical spec r)
    (h : (UnpackedFloat.unpack spec (UnpackedFloat.pack spec r)).IsFinite) :
    UnpackedFloat.unpack spec (UnpackedFloat.pack spec r) = r := by
  cases r with
  | notANumber => rw [unpack_pack_nan] at h; simp [IsFinite, isFinite] at h
  | infinity s => rw [unpack_pack_infinity] at h; simp [IsFinite, isFinite] at h
  | zero s => exact unpack_pack_zero s
  | finite s m e hm =>
    rcases unpack_pack_finite hr with h' | h'
    · exact h'
    · rw [h'] at h; simp [IsFinite, isFinite] at h

end Float.Model.UnpackedFloat
