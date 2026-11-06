/-
Copyright (c) 2026 NumLean contributors and NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NumLean contributors, NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Init.Data.Float.Model.Unpacked.Round

/-!
# Correct rounding of extended mantissas

Upstream candidates for the mathematical API of Lean core's floating-point model.
Adapted from the supplied NumLean archive, `NumLean/Data/Scalars/IEEE/Mantissa.lean`. The archive's
SHA-256 and licensing status, the earlier Mathlib search and the changes needed for Lean 4.33
are recorded in `docs/design/Finite-Precision-Arithmetic.md`. No NumLean dependency is imported.
General format lemmas state a two-exponent-bit assumption explicitly where needed; core 4.33
also permits one-bit layouts. These results concern logical arithmetic, not native execution cost.

## Main results

* `Float.Model.UnpackedFloat.ExtendedMantissa.Approximates.shiftRight`.
* `Float.Model.UnpackedFloat.ExtendedMantissa.Approximates.abs_roundedMantissa_sub_le`.
-/

@[expose] public section

namespace Float.Model.UnpackedFloat.ExtendedMantissa

/-- An extended mantissa describes $w$ in $[m,m+1)$: the round bit records
$w\ge m+1/2$, and the sticky bit excludes both $m$ and $m+1/2$. -/
structure Approximates (em : ExtendedMantissa) (w : ℝ) : Prop where
  /-- The represented value is at least the integral mantissa. -/
  le : (em.mantissa : ℝ) ≤ w
  /-- The represented value is less than the next integral mantissa. -/
  lt : w < em.mantissa + 1
  /-- The round bit identifies the upper half of the unit interval. -/
  round : em.roundBit = true ↔ (em.mantissa : ℝ) + 1 / 2 ≤ w
  /-- The sticky bit excludes exact integers and midpoints. -/
  sticky : em.stickyBit = true ↔ (w ≠ em.mantissa ∧ w ≠ em.mantissa + 1 / 2)

/-- An integral mantissa with clear round and sticky bits describes its exact natural value. -/
theorem approximates_exact (m : ℕ) : Approximates ⟨m, false, false⟩ (m : ℝ) where
  le := le_rfl
  lt := by linarith
  round := by simp
  sticky := by simp

/-- Shifting an extended mantissa right once preserves its description after division by two. -/
theorem Approximates.shiftRightOne {em : ExtendedMantissa} {w : ℝ} (h : Approximates em w) :
    Approximates em.shiftRightOne (w / 2) := by
  obtain ⟨m, rb, sb⟩ := em
  obtain ⟨hle, hlt, hr, hs⟩ := h
  simp only [ExtendedMantissa.shiftRightOne] at *
  have hm : (m : ℝ) = 2 * (m / 2 : ℕ) + (m % 2 : ℕ) := by
    exact_mod_cast (Nat.div_add_mod m 2).symm
  set q := m / 2
  rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
  · rw [h0] at hm
    push_cast at hm
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · simp only [h0, bne_self_eq_false, Bool.false_eq_true, false_iff, not_le]; linarith
    · rw [Bool.or_eq_true, hr, hs]
      constructor
      · rintro (h | ⟨h, -⟩)
        · constructor <;> intro <;> linarith
        · constructor
          · intro h'; exact h (by linarith)
          · intro h'; linarith
      · rintro ⟨h, -⟩
        by_cases h2 : (m : ℝ) + 1 / 2 ≤ w
        · exact Or.inl h2
        · right; constructor
          · intro h'; exact h (by linarith)
          · intro h'; linarith
  · rw [h1] at hm
    push_cast at hm
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · simp only [h1]; simp; linarith
    · rw [Bool.or_eq_true, hr, hs]
      constructor
      · rintro (h | ⟨h, -⟩)
        · constructor <;> intro <;> linarith
        · constructor
          · intro; linarith
          · intro h'; exact h (by linarith)
      · rintro ⟨-, h⟩
        by_cases h2 : (m : ℝ) + 1 / 2 ≤ w
        · exact Or.inl h2
        · right; constructor
          · intro h'; exact h (by linarith)
          · intro h'; linarith

/-- Shifting an extended mantissa right by $n$ places preserves its description divided by $2^n$. -/
theorem Approximates.shiftRight {em : ExtendedMantissa} {w : ℝ} (h : Approximates em w) (n : ℕ) :
    Approximates (em >>> n) (w / 2 ^ n) := by
  induction n with
  | zero => rw [pow_zero, div_one]; exact h
  | succ n ih =>
    have := ih.shiftRightOne
    rw [show w / 2 ^ (n + 1) = w / 2 ^ n / 2 by rw [pow_succ, div_div]]
    exact this

/-- An extended mantissa describing a natural number has that exact integral mantissa. -/
theorem Approximates.mantissa_eq_of_natCast {em : ExtendedMantissa} {k : ℕ}
    (h : Approximates em k) :
    em.mantissa = k := by
  have h1 := h.le
  have h2 := h.lt
  have : em.mantissa ≤ k := by exact_mod_cast h1
  have : k < em.mantissa + 1 := by exact_mod_cast h2
  omega

/-- Round to nearest is within half a unit. -/
theorem Approximates.abs_roundedMantissa_sub_le {em : ExtendedMantissa} {w : ℝ}
    (h : Approximates em w) :
    |(em.roundedMantissa : ℝ) - w| ≤ 1 / 2 := by
  obtain ⟨m, rb, sb⟩ := em
  obtain ⟨hle, hlt, hr, hs⟩ := h
  simp only at *
  rw [abs_le]
  cases rb <;> cases sb <;>
    simp only [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
      Accuracy.roundToNearestEven, Bool.false_eq_true, false_iff, true_iff, not_le, not_and_or,
      not_ne_iff] at hr hs ⊢
  · -- exact
    rcases hs with hs | hs
    · subst hs; constructor <;> linarith
    · linarith
  · -- below the midpoint
    constructor <;> linarith
  · -- at the midpoint
    rcases hs with hs | hs
    · linarith
    · subst hs
      rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
      · rw [h0]; push_cast; constructor <;> linarith
      · rw [h1]; push_cast; constructor <;> linarith
  · -- above the midpoint
    push_cast; constructor <;> linarith

/-- Rounding an exact extended mantissa returns its integral mantissa unchanged. -/
theorem roundedMantissa_mk_false_false {m : ℕ} :
    (ExtendedMantissa.mk m false false).roundedMantissa = m := rfl

/-- The quotient accuracy describes $q+n/d$ whenever $n<d$, for natural $q,n,d$. -/
theorem approximates_ofFraction (q num den : ℕ) (hlt : num < den) :
    Approximates (ExtendedMantissa.ofMantissaAndAccuracy q (accuracyOfFraction num den))
      (q + num / den) := by
  have hd : (0 : ℝ) < den := by exact_mod_cast (Nat.zero_lt_of_lt hlt)
  have hfr : (num : ℝ) / den < 1 := by
    rw [div_lt_one hd]; exact_mod_cast hlt
  have hfr0 : 0 ≤ (num : ℝ) / den := by positivity
  unfold accuracyOfFraction
  split_ifs with h0
  · subst h0; simpa [ExtendedMantissa.ofMantissaAndAccuracy] using approximates_exact q
  · have hpos : 0 < (num : ℝ) / den := by
      have : (0 : ℝ) < num := by exact_mod_cast Nat.pos_of_ne_zero h0
      positivity
    have e : ((2 * num : ℕ) : ℝ) = 2 * ((num : ℝ) / den) * den := by
      push_cast; field_simp
    rcases lt_trichotomy (2 * num) den with hc | hc | hc
    · rw [Nat.compare_eq_lt.mpr hc]
      have hc' : ((2 * num : ℕ) : ℝ) < den := by exact_mod_cast hc
      rw [e] at hc'
      have : (num : ℝ) / den < 1 / 2 := by nlinarith
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp only [ExtendedMantissa.ofMantissaAndAccuracy, Bool.false_eq_true, false_iff,
          true_iff, not_le, ne_eq] <;> first | linarith | (constructor <;> intro <;> linarith)
    · rw [Nat.compare_eq_eq.mpr hc]
      have hc' : ((2 * num : ℕ) : ℝ) = den := by exact_mod_cast hc
      rw [e] at hc'
      have : (num : ℝ) / den = 1 / 2 := by
        have := mul_right_cancel₀ hd.ne' (hc'.trans (one_mul _).symm)
        linarith
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp only [ExtendedMantissa.ofMantissaAndAccuracy, Bool.false_eq_true, false_iff,
          true_iff, ne_eq, not_and, not_not] <;> first | linarith | (intro; linarith)
    · rw [Nat.compare_eq_gt.mpr hc]
      have hc' : (den : ℝ) < ((2 * num : ℕ) : ℝ) := by exact_mod_cast hc
      rw [e] at hc'
      have : 1 / 2 < (num : ℝ) / den := by nlinarith
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp only [ExtendedMantissa.ofMantissaAndAccuracy,
          true_iff, ne_eq] <;> first | linarith | (constructor <;> intro <;> linarith)

end Float.Model.UnpackedFloat.ExtendedMantissa
