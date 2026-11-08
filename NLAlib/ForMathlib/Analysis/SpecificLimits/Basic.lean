/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Eventual bounds by powers of two

A bound $C\,2^{-t} \le D$ with $D > 0$ holds for every large $t$, and every large $t$ is positive
with $B < 2^t$: the precision hypotheses of a rounded witness at $t$ bits. Upstream candidate for
`Mathlib.Analysis.SpecificLimits.Basic`.

## Main results

* `eventually_mul_two_inv_pow_le`, `eventually_pos_and_lt_two_pow`.
-/

@[expose] public section

open Filter

/-- A precision hypothesis $C\,2^{-t} \le D$ with $D > 0$ holds for every large $t$.
No printed source. -/
theorem eventually_mul_two_inv_pow_le (C : ℝ) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ t : ℕ in atTop, C * 2⁻¹ ^ t ≤ D := by
  have h : Tendsto (fun t : ℕ => C * (2⁻¹ : ℝ) ^ t) atTop (nhds (C * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul C
  rw [mul_zero] at h
  exact (h.eventually (gt_mem_nhds hD)).mono fun _ h => h.le

/-- Every large $t$ is positive with $B < 2^t$. No printed source. -/
theorem eventually_pos_and_lt_two_pow (B : ℕ) : ∀ᶠ t : ℕ in atTop, 0 < t ∧ B < 2 ^ t :=
  (eventually_ge_atTop (B + 1)).mono fun t ht =>
    ⟨by omega, Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right two_pos (by omega))⟩
