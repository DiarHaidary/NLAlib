/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A threshold for a union bound of exponential tails

$(r+2)e^{-m/(2G)} < 1/2$ once $4G(r+2) \le m$: the exceptional probability of $r+2$ Gaussian
events stays below one half for a long enough tail. Upstream candidate for
`Mathlib.Analysis.SpecialFunctions.Exp`.

## Main results

* `Real.mul_exp_neg_div_lt_half`.
-/

@[expose] public section

namespace Real

/-- For $G > 0$ and natural $r, m$ with $4G(r+2) \le m$,
$$(r+2)\,e^{-m/(2G)} < \tfrac12 \,.$$ -/
theorem mul_exp_neg_div_lt_half {r m : ℕ} {G : ℝ} (hG : 0 < G) (hm : 4 * G * (r + 2) ≤ m) :
    ((r : ℝ) + 2) * exp (-(m / (2 * G))) < 1 / 2 := by
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hy : 2 * ((r : ℝ) + 2) ≤ m / (2 * G) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hexp : 2 * ((r : ℝ) + 2) < exp (m / (2 * G)) := by
    have h := add_one_le_exp (m / (2 * G))
    linarith
  have hinv : exp (-(m / (2 * G))) * exp (m / (2 * G)) = 1 := by
    rw [← exp_add]; simp
  nlinarith [mul_pos (exp_pos (-(m / (2 * G)))) (sub_pos.mpr hexp)]

end Real
