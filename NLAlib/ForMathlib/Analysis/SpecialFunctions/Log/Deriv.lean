/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A third-order upper bound on $\log(1 + u)$ for $-1 < u \le 0$

$\log(1 + u) \le u - u^2/2 + u^3/3$ for $-1 < u \le 0$: every term of the series of $\log(1 + u)$
is nonpositive there, and the bound keeps the first three. It is the second-order log term the
lower Johnson–Lindenstrauss tail of a sum of squares needs
(`NLAlib/Probability/SubGaussian/SquareSum.lean`, `docs/design/Sketching-S3.md` §8, item 2),
where $1 + v \le e^v$ is too weak. The same bound for $u \ge 0$ is the private
`log_one_add_le_cubic` of `NLAlib/Probability/Distributions/ChiSquareTails.lean`; at the wrap-up
the two become one public statement for $-1 < u$. Upstream candidate for
`Mathlib.Analysis.SpecialFunctions.Log.Deriv`.

## Main results

* `Real.log_one_add_le_cubic_of_nonpos`.
-/

@[expose] public section

namespace Real

/-- For $-1 < u \le 0$,
$$\log(1 + u) \le u - \frac{u^2}{2} + \frac{u^3}{3} \,.$$
Proof: with $x = -u \in [0, 1)$ the series $-\log(1 - x) = \sum_{k \ge 1} x^k / k$
(`Real.hasSum_pow_div_log_of_abs_lt_one`) has nonnegative terms, so it is at least the sum of its
first three terms, $x + x^2/2 + x^3/3$. Substituting $x = -u$ gives the claim. -/
theorem log_one_add_le_cubic_of_nonpos {u : ℝ} (h1 : -1 < u) (h0 : u ≤ 0) :
    log (1 + u) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 := by
  have hu : 0 ≤ -u := by linarith
  have h := hasSum_pow_div_log_of_abs_lt_one (x := -u) (by rw [abs_of_nonneg hu]; linarith)
  have := sum_le_hasSum (Finset.range 3) (fun n _ => by positivity) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add] at this
  norm_num at this
  have e : (-u) ^ 3 = -u ^ 3 := by ring
  linarith

end Real
