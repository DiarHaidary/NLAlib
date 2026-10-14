/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A third-order upper bound on `log (1 + u)` for `-1 < u ≤ 0`

`log (1 + u) ≤ u - u²/2 + u³/3` for `-1 < u ≤ 0`: every term of the series of `log (1 + u)` is
nonpositive there, and the bound keeps the first three. It is the second-order log term the lower
Johnson–Lindenstrauss tail of a sum of squares needs
(`NLAlib/Probability/SubGaussian/SquareSum.lean`, `docs/design/Sketching-S3.md` §8, item 2),
where `1 + v ≤ exp v` is too weak. The same bound for
`u ≥ 0` is the private `log_one_add_le_cubic` of
`NLAlib/Probability/Distributions/ChiSquareTails.lean`; at the wrap-up the two become one public
statement for `-1 < u`. Upstream candidate for `Mathlib.Analysis.SpecialFunctions.Log.Deriv`.

## Main results

* `Real.log_one_add_le_cubic_of_nonpos`.
-/

@[expose] public section

namespace Real

/-- `log (1 + u) ≤ u - u²/2 + u³/3` for `-1 < u ≤ 0`. The difference
`u - u²/2 + u³/3 - log (1 + u)` has derivative `u³/(1 + u) ≤ 0` on `(-1, 0]` and vanishes at
`0`. -/
theorem log_one_add_le_cubic_of_nonpos {u : ℝ} (h1 : -1 < u) (h0 : u ≤ 0) :
    log (1 + u) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 := by
  sorry

end Real
