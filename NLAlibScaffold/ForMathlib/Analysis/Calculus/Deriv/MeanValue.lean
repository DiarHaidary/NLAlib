/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# An integrating-factor comparison

Statements for `NLAlib/ForMathlib/Analysis/Calculus/Deriv/MeanValue.lean` whose proofs are
deferred (`docs/design/Probability-Beta.md`, §3.3, β4e). If $t f'(t) + b f(t) \le 0$ on
$(0, \infty)$ with $b > 0$, the integrating factor $t^b$ makes $t^b f(t)$ antitone on
$[0, \infty)$. Grönwall's inequality (`norm_le_gronwallBound_of_norm_deriv_right_le`) does not
cover this case, because the coefficient $b/t$ is singular at $0$. Upstream candidate for
`Mathlib.Analysis.Calculus.Deriv.MeanValue`.

## Main results

* `antitoneOn_rpow_mul_of_hasDerivAt`: the integrating-factor comparison.
-/

@[expose] public section

open Set

/-- **Integrating factor**: if $f$ is differentiable on $(0, \infty)$ with derivative $f'$,
continuous from the right at $0$, $b > 0$, and $t f'(t) + b f(t) \le 0$ for every $t > 0$, then
$t \mapsto t^b f(t)$ is antitone on $[0, \infty)$.
Proof: S, about 20 lines. `antitoneOn_of_deriv_nonpos` on `Ici 0` (`convex_Ici`,
`interior_Ici`); continuity on `Ici 0`: at $0$ from `hc`, `Real.continuousAt_rpow_const` and
`Real.zero_rpow hb.ne'` (`ContinuousWithinAt.mul`), elsewhere from `hf`; the derivative
$t^{b-1}(t f'(t) + b f(t))$ by `Real.hasDerivAt_rpow_const`, `HasDerivAt.mul` and
`Real.rpow_sub_one`, nonpositive by `h` and `Real.rpow_nonneg`. -/
theorem antitoneOn_rpow_mul_of_hasDerivAt {f f' : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hc : ContinuousWithinAt f (Ici 0) 0) (hf : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (h : ∀ t ∈ Ioi (0 : ℝ), t * f' t + b * f t ≤ 0) :
    AntitoneOn (fun t => t ^ b * f t) (Ici 0) := by
  sorry
