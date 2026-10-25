/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Moments.Variance

/-!
# The Paley–Zygmund inequality

A nonnegative random variable with a finite second moment exceeds a fraction $\theta$ of its mean
with probability at least $(1 - \theta)^2 (\mathbb{E} Z)^2 / \mathbb{E} Z^2$. It is the
anti-concentration step of the early-truncation lower bound
(`docs/design/LowRank-EstimatorLowerBounds.md`, §3.1). Not in Mathlib (searched: `paley`,
`zygmund`, `second moment method`); an upstream candidate for
`Mathlib/Probability/Moments/Variance.lean` or a new `Mathlib/Probability/PaleyZygmund.lean`.
Its proof is deferred.

## Main results

* `ProbabilityTheory.sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt`: the inequality.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The Paley–Zygmund inequality.** Under a probability measure, for a random variable
$Z \ge 0$ almost surely with $\mathbb{E} Z^2 < \infty$ and $0 \le \theta \le 1$,
$$(1 - \theta)^2 (\mathbb{E} Z)^2 \le \mathbb{E} Z^2 \cdot
\mathbb{P}\bigl[Z > \theta\,\mathbb{E} Z\bigr]\,.$$
Both hypotheses on $\theta$ are needed: for $\theta < 0$ and a constant $Z > 0$ the left side
exceeds $\mathbb{E}Z^2$, and for $\theta > 1$ the event is empty for a constant $Z$.
[PaleyZygmund1932, Lemma 19] (locator to check); the product form avoids dividing by
$\mathbb{E} Z^2$.
Proof: S, about 25 lines. Split
$\mathbb{E} Z = \mathbb{E}[Z \mathbf{1}_{Z \le \theta \mathbb{E}Z}] +
\mathbb{E}[Z \mathbf{1}_{Z > \theta \mathbb{E}Z}] \le \theta\,\mathbb{E} Z +
\sqrt{\mathbb{E} Z^2 \cdot \mathbb{P}[Z > \theta \mathbb{E} Z]}$ (`integral_add_compl` on the
measurable set `{ω | θ * ∫ Z < Z ω}`, which is `measurableSet_lt` after
`MemLp.aestronglyMeasurable`
and `AEMeasurable.nullMeasurableSet`, or work with `toMeasurable`; the first piece by
`setIntegral_mono_on`, the second by Cauchy–Schwarz `integral_mul_le_Lp_mul_Lq_of_nonneg` with
$p = q = 2$ on $Z \cdot \mathbf{1}$, `indicator` squared is itself). So
$0 \le (1-\theta)\mathbb{E}Z \le \sqrt{\cdots}$ (`integral_nonneg_of_ae`), square both sides
(`Real.sq_sqrt`, `pow_le_pow_left₀`).
Result: paley-zygmund-inequality -/
theorem sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ0 : 0 ≤ᵐ[μ] Z) (hZ : MemLp Z 2 μ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 ≤
      (∫ ω, Z ω ^ 2 ∂μ) * μ.real {ω | θ * ∫ ω', Z ω' ∂μ < Z ω} := by
  sorry

end ProbabilityTheory
