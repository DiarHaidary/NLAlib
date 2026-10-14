/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Deriv
public import NLAlib.Probability.SubGaussian.Square

/-!
# Sums of squares of sub-Gaussian variables with Gaussian moments

For independent real `Y₁, …, Y_k`, each sub-Gaussian with proxy `1`, with `E Yᵢ² = 1` and
`E Yᵢ⁴ ≤ 3` (the moments of a standard Gaussian), the relative deviation of `k⁻¹ ∑ Yᵢ²` from `1`
has the tail `2 exp (-k (ε²/4 - ε³/6))` of `χ²_k`, Dasgupta and Gupta's exponent. The upper half
is Chernoff's bound with `E exp (θ Y²) ≤ (1 - 2θ)^{-1/2}`
(`HasSubgaussianMGF.integral_exp_mul_sq_le`) and the arithmetic of the `χ²` tail; the lower half
is Chernoff's bound with `E exp (-θ Y²) ≤ 1 - θ + 3θ²/2` at `θ = ε/(2(1 + ε))`, through
`Real.log_one_add_le_cubic_of_nonpos`. A standard Gaussian and a Rademacher combination
`⟨ξ, x⟩` with `‖x‖ = 1` (`E ⟨ξ, x⟩⁴ = 3 - 2 ∑ xⱼ⁴`) satisfy the hypotheses; the latter gives the
sign-sketch Johnson–Lindenstrauss tail with Gaussian constants (Achlioptas).

This file is a skeleton of Sketching stage S3 (`docs/design/Sketching-S3.md` §8, item 2). At the
wrap-up it merges into `NLAlib/Probability/SubGaussian/Square.lean`, and the `χ²` relative
deviation `NLAlib.measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector`, which
it dominates (same bound, weaker hypotheses), can be reproved from it and keep its name
(CONTRIBUTING §5.2, rule 6).

## Main results

* `NLAlib.measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ι : Type*} [Fintype ι]
  {Y : ι → Ω → ℝ} {ε : ℝ}

/-- **Dasgupta–Gupta tail for sums of squares**: for independent real `Yᵢ`, each sub-Gaussian
with proxy `1`, with `E Yᵢ² = 1` and `E Yᵢ⁴ ≤ 3`, and `0 ≤ ε`,
`P(ε ≤ |k⁻¹ ∑ Yᵢ² - 1|) ≤ 2 exp (-k (ε²/4 - ε³/6))`, `k = card ι`. The exponent of Dasgupta and
Gupta (2003) for `χ²_k`, cited by name only (`docs/PORT_SKETCHING.md` §7.2); here for any
variables with the Gaussian's proxy and its second and fourth moments. The lower half covers
`ε = 1`, where `∑ Yᵢ² = 0` may have positive probability (`2^{-k}` for Rademacher combinations).
The bound is at least `2` for `ε ≥ 3/2` and for empty `ι`. -/
theorem measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun (hind : iIndepFun Y μ)
    (hsub : ∀ i, HasSubgaussianMGF (Y i) 1 μ) (h2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = 1)
    (h4 : ∀ i, ∫ ω, Y i ω ^ 4 ∂μ ≤ 3) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |(∑ i, Y i ω ^ 2) / Fintype.card ι - 1|} ≤
      2 * Real.exp (-(Fintype.card ι * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
  sorry

end NLAlib
