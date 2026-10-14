/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.ChiSquare

/-!
# Chernoff tails of `χ²_n`

For a standard Gaussian vector `X` in `ℝⁿ`, Chernoff's bound with the exact Laplace transform of
`‖X‖² ~ χ²_n` at `θ = (1 - 1/β)/2` gives `P(‖X‖² ≥ β n)` and `P(‖X‖² ≤ β n)` at most
`exp ((n/2)(1 - β + log β))`, on either side of `β = 1`; the relative deviation
`P(ε ≤ |‖X‖²/n - 1|) ≤ 2 exp (-n (ε²/4 - ε³/6))` follows, with the polynomial exponent of
Dasgupta and Gupta (2003). The weighted Laplace transform `E exp (∑ θᵢ Xᵢ²)` is the input of the
projection tails of a uniform unit vector (`NLAlib/RandomMatrix/Haar/Sphere.lean`).

The lower tail dominates both lower bounds of `NLAlib/Probability/Distributions/ChiSquare.lean`
(Laurent–Massart and the small ball; CONTRIBUTING §5.2 rule 6). This file is a skeleton of
Sketching stage S2 (`docs/design/Sketching-S2.md` §3.1, §8): at the wrap-up it merges into
`ChiSquare.lean`, where both older bounds are reproved from the new tail and keep their names.

## Main results

* `NLAlib.integral_exp_sum_mul_sq_of_hasLaw_gaussianVector`:
  `E exp (∑ θᵢ Xᵢ²) = ∏ (1 - 2θᵢ)^{-1/2}`.
* `NLAlib.measureReal_mul_card_le_norm_sq_le_of_hasLaw_gaussianVector`: the upper tail, `β ≥ 1`.
* `NLAlib.measureReal_norm_sq_le_mul_card_le_of_hasLaw_gaussianVector`: the lower tail,
  `0 < β ≤ 1`.
* `NLAlib.measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector`: the relative
  deviation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {X : Ω → n → ℝ} {ε β : ℝ}

/-- **The weighted Laplace transform of a Gaussian vector**: `E exp (∑ θᵢ Xᵢ²) = ∏ (1 - 2θᵢ)^{-1/2}`
for weights with `θᵢ < 1/2`, by independence of the coordinates. The equal-weight case is
`NLAlib.integral_exp_mul_norm_sq_of_hasLaw_gaussianVector`; two weights give the projection tails
of a uniform unit vector. -/
theorem integral_exp_sum_mul_sq_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    {θ : n → ℝ} (hθ : ∀ i, 2 * θ i < 1) :
    ∫ ω, Real.exp (∑ i, θ i * X ω i ^ 2) ∂μ = ∏ i, (1 - 2 * θ i) ^ (-(1 / 2 : ℝ)) := by
  sorry

/-- **Upper Chernoff tail of `χ²_n`**: `P(β n ≤ ‖X‖²) ≤ exp ((n/2)(1 - β + log β))` for
`β ≥ 1`, Chernoff's bound with the exact Laplace transform at `θ = (1 - 1/β)/2`. At every
threshold it is at least as good as Laurent and Massart's upper tail, which stays in the library
as the sub-Gaussian-vector bound `NLAlib.IsSubgaussianVector.measure_norm_sq_ge_le` at proxy `1`
(rule 6: that theorem is about every sub-Gaussian vector and keeps its form). The exponent of
Dasgupta and Gupta (2003), there for the projection of a uniform unit vector.
Result: chi-square-upper-tail -/
theorem measureReal_mul_card_le_norm_sq_le_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ) (hβ : 1 ≤ β) :
    μ.real {ω | β * Fintype.card n ≤ ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤
      Real.exp (Fintype.card n / 2 * (1 - β + Real.log β)) := by
  sorry

/-- **Lower Chernoff tail of `χ²_n`**: `P(‖X‖² ≤ β n) ≤ exp ((n/2)(1 - β + log β))` for
`0 < β ≤ 1`, Chernoff's bound with the exact Laplace transform at `θ = (1 - 1/β)/2`. It dominates
(CONTRIBUTING §5.2 rule 6) both lower bounds of `ChiSquare.lean`: Laurent and Massart's
`NLAlib.measureReal_norm_sq_le_of_hasLaw_gaussianVector` (at `β = 1 - 2√(t/n)`, with
`log (1 - u) ≤ -u - u²/2`) and the small ball
`NLAlib.measureReal_norm_sq_le_le_rpow_of_hasLaw_gaussianVector` (at `β = u/n`, the same Chernoff
parameter `s = (n/u - 1)/2`, after dropping the factor `e^{-u/2} ≤ 1`). At the merge into
`ChiSquare.lean` both become corollaries of this tail and keep their names; the private
`measureReal_norm_sq_le_le_exp_mul_rpow` there is this bound before optimisation. The exponent of
Dasgupta and Gupta (2003), there for the projection of a uniform unit vector.
Result: chi-square-lower-tail -/
theorem measureReal_norm_sq_le_mul_card_le_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ) (hβ0 : 0 < β) (hβ : β ≤ 1) :
    μ.real {ω | ‖WithLp.toLp 2 (X ω)‖ ^ 2 ≤ β * Fintype.card n} ≤
      Real.exp (Fintype.card n / 2 * (1 - β + Real.log β)) := by
  sorry

/-- **Relative deviation of `χ²_n`**: `P(ε ≤ |‖X‖²/n - 1|) ≤ 2 exp (-n (ε²/4 - ε³/6))` for
`ε ≥ 0`, from the two Chernoff tails with `log (1 + ε) ≤ ε - ε²/2 + ε³/3` and
`log (1 - ε) ≤ -ε - ε²/2`; for `ε ≥ 1` the lower event is `{‖X‖² ≤ 0}`, null for nonempty `n`.
The bound is at least `2` for `ε ≥ 3/2` and for empty `n`. The exponent of Dasgupta and Gupta
(2003); [Woodruff2014, Lemma 18] has Laurent and Massart's `ε² n / 16` in its place. -/
theorem measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |‖WithLp.toLp 2 (X ω)‖ ^ 2 / Fintype.card n - 1|} ≤
      2 * Real.exp (-(Fintype.card n * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
  sorry

end NLAlib
