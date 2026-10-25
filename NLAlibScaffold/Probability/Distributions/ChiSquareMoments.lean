/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.ChiSquareMoments

/-!
# Moments of a difference of two independent chi-square variables (stage S10)

For independent standard Gaussian vectors $\mathbf{g}, \mathbf{h}$ of dimension
$d = \lvert n \rvert$,
the symmetric variable $X = \|\mathbf{g}\|^2 - \|\mathbf{h}\|^2$ has $\mathbb{E} X^2 = 4d$ and
$\mathbb{E} X^4 = 48 d^2 + 96 d$. These are the two moments the Paley–Zygmund step of the
early-truncation lower bound needs (`docs/design/LowRank-EstimatorLowerBounds.md`, §3.1). They
join `NLAlib/Probability/Distributions/ChiSquareMoments.lean`; their proofs are deferred.

## Main results

* `NLAlib.integral_norm_sq_sub_norm_sq_sq_of_hasLaw_gaussianVector`: $\mathbb{E}X^2 = 4d$.
* `NLAlib.integral_norm_sq_sub_norm_sq_pow_four_of_hasLaw_gaussianVector`:
  $\mathbb{E}X^4 = 48d^2 + 96d$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {g h : Ω → n → ℝ}

/-- **The variance of a difference of two independent $\chi^2_d$ variables**: for independent
standard Gaussian vectors $\mathbf{g}, \mathbf{h}$ of dimension $d = \lvert n \rvert$,
$$\mathbb{E}\bigl(\|\mathbf{g}\|^2 - \|\mathbf{h}\|^2\bigr)^2 = 4d\,.$$
Proof: S, about 20 lines. Expand the square; $\mathbb{E}\|\mathbf{g}\|^4 = d(d+2)$ and
$\mathbb{E}\|\mathbf{g}\|^2 = d$ from `integral_norm_sq_rpow_of_hasLaw_gaussianVector` at $s = 2, 1$
(`Real.Gamma_add_one`, `Real.rpow_natCast`), the cross term
$\mathbb{E}\|\mathbf{g}\|^2\|\mathbf{h}\|^2 = d^2$ by independence
(`IndepFun.integral_mul_eq_mul_integral`
after `IndepFun.comp` with the measurable map $x \mapsto \|x\|^2$); integrability from
`integrable_norm_sq_rpow_of_hasLaw_gaussianVector`. Then $2d(d+2) - 2d^2 = 4d$. -/
theorem integral_norm_sq_sub_norm_sq_sq_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hh : HasLaw h (gaussianVector n) μ)
    (hgh : IndepFun g h μ) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2 - ‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2 ∂μ =
      4 * Fintype.card n := by
  sorry

/-- **The fourth moment of a difference of two independent $\chi^2_d$ variables**: for
independent standard Gaussian vectors $\mathbf{g}, \mathbf{h}$ of dimension
$d = \lvert n \rvert$,
$$\mathbb{E}\bigl(\|\mathbf{g}\|^2 - \|\mathbf{h}\|^2\bigr)^4 = 48 d^2 + 96 d\,.$$
Proof: S, about 30 lines. With $U = \|\mathbf{g}\|^2$, $V = \|\mathbf{h}\|^2$ independent and
$\mathbb{E} U^j = d(d+2)\cdots(d+2j-2)$ (`integral_norm_sq_rpow_of_hasLaw_gaussianVector` at
$s = j$, `Real.Gamma_add_one` four times),
$\mathbb{E}(U - V)^4 = 2\mathbb{E}U^4 - 8\,\mathbb{E}U^3\,\mathbb{E}U + 6(\mathbb{E}U^2)^2$
(binomial expansion, `IndepFun.integral_mul_eq_mul_integral` on each mixed term), and
$2d(d+2)(d+4)(d+6) - 8d^2(d+2)(d+4) + 6d^2(d+2)^2 = 48d(d+2)$ (`ring`). -/
theorem integral_norm_sq_sub_norm_sq_pow_four_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hh : HasLaw h (gaussianVector n) μ)
    (hgh : IndepFun g h μ) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2 - ‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 4 ∂μ =
      48 * (Fintype.card n : ℝ) ^ 2 + 96 * Fintype.card n := by
  sorry

end NLAlib
