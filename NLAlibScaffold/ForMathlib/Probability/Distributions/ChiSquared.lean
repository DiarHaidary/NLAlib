/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.HasLaw
public import NLAlib.ForMathlib.Probability.Distributions.ChiSquared

/-!
# The chi-square law

Statements for `NLAlib/ForMathlib/Probability/Distributions/ChiSquared.lean` whose proofs are
deferred (`docs/design/Probability-Beta.md`, §3.1, β1a, β1, β1h). For $d = \lvert\iota\rvert \ge 1$
independent standard normal coordinates, $\sum_i \mathbf{g}_i^2$ has the chi-square law
$\chi^2_d$, which is `gammaMeasure (d / 2) (1 / 2)` (shape $d/2$, rate $1/2$): the polar formula
`ProbabilityTheory.integral_comp_norm_pi_gaussianReal` and the substitution $y \mapsto y^2$.
The primary statement is Mathlib's measure-level form, an equality of `Measure.map`s; the
`HasLaw` form is its corollary. Upstream candidate for a new
`Mathlib/Probability/Distributions/ChiSquared.lean`, there about
`(stdGaussian (EuclideanSpace ℝ ι)).map (‖·‖ ^ 2)` (`map_pi_eq_stdGaussian`).

## Main results

* `ProbabilityTheory.map_sum_sq_pi_gaussianReal`: the chi-square law, measure-level.
* `ProbabilityTheory.hasLaw_sum_sq_of_hasLaw_pi_gaussianReal`: its `HasLaw` form.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The chi-square law, set by set: for $\iota$ nonempty and measurable $S \subseteq \mathbb{R}$,
the product of $d = \lvert\iota\rvert$ standard normal laws gives $\sum_i x_i^2 \in S$ the
probability that $\mathrm{Gamma}(d/2, 1/2)$ gives $S$.
Proof: M, about 45 lines. `integral_comp_norm_pi_gaussianReal` with
`φ := S.indicator 1 ∘ (· ^ 2)` (`EuclideanSpace.real_norm_sq_eq` for
$\|\mathbf{x}\|^2 = \sum_i x_i^2$, `integral_indicator_one`); the substitution $y \mapsto y^2$ on
$(0, \infty)$ (`integral_comp_rpow_Ioi` with `p := 2`; `Real.rpow_natCast`, `Real.rpow_mul`);
the Gamma side by `gammaMeasure`, `withDensity_apply`, `gammaPDF_of_nonneg`,
`ofReal_integral_eq_lintegral_ofReal` and `measureReal_def`. -/
private theorem measureReal_sum_sq_mem_pi_gaussianReal {ι : Type*} [Fintype ι] [Nonempty ι]
    {S : Set ℝ} (hS : MeasurableSet S) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real {x | ∑ i, x i ^ 2 ∈ S} =
      (gammaMeasure (Fintype.card ι / 2) (1 / 2)).real S := by
  sorry

/-- **The chi-square law**: for $\iota$ nonempty, under the product of $d = \lvert\iota\rvert$
standard normal laws, $\sum_i x_i^2$ has law $\mathrm{Gamma}(d/2, 1/2)$ (shape $d/2$, rate
$1/2$), the chi-square law $\chi^2_d$. For empty $\iota$ the sum is $0$ while
`gammaMeasure 0 (1 / 2)` is the zero measure.
No printed source.
Proof: S, about 20 lines. `Measure.ext` through `measureReal` (both sides are probability
measures: `isProbabilityMeasure_gammaMeasure`, `Measure.isProbabilityMeasure_map`),
`Measure.map_apply` (the sum of squares is measurable), and
`measureReal_sum_sq_mem_pi_gaussianReal`.
Result: chi-square-law -/
theorem map_sum_sq_pi_gaussianReal {ι : Type*} [Fintype ι] [Nonempty ι] :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x => ∑ i, x i ^ 2) =
      gammaMeasure (Fintype.card ι / 2) (1 / 2) := by
  sorry

/-- The chi-square law, `HasLaw` form: if $\mathbf{g} = (\mathbf{g}_i)_{i \in \iota}$ has
independent standard normal coordinates (law the product of `gaussianReal 0 1`) and $\iota$ is
nonempty, then $\sum_i \mathbf{g}_i^2$ has law $\mathrm{Gamma}(d/2, 1/2)$ with
$d = \lvert\iota\rvert$, the chi-square law with $d$ degrees of freedom.
Proof: S, about 5 lines. `HasLaw.comp` of `map_sum_sq_pi_gaussianReal` (as
`⟨measurable.aemeasurable, map_sum_sq_pi_gaussianReal⟩`) with `hg`. -/
theorem hasLaw_sum_sq_of_hasLaw_pi_gaussianReal {ι : Type*} [Fintype ι] [Nonempty ι]
    {g : Ω → ι → ℝ} (hg : HasLaw g (Measure.pi fun _ : ι => gaussianReal 0 1) μ) :
    HasLaw (fun ω => ∑ i, g ω i ^ 2) (gammaMeasure (Fintype.card ι / 2) (1 / 2)) μ := by
  sorry

end ProbabilityTheory
