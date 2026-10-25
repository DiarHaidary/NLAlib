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

/-- Exponent arithmetic for the substitution $y \mapsto y^2$:
`x * (x ^ 2) ^ (d / 2 - 1) = x ^ (d - 1)`. -/
private theorem mul_rpow_sq_pow_eq {x : ℝ} (hx : 0 < x) {d : ℕ} (hd : 1 ≤ d) :
    x * (x ^ 2) ^ ((d : ℝ) / 2 - 1) = x ^ (d - 1) := by
  have hd' : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  rw [← Real.rpow_natCast x (d - 1), hd', ← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
  have e : x ^ ((d : ℝ) - 1) = x ^ (1 + ((2 : ℕ) : ℝ) * ((d : ℝ) / 2 - 1)) := by
    congr 1; push_cast; ring
  rw [e, Real.rpow_add hx, Real.rpow_one]

/-- The integrand of the substitution `y ↦ y ^ 2` on `(0, ∞)`, pointwise. -/
private theorem subst_integrand_eq {S : Set ℝ} {d : ℕ} (hd : 1 ≤ d) {x : ℝ} (hx : 0 < x) :
    (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) •
        S.indicator (fun z => gammaPDFReal ((d : ℝ) / 2) (1 / 2) z) (x ^ (2 : ℝ)) =
      2 * ((1 / 2 : ℝ) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
        (x ^ (d - 1) * (Real.exp (-x ^ 2 / 2) * S.indicator (1 : ℝ → ℝ) (x ^ 2))) := by
  rw [Real.rpow_two]
  norm_num
  by_cases h : x ^ 2 ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    simp only [gammaPDFReal, sq_nonneg, if_true, Pi.one_apply, mul_one]
    rw [← mul_rpow_sq_pow_eq hx hd, show -(1 / 2 * x ^ 2) = -x ^ 2 / 2 by ring]
    ring
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    simp

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
  classical
  have hd : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hdpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have hmeas : MeasurableSet {x : ι → ℝ | ∑ i, x i ^ 2 ∈ S} :=
    hS.preimage (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2)
  -- left side: the polar formula
  have hL : (Measure.pi fun _ : ι => gaussianReal 0 1).real {x | ∑ i, x i ^ 2 ∈ S} =
      ∫ x, S.indicator (1 : ℝ → ℝ) (‖WithLp.toLp 2 x‖ ^ 2)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
    rw [← integral_indicator_one hmeas]
    congr 1
    funext x
    rw [Set.indicator_apply, Set.indicator_apply, EuclideanSpace.real_norm_sq_eq]
    simp
  have hpolar := integral_comp_norm_pi_gaussianReal (ι := ι)
    (fun r : ℝ => S.indicator (1 : ℝ → ℝ) (r ^ 2))
  beta_reduce at hpolar
  -- right side: the Gamma density as an integral over `(0, ∞)`
  have hG1 : (gammaMeasure (Fintype.card ι / 2) (1 / 2)).real S =
      ∫ x, S.indicator (fun z => gammaPDFReal ((Fintype.card ι : ℝ) / 2) (1 / 2) z) x := by
    have hm : Measurable (gammaPDF ((Fintype.card ι : ℝ) / 2) (1 / 2)) := by
      unfold gammaPDF gammaPDFReal
      exact Measurable.ennreal_ofReal
        (Measurable.ite (measurableSet_le measurable_const measurable_id)
          (by fun_prop) measurable_const)
    rw [← integral_indicator_one hS, gammaMeasure,
      integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    congr 1
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, gammaPDF,
        ENNReal.toReal_ofReal
          (gammaPDFReal_nonneg (div_pos hdpos two_pos) (one_div_pos.mpr two_pos) _),
        smul_eq_mul, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, smul_zero]
  have hG2 : ∫ x, S.indicator (fun z => gammaPDFReal ((Fintype.card ι : ℝ) / 2) (1 / 2) z) x =
      ∫ x in Ioi (0 : ℝ),
        S.indicator (fun z => gammaPDFReal ((Fintype.card ι : ℝ) / 2) (1 / 2) z) x := by
    rw [← integral_Ici_eq_integral_Ioi]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    simp only [Set.mem_Ici, not_le] at hx
    simp [Set.indicator_apply, gammaPDFReal, not_le.mpr hx]
  have hsub := integral_comp_rpow_Ioi
    (fun z => S.indicator (fun z => gammaPDFReal ((Fintype.card ι : ℝ) / 2) (1 / 2) z) z)
    (p := 2) two_ne_zero
  beta_reduce at hsub
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => subst_integrand_eq hd hx),
    integral_const_mul] at hsub
  have hK : 2 * ((1 / 2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) / Real.Gamma ((Fintype.card ι : ℝ) / 2))
      = 1 / (2 ^ ((Fintype.card ι : ℝ) / 2 - 1) * Real.Gamma ((Fintype.card ι : ℝ) / 2)) := by
    have hdpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
    have hG : 0 < Real.Gamma ((Fintype.card ι : ℝ) / 2) :=
      Real.Gamma_pos_of_pos (by positivity)
    rw [Real.div_rpow zero_le_one zero_le_two, Real.one_rpow, Real.rpow_sub two_pos,
      Real.rpow_one]
    field_simp
  rw [hL, hpolar, hG1, hG2, ← hsub, hK]
  ring

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
