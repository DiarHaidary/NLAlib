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

private lemma integral_norm_sq_moments_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hd : 0 < Fintype.card n) :
    ∫ ω, ‖WithLp.toLp 2 (g ω)‖ ^ 2 ∂μ = Fintype.card n ∧
      ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ 2 ∂μ = Fintype.card n * (Fintype.card n + 2) := by
  have hdpos : (0 : ℝ) < Fintype.card n := by exact_mod_cast hd
  have hG : Real.Gamma ((Fintype.card n : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have h1 : Real.Gamma ((Fintype.card n : ℝ) / 2 + 1) =
      (Fintype.card n : ℝ) / 2 * Real.Gamma ((Fintype.card n : ℝ) / 2) :=
    Real.Gamma_add_one (by positivity)
  have h2 : Real.Gamma ((Fintype.card n : ℝ) / 2 + 2) =
      ((Fintype.card n : ℝ) / 2 + 1) * Real.Gamma ((Fintype.card n : ℝ) / 2 + 1) := by
    rw [show (Fintype.card n : ℝ) / 2 + 2 = ((Fintype.card n : ℝ) / 2 + 1) + 1 by ring]
    exact Real.Gamma_add_one (by positivity)
  constructor
  · have := integral_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := 1) (by linarith)
    simp only [Real.rpow_one] at this
    rw [this, h1]
    field_simp
  · have := integral_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := 2) (by linarith)
    simp only [Real.rpow_two] at this
    rw [this, h2, h1]
    field_simp

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
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hd0 | hd
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hd0
    simp [Subsingleton.elim (WithLp.toLp 2 (g _)) 0, Subsingleton.elim (WithLp.toLp 2 (h _)) 0]
  have hdpos : (0 : ℝ) < Fintype.card n := by exact_mod_cast hd
  obtain ⟨hU1, hU2⟩ := integral_norm_sq_moments_of_hasLaw_gaussianVector hg hd
  obtain ⟨hV1, hV2⟩ := integral_norm_sq_moments_of_hasLaw_gaussianVector hh hd
  have hmeas : Measurable fun x : n → ℝ => ‖WithLp.toLp 2 x‖ ^ 2 := by fun_prop
  have hind : IndepFun (fun ω => ‖WithLp.toLp 2 (g ω)‖ ^ 2)
      (fun ω => ‖WithLp.toLp 2 (h ω)‖ ^ 2) μ :=
    hgh.comp hmeas hmeas
  have hiU : Integrable (fun ω => ‖WithLp.toLp 2 (g ω)‖ ^ 2) μ := by
    have := integrable_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := 1) (by linarith)
    simpa only [Real.rpow_one] using this
  have hiV : Integrable (fun ω => ‖WithLp.toLp 2 (h ω)‖ ^ 2) μ := by
    have := integrable_norm_sq_rpow_of_hasLaw_gaussianVector hh (s := 1) (by linarith)
    simpa only [Real.rpow_one] using this
  have hiU2 : Integrable (fun ω => (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ 2) μ := by
    have := integrable_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := 2) (by linarith)
    simpa only [Real.rpow_two] using this
  have hiV2 : Integrable (fun ω => (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2) μ := by
    have := integrable_norm_sq_rpow_of_hasLaw_gaussianVector hh (s := 2) (by linarith)
    simpa only [Real.rpow_two] using this
  have hiUV : Integrable (fun ω => ‖WithLp.toLp 2 (g ω)‖ ^ 2 * ‖WithLp.toLp 2 (h ω)‖ ^ 2) μ :=
    hind.integrable_mul hiU hiV
  have hUV : ∫ ω, ‖WithLp.toLp 2 (g ω)‖ ^ 2 * ‖WithLp.toLp 2 (h ω)‖ ^ 2 ∂μ =
      Fintype.card n * Fintype.card n := by
    have h := hind.integral_mul_eq_mul_integral
      (hmeas.comp_aemeasurable hg.aemeasurable).aestronglyMeasurable
      (hmeas.comp_aemeasurable hh.aemeasurable).aestronglyMeasurable
    simp only [Pi.mul_apply] at h
    rw [h, hU1, hV1]
  have e : ∀ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2 - ‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2 =
      ((‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ 2 + (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2) -
        2 * (‖WithLp.toLp 2 (g ω)‖ ^ 2 * ‖WithLp.toLp 2 (h ω)‖ ^ 2) := fun ω => by ring
  have hI : Integrable (fun ω => (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ 2 +
      (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2) μ := hiU2.add hiV2
  have hJ : Integrable (fun ω => 2 * (‖WithLp.toLp 2 (g ω)‖ ^ 2 * ‖WithLp.toLp 2 (h ω)‖ ^ 2)) μ :=
    hiUV.const_mul 2
  simp only [e]
  rw [integral_sub hI hJ, integral_add hiU2 hiV2, integral_const_mul, hUV, hU2, hV2]
  ring

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
