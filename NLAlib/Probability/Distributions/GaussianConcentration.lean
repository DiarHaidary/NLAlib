/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2
public import NLAlib.Probability.Distributions.GaussianLogSobolev
public import NLAlib.Probability.SubGaussian.Basic

/-!
# Gaussian concentration of Lipschitz functions

A Lipschitz function $f$ of a standard Gaussian vector is sub-Gaussian about its mean with proxy
$L^2$, where $L$ is its Lipschitz constant for the Euclidean norm (Tsirelson, Ibragimov and
Sudakov); the constant is sharp. The general statement is for Mathlib's `stdGaussian E` on a
Euclidean space; for `f : (n → ℝ) → ℝ` and $\mathbf{g}$ with law `gaussianVector n`, the Lipschitz
hypothesis is stated on `EuclideanSpace ℝ n`, since `n → ℝ` carries the sup metric, and
`EuclideanSpace.lipschitzWith_ofLp_iff` turns it into the explicit inequality.

## Main results

* `NLAlib.hasSubgaussianMGF_sub_integral_of_lipschitzWith_of_hasLaw_stdGaussian`.
* `NLAlib.hasSubgaussianMGF_sub_integral_of_lipschitzWith_of_hasLaw_gaussianVector`.
* `NLAlib.measureReal_ge_integral_add_le_of_lipschitzWith_of_hasLaw_gaussianVector`: the upper tail.
* `NLAlib.mul_exp_neg_sq_le_measureReal_abs_ge_of_hasLaw_gaussianReal`: a lower absolute tail
  of the scalar standard Gaussian, from its density.

## References

* [S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*][BoucheronLugosiMassart2013],
  Theorem 5.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {g : Ω → E} {f : E → ℝ} {L : ℝ≥0}

/-- A Lipschitz function of a standard Gaussian vector is integrable. -/
theorem integrable_comp_of_lipschitzWith_of_hasLaw_stdGaussian (hg : HasLaw g (stdGaussian E) μ)
    (hf : LipschitzWith L f) : Integrable (fun ω => f (g ω)) μ := by
  exact (hg.integrable_comp_iff hf.continuous.aestronglyMeasurable).2
    (hasLogSobolev_stdGaussian.integrable_of_lipschitzWith hf)

/-- **Gaussian concentration of Lipschitz functions** ([BoucheronLugosiMassart2013,
Theorem 5.6]): for $\mathbf{g}$ with law `stdGaussian E` and $f$ $L$-Lipschitz,
$f(\mathbf{g}) - \mathbb{E} f(\mathbf{g})$ is sub-Gaussian with proxy $L^2$.
Result: gaussian-lipschitz-concentration -/
theorem hasSubgaussianMGF_sub_integral_of_lipschitzWith_of_hasLaw_stdGaussian
    (hg : HasLaw g (stdGaussian E) μ) (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun ω => f (g ω) - ∫ ω', f (g ω') ∂μ) (L ^ 2) μ := by
  have h := hasLogSobolev_stdGaussian.hasSubgaussianMGF_sub_integral (E := E) hf
  rw [one_mul, ← hg.map_eq] at h
  have hint : ∫ ω', f (g ω') ∂μ = ∫ y, f y ∂μ.map g := by
    rw [hg.map_eq]
    exact hg.integral_comp hf.continuous.aestronglyMeasurable
  rw [hint]
  exact h.of_map hg.aemeasurable

end Euclidean

section Vector

variable {n : Type*} [Fintype n] {g : Ω → n → ℝ} {f : (n → ℝ) → ℝ} {L : ℝ≥0}

/-- Gaussian concentration for a standard Gaussian vector $\mathbf{g}$ in $\mathbb{R}^n$, with
$f$ $L$-Lipschitz for the Euclidean norm: $f(\mathbf{g}) - \mathbb{E} f(\mathbf{g})$ is
sub-Gaussian with proxy $L^2$. -/
theorem hasSubgaussianMGF_sub_integral_of_lipschitzWith_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ)
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ n => f (WithLp.ofLp x))) :
    HasSubgaussianMGF (fun ω => f (g ω) - ∫ ω', f (g ω') ∂μ) (L ^ 2) μ := by
  have hY : HasLaw (fun ω => WithLp.toLp 2 (g ω)) (stdGaussian (EuclideanSpace ℝ n)) μ :=
    HasLaw.comp (Y := WithLp.toLp 2) ⟨by fun_prop, map_pi_eq_stdGaussian⟩ hg
  exact hasSubgaussianMGF_sub_integral_of_lipschitzWith_of_hasLaw_stdGaussian
    (f := fun x : EuclideanSpace ℝ n => f (WithLp.ofLp x)) hY hf

/-- A Lipschitz function of a standard Gaussian vector in $\mathbb{R}^n$ is integrable. -/
theorem integrable_comp_of_lipschitzWith_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ)
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ n => f (WithLp.ofLp x))) :
    Integrable (fun ω => f (g ω)) μ := by
  have hY : HasLaw (fun ω => WithLp.toLp 2 (g ω)) (stdGaussian (EuclideanSpace ℝ n)) μ :=
    HasLaw.comp (Y := WithLp.toLp 2) ⟨by fun_prop, map_pi_eq_stdGaussian⟩ hg
  exact integrable_comp_of_lipschitzWith_of_hasLaw_stdGaussian
    (f := fun x : EuclideanSpace ℝ n => f (WithLp.ofLp x)) hY hf

/-- The upper tail of a Lipschitz function of a standard Gaussian vector: for $f$ $L$-Lipschitz
for the Euclidean norm and $t \ge 0$,
$$\mathbb{P}\bigl[\mathbb{E} f(\mathbf{g}) + t \le f(\mathbf{g})\bigr]
\le \exp\Bigl(-\frac{t^2}{2L^2}\Bigr),$$
with the event in the form the random-matrix consumers use. -/
theorem measureReal_ge_integral_add_le_of_lipschitzWith_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ)
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ n => f (WithLp.ofLp x))) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | ∫ ω', f (g ω') ∂μ + t ≤ f (g ω)} ≤ rexp (-t ^ 2 / (2 * L ^ 2)) := by
  have h := (hasSubgaussianMGF_sub_integral_of_lipschitzWith_of_hasLaw_gaussianVector hg
    hf).measure_ge_le ht
  simp only [le_sub_iff_add_le', NNReal.coe_pow] at h
  exact h

end Vector

/-! ### A scalar lower tail -/

/-- A positive factor in the standard Gaussian lower absolute tail.
Its value is <!-- value gaussianLowerTailConstant -->$e^{-1}/\sqrt{2\pi}$, from integrating the
density on a unit interval. -/
noncomputable irreducible_def gaussianLowerTailConstant : ℝ :=
  Real.exp (-1) / Real.sqrt (2 * Real.pi)

/-- The scalar Gaussian lower-tail factor is positive. -/
theorem gaussianLowerTailConstant_pos : 0 < gaussianLowerTailConstant := by
  rw [gaussianLowerTailConstant_def]
  positivity

/-- The Gaussian density on $[t,t+1]$ gives a uniform lower mass. -/
private theorem gaussianLowerTailConstant_mul_exp_le_measureReal_Icc (t : ℝ) (ht : 0 ≤ t) :
    gaussianLowerTailConstant * exp (-t ^ 2) ≤ (gaussianReal 0 1).real (Set.Icc t (t + 1)) := by
  rw [gaussianLowerTailConstant_def]
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc t (t + 1)) :
      exp (-1) / sqrt (2 * π) * exp (-t ^ 2) ≤ gaussianPDFReal 0 1 x := by
    have hx0 : 0 ≤ x := ht.trans hx.1
    have hsq : x ^ 2 ≤ (t + 1) ^ 2 := pow_le_pow_left₀ hx0 hx.2 2
    have he : -t ^ 2 - 1 ≤ -x ^ 2 / 2 := by nlinarith [sq_nonneg (t - 1)]
    have hexp := exp_le_exp.mpr he
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [show exp (-1) / sqrt (2 * π) * exp (-t ^ 2) =
      (1 / sqrt (2 * π)) * exp (-t ^ 2 - 1) by rw [sub_eq_add_neg, exp_add]; ring]
    simpa only [one_div] using mul_le_mul_of_nonneg_left hexp
      (inv_nonneg.mpr (sqrt_nonneg (2 * π)))
  have hconst : IntegrableOn (fun _ : ℝ => exp (-1) / sqrt (2 * π) * exp (-t ^ 2))
      (Set.Icc t (t + 1)) volume := integrableOn_const (isCompact_Icc.measure_lt_top.ne)
  have hmono := setIntegral_mono_on hconst (integrable_gaussianPDFReal 0 1).restrict
    measurableSet_Icc hpoint
  rw [integral_const] at hmono
  simp only [Measure.real, Measure.restrict_apply_univ] at hmono
  change volume.real (Set.Icc t (t + 1)) • _ ≤ _ at hmono
  rw [volume_real_Icc_of_le (by linarith), show t + 1 - t = 1 by ring, one_smul] at hmono
  rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num), ENNReal.toReal_ofReal
    (integral_nonneg fun x => gaussianPDFReal_nonneg 0 1 x)]
  exact hmono

/-- For a standard scalar Gaussian and $t\ge0$, the absolute upper-tail event has the lower
bound <!-- value gaussianLowerTailConstant -->$e^{-1}/\sqrt{2\pi}\,e^{-t^2}$.
The Lean factor is `gaussianLowerTailConstant`; the bound follows by integrating the density
on $[t,t+1]$. Port of `NLAlib.exp_neg_sq_div_sqrt_two_pi_le_gaussianReal_abs_tail`. -/
theorem mul_exp_neg_sq_le_measureReal_abs_ge_of_hasLaw_gaussianReal
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) μ) {t : ℝ} (ht : 0 ≤ t) :
    gaussianLowerTailConstant * exp (-t ^ 2) ≤ μ.real {ω | t ≤ |X ω|} := by
  rw [hX.measureReal_eq (p := fun x => t ≤ |x|)
    (measurableSet_le measurable_const measurable_abs)]
  refine (gaussianLowerTailConstant_mul_exp_le_measureReal_Icc t ht).trans ?_
  exact measureReal_mono (fun x hx => hx.1.trans (le_abs_self x))

end NLAlib
