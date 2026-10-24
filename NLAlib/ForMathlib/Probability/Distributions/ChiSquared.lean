/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Polar coordinates for a standard normal vector, and the chi-square law

For $d = \lvert\iota\rvert \ge 1$ independent standard normal coordinates $\mathbf{g}$, a radial
function integrates in polar coordinates against the $\chi_d$ density:
$$\mathbb{E}\,\varphi(\|\mathbf{g}\|) = \frac{1}{2^{d/2-1}\Gamma(d/2)}
\int_0^\infty y^{d-1}e^{-y^2/2}\varphi(y)\,dy\,.$$
This is the density behind the chi-square law $\chi^2_d$ of $\sum_i \mathbf{g}_i^2$, which is
Mathlib's `gammaMeasure (d / 2) (1 / 2)` (shape $d/2$, rate $1/2$).

Upstream candidate: a new file `Mathlib/Probability/Distributions/ChiSquared.lean` beside
`Gamma.lean`. Upstream, the natural statement is about `(stdGaussian (EuclideanSpace ℝ ι)).map
(‖·‖ ^ 2)`, through `map_pi_eq_stdGaussian`; here the law is `Measure.pi` of `gaussianReal 0 1`.

## Main results

* `ProbabilityTheory.integral_comp_norm_pi_gaussianReal`: polar coordinates, the $\chi_d$
  density.
-/

@[expose] public section

open MeasureTheory Real Set

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- The product of standard normal laws has the density
$(2\pi)^{-\lvert\iota\rvert/2} e^{-\|\mathbf{x}\|^2/2}$. -/
private theorem pi_gaussianReal_eq_withDensity :
    (Measure.pi fun _ : ι => gaussianReal 0 1) = volume.withDensity fun x : ι → ℝ =>
      ENNReal.ofReal ((√(2 * π))⁻¹ ^ Fintype.card ι * rexp (-‖WithLp.toLp 2 x‖ ^ 2 / 2)) := by
  have hprod (x : ι → ℝ) : ∏ i, gaussianPDFReal 0 1 (x i) =
      (√(2 * π))⁻¹ ^ Fintype.card ι * rexp (-‖WithLp.toLp 2 x‖ ^ 2 / 2) := by
    simp only [gaussianPDFReal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← Real.exp_sum, EuclideanSpace.real_norm_sq_eq, NNReal.coe_one, mul_one, sub_zero]
    congr 2
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
  simp only [← hprod]
  refine Measure.pi_eq fun s hs => ?_
  have hS : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hS, ← lintegral_indicator hS]
  have hind (x : ι → ℝ) : (Set.univ.pi s).indicator
      (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) x =
        ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _),
        ENNReal.ofReal_zero]
  simp only [hind]
  have hint : Integrable (fun x : ι → ℝ => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i))
      volume := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun i => (s i).indicator (gaussianPDFReal 0 1))
      (fun i => (integrable_gaussianPDFReal 0 1).indicator (hs i))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ =>
      Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _),
    integral_fintype_prod_volume_eq_prod, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun y =>
      Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, integral_indicator (hs i)]

/-- Polar coordinates for a radial function of standard normal coordinates, with the
normalising constant not yet evaluated. -/
private theorem integral_comp_norm_pi_gaussianReal_eq_mul [Nonempty ι] (φ : ℝ → ℝ) :
    ∫ x, φ ‖WithLp.toLp 2 x‖ ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      Fintype.card ι * (volume : Measure (EuclideanSpace ℝ ι)).real (Metric.ball 0 1) *
        ((√(2 * π))⁻¹ ^ Fintype.card ι *
          ∫ y in Ioi (0 : ℝ), y ^ (Fintype.card ι - 1) * (rexp (-y ^ 2 / 2) * φ y)) := by
  rw [pi_gaussianReal_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hpos (x : ι → ℝ) :
      0 ≤ (√(2 * π))⁻¹ ^ Fintype.card ι * rexp (-‖WithLp.toLp 2 x‖ ^ 2 / 2) := by positivity
  simp only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul]
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding
  rw [(PiLp.volume_preserving_toLp ι).integral_comp hemb (fun y : EuclideanSpace ℝ ι =>
      (√(2 * π))⁻¹ ^ Fintype.card ι * rexp (-‖y‖ ^ 2 / 2) * φ ‖y‖),
    integral_fun_norm_addHaar volume (fun r =>
      (√(2 * π))⁻¹ ^ Fintype.card ι * rexp (-r ^ 2 / 2) * φ r),
    finrank_euclideanSpace, nsmul_eq_mul, smul_eq_mul]
  simp only [smul_eq_mul]
  have e (y : ℝ) : y ^ (Fintype.card ι - 1) * ((√(2 * π))⁻¹ ^ Fintype.card ι *
      rexp (-y ^ 2 / 2) * φ y) = (√(2 * π))⁻¹ ^ Fintype.card ι *
        (y ^ (Fintype.card ι - 1) * (rexp (-y ^ 2 / 2) * φ y)) := by ring
  simp only [e, integral_const_mul]
  ring

/-- The $\chi_d$ normalising constant:
$\int_0^\infty y^{d-1} e^{-y^2/2}\,dy = 2^{d/2-1}\Gamma(d/2)$ for $d \ge 1$. -/
private theorem integral_pow_mul_exp_neg_sq_div_two {d : ℕ} (hd : 1 ≤ d) :
    ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * rexp (-y ^ 2 / 2) =
      2 ^ ((d : ℝ) / 2 - 1) * Real.Gamma ((d : ℝ) / 2) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (d : ℝ) - 1) (b := 1 / 2)
    (by norm_num) (by linarith) (by norm_num)
  have hhalf : (1 / 2 : ℝ) ^ (-((d : ℝ) - 1 + 1) / 2) * (1 / 2) = 2 ^ ((d : ℝ) / 2 - 1) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
      Real.rpow_sub (by norm_num), Real.rpow_one]
    ring_nf
  rw [show ((d : ℝ) - 1 + 1) / 2 = (d : ℝ) / 2 by ring, hhalf] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  rw [← Real.rpow_natCast, hcast, Real.rpow_two]
  congr 2
  ring

/-- **Polar coordinates for a standard normal vector**: for $d = \lvert\iota\rvert \ge 1$
independent standard normal coordinates $\mathbf{g}$ ($\iota$ nonempty) and every
$\varphi : \mathbb{R} \to \mathbb{R}$,
$$\mathbb{E}\,\varphi(\|\mathbf{g}\|) = \frac{1}{2^{d/2 - 1}\,\Gamma(d/2)}
\int_0^\infty y^{d-1} e^{-y^2/2} \varphi(y)\,dy\,,$$
the $\chi_d$ density. Both sides are Bochner integrals, so the identity also holds (as $0 = 0$)
when either side is not integrable. -/
theorem integral_comp_norm_pi_gaussianReal [Nonempty ι] (φ : ℝ → ℝ) :
    ∫ x, φ ‖WithLp.toLp 2 x‖ ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      (∫ y in Ioi (0 : ℝ), y ^ (Fintype.card ι - 1) * (Real.exp (-y ^ 2 / 2) * φ y)) /
        (2 ^ ((Fintype.card ι : ℝ) / 2 - 1) * Real.Gamma ((Fintype.card ι : ℝ) / 2)) := by
  rw [integral_comp_norm_pi_gaussianReal_eq_mul]
  have hnorm := integral_comp_norm_pi_gaussianReal_eq_mul (ι := ι) (fun _ => 1)
  set d := Fintype.card ι with hd_def
  have hd : 1 ≤ d := Fintype.card_pos
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hnorm
  rw [integral_pow_mul_exp_neg_sq_div_two hd] at hnorm
  have hG : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  rw [eq_div_iff (by positivity)]
  set I := ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * (rexp (-y ^ 2 / 2) * φ y)
  linear_combination (-I) * hnorm

end ProbabilityTheory
