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
public import Mathlib.Probability.HasLaw

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
* `ProbabilityTheory.map_sum_sq_pi_gaussianReal`: the chi-square law, measure-level.
* `ProbabilityTheory.hasLaw_sum_sq_of_hasLaw_pi_gaussianReal`: its `HasLaw` form.
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

/-! ### The chi-square law -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Exponent arithmetic for the substitution $y \mapsto y^2$:
`x * (x ^ 2) ^ (d / 2 - 1) = x ^ (d - 1)`. -/
private theorem mul_rpow_sq_pow_eq {x : ℝ} (hx : 0 < x) {d : ℕ} (hd : 1 ≤ d) :
    x * (x ^ 2) ^ ((d : ℝ) / 2 - 1) = x ^ (d - 1) := by
  have hd' : ((d - 1 : ℕ) : ℝ) = 1 + ((2 : ℕ) : ℝ) * ((d : ℝ) / 2 - 1) := by
    push_cast [Nat.cast_sub hd]
    ring
  rw [← Real.rpow_natCast x (d - 1), hd', Real.rpow_add hx, Real.rpow_one, Real.rpow_mul hx.le,
    Real.rpow_natCast]

/-- The integrand of the substitution `y ↦ y ^ 2` on `(0, ∞)`, pointwise. -/
private theorem subst_integrand_eq {S : Set ℝ} {d : ℕ} (hd : 1 ≤ d) {x : ℝ} (hx : 0 < x) :
    (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) •
        S.indicator (fun z => gammaPDFReal ((d : ℝ) / 2) (1 / 2) z) (x ^ (2 : ℝ)) =
      2 * ((1 / 2 : ℝ) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)) *
        (x ^ (d - 1) * (Real.exp (-x ^ 2 / 2) * S.indicator (1 : ℝ → ℝ) (x ^ 2))) := by
  by_cases h : x ^ 2 ∈ S
  · rw [Real.rpow_two, Set.indicator_of_mem h, Set.indicator_of_mem h, ← mul_rpow_sq_pow_eq hx hd]
    simp only [gammaPDFReal, sq_nonneg, if_true, Pi.one_apply]
    norm_num
    rw [show -(1 / 2 * x ^ 2) = -x ^ 2 / 2 by ring]
    ring
  · simp [Set.indicator_of_notMem h]

/-- The chi-square law, set by set: for $\iota$ nonempty and measurable $S \subseteq \mathbb{R}$,
the product of $d = \lvert\iota\rvert$ standard normal laws gives $\sum_i x_i^2 \in S$ the
probability that $\mathrm{Gamma}(d/2, 1/2)$ gives $S$. -/
private theorem measureReal_sum_sq_mem_pi_gaussianReal {ι : Type*} [Fintype ι] [Nonempty ι]
    {S : Set ℝ} (hS : MeasurableSet S) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real {x | ∑ i, x i ^ 2 ∈ S} =
      (gammaMeasure (Fintype.card ι / 2) (1 / 2)).real S := by
  classical
  have hd : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hdpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have hmeas : MeasurableSet {x : ι → ℝ | ∑ i, x i ^ 2 ∈ S} :=
    hS.preimage (by fun_prop)
  -- left side: the polar formula
  have hL : (Measure.pi fun _ : ι => gaussianReal 0 1).real {x | ∑ i, x i ^ 2 ∈ S} =
      ∫ x, S.indicator (1 : ℝ → ℝ) (‖WithLp.toLp 2 x‖ ^ 2)
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
    rw [← integral_indicator_one hmeas]
    congr with x
    simp [Set.indicator_apply, EuclideanSpace.real_norm_sq_eq]
  have hpolar := integral_comp_norm_pi_gaussianReal (ι := ι)
    (fun r : ℝ => S.indicator (1 : ℝ → ℝ) (r ^ 2))
  beta_reduce at hpolar
  -- right side: the Gamma density as an integral over `(0, ∞)`
  have hG1 : (gammaMeasure (Fintype.card ι / 2) (1 / 2)).real S =
      ∫ x, S.indicator (fun z => gammaPDFReal ((Fintype.card ι : ℝ) / 2) (1 / 2) z) x := by
    rw [integral_indicator hS, measureReal_def, gammaMeasure, withDensity_apply _ hS]
    refine (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => ?_) (by fun_prop)).symm
    exact gammaPDFReal_nonneg (div_pos hdpos two_pos) (one_div_pos.mpr two_pos) x
  have hG2 : ∫ x, S.indicator (fun z => gammaPDFReal ((Fintype.card ι : ℝ) / 2) (1 / 2) z) x =
      ∫ x in Ioi (0 : ℝ),
        S.indicator (fun z => gammaPDFReal ((Fintype.card ι : ℝ) / 2) (1 / 2) z) x := by
    rw [← integral_Ici_eq_integral_Ioi]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    simp [gammaPDFReal, show ¬0 ≤ x from hx]
  have hsub := integral_comp_rpow_Ioi
    (fun z => S.indicator (fun z => gammaPDFReal ((Fintype.card ι : ℝ) / 2) (1 / 2) z) z)
    (p := 2) two_ne_zero
  beta_reduce at hsub
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => subst_integrand_eq hd hx),
    integral_const_mul] at hsub
  have hK : 2 * ((1 / 2 : ℝ) ^ ((Fintype.card ι : ℝ) / 2) / Real.Gamma ((Fintype.card ι : ℝ) / 2))
      = 1 / (2 ^ ((Fintype.card ι : ℝ) / 2 - 1) * Real.Gamma ((Fintype.card ι : ℝ) / 2)) := by
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
Result: chi-square-law -/
theorem map_sum_sq_pi_gaussianReal {ι : Type*} [Fintype ι] [Nonempty ι] :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x => ∑ i, x i ^ 2) =
      gammaMeasure (Fintype.card ι / 2) (1 / 2) := by
  have hm : Measurable fun x : ι → ℝ => ∑ i, x i ^ 2 := by fun_prop
  have ha : (0 : ℝ) < Fintype.card ι / 2 := by
    have := Fintype.card_pos (α := ι)
    positivity
  have := isProbabilityMeasure_gammaMeasure ha (by norm_num : (0 : ℝ) < 1 / 2)
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hm hS]
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 ?_
  exact measureReal_sum_sq_mem_pi_gaussianReal hS

/-- The chi-square law, `HasLaw` form: if $\mathbf{g} = (\mathbf{g}_i)_{i \in \iota}$ has
independent standard normal coordinates (law the product of `gaussianReal 0 1`) and $\iota$ is
nonempty, then $\sum_i \mathbf{g}_i^2$ has law $\mathrm{Gamma}(d/2, 1/2)$ with
$d = \lvert\iota\rvert$, the chi-square law with $d$ degrees of freedom. -/
theorem hasLaw_sum_sq_of_hasLaw_pi_gaussianReal {ι : Type*} [Fintype ι] [Nonempty ι]
    {g : Ω → ι → ℝ} (hg : HasLaw g (Measure.pi fun _ : ι => gaussianReal 0 1) μ) :
    HasLaw (fun ω => ∑ i, g ω i ^ 2) (gammaMeasure (Fintype.card ι / 2) (1 / 2)) μ :=
  HasLaw.comp (Y := fun x : ι → ℝ => ∑ i, x i ^ 2)
    ⟨(by fun_prop : Measurable _).aemeasurable, map_sum_sq_pi_gaussianReal⟩ hg

end ProbabilityTheory
