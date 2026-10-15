/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Gamma.Basic
public import NLAlib.Probability.Distributions.ChiSquareMoments
public import NLAlib.Probability.SubGaussian.Square

/-!
# The squared norm of a standard Gaussian vector

The squared norm of a standard Gaussian vector $\mathbf{g}$ in $\mathbb{R}^n$ is $\chi^2$ with
$d = \lvert n \rvert$ degrees of freedom. This file gives its Laplace transform, weighted and
unweighted, and its tails. Chernoff's bound with the exact Laplace transform at
$\theta = (1 - 1/\beta)/2$ gives $\mathbb{P}(\|\mathbf{g}\|^2 \ge \beta d)$ and
$\mathbb{P}(\|\mathbf{g}\|^2 \le \beta d)$ at most $e^{(d/2)(1 - \beta + \log \beta)}$, on either
side of $\beta = 1$, with the exponent of Dasgupta and Gupta (2003). The lower tail gives
Laurent and Massart's lower tail as a corollary (CONTRIBUTING §5.2, rule 6). The exact small ball
$\mathbb{P}(\|\mathbf{g}\|^2 \le u) \le (u/2)^{d/2} / \Gamma(d/2 + 1)$ comes from the
$\chi^2_d$ density in `NLAlib/Probability/Distributions/ChiSquareMoments.lean`, and the Chernoff
small ball $(e u / d)^{d/2}$ is its corollary. The relative deviation
$\mathbb{P}(\varepsilon \le \lvert \|\mathbf{g}\|^2/d - 1 \rvert)
\le 2 e^{-d(\varepsilon^2/4 - \varepsilon^3/6)}$ is the case of standard Gaussian coordinates of
the sums-of-squares tail `NLAlib.measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun`.
Laurent and Massart's upper tail is the sub-Gaussian-vector bound
`NLAlib.IsSubgaussianVector.measure_norm_sq_ge_le` at proxy $1$. The weighted Laplace transform
$\mathbb{E} \exp(\sum_i \theta_i \mathbf{g}_i^2)$ is the input of the projection tails of a
uniform unit vector (`NLAlib/RandomMatrix/Haar/Sphere.lean`) and of the weighted squares of a
sub-Gaussian vector (`NLAlib/Probability/SubGaussianVector/Norm.lean`).

## Main results

* `NLAlib.integral_exp_sum_mul_sq_of_hasLaw_gaussianVector`:
  $\mathbb{E} \exp(\sum_i \theta_i \mathbf{g}_i^2) = \prod_i (1 - 2\theta_i)^{-1/2}$.
* `NLAlib.integral_exp_mul_norm_sq_of_hasLaw_gaussianVector`:
  $\mathbb{E}\, e^{\theta \|\mathbf{g}\|^2} = (1 - 2\theta)^{-d/2}$.
* `NLAlib.measureReal_mul_card_le_norm_sq_le_of_hasLaw_gaussianVector`: the upper Chernoff tail,
  $\beta \ge 1$.
* `NLAlib.measureReal_norm_sq_le_mul_card_le_of_hasLaw_gaussianVector`: the lower Chernoff tail,
  $0 < \beta \le 1$.
* `NLAlib.measureReal_norm_sq_le_of_hasLaw_gaussianVector`:
  $\mathbb{P}(\|\mathbf{g}\|^2 \le d - 2\sqrt{d t}) \le e^{-t}$.
* `NLAlib.measureReal_norm_sq_le_le_rpow_div_Gamma_of_hasLaw_gaussianVector`: the exact small
  ball $\mathbb{P}(\|\mathbf{g}\|^2 \le u) \le (u/2)^{d/2} / \Gamma(d/2 + 1)$.
* `NLAlib.measureReal_norm_sq_le_le_rpow_of_hasLaw_gaussianVector`: the small ball
  $\mathbb{P}(\|\mathbf{g}\|^2 \le u) \le (e u / d)^{d/2}$.
* `NLAlib.measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector`: the relative
  deviation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {g : Ω → n → ℝ} {ε β : ℝ}

/-! ### Laplace transforms -/

private theorem integral_exp_mul_sq_gaussianReal {θ : ℝ} (hθ : 2 * θ < 1) :
    ∫ y, rexp (θ * y ^ 2) ∂(gaussianReal 0 1) = (1 - 2 * θ) ^ (-(1 / 2 : ℝ)) := by
  have hu : 0 < 1 - 2 * θ := by linarith
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal_def, smul_eq_mul, NNReal.coe_one, sub_zero, mul_one]
  have h (x : ℝ) : (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * rexp (θ * x ^ 2)
      = (√(2 * π))⁻¹ * rexp (-((1 - 2 * θ) / 2) * x ^ 2) := by
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  simp only [h]
  rw [integral_const_mul, integral_gaussian,
    show π / ((1 - 2 * θ) / 2) = (2 * π) / (1 - 2 * θ) by field_simp,
    Real.sqrt_div (by positivity), Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  have : √(2 * π) ≠ 0 := by positivity
  field_simp

/-- **The weighted Laplace transform of a Gaussian vector**: for a standard Gaussian vector
$\mathbf{g}$ and weights with $\theta_i < 1/2$,
$\mathbb{E} \exp(\sum_i \theta_i \mathbf{g}_i^2) = \prod_i (1 - 2\theta_i)^{-1/2}$, by independence
of the coordinates. The equal-weight case is
`NLAlib.integral_exp_mul_norm_sq_of_hasLaw_gaussianVector`; two weights give the projection tails
of a uniform unit vector. -/
theorem integral_exp_sum_mul_sq_of_hasLaw_gaussianVector (hg : HasLaw g (gaussianVector n) μ)
    {θ : n → ℝ} (hθ : ∀ i, 2 * θ i < 1) :
    ∫ ω, rexp (∑ i, θ i * g ω i ^ 2) ∂μ = ∏ i, (1 - 2 * θ i) ^ (-(1 / 2 : ℝ)) := by
  refine (hg.integral_comp (f := fun x : n → ℝ => rexp (∑ i, θ i * x i ^ 2))
    (Continuous.aestronglyMeasurable (by fun_prop))).trans ?_
  simp only [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i y => rexp (θ i * y ^ 2))]
  exact Finset.prod_congr rfl fun i _ => integral_exp_mul_sq_gaussianReal (hθ i)

/-- The Laplace transform of $\chi^2$: for a standard Gaussian vector $\mathbf{g}$ and
$\theta < 1/2$, $\mathbb{E}\, e^{\theta \|\mathbf{g}\|^2} = (1 - 2\theta)^{-d/2}$, where
$d = \lvert n \rvert$. -/
theorem integral_exp_mul_norm_sq_of_hasLaw_gaussianVector (hg : HasLaw g (gaussianVector n) μ)
    {θ : ℝ} (hθ : 2 * θ < 1) :
    ∫ ω, rexp (θ * ‖WithLp.toLp 2 (g ω)‖ ^ 2) ∂μ = (1 - 2 * θ) ^ (-(Fintype.card n / 2 : ℝ)) := by
  have h (x : n → ℝ) : θ * ‖WithLp.toLp 2 x‖ ^ 2 = ∑ i, θ * x i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  simp only [h]
  rw [integral_exp_sum_mul_sq_of_hasLaw_gaussianVector hg (θ := fun _ => θ) fun _ => hθ,
    Finset.prod_const, Finset.card_univ, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  congr 1
  ring

/-! ### Chernoff tails -/

/-- Chernoff's bound at $\theta$, with the exact Laplace transform, for the upper tail: for
$0 \le \theta < 1/2$,
$\mathbb{P}(c \le \|\mathbf{g}\|^2) \le e^{-\theta c} (1 - 2\theta)^{-\lvert n \rvert / 2}$. -/
private theorem measureReal_le_norm_sq_le_exp_mul_rpow (hg : HasLaw g (gaussianVector n) μ)
    (c : ℝ) {θ : ℝ} (hθ : 2 * θ < 1) (hθ0 : 0 ≤ θ) :
    μ.real {ω | c ≤ ‖WithLp.toLp 2 (g ω)‖ ^ 2} ≤
      rexp (-θ * c) * (1 - 2 * θ) ^ (-(Fintype.card n / 2 : ℝ)) := by
  have : IsProbabilityMeasure μ := hg.isProbabilityMeasure_iff.2 inferInstance
  have hlap := integral_exp_mul_norm_sq_of_hasLaw_gaussianVector hg hθ
  have hint : Integrable (fun ω => rexp (θ * ‖WithLp.toLp 2 (g ω)‖ ^ 2)) μ :=
    Integrable.of_integral_ne_zero (by rw [hlap]; exact (Real.rpow_pos_of_pos (by linarith) _).ne')
  have h := measure_ge_le_exp_mul_mgf (X := fun ω => ‖WithLp.toLp 2 (g ω)‖ ^ 2) c hθ0 hint
  rwa [mgf, hlap] at h

/-- Chernoff's bound at $-s$, with the exact Laplace transform, for the lower tail: for $s \ge 0$,
$\mathbb{P}(\|\mathbf{g}\|^2 \le c) \le e^{s c} (1 + 2s)^{-\lvert n \rvert / 2}$. -/
private theorem measureReal_norm_sq_le_le_exp_mul_rpow (hg : HasLaw g (gaussianVector n) μ)
    (c : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ‖WithLp.toLp 2 (g ω)‖ ^ 2 ≤ c} ≤
      rexp (s * c) * (1 + 2 * s) ^ (-(Fintype.card n / 2 : ℝ)) := by
  have : IsProbabilityMeasure μ := hg.isProbabilityMeasure_iff.2 inferInstance
  have hlap := integral_exp_mul_norm_sq_of_hasLaw_gaussianVector hg (θ := -s) (by linarith)
  rw [show 1 - 2 * -s = 1 + 2 * s by ring] at hlap
  have hint : Integrable (fun ω => rexp (-s * ‖WithLp.toLp 2 (g ω)‖ ^ 2)) μ :=
    Integrable.of_integral_ne_zero (by rw [hlap]; exact (Real.rpow_pos_of_pos (by linarith) _).ne')
  have h := measure_le_le_exp_mul_mgf (X := fun ω => ‖WithLp.toLp 2 (g ω)‖ ^ 2) c
    (neg_nonpos.2 hs) hint
  rwa [mgf, hlap, neg_neg] at h

/-- $e^{a} (\beta^{-1})^{-N/2} = e^{a + (N/2) \log \beta}$ for $\beta > 0$. -/
private theorem exp_mul_inv_rpow (a N : ℝ) (hβ : 0 < β) :
    rexp a * (β⁻¹) ^ (-(N / 2 : ℝ)) = rexp (a + N / 2 * Real.log β) := by
  rw [Real.inv_rpow hβ.le, ← Real.rpow_neg hβ.le, neg_neg, Real.rpow_def_of_pos hβ,
    ← Real.exp_add]
  ring_nf

/-- **Upper Chernoff tail of $\chi^2$**: for a standard Gaussian vector $\mathbf{g}$ of dimension
$d = \lvert n \rvert$ and $\beta \ge 1$,
$\mathbb{P}(\beta d \le \|\mathbf{g}\|^2) \le e^{(d/2)(1 - \beta + \log \beta)}$, Chernoff's bound
with the exact Laplace transform at $\theta = (1 - 1/\beta)/2$. At every
threshold it is at least as good as Laurent and Massart's upper tail, which stays in the library
as the sub-Gaussian-vector bound `NLAlib.IsSubgaussianVector.measure_norm_sq_ge_le` at proxy $1$
(rule 6: that theorem is about every sub-Gaussian vector and keeps its form). The exponent of
Dasgupta and Gupta (2003), there for the projection of a uniform unit vector.
Result: chi-square-upper-tail -/
theorem measureReal_mul_card_le_norm_sq_le_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hβ : 1 ≤ β) :
    μ.real {ω | β * Fintype.card n ≤ ‖WithLp.toLp 2 (g ω)‖ ^ 2} ≤
      rexp (Fintype.card n / 2 * (1 - β + Real.log β)) := by
  have hβ0 : 0 < β := by linarith
  have hθ : 2 * ((1 - β⁻¹) / 2) < 1 := by
    have := inv_pos.2 hβ0; linarith
  have hθ0 : 0 ≤ (1 - β⁻¹) / 2 := by
    have := inv_le_one_of_one_le₀ hβ; linarith
  refine (measureReal_le_norm_sq_le_exp_mul_rpow hg _ hθ hθ0).trans (le_of_eq ?_)
  rw [show 1 - 2 * ((1 - β⁻¹) / 2) = β⁻¹ by ring, exp_mul_inv_rpow _ _ hβ0]
  congr 1
  field_simp
  ring

/-- **Lower Chernoff tail of $\chi^2$**: for a standard Gaussian vector $\mathbf{g}$ of dimension
$d = \lvert n \rvert$ and $0 < \beta \le 1$,
$\mathbb{P}(\|\mathbf{g}\|^2 \le \beta d) \le e^{(d/2)(1 - \beta + \log \beta)}$, Chernoff's bound
with the exact Laplace transform at $\theta = (1 - 1/\beta)/2$. It dominates
(CONTRIBUTING §5.2 rule 6) Laurent and Massart's
`NLAlib.measureReal_norm_sq_le_of_hasLaw_gaussianVector` (at $\beta = 1 - 2\sqrt{t/d}$, with
$\log(1 - u) \le -u - u^2/2$), which is proved from it, and the small ball
`NLAlib.measureReal_norm_sq_le_le_rpow_of_hasLaw_gaussianVector` (at $\beta = u/d$, after dropping
the factor $e^{-u/2} \le 1$), which is proved from the sharper exact small ball
`NLAlib.measureReal_norm_sq_le_le_rpow_div_Gamma_of_hasLaw_gaussianVector`. The exponent of
Dasgupta and Gupta (2003), there for the projection of a uniform unit vector.
Result: chi-square-lower-tail -/
theorem measureReal_norm_sq_le_mul_card_le_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hβ0 : 0 < β) (hβ : β ≤ 1) :
    μ.real {ω | ‖WithLp.toLp 2 (g ω)‖ ^ 2 ≤ β * Fintype.card n} ≤
      rexp (Fintype.card n / 2 * (1 - β + Real.log β)) := by
  have hs : 0 ≤ (β⁻¹ - 1) / 2 := by
    have := one_le_inv_iff₀.2 ⟨hβ0, hβ⟩; linarith
  refine (measureReal_norm_sq_le_le_exp_mul_rpow hg _ hs).trans (le_of_eq ?_)
  rw [show 1 + 2 * ((β⁻¹ - 1) / 2) = β⁻¹ by ring, exp_mul_inv_rpow _ _ hβ0]
  congr 1
  field_simp

/-! ### Lower tails and the small ball -/

/-- A standard Gaussian vector of positive dimension is almost surely nonzero:
$\mathbb{P}(\|\mathbf{g}\|^2 \le 0) = 0$. -/
private theorem measureReal_norm_sq_le_zero_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hn : 0 < Fintype.card n) :
    μ.real {ω | ‖WithLp.toLp 2 (g ω)‖ ^ 2 ≤ 0} = 0 := by
  have : IsProbabilityMeasure μ := hg.isProbabilityMeasure_iff.2 inferInstance
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp hn
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hsub : {ω | ‖WithLp.toLp 2 (g ω)‖ ^ 2 ≤ 0} ⊆ {ω | g ω i = 0} := by
    intro ω (hω : ‖WithLp.toLp 2 (g ω)‖ ^ 2 ≤ 0)
    have h0 : WithLp.toLp 2 (g ω) = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
      (le_antisymm hω (sq_nonneg _)))
    change g ω i = 0
    rw [← WithLp.ofLp_toLp 2 (g ω), h0]
    rfl
  refine le_antisymm ((measureReal_mono hsub).trans (le_of_eq ?_)) measureReal_nonneg
  rw [(hg.eval i).measureReal_eq (p := fun x => x = 0) (measurableSet_singleton 0)]
  rw [measureReal_def, Set.ofPred_eq_eq_singleton, measure_singleton, ENNReal.toReal_zero]

/-- **The lower tail of $\chi^2$** (Laurent and Massart 2000, Lemma 1): for a standard Gaussian
vector $\mathbf{g}$ of dimension $d = \lvert n \rvert \ge 1$ and $t \ge 0$,
$\mathbb{P}(\|\mathbf{g}\|^2 \le d - 2\sqrt{d t}) \le e^{-t}$. The dimension must be positive: for
$d = 0$ the event is everything. A corollary of
`NLAlib.measureReal_norm_sq_le_mul_card_le_of_hasLaw_gaussianVector` at
$\beta = 1 - 2\sqrt{t/d}$.
Result: laurent-massart -/
theorem measureReal_norm_sq_le_of_hasLaw_gaussianVector (hg : HasLaw g (gaussianVector n) μ)
    (hn : 0 < Fintype.card n) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ‖WithLp.toLp 2 (g ω)‖ ^ 2 ≤ Fintype.card n - 2 * √(Fintype.card n * t)} ≤
      rexp (-t) := by
  have : IsProbabilityMeasure μ := hg.isProbabilityMeasure_iff.2 inferInstance
  have hN : (0 : ℝ) < Fintype.card n := by exact_mod_cast hn
  set N : ℝ := (Fintype.card n : ℝ)
  set u := 2 * √(t / N) with hu_def
  have hu0 : 0 ≤ u := by positivity
  have hu2 : u ^ 2 = 4 * (t / N) := by
    rw [hu_def, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  have ht' : t = N * u ^ 2 / 4 := by rw [hu2]; field_simp
  have hc : N - 2 * √(N * t) = (1 - u) * N := by
    rw [show N * t = N ^ 2 * (t / N) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hN.le, hu_def]
    ring
  rw [hc]
  rcases lt_or_ge u 1 with hu1 | hu1
  · refine (measureReal_norm_sq_le_mul_card_le_of_hasLaw_gaussianVector hg (β := 1 - u)
      (by linarith) (by linarith)).trans (Real.exp_le_exp.2 ?_)
    have h := mul_le_mul_of_nonneg_left (Real.log_one_sub_le_quadratic hu0 hu1)
      (by positivity : (0 : ℝ) ≤ N / 2)
    rw [ht']
    nlinarith
  · refine (measureReal_mono (s₂ := {ω | ‖WithLp.toLp 2 (g ω)‖ ^ 2 ≤ 0})
      (fun ω hω => ?_) (measure_ne_top _ _)).trans ?_
    · simp only [Set.mem_ofPred_eq] at hω ⊢
      exact hω.trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) hN.le)
    · rw [measureReal_norm_sq_le_zero_of_hasLaw_gaussianVector hg hn]
      positivity

/-- $\int_0^\infty y^{d-1} e^{-y^2/2} \mathbf{1}[y \le r]\,dy \le r^d / d$: the radial
integral of the small ball, after dropping $e^{-y^2/2} \le 1$. -/
private theorem integral_Ioi_pow_mul_exp_mul_indicator_le {d : ℕ} (hd : 1 ≤ d) {r : ℝ}
    (hr : 0 ≤ r) :
    ∫ y in Set.Ioi (0 : ℝ), y ^ (d - 1) * (rexp (-y ^ 2 / 2) * (Set.Iic r).indicator 1 y) ≤
      r ^ d / d := by
  have e : (fun y : ℝ => y ^ (d - 1) * (rexp (-y ^ 2 / 2) * (Set.Iic r).indicator 1 y)) =
      (Set.Iic r).indicator fun y => y ^ (d - 1) * rexp (-y ^ 2 / 2) := by
    funext y
    by_cases hy : y ∈ Set.Iic r <;> simp [hy]
  rw [e, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic]
  have hcont : Continuous fun y : ℝ => y ^ (d - 1) := continuous_pow _
  calc ∫ y in Set.Ioc 0 r, y ^ (d - 1) * rexp (-y ^ 2 / 2)
      ≤ ∫ y in Set.Ioc 0 r, y ^ (d - 1) := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun y (hy : 0 < y ∧ y ≤ r) => ?_
        · exact ((hcont.mul (by fun_prop)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
        · exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
        · refine mul_le_of_le_one_right (pow_nonneg hy.1.le _) ?_
          rw [Real.exp_le_one_iff]
          have := sq_nonneg y
          linarith
    _ = r ^ d / d := by
        rw [← intervalIntegral.integral_of_le hr, integral_pow, Nat.sub_add_cancel hd,
          zero_pow (by omega), sub_zero, Nat.cast_sub hd, Nat.cast_one, sub_add_cancel]

/-- **Small-ball bound for $\chi^2$, exact density**: for a standard Gaussian vector $\mathbf{g}$
of dimension $d = \lvert n \rvert$ and $u \ge 0$,
$$\mathbb{P}(\|\mathbf{g}\|^2 \le u) \le \frac{(u/2)^{d/2}}{\Gamma(d/2 + 1)}\,,$$
from the $\chi^2_d$ density (`NLAlib.integral_comp_norm_of_hasLaw_gaussianVector`) after dropping
$e^{-u/2} \le 1$; for $d = 0$ both sides are $1$. It dominates the Chernoff small ball
`NLAlib.measureReal_norm_sq_le_le_rpow_of_hasLaw_gaussianVector` by
$\Gamma(x + 1) \ge (x/e)^x$ (`Real.rpow_mul_exp_neg_le_Gamma_add_one`), which is proved from it
(CONTRIBUTING §5.2, rule 6); asymptotically it is smaller by the Stirling factor
$\sqrt{\pi d}$.
Result: chi-square-small-ball -/
theorem measureReal_norm_sq_le_le_rpow_div_Gamma_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | ‖WithLp.toLp 2 (g ω)‖ ^ 2 ≤ u} ≤
      (u / 2) ^ (Fintype.card n / 2 : ℝ) / Real.Gamma (Fintype.card n / 2 + 1) := by
  have : IsProbabilityMeasure μ := hg.isProbabilityMeasure_iff.2 inferInstance
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hd | hd
  · rw [hd, Nat.cast_zero, zero_div, Real.rpow_zero, zero_add, Real.Gamma_one, div_one]
    exact measureReal_le_one
  set d := Fintype.card n with hd_def
  have hset : MeasurableSet {x : n → ℝ | ‖WithLp.toLp 2 x‖ ^ 2 ≤ u} :=
    measurableSet_le (by fun_prop) measurable_const
  have hind : (fun x : n → ℝ => (Set.Iic √u).indicator (1 : ℝ → ℝ) ‖WithLp.toLp 2 x‖) =
      {x : n → ℝ | ‖WithLp.toLp 2 x‖ ^ 2 ≤ u}.indicator 1 := by
    funext x
    have hiff : ‖WithLp.toLp 2 x‖ ≤ √u ↔ ‖WithLp.toLp 2 x‖ ^ 2 ≤ u := by
      rw [Real.le_sqrt (norm_nonneg _) hu]
    by_cases hx : ‖WithLp.toLp 2 x‖ ^ 2 ≤ u
    · rw [Set.indicator_of_mem (show _ ∈ Set.Iic √u from hiff.2 hx),
        Set.indicator_of_mem (show x ∈ {x : n → ℝ | ‖WithLp.toLp 2 x‖ ^ 2 ≤ u} from hx)]
      rfl
    · rw [Set.indicator_of_notMem (show _ ∉ Set.Iic √u from fun h => hx (hiff.1 h)),
        Set.indicator_of_notMem (show x ∉ {x : n → ℝ | ‖WithLp.toLp 2 x‖ ^ 2 ≤ u} from hx)]
  have hP : μ.real {ω | ‖WithLp.toLp 2 (g ω)‖ ^ 2 ≤ u} =
      ∫ x, (Set.Iic √u).indicator (1 : ℝ → ℝ) ‖WithLp.toLp 2 (id x : n → ℝ)‖
        ∂(gaussianVector n) := by
    rw [hg.measureReal_eq (p := fun x => ‖WithLp.toLp 2 x‖ ^ 2 ≤ u) hset]
    simp only [id, hind]
    rw [integral_indicator_one hset]
  rw [hP, integral_comp_norm_of_hasLaw_gaussianVector (g := id) (φ := (Set.Iic √u).indicator 1)
    HasLaw.id hd (measurable_const.indicator measurableSet_Iic)]
  have hG : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hd1 : (0 : ℝ) < d := by exact_mod_cast hd
  refine (div_le_div_of_nonneg_right (integral_Ioi_pow_mul_exp_mul_indicator_le hd
    (Real.sqrt_nonneg u)) (by positivity)).trans (le_of_eq ?_)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu, Real.div_rpow hu (by norm_num),
    Real.Gamma_add_one (by positivity), Real.rpow_sub (by norm_num), Real.rpow_one,
    show (1 / 2 : ℝ) * d = d / 2 by ring]
  simp only [← hd_def]
  field_simp

/-- **Small-ball bound for $\chi^2$**: for a standard Gaussian vector $\mathbf{g}$ of dimension
$d = \lvert n \rvert$ and $u \ge 0$, $\mathbb{P}(\|\mathbf{g}\|^2 \le u) \le (e u / d)^{d/2}$.
A corollary of the exact small ball
`NLAlib.measureReal_norm_sq_le_le_rpow_div_Gamma_of_hasLaw_gaussianVector` by
$\Gamma(x + 1) \ge (x/e)^x$ at $x = d/2$; it is also Chernoff's bound at $\beta = u/d$, after
dropping the factor $e^{-u/2} \le 1$. It decays like $u^{d/2}$ as $u \to 0$, which
`NLAlib.measureReal_norm_sq_le_of_hasLaw_gaussianVector` (better for thresholds near $d$) does not
see; it is at least $1$ for $u \ge d$ and for $d = 0$.
Port of `NLAlib.measureReal_sum_sq_le_le_gaussianVector`, there for `Fin d`, $d \ge 1$ and
$u \le d$. -/
theorem measureReal_norm_sq_le_le_rpow_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | ‖WithLp.toLp 2 (g ω)‖ ^ 2 ≤ u} ≤
      (rexp 1 * u / Fintype.card n) ^ (Fintype.card n / 2 : ℝ) := by
  have : IsProbabilityMeasure μ := hg.isProbabilityMeasure_iff.2 inferInstance
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hd | hd
  · rw [hd, Nat.cast_zero, zero_div, Real.rpow_zero]
    exact measureReal_le_one
  refine (measureReal_norm_sq_le_le_rpow_div_Gamma_of_hasLaw_gaussianVector hg hu).trans ?_
  set x : ℝ := (Fintype.card n : ℝ) / 2
  have hx : 0 < x := by positivity
  have hΓ := Real.rpow_mul_exp_neg_le_Gamma_add_one hx.le
  have hpos : 0 < x ^ x * rexp (-x) := by positivity
  refine (div_le_div_of_nonneg_left (by positivity) hpos hΓ).trans (le_of_eq ?_)
  rw [show rexp 1 * u / Fintype.card n = rexp 1 * (u / 2) / x by
      simp only [x]; field_simp,
    Real.div_rpow (by positivity) hx.le, Real.mul_rpow (by positivity) (by positivity),
    Real.exp_one_rpow, Real.exp_neg]
  field_simp
/-! ### The relative deviation -/

/-- **Relative deviation of $\chi^2$**: for a standard Gaussian vector $\mathbf{g}$ of dimension
$d = \lvert n \rvert$ and $\varepsilon \ge 0$,
$$\mathbb{P}\bigl(\varepsilon \le \lvert \|\mathbf{g}\|^2/d - 1 \rvert\bigr)
\le 2 e^{-d(\varepsilon^2/4 - \varepsilon^3/6)} \,.$$
The case of standard Gaussian coordinates (independent, proxy $1$, moments $1$ and $3$) of
`NLAlib.measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun`. The bound is at least $2$
for $\varepsilon \ge 3/2$ and for empty $n$. The exponent of Dasgupta and Gupta (2003);
[Woodruff2014, Lemma 18] has Laurent and Massart's $\varepsilon^2 d / 16$ in its place. -/
theorem measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |‖WithLp.toLp 2 (g ω)‖ ^ 2 / Fintype.card n - 1|} ≤
      2 * rexp (-(Fintype.card n * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
  have hY : ∀ i, HasLaw (fun ω => g ω i) (gaussianReal 0 1) μ := hg.eval
  have h := measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun hg.iIndepFun_eval
    (fun i => hasSubgaussianMGF_of_hasLaw_gaussianReal (hY i))
    (fun i => by rw [integral_sq_of_hasLaw_gaussianReal (hY i), NNReal.coe_one])
    (fun i => by rw [integral_pow_four_of_hasLaw_gaussianReal (hY i)]; norm_num) hε
  simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply] using h

end NLAlib
