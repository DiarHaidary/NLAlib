/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.QuadraticForm.Moments
public import NLAlib.Probability.Distributions.GaussianConcentration
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Gaussian moments and lower coordinate maxima

Fourth-order Wick identities and moments of linear images of standard Gaussian vectors.
The maximum absolute coordinate, written as the Pi norm, also has a lower expected value
of order $\sqrt{\log(d+1)}$ in dimension $d$. Its coordinates are independent under
`gaussianVector n`; no independence assumption is needed in addition to the stated law.

## Main results

* `NLAlib.integral_dotProduct_mul_four_of_hasLaw_gaussianVector`.
* `NLAlib.integral_norm_mulVec_pow_four_of_hasLaw_gaussianVector`.
* `NLAlib.one_sub_exp_le_measureReal_norm_ge_of_hasLaw_gaussianVector`: the product lower tail.
* `NLAlib.mul_sqrt_log_le_integral_norm_of_hasLaw_gaussianVector`: the lower expected maximum
  absolute coordinate (Pi norm), including dimension zero.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {n m : Type*} [Fintype n] [Fintype m] {g : Ω → n → ℝ}

private theorem memLp_linear (hg : HasLaw g (gaussianVector n) μ) (u : n → ℝ) :
    MemLp (fun ω => u ⬝ᵥ g ω) 4 μ :=
  ((hasLaw_dotProduct_of_hasLaw_gaussianVector hg u).memLp_comp_iff
    (f := id) aestronglyMeasurable_id).2 (memLp_id_gaussianReal' 4 (by norm_num))

private theorem memLp_pair (hg : HasLaw g (gaussianVector n) μ) (u v : n → ℝ) :
    MemLp (fun ω => (u ⬝ᵥ g ω) * (v ⬝ᵥ g ω)) 2 μ := by
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
      ← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]⟩
  exact (memLp_linear hg v).mul' (memLp_linear hg u)

/-- Products of four Gaussian linear forms are integrable, including degenerate forms. -/
theorem integrable_dotProduct_mul_four_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (u v w z : n → ℝ) :
    Integrable (fun ω => (u ⬝ᵥ g ω) * (v ⬝ᵥ g ω) *
      (w ⬝ᵥ g ω) * (z ⬝ᵥ g ω)) μ := by
  exact ((memLp_pair hg u v).integrable_mul (memLp_pair hg w z)).congr
    (ae_of_all _ fun ω => by dsimp only [Pi.mul_apply]; ring)

private theorem integral_linear_four (hg : HasLaw g (gaussianVector n) μ) (u : n → ℝ) :
    ∫ ω, (u ⬝ᵥ g ω) ^ 4 ∂μ = 3 * (u ⬝ᵥ u) ^ 2 := by
  rw [integral_pow_four_of_hasLaw_gaussianReal
    (hasLaw_dotProduct_of_hasLaw_gaussianVector hg u), NNReal.coe_pow, coe_nnnorm,
    EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]

private theorem integrable_linear_four (hg : HasLaw g (gaussianVector n) μ) (u : n → ℝ) :
    Integrable (fun ω => (u ⬝ᵥ g ω) ^ 4) μ := by
  exact (integrable_dotProduct_mul_four_of_hasLaw_gaussianVector hg u u u u).congr
    (ae_of_all _ fun ω => by dsimp only [Pi.mul_apply]; ring)

private theorem integral_pair_sq (hg : HasLaw g (gaussianVector n) μ) (u v : n → ℝ) :
    ∫ ω, (u ⬝ᵥ g ω) ^ 2 * (v ⬝ᵥ g ω) ^ 2 ∂μ =
      (u ⬝ᵥ u) * (v ⬝ᵥ v) + 2 * (u ⬝ᵥ v) ^ 2 := by
  have he : ∀ ω, 12 * ((u ⬝ᵥ g ω) ^ 2 * (v ⬝ᵥ g ω) ^ 2) =
      ((u + v) ⬝ᵥ g ω) ^ 4 + ((u - v) ⬝ᵥ g ω) ^ 4 -
        2 * (u ⬝ᵥ g ω) ^ 4 - 2 * (v ⬝ᵥ g ω) ^ 4 := by
    intro ω
    rw [add_dotProduct, sub_dotProduct]
    ring
  have hi := congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) (funext he)
  simp only [integral_const_mul] at hi
  have h1 := integral_sub ((integrable_linear_four hg (u + v)).add
    (integrable_linear_four hg (u - v)) |>.sub ((integrable_linear_four hg u).const_mul 2))
    ((integrable_linear_four hg v).const_mul 2)
  have h2 := integral_sub
    ((integrable_linear_four hg (u + v)).add (integrable_linear_four hg (u - v)))
    ((integrable_linear_four hg u).const_mul 2)
  have h3 := integral_add (integrable_linear_four hg (u + v)) (integrable_linear_four hg (u - v))
  simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 h3
  rw [h1, h2, h3] at hi
  simp only [integral_const_mul] at hi
  rw [integral_linear_four hg (u + v), integral_linear_four hg (u - v),
    integral_linear_four hg u, integral_linear_four hg v] at hi
  simp only [add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub, dotProduct_comm v u] at hi
  linarith

private theorem integrable_pair_sq (hg : HasLaw g (gaussianVector n) μ) (u v : n → ℝ) :
    Integrable (fun ω => (u ⬝ᵥ g ω) ^ 2 * (v ⬝ᵥ g ω) ^ 2) μ := by
  exact (integrable_dotProduct_mul_four_of_hasLaw_gaussianVector hg u u v v).congr
    (ae_of_all _ fun ω => by ring)

/-- **Fourth-order Wick formula.** Four linear forms of a standard Gaussian vector have
fourth mixed moment equal to the sum of the three covariance pairings:
$$\begin{aligned}
\mathbb{E}[\langle\mathbf{u},\mathbf{g}\rangle
\langle\mathbf{v},\mathbf{g}\rangle\langle\mathbf{w},\mathbf{g}\rangle
\langle\mathbf{z},\mathbf{g}\rangle]
&= \langle\mathbf{u},\mathbf{v}\rangle\langle\mathbf{w},\mathbf{z}\rangle \\
&\quad+\langle\mathbf{u},\mathbf{w}\rangle\langle\mathbf{v},\mathbf{z}\rangle
+\langle\mathbf{u},\mathbf{z}\rangle\langle\mathbf{v},\mathbf{w}\rangle\,.
\end{aligned}$$
[Isserlis1918, fourth-order formula]; here linear forms with possibly singular covariance.
Result: gaussian-fourth-moment -/
theorem integral_dotProduct_mul_four_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (u v w z : n → ℝ) :
    ∫ ω, (u ⬝ᵥ g ω) * (v ⬝ᵥ g ω) * (w ⬝ᵥ g ω) * (z ⬝ᵥ g ω) ∂μ =
      (u ⬝ᵥ v) * (w ⬝ᵥ z) + (u ⬝ᵥ w) * (v ⬝ᵥ z) +
        (u ⬝ᵥ z) * (v ⬝ᵥ w) := by
  let F (a b : n → ℝ) : Ω → ℝ := fun ω => (a ⬝ᵥ g ω) ^ 2 * (b ⬝ᵥ g ω) ^ 2
  have hF (a b : n → ℝ) : Integrable (F a b) μ := integrable_pair_sq hg a b
  have he : (fun ω => 16 * ((u ⬝ᵥ g ω) * (v ⬝ᵥ g ω) *
      (w ⬝ᵥ g ω) * (z ⬝ᵥ g ω))) =
      F (u + v) (w + z) - F (u - v) (w + z) -
        F (u + v) (w - z) + F (u - v) (w - z) := by
    funext ω
    dsimp only [F, Pi.sub_apply, Pi.add_apply]
    simp only [add_dotProduct, sub_dotProduct]
    ring
  have hi := congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) he
  rw [integral_const_mul] at hi
  have h1 := integral_add
    (((hF (u + v) (w + z)).sub (hF (u - v) (w + z))).sub (hF (u + v) (w - z)))
    (hF (u - v) (w - z))
  have h2 := integral_sub ((hF (u + v) (w + z)).sub (hF (u - v) (w + z)))
    (hF (u + v) (w - z))
  have h3 := integral_sub (hF (u + v) (w + z)) (hF (u - v) (w + z))
  simp only [Pi.sub_apply, Pi.add_apply] at hi h1 h2 h3
  rw [h1, h2, h3] at hi
  dsimp only [F] at hi
  rw [integral_pair_sq hg, integral_pair_sq hg, integral_pair_sq hg, integral_pair_sq hg] at hi
  simp only [add_dotProduct, sub_dotProduct, dotProduct_add,
    dotProduct_sub] at hi
  simp only [dotProduct_comm v u, dotProduct_comm z w] at hi
  linarith

private theorem memLp_gaussian_coordinate (hg : HasLaw g (gaussianVector n) μ) (i : n) :
    MemLp (fun ω => g ω i) 4 μ :=
  ((hg.eval i).memLp_comp_iff (f := id) aestronglyMeasurable_id).2
    (memLp_id_gaussianReal' 4 (by norm_num))

/-- The fourth power of the Euclidean norm of a Gaussian linear image is integrable. -/
theorem integrable_norm_mulVec_pow_four_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (A : Matrix m n ℝ) :
    Integrable (fun ω => ‖WithLp.toLp 2 (A *ᵥ g ω)‖ ^ 4) μ := by
  have hq := memLp_quadForm (memLp_gaussian_coordinate hg) (Aᴴ * A)
  exact (hq.integrable_mul hq).congr (ae_of_all _ fun ω => by
    dsimp only [Pi.mul_apply]
    rw [quadForm_conjTranspose_mul_self]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    ring)

/-- **The fourth moment of a Gaussian linear image** is
$\mathbb{E}\|\mathbf{A}\mathbf{g}\|^4 =
\|\mathbf{A}\|_{\mathsf{F}}^4 + 2\|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\mathsf{F}}^2$.
[Isserlis1918, fourth-order formula]; the norm contraction of that identity. -/
theorem integral_norm_mulVec_pow_four_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (A : Matrix m n ℝ) :
    ∫ ω, ‖WithLp.toLp 2 (A *ᵥ g ω)‖ ^ 4 ∂μ =
      frobNorm A ^ 4 + 2 * frobNorm (Aᴴ * A) ^ 2 := by
  classical
  have : IsProbabilityMeasure μ := hg.isProbabilityMeasure
  have hq := memLp_quadForm (memLp_gaussian_coordinate hg) (Aᴴ * A)
  have hmean := (isIsotropic_of_hasLaw_gaussianVector hg).integral_quadForm (Aᴴ * A)
  have hvar := variance_quadForm_of_hasLaw_gaussianVector hg
    (Matrix.isHermitian_conjTranspose_mul_self A)
  rw [variance_eq_sub hq] at hvar
  simp only [Pi.pow_apply] at hvar
  rw [hmean] at hvar
  have ht : (Aᴴ * A).trace = frobNorm A ^ 2 := by
    simpa only [RCLike.re_to_real] using (frobNorm_sq_eq_re_trace A).symm
  have he : (fun ω => quadForm (Aᴴ * A) (g ω) ^ 2) =
      (fun ω => ‖WithLp.toLp 2 (A *ᵥ g ω)‖ ^ 4) := by
    funext ω
    rw [quadForm_conjTranspose_mul_self]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    ring
  rw [he, ht] at hvar
  nlinarith [hvar]

/-! ### Lower coordinate maxima -/

/-- The product-law lower tail for the Pi norm of an independent standard Gaussian vector. -/
private theorem one_sub_exp_le_measureReal_norm_ge_gaussianVector (t : ℝ) :
    1 - Real.exp (-(Fintype.card n : ℝ) *
      (gaussianReal 0 1).real {x : ℝ | t ≤ |x|}) ≤ (gaussianVector n).real {g | t ≤ ‖g‖} := by
  classical
  by_cases ht : t ≤ 0
  · have he : {g : n → ℝ | t ≤ ‖g‖} = Set.univ := by
      ext g
      simp [ht.trans (norm_nonneg g)]
    rw [he, probReal_univ]
    linarith [Real.exp_pos (-(Fintype.card n : ℝ) *
      (gaussianReal 0 1).real {x : ℝ | t ≤ |x|})]
  let q := (gaussianReal 0 1).real {x : ℝ | t ≤ |x|}
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := by
    have h := measureReal_mono (μ := gaussianReal 0 1) (Set.subset_univ {x : ℝ | t ≤ |x|})
    simpa only [probReal_univ] using h
  have hs : (gaussianReal 0 1).real {x : ℝ | |x| < t} = 1 - q := by
    have he : {x : ℝ | |x| < t} = {x : ℝ | t ≤ |x|}ᶜ := by ext x; simp
    rw [he, measureReal_compl (measurableSet_le measurable_const measurable_abs), probReal_univ]
  have hprod : (gaussianVector n).real {g | ∀ i, |g i| < t} = (1 - q) ^ Fintype.card n := by
    have he : {g : n → ℝ | ∀ i, |g i| < t} = Set.univ.pi (fun _ => {x : ℝ | |x| < t}) := by
      ext g
      simp
    rw [he, Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
    change (∏ _i : n, (gaussianReal 0 1).real {x : ℝ | |x| < t}) = _
    simp only [hs, Finset.prod_const, Finset.card_univ]
  have hbad : (gaussianVector n).real {g | ‖g‖ < t} ≤ (1 - q) ^ Fintype.card n := by
    rw [← hprod]
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro g hg i
    exact (norm_le_pi_norm g i).trans_lt hg
  have hcomp : (gaussianVector n).real {g | t ≤ ‖g‖} =
      1 - (gaussianVector n).real {g | ‖g‖ < t} := by
    have he : {g : n → ℝ | t ≤ ‖g‖} = {g : n → ℝ | ‖g‖ < t}ᶜ := by ext g; simp
    rw [he, measureReal_compl (measurableSet_lt measurable_norm measurable_const), probReal_univ]
  have hpow : (1 - q) ^ Fintype.card n ≤ Real.exp (-(Fintype.card n : ℝ) * q) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - q) (Real.one_sub_le_exp_neg q)
      (Fintype.card n)
    simpa only [← Real.exp_nat_mul, mul_neg, neg_mul] using h
  rw [hcomp]
  dsimp [q] at hpow hbad
  linarith

/-- For independent standard Gaussian coordinates, the maximum absolute coordinate (Pi norm)
has lower tail $1-\exp(-d\,\mathbb{P}[t\le|Z|])$, where $Z$ is a scalar standard Gaussian.
All thresholds and finite index types, including empty ones, are allowed.
Port of `NLAlib.one_sub_exp_gaussian_tail_le_measure_norm_ge`. -/
theorem one_sub_exp_le_measureReal_norm_ge_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (t : ℝ) :
    1 - Real.exp (-(Fintype.card n : ℝ) *
      (gaussianReal 0 1).real {x : ℝ | t ≤ |x|}) ≤ μ.real {ω | t ≤ ‖g ω‖} := by
  rw [hg.measureReal_eq (p := fun x => t ≤ ‖x‖)
    (measurableSet_le measurable_const measurable_norm)]
  exact one_sub_exp_le_measureReal_norm_ge_gaussianVector t

/-- A positive factor for lower expected Gaussian coordinate maxima.
Its value is <!-- value gaussianMaximumLowerConstant -->$1-\exp(-e^{-1}/(2\sqrt{2\pi}))$.
Port of the backend's `gaussianMaximumLowerConstant`. -/
noncomputable irreducible_def gaussianMaximumLowerConstant : ℝ :=
  1 - Real.exp (-(Real.exp (-1) / Real.sqrt (2 * Real.pi)) / 2)

/-- The lower Gaussian maximum factor is strictly positive.
Port of `NLAlib.gaussianMaximumLowerConstant_pos`. -/
theorem gaussianMaximumLowerConstant_pos : 0 < gaussianMaximumLowerConstant := by
  rw [gaussianMaximumLowerConstant_def]
  have hc : 0 < Real.exp (-1) / Real.sqrt (2 * Real.pi) := by positivity
  have h := Real.exp_lt_one_iff.mpr
    (show -(Real.exp (-1) / Real.sqrt (2 * Real.pi)) / 2 < 0 by linarith)
  linarith

/-- The expected maximum absolute coordinate (Pi norm) of an independent standard Gaussian
vector is at least `gaussianMaximumLowerConstant` times $\sqrt{\log(d+1)}$.
Its factor is <!-- value gaussianMaximumLowerConstant -->$1-\exp(-e^{-1}/(2\sqrt{2\pi}))$.
The integrability companion is `hg.hasGaussianLaw.integrable.norm`; the empty index type
is included.
Port of `NLAlib.gaussianMaximumLowerConstant_mul_sqrt_log_le_integral_norm_gaussianVector`. -/
theorem mul_sqrt_log_le_integral_norm_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) :
    gaussianMaximumLowerConstant * Real.sqrt (Real.log ((Fintype.card n : ℝ) + 1)) ≤
      ∫ ω, ‖g ω‖ ∂μ := by
  rcases eq_or_ne (Fintype.card n) 0 with hd | hd
  · simp only [hd, Nat.cast_zero, zero_add, Real.log_one, Real.sqrt_zero, mul_zero]
    exact integral_nonneg fun ω => norm_nonneg _
  have hd1 : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  let t := Real.sqrt (Real.log ((Fintype.card n : ℝ) + 1))
  let c := Real.exp (-1) / Real.sqrt (2 * Real.pi)
  let q := (gaussianReal 0 1).real {x : ℝ | t ≤ |x|}
  have hc : 0 < c := by dsimp [c]; positivity
  have hq0 : 0 ≤ q := measureReal_nonneg
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hlog : 0 ≤ Real.log ((Fintype.card n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hscalar : c / ((Fintype.card n : ℝ) + 1) ≤ q := by
    have h := mul_exp_neg_sq_le_measureReal_abs_ge_of_hasLaw_gaussianReal
      (HasLaw.id (μ := gaussianReal 0 1)) ht
    have he : Real.exp (-t ^ 2) = ((Fintype.card n : ℝ) + 1)⁻¹ := by
      dsimp [t]
      rw [Real.sq_sqrt hlog, Real.exp_neg, Real.exp_log (by linarith)]
    rw [gaussianLowerTailConstant_def, he] at h
    simpa only [c, q, div_eq_mul_inv, id_eq] using h
  have hdq : c / 2 ≤ (Fintype.card n : ℝ) * q := by
    have h := (div_le_iff₀ (by linarith : 0 < (Fintype.card n : ℝ) + 1)).mp hscalar
    have hmul := mul_nonneg hq0 (sub_nonneg.mpr hd1)
    nlinarith
  have htail : gaussianMaximumLowerConstant ≤ μ.real {ω | t ≤ ‖g ω‖} := by
    have h := one_sub_exp_le_measureReal_norm_ge_of_hasLaw_gaussianVector hg t
    have he := Real.exp_le_exp.mpr (show -(Fintype.card n : ℝ) * q ≤ -c / 2 by nlinarith)
    rw [gaussianMaximumLowerConstant_def]
    change 1 - Real.exp (-c / 2) ≤ _
    change 1 - Real.exp (-(Fintype.card n : ℝ) * q) ≤ _ at h
    linarith
  have hmean := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => norm_nonneg (g ω)) hg.hasGaussianLaw.integrable.norm t
  calc _ ≤ t * μ.real {ω | t ≤ ‖g ω‖} := by
        change gaussianMaximumLowerConstant * t ≤ _
        nlinarith
    _ ≤ _ := hmean

end NLAlib
