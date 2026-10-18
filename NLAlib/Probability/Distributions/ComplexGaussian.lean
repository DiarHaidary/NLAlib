/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import NLAlib.Probability.Distributions.Gaussian

/-!
# Standard complex Gaussian variables and vectors

`NLAlib.complexGaussianMeasure` is the law of $(g_1 + i g_2)/\sqrt{2}$ for independent standard
real Gaussians $g_1, g_2$: the product of two $\mathcal{N}(0, 1/2)$ laws, read in $\mathbb{C}$
through `Complex.measurableEquivRealProd`. `NLAlib.complexGaussianVector n` is the law of a vector
of independent such coordinates, an `abbrev` for the product, as `NLAlib.gaussianVector n` is in
the real case (the parallel definition of `docs/design/Probability-P2.md` §7 Q1).

A standard complex Gaussian $Z$ has $\mathbb{E} Z = 0$, $\mathbb{E}\lvert Z \rvert^2 = 1$,
pseudo-variance $\mathbb{E} Z^2 = 0$ and $\mathbb{E}\lvert Z \rvert^4 = 2$: the moment parameters
$s = 0$, $m_4 = 2$ of `NLAlib.integral_norm_quadForm_sub_trace_sq`.

Mathlib's `ProbabilityTheory.stdGaussian ℂ`, the standard Gaussian of $\mathbb{C}$ as a real inner
product space, is the law of $\sqrt{2}\,Z$; the bridge is not proved here
(`docs/design/Mathlib-deviations.md` entry 20).

## Main definitions

* `NLAlib.complexGaussianMeasure`, `NLAlib.complexGaussianVector n`.

## Main results

* `NLAlib.integral_complexGaussianMeasure`: the integral as one over two real Gaussians.
* `NLAlib.memLp_of_hasLaw_complexGaussianMeasure`,
  `NLAlib.integral_of_hasLaw_complexGaussianMeasure`,
  `NLAlib.integral_norm_sq_of_hasLaw_complexGaussianMeasure`,
  `NLAlib.integral_sq_of_hasLaw_complexGaussianMeasure`,
  `NLAlib.integral_norm_pow_four_of_hasLaw_complexGaussianMeasure`: the moments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]

/-- The **standard complex Gaussian** law on $\mathbb{C}$: the law of $X + iY$ for independent
$X, Y \sim \mathcal{N}(0, 1/2)$, equivalently of $(g_1 + i g_2)/\sqrt{2}$ for independent standard
real Gaussians. [Epperly2023, Complex-Valued Test Vectors]. -/
noncomputable def complexGaussianMeasure : Measure ℂ :=
  ((gaussianReal 0 2⁻¹).prod (gaussianReal 0 2⁻¹)).map measurableEquivRealProd.symm

/-- The standard complex Gaussian law is a probability measure. -/
instance isProbabilityMeasure_complexGaussianMeasure :
    IsProbabilityMeasure complexGaussianMeasure :=
  Measure.isProbabilityMeasure_map measurableEquivRealProd.symm.measurable.aemeasurable

/-- The law of a vector in $\mathbb{C}^n$ with independent standard complex Gaussian
coordinates. -/
noncomputable abbrev complexGaussianVector (n : Type*) [Fintype n] : Measure (n → ℂ) :=
  Measure.pi fun _ : n => complexGaussianMeasure

/-- An integral against the standard complex Gaussian law is one against two independent
$\mathcal{N}(0, 1/2)$ coordinates: $\int f \, d\nu = \mathbb{E} f(X + iY)$. -/
theorem integral_complexGaussianMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) :
    ∫ z, f z ∂complexGaussianMeasure =
      ∫ p, f (p.1 + p.2 * I) ∂((gaussianReal 0 2⁻¹).prod (gaussianReal 0 2⁻¹)) := by
  rw [complexGaussianMeasure, integral_map_equiv]
  congr 1
  funext p
  congr 1
  apply Complex.ext <;> simp [measurableEquivRealProd]

private theorem memLp_fst_ofReal (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ)) p
      ((gaussianReal 0 2⁻¹).prod (gaussianReal 0 2⁻¹)) :=
  ((memLp_id_gaussianReal' p hp).ofReal (K := ℂ)).comp_fst _

private theorem memLp_snd_ofReal (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun q : ℝ × ℝ => ((q.2 : ℝ) : ℂ)) p
      ((gaussianReal 0 2⁻¹).prod (gaussianReal 0 2⁻¹)) :=
  ((memLp_id_gaussianReal' p hp).ofReal (K := ℂ)).comp_snd _

/-- A standard complex Gaussian has moments of every finite order. -/
theorem memLp_of_hasLaw_complexGaussianMeasure {Z : Ω → ℂ}
    (hZ : HasLaw Z complexGaussianMeasure μ) (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp Z p μ := by
  refine (hZ.memLp_comp_iff (f := id) aestronglyMeasurable_id).2 ?_
  rw [complexGaussianMeasure, memLp_map_measure_iff aestronglyMeasurable_id
    measurableEquivRealProd.symm.measurable.aemeasurable]
  have h : (id ∘ ⇑measurableEquivRealProd.symm) =
      fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ) + ((q.2 : ℝ) : ℂ) * I := by
    funext q
    apply Complex.ext <;> simp [measurableEquivRealProd]
  rw [h]
  exact (memLp_fst_ofReal p hp).add ((memLp_snd_ofReal p hp).mul_const I)

/-- The two real coordinates of a standard complex Gaussian. -/
local notation "𝒫" => Measure.prod (gaussianReal 0 2⁻¹) (gaussianReal 0 2⁻¹)

private theorem integrable_pow_gaussianReal (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 2⁻¹) := by
  refine ((memLp_id_gaussianReal' k (by simp)).integrable_norm_pow').mono'
    (by fun_prop) (ae_of_all _ fun x => ?_)
  simp [norm_pow]

private theorem integral_id_half : ∫ x, x ∂(gaussianReal 0 2⁻¹) = 0 :=
  integral_id_gaussianReal

private theorem integral_sq_half : ∫ x, x ^ 2 ∂(gaussianReal 0 2⁻¹) = 2⁻¹ := by
  simpa using integral_sq_of_hasLaw_gaussianReal (HasLaw.id (μ := gaussianReal 0 2⁻¹))

private theorem integral_pow_four_half : ∫ x, x ^ 4 ∂(gaussianReal 0 2⁻¹) = 3 / 4 := by
  have h := integral_pow_four_of_hasLaw_gaussianReal (HasLaw.id (μ := gaussianReal 0 2⁻¹))
  simp only [id] at h
  rw [h]
  norm_num

private theorem integral_fst_pow (k : ℕ) :
    ∫ p, p.1 ^ k ∂𝒫 = ∫ x, x ^ k ∂(gaussianReal 0 2⁻¹) := by
  rw [integral_fun_fst (f := fun x : ℝ => x ^ k), probReal_univ, one_smul]

private theorem integral_snd_pow (k : ℕ) :
    ∫ p, p.2 ^ k ∂𝒫 = ∫ x, x ^ k ∂(gaussianReal 0 2⁻¹) := by
  rw [integral_fun_snd (f := fun x : ℝ => x ^ k), probReal_univ, one_smul]

private theorem integral_fst_pow_mul_snd_pow (j k : ℕ) :
    ∫ p, p.1 ^ j * p.2 ^ k ∂𝒫 =
      (∫ x, x ^ j ∂(gaussianReal 0 2⁻¹)) * ∫ x, x ^ k ∂(gaussianReal 0 2⁻¹) :=
  integral_prod_mul (fun x : ℝ => x ^ j) fun x : ℝ => x ^ k

private theorem integrable_fst_pow_mul_snd_pow (j k : ℕ) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ j * p.2 ^ k) 𝒫 :=
  (integrable_pow_gaussianReal j).mul_prod (integrable_pow_gaussianReal k)

private theorem integrable_fst_pow (k : ℕ) : Integrable (fun p : ℝ × ℝ => p.1 ^ k) 𝒫 :=
  (integrable_pow_gaussianReal k).comp_fst _

private theorem integrable_snd_pow (k : ℕ) : Integrable (fun p : ℝ × ℝ => p.2 ^ k) 𝒫 :=
  (integrable_pow_gaussianReal k).comp_snd _

private theorem integral_ofReal_add_ofReal_mul_I {f g : ℝ × ℝ → ℝ} (hf : Integrable f 𝒫)
    (hg : Integrable g 𝒫) :
    ∫ p, (((f p : ℝ) : ℂ) + ((g p : ℝ) : ℂ) * I) ∂𝒫 =
      (((∫ p, f p ∂𝒫) : ℝ) : ℂ) + (((∫ p, g p ∂𝒫) : ℝ) : ℂ) * I := by
  have hf' : Integrable (fun p => ((f p : ℝ) : ℂ)) 𝒫 := hf.ofReal
  have hg' : Integrable (fun p => ((g p : ℝ) : ℂ) * I) 𝒫 := hg.ofReal.mul_const I
  rw [integral_add hf' hg', integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]

/-- A standard complex Gaussian has mean zero. -/
theorem integral_of_hasLaw_complexGaussianMeasure {Z : Ω → ℂ}
    (hZ : HasLaw Z complexGaussianMeasure μ) : ∫ ω, Z ω ∂μ = 0 := by
  rw [hZ.integral_eq, integral_complexGaussianMeasure]
  have h1 := integral_fst_pow 1
  have h2 := integral_snd_pow 1
  simp only [pow_one] at h1 h2
  rw [integral_ofReal_add_ofReal_mul_I (f := fun p => p.1) (g := fun p => p.2)
    (by simpa using integrable_fst_pow 1) (by simpa using integrable_snd_pow 1), h1, h2,
    integral_id_half]
  simp

/-- A standard complex Gaussian has second moment $\mathbb{E}\lvert Z \rvert^2 = 1$. -/
theorem integral_norm_sq_of_hasLaw_complexGaussianMeasure {Z : Ω → ℂ}
    (hZ : HasLaw Z complexGaussianMeasure μ) : ∫ ω, ‖Z ω‖ ^ 2 ∂μ = 1 := by
  have hc := hZ.integral_comp (f := fun z : ℂ => ‖z‖ ^ 2) (by fun_prop)
  simp only [Function.comp_def] at hc
  rw [hc, integral_complexGaussianMeasure]
  simp only [Complex.sq_norm, normSq_add_mul_I]
  rw [integral_add (integrable_fst_pow 2) (integrable_snd_pow 2), integral_fst_pow,
    integral_snd_pow, integral_sq_half]
  norm_num

/-- A standard complex Gaussian has pseudo-variance zero: $\mathbb{E} Z^2 = 0$. -/
theorem integral_sq_of_hasLaw_complexGaussianMeasure {Z : Ω → ℂ}
    (hZ : HasLaw Z complexGaussianMeasure μ) : ∫ ω, Z ω ^ 2 ∂μ = 0 := by
  have hc := hZ.integral_comp (f := fun z : ℂ => z ^ 2) (by fun_prop)
  simp only [Function.comp_def] at hc
  rw [hc, integral_complexGaussianMeasure]
  have h (p : ℝ × ℝ) : ((p.1 : ℂ) + (p.2 : ℂ) * I) ^ 2 =
      (((p.1 ^ 2 * p.2 ^ 0 - p.1 ^ 0 * p.2 ^ 2 : ℝ)) : ℂ) +
        (((2 * (p.1 ^ 1 * p.2 ^ 1) : ℝ)) : ℂ) * I := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  simp only [h]
  rw [integral_ofReal_add_ofReal_mul_I (f := fun p => p.1 ^ 2 * p.2 ^ 0 - p.1 ^ 0 * p.2 ^ 2)
      (g := fun p => 2 * (p.1 ^ 1 * p.2 ^ 1)) ((integrable_fst_pow_mul_snd_pow 2 0).sub
      (integrable_fst_pow_mul_snd_pow 0 2)) ((integrable_fst_pow_mul_snd_pow 1 1).const_mul 2),
    integral_sub (integrable_fst_pow_mul_snd_pow 2 0) (integrable_fst_pow_mul_snd_pow 0 2),
    integral_const_mul, integral_fst_pow_mul_snd_pow, integral_fst_pow_mul_snd_pow,
    integral_fst_pow_mul_snd_pow]
  simp [integral_sq_half]

/-- A standard complex Gaussian has fourth moment $\mathbb{E}\lvert Z \rvert^4 = 2$. -/
theorem integral_norm_pow_four_of_hasLaw_complexGaussianMeasure {Z : Ω → ℂ}
    (hZ : HasLaw Z complexGaussianMeasure μ) : ∫ ω, ‖Z ω‖ ^ 4 ∂μ = 2 := by
  have hc := hZ.integral_comp (f := fun z : ℂ => ‖z‖ ^ 4) (by fun_prop)
  simp only [Function.comp_def] at hc
  rw [hc, integral_complexGaussianMeasure]
  have h (p : ℝ × ℝ) : ‖(p.1 : ℂ) + (p.2 : ℂ) * I‖ ^ 4 =
      p.1 ^ 4 * p.2 ^ 0 + 2 * (p.1 ^ 2 * p.2 ^ 2) + p.1 ^ 0 * p.2 ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.sq_norm, normSq_add_mul_I]
    ring
  simp only [h]
  have h1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 4 * p.2 ^ 0 + 2 * (p.1 ^ 2 * p.2 ^ 2)) 𝒫 :=
    (integrable_fst_pow_mul_snd_pow 4 0).add ((integrable_fst_pow_mul_snd_pow 2 2).const_mul 2)
  rw [integral_add h1 (integrable_fst_pow_mul_snd_pow 0 4),
    integral_add (integrable_fst_pow_mul_snd_pow 4 0)
      ((integrable_fst_pow_mul_snd_pow 2 2).const_mul 2),
    integral_const_mul, integral_fst_pow_mul_snd_pow, integral_fst_pow_mul_snd_pow,
    integral_fst_pow_mul_snd_pow]
  simp only [pow_zero, integral_const, probReal_univ, one_smul, integral_sq_half,
    integral_pow_four_half]
  norm_num

end NLAlib
