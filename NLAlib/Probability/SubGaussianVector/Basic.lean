/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Probability.Distributions.Gaussian
public import NLAlib.Probability.Distributions.Rademacher
public import NLAlib.Probability.SubGaussian.Basic

/-!
# Sub-Gaussian random vectors

`NLAlib.IsSubgaussianVector x c μ` says that every real linear functional
$\operatorname{Re}(\mathbf{u}^{\mathsf{T}}\mathbf{x})$ of the random vector `x : Ω → n → 𝕜` is
sub-Gaussian with proxy $c \|\mathbf{u}\|^2$. Every real-linear functional of $\Bbbk^n$ has this
form, so over $\mathbb{C}$ the real and imaginary parts are constrained alike; over $\mathbb{R}$,
$\operatorname{Re}$ is the identity (`RCLike.re_to_real`). It is the hypothesis of the tails of
$\|\mathbf{x}\|^2$ and of the net argument for random matrices with sub-Gaussian rows.

Standard Gaussian and Rademacher vectors are sub-Gaussian vectors with proxy $1$, so are real
vectors with independent sub-Gaussian coordinates, and linear images of sub-Gaussian vectors are
sub-Gaussian vectors.

## Main definitions

* `NLAlib.IsSubgaussianVector x c μ`.

## Main results

* `NLAlib.IsSubgaussianVector.mulVec`: $\mathbf{A}\mathbf{x}$ has proxy $c \|\mathbf{A}\|_2^2$.
* `NLAlib.IsSubgaussianVector.of_iIndepFun`: independent real sub-Gaussian coordinates.
* `NLAlib.isSubgaussianVector_of_hasLaw_gaussianVector`,
  `NLAlib.isSubgaussianVector_of_hasLaw_rademacherVector`: proxy $1$.
* `ProbabilityTheory.HasLaw.isSubgaussianVector_iff`: the property depends only on the law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {𝕜 : Type*} [RCLike 𝕜] {x : Ω → n → 𝕜} {c : ℝ≥0}

/-- $\mathbf{x}$ is a sub-Gaussian random vector with proxy $c$ under $\mu$: for every
$\mathbf{u} \in \Bbbk^n$ the real linear functional
$\operatorname{Re}(\mathbf{u}^{\mathsf{T}}\mathbf{x}) = \operatorname{Re} \sum_i \mathbf{u}_i
\mathbf{x}_i$ (no conjugation) is sub-Gaussian with proxy $c \|\mathbf{u}\|^2$. -/
structure IsSubgaussianVector (x : Ω → n → 𝕜) (c : ℝ≥0) (μ : Measure Ω) : Prop where
  /-- Every real linear functional $\operatorname{Re}(\mathbf{u}^{\mathsf{T}}\mathbf{x})$ is
  sub-Gaussian with proxy $c \|\mathbf{u}\|^2$. -/
  hasSubgaussianMGF : ∀ u : n → 𝕜,
    HasSubgaussianMGF (fun ω => RCLike.re (u ⬝ᵥ x ω)) (c * ‖WithLp.toLp 2 u‖₊ ^ 2) μ

namespace IsSubgaussianVector

/-- A larger proxy. -/
theorem mono (h : IsSubgaussianVector x c μ) {d : ℝ≥0} (hcd : c ≤ d) :
    IsSubgaussianVector x d μ := by
  refine ⟨fun u => (h.hasSubgaussianMGF u).mono ?_⟩
  gcongr

/-- The property depends only on the almost-everywhere class of the vector. -/
theorem congr {y : Ω → n → 𝕜} (h : IsSubgaussianVector x c μ) (hxy : x =ᵐ[μ] y) :
    IsSubgaussianVector y c μ := by
  refine ⟨fun u => (h.hasSubgaussianMGF u).congr ?_⟩
  filter_upwards [hxy] with ω hω
  rw [hω]

/-- The real part $\operatorname{Re} \mathbf{x}_i$ of each coordinate is sub-Gaussian with
proxy $c$. -/
theorem hasSubgaussianMGF_re_apply (h : IsSubgaussianVector x c μ) (i : n) :
    HasSubgaussianMGF (fun ω => RCLike.re (x ω i)) c μ := by
  classical
  simpa only [single_one_dotProduct, PiLp.toLp_single, PiLp.nnnorm_single, nnnorm_one, one_pow,
    mul_one] using h.hasSubgaussianMGF (Pi.single i 1)

private lemma hasSubgaussianMGF_im_apply (h : IsSubgaussianVector x c μ) (i : n) :
    HasSubgaussianMGF (fun ω => RCLike.im (x ω i)) c μ := by
  classical
  have hu := h.hasSubgaussianMGF (Pi.single i (-RCLike.I))
  simp only [single_dotProduct, PiLp.toLp_single, PiLp.nnnorm_single, nnnorm_neg, neg_mul,
    map_neg, RCLike.I_mul_re, neg_neg] at hu
  refine hu.mono (mul_le_of_le_one_right' (pow_le_one₀ bot_le ?_))
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, RCLike.norm_I]
  split_ifs <;> norm_num

/-- The coordinates of a sub-Gaussian vector have moments of every order. -/
theorem memLp_apply (h : IsSubgaussianVector x c μ) (i : n) (p : ℝ≥0) :
    MemLp (fun ω => x ω i) p μ := by
  refine memLp_re_im_iff.mp ⟨(h.hasSubgaussianMGF_re_apply i).memLp p, ?_⟩
  exact (h.hasSubgaussianMGF_im_apply i).memLp p

/-- A sub-Gaussian vector is almost everywhere measurable. -/
theorem aemeasurable (h : IsSubgaussianVector x c μ) : AEMeasurable x μ :=
  aemeasurable_pi_lambda _ fun i => (h.memLp_apply i 1).aestronglyMeasurable.aemeasurable

/-- A sub-Gaussian vector has mean zero under a probability measure: $\mathbb{E}[\mathbf{x}_i] = 0$
for every coordinate $i$. -/
theorem integral_apply_eq_zero [IsProbabilityMeasure μ] (h : IsSubgaussianVector x c μ)
    (i : n) : ∫ ω, x ω i ∂μ = 0 := by
  have hint : Integrable (fun ω => x ω i) μ :=
    memLp_one_iff_integrable.mp (by simpa using h.memLp_apply i 1)
  refine RCLike.ext ?_ ?_
  · rw [← integral_re hint, (h.hasSubgaussianMGF_re_apply i).integral_eq_zero, map_zero]
  · rw [← integral_im hint, (h.hasSubgaussianMGF_im_apply i).integral_eq_zero, map_zero]

/-- A linear image of a sub-Gaussian vector is a sub-Gaussian vector: if $\mathbf{x}$ has proxy
$c$, then $\mathbf{A}\mathbf{x}$ has proxy $c \|\mathbf{A}\|_2^2$. -/
theorem mulVec {m : Type*} [Fintype m] (h : IsSubgaussianVector x c μ) (A : Matrix m n 𝕜) :
    IsSubgaussianVector (fun ω => A *ᵥ x ω) (c * ‖specNorm A‖₊ ^ 2) μ := by
  refine ⟨fun u => ?_⟩
  have hu := h.hasSubgaussianMGF (Aᵀ *ᵥ u)
  simp only [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec] at hu
  refine hu.mono ?_
  rw [mul_assoc]
  gcongr
  rw [← mul_pow]
  gcongr
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, coe_nnnorm,
    Real.norm_of_nonneg (specNorm_nonneg A), ← Matrix.mulVec_transpose, ← specNorm_transpose]
  exact norm_toLp_mulVec_le Aᵀ u

/-- A real vector with independent coordinates, each sub-Gaussian with proxy $c$, is a
sub-Gaussian vector with proxy $c$. -/
theorem of_iIndepFun {x : Ω → n → ℝ} (hind : iIndepFun (fun i ω => x ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => x ω i) c μ) : IsSubgaussianVector x c μ := by
  refine ⟨fun u => ?_⟩
  have hu := HasSubgaussianMGF.sum_const_mul_of_iIndepFun hind (s := Finset.univ)
    (fun i _ => h i) u
  have hc : ∑ i, ‖u i‖₊ ^ 2 * c = c * ‖WithLp.toLp 2 u‖₊ ^ 2 := by
    rw [EuclideanSpace.nnnorm_eq, NNReal.sq_sqrt, ← Finset.sum_mul, mul_comm]
  rw [hc] at hu
  simpa only [RCLike.re_to_real, dotProduct] using hu

end IsSubgaussianVector

/-- Being a sub-Gaussian vector depends only on the law. -/
theorem _root_.ProbabilityTheory.HasLaw.isSubgaussianVector_iff {ν : Measure (n → 𝕜)}
    (hx : HasLaw x ν μ) : IsSubgaussianVector x c μ ↔ IsSubgaussianVector id c ν := by
  have key : ∀ u : n → 𝕜, ∀ d : ℝ≥0, HasSubgaussianMGF (fun ω => RCLike.re (u ⬝ᵥ x ω)) d μ ↔
      HasSubgaussianMGF (fun v => RCLike.re (u ⬝ᵥ id v)) d ν := by
    intro u d
    have hf : Measurable fun v : n → 𝕜 => RCLike.re (u ⬝ᵥ v) := by
      simp only [dotProduct]
      fun_prop
    have hfx : HasLaw ((fun v : n → 𝕜 => RCLike.re (u ⬝ᵥ v)) ∘ x)
        (ν.map fun v => RCLike.re (u ⬝ᵥ v)) μ :=
      HasLaw.comp ⟨hf.aemeasurable, rfl⟩ hx
    change HasSubgaussianMGF ((fun v : n → 𝕜 => RCLike.re (u ⬝ᵥ v)) ∘ x) d μ ↔
      HasSubgaussianMGF (fun v : n → 𝕜 => RCLike.re (u ⬝ᵥ v)) d ν
    rw [← HasSubgaussianMGF.id_map_iff hfx.aemeasurable, hfx.map_eq,
      ← HasSubgaussianMGF.id_map_iff hf.aemeasurable]
  exact ⟨fun h => ⟨fun u => (key u _).mp (h.hasSubgaussianMGF u)⟩,
    fun h => ⟨fun u => (key u _).mpr (h.hasSubgaussianMGF u)⟩⟩

/-- A standard Gaussian vector is a sub-Gaussian vector with proxy $1$. -/
theorem isSubgaussianVector_of_hasLaw_gaussianVector {g : Ω → n → ℝ}
    (hg : HasLaw g (gaussianVector n) μ) : IsSubgaussianVector g 1 μ := by
  refine ⟨fun u => ?_⟩
  simpa only [RCLike.re_to_real, one_mul] using
    hasSubgaussianMGF_of_hasLaw_gaussianReal (hasLaw_dotProduct_of_hasLaw_gaussianVector hg u)

/-- A vector of independent random signs is a sub-Gaussian vector with proxy $1$. -/
theorem isSubgaussianVector_of_hasLaw_rademacherVector {x : Ω → n → ℝ}
    (hx : HasLaw x (rademacherVector n) μ) : IsSubgaussianVector x 1 μ := by
  exact IsSubgaussianVector.of_iIndepFun hx.iIndepFun_eval
    fun i => hasSubgaussianMGF_of_hasLaw_rademacherMeasure (hx.eval i)

end NLAlib
