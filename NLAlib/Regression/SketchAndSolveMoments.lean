/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Regression.SketchAndSolve

/-!
# Gaussian oblique completion with supplied inverse moments

A supplied inverse spectral second moment sharpens the completion noise bound and its
weighted first-moment analogue. Both retain the Gaussian law and exact inverse-Wishart
weighted Frobenius denominator. Here $q$ denotes the rank of the sampled matrix.

## Main results

* The spectral completion second moment with a supplied canonical inverse moment.
* The weighted spectral completion first moment with that same supplied inverse moment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {m p r s a : Type*} [Fintype m] [Fintype p] [Fintype r] [Fintype s]
  [Fintype a] [DecidableEq m] {S : Ω → Matrix p m ℝ}

-- The declaration names alone exceed the line limit.
set_option linter.style.longLine false in
/-- Supplied inverse spectral second moment for Gaussian oblique completion: for a standard
Gaussian sketch, rank(X)+2 at most the sketch width, residual E=(I-P_X)B and beta nonnegative,
the canonical inverse second-moment bound beta squared implies
$$\mathbb E\|\Pi_{X,S}E\|_2^2\le
(\|E\|_2\sqrt{q/(p-q-1)}+\beta\|E\|_{\mathsf F})^2+(\beta\|E\|_2)^2.$$
No printed source. -/
theorem
    integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_of_hasLaw_gaussianMatrix_of_integral_le
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) {β : ℝ} (hβ0 : 0 ≤ β)
    (hEP : ∫ G : Matrix (Fin X.rank) p ℝ, specNorm (pinv G) ^ 2
      ∂gaussianMatrix (Fin X.rank) p ≤ β ^ 2) :
    ∫ ω, specNorm (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B)) ^ 2 ∂μ ≤
      (specNorm ((1 - rangeProjector X) * B) *
            √((X.rank : ℝ) / ((Fintype.card p : ℝ) - X.rank - 1)) +
          frobNorm ((1 - rangeProjector X) * B) *
            β) ^ 2 +
        (specNorm ((1 - rangeProjector X) * B) *
          β) ^ 2 := by
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl X B
  have hrk : Fintype.card (Fin X.rank) + 2 ≤ Fintype.card p := by rwa [Fintype.card_fin]
  have hY := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hG hQ₁
  have hm : AEStronglyMeasurable
      (fun G : Matrix (Fin X.rank) p ℝ => specNorm (pinv G) ^ 2)
      (gaussianMatrix (Fin X.rank) p) :=
    ((continuous_specNorm.measurable.comp measurable_pinv).pow_const 2).aestronglyMeasurable
  have hEP' := (hY.integral_comp hm).trans_le hEP
  have hval := integral_specNorm_pinv_mul_mul_sq_le_of_hasLaw_gaussianMatrix_of_integral_le
    hG hQ₁ hQ₂ h₁₂ hrk (Q₂ᴴ * ((1 - rangeProjector X) * B)) hβ0 hEP'
  simp only [Matrix.conjTranspose_conjTranspose, Fintype.card_fin] at hval
  have hQE : frobNorm (Q₂ᴴ * ((1 - rangeProjector X) * B)) =
      frobNorm ((1 - rangeProjector X) * B) := by
    rw [← hQ₂.frobNorm_mul_left, hE]
  have hQE' : specNorm (Q₂ᴴ * ((1 - rangeProjector X) * B)) =
      specNorm ((1 - rangeProjector X) * B) := by
    rw [← hQ₂.specNorm_mul_left, hE]
  rw [integral_congr_ae (ae_specNorm_obliqueProjector_mul_eq_of_hasLaw_gaussianMatrix
      hS (by omega) hQ₁ hR₁ hE)]
  rwa [hQE, hQE'] at hval


-- The declaration name alone exceeds the line limit.
set_option linter.style.longLine false in
/-- Supplied inverse spectral second moment for weighted Gaussian oblique completion:
under the Gaussian sketch law, rank(X)+2 at most its width and beta nonnegative, writing
E=(I-P_X)B, the canonical inverse second-moment bound beta squared implies
$$\mathbb E\|F\Pi_{X,S}E\|_2\le
\beta\|F\|_2\|E\|_{\mathsf F}+\|F\|_{\mathsf F}\|E\|_2/\sqrt{p-q-1}.$$
No printed source. -/
theorem
    integral_specNorm_mul_obliqueProjector_mul_one_sub_rangeProjector_mul_le_of_hasLaw_gaussianMatrix_of_integral_le
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) (F : Matrix a m ℝ)
    {β : ℝ} (hβ0 : 0 ≤ β)
    (hEP : ∫ G : Matrix (Fin X.rank) p ℝ, specNorm (pinv G) ^ 2
      ∂gaussianMatrix (Fin X.rank) p ≤ β ^ 2) :
    ∫ ω, specNorm (F * (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B))) ∂μ ≤
      β * specNorm F * frobNorm ((1 - rangeProjector X) * B) +
        frobNorm F * specNorm ((1 - rangeProjector X) * B) /
          √((Fintype.card p : ℝ) - X.rank - 1) := by
  have := hS.isProbabilityMeasure
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl X B
  have hrk : Fintype.card (Fin X.rank) + 2 ≤ Fintype.card p := by rwa [Fintype.card_fin]
  have hY := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hG hQ₁
  have hm : AEStronglyMeasurable
      (fun G : Matrix (Fin X.rank) p ℝ => specNorm (pinv G) ^ 2)
      (gaussianMatrix (Fin X.rank) p) :=
    ((continuous_specNorm.measurable.comp measurable_pinv).pow_const 2).aestronglyMeasurable
  have hEP' := (hY.integral_comp hm).trans_le hEP
  have hint := integral_specNorm_mul_mul_pinv_mul_le_of_hasLaw_gaussianMatrix_of_integral_le
    hG hQ₁ hQ₂ h₁₂ hrk (((1 - rangeProjector X) * B)ᴴ * Q₂)
      (Q₁ᴴ * Fᴴ) hβ0 hEP'
  simp only [Fintype.card_fin] at hint
  have hpt : ∀ᵐ ω ∂μ, specNorm (F * (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B))) =
      specNorm (((1 - rangeProjector X) * B)ᴴ * Q₂ * (Q₂ᴴ * (S ω)ᴴ) *
        pinv (Q₁ᴴ * (S ω)ᴴ) * (Q₁ᴴ * Fᴴ)) := by
    have hrank : ∀ᵐ ω ∂μ, (S ω * X).rank = X.rank := by
      filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix X
        (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS) (by omega)] with ω hω
      rwa [Matrix.conjTranspose_conjTranspose] at hω
    filter_upwards [hrank] with ω hω
    rw [obliqueProjector_mul_one_sub_rangeProjector_mul_eq hR₁ hE hω, ← specNorm_conjTranspose]
    congr 1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← pinv_conjTranspose, Matrix.mul_assoc]
  have hC : (Q₂ᴴ * ((1 - rangeProjector X) * B))ᴴ = ((1 - rangeProjector X) * B)ᴴ * Q₂ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hS1 : specNorm (((1 - rangeProjector X) * B)ᴴ * Q₂) =
      specNorm ((1 - rangeProjector X) * B) := by
    rw [← hC, specNorm_conjTranspose, ← hQ₂.specNorm_mul_left, hE]
  have hS2 : frobNorm (((1 - rangeProjector X) * B)ᴴ * Q₂) =
      frobNorm ((1 - rangeProjector X) * B) := by
    rw [← hC, frobNorm_conjTranspose, ← hQ₂.frobNorm_mul_left, hE]
  have hT1 : specNorm (Q₁ᴴ * Fᴴ) ≤ specNorm F := by
    refine (specNorm_mul_le _ _).trans ?_
    rw [specNorm_conjTranspose, specNorm_conjTranspose]
    exact mul_le_of_le_one_left (specNorm_nonneg _) hQ₁.specNorm_le_one
  have hT2 : frobNorm (Q₁ᴴ * Fᴴ) ≤ frobNorm F := by
    refine (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans ?_
    rw [specNorm_conjTranspose, frobNorm_conjTranspose]
    exact mul_le_of_le_one_left (frobNorm_nonneg _) hQ₁.specNorm_le_one
  rw [integral_congr_ae hpt]
  refine hint.trans ?_
  rw [hS1, hS2]
  have h1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hT2 (specNorm_nonneg ((1 - rangeProjector X) * B)))
    (Real.sqrt_nonneg ((Fintype.card p : ℝ) - X.rank - 1))
  have h2 := mul_le_mul_of_nonneg_left hT1
    (mul_nonneg hβ0 (frobNorm_nonneg ((1 - rangeProjector X) * B)))
  calc
    _ ≤ specNorm ((1 - rangeProjector X) * B) * frobNorm F /
        √((Fintype.card p : ℝ) - X.rank - 1) +
        β * frobNorm ((1 - rangeProjector X) * B) * specNorm F := add_le_add h1 h2
    _ = _ := by ring

end NLAlib
