/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Vec
public import NLAlib.Probability.Distributions.GaussianMoments
public import NLAlib.RandomMatrix.Gaussian.Moments

/-!
# Fourth moments of Gaussian matrix products

Exact fourth moments of Gaussian sandwiches and exact mean squared errors of Gaussian Gram
products, with their Frobenius bounds.

## Main results

* `NLAlib.integral_frobNorm_mul_mul_pow_four_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_frobNorm_mul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_frobNorm_mul_smul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {a b m n k : Type*} [Fintype a] [Fintype b] [Fintype m] [Fintype n] [Fintype k]

/-- The fourth power of the Frobenius norm of a Gaussian sandwich is integrable. -/
theorem integrable_frobNorm_mul_mul_pow_four_of_hasLaw_gaussianMatrix
    {G : Ω → Matrix m n ℝ} (hG : HasLaw G (gaussianMatrix m n) μ)
    (A : Matrix a m ℝ) (B : Matrix n b ℝ) :
    Integrable (fun ω => frobNorm (A * G ω * B) ^ 4) μ := by
  have h := integrable_norm_mulVec_pow_four_of_hasLaw_gaussianVector
    (hasLaw_uncurry_of_hasLaw_gaussianMatrix hG) (A ⊗ₖ Bᵀ)
  convert h using 1
  funext ω
  have hv := Matrix.kronecker_mulVec_vec Bᵀ (G ω)ᵀ A
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.mul_assoc] at hv
  change (A ⊗ₖ Bᵀ) *ᵥ Function.uncurry (G ω) =
    Function.uncurry (A * G ω * B) at hv
  rw [hv, ← frobNorm_eq_norm_toLp_uncurry]

/-- **Fourth moment of a Gaussian sandwich.**
$$\mathbb{E}\|\mathbf{A}\mathbf{G}\mathbf{B}\|_{\mathsf{F}}^4
= (\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{B}\|_{\mathsf{F}}^2)^2
+2\|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\mathsf{F}}^2
\|\mathbf{B}\mathbf{B}^{\mathsf{H}}\|_{\mathsf{F}}^2\,.$$
[Isserlis1918, fourth-order formula]; here its matrix contraction.
Ported from `NLAlib.integral_frobSq_mul_gaussianMatrix_mul_sq`.
Result: gaussian-frob-fourth-moment -/
theorem integral_frobNorm_mul_mul_pow_four_of_hasLaw_gaussianMatrix
    {G : Ω → Matrix m n ℝ} (hG : HasLaw G (gaussianMatrix m n) μ)
    (A : Matrix a m ℝ) (B : Matrix n b ℝ) :
    ∫ ω, frobNorm (A * G ω * B) ^ 4 ∂μ =
      (frobNorm A ^ 2 * frobNorm B ^ 2) ^ 2 +
        2 * frobNorm (Aᴴ * A) ^ 2 * frobNorm (B * Bᴴ) ^ 2 := by
  have h := integral_norm_mulVec_pow_four_of_hasLaw_gaussianVector
    (hasLaw_uncurry_of_hasLaw_gaussianMatrix hG) (A ⊗ₖ Bᵀ)
  have he : (fun ω => frobNorm (A * G ω * B) ^ 4) =
      (fun ω => ‖WithLp.toLp 2 ((A ⊗ₖ Bᵀ) *ᵥ Function.uncurry (G ω))‖ ^ 4) := by
    funext ω
    have hv := Matrix.kronecker_mulVec_vec Bᵀ (G ω)ᵀ A
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.mul_assoc] at hv
    change (A ⊗ₖ Bᵀ) *ᵥ Function.uncurry (G ω) =
      Function.uncurry (A * G ω * B) at hv
    rw [hv, ← frobNorm_eq_norm_toLp_uncurry]
  rw [he, h, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    frobNorm_kronecker, frobNorm_kronecker, frobNorm_transpose]
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
  ring

/-- The fourth moment of a Gaussian sandwich is at most three times its squared second moment:
$$\mathbb{E}\|\mathbf{A}\mathbf{G}\mathbf{B}\|_{\mathsf{F}}^4
\le 3(\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{B}\|_{\mathsf{F}}^2)^2\,.$$
[Isserlis1918, fourth-order formula]; consequence of the exact contraction. -/
theorem integral_frobNorm_mul_mul_pow_four_le_of_hasLaw_gaussianMatrix
    {G : Ω → Matrix m n ℝ} (hG : HasLaw G (gaussianMatrix m n) μ)
    (A : Matrix a m ℝ) (B : Matrix n b ℝ) :
    ∫ ω, frobNorm (A * G ω * B) ^ 4 ∂μ ≤
      3 * (frobNorm A ^ 2 * frobNorm B ^ 2) ^ 2 := by
  rw [integral_frobNorm_mul_mul_pow_four_of_hasLaw_gaussianMatrix hG]
  have hA : frobNorm (Aᴴ * A) ^ 2 ≤ (frobNorm A ^ 2) ^ 2 := by
    have h := frobNorm_mul_le Aᴴ A
    rw [frobNorm_conjTranspose] at h
    nlinarith [frobNorm_nonneg (Aᴴ * A)]
  have hB : frobNorm (B * Bᴴ) ^ 2 ≤ (frobNorm B ^ 2) ^ 2 := by
    have h := frobNorm_mul_le B Bᴴ
    rw [frobNorm_conjTranspose] at h
    nlinarith [frobNorm_nonneg (B * Bᴴ)]
  have hh := mul_le_mul hA hB (sq_nonneg _) (sq_nonneg _)
  nlinarith [hh]

private def gramCoefficient [DecidableEq k] (u v : n → ℝ) : Matrix (n × k) (n × k) ℝ :=
  Matrix.of fun e f => if e.2 = f.2 then u e.1 * v f.1 else 0

private theorem gramCoefficient_trace [DecidableEq k] (u v : n → ℝ) :
    (gramCoefficient (k := k) u v).trace = (Fintype.card k : ℝ) * (u ⬝ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag, gramCoefficient, Matrix.of_apply, if_true,
    Fintype.sum_prod_type, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, dotProduct]
  rw [← Finset.mul_sum]

private theorem gramCoefficient_frobNorm_sq [DecidableEq k] (u v : n → ℝ) :
    frobNorm (gramCoefficient (k := k) u v) ^ 2 =
      (Fintype.card k : ℝ) * ((u ⬝ᵥ u) * (v ⬝ᵥ v)) := by
  rw [frobNorm_sq_eq_sum_sq]
  simp only [gramCoefficient, Matrix.of_apply, Fintype.sum_prod_type, ite_pow,
    zero_pow two_ne_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [mul_pow, Finset.mul_sum, Finset.sum_mul, dotProduct, ← sq]
  rw [Finset.sum_comm]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

private theorem gramCoefficient_frobInner [DecidableEq k] (u v : n → ℝ) :
    frobInner (gramCoefficient (k := k) u v) (gramCoefficient (k := k) u v)ᵀ =
      (Fintype.card k : ℝ) * (u ⬝ᵥ v) ^ 2 := by
  rw [frobInner_eq_sum_mul]
  simp only [gramCoefficient, Matrix.of_apply, Matrix.transpose_apply, Fintype.sum_prod_type]
  have he (i j : n) (t s : k) :
      (if t = s then u i * v j else 0) * (if s = t then u j * v i else 0) =
        if t = s then (u i * v i) * (u j * v j) else 0 := by
    by_cases h : t = s
    · subst s
      simp only [if_true]
      ring
    · simp only [h, Ne.symm h, if_false, mul_zero]
  simp only [he, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, dotProduct, sq,
    Finset.sum_mul_sum, ← Finset.mul_sum]

private theorem gramCoefficient_quadForm [DecidableEq k] (u v : n → ℝ)
    (X : Matrix n k ℝ) :
    quadForm (gramCoefficient (k := k) u v) (Function.uncurry X) =
      ∑ t : k, (u ⬝ᵥ X.col t) * (v ⬝ᵥ X.col t) := by
  rw [quadForm_eq_sum]
  simp only [gramCoefficient, Matrix.of_apply, Fintype.sum_prod_type,
    star_trivial, mul_ite, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [dotProduct, Matrix.col_apply, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by
      change X i t * (u i * v j) * X j t = _
      ring

private theorem gram_bilinear_moment {G : Ω → Matrix n k ℝ}
    (hG : HasLaw G (gaussianMatrix n k) μ) (u v : n → ℝ) :
    let f := fun ω => (∑ t : k, (u ⬝ᵥ (G ω).col t) * (v ⬝ᵥ (G ω).col t) -
      (Fintype.card k : ℝ) * (u ⬝ᵥ v)) ^ 2
    Integrable f μ ∧ ∫ ω, f ω ∂μ =
      (Fintype.card k : ℝ) * ((u ⬝ᵥ u) * (v ⬝ᵥ v) + (u ⬝ᵥ v) ^ 2) := by
  classical
  have hg := hasLaw_uncurry_of_hasLaw_gaussianMatrix hG
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hL4 (i : n × k) : MemLp (fun ω => Function.uncurry (G ω) i) 4 μ :=
    ((hg.eval i).memLp_comp_iff (f := id) aestronglyMeasurable_id).2
      (memLp_id_gaussianReal' 4 (by norm_num))
  let H := gramCoefficient (k := k) u v
  have hq := (memLp_quadForm hL4 H).sub (memLp_const H.trace)
  have hint : Integrable (fun ω => (quadForm H (Function.uncurry (G ω)) - H.trace) ^ 2) μ := by
    exact (hq.integrable_mul hq).congr (ae_of_all _ fun ω => by
      dsimp only [Pi.mul_apply, Pi.sub_apply]
      ring)
  have he := integral_norm_quadForm_sub_trace_sq hg.iIndepFun_eval hL4
    (fun i => integral_of_hasLaw_gaussianReal (hg.eval i))
    (fun i => by simpa only [Real.norm_eq_abs, sq_abs, NNReal.coe_one] using
      integral_sq_of_hasLaw_gaussianReal (hg.eval i))
    (s := (1 : ℝ)) (fun i => by simpa only [NNReal.coe_one] using
      integral_sq_of_hasLaw_gaussianReal (hg.eval i))
    (m₄ := 3) (fun i => by simpa only [Real.norm_eq_abs, Even.pow_abs ⟨2, rfl⟩,
      NNReal.coe_one, one_pow, mul_one] using
      integral_pow_four_of_hasLaw_gaussianReal (hg.eval i)) H
  simp only [norm_one, one_pow, one_mul, add_zero,
    show (3 : ℝ) - 2 - 1 = 0 by norm_num, zero_mul, Real.norm_eq_abs, sq_abs] at he
  change Integrable _ μ ∧ _
  dsimp only [H] at hint he
  simp only [gramCoefficient_quadForm, gramCoefficient_trace] at hint he
  refine ⟨hint, ?_⟩
  rw [he, gramCoefficient_frobNorm_sq, gramCoefficient_frobInner]
  ring

omit [Fintype a] [Fintype b] in
private theorem gram_error_apply (A : Matrix a n ℝ) (B : Matrix n b ℝ)
    (X : Matrix n k ℝ) (i : a) (j : b) :
    (A * (X * Xᴴ) * B - (Fintype.card k : ℝ) • (A * B)) i j =
      ∑ t : k, (A i ⬝ᵥ X.col t) * (B.col j ⬝ᵥ X.col t) -
        (Fintype.card k : ℝ) * (A i ⬝ᵥ B.col j) := by
  rw [← Matrix.mul_assoc A X Xᴴ, Matrix.mul_assoc (A * X) Xᴴ B]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_trivial, dotProduct, Matrix.col_apply]
  congr 1
  exact Finset.sum_congr rfl fun t _ => congrArg₂ (· * ·) rfl
    (Finset.sum_congr rfl fun l _ => mul_comm _ _)

/-- The squared Frobenius error of a centered Gaussian Gram product is integrable. -/
theorem integrable_frobNorm_mul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (A : Matrix a n ℝ) (B : Matrix n b ℝ) :
    Integrable (fun ω => frobNorm (A * (G ω * (G ω)ᴴ) * B -
      (Fintype.card k : ℝ) • (A * B)) ^ 2) μ := by
  simp_rw [frobNorm_sq_eq_sum_sq, gram_error_apply]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (gram_bilinear_moment hG (A i) (B.col j)).1

/-- **Centered Gaussian Gram moment.** The exact squared Frobenius error is
$$\mathbb{E}\|\mathbf{A}\mathbf{G}\mathbf{G}^{\mathsf{H}}\mathbf{B}
-\lvert k\rvert\mathbf{A}\mathbf{B}\|_{\mathsf{F}}^2
=\lvert k\rvert(\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{B}\|_{\mathsf{F}}^2
+\|\mathbf{A}\mathbf{B}\|_{\mathsf{F}}^2)\,.$$
[Isserlis1918, fourth-order formula]; its centered Gram contraction, including zero columns. -/
theorem integral_frobNorm_mul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (A : Matrix a n ℝ) (B : Matrix n b ℝ) :
    ∫ ω, frobNorm (A * (G ω * (G ω)ᴴ) * B -
      (Fintype.card k : ℝ) • (A * B)) ^ 2 ∂μ =
      (Fintype.card k : ℝ) * (frobNorm A ^ 2 * frobNorm B ^ 2 + frobNorm (A * B) ^ 2) := by
  simp_rw [frobNorm_sq_eq_sum_sq, gram_error_apply]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (gram_bilinear_moment hG (A i) (B.col j)).1]
  simp_rw [integral_finsetSum _ fun j _ => (gram_bilinear_moment hG _ (B.col j)).1]
  simp_rw [(gram_bilinear_moment hG _ _).2]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  change (Fintype.card k : ℝ) * (∑ i, (∑ l, A i l * A i l) *
      (∑ j, ∑ l, B l j * B l j)) + (Fintype.card k : ℝ) *
      (∑ i, ∑ j, (∑ l, A i l * B l j) ^ 2) = _
  simp only [← sq, Matrix.mul_apply, ← Finset.sum_mul]
  rw [Finset.sum_comm (f := fun j l => B l j ^ 2)]

omit [Fintype a] [Fintype b] in
private theorem normalized_gram_error [Nonempty k] (A : Matrix a n ℝ)
    (B : Matrix n b ℝ) (X : Matrix n k ℝ) :
    A * ((Fintype.card k : ℝ)⁻¹ • (X * Xᴴ)) * B - A * B =
      (Fintype.card k : ℝ)⁻¹ • (A * (X * Xᴴ) * B -
        (Fintype.card k : ℝ) • (A * B)) := by
  have hc : (Fintype.card k : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- The squared Frobenius error of normalized Gaussian AMM is integrable, even when the
sketch dimension is zero (when the error is the constant negative product). -/
theorem integrable_frobNorm_mul_smul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (A : Matrix a n ℝ) (B : Matrix n b ℝ) :
    Integrable (fun ω => frobNorm (A * ((Fintype.card k : ℝ)⁻¹ •
      (G ω * (G ω)ᴴ)) * B - A * B) ^ 2) μ := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  cases isEmpty_or_nonempty k with
  | inl hk =>
    have hc : Fintype.card k = 0 := Fintype.card_eq_zero
    simp only [hc, Nat.cast_zero, inv_zero, zero_smul, Matrix.mul_zero, Matrix.zero_mul,
      zero_sub]
    exact integrable_const _
  | inr hk =>
    simp_rw [normalized_gram_error, frobNorm_real_smul, mul_pow, sq_abs]
    exact (integrable_frobNorm_mul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix hG A B).const_mul _

/-- **Gaussian approximate matrix multiplication, exact error.** For a nonempty sketch,
$$\mathbb{E}\|\mathbf{A}(\mathbf{G}\mathbf{G}^{\mathsf{H}}/\lvert k\rvert)
\mathbf{B}-\mathbf{A}\mathbf{B}\|_{\mathsf{F}}^2
=\frac{\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{B}\|_{\mathsf{F}}^2
+\|\mathbf{A}\mathbf{B}\|_{\mathsf{F}}^2}{\lvert k\rvert}\,.$$
[Isserlis1918, fourth-order formula]; the normalized centered Gram contraction.
Ported from `NLAlib.integral_frobSq_mul_gram_mul_transpose_sub`.
Result: gaussian-amm -/
theorem integral_frobNorm_mul_smul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix [Nonempty k]
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (A : Matrix a n ℝ) (B : Matrix n b ℝ) :
    ∫ ω, frobNorm (A * ((Fintype.card k : ℝ)⁻¹ •
      (G ω * (G ω)ᴴ)) * B - A * B) ^ 2 ∂μ =
      (frobNorm A ^ 2 * frobNorm B ^ 2 + frobNorm (A * B) ^ 2) / Fintype.card k := by
  have hc : (Fintype.card k : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp_rw [normalized_gram_error, frobNorm_real_smul, mul_pow, sq_abs]
  rw [integral_const_mul, integral_frobNorm_mul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix hG]
  field_simp

/-- The Gaussian AMM mean squared error is at most
$$\frac{2\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{B}\|_{\mathsf{F}}^2}
{\lvert k\rvert}\,.$$
[Isserlis1918, fourth-order formula]; consequence of the exact error and Frobenius
submultiplicativity. -/
theorem integral_frobNorm_mul_smul_gram_mul_sub_sq_le_of_hasLaw_gaussianMatrix [Nonempty k]
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (A : Matrix a n ℝ) (B : Matrix n b ℝ) :
    ∫ ω, frobNorm (A * ((Fintype.card k : ℝ)⁻¹ •
      (G ω * (G ω)ᴴ)) * B - A * B) ^ 2 ∂μ ≤
      2 * frobNorm A ^ 2 * frobNorm B ^ 2 / Fintype.card k := by
  rw [integral_frobNorm_mul_smul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix hG]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := frobNorm_mul_le A B
  nlinarith [frobNorm_nonneg (A * B)]

end NLAlib
