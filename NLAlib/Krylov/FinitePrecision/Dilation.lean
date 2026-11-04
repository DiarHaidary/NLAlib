/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Matrix.Block
public import NLAlib.Krylov.FinitePrecision.LanczosData
public import NLAlib.Matrix.Subspaces.OrthonormalDilation
public import NLAlib.Krylov.Processes.LanczosRecurrence
public import NLAlib.Matrix.Norms.Projector

/-!
# Orthonormal dilation of perturbed Lanczos data

The nilpotent dilation of a symmetric three-term datum with unit vectors gives an orthonormal
basis in a larger space. Its exchange identities construct a symmetric matrix on which exact
Lanczos recovers the original tridiagonal coefficients, including terminal breakdown.
No printed source; the maintainer's draft, `lem:dilation`, `lem:exchange`, `thm:greenbaum`.

## Main results

* `NLAlib.LanczosData.exchangeDefect_one`, `NLAlib.LanczosData.exchangeDefect_succ`.
* `NLAlib.LanczosData.backwardH_mul_dilatedBasis`.
* `NLAlib.LanczosData.frobNorm_backwardH_sub_dilatedH_le_two_mul`.
* `NLAlib.LanczosData.lanczosTridiagonal_backwardH_dilatedStart`.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-- Block $r$ of $(\mathbf{I} \otimes \mathbf{H})\mathbf{M}$ is $\mathbf{H}$ times block $r$ of
$\mathbf{M}$. -/
private theorem submatrix_blockDiagonal_mul {n m : ℕ} {p : Type*}
    (H : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin n × Fin m) p ℝ) (r : Fin m) :
    (Matrix.blockDiagonal (fun _ : Fin m => H) * M).submatrix (fun i => (i, r)) id =
      H * M.submatrix (fun i => (i, r)) id := by
  ext i j
  simp only [Matrix.submatrix_apply, id, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem submatrix_sub' {a b c d : Type*} (A B : Matrix a b ℝ) (f : c → a) (g : d → b) :
    (A - B).submatrix f g = A.submatrix f g - B.submatrix f g := rfl

namespace LanczosData

variable {n k : ℕ} (D : LanczosData n k)

/-! ### The dilated recurrence of a three-term datum

The construction of the backward model uses of a run only a symmetric three-term datum with unit
vectors $\mathbf{v}_1, \dots, \mathbf{v}_{k+1}$ (the hypothesis `hW` below, on the Gram matrix
of $\mathbf{V}_{k+1}$); the bounds take the recurrence residual and the Gram commutator as
inputs. The run versions in `NLAlib.LanczosRun` are the instances for the normalised run. -/

/-- The **dilated matrix** $\hat{\mathbf{H}} = \mathbf{I}_{k+1} \otimes \mathbf{H}$. -/
def dilatedH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  Matrix.blockDiagonal fun _ => D.H

/-- The **dilated vectors** $\hat{\mathbf{V}}_{k+1}$: the orthonormal dilation of
$\mathbf{v}_1, \dots, \mathbf{v}_{k+1}$. -/
noncomputable def dilatedBasisSucc : Matrix (Fin n × Fin (k + 1)) (Fin (k + 1)) ℝ :=
  orthonormalDilation D.basisSucc

/-- The first $k$ dilated vectors $\hat{\mathbf{V}}_k$. -/
noncomputable def dilatedBasis : Matrix (Fin n × Fin (k + 1)) (Fin k) ℝ :=
  D.dilatedBasisSucc.submatrix id Fin.castSucc

/-- The **dilated starting vector** $(\mathbf{v}_1, \mathbf{0}, \dots, \mathbf{0})$. -/
def dilatedStart : Fin n × Fin (k + 1) → ℝ :=
  fun p => if (p.2 : ℕ) = 0 then D.v 1 p.1 else 0

/-- The **residual of the dilated recurrence**
$\hat{\mathbf{E}} = \hat{\mathbf{H}}\hat{\mathbf{V}}_k - \hat{\mathbf{V}}_{k+1}
\underline{\mathbf{T}}_k$. -/
noncomputable def dilatedResidual : Matrix (Fin n × Fin (k + 1)) (Fin k) ℝ :=
  D.dilatedH * D.dilatedBasis - D.dilatedBasisSucc * D.tridiagonalSucc

/-- Unit vectors $\mathbf{v}_1, \dots, \mathbf{v}_{k+1}$ give a Gram matrix of
$\mathbf{V}_{k+1}$ with unit diagonal. -/
theorem transpose_basisSucc_mul_self_apply_of_norm
    (h : ∀ j, 1 ≤ j → j ≤ k + 1 → ‖WithLp.toLp 2 (D.v j)‖ = 1) (j : Fin (k + 1)) :
    (D.basisSuccᵀ * D.basisSucc) j j = 1 := by
  have h1 := h ((j : ℕ) + 1) (by omega) (by omega)
  have h2 : ‖WithLp.toLp 2 (D.v ((j : ℕ) + 1))‖ ^ 2 = 1 := by rw [h1, one_pow]
  rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self] at h2
  rw [Matrix.mul_apply]
  exact h2

/-- **The dilated vectors are orthonormal** when $\mathbf{v}_1, \dots, \mathbf{v}_{k+1}$ are unit
vectors. No printed source; the maintainer's draft, `lem:dilation`. -/
theorem hasOrthonormalCols_dilatedBasisSucc (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    HasOrthonormalCols D.dilatedBasisSucc :=
  hasOrthonormalCols_orthonormalDilation hW

/-- The first dilated vector is the dilated starting vector. -/
theorem dilatedBasisSucc_col_zero : D.dilatedBasisSucc.col 0 = D.dilatedStart := by
  funext p
  rw [Matrix.col_apply, dilatedBasisSucc, orthonormalDilation_apply_of_val_eq_zero _ rfl]
  simp only [dilatedStart, Fin.ext_iff, Fin.val_zero]
  rfl

/-- The **exchange defect** $\mathbf{Y}_r = \underline{\mathbf{T}}_k\mathbf{K}_k^r -
\mathbf{K}^r\underline{\mathbf{T}}_k$ of the dilation. -/
noncomputable def exchangeDefect (r : ℕ) : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  D.tridiagonalSucc * (dilationK D.basisSucc ^ r).submatrix Fin.castSucc Fin.castSucc -
    dilationK D.basisSucc ^ r * D.tridiagonalSucc

/-- Block $r$ of the dilated residual:
$\hat{\mathbf{E}}_r = \mathbf{F}_k(\mathbf{C}\mathbf{K}^r)_k
+ \mathbf{V}_{k+1}(\mathbf{Y}_r - \mathbf{Y}_{r+1})$. -/
theorem dilatedResidual_submatrix (r : Fin (k + 1)) :
    D.dilatedResidual.submatrix (fun i => (i, r)) id =
      D.residual * (dilationC D.basisSucc *
          dilationK D.basisSucc ^ (r : ℕ)).submatrix Fin.castSucc Fin.castSucc +
        D.basisSucc * (D.exchangeDefect r - D.exchangeDefect (r + 1)) := by
  set W := D.basisSucc
  set C := dilationC W
  set K := dilationK W
  have hCKr : (C * K ^ (r : ℕ)).IsUpperTriangular :=
    (isUpperTriangular_dilationC W).mul ((isUpperTriangular_dilationK W).pow _)
  have hB : D.dilatedBasis.submatrix (fun i => (i, r)) id =
      (W * (C * K ^ (r : ℕ))).submatrix id Fin.castSucc := by
    ext i j
    simp only [dilatedBasis, dilatedBasisSucc, orthonormalDilation, Matrix.submatrix_apply, id,
      Matrix.of_apply, Matrix.mul_assoc]
    rfl
  have hBs : D.dilatedBasisSucc.submatrix (fun i => (i, r)) id = W * (C * K ^ (r : ℕ)) := by
    ext i j
    simp only [dilatedBasisSucc, orthonormalDilation, Matrix.submatrix_apply, id,
      Matrix.of_apply, Matrix.mul_assoc]
    rfl
  have hW : W.submatrix id Fin.castSucc = D.basis := by
    ext i j
    rfl
  have hrec := D.mul_basis_eq_basisSucc_mul
  have hCK : C * K ^ (r : ℕ) = K ^ (r : ℕ) - K ^ ((r : ℕ) + 1) := by
    have : C = 1 - K := by simp only [K, dilationK]; abel
    rw [this, Matrix.sub_mul, Matrix.one_mul, pow_succ']
  have hdil : D.dilatedH = Matrix.blockDiagonal (fun _ : Fin (k + 1) => D.H) := rfl
  rw [dilatedResidual, submatrix_sub', hdil, submatrix_blockDiagonal_mul,
    Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, hB, hBs,
    hCKr.submatrix_castSucc_mul W, hW]
  rw [← Matrix.mul_assoc, hrec]
  simp only [exchangeDefect]
  rw [hCK, submatrix_sub']
  simp only [Matrix.submatrix_id_id, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc]
  abel

/-- The exchange defects satisfy $\mathbf{Y}_{r+1} = \mathbf{Y}_r\mathbf{K}_k +
\mathbf{K}^r\mathbf{Y}_1$. -/
theorem exchangeDefect_succ (r : ℕ) :
    D.exchangeDefect (r + 1) =
      D.exchangeDefect r * (dilationK D.basisSucc).submatrix Fin.castSucc Fin.castSucc +
        dilationK D.basisSucc ^ r * D.exchangeDefect 1 := by
  set K := dilationK D.basisSucc
  have hK := isUpperTriangular_dilationK D.basisSucc
  simp only [exchangeDefect]
  rw [pow_succ, hK.submatrix_castSucc_mul_castSucc _, pow_one]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- The exchange recurrence with the left power advanced first. -/
theorem exchangeDefect_succ_eq_mul_add (r : ℕ) :
    D.exchangeDefect (r + 1) = dilationK D.basisSucc * D.exchangeDefect r +
      D.exchangeDefect 1 *
        (dilationK D.basisSucc ^ r).submatrix Fin.castSucc Fin.castSucc := by
  have hK := (isUpperTriangular_dilationK D.basisSucc).pow r
  simp only [exchangeDefect]
  rw [pow_succ', Matrix.IsUpperTriangular.submatrix_castSucc_mul_castSucc hK _, pow_one]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- $\mathbf{Y}_0 = \mathbf{0}$. -/
theorem exchangeDefect_zero : D.exchangeDefect 0 = 0 := by
  simp only [exchangeDefect, pow_zero, Matrix.one_mul]
  rw [Matrix.submatrix_one _ (Fin.castSucc_injective k), Matrix.mul_one, sub_self]

/-- **The exchange rule**: $\mathbf{Y}_1 = \mathbf{C}(\underline{\mathbf{T}}_k\mathbf{R}_k -
\mathbf{R}\underline{\mathbf{T}}_k)\mathbf{C}_k$. No printed source; the maintainer's draft,
`eq:L-commutator`; [Paige2010, (3.9)]. -/
theorem exchangeDefect_one :
    D.exchangeDefect 1 = dilationC D.basisSucc *
      (D.tridiagonalSucc * (strictUpperGram D.basisSucc).submatrix Fin.castSucc
          Fin.castSucc - strictUpperGram D.basisSucc * D.tridiagonalSucc) *
      (dilationC D.basisSucc).submatrix Fin.castSucc Fin.castSucc := by
  simp only [exchangeDefect, pow_one]
  set W := D.basisSucc
  set R := strictUpperGram W
  set C := dilationC W
  set K := dilationK W
  set T := D.tridiagonalSucc
  have hRC : R.submatrix Fin.castSucc Fin.castSucc * C.submatrix Fin.castSucc Fin.castSucc =
      K.submatrix Fin.castSucc Fin.castSucc := by
    rw [← (isUpperTriangular_dilationC W).submatrix_castSucc_mul_castSucc _,
      ← dilationK_eq_strictUpperGram_mul]
  have hCR : C * R = K := (dilationK_eq_dilationC_mul W).symm
  have hC : C = 1 - K := by simp only [K, dilationK]; abel
  have hCk :
      C.submatrix Fin.castSucc Fin.castSucc = 1 - K.submatrix Fin.castSucc Fin.castSucc := by
    rw [hC, submatrix_sub', Matrix.submatrix_one _ (Fin.castSucc_injective k)]
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  rw [hRC, ← Matrix.mul_assoc C R, hCR, hCk]
  conv_rhs => rw [hC]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  abel

/-- The commutator of the Gram matrix with $\underline{\mathbf{T}}_k$ is the Gram commutator
with a zero last row: $\underline{\mathbf{T}}_k\mathbf{R}_k - \mathbf{R}\underline{\mathbf{T}}_k
= \mathbf{J}\mathbf{M}_k$, $\mathbf{J}$ the first $k$ columns of $\mathbf{I}_{k+1}$. -/
theorem tridiagonalSucc_mul_sub_eq :
    D.tridiagonalSucc * (strictUpperGram D.basisSucc).submatrix Fin.castSucc
        Fin.castSucc - strictUpperGram D.basisSucc * D.tridiagonalSucc =
      (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).submatrix id Fin.castSucc *
        D.gramCommutator := by
  have hRc : ∀ a b : Fin k, strictUpperGram D.basisSucc (Fin.castSucc a) (Fin.castSucc b) =
      D.gramStrictUpper a b := fun a b => by
    simp only [strictUpperGram, LanczosData.gramStrictUpper, Matrix.of_apply,
      Fin.castSucc_lt_castSucc_iff, Matrix.mul_apply, Matrix.transpose_apply,
      LanczosData.basisSucc, dotProduct, Fin.val_castSucc]
  have hRlast : ∀ a : Fin k, strictUpperGram D.basisSucc (Fin.castSucc a) (Fin.last k) =
      D.v ((a : ℕ) + 1) ⬝ᵥ D.v (k + 1) := fun a => by
    simp only [strictUpperGram, Matrix.of_apply, if_pos (Fin.castSucc_lt_last a),
      Matrix.mul_apply, Matrix.transpose_apply, LanczosData.basisSucc, dotProduct,
      Fin.val_castSucc, Fin.val_last]
  have hRl : ∀ l, strictUpperGram D.basisSucc (Fin.last k) l = 0 := fun l =>
    strictUpperGram_apply_of_le _ (Fin.le_last l)
  have hlast : ∀ j : Fin k, j = D.lastIndex ↔ k = (j : ℕ) + 1 := fun j => by
    rw [Fin.ext_iff]
    simp only [LanczosData.lastIndex]
    have := D.k_pos
    omega
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · have h1 : ∀ l : Fin k, (Fin.last k = Fin.castSucc l) ↔ False :=
      fun l => ⟨fun h => (Fin.castSucc_lt_last l).ne' h, False.elim⟩
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [hRl, zero_mul, Finset.sum_const_zero, sub_zero, Matrix.submatrix_apply, id,
      Matrix.one_apply, h1, if_false]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [D.tridiagonalSucc_last]
    split_ifs with h
    · rw [strictUpperGram_apply_of_le _ (by rw [Fin.le_def]; simp only [Fin.val_castSucc]; omega),
        mul_zero]
    · rw [zero_mul]
  · rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc,
      Matrix.mul_apply]
    simp only [Matrix.submatrix_apply, id, D.tridiagonalSucc_castSucc, D.tridiagonalSucc_last,
      hRc, hRlast, Matrix.one_apply, Fin.castSucc_inj, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [LanczosData.gramCommutator, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.vecMulVec_apply, Pi.single_apply, hlast]
    have hc : (D.basisᵀ *ᵥ (D.β k • D.v (k + 1))) i' =
        D.β k * (D.v ((i' : ℕ) + 1) ⬝ᵥ D.v (k + 1)) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, LanczosData.basis,
        Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hc]
    by_cases h : k = (j : ℕ) + 1
    · simp only [h, if_true]
      ring
    · simp only [h, if_false]
      ring

/-- With unit vectors, $\mathbf{V}_{k+1}$ has Frobenius norm $\sqrt{k + 1}$. -/
theorem frobNorm_basisSucc_of_unit (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    frobNorm D.basisSucc = Real.sqrt (k + 1) := by
  rw [← Real.sqrt_sq (frobNorm_nonneg _), frobNorm_sq_eq_sum_col]
  congr 1
  have : ∀ j : Fin (k + 1), ‖WithLp.toLp 2 (D.basisSucc.col j)‖ = 1 := fun j => by
    have h := hW j
    rw [Matrix.mul_apply] at h
    have h2 : ‖WithLp.toLp 2 (D.basisSucc.col j)‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
      exact h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  simp only [this, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- **The exchange rule, bounds**: $\|\mathbf{Y}_1\|_2 \le 4\|\mathbf{M}_k\|_2$ for unit
vectors. No printed source; the maintainer's draft, `lem:exchange`. -/
theorem specNorm_exchangeDefect_one_le (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1)
    {G : ℝ} (hG : specNorm D.gramCommutator ≤ G) :
    specNorm (D.exchangeDefect 1) ≤ 4 * G := by
  set W := D.basisSucc
  have hC := specNorm_dilationC_le_two hW
  have hCk : specNorm ((dilationC W).submatrix Fin.castSucc Fin.castSucc) ≤ 2 :=
    (specNorm_submatrix_le _ (Fin.castSucc_injective k) (Fin.castSucc_injective k)).trans hC
  have hJ : HasOrthonormalCols ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).submatrix id
      Fin.castSucc) :=
    hasOrthonormalCols_one.submatrix (Equiv.refl _) (Fin.castSucc_injective k)
  have hZ : specNorm (D.tridiagonalSucc * (strictUpperGram W).submatrix Fin.castSucc
      Fin.castSucc - strictUpperGram W * D.tridiagonalSucc) ≤ G := by
    rw [D.tridiagonalSucc_mul_sub_eq, hJ.specNorm_mul_left]
    exact hG
  rw [D.exchangeDefect_one]
  refine (specNorm_mul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)).trans ?_
  calc specNorm (dilationC W) * specNorm (D.tridiagonalSucc *
        (strictUpperGram W).submatrix Fin.castSucc Fin.castSucc -
        strictUpperGram W * D.tridiagonalSucc) *
        specNorm ((dilationC W).submatrix Fin.castSucc Fin.castSucc)
      ≤ 2 * G * 2 := by
        have := (specNorm_nonneg _).trans hZ
        gcongr
    _ = 4 * G := by ring

/-- The exchange defects grow at most linearly: $\|\mathbf{Y}_r\|_2 \le r\|\mathbf{Y}_1\|_2$. -/
theorem specNorm_exchangeDefect_le (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) (r : ℕ) :
    specNorm (D.exchangeDefect r) ≤ r * specNorm (D.exchangeDefect 1) := by
  have hK := specNorm_dilationK_le_one hW
  have hKk : specNorm ((dilationK D.basisSucc).submatrix Fin.castSucc Fin.castSucc) ≤ 1 :=
    (specNorm_submatrix_le _ (Fin.castSucc_injective k) (Fin.castSucc_injective k)).trans hK
  have hKr : ∀ r : ℕ, specNorm (dilationK D.basisSucc ^ r) ≤ 1 := fun r =>
    (specNorm_pow_le _ r).trans (pow_le_one₀ (specNorm_nonneg _) hK)
  induction r with
  | zero => rw [D.exchangeDefect_zero, specNorm_zero]; simp
  | succ r ih =>
    rw [D.exchangeDefect_succ]
    refine (specNorm_add_le _ _).trans ?_
    have h1 : specNorm (D.exchangeDefect r * (dilationK D.basisSucc).submatrix
        Fin.castSucc Fin.castSucc) ≤ r * specNorm (D.exchangeDefect 1) :=
      (specNorm_mul_le _ _).trans (by
        calc specNorm (D.exchangeDefect r) * _ ≤ r * specNorm (D.exchangeDefect 1) * 1 := by
              gcongr
          _ = _ := mul_one _)
    have h2 : specNorm (dilationK D.basisSucc ^ r * D.exchangeDefect 1) ≤
        specNorm (D.exchangeDefect 1) :=
      (specNorm_mul_le _ _).trans (by
        calc _ ≤ 1 * specNorm (D.exchangeDefect 1) := by gcongr; exact hKr r
          _ = _ := one_mul _)
    push_cast
    linarith

/-! ### The backward model of a three-term datum -/

/-- The **backward perturbation**
$\mathbf{\Delta} = -\hat{\mathbf{E}}\hat{\mathbf{V}}_k^{\mathsf{T}} -
\hat{\mathbf{V}}_k\hat{\mathbf{E}}^{\mathsf{T}}(\mathbf{I} - \hat{\mathbf{V}}_k
\hat{\mathbf{V}}_k^{\mathsf{T}})$. -/
noncomputable def backwardPerturbation : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  -(D.dilatedResidual * D.dilatedBasisᵀ) -
    D.dilatedBasis * D.dilatedResidualᵀ * (1 - D.dilatedBasis * D.dilatedBasisᵀ)

/-- The **backward model** $\tilde{\mathbf{H}} = \mathbf{I}_{k+1} \otimes \mathbf{H} +
\mathbf{\Delta}$. -/
noncomputable def backwardH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  D.dilatedH + D.backwardPerturbation

/-- The first $k$ dilated vectors are orthonormal. -/
theorem hasOrthonormalCols_dilatedBasis (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    HasOrthonormalCols D.dilatedBasis :=
  (D.hasOrthonormalCols_dilatedBasisSucc hW).submatrix (Equiv.refl _) (Fin.castSucc_injective k)

/-- $\hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{V}}_{k+1}\underline{\mathbf{T}}_k
= \mathbf{T}_k$. -/
theorem transpose_dilatedBasis_mul_dilatedBasisSucc_mul
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    D.dilatedBasisᵀ * (D.dilatedBasisSucc * D.tridiagonalSucc) = D.tridiagonal := by
  have hQ := D.hasOrthonormalCols_dilatedBasisSucc hW
  have hQQ : D.dilatedBasisSuccᵀ * D.dilatedBasisSucc = 1 := by
    have := hQ.conjTranspose_mul_self
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have h1 : D.dilatedBasisᵀ * D.dilatedBasisSucc =
      (D.dilatedBasisSuccᵀ * D.dilatedBasisSucc).submatrix Fin.castSucc id := by
    rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
    rfl
  rw [← Matrix.mul_assoc, h1, hQQ]
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact D.tridiagonalSucc_castSucc i j

/-- The dilated matrix is symmetric. -/
theorem transpose_dilatedH : D.dilatedHᵀ = D.dilatedH := by
  rw [dilatedH, Matrix.blockDiagonal_transpose, D.transpose_H]

/-- $\hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{E}}$ is symmetric. -/
theorem transpose_dilatedResidual_mul_dilatedBasis
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    D.dilatedResidualᵀ * D.dilatedBasis = D.dilatedBasisᵀ * D.dilatedResidual := by
  have hX : D.dilatedBasisᵀ * D.dilatedResidual =
      D.dilatedBasisᵀ * D.dilatedH * D.dilatedBasis - D.tridiagonal := by
    rw [dilatedResidual, Matrix.mul_sub, D.transpose_dilatedBasis_mul_dilatedBasisSucc_mul hW,
      Matrix.mul_assoc]
  rw [← Matrix.transpose_transpose (D.dilatedResidualᵀ * D.dilatedBasis), Matrix.transpose_mul,
    Matrix.transpose_transpose, hX, Matrix.transpose_sub, D.transpose_tridiagonal,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, D.transpose_dilatedH,
    Matrix.mul_assoc]

/-- The backward model is symmetric. -/
theorem transpose_backwardH (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    D.backwardHᵀ = D.backwardH := by
  set Q := D.dilatedBasis
  set E := D.dilatedResidual
  have hsym := D.transpose_dilatedResidual_mul_dilatedBasis hW
  rw [backwardH, backwardPerturbation, Matrix.transpose_add, D.transpose_dilatedH]
  congr 1
  simp only [Matrix.transpose_sub, Matrix.transpose_neg, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_one]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Eᵀ Q, hsym, Matrix.mul_assoc]
  abel

/-- **The backward model satisfies the recurrence exactly**:
$\tilde{\mathbf{H}}\hat{\mathbf{V}}_k = \hat{\mathbf{V}}_{k+1}\underline{\mathbf{T}}_k$. -/
theorem backwardH_mul_dilatedBasis (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    D.backwardH * D.dilatedBasis = D.dilatedBasisSucc * D.tridiagonalSucc := by
  have hQ := D.hasOrthonormalCols_dilatedBasis hW
  have hQQ : D.dilatedBasisᵀ * D.dilatedBasis = 1 := by
    have := hQ.conjTranspose_mul_self
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [backwardH, backwardPerturbation, Matrix.add_mul, Matrix.sub_mul, Matrix.neg_mul]
  simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hQQ, Matrix.mul_one, sub_self,
    Matrix.mul_zero, sub_zero]
  rw [dilatedResidual]
  abel

/-- The backward perturbation is at most $\sqrt{2}$ times the dilated residual in Frobenius
norm, by orthogonality of the two completion summands. -/
theorem frobNorm_backwardH_sub_dilatedH_le_sqrt_two_mul
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    frobNorm (D.backwardH - D.dilatedH) ≤ Real.sqrt 2 * frobNorm D.dilatedResidual := by
  have h := (D.hasOrthonormalCols_dilatedBasis hW).frobNorm_add_mul_conjTranspose_le
    D.dilatedResidual
  rw [backwardH, add_sub_cancel_left, backwardPerturbation]
  rw [sub_eq_add_neg, ← neg_add, frobNorm_neg]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- The backward perturbation is at most twice the dilated residual in Frobenius norm. -/
theorem frobNorm_backwardH_sub_dilatedH_le_two_mul
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    frobNorm (D.backwardH - D.dilatedH) ≤ 2 * frobNorm D.dilatedResidual := by
  have hs : Real.sqrt (2 : ℝ) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  exact (D.frobNorm_backwardH_sub_dilatedH_le_sqrt_two_mul hW).trans
    (mul_le_mul_of_nonneg_right hs (frobNorm_nonneg _))

/-- The dilated vectors as a sequence: $\hat{\mathbf{u}}_m$ is column $m - 1$ of
$\hat{\mathbf{V}}_{k+1}$ for $1 \le m \le k + 1$, and $\mathbf{0}$ otherwise. -/
noncomputable def dilatedV (m : ℕ) : Fin n × Fin (k + 1) → ℝ :=
  fun p => if h : 1 ≤ m ∧ m ≤ k + 1 then D.dilatedBasisSucc p ⟨m - 1, by omega⟩ else 0

private theorem dilatedV_succ {m : ℕ} (hm : m < k + 1) (p : Fin n × Fin (k + 1)) :
    D.dilatedBasisSucc p ⟨m, hm⟩ = D.dilatedV (m + 1) p := by
  simp only [dilatedV, dif_pos (show 1 ≤ m + 1 ∧ m + 1 ≤ k + 1 by omega), Nat.add_sub_cancel]

/-- The dilated sequence satisfies the hypotheses of
`NLAlib.lanczosState_eq_of_orthonormal_recurrence` for the backward model. -/
private theorem dilatedV_orthonormal_recurrence
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    D.dilatedV 0 = 0 ∧
    (∀ i j, 1 ≤ i → i ≤ k + 1 → 1 ≤ j → j ≤ k + 1 →
      D.dilatedV i ⬝ᵥ D.dilatedV j = if i = j then 1 else 0) ∧
    (∀ j < k, D.backwardH *ᵥ D.dilatedV (j + 1) = D.β j • D.dilatedV j +
      D.α (j + 1) • D.dilatedV (j + 1) + D.β (j + 1) • D.dilatedV (j + 2)) ∧
    D.dilatedV 1 = D.dilatedStart := by
  have hQ := D.hasOrthonormalCols_dilatedBasisSucc hW
  have hQQ : D.dilatedBasisSuccᵀ * D.dilatedBasisSucc = 1 := by
    have := hQ.conjTranspose_mul_self
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext p
    simp only [dilatedV, Pi.zero_apply]
    rw [dif_neg (by omega)]
  · intro i j hi1 hi2 hj1 hj2
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have h := congrFun (congrFun hQQ ⟨i, by omega⟩) ⟨j, by omega⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [Matrix.transpose_apply, dilatedV_succ] at h
    rw [dotProduct, h]
    simp only [Fin.mk.injEq, Nat.add_right_cancel_iff]
  · intro j hj
    funext p
    have hl := D.mul_tridiagonalSucc_apply D.dilatedBasisSucc D.dilatedV
      (fun m hm q => D.dilatedV_succ hm q) p ⟨j, hj⟩
    have hcol : ∀ q, D.dilatedBasis q ⟨j, hj⟩ = D.dilatedV (j + 1) q := fun q =>
      D.dilatedV_succ (by omega) q
    have := congrFun (congrFun (D.backwardH_mul_dilatedBasis hW) p) ⟨j, hj⟩
    rw [Matrix.mul_apply, hl] at this
    simp only [hcol] at this
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact this
  · rw [← D.dilatedBasisSucc_col_zero]
    funext p
    rw [Matrix.col_apply, show (0 : Fin (k + 1)) = ⟨0, by omega⟩ from Fin.ext (by simp),
      D.dilatedV_succ (m := 0) (by omega)]

variable {D}

/-- **Exact Lanczos on the backward model computes the tridiagonal matrix**, for unit vectors and
$\beta_j \ge 0$ ($j \le k$), $\beta_j > 0$ ($1 \le j < k$). -/
theorem lanczosTridiagonal_backwardH_dilatedStart
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) (hβ : ∀ j ≤ k, 0 ≤ D.β j)
    (hβpos : ∀ j, 1 ≤ j → j < k → 0 < D.β j) :
    lanczosTridiagonal D.backwardH D.dilatedStart k = D.tridiagonal := by
  obtain ⟨h0, horth, hrec, h1⟩ := D.dilatedV_orthonormal_recurrence hW
  have hst := lanczosState_eq_of_orthonormal_recurrence h0 horth hrec D.β_zero hβ hβpos
  rw [← h1]
  ext i j
  simp only [lanczosTridiagonal, Matrix.of_apply, hst i i.2, hst j j.2,
    (lanczosStep_of_orthonormal_recurrence horth hrec hβ i.2).1,
    RCLike.ofReal_real_eq_id, id]
  rfl

/-- Exact Lanczos on the backward model computes the dilated vectors. -/
theorem lanczosMatrix_backwardH_dilatedStart
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) (hβ : ∀ j ≤ k, 0 ≤ D.β j)
    (hβpos : ∀ j, 1 ≤ j → j < k → 0 < D.β j) :
    lanczosMatrix D.backwardH D.dilatedStart k = D.dilatedBasis := by
  obtain ⟨h0, horth, hrec, h1⟩ := D.dilatedV_orthonormal_recurrence hW
  have hst := lanczosState_eq_of_orthonormal_recurrence h0 horth hrec D.β_zero hβ hβpos
  rw [← h1]
  ext p j
  simp only [lanczosMatrix, Matrix.of_apply, hst j j.2]
  exact (D.dilatedV_succ (by omega) p).symm

/-- Exact Lanczos on the backward model computes the last coefficient $\beta_k$. -/
theorem lanczosState_backwardH_dilatedStart_beta
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) (hβ : ∀ j ≤ k, 0 ≤ D.β j)
    (hβpos : ∀ j, 1 ≤ j → j < k → 0 < D.β j) :
    (lanczosState D.backwardH D.dilatedStart k).beta = D.β k := by
  obtain ⟨h0, horth, hrec, h1⟩ := D.dilatedV_orthonormal_recurrence hW
  rw [← h1]
  exact lanczosState_beta_eq_of_orthonormal_recurrence h0 horth hrec D.β_zero hβ hβpos

/-- Exact Lanczos on the backward model computes the diagonal coefficients. -/
theorem lanczosAlpha_backwardH_dilatedStart
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) (hβ : ∀ j ≤ k, 0 ≤ D.β j)
    (hβpos : ∀ j, 1 ≤ j → j < k → 0 < D.β j) {j : ℕ} (hj : j < k) :
    lanczosAlpha D.backwardH (lanczosState D.backwardH D.dilatedStart j) = D.α (j + 1) := by
  obtain ⟨h0, horth, hrec, h1⟩ := D.dilatedV_orthonormal_recurrence hW
  rw [← h1, lanczosState_eq_of_orthonormal_recurrence h0 horth hrec D.β_zero hβ hβpos j hj]
  exact (lanczosStep_of_orthonormal_recurrence horth hrec hβ hj).1

/-- Exact Lanczos on the backward model computes the off-diagonal coefficients. -/
theorem lanczosState_backwardH_dilatedStart_succ_beta
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) (hβ : ∀ j ≤ k, 0 ≤ D.β j)
    (hβpos : ∀ j, 1 ≤ j → j < k → 0 < D.β j) {j : ℕ} (hj : j < k) :
    (lanczosState D.backwardH D.dilatedStart (j + 1)).beta = D.β (j + 1) := by
  obtain ⟨h0, horth, hrec, h1⟩ := D.dilatedV_orthonormal_recurrence hW
  rw [← h1, show lanczosState D.backwardH (D.dilatedV 1) (j + 1) =
      lanczosStep D.backwardH (lanczosState D.backwardH (D.dilatedV 1) j) from rfl,
    lanczosState_eq_of_orthonormal_recurrence h0 horth hrec D.β_zero hβ hβpos j hj,
    (lanczosStep_of_orthonormal_recurrence horth hrec hβ hj).2]

end LanczosData

end NLAlib
