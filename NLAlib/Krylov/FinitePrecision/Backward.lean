/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.Normalized
public import NLAlib.Matrix.Subspaces.OrthonormalDilation
public import NLAlib.Krylov.Processes.LanczosRecurrence
public import NLAlib.Matrix.Norms.Projector

/-!
# A backward model for finite-precision Lanczos

The computed tridiagonal matrix of a run `L : NLAlib.LanczosRun n k` is exactly what $k$ steps of
exact Lanczos produce on a symmetric matrix $\tilde{\mathbf{H}}$ of dimension $n(k+1)$ that is
close to $\mathbf{I}_{k+1} \otimes \mathbf{H}$, from a starting vector whose spectral weights
with respect to $\mathbf{I}_{k+1} \otimes \mathbf{H}$ are those of the normalised
$\bar{\mathbf{v}}_1$ with respect to $\mathbf{H}$ (a Greenbaum-type backward model, with a
perturbation of order $k^4\varepsilon\|\mathbf{H}\|_2$).

The construction: normalise the computed vectors (`NLAlib.LanczosRun.normalized`, whose local
errors stay of order $j\varepsilon\|\mathbf{H}\|_2$); dilate them to orthonormal vectors
(`NLAlib.orthonormalDilation`), which satisfy the computed recurrence with the computed
coefficients up to a residual $\hat{\mathbf{E}}$ (`NLAlib.LanczosRun.dilatedResidual`),
controlled through the Gram commutator of the normalised vectors; remove the residual by the
symmetric perturbation
$\mathbf{\Delta} = -\hat{\mathbf{E}}\hat{\mathbf{V}}_k^{\mathsf{T}} -
\hat{\mathbf{V}}_k\hat{\mathbf{E}}^{\mathsf{T}}(\mathbf{I} - \hat{\mathbf{V}}_k
\hat{\mathbf{V}}_k^{\mathsf{T}})$.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `sec:backward`, `lem:normalized-errors`, `cor:normalized-commutator`,
`lem:exchange`, `lem:dilated-recurrence`, `thm:greenbaum`; [Greenbaum1989] for the original
model (perturbation of order $\varepsilon^{1/4}$), [Paige2010] for the augmented model of
dimension $n + k$.

## Main definitions

* `NLAlib.LanczosRun.dilatedH`, `NLAlib.LanczosRun.dilatedBasisSucc`,
  `NLAlib.LanczosRun.dilatedBasis`, `NLAlib.LanczosRun.dilatedStart`,
  `NLAlib.LanczosRun.dilatedResidual`: the dilated recurrence.
* `NLAlib.LanczosRun.backwardPerturbation`, `NLAlib.LanczosRun.backwardH`: the backward model.
* `NLAlib.lanczosDilatedResidualFactor`, `NLAlib.lanczosBackwardFactor`: the factors of the
  two bounds, <!-- value lanczosDilatedResidualFactor k --> $1000k^4$ and twice that,
  that is <!-- value lanczosBackwardFactor k --> $2000k^4$.

The construction and its exact properties are stated for any symmetric three-term datum with unit
vectors (`NLAlib.LanczosData.dilatedResidual`, `NLAlib.LanczosData.backwardH`,
`NLAlib.LanczosData.frobNorm_dilatedResidual_le_of_le`, with the recurrence residual and the
Gram commutator as inputs); the run versions are their instances for `L.normalized`.

## Main results

* `NLAlib.LanczosData.frobNorm_dilatedResidual_le_of_le`,
  `NLAlib.LanczosData.frobNorm_backwardH_sub_dilatedH_le_two_mul`: the general bounds.
* `NLAlib.LanczosRun.frobNorm_dilatedResidual_le`: the dilated recurrence.
* `NLAlib.LanczosRun.backwardH_mul_dilatedBasis`,
  `NLAlib.LanczosRun.frobNorm_backwardH_sub_dilatedH_le`: the backward model.
* `NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`,
  `NLAlib.LanczosRun.lanczosAlpha_backwardH_dilatedStart`,
  `NLAlib.LanczosRun.lanczosState_backwardH_dilatedStart_succ_beta`: exact Lanczos on the model
  computes $\mathbf{T}_k$ and the coefficients.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-! ### Leading blocks of upper triangular matrices -/

/-- Dropping the last column of $\mathbf{B}\mathbf{X}$, for $\mathbf{X}$ upper triangular, is
$\mathbf{B}$ without its last column times the leading block of $\mathbf{X}$. -/
private theorem submatrix_castSucc_mul {p : Type*} {m : ℕ} (B : Matrix p (Fin (m + 1)) ℝ)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hX : X.IsUpperTriangular) :
    (B * X).submatrix id Fin.castSucc =
      B.submatrix id Fin.castSucc * X.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [Matrix.submatrix_apply, id, Matrix.mul_apply]
  rw [Fin.sum_univ_castSucc,
    show X (Fin.last m) (Fin.castSucc j) = 0 from hX (Fin.castSucc_lt_last j), mul_zero, add_zero]

/-- The leading block of a product with an upper triangular right factor is the product of the
leading blocks. -/
private theorem submatrix_castSucc_mul_castSucc {m : ℕ}
    (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hY : Y.IsUpperTriangular) :
    (X * Y).submatrix Fin.castSucc Fin.castSucc =
      X.submatrix Fin.castSucc Fin.castSucc * Y.submatrix Fin.castSucc Fin.castSucc := by
  have h := submatrix_castSucc_mul X hY
  ext i j
  have := congrFun (congrFun h (Fin.castSucc i)) j
  simpa only [Matrix.submatrix_apply, id, Matrix.mul_apply] using this

/-- Block $r$ of $(\mathbf{I} \otimes \mathbf{H})\mathbf{M}$ is $\mathbf{H}$ times block $r$ of
$\mathbf{M}$. -/
private theorem submatrix_blockDiagonal_mul {n m : ℕ} {p : Type*}
    (H : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin n × Fin m) p ℝ) (r : Fin m) :
    (Matrix.blockDiagonal (fun _ : Fin m => H) * M).submatrix (fun i => (i, r)) id =
      H * M.submatrix (fun i => (i, r)) id := by
  ext i j
  simp only [Matrix.submatrix_apply, id, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The squared Frobenius norm of a matrix with rows indexed by blocks is the sum over the
blocks. -/
private theorem frobNorm_sq_eq_sum_submatrix {n m : ℕ} {p : Type*} [Fintype p]
    (M : Matrix (Fin n × Fin m) p ℝ) :
    frobNorm M ^ 2 = ∑ r, frobNorm (M.submatrix (fun i => (i, r)) id) ^ 2 := by
  simp only [frobNorm_sq_eq_sum_sq, Fintype.sum_prod_type, Matrix.submatrix_apply, id]
  exact Finset.sum_comm

/-- **The factor of the dilated residual bound** of a finite-precision Lanczos run of $k$ steps
(`NLAlib.LanczosRun.frobNorm_dilatedResidual_le`, Frobenius
norm): <!-- value lanczosDilatedResidualFactor k -->
$$1000k^4 \,.$$
The maintainer's draft states the bound as $\lesssim_k \varepsilon\|\mathbf{A}\|_2$; its
formalization has the factor $240000k^6$, in the spectral norm. -/
noncomputable irreducible_def lanczosDilatedResidualFactor (k : ℕ) : ℝ := 1000 * (k : ℝ) ^ 4

/-- **The factor of the backward perturbation** of a finite-precision Lanczos run of $k$ steps
(`NLAlib.LanczosRun.frobNorm_backwardH_sub_dilatedH_le`, Frobenius norm), twice the dilated
residual factor: <!-- value lanczosBackwardFactor k -->
$$2000k^4 \,.$$
The maintainer's draft states the bound as $\lesssim_k \varepsilon\|\mathbf{A}\|_2$; its
formalization has the factor $480000k^6$, in the spectral norm. -/
noncomputable irreducible_def lanczosBackwardFactor (k : ℕ) : ℝ := 2000 * (k : ℝ) ^ 4

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
    submatrix_castSucc_mul W hCKr, hW]
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
  rw [pow_succ, submatrix_castSucc_mul_castSucc _ hK, pow_one]
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
    rw [← submatrix_castSucc_mul_castSucc _ (isUpperTriangular_dilationC W),
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

/-- **The dilated recurrence, from the residual and the Gram commutator**: for unit vectors,
$\|\mathbf{F}_k\|_{\mathsf{F}} \le F$ and $\|\mathbf{M}_k\|_2 \le G$,
$$\|\hat{\mathbf{E}}\|_{\mathsf{F}} \le 2\sqrt{k+1}\,F + 4(k+1)(2k+1)\,G \,.$$
No printed source; the maintainer's draft, `lem:exchange` and `lem:dilated-recurrence`. -/
theorem frobNorm_dilatedResidual_le_of_le (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1)
    {F G : ℝ} (hF : frobNorm D.residual ≤ F) (hG : specNorm D.gramCommutator ≤ G) :
    frobNorm D.dilatedResidual ≤
      2 * Real.sqrt (k + 1) * F + 4 * ((k + 1) * (2 * k + 1)) * G := by
  set W := D.basisSucc
  have hF0 : 0 ≤ F := (frobNorm_nonneg _).trans hF
  have hG0 : 0 ≤ G := (specNorm_nonneg _).trans hG
  have hY1 := D.specNorm_exchangeDefect_one_le hW hG
  set c := 2 * F + Real.sqrt (k + 1) * ((2 * k + 1) * (4 * G))
  have hblock : ∀ r : Fin (k + 1),
      frobNorm (D.dilatedResidual.submatrix (fun i => (i, r)) id) ≤ c := by
    intro r
    have hr : ((r : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp r.2
    have hCK : specNorm ((dilationC W * dilationK W ^ (r : ℕ)).submatrix Fin.castSucc
        Fin.castSucc) ≤ 2 := by
      refine (specNorm_submatrix_le _ (Fin.castSucc_injective k)
        (Fin.castSucc_injective k)).trans ((specNorm_mul_le _ _).trans ?_)
      have h1 := specNorm_dilationC_le_two hW
      have h2 : specNorm (dilationK W ^ (r : ℕ)) ≤ 1 :=
        (specNorm_pow_le _ _).trans (pow_le_one₀ (specNorm_nonneg _)
          (specNorm_dilationK_le_one hW))
      calc _ ≤ 2 * 1 := mul_le_mul h1 h2 (specNorm_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    have hY : specNorm (D.exchangeDefect r - D.exchangeDefect (r + 1)) ≤
        (2 * k + 1) * (4 * G) := by
      refine (specNorm_sub_le _ _).trans ?_
      have h1 := D.specNorm_exchangeDefect_le hW r
      have h2 := D.specNorm_exchangeDefect_le hW (r + 1)
      push_cast at h2
      have hY0 := specNorm_nonneg (D.exchangeDefect 1)
      nlinarith
    rw [D.dilatedResidual_submatrix]
    refine (frobNorm_add_le _ _).trans ?_
    have e1 := frobNorm_mul_le_frobNorm_mul_specNorm D.residual
      ((dilationC W * dilationK W ^ (r : ℕ)).submatrix Fin.castSucc Fin.castSucc)
    have e2 := frobNorm_mul_le_frobNorm_mul_specNorm W
      (D.exchangeDefect r - D.exchangeDefect (r + 1))
    rw [D.frobNorm_basisSucc_of_unit hW] at e2
    have hs1 : 0 ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
    calc _ ≤ frobNorm D.residual * 2 + Real.sqrt (k + 1) * ((2 * k + 1) * (4 * G)) := by
          gcongr
          · exact e1.trans (mul_le_mul_of_nonneg_left hCK (frobNorm_nonneg _))
          · exact e2.trans (mul_le_mul_of_nonneg_left hY hs1)
      _ ≤ F * 2 + Real.sqrt (k + 1) * ((2 * k + 1) * (4 * G)) := by gcongr
      _ = c := by simp only [c]; ring
  have hc0 : 0 ≤ c := by positivity
  have hsq : frobNorm D.dilatedResidual ^ 2 ≤ (Real.sqrt (k + 1) * c) ^ 2 := by
    rw [frobNorm_sq_eq_sum_submatrix, mul_pow, Real.sq_sqrt (by positivity)]
    calc ∑ r, frobNorm (D.dilatedResidual.submatrix (fun i => (i, r)) id) ^ 2
        ≤ ∑ _r : Fin (k + 1), c ^ 2 :=
          Finset.sum_le_sum fun r _ => pow_le_pow_left₀ (frobNorm_nonneg _) (hblock r) 2
      _ = (k + 1) * c ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  refine ((sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).1 hsq).trans (le_of_eq ?_)
  have hsk : Real.sqrt (k + 1) * Real.sqrt (k + 1) = k + 1 := Real.mul_self_sqrt (by positivity)
  simp only [c]
  linear_combination (4 * (2 * (k : ℝ) + 1) * G) * hsk

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

/-- **The backward perturbation is at most twice the dilated residual**:
$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}} \le
2\|\hat{\mathbf{E}}\|_{\mathsf{F}}$. -/
theorem frobNorm_backwardH_sub_dilatedH_le_two_mul
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    frobNorm (D.backwardH - D.dilatedH) ≤ 2 * frobNorm D.dilatedResidual := by
  have hQ := D.hasOrthonormalCols_dilatedBasis hW
  have hQ1 : specNorm D.dilatedBasis ≤ 1 := hQ.specNorm_le_one
  have hQt : specNorm D.dilatedBasisᵀ ≤ 1 := by rw [specNorm_transpose]; exact hQ1
  have hP : specNorm (1 - D.dilatedBasis * D.dilatedBasisᵀ) ≤ 1 := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hQ.isStarProjection_mul_conjTranspose.one_sub.specNorm_le_one
  rw [backwardH, add_sub_cancel_left, backwardPerturbation]
  refine (frobNorm_sub_le _ _).trans ?_
  rw [frobNorm_neg]
  have h1 : frobNorm (D.dilatedResidual * D.dilatedBasisᵀ) ≤ frobNorm D.dilatedResidual :=
    (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
      (by simpa using mul_le_mul_of_nonneg_left hQt (frobNorm_nonneg D.dilatedResidual))
  have h2 : frobNorm (D.dilatedBasis * D.dilatedResidualᵀ *
      (1 - D.dilatedBasis * D.dilatedBasisᵀ)) ≤ frobNorm D.dilatedResidual := by
    rw [Matrix.mul_assoc]
    refine (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans ?_
    refine (mul_le_mul hQ1 ((frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
      (mul_le_mul_of_nonneg_left hP (frobNorm_nonneg _))) (frobNorm_nonneg _) zero_le_one).trans ?_
    rw [one_mul, mul_one, frobNorm_transpose]
  linarith

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

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-! ### The dilated recurrence

The constructions of `NLAlib.LanczosData` for the normalised run `L.normalized`, under the names
of the run. -/

/-- The **dilated matrix** $\hat{\mathbf{H}} = \mathbf{I}_{k+1} \otimes \mathbf{H}$, block
diagonal with $k + 1$ copies of $\mathbf{H}$. -/
def dilatedH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  Matrix.blockDiagonal fun _ => L.H

/-- The **dilated vectors** $\hat{\mathbf{V}}_{k+1}$: the orthonormal dilation of the normalised
vectors $\bar{\mathbf{v}}_1, \dots, \bar{\mathbf{v}}_{k+1}$. -/
noncomputable def dilatedBasisSucc : Matrix (Fin n × Fin (k + 1)) (Fin (k + 1)) ℝ :=
  orthonormalDilation L.normalized.basisSucc

/-- The first $k$ dilated vectors $\hat{\mathbf{V}}_k$. -/
noncomputable def dilatedBasis : Matrix (Fin n × Fin (k + 1)) (Fin k) ℝ :=
  L.dilatedBasisSucc.submatrix id Fin.castSucc

/-- The **dilated starting vector** $(\bar{\mathbf{v}}_1, \mathbf{0}, \dots, \mathbf{0})$. -/
noncomputable def dilatedStart : Fin n × Fin (k + 1) → ℝ :=
  fun p => if (p.2 : ℕ) = 0 then L.normalizedV 1 p.1 else 0

/-- The tridiagonal matrix with the extra row, $\underline{\mathbf{T}}_k$
(`NLAlib.LanczosData.tridiagonalSucc` of the run). -/
def tridiagonalSucc : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  L.toLanczosData.tridiagonalSucc

/-- The **residual of the dilated recurrence**
$\hat{\mathbf{E}} = \hat{\mathbf{H}}\hat{\mathbf{V}}_k - \hat{\mathbf{V}}_{k+1}
\underline{\mathbf{T}}_k$. -/
noncomputable def dilatedResidual : Matrix (Fin n × Fin (k + 1)) (Fin k) ℝ :=
  L.dilatedH * L.dilatedBasis - L.dilatedBasisSucc * L.tridiagonalSucc

/-- The normalised vectors have unit length: the Gram matrix of $\bar{\mathbf{V}}_{k+1}$ has unit
diagonal. -/
theorem transpose_basisSucc_mul_self_apply (j : Fin (k + 1)) :
    (L.normalized.basisSuccᵀ * L.normalized.basisSucc) j j = 1 :=
  L.normalized.transpose_basisSucc_mul_self_apply_of_norm
    (fun _ h1 h2 => L.norm_normalizedV h1 h2) j

/-- **The dilated vectors are orthonormal**. No printed source; the maintainer's draft,
`lem:dilation`. -/
theorem hasOrthonormalCols_dilatedBasisSucc : HasOrthonormalCols L.dilatedBasisSucc :=
  L.normalized.hasOrthonormalCols_dilatedBasisSucc L.transpose_basisSucc_mul_self_apply

/-- The first dilated vector is the dilated starting vector. No printed source; the maintainer's
draft, `lem:dilation`. -/
theorem dilatedBasisSucc_col_zero : L.dilatedBasisSucc.col 0 = L.dilatedStart :=
  L.normalized.dilatedBasisSucc_col_zero

/-- The **exchange defect** $\mathbf{Y}_r = \underline{\mathbf{T}}_k\mathbf{K}_k^r -
\mathbf{K}^r\underline{\mathbf{T}}_k$ of the dilation ($\mathbf{K}_k$ the leading block of
$\mathbf{K}$), which measures how far $\mathbf{K}^r$ is from intertwining
$\underline{\mathbf{T}}_k$ (`lem:exchange` of the maintainer's draft). -/
noncomputable def exchangeDefect (r : ℕ) : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  L.tridiagonalSucc *
      (dilationK L.normalized.basisSucc ^ r).submatrix Fin.castSucc Fin.castSucc -
    dilationK L.normalized.basisSucc ^ r * L.tridiagonalSucc

/-- Block $r$ of the dilated residual:
$\hat{\mathbf{E}}_r = \bar{\mathbf{F}}_k(\mathbf{C}\mathbf{K}^r)_k
+ \bar{\mathbf{V}}_{k+1}(\mathbf{Y}_r - \mathbf{Y}_{r+1})$. -/
theorem dilatedResidual_submatrix (r : Fin (k + 1)) :
    L.dilatedResidual.submatrix (fun i => (i, r)) id =
      L.normalized.residual * (dilationC L.normalized.basisSucc *
          dilationK L.normalized.basisSucc ^ (r : ℕ)).submatrix Fin.castSucc Fin.castSucc +
        L.normalized.basisSucc * (L.exchangeDefect r - L.exchangeDefect (r + 1)) :=
  L.normalized.dilatedResidual_submatrix r

/-- The exchange defects satisfy $\mathbf{Y}_{r+1} = \mathbf{Y}_r\mathbf{K}_k +
\mathbf{K}^r\mathbf{Y}_1$. -/
theorem exchangeDefect_succ (r : ℕ) :
    L.exchangeDefect (r + 1) =
      L.exchangeDefect r * (dilationK L.normalized.basisSucc).submatrix Fin.castSucc
          Fin.castSucc +
        dilationK L.normalized.basisSucc ^ r * L.exchangeDefect 1 :=
  L.normalized.exchangeDefect_succ r

/-- $\mathbf{Y}_0 = \mathbf{0}$. -/
theorem exchangeDefect_zero : L.exchangeDefect 0 = 0 :=
  L.normalized.exchangeDefect_zero

/-- **The exchange rule**: $\mathbf{Y}_1 = \mathbf{C}(\underline{\mathbf{T}}_k\mathbf{R}_k -
\mathbf{R}\underline{\mathbf{T}}_k)\mathbf{C}_k$. No printed source; the maintainer's draft,
`eq:L-commutator`; [Paige2010, (3.9)]. -/
theorem exchangeDefect_one :
    L.exchangeDefect 1 = dilationC L.normalized.basisSucc *
      (L.tridiagonalSucc * (strictUpperGram L.normalized.basisSucc).submatrix Fin.castSucc
          Fin.castSucc - strictUpperGram L.normalized.basisSucc * L.tridiagonalSucc) *
      (dilationC L.normalized.basisSucc).submatrix Fin.castSucc Fin.castSucc :=
  L.normalized.exchangeDefect_one

/-- The commutator of the normalised Gram matrix with $\underline{\mathbf{T}}_k$ is the
normalised Gram commutator with a zero last row:
$\underline{\mathbf{T}}_k\mathbf{R}_k - \mathbf{R}\underline{\mathbf{T}}_k =
\mathbf{J}\bar{\mathbf{M}}_k$, $\mathbf{J}$ the first $k$ columns of $\mathbf{I}_{k+1}$. -/
theorem tridiagonalSucc_mul_sub_eq :
    L.tridiagonalSucc * (strictUpperGram L.normalized.basisSucc).submatrix Fin.castSucc
        Fin.castSucc - strictUpperGram L.normalized.basisSucc * L.tridiagonalSucc =
      (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).submatrix id Fin.castSucc *
        L.normalized.gramCommutator :=
  L.normalized.tridiagonalSucc_mul_sub_eq

/-- The normalised basis with the next vector has Frobenius norm $\sqrt{k + 1}$. -/
theorem frobNorm_normalized_basisSucc :
    frobNorm L.normalized.basisSucc = Real.sqrt (k + 1) :=
  L.normalized.frobNorm_basisSucc_of_unit L.transpose_basisSucc_mul_self_apply

/-- **The exchange rule, bounds**: $\|\mathbf{Y}_1\|_2 \le 160k^2\varepsilon\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `lem:exchange`. -/
theorem specNorm_exchangeDefect_one_le :
    specNorm (L.exchangeDefect 1) ≤ 160 * k ^ 2 * L.ε * specNorm L.H := by
  have h := L.normalized.specNorm_exchangeDefect_one_le L.transpose_basisSucc_mul_self_apply
    L.specNorm_normalized_gramCommutator_le
  exact h.trans_eq (by ring)

/-- The exchange defects grow at most linearly: $\|\mathbf{Y}_r\|_2 \le r\|\mathbf{Y}_1\|_2$. -/
theorem specNorm_exchangeDefect_le (r : ℕ) :
    specNorm (L.exchangeDefect r) ≤ r * specNorm (L.exchangeDefect 1) :=
  L.normalized.specNorm_exchangeDefect_le L.transpose_basisSucc_mul_self_apply r

/-- **The dilated recurrence** (the exchange rule and the dilated residual): the orthonormal
dilated vectors satisfy the computed recurrence with the computed coefficients up
to <!-- value lanczosDilatedResidualFactor k -->
$$\|\hat{\mathbf{E}}\|_{\mathsf{F}} =
\|\hat{\mathbf{H}}\hat{\mathbf{V}}_k - \hat{\mathbf{V}}_{k+1}\underline{\mathbf{T}}_k\|_{\mathsf{F}}
\le 1000k^4\varepsilon\|\mathbf{H}\|_2 \,.$$
No printed source; the maintainer's draft, `lem:exchange` and `lem:dilated-recurrence`, state
$\lesssim_k \varepsilon\|\mathbf{A}\|_2$ (its formalization: $240000k^6$ in the spectral norm).
Result: lanczos-dilated-recurrence -/
theorem frobNorm_dilatedResidual_le :
    frobNorm L.dilatedResidual ≤ lanczosDilatedResidualFactor k * L.ε * specNorm L.H := by
  rw [lanczosDilatedResidualFactor_def]
  have hε0 := L.ε_nonneg
  have hH := specNorm_nonneg L.H
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.k_pos
  set A := L.ε * specNorm L.H with hA
  have hA0 : 0 ≤ A := by positivity
  have hE := L.normalized.frobNorm_dilatedResidual_le_of_le L.transpose_basisSucc_mul_self_apply
    L.frobNorm_normalized_residual_le L.specNorm_normalized_gramCommutator_le
  refine hE.trans ?_
  have hss : Real.sqrt (k + 1) * Real.sqrt k ≤ 3 / 2 * k := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have : 2 * Real.sqrt (k + 1) * (12 * k * Real.sqrt k * L.ε * specNorm L.H) +
      4 * ((k + 1) * (2 * k + 1)) * (40 * k ^ 2 * L.ε * specNorm L.H) =
      (24 * k * (Real.sqrt (k + 1) * Real.sqrt k) +
        (k + 1) * (2 * k + 1) * (160 * k ^ 2)) * A := by
    simp only [hA]; ring
  rw [this]
  have hpoly : 24 * (k : ℝ) * (3 / 2 * k) + (k + 1) * (2 * k + 1) * (160 * k ^ 2) ≤
      1000 * (k : ℝ) ^ 4 := by
    have h2 : (k : ℝ) ≤ k ^ 2 := by nlinarith
    have h3 : (k : ℝ) ^ 2 ≤ k ^ 3 := by nlinarith
    have h4 : (k : ℝ) ^ 3 ≤ k ^ 4 := by nlinarith
    nlinarith
  calc (24 * k * (Real.sqrt (k + 1) * Real.sqrt k) + (k + 1) * (2 * k + 1) * (160 * k ^ 2)) * A
      ≤ (24 * k * (3 / 2 * k) + (k + 1) * (2 * k + 1) * (160 * k ^ 2)) * A := by gcongr
    _ ≤ 1000 * k ^ 4 * A := by gcongr
    _ = 1000 * k ^ 4 * L.ε * specNorm L.H := by rw [hA]; ring

/-! ### The backward model -/

/-- The **backward perturbation**
$\mathbf{\Delta} = -\hat{\mathbf{E}}\hat{\mathbf{V}}_k^{\mathsf{T}} -
\hat{\mathbf{V}}_k\hat{\mathbf{E}}^{\mathsf{T}}(\mathbf{I} - \hat{\mathbf{V}}_k
\hat{\mathbf{V}}_k^{\mathsf{T}})$. -/
noncomputable def backwardPerturbation : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  -(L.dilatedResidual * L.dilatedBasisᵀ) -
    L.dilatedBasis * L.dilatedResidualᵀ * (1 - L.dilatedBasis * L.dilatedBasisᵀ)

/-- The **backward model** $\tilde{\mathbf{H}} = \mathbf{I}_{k+1} \otimes \mathbf{H} +
\mathbf{\Delta}$. -/
noncomputable def backwardH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  L.dilatedH + L.backwardPerturbation

/-- The backward model of the run is that of its normalised run. -/
theorem backwardH_eq_normalized_backwardH : L.backwardH = L.normalized.backwardH :=
  rfl

/-- The first $k$ dilated vectors are orthonormal. -/
theorem hasOrthonormalCols_dilatedBasis : HasOrthonormalCols L.dilatedBasis :=
  L.normalized.hasOrthonormalCols_dilatedBasis L.transpose_basisSucc_mul_self_apply

/-- $\hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{V}}_{k+1}\underline{\mathbf{T}}_k
= \mathbf{T}_k$. -/
theorem transpose_dilatedBasis_mul_dilatedBasisSucc_mul :
    L.dilatedBasisᵀ * (L.dilatedBasisSucc * L.tridiagonalSucc) = L.tridiagonal :=
  L.normalized.transpose_dilatedBasis_mul_dilatedBasisSucc_mul
    L.transpose_basisSucc_mul_self_apply

/-- $\hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{E}}$ is symmetric:
$\hat{\mathbf{E}}^{\mathsf{T}}\hat{\mathbf{V}}_k
= \hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{E}}$. -/
theorem transpose_dilatedResidual_mul_dilatedBasis :
    L.dilatedResidualᵀ * L.dilatedBasis = L.dilatedBasisᵀ * L.dilatedResidual :=
  L.normalized.transpose_dilatedResidual_mul_dilatedBasis L.transpose_basisSucc_mul_self_apply

/-- The backward model is symmetric. -/
theorem transpose_backwardH : L.backwardHᵀ = L.backwardH :=
  L.normalized.transpose_backwardH L.transpose_basisSucc_mul_self_apply

/-- **The backward model satisfies the computed recurrence exactly**:
$\tilde{\mathbf{H}}\hat{\mathbf{V}}_k = \hat{\mathbf{V}}_{k+1}\underline{\mathbf{T}}_k$ with
$\hat{\mathbf{V}}_{k+1}$ orthonormal. No printed source; the maintainer's draft, `thm:greenbaum`. -/
theorem backwardH_mul_dilatedBasis :
    L.backwardH * L.dilatedBasis = L.dilatedBasisSucc * L.tridiagonalSucc :=
  L.normalized.backwardH_mul_dilatedBasis L.transpose_basisSucc_mul_self_apply

/-- **Greenbaum-type backward model for finite-precision Lanczos**: the symmetric backward model
$\tilde{\mathbf{H}}$ is close to $\mathbf{I}_{k+1} \otimes
\mathbf{H}$, <!-- value lanczosBackwardFactor k -->
$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}}
\le 2000k^4\varepsilon\|\mathbf{H}\|_2 \,,$$
and it satisfies the computed recurrence exactly with orthonormal vectors
(`NLAlib.LanczosRun.backwardH_mul_dilatedBasis`), so exact Lanczos on it from the dilated
starting vector computes $\mathbf{T}_k$ and $\beta_k$
(`NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`).
No printed source; the maintainer's draft, `thm:greenbaum`, states
$\|\mathbf{\Delta}\|_2 \lesssim_k \varepsilon\|\mathbf{A}\|_2$ (its formalization:
$480000k^6$ in the spectral norm); the Frobenius norm here is at least the spectral norm.
[Greenbaum1989, (7.10)] has a perturbation of order $\varepsilon^{1/4}$.
Result: greenbaum-backward-model -/
theorem frobNorm_backwardH_sub_dilatedH_le :
    frobNorm (L.backwardH - L.dilatedH) ≤ lanczosBackwardFactor k * L.ε * specNorm L.H := by
  have hE := L.frobNorm_dilatedResidual_le
  rw [lanczosDilatedResidualFactor_def] at hE
  rw [lanczosBackwardFactor_def]
  have h := L.normalized.frobNorm_backwardH_sub_dilatedH_le_two_mul
    L.transpose_basisSucc_mul_self_apply
  change frobNorm (L.backwardH - L.dilatedH) ≤ 2 * frobNorm L.dilatedResidual at h
  linarith

/-- The dilated vectors as a sequence: $\hat{\mathbf{u}}_m$ is column  - 1$ of
$\hat{\mathbf{V}}_{k+1}$ for  \le m \le k + 1$, and $\mathbf{0}$ otherwise. -/
noncomputable def dilatedV (m : ℕ) : Fin n × Fin (k + 1) → ℝ :=
  fun p => if h : 1 ≤ m ∧ m ≤ k + 1 then L.dilatedBasisSucc p ⟨m - 1, by omega⟩ else 0

/-- **Exact Lanczos on the backward model computes the computed tridiagonal matrix**: $k$ steps
of the Lanczos recurrence on $\tilde{\mathbf{H}}$ from
$(\bar{\mathbf{v}}_1, \mathbf{0}, \dots, \mathbf{0})$ give $\mathbf{T}_k$.
No printed source; the maintainer's draft, `thm:greenbaum`. -/
theorem lanczosTridiagonal_backwardH_dilatedStart :
    lanczosTridiagonal L.backwardH L.dilatedStart k = L.tridiagonal :=
  LanczosData.lanczosTridiagonal_backwardH_dilatedStart (D := L.normalized)
    L.transpose_basisSucc_mul_self_apply L.β_nonneg L.β_pos

/-- Exact Lanczos on the backward model computes the dilated vectors:
`lanczosMatrix` of $\tilde{\mathbf{H}}$ from the dilated start is $\hat{\mathbf{V}}_k$. -/
theorem lanczosMatrix_backwardH_dilatedStart :
    lanczosMatrix L.backwardH L.dilatedStart k = L.dilatedBasis :=
  LanczosData.lanczosMatrix_backwardH_dilatedStart (D := L.normalized)
    L.transpose_basisSucc_mul_self_apply L.β_nonneg L.β_pos

/-- Exact Lanczos on the backward model computes the last coefficient: $\beta_k$ is the
coefficient of the state after $k$ steps. -/
theorem lanczosState_backwardH_dilatedStart_beta :
    (lanczosState L.backwardH L.dilatedStart k).beta = L.β k :=
  LanczosData.lanczosState_backwardH_dilatedStart_beta (D := L.normalized)
    L.transpose_basisSucc_mul_self_apply L.β_nonneg L.β_pos

/-- Exact Lanczos on the backward model computes the computed diagonal coefficients: for
$j < k$, the coefficient $\alpha$ of step $j$ of the Lanczos recurrence on
$\tilde{\mathbf{H}}$ from the dilated start is $\alpha_{j+1}$. -/
theorem lanczosAlpha_backwardH_dilatedStart {j : ℕ} (hj : j < k) :
    lanczosAlpha L.backwardH (lanczosState L.backwardH L.dilatedStart j) = L.α (j + 1) :=
  LanczosData.lanczosAlpha_backwardH_dilatedStart (D := L.normalized)
    L.transpose_basisSucc_mul_self_apply L.β_nonneg L.β_pos hj

/-- Exact Lanczos on the backward model computes the computed off-diagonal coefficients: for
$j < k$, the coefficient $\beta$ of the state after $j + 1$ steps of the Lanczos recurrence on
$\tilde{\mathbf{H}}$ from the dilated start is $\beta_{j+1}$. -/
theorem lanczosState_backwardH_dilatedStart_succ_beta {j : ℕ} (hj : j < k) :
    (lanczosState L.backwardH L.dilatedStart (j + 1)).beta = L.β (j + 1) :=
  LanczosData.lanczosState_backwardH_dilatedStart_succ_beta (D := L.normalized)
    L.transpose_basisSucc_mul_self_apply L.β_nonneg L.β_pos hj

end LanczosRun

end NLAlib
