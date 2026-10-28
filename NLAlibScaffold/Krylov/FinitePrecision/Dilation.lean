/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.LanczosData

/-!
# An orthonormal dilation of unit vectors

For $m$ unit vectors, the columns of $\mathbf{W} \in \mathbb{R}^{n \times m}$, split the Gram
matrix as $\mathbf{W}^{\mathsf{T}}\mathbf{W} = \mathbf{I} + \mathbf{R} + \mathbf{R}^{\mathsf{T}}$
with $\mathbf{R}$ strictly upper triangular, and put $\mathbf{C} = (\mathbf{I} + \mathbf{R})^{-1}$
(the finite Neumann series, $\mathbf{R}$ being nilpotent) and $\mathbf{K} = \mathbf{I} - \mathbf{C}
= \mathbf{R}\mathbf{C}$. Then $\mathbf{C}^{\mathsf{T}}\mathbf{W}^{\mathsf{T}}\mathbf{W}\mathbf{C}
= \mathbf{I} - \mathbf{K}^{\mathsf{T}}\mathbf{K}$, and the $m$ stacked blocks
$\mathbf{W}\mathbf{C}\mathbf{K}^r$, $r < m$, form a matrix with orthonormal columns (the sum
telescopes, $\mathbf{K}^m = \mathbf{0}$) whose first column is $\mathbf{w}_0$ in the first block.
This is Paige's unitary augmentation iterated until it closes, the isometric dilation of a
contraction.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `eq:CKsy`, `eq:dilation-def`, `lem:dilation`, `eq:CGC-identity`.

## Main definitions

* `NLAlib.strictUpperGram`, `NLAlib.dilationC`, `NLAlib.dilationK`, `NLAlib.orthonormalDilation`.

## Main results

* `NLAlib.transpose_dilationC_mul_mul_dilationC`: the identity
  $\mathbf{C}^{\mathsf{T}}\mathbf{W}^{\mathsf{T}}\mathbf{W}\mathbf{C} = \mathbf{I} -
  \mathbf{K}^{\mathsf{T}}\mathbf{K}$.
* `NLAlib.hasOrthonormalCols_orthonormalDilation`,
  `NLAlib.orthonormalDilation_apply_of_val_eq_zero`: the dilation.
* `NLAlib.specNorm_dilationK_le_one`, `NLAlib.specNorm_dilationC_le_two`.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

variable {n m : ℕ}

/-- The **strict upper triangle of the Gram matrix** of the columns of $\mathbf{W}$:
$\mathbf{R}_{i,j} = \mathbf{w}_i^{\mathsf{T}}\mathbf{w}_j$ for $i < j$, and $0$ otherwise. -/
def strictUpperGram (W : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => if i < j then (Wᵀ * W) i j else 0

/-- $\mathbf{C} = (\mathbf{I} + \mathbf{R})^{-1} = \sum_{r < m} (-\mathbf{R})^r$, a finite sum
because $\mathbf{R}^m = \mathbf{0}$. -/
def dilationC (W : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ r ∈ Finset.range m, (-strictUpperGram W) ^ r

/-- $\mathbf{K} = \mathbf{I} - \mathbf{C}$, strictly upper triangular. -/
def dilationK (W : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  1 - dilationC W

/-- The **orthonormal dilation** of the columns of $\mathbf{W}$: the $m$ stacked blocks
$\mathbf{W}\mathbf{C}\mathbf{K}^r$, $r < m$; row $(i, r)$ is row $i$ of block $r$. -/
def orthonormalDilation (W : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n × Fin m) (Fin m) ℝ :=
  Matrix.of fun p j => (W * dilationC W * dilationK W ^ (p.2 : ℕ)) p.1 j

/-- $\mathbf{R}$ is strictly upper triangular: $\mathbf{R}_{i,j} = 0$ for $j \le i$. -/
theorem strictUpperGram_apply_of_le (W : Matrix (Fin n) (Fin m) ℝ) {i j : Fin m} (h : j ≤ i) :
    strictUpperGram W i j = 0 := by
  simp only [strictUpperGram, Matrix.of_apply, if_neg (not_lt.mpr h)]

/-- Powers of a strictly upper triangular matrix: if $\mathbf{X}_{i,j} = 0$ for $j \le i$, then
$(\mathbf{X}^r)_{i,j} = 0$ for $j < i + r$. -/
private theorem pow_apply_eq_zero_of_lt {X : Matrix (Fin m) (Fin m) ℝ}
    (hX : ∀ i j : Fin m, j ≤ i → X i j = 0) (r : ℕ) :
    ∀ i j : Fin m, (j : ℕ) < i + r → (X ^ r) i j = 0 := by
  induction r with
  | zero =>
    intro i j h
    rw [pow_zero, Matrix.one_apply_ne]
    exact fun h' => by rw [h'] at h; omega
  | succ r ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) < i + r
    · rw [ih i l hl, zero_mul]
    · rw [hX l j (by rw [Fin.le_def]; omega), mul_zero]

/-- $\mathbf{R}^m = \mathbf{0}$. -/
theorem strictUpperGram_pow_eq_zero (W : Matrix (Fin n) (Fin m) ℝ) :
    strictUpperGram W ^ m = 0 := by
  ext i j
  rw [pow_apply_eq_zero_of_lt (fun i j h => strictUpperGram_apply_of_le W h) m i j (by omega)]
  rfl

/-- $\mathbf{C}$ inverts $\mathbf{I} + \mathbf{R}$: $(\mathbf{I} + \mathbf{R})\mathbf{C} =
\mathbf{I}$. -/
theorem one_add_strictUpperGram_mul_dilationC (W : Matrix (Fin n) (Fin m) ℝ) :
    (1 + strictUpperGram W) * dilationC W = 1 := by
  have h := mul_neg_geom_sum (-strictUpperGram W) m
  rw [sub_neg_eq_add, neg_pow, strictUpperGram_pow_eq_zero, mul_zero, sub_zero] at h
  exact h

/-- $\mathbf{C}(\mathbf{I} + \mathbf{R}) = \mathbf{I}$. -/
theorem dilationC_mul_one_add_strictUpperGram (W : Matrix (Fin n) (Fin m) ℝ) :
    dilationC W * (1 + strictUpperGram W) = 1 := by
  have h := geom_sum_mul_neg (-strictUpperGram W) m
  rw [sub_neg_eq_add, neg_pow, strictUpperGram_pow_eq_zero, mul_zero, sub_zero] at h
  exact h

/-- $\mathbf{K} = \mathbf{R}\mathbf{C}$. -/
theorem dilationK_eq_strictUpperGram_mul (W : Matrix (Fin n) (Fin m) ℝ) :
    dilationK W = strictUpperGram W * dilationC W := by
  have h := one_add_strictUpperGram_mul_dilationC W
  rw [add_mul, one_mul] at h
  rw [dilationK, ← h]
  abel

/-- $\mathbf{K} = \mathbf{C}\mathbf{R}$. -/
theorem dilationK_eq_dilationC_mul (W : Matrix (Fin n) (Fin m) ℝ) :
    dilationK W = dilationC W * strictUpperGram W := by
  have h := dilationC_mul_one_add_strictUpperGram W
  rw [mul_add, mul_one] at h
  rw [dilationK, ← h]
  abel

/-- $\mathbf{K}^m = \mathbf{0}$. -/
theorem dilationK_pow_eq_zero (W : Matrix (Fin n) (Fin m) ℝ) : dilationK W ^ m = 0 := by
  have hc : Commute (strictUpperGram W) (dilationC W) := by
    rw [Commute, SemiconjBy, ← dilationK_eq_strictUpperGram_mul, ← dilationK_eq_dilationC_mul]
  rw [dilationK_eq_strictUpperGram_mul, hc.mul_pow, strictUpperGram_pow_eq_zero, zero_mul]

/-- $\mathbf{C}$ is upper triangular. -/
theorem isUpperTriangular_dilationC (W : Matrix (Fin n) (Fin m) ℝ) :
    (dilationC W).IsUpperTriangular := by
  have hR : (strictUpperGram W).IsUpperTriangular := fun i j h =>
    strictUpperGram_apply_of_le W h.le
  unfold dilationC
  induction Finset.range m using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Matrix.blockTriangular_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hR.neg.pow a).add ih

/-- $\mathbf{K}$ is upper triangular. -/
theorem isUpperTriangular_dilationK (W : Matrix (Fin n) (Fin m) ℝ) :
    (dilationK W).IsUpperTriangular :=
  Matrix.blockTriangular_one.sub (isUpperTriangular_dilationC W)

/-- $\mathbf{K}$ is strictly upper triangular: $\mathbf{K}_{i,j} = 0$ for $j \le i$. -/
theorem dilationK_apply_of_le (W : Matrix (Fin n) (Fin m) ℝ) {i j : Fin m} (h : j ≤ i) :
    dilationK W i j = 0 := by
  rw [dilationK_eq_strictUpperGram_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l ≤ i
  · rw [strictUpperGram_apply_of_le W hl, zero_mul]
  · rw [isUpperTriangular_dilationC W (show j < l from lt_of_le_of_lt h (not_le.mp hl)),
      mul_zero]

/-- **The Gram identity of the dilation**: for unit columns,
$\mathbf{C}^{\mathsf{T}}\mathbf{W}^{\mathsf{T}}\mathbf{W}\mathbf{C} = \mathbf{I} -
\mathbf{K}^{\mathsf{T}}\mathbf{K}$. No printed source; the maintainer's draft,
`eq:CGC-identity`; [Paige2009, Theorem 2.1] in the form of a unitary augmentation. -/
theorem transpose_dilationC_mul_mul_dilationC {W : Matrix (Fin n) (Fin m) ℝ}
    (hW : ∀ j, (Wᵀ * W) j j = 1) :
    (dilationC W)ᵀ * (Wᵀ * W) * dilationC W = 1 - (dilationK W)ᵀ * dilationK W := by
  set R := strictUpperGram W
  set C := dilationC W
  set K := dilationK W
  have hG : Wᵀ * W = (1 + R) + Rᵀ := by
    ext i j
    simp only [R, strictUpperGram, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.one_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_neg h.ne, if_pos h, if_neg (lt_asymm h)]
      ring
    · rw [if_pos rfl, if_neg (lt_irrefl _), hW]
      ring
    · rw [if_neg h.ne', if_neg (lt_asymm h), if_pos h, ← Matrix.transpose_apply (Wᵀ * W),
        Matrix.transpose_mul, Matrix.transpose_transpose]
      ring
  have hRC : R * C = K := (dilationK_eq_strictUpperGram_mul W).symm
  have h1 : (1 + R) * C = 1 := one_add_strictUpperGram_mul_dilationC W
  have hC : C = 1 - K := by simp only [K, dilationK]; abel
  rw [hG, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h1, Matrix.mul_one,
    show Cᵀ * Rᵀ * C = (R * C)ᵀ * C by rw [Matrix.transpose_mul], hRC]
  conv_lhs => rw [hC]
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one]
  abel

/-- **The dilation has orthonormal columns**: for unit columns of $\mathbf{W}$, the stacked
blocks $\mathbf{W}\mathbf{C}\mathbf{K}^r$, $r < m$, have orthonormal columns.
No printed source; the maintainer's draft, `lem:dilation`. -/
theorem hasOrthonormalCols_orthonormalDilation {W : Matrix (Fin n) (Fin m) ℝ}
    (hW : ∀ j, (Wᵀ * W) j j = 1) : HasOrthonormalCols (orthonormalDilation W) := by
  set C := dilationC W
  set K := dilationK W
  have hblock : (orthonormalDilation W)ᴴ * orthonormalDilation W =
      ∑ r ∈ Finset.range m, ((K ^ r)ᵀ * K ^ r - (K ^ (r + 1))ᵀ * K ^ (r + 1)) := by
    have hr : ∀ r : ℕ, (W * C * K ^ r)ᵀ * (W * C * K ^ r) =
        (K ^ r)ᵀ * K ^ r - (K ^ (r + 1))ᵀ * K ^ (r + 1) := by
      intro r
      have h := transpose_dilationC_mul_mul_dilationC hW
      rw [Matrix.transpose_mul, Matrix.transpose_mul]
      calc (K ^ r)ᵀ * (Cᵀ * Wᵀ) * (W * C * K ^ r)
          = (K ^ r)ᵀ * (Cᵀ * (Wᵀ * W) * C) * K ^ r := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [h, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, pow_succ', Matrix.transpose_mul]
          simp only [Matrix.mul_assoc, K]
    ext j l
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_apply, Fintype.sum_prod_type,
      Finset.sum_comm, Matrix.sum_apply,
      ← Fin.sum_univ_eq_sum_range (fun r => ((K ^ r)ᵀ * K ^ r - (K ^ (r + 1))ᵀ * K ^ (r + 1)) j l)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← hr, Matrix.mul_apply]
    rfl
  rw [HasOrthonormalCols, hblock, Finset.sum_range_sub' (fun r => (K ^ r)ᵀ * K ^ r),
    dilationK_pow_eq_zero, pow_zero, Matrix.transpose_one, Matrix.mul_one,
    Matrix.transpose_zero, Matrix.zero_mul, sub_zero]

/-- The first column of the dilation is $\mathbf{w}_0$ in the first block and $\mathbf{0}$ in
the others. No printed source; the maintainer's draft, `lem:dilation`. -/
theorem orthonormalDilation_apply_of_val_eq_zero (W : Matrix (Fin n) (Fin m) ℝ) {j : Fin m}
    (hj : (j : ℕ) = 0) (p : Fin n × Fin m) :
    orthonormalDilation W p j = if p.2 = j then W p.1 j else 0 := by
  have hK : ∀ i, dilationK W i j = 0 := fun i =>
    dilationK_apply_of_le W (show j ≤ i by rw [Fin.le_def]; omega)
  have hC : ∀ i, dilationC W i j = if i = j then 1 else 0 := fun i => by
    have : dilationC W = 1 - dilationK W := by simp only [dilationK]; abel
    rw [this, Matrix.sub_apply, hK, sub_zero, Matrix.one_apply]
  have hKr : ∀ r : ℕ, ∀ i, (dilationK W ^ r) i j = if r = 0 ∧ i = j then 1 else 0 := by
    intro r i
    rcases r with _ | r
    · simp only [pow_zero, Matrix.one_apply, true_and]
    · rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_zero fun l _ => by rw [hK, mul_zero]]
      simp
  simp only [orthonormalDilation, Matrix.of_apply, Matrix.mul_apply, hKr]
  by_cases hp : p.2 = j
  · have h0 : (p.2 : ℕ) = 0 := by rw [hp]; exact hj
    simp only [h0, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, if_pos hp]
    simp only [hC, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have h0 : (p.2 : ℕ) ≠ 0 := fun h => hp (Fin.ext (by rw [h, hj]))
    simp only [h0, false_and, if_false, mul_zero, Finset.sum_const_zero, if_neg hp]

/-- $\|\mathbf{K}\|_2 \le 1$ for unit columns. -/
theorem specNorm_dilationK_le_one {W : Matrix (Fin n) (Fin m) ℝ}
    (hW : ∀ j, (Wᵀ * W) j j = 1) : specNorm (dilationK W) ≤ 1 := by
  refine (specNorm_le_iff zero_le_one).2 fun x => ?_
  rw [one_mul]
  have h := transpose_dilationC_mul_mul_dilationC hW
  have hsq : ‖WithLp.toLp 2 (dilationK W *ᵥ x)‖ ^ 2 =
      ‖WithLp.toLp 2 x‖ ^ 2 - ‖WithLp.toLp 2 (W *ᵥ (dilationC W *ᵥ x))‖ ^ 2 := by
    simp only [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    have e1 : (dilationK W *ᵥ x) ⬝ᵥ (dilationK W *ᵥ x) =
        x ⬝ᵥ (((dilationK W)ᵀ * dilationK W) *ᵥ x) := by
      rw [eq_comm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have e2 : (W *ᵥ (dilationC W *ᵥ x)) ⬝ᵥ (W *ᵥ (dilationC W *ᵥ x)) =
        x ⬝ᵥ (((dilationC W)ᵀ * (Wᵀ * W) * dilationC W) *ᵥ x) := by
      rw [eq_comm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose]
    rw [e1, e2, h, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
    ring
  have h0 := sq_nonneg ‖WithLp.toLp 2 (W *ᵥ (dilationC W *ᵥ x))‖
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

/-- $\|\mathbf{C}\|_2 \le 2$ for unit columns. -/
theorem specNorm_dilationC_le_two {W : Matrix (Fin n) (Fin m) ℝ}
    (hW : ∀ j, (Wᵀ * W) j j = 1) : specNorm (dilationC W) ≤ 2 := by
  have : dilationC W = 1 - dilationK W := by simp only [dilationK]; abel
  rw [this]
  refine (specNorm_sub_le _ _).trans ?_
  have h1 : specNorm (1 : Matrix (Fin m) (Fin m) ℝ) ≤ 1 := specNorm_one_le
  linarith [specNorm_dilationK_le_one hW]

/-- For $\mathbf{Q}$ with orthonormal columns, $\|\mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{T}}\|_2
\le 1$ (an orthogonal projector). -/
theorem HasOrthonormalCols.specNorm_one_sub_mul_transpose_le {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] {Q : Matrix ι κ ℝ} (hQ : HasOrthonormalCols Q) :
    specNorm (1 - Q * Qᵀ) ≤ 1 := by
  have hQQ : Qᵀ * Q = 1 := by
    have := hQ.conjTranspose_mul_self
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  refine (specNorm_le_iff zero_le_one).2 fun x => ?_
  rw [one_mul]
  set y := Qᵀ *ᵥ x
  have hsq : ‖WithLp.toLp 2 ((1 - Q * Qᵀ) *ᵥ x)‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 - y ⬝ᵥ y := by
    simp only [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, Matrix.sub_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec, dotProduct_sub, sub_dotProduct]
    have e1 : x ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ y := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have e2 : (Q *ᵥ y) ⬝ᵥ x = y ⬝ᵥ y := by rw [dotProduct_comm, e1]
    have e3 : (Q *ᵥ y) ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ y := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQQ,
        Matrix.one_mulVec]
    rw [e1, e2, e3]
    ring
  have hy : 0 ≤ y ⬝ᵥ y := by
    rw [← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]; positivity
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)

end NLAlib
