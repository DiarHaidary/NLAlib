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
  sorry

/-- $\mathbf{R}^m = \mathbf{0}$. -/
theorem strictUpperGram_pow_eq_zero (W : Matrix (Fin n) (Fin m) ℝ) : strictUpperGram W ^ m = 0 := by
  sorry

/-- $\mathbf{C}$ inverts $\mathbf{I} + \mathbf{R}$: $(\mathbf{I} + \mathbf{R})\mathbf{C} =
\mathbf{I}$. -/
theorem one_add_strictUpperGram_mul_dilationC (W : Matrix (Fin n) (Fin m) ℝ) :
    (1 + strictUpperGram W) * dilationC W = 1 := by
  sorry

/-- $\mathbf{K} = \mathbf{R}\mathbf{C}$. -/
theorem dilationK_eq_strictUpperGram_mul (W : Matrix (Fin n) (Fin m) ℝ) :
    dilationK W = strictUpperGram W * dilationC W := by
  sorry

/-- $\mathbf{K} = \mathbf{C}\mathbf{R}$. -/
theorem dilationK_eq_dilationC_mul (W : Matrix (Fin n) (Fin m) ℝ) :
    dilationK W = dilationC W * strictUpperGram W := by
  sorry

/-- $\mathbf{K}^m = \mathbf{0}$. -/
theorem dilationK_pow_eq_zero (W : Matrix (Fin n) (Fin m) ℝ) : dilationK W ^ m = 0 := by
  sorry

/-- $\mathbf{C}$ is upper triangular. -/
theorem isUpperTriangular_dilationC (W : Matrix (Fin n) (Fin m) ℝ) :
    (dilationC W).IsUpperTriangular := by
  sorry

/-- $\mathbf{K}$ is upper triangular. -/
theorem isUpperTriangular_dilationK (W : Matrix (Fin n) (Fin m) ℝ) :
    (dilationK W).IsUpperTriangular := by
  sorry

/-- **The Gram identity of the dilation**: for unit columns,
$\mathbf{C}^{\mathsf{T}}\mathbf{W}^{\mathsf{T}}\mathbf{W}\mathbf{C} = \mathbf{I} -
\mathbf{K}^{\mathsf{T}}\mathbf{K}$. No printed source; the maintainer's draft,
`eq:CGC-identity`; [Paige2009, Theorem 2.1] in the form of a unitary augmentation. -/
theorem transpose_dilationC_mul_mul_dilationC {W : Matrix (Fin n) (Fin m) ℝ}
    (hW : ∀ j, (Wᵀ * W) j j = 1) :
    (dilationC W)ᵀ * (Wᵀ * W) * dilationC W = 1 - (dilationK W)ᵀ * dilationK W := by
  sorry

/-- **The dilation has orthonormal columns**: for unit columns of $\mathbf{W}$, the stacked
blocks $\mathbf{W}\mathbf{C}\mathbf{K}^r$, $r < m$, have orthonormal columns.
No printed source; the maintainer's draft, `lem:dilation`. -/
theorem hasOrthonormalCols_orthonormalDilation {W : Matrix (Fin n) (Fin m) ℝ}
    (hW : ∀ j, (Wᵀ * W) j j = 1) : HasOrthonormalCols (orthonormalDilation W) := by
  sorry

/-- The first column of the dilation is $\mathbf{w}_0$ in the first block and $\mathbf{0}$ in
the others. No printed source; the maintainer's draft, `lem:dilation`. -/
theorem orthonormalDilation_apply_of_val_eq_zero (W : Matrix (Fin n) (Fin m) ℝ) {j : Fin m}
    (hj : (j : ℕ) = 0) (p : Fin n × Fin m) :
    orthonormalDilation W p j = if p.2 = j then W p.1 j else 0 := by
  sorry

/-- $\|\mathbf{K}\|_2 \le 1$ for unit columns. -/
theorem specNorm_dilationK_le_one {W : Matrix (Fin n) (Fin m) ℝ}
    (hW : ∀ j, (Wᵀ * W) j j = 1) : specNorm (dilationK W) ≤ 1 := by
  sorry

/-- $\|\mathbf{C}\|_2 \le 2$ for unit columns. -/
theorem specNorm_dilationC_le_two {W : Matrix (Fin n) (Fin m) ℝ}
    (hW : ∀ j, (Wᵀ * W) j j = 1) : specNorm (dilationC W) ≤ 2 := by
  sorry

end NLAlib
