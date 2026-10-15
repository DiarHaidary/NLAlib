/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Conjugate transposes: real diagonal matrices and cross-Gram matrices

A diagonal matrix over an `RCLike` field whose diagonal entries are real is its own conjugate
transpose; upstream candidate for `Mathlib.Analysis.RCLike.Basic` or a file on Hermitian
matrices. The cross-Gram matrix $\mathbf{A}^{\mathsf{H}}\mathbf{B}$ is the sum of the rank-one
products of the rows; upstream candidate for `Mathlib.LinearAlgebra.Matrix.ConjTranspose`, beside
`Matrix.conjTranspose_vecMulVec`.

## Main results

* `Matrix.conjTranspose_diagonal_ofReal`:
  $\operatorname{diag}(\mathbf{d})^{\mathsf{H}} = \operatorname{diag}(\mathbf{d})$ for real
  $\mathbf{d}$.
* `Matrix.conjTranspose_mul_eq_sum_vecMulVec`:
  $\mathbf{A}^{\mathsf{H}}\mathbf{B} = \sum_i \mathbf{a}_i^{\mathsf{H}} \mathbf{b}_i$ over the rows
  $\mathbf{a}_i$, $\mathbf{b}_i$.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

section Diagonal

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [DecidableEq n]

/-- A diagonal matrix with real entries, over an `RCLike` field, is its own conjugate
transpose: $\operatorname{diag}(\mathbf{d})^{\mathsf{H}} = \operatorname{diag}(\mathbf{d})$ for
$\mathbf{d}$ real. -/
theorem conjTranspose_diagonal_ofReal (d : n → ℝ) :
    (diagonal fun i => ((d i : ℝ) : 𝕜))ᴴ = diagonal fun i => ((d i : ℝ) : 𝕜) := by
  rw [diagonal_conjTranspose]
  exact congrArg diagonal (funext fun i => RCLike.conj_ofReal (d i))

end Diagonal

section Gram

variable {α : Type*} [Mul α] [AddCommMonoid α] [Star α] {n q r : Type*} [Fintype n]

/-- The cross-Gram matrix is the sum of the rank-one products of the rows:
$\mathbf{A}^{\mathsf{H}}\mathbf{B} = \sum_i \mathbf{a}_i^{\mathsf{H}} \mathbf{b}_i$, where
$\mathbf{a}_i$, $\mathbf{b}_i$ are row $i$ of $\mathbf{A}$ and $\mathbf{B}$ and the summand is
`vecMulVec (star (A i)) (B i)`. At $\mathbf{A} = \mathbf{B}$ it writes a Gram matrix as a sum of
positive semidefinite rank-one matrices, the form row-sampling arguments use. -/
theorem conjTranspose_mul_eq_sum_vecMulVec (A : Matrix n q α) (B : Matrix n r α) :
    Aᴴ * B = ∑ i, vecMulVec (star (A i)) (B i) := by
  ext a b
  simp only [mul_apply, conjTranspose_apply, sum_apply, vecMulVec_apply, Pi.star_apply]

end Gram

end Matrix
