/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Selection
public import NLAlib.Matrix.Spectral.CourantFischer

/-!
# Cauchy interlacing

The eigenvalues of a compression $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ of a Hermitian
matrix by a matrix $\mathbf{Q}$ with orthonormal columns interlace those of $\mathbf{A}$. Principal
submatrices `A.submatrix s s` are the case where $\mathbf{Q}$ selects coordinates.

Index shifts are written with an auxiliary natural number and an equation between cardinalities,
never with subtraction.

## Main results

* `Matrix.IsHermitian.eigenvalue_conjTranspose_mul_mul_le`,
  `Matrix.IsHermitian.eigenvalue_le_eigenvalue_conjTranspose_mul_mul`: the Poincaré separation
  theorem for compressions.
* `Matrix.IsHermitian.eigenvalue_submatrix_le`,
  `Matrix.IsHermitian.eigenvalue_le_eigenvalue_submatrix`: Cauchy interlacing for principal
  submatrices.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p : Type*} [Fintype n] [Fintype p]

/-- Pushing a subspace forward by a matrix with orthonormal columns preserves its dimension. -/
private theorem finrank_map_mulVecLin [DecidableEq p] {Q : Matrix n p 𝕜}
    (hQ : HasOrthonormalCols Q) (S : Submodule 𝕜 (p → 𝕜)) :
    Module.finrank 𝕜 (S.map Q.mulVecLin) = Module.finrank 𝕜 S :=
  (Submodule.equivMapOfInjective Q.mulVecLin hQ.mulVec_injective S).finrank_eq.symm

/-- **Poincaré separation, upper.** For Hermitian $\mathbf{A}$ and $\mathbf{Q}$ with orthonormal
columns indexed by $p$, the $k$-th eigenvalue of the compression
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ is at most the $k$-th eigenvalue of $\mathbf{A}$:
$\lambda_k(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}) \le \lambda_k(\mathbf{A})$ for
$k < \lvert p \rvert$.
[HornJohnson2013, Corollary 4.3.37].
Port of `Matrix.IsHermitian.eigenvalues₀_compression_le`.
Result: poincare-separation, cauchy-interlacing -/
theorem _root_.Matrix.IsHermitian.eigenvalue_conjTranspose_mul_mul_le [DecidableEq p]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n p 𝕜} (hQ : HasOrthonormalCols Q)
    {k : ℕ} (hk : k < Fintype.card p) : eigenvalue (Qᴴ * A * Q) k ≤ eigenvalue A k := by
  obtain ⟨S, hS, hBS⟩ :=
    (Matrix.isHermitian_conjTranspose_mul_mul Q hA).exists_submodule_eigenvalue_mul_le hk
  refine hA.le_eigenvalue_of_forall_mem (S.map Q.mulVecLin)
    (by rw [finrank_map_mulVecLin hQ, hS]) ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [Matrix.mulVecLin_apply, hQ.norm_toLp_mulVec, ← quadForm_conjTranspose_mul_mul]
  exact hBS y hy

/-- **Poincaré separation, lower.** For Hermitian $\mathbf{A}$ of size $\lvert p \rvert + d$ and
$\mathbf{Q}$ with orthonormal columns indexed by $p$, the $(k + d)$-th eigenvalue of $\mathbf{A}$
is at most the $k$-th eigenvalue of the compression:
$\lambda_{k+d}(\mathbf{A}) \le \lambda_k(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})$ for
$k < \lvert p \rvert$.
[HornJohnson2013, Corollary 4.3.37].
Port of `Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_compression`.
Result: poincare-separation, cauchy-interlacing -/
theorem _root_.Matrix.IsHermitian.eigenvalue_le_eigenvalue_conjTranspose_mul_mul
    [DecidableEq p] {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n p 𝕜}
    (hQ : HasOrthonormalCols Q) {k d : ℕ} (hk : k < Fintype.card p)
    (hd : Fintype.card p + d = Fintype.card n) :
    eigenvalue A (k + d) ≤ eigenvalue (Qᴴ * A * Q) k := by
  obtain ⟨W, hW, hBW⟩ :=
    (Matrix.isHermitian_conjTranspose_mul_mul Q hA).exists_submodule_le_eigenvalue_mul hk
  refine hA.eigenvalue_le_of_forall_mem (by omega) (W.map Q.mulVecLin)
    (by rw [finrank_map_mulVecLin hQ]; omega) ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [Matrix.mulVecLin_apply, hQ.norm_toLp_mulVec, ← quadForm_conjTranspose_mul_mul]
  exact hBW y hy

/-- **Cauchy interlacing, upper.** The $k$-th eigenvalue of a principal submatrix of a Hermitian
matrix is at most the $k$-th eigenvalue of the matrix: for an injective $s : p \to n$ and
$k < \lvert p \rvert$, $\lambda_k(\mathbf{A}_{s,s}) \le \lambda_k(\mathbf{A})$, where
$\mathbf{A}_{s,s}$ is `A.submatrix s s`.
[HornJohnson2013, Theorem 4.3.17].
Port of `Matrix.IsHermitian.eigenvalues₀_submatrix_le`.
Result: cauchy-interlacing -/
theorem _root_.Matrix.IsHermitian.eigenvalue_submatrix_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {s : p → n} (hs : Function.Injective s) {k : ℕ}
    (hk : k < Fintype.card p) : eigenvalue (A.submatrix s s) k ≤ eigenvalue A k := by
  classical
  rw [← conjTranspose_selectionMatrix_mul_mul_selectionMatrix]
  exact hA.eigenvalue_conjTranspose_mul_mul_le (hasOrthonormalCols_selectionMatrix hs) hk

/-- **Cauchy interlacing, lower.** For a principal submatrix $\mathbf{A}_{s,s}$ (`A.submatrix s s`,
$s : p \to n$ injective) of a Hermitian matrix of size $\lvert p \rvert + d$,
$\lambda_{k+d}(\mathbf{A}) \le \lambda_k(\mathbf{A}_{s,s})$ for $k < \lvert p \rvert$.
[HornJohnson2013, Theorem 4.3.17].
Port of `Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_submatrix`.
Result: cauchy-interlacing -/
theorem _root_.Matrix.IsHermitian.eigenvalue_le_eigenvalue_submatrix {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {s : p → n} (hs : Function.Injective s) {k d : ℕ}
    (hk : k < Fintype.card p) (hd : Fintype.card p + d = Fintype.card n) :
    eigenvalue A (k + d) ≤ eigenvalue (A.submatrix s s) k := by
  classical
  rw [← conjTranspose_selectionMatrix_mul_mul_selectionMatrix]
  exact hA.eigenvalue_le_eigenvalue_conjTranspose_mul_mul
    (hasOrthonormalCols_selectionMatrix hs) hk hd

/-- **Cauchy interlacing for deleting one row and column**:
$\lambda_{k+1}(\mathbf{A}) \le \lambda_k(\mathbf{A}')$ for $k + 1 < \lvert n \rvert$, where
$\mathbf{A}'$ is $\mathbf{A}$ with row and column $i$ removed. [HornJohnson2013, Theorem 4.3.17]. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_succ_le_eigenvalue_submatrix_ne [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (i : n) {k : ℕ} (hk : k + 1 < Fintype.card n) :
    eigenvalue A (k + 1) ≤
      eigenvalue (A.submatrix (Subtype.val : {j // j ≠ i} → n) Subtype.val) k := by
  have hd : Fintype.card {j // j ≠ i} + 1 = Fintype.card n := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    omega
  exact hA.eigenvalue_le_eigenvalue_submatrix Subtype.val_injective (by omega) hd

/-- The largest eigenvalue of a compression $\mathbf{B}^{\mathsf{H}}\mathbf{A}\mathbf{B}$ of a
positive semidefinite matrix $\mathbf{A}$ by any matrix $\mathbf{B}$ is at most the largest
eigenvalue of $\mathbf{A}$ times the squared spectral norm of $\mathbf{B}$:
$\lambda_0(\mathbf{B}^{\mathsf{H}}\mathbf{A}\mathbf{B}) \le \lambda_0(\mathbf{A})
\|\mathbf{B}\|_2^2$. That the compression is itself positive semidefinite is Mathlib's
`Matrix.PosSemidef.conjTranspose_mul_mul_same`. -/
theorem _root_.Matrix.PosSemidef.eigenvalue_zero_conjTranspose_mul_mul_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (B : Matrix n p 𝕜) :
    eigenvalue (Bᴴ * A * B) 0 ≤ eigenvalue A 0 * specNorm B ^ 2 := by
  rw [← (hA.conjTranspose_mul_mul_same B).specNorm_eq_eigenvalue_zero,
    ← hA.specNorm_eq_eigenvalue_zero, mul_comm, sq, mul_assoc]
  refine (specNorm_mul_le _ _).trans ?_
  rw [mul_comm (specNorm B)]
  refine mul_le_mul_of_nonneg_right ((specNorm_mul_le _ _).trans ?_) (specNorm_nonneg B)
  rw [specNorm_conjTranspose]

end NLAlib
