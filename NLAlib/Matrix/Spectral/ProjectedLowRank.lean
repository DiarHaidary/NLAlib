/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.LowRank

/-!
# Best low-rank approximation with columns in a given range

For a matrix $\mathbf{Q}$ with orthonormal columns, the approximations $\mathbf{Q}\mathbf{B}$ of
$\mathbf{A}$ with $\mathbf{B}$ of rank at most $k$ are compared through the compression
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}$: the squared Frobenius error of $\mathbf{Q}\mathbf{B}$ is the
squared projection residual of $\mathbf{A}$ plus the squared error of $\mathbf{B}$ as an
approximation of $\mathbf{Q}^{\mathsf{H}}\mathbf{A}$. By the Eckart–Young theorem the error is
therefore least at $\mathbf{B} = \llbracket \mathbf{Q}^{\mathsf{H}}\mathbf{A} \rrbracket_k$. This
is the truncation step of the randomized singular value decomposition, where $\mathbf{Q}$ is the
output of a range finder.

## Main results

* `NLAlib.HasOrthonormalCols.frobNorm_sub_mul_sq`: the error split
  $\|\mathbf{A} - \mathbf{Q}\mathbf{B}\|_{\mathsf{F}}^2 =
  \|(\mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{A}\|_{\mathsf{F}}^2 +
  \|\mathbf{Q}^{\mathsf{H}}\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}^2$.
* `NLAlib.HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_le_of_rank_le`,
  `NLAlib.HasOrthonormalCols.isLeast_frobNorm_sub_mul_of_rank_le`:
  $\mathbf{Q} \llbracket \mathbf{Q}^{\mathsf{H}}\mathbf{A} \rrbracket_k$ is a best approximation of
  $\mathbf{A}$ among the matrices $\mathbf{Q}\mathbf{B}$ with $\mathbf{B}$ of rank at most $k$.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq r]

/-- **The exact error split for a frame.** For $\mathbf{Q}$ with orthonormal columns and any
coefficient matrix $\mathbf{B}$,
$$\|\mathbf{A} - \mathbf{Q}\mathbf{B}\|_{\mathsf{F}}^2 =
  \|(\mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{A}\|_{\mathsf{F}}^2 +
  \|\mathbf{Q}^{\mathsf{H}}\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}^2:$$
the squared projection residual plus the squared error of $\mathbf{B}$ as an approximation of the
compression $\mathbf{Q}^{\mathsf{H}}\mathbf{A}$. This is `NLAlib.frobNorm_sub_mul_sq` with the
range projector written $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$ and the error inside the range pulled
back through $\mathbf{Q}$. It is the core-form split of the sketched low-rank approximations: with
$\mathbf{B}$ the sketched core it splits the error of generalized Nyström in the form
`NLAlib.generalizedNystrom_eq_mul_sketchAndSolve` gives.
[HalkoMartinssonTropp2011, Theorem 9.1 (proof)]; [TroppYurtseverUdellCevher2017, Lemma A.3].
Port of `NLAlib.frobSq_sub_mul_eq`. -/
theorem HasOrthonormalCols.frobNorm_sub_mul_sq [DecidableEq m] {Q : Matrix m r 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) (B : Matrix r n 𝕜) :
    frobNorm (A - Q * B) ^ 2 =
      frobNorm ((1 - Q * Qᴴ) * A) ^ 2 + frobNorm (Qᴴ * A - B) ^ 2 := by
  rw [NLAlib.frobNorm_sub_mul_sq Q A B, hQ.rangeProjector_eq, Matrix.mul_assoc, ← Matrix.mul_sub,
    hQ.frobNorm_mul_left]

/-- **Truncation inside a range is optimal.** For $\mathbf{Q}$ with orthonormal columns, the
truncated singular value decomposition of the compression $\mathbf{Q}^{\mathsf{H}}\mathbf{A}$
gives the best Frobenius approximation of $\mathbf{A}$ among the matrices $\mathbf{Q}\mathbf{B}$
with $\mathbf{B}$ of rank at most $k$:
$$\|\mathbf{A} - \mathbf{Q} \llbracket \mathbf{Q}^{\mathsf{H}}\mathbf{A} \rrbracket_k\|_{\mathsf{F}}
  \le \|\mathbf{A} - \mathbf{Q}\mathbf{B}\|_{\mathsf{F}}.$$
For $k$ at least the rank of $\mathbf{Q}^{\mathsf{H}}\mathbf{A}$ the left side is the projection
residual $\|(\mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{A}\|_{\mathsf{F}}$.
[HalkoMartinssonTropp2011, Theorem 9.1 (proof)]; there in the analysis of the fixed-rank
randomized singular value decomposition.
Port of `NLAlib.frobSq_sub_mul_le_of_isBestFrobRankApprox`, there for any best approximation of
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}$ in place of
$\llbracket \mathbf{Q}^{\mathsf{H}}\mathbf{A} \rrbracket_k$. -/
theorem HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_le_of_rank_le {Q : Matrix m r 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) {B : Matrix r n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) :
    frobNorm (A - Q * truncatedSVD (Qᴴ * A) k) ≤ frobNorm (A - Q * B) := by
  classical
  refine (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).mp ?_
  rw [hQ.frobNorm_sub_mul_sq, hQ.frobNorm_sub_mul_sq]
  exact add_le_add_right (pow_le_pow_left₀ (frobNorm_nonneg _)
    (frobNorm_sub_truncatedSVD_le_of_rank_le _ hB) 2) _

/-- Truncation inside a range is optimal, as a least element: among the matrices
$\mathbf{Q}\mathbf{B}$ with $\mathbf{B}$ of rank at most $k$, the least Frobenius error is attained
at $\mathbf{B} = \llbracket \mathbf{Q}^{\mathsf{H}}\mathbf{A} \rrbracket_k$. -/
theorem HasOrthonormalCols.isLeast_frobNorm_sub_mul_of_rank_le {Q : Matrix m r 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) (k : ℕ) :
    IsLeast ((fun B : Matrix r n 𝕜 => frobNorm (A - Q * B)) '' {B | B.rank ≤ k})
      (frobNorm (A - Q * truncatedSVD (Qᴴ * A) k)) := by
  refine ⟨⟨truncatedSVD (Qᴴ * A) k, rank_truncatedSVD_le _ k, rfl⟩, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  exact hQ.frobNorm_sub_mul_truncatedSVD_le_of_rank_le A hB

end NLAlib
