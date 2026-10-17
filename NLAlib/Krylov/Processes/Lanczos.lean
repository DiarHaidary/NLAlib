/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.Grade
public import NLAlib.Matrix.Factorizations.GramSchmidt
public import NLAlib.Matrix.Factorizations.Hessenberg

/-!
# Graded Krylov bases and the Lanczos basis

An orthonormal basis is graded by the Krylov spaces when its first $j + 1$ columns span
$\mathcal{K}_{j+1}(\mathbf{A}, \mathbf{b})$ for every $j$. The compression
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ to such a basis is upper Hessenberg, and tridiagonal
for Hermitian $\mathbf{A}$; it is always written out, never bundled. The canonical graded basis is
the Gram–Schmidt matrix of the Krylov matrix (the Arnoldi basis; for Hermitian $\mathbf{A}$ the
Lanczos basis). Its columns from the grade on are zero, so it is orthonormal exactly up to the
grade, while its range, the Arnoldi relation and its first coordinate need no hypothesis.

The three-term recurrence that computes this basis is in
`NLAlib.Krylov.Processes.LanczosRecurrence`; the corollary that it yields the conjugate gradient
iterate is in `NLAlib.Krylov.LinearSystems.CGLanczos`.

## Main definitions

* `NLAlib.IsGradedKrylovBasis`: an orthonormal basis graded by the Krylov spaces.
* `NLAlib.arnoldiMatrix`: the canonical one, `gramSchmidtQ (krylovMatrix A b q)`.

## Main results

* `NLAlib.isGradedKrylovBasis_of_forall_col_mem`: the constructor from column membership.
* `NLAlib.IsGradedKrylovBasis.isUpperHessenberg`, `NLAlib.IsGradedKrylovBasis.isTridiagonal`.
* `NLAlib.IsGradedKrylovBasis.eq_arnoldiMatrix`: uniqueness under a positive diagonal.
* `NLAlib.hasOrthonormalCols_arnoldiMatrix_iff`, `NLAlib.isGradedKrylovBasis_arnoldiMatrix`.
* `NLAlib.conjTranspose_arnoldiMatrix_mulVec_self`: $\mathbf{Q}^{\mathsf{H}}\mathbf{b} =
  \|\mathbf{b}\|\mathbf{e}_0$.
* `NLAlib.mul_arnoldiMatrix`: the Arnoldi relation, for every $q$.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- `IsGradedKrylovBasis A b Q`: **$\mathbf{Q}$ is an orthonormal basis graded by the Krylov
spaces**: it has orthonormal columns and, for each $j < q$, its first $j + 1$ columns span
$\mathcal{K}_{j+1}(\mathbf{A}, \mathbf{b})$. Such a basis exists exactly for $q \le \nu$, and it
is unique up to unimodular column scalars; with the diagonal of
$\mathbf{Q}^{\mathsf{H}}\mathbf{K}_q(\mathbf{A}, \mathbf{b})$ real positive it is
`arnoldiMatrix A b q` (`IsGradedKrylovBasis.eq_arnoldiMatrix`). [Saad2003, §6.3]. -/
structure IsGradedKrylovBasis (A : Matrix n n 𝕜) (b : n → 𝕜) {q : ℕ}
    (Q : Matrix n (Fin q) 𝕜) : Prop where
  /-- The columns are orthonormal. -/
  hasOrthonormalCols : HasOrthonormalCols Q
  /-- The first $j + 1$ columns span the Krylov space of dimension $j + 1$. -/
  span_col_image_Iic : ∀ j : Fin q,
    Submodule.span 𝕜 (Q.col '' Set.Iic j) = krylovSpace A b ((j : ℕ) + 1)

variable {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ} {Q : Matrix n (Fin q) 𝕜}

/-- **Constructor**: orthonormal columns with column $j$ in $\mathcal{K}_{j+1}(\mathbf{A},
\mathbf{b})$ form a graded Krylov basis.
Proof: the first $j + 1$ columns are independent and lie in $\mathcal{K}_{j+1}$, whose dimension
is at most $j + 1$ (`finrank_krylovSpace`); `Submodule.eq_of_le_of_finrank_le`. Small. -/
theorem isGradedKrylovBasis_of_forall_col_mem (hQ : HasOrthonormalCols Q)
    (h : ∀ j : Fin q, Q.col j ∈ krylovSpace A b ((j : ℕ) + 1)) : IsGradedKrylovBasis A b Q := by
  sorry

/-- A graded basis spans the Krylov space. -/
theorem IsGradedKrylovBasis.range_eq (hQ : IsGradedKrylovBasis A b Q) :
    LinearMap.range Q.mulVecLin = krylovSpace A b q := by
  sorry

/-- A graded basis exists only up to the grade. -/
theorem IsGradedKrylovBasis.le_krylovGrade (hQ : IsGradedKrylovBasis A b Q) :
    q ≤ krylovGrade A b := by
  sorry

/-- **The compression to a graded basis is upper Hessenberg.** [Saad2003, §6.3].
Proof: $\mathbf{A}\mathbf{q}_j \in \mathcal{K}_{j+2}$ (`mulVec_mem_krylovSpace_succ`), which is
spanned by columns $\le j + 1$, orthogonal to $\mathbf{q}_i$ for $i > j + 1$. Small. -/
theorem IsGradedKrylovBasis.isUpperHessenberg (hQ : IsGradedKrylovBasis A b Q) :
    IsUpperHessenberg (Qᴴ * A * Q) := by
  sorry

/-- **For Hermitian $\mathbf{A}$ the compression to a graded basis is tridiagonal**: the Lanczos
matrix $\mathbf{T} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$. [Saad2003, §6.6]. -/
theorem IsGradedKrylovBasis.isTridiagonal (hQ : IsGradedKrylovBasis A b Q)
    (hA : A.IsHermitian) : IsTridiagonal (Qᴴ * A * Q) :=
  hQ.isUpperHessenberg.isTridiagonal (Matrix.isHermitian_conjTranspose_mul_mul Q hA)

/-- The **canonical Krylov basis** (the Arnoldi basis; for Hermitian $\mathbf{A}$ the Lanczos
basis): $\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q)$ is the Gram–Schmidt matrix of
$\mathbf{K}_q(\mathbf{A}, \mathbf{b})$. Column $j$ is the same for every $q > j$; columns from
the grade on are zero, so it has orthonormal columns exactly for $q \le \nu$. -/
noncomputable def arnoldiMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) : Matrix n (Fin q) 𝕜 :=
  gramSchmidtQ (krylovMatrix A b q)

/-- The canonical basis spans the Krylov space, for every $q$. -/
theorem range_arnoldiMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    LinearMap.range (arnoldiMatrix A b q).mulVecLin = krylovSpace A b q :=
  range_gramSchmidtQ _

/-- The first $q$ columns of a longer canonical basis form the shorter one. -/
theorem arnoldiMatrix_submatrix_castLE (A : Matrix n n 𝕜) (b : n → 𝕜) {q q' : ℕ}
    (h : q ≤ q') : (arnoldiMatrix A b q').submatrix id (Fin.castLE h) = arnoldiMatrix A b q := by
  rw [arnoldiMatrix, arnoldiMatrix, ← gramSchmidtQ_submatrix_castLE, krylovMatrix_submatrix_castLE]

/-- The canonical basis has orthonormal columns exactly up to the grade.
Proof: `hasOrthonormalCols_gramSchmidtQ` and `krylovMatrix_mulVec_injective_iff` one way; for the
other, an orthonormal $\mathbf{Q}$ with the range of $\mathbf{K}_q$ forces rank $q$. Small. -/
theorem hasOrthonormalCols_arnoldiMatrix_iff :
    HasOrthonormalCols (arnoldiMatrix A b q) ↔ q ≤ krylovGrade A b := by
  sorry

/-- Up to the grade the canonical basis is graded. -/
theorem isGradedKrylovBasis_arnoldiMatrix (h : q ≤ krylovGrade A b) :
    IsGradedKrylovBasis A b (arnoldiMatrix A b q) := by
  sorry

/-- **Uniqueness of the graded basis**: a graded basis whose matrix
$\mathbf{Q}^{\mathsf{H}}\mathbf{K}_q(\mathbf{A}, \mathbf{b})$ has positive diagonal (in the order
of $\Bbbk$, so real positive) is the canonical one.
Proof: `IsQR (krylovMatrix A b q) Q (Qᴴ * krylovMatrix A b q)`, then `IsQR.unique` against
`isQR_gramSchmidt`. Small to medium. -/
theorem IsGradedKrylovBasis.eq_arnoldiMatrix (hQ : IsGradedKrylovBasis A b Q)
    (hpos : ∀ j, 0 < (Qᴴ * krylovMatrix A b q) j j) : Q = arnoldiMatrix A b q := by
  sorry

/-- The canonical basis sees $\mathbf{b}$ in its first coordinate only:
$\mathbf{Q}^{\mathsf{H}}\mathbf{b} = \|\mathbf{b}\|\mathbf{e}_0$, for every $q$. -/
theorem conjTranspose_arnoldiMatrix_mulVec_self (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    (arnoldiMatrix A b (q + 1))ᴴ *ᵥ b = (‖WithLp.toLp 2 b‖ : 𝕜) • Pi.single 0 1 := by
  sorry

/-- **The Arnoldi relation**, for every $q$:
$\mathbf{A}\mathbf{Q}_q = \mathbf{Q}_{q+1}(\mathbf{Q}_{q+1}^{\mathsf{H}}\mathbf{A}\mathbf{Q}_q)$
for the canonical bases $\mathbf{Q}_q$, $\mathbf{Q}_{q+1}$. [Saad2003, §6.3].
Proof: the columns of $\mathbf{A}\mathbf{Q}_q$ lie in $\mathcal{K}_{q+1}$, fixed by
$\mathbf{Q}_{q+1}\mathbf{Q}_{q+1}^{\mathsf{H}} = \mathbf{P}_{\mathcal{K}_{q+1}}$
(`gramSchmidtQ_mul_conjTranspose`). Small. -/
theorem mul_arnoldiMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    A * arnoldiMatrix A b q =
      arnoldiMatrix A b (q + 1) * ((arnoldiMatrix A b (q + 1))ᴴ * A * arnoldiMatrix A b q) := by
  sorry

end NLAlib
