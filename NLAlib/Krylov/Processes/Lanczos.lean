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
\mathbf{b})$ form a graded Krylov basis. -/
theorem isGradedKrylovBasis_of_forall_col_mem (hQ : HasOrthonormalCols Q)
    (h : ∀ j : Fin q, Q.col j ∈ krylovSpace A b ((j : ℕ) + 1)) : IsGradedKrylovBasis A b Q := by
  refine ⟨hQ, fun j => ?_⟩
  have hle : Submodule.span 𝕜 (Q.col '' Set.Iic j) ≤ krylovSpace A b ((j : ℕ) + 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact krylovSpace_mono A b (Nat.succ_le_succ (Fin.le_def.mp hi)) (h i)
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  have hli : LinearIndependent 𝕜 Q.col := Matrix.mulVec_injective_iff.mp hQ.mulVec_injective
  have h2 : Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun x : Set.Iic j => Q.col x)) =
      (j : ℕ) + 1 := by
    rw [finrank_span_eq_card (b := fun x : Set.Iic j => Q.col x)
      (hli.comp _ Subtype.val_injective)]
    simp
  rw [finrank_krylovSpace, Set.image_eq_range, h2]
  exact min_le_left _ _

/-- A graded basis spans the Krylov space. -/
theorem IsGradedKrylovBasis.range_eq (hQ : IsGradedKrylovBasis A b Q) :
    LinearMap.range Q.mulVecLin = krylovSpace A b q := by
  cases q with
  | zero =>
    rw [krylovSpace_zero, Matrix.range_mulVecLin, Set.range_eq_empty, Submodule.span_empty]
  | succ q =>
    have h := hQ.span_col_image_Iic (Fin.last q)
    rw [Fin.val_last] at h
    rw [← h, Matrix.range_mulVecLin, ← Set.image_univ]
    congr 2
    exact (Set.eq_univ_of_forall fun i => Set.mem_Iic.mpr (Fin.le_last i)).symm

/-- A graded basis exists only up to the grade. -/
theorem IsGradedKrylovBasis.le_krylovGrade (hQ : IsGradedKrylovBasis A b Q) :
    q ≤ krylovGrade A b := by
  have h := hQ.hasOrthonormalCols.rank_eq
  rw [Matrix.rank, hQ.range_eq, finrank_krylovSpace, Fintype.card_fin] at h
  omega

/-- **The compression to a graded basis is upper Hessenberg.** [Saad2003, §6.3]. -/
theorem IsGradedKrylovBasis.isUpperHessenberg (hQ : IsGradedKrylovBasis A b Q) :
    IsUpperHessenberg (Qᴴ * A * Q) := by
  intro i j hij
  rw [conjTranspose_mul_mul_apply]
  have hj : Q.col j ∈ krylovSpace A b ((j : ℕ) + 1) := by
    rw [← hQ.span_col_image_Iic j]
    exact Submodule.subset_span ⟨j, Set.mem_Iic.mpr le_rfl, rfl⟩
  have hAj := mulVec_mem_krylovSpace_succ hj
  have hk : (j : ℕ) + 1 < q := lt_trans hij i.2
  rw [show (j : ℕ) + 1 + 1 = ((⟨(j : ℕ) + 1, hk⟩ : Fin q) : ℕ) + 1 from rfl,
    ← hQ.span_col_image_Iic] at hAj
  refine hQ.hasOrthonormalCols.star_col_dotProduct_eq_zero_of_mem_span ?_ hAj
  rw [Set.mem_Iic, Fin.le_def, not_le]
  exact hij

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

/-- The canonical basis has orthonormal columns exactly up to the grade. -/
theorem hasOrthonormalCols_arnoldiMatrix_iff :
    HasOrthonormalCols (arnoldiMatrix A b q) ↔ q ≤ krylovGrade A b := by
  refine ⟨fun h => ?_, fun h => hasOrthonormalCols_gramSchmidtQ
    (krylovMatrix_mulVec_injective_iff.mpr h)⟩
  have h' := h.rank_eq
  rw [Matrix.rank, range_arnoldiMatrix, finrank_krylovSpace, Fintype.card_fin] at h'
  omega

/-- Up to the grade the canonical basis is graded. -/
theorem isGradedKrylovBasis_arnoldiMatrix (h : q ≤ krylovGrade A b) :
    IsGradedKrylovBasis A b (arnoldiMatrix A b q) := by
  refine isGradedKrylovBasis_of_forall_col_mem (hasOrthonormalCols_arnoldiMatrix_iff.mpr h)
    fun j => ?_
  have hj : (arnoldiMatrix A b q).col j ∈
      Submodule.span 𝕜 ((arnoldiMatrix A b q).col '' Set.Iic j) :=
    Submodule.subset_span ⟨j, Set.mem_Iic.mpr le_rfl, rfl⟩
  rw [arnoldiMatrix, span_gramSchmidtQ_col_image_Iic] at hj
  refine Submodule.span_le.mpr ?_ hj
  rintro _ ⟨i, hi, rfl⟩
  exact pow_mulVec_mem_krylovSpace A b (Nat.lt_succ_of_le (Fin.le_def.mp hi))

/-- **Uniqueness of the graded basis**: a graded basis whose matrix
$\mathbf{Q}^{\mathsf{H}}\mathbf{K}_q(\mathbf{A}, \mathbf{b})$ has positive diagonal (in the order
of $\Bbbk$, so real positive) is the canonical one. -/
theorem IsGradedKrylovBasis.eq_arnoldiMatrix (hQ : IsGradedKrylovBasis A b Q)
    (hpos : ∀ j, 0 < (Qᴴ * krylovMatrix A b q) j j) : Q = arnoldiMatrix A b q := by
  have hK : Function.Injective (krylovMatrix A b q).mulVec :=
    krylovMatrix_mulVec_injective_iff.mpr hQ.le_krylovGrade
  have hQR : IsQR (krylovMatrix A b q) Q (Qᴴ * krylovMatrix A b q) := by
    refine ⟨?_, hQ.hasOrthonormalCols, fun i j hij => ?_⟩
    · rw [← Matrix.mul_assoc, ← hQ.hasOrthonormalCols.rangeProjector_eq]
      exact (rangeProjector_mul_eq_self_iff.mpr (hQ.range_eq.symm ▸ le_rfl)).symm
    · have hij' : j < i := hij
      rw [conjTranspose_mul_apply]
      have hj : (krylovMatrix A b q).col j ∈ krylovSpace A b ((j : ℕ) + 1) :=
        pow_mulVec_mem_krylovSpace A b (Nat.lt_succ_self _)
      rw [← hQ.span_col_image_Iic] at hj
      exact hQ.hasOrthonormalCols.star_col_dotProduct_eq_zero_of_mem_span
        (fun h => (not_le.mpr hij') (Set.mem_Iic.mp h)) hj
  exact (hQR.unique (isQR_gramSchmidt hK) hpos (gramSchmidtR_apply_self_pos hK)).1

/-- The canonical basis sees $\mathbf{b}$ in its first coordinate only:
$\mathbf{Q}^{\mathsf{H}}\mathbf{b} = \|\mathbf{b}\|\mathbf{e}_0$, for every $q$. -/
theorem conjTranspose_arnoldiMatrix_mulVec_self (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    (arnoldiMatrix A b (q + 1))ᴴ *ᵥ b = (‖WithLp.toLp 2 b‖ : 𝕜) • Pi.single 0 1 := by
  have hb : krylovMatrix A b (q + 1) *ᵥ Pi.single 0 1 = b := by
    rw [Matrix.mulVec_single_one]
    ext i
    simp
  have hR : (arnoldiMatrix A b (q + 1))ᴴ *ᵥ b =
      (gramSchmidtR (krylovMatrix A b (q + 1))).col 0 := by
    calc (arnoldiMatrix A b (q + 1))ᴴ *ᵥ b =
        (arnoldiMatrix A b (q + 1))ᴴ *ᵥ (krylovMatrix A b (q + 1) *ᵥ Pi.single 0 1) := by
          rw [hb]
      _ = _ := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
          rfl
  rw [hR]
  ext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
  · rw [Matrix.col_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, gramSchmidtR,
      conjTranspose_mul_apply, ← bot_eq_zero (α := Fin (q + 1)), gramSchmidtQ_col_bot]
    have hcol : (krylovMatrix A b (q + 1)).col ⊥ = b := by
      ext i
      simp [bot_eq_zero (α := Fin (q + 1))]
    rw [hcol, star_smul, smul_dotProduct, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq,
      smul_eq_mul, RCLike.star_def, map_inv₀, RCLike.conj_ofReal]
    rcases eq_or_ne ‖WithLp.toLp 2 b‖ 0 with h | h
    · simp [h]
    · push_cast
      field_simp
  · rw [Matrix.col_apply, Pi.smul_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero k), smul_zero]
    exact isUpperTriangular_gramSchmidtR _ (Fin.succ_pos k)

/-- **The Arnoldi relation**, for every $q$:
$\mathbf{A}\mathbf{Q}_q = \mathbf{Q}_{q+1}(\mathbf{Q}_{q+1}^{\mathsf{H}}\mathbf{A}\mathbf{Q}_q)$
for the canonical bases $\mathbf{Q}_q$, $\mathbf{Q}_{q+1}$. [Saad2003, §6.3]. -/
theorem mul_arnoldiMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    A * arnoldiMatrix A b q =
      arnoldiMatrix A b (q + 1) * ((arnoldiMatrix A b (q + 1))ᴴ * A * arnoldiMatrix A b q) := by
  rw [Matrix.mul_assoc _ A, ← Matrix.mul_assoc,
    show arnoldiMatrix A b (q + 1) * (arnoldiMatrix A b (q + 1))ᴴ =
      rangeProjector (krylovMatrix A b (q + 1)) from gramSchmidtQ_mul_conjTranspose _]
  refine (rangeProjector_mul_eq_self_iff.mpr ?_).symm
  rintro _ ⟨c, rfl⟩
  rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
  exact mulVec_mem_krylovSpace_succ (by
    rw [← range_arnoldiMatrix]
    exact ⟨c, rfl⟩)

end NLAlib
