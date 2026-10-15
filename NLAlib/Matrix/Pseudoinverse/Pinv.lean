/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.Penrose
public import NLAlib.Matrix.Spectral.SVD

/-!
# The Moore–Penrose pseudoinverse

`NLAlib.pinv A` is the Moore–Penrose pseudoinverse $\mathbf{A}^{+}$ of a matrix $\mathbf{A}$ of
any shape and rank. It is the unique matrix satisfying the four Penrose identities
(`NLAlib.IsPinv`), and `NLAlib.pinv_eq_iff` identifies it by them. It is the library's only
pseudoinverse: the full-rank formulas
$(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{-1}\mathbf{A}^{\mathsf{H}}$ and
$\mathbf{A}^{\mathsf{H}}(\mathbf{A}\mathbf{A}^{\mathsf{H}})^{-1}$ are lemmas about it
(`NLAlib.pinv_eq_inv_mul_conjTranspose`, `NLAlib.pinv_eq_conjTranspose_mul_inv`), taking the
full-rank hypothesis in the form `Function.Injective A.mulVec`.

The two products with $\mathbf{A}$ are orthogonal projectors:
$\mathbf{A}\mathbf{A}^{+} = \mathbf{P}_{\mathbf{A}}$ and
$\mathbf{A}^{+}\mathbf{A} = \mathbf{P}_{\mathbf{A}^{\mathsf{H}}}$, with $\mathbf{P}_{\mathbf{A}}$
the orthogonal projector onto the range of $\mathbf{A}$ (`rangeProjector`).

## Main definitions

* `NLAlib.pinv`: the Moore–Penrose pseudoinverse.

## Main results

* `NLAlib.exists_isPinv`, `NLAlib.isPinv_pinv`, `NLAlib.pinv_eq_iff`: existence and
  characterisation.
* `NLAlib.mul_pinv`, `NLAlib.pinv_mul`: the projector identities.
* `NLAlib.IsSVD.pinv_eq`: the pseudoinverse from any singular value decomposition.
* `NLAlib.pinv_conjTranspose`, `NLAlib.pinv_pinv`, `NLAlib.pinv_smul`,
  `NLAlib.HasOrthonormalCols.pinv_mul_left`: transformations.
* `NLAlib.pinv_eq_inv_mul_conjTranspose`, `NLAlib.pinv_mul_self_of_injective`: full column rank.
* `NLAlib.pinv_mul_rev`: the reverse-order law.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p r : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype p] [Fintype r]

/-- For any SVD
$\mathbf{A} = \mathbf{U} \operatorname{diag}(\boldsymbol{\sigma}) \mathbf{V}^{\mathsf{H}}$, the
matrix $\mathbf{V} \operatorname{diag}(\boldsymbol{\sigma}_i^{-1}) \mathbf{U}^{\mathsf{H}}$, with
$0^{-1} = 0$, satisfies the Penrose identities with $\mathbf{A}$. -/
private theorem IsSVD.isPinv [DecidableEq r] {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ}
    {V : Matrix n r 𝕜} (h : IsSVD A U σ V) :
    IsPinv A (V * Matrix.diagonal (fun i => (((σ i)⁻¹ : ℝ) : 𝕜)) * Uᴴ) := by
  have hD : IsPinv (Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜))
      (Matrix.diagonal fun i => (((σ i)⁻¹ : ℝ) : 𝕜)) := by
    have hd := isPinv_diagonal fun i => ((σ i : ℝ) : 𝕜)
    simpa only [RCLike.ofReal_inv] using hd
  have h' := (hD.mul_left h.hasOrthonormalCols_left).mul_conjTranspose_right
    h.hasOrthonormalCols_right
  rwa [← h.eq, ← Matrix.mul_assoc] at h'

/-- **Existence of the pseudoinverse.** Every matrix $\mathbf{A}$, of any shape and rank, has a
Moore–Penrose pseudoinverse: some $\mathbf{B}$ satisfies the four Penrose identities
$$\mathbf{A}\mathbf{B}\mathbf{A} = \mathbf{A}, \quad \mathbf{B}\mathbf{A}\mathbf{B} = \mathbf{B},
  \quad (\mathbf{A}\mathbf{B})^{\mathsf{H}} = \mathbf{A}\mathbf{B}, \quad
  (\mathbf{B}\mathbf{A})^{\mathsf{H}} = \mathbf{B}\mathbf{A}\,.$$
[GolubVanLoan2013, §5.5.2]. Port of `NLAlib.exists_isMoorePenroseInverse`.
Result: moore-penrose-existence -/
theorem exists_isPinv (A : Matrix m n 𝕜) : ∃ B : Matrix n m 𝕜, IsPinv A B := by
  obtain ⟨U, V, h⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  exact ⟨_, h.isPinv⟩

open Classical in
/-- The **Moore–Penrose pseudoinverse** $\mathbf{A}^{+}$ of a matrix of any shape and rank: the
unique matrix satisfying the four Penrose identities with $\mathbf{A}$. For an invertible matrix it
is the inverse, for the zero matrix it is zero, with full column rank it is
$(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{-1}\mathbf{A}^{\mathsf{H}}$.
[GolubVanLoan2013, §5.5.2]. Port of `NLAlib.moorePenroseInverse`. -/
noncomputable def pinv (A : Matrix m n 𝕜) : Matrix n m 𝕜 :=
  if h : ∃ B : Matrix n m 𝕜, IsPinv A B then h.choose else 0

/-- The pseudoinverse satisfies the Penrose identities.
Port of `NLAlib.isMoorePenroseInverse`. -/
theorem isPinv_pinv (A : Matrix m n 𝕜) : IsPinv A (pinv A) := by
  rw [pinv, dif_pos (exists_isPinv A)]
  exact (exists_isPinv A).choose_spec

/-- A matrix satisfying the Penrose identities with $\mathbf{A}$ is the pseudoinverse of
$\mathbf{A}$. -/
theorem IsPinv.pinv_eq {A : Matrix m n 𝕜} {B : Matrix n m 𝕜} (h : IsPinv A B) : pinv A = B := by
  exact (isPinv_pinv A).unique h

/-- The pseudoinverse is characterised by the Penrose identities. -/
theorem pinv_eq_iff {A : Matrix m n 𝕜} {B : Matrix n m 𝕜} : pinv A = B ↔ IsPinv A B := by
  refine ⟨fun h => ?_, IsPinv.pinv_eq⟩
  rw [← h]
  exact isPinv_pinv A

/-! ### The Penrose identities and the projectors -/

/-- $\mathbf{A}\mathbf{A}^{+}\mathbf{A} = \mathbf{A}$. Port of `NLAlib.mul_moorePenroseInverse_mul`.
-/
@[simp]
theorem mul_pinv_mul_self (A : Matrix m n 𝕜) : A * pinv A * A = A := by
  exact (isPinv_pinv A).mul_mul_left

/-- $\mathbf{A}^{+}\mathbf{A}\mathbf{A}^{+} = \mathbf{A}^{+}$.
Port of `NLAlib.moorePenroseInverse_mul_moorePenroseInverse`. -/
@[simp]
theorem pinv_mul_mul_pinv (A : Matrix m n 𝕜) : pinv A * A * pinv A = pinv A := by
  exact (isPinv_pinv A).mul_mul_right

/-- **$\mathbf{A}\mathbf{A}^{+}$ is the orthogonal projector onto the column space of
$\mathbf{A}$:** $\mathbf{A}\mathbf{A}^{+} = \mathbf{P}_{\mathbf{A}}$.
Port of `NLAlib.rangeProjector_eq_mul_moorePenroseInverse`, there the definition of
`rangeProjector`. -/
theorem mul_pinv (A : Matrix m n 𝕜) : A * pinv A = rangeProjector A := by
  exact (isPinv_pinv A).mul_eq_rangeProjector

/-- **$\mathbf{A}^{+}\mathbf{A}$ is the orthogonal projector onto the row space of
$\mathbf{A}$:** $\mathbf{A}^{+}\mathbf{A} = \mathbf{P}_{\mathbf{A}^{\mathsf{H}}}$. -/
theorem pinv_mul (A : Matrix m n 𝕜) : pinv A * A = rangeProjector Aᴴ := by
  exact (isPinv_pinv A).mul_eq_rangeProjector_conjTranspose

/-- $\mathbf{A}\mathbf{A}^{+}\mathbf{B} = \mathbf{B}$ exactly when the column space of
$\mathbf{B}$ is contained in that of $\mathbf{A}$. -/
theorem mul_pinv_mul_eq_iff_range_le {A : Matrix m l 𝕜} {B : Matrix m n 𝕜} :
    A * pinv A * B = B ↔ LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin := by
  rw [mul_pinv, rangeProjector_mul_eq_self_iff]

/-- When the columns of $\mathbf{B}$ lie in the column space of $\mathbf{A}$,
$\mathbf{A}^{+}\mathbf{B}$ solves $\mathbf{A}\mathbf{X} = \mathbf{B}$:
$\mathbf{A}\mathbf{A}^{+}\mathbf{B} = \mathbf{B}$. -/
theorem mul_pinv_mul_eq_of_range_le {A : Matrix m l 𝕜} {B : Matrix m n 𝕜}
    (h : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin) : A * pinv A * B = B := by
  exact mul_pinv_mul_eq_iff_range_le.mpr h

/-- $\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{A}^{+} = \mathbf{A}^{\mathsf{H}}$. Port of
`NLAlib.transpose_mul_mul_moorePenroseInverse`. -/
theorem conjTranspose_mul_mul_pinv (A : Matrix m n 𝕜) : Aᴴ * (A * pinv A) = Aᴴ := by
  rw [mul_pinv, conjTranspose_mul_rangeProjector]

/-- The column space of $\mathbf{A}^{+}$ is the column space of $\mathbf{A}^{\mathsf{H}}$. -/
theorem range_mulVecLin_pinv (A : Matrix m n 𝕜) :
    LinearMap.range (pinv A).mulVecLin = LinearMap.range Aᴴ.mulVecLin := by
  exact (isPinv_pinv A).range_mulVecLin_eq

/-- The pseudoinverse has the rank of the matrix:
$\operatorname{rank} \mathbf{A}^{+} = \operatorname{rank} \mathbf{A}$. -/
@[simp]
theorem rank_pinv (A : Matrix m n 𝕜) : (pinv A).rank = A.rank := by
  exact (isPinv_pinv A).rank_eq

/-! ### Transformations -/

/-- The pseudoinverse commutes with the conjugate transpose:
$(\mathbf{A}^{\mathsf{H}})^{+} = (\mathbf{A}^{+})^{\mathsf{H}}$.
Port of `NLAlib.moorePenroseInverse_conjTranspose`. -/
theorem pinv_conjTranspose (A : Matrix m n 𝕜) : pinv Aᴴ = (pinv A)ᴴ := by
  exact (isPinv_pinv A).conjTranspose.pinv_eq

/-- The pseudoinverse is an involution: $(\mathbf{A}^{+})^{+} = \mathbf{A}$.
Port of `NLAlib.moorePenroseInverse_moorePenroseInverse`. -/
@[simp]
theorem pinv_pinv (A : Matrix m n 𝕜) : pinv (pinv A) = A := by
  exact (isPinv_pinv A).symm.pinv_eq

/-- The pseudoinverse of the zero matrix is zero. Port of `NLAlib.moorePenroseInverse_zero`. -/
@[simp]
theorem pinv_zero : pinv (0 : Matrix m n 𝕜) = 0 := by
  exact isPinv_zero.pinv_eq

/-- The pseudoinverse vanishes only for the zero matrix.
Port of `NLAlib.moorePenroseInverse_eq_zero_iff`. -/
@[simp]
theorem pinv_eq_zero {A : Matrix m n 𝕜} : pinv A = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, pinv_zero]⟩
  have hA := mul_pinv_mul_self A
  rw [h, Matrix.mul_zero, Matrix.zero_mul] at hA
  exact hA.symm

/-- Scaling: $(c\mathbf{A})^{+} = c^{-1}\mathbf{A}^{+}$, also for $c = 0$ with $0^{-1} = 0$.
Port of `NLAlib.moorePenroseInverse_smul`. -/
theorem pinv_smul (c : 𝕜) (A : Matrix m n 𝕜) : pinv (c • A) = c⁻¹ • pinv A := by
  by_cases hc : c = 0
  · rw [hc, zero_smul, pinv_zero, inv_zero, zero_smul]
  · exact ((isPinv_pinv A).smul hc).pinv_eq

/-- The pseudoinverse commutes with negation: $(-\mathbf{A})^{+} = -\mathbf{A}^{+}$. -/
@[simp]
theorem pinv_neg (A : Matrix m n 𝕜) : pinv (-A) = -pinv A := by
  have h := pinv_smul (-1 : 𝕜) A
  rwa [inv_neg_one, neg_one_smul, neg_one_smul] at h

/-- The pseudoinverse of an invertible matrix is its inverse: $\mathbf{A}^{+} = \mathbf{A}^{-1}$.
Port of `NLAlib.moorePenroseInverse_eq_inv_of_isUnit`. -/
theorem pinv_of_isUnit [DecidableEq n] {A : Matrix n n 𝕜} (hA : IsUnit A) : pinv A = A⁻¹ := by
  exact (isPinv_inv hA).pinv_eq

/-- The pseudoinverse of a diagonal matrix inverts the nonzero diagonal entries:
$\operatorname{diag}(\mathbf{d})^{+} = \operatorname{diag}(\mathbf{d}_i^{-1})$ with $0^{-1} = 0$. -/
theorem pinv_diagonal [DecidableEq n] (d : n → 𝕜) :
    pinv (Matrix.diagonal d) = Matrix.diagonal fun i => (d i)⁻¹ := by
  exact (isPinv_diagonal d).pinv_eq

/-- The pseudoinverse commutes with relabelling.
Port of `NLAlib.moorePenroseInverse_reindex`. -/
theorem pinv_submatrix_equiv (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    pinv (A.submatrix e₁ e₂) = (pinv A).submatrix e₂ e₁ := by
  exact ((isPinv_pinv A).submatrix e₁ e₂).pinv_eq

/-- The pseudoinverse of a Hermitian matrix is Hermitian.
Port of `Matrix.IsHermitian.moorePenroseInverse`. -/
theorem _root_.Matrix.IsHermitian.pinv {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (pinv A).IsHermitian := by
  rw [Matrix.IsHermitian, ← pinv_conjTranspose, hA.eq]

/-- The pseudoinverse of a positive semidefinite matrix is positive semidefinite.
Port of `Matrix.PosSemidef.moorePenroseInverse`. -/
theorem _root_.Matrix.PosSemidef.pinv {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    (pinv A).PosSemidef := by
  have h := hA.mul_mul_conjTranspose_same (NLAlib.pinv A)
  rwa [hA.isHermitian.pinv.eq, pinv_mul_mul_pinv] at h

/-- The pseudoinverse of an orthogonal projector is the projector. -/
theorem _root_.IsStarProjection.pinv_eq {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    pinv P = P := by
  exact hP.isPinv.pinv_eq

/-- The pseudoinverse of a matrix with orthonormal columns is its conjugate transpose:
$\mathbf{Q}^{+} = \mathbf{Q}^{\mathsf{H}}$. -/
theorem HasOrthonormalCols.pinv_eq [DecidableEq n] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) : pinv Q = Qᴴ := by
  exact hQ.isPinv.pinv_eq

/-- $(\mathbf{Q}\mathbf{A})^{+} = \mathbf{A}^{+}\mathbf{Q}^{\mathsf{H}}$ for $\mathbf{Q}$ with
orthonormal columns.
Port of `NLAlib.moorePenroseInverse_mul_left_of_hasOrthonormalCols`. -/
theorem HasOrthonormalCols.pinv_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) : pinv (Q * A) = pinv A * Qᴴ := by
  exact ((isPinv_pinv A).mul_left hQ).pinv_eq

/-- $(\mathbf{A}\mathbf{Q}^{\mathsf{H}})^{+} = \mathbf{Q}\mathbf{A}^{+}$ for $\mathbf{Q}$ with
orthonormal columns. -/
theorem HasOrthonormalCols.pinv_mul_conjTranspose_right [DecidableEq n] {Q : Matrix l n 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) : pinv (A * Qᴴ) = Q * pinv A := by
  exact ((isPinv_pinv A).mul_conjTranspose_right hQ).pinv_eq

/-- The pseudoinverse of the Gram matrix:
$(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{+} = \mathbf{A}^{+}(\mathbf{A}^{+})^{\mathsf{H}}$.
Port of `NLAlib.moorePenroseInverse_conjTranspose_mul_self`. -/
theorem pinv_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    pinv (Aᴴ * A) = pinv A * (pinv A)ᴴ := by
  exact (isPinv_pinv A).conjTranspose_mul_self.pinv_eq

/-- $(\mathbf{A}\mathbf{A}^{\mathsf{H}})^{+} = (\mathbf{A}^{+})^{\mathsf{H}}\mathbf{A}^{+}$.
Port of `NLAlib.moorePenroseInverse_self_mul_conjTranspose`. -/
theorem pinv_mul_conjTranspose_self (A : Matrix m n 𝕜) :
    pinv (A * Aᴴ) = (pinv A)ᴴ * pinv A := by
  have h := pinv_conjTranspose_mul_self Aᴴ
  rwa [Matrix.conjTranspose_conjTranspose, pinv_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at h

/-- **The projector through the Gram pseudoinverse**:
$\mathbf{A}(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{+}\mathbf{A}^{\mathsf{H}} =
\mathbf{P}_{\mathbf{A}}$, the orthogonal projector onto the column space of $\mathbf{A}$, with no
rank assumption. With $\mathbf{A} = \mathbf{M}^{1/2}\mathbf{\Omega}$ this is the identity behind the
Nyström approximation. -/
theorem mul_pinv_conjTranspose_mul_self_mul_conjTranspose (A : Matrix m n 𝕜) :
    A * pinv (Aᴴ * A) * Aᴴ = rangeProjector A := by
  rw [pinv_conjTranspose_mul_self, ← Matrix.mul_assoc A, Matrix.mul_assoc (A * pinv A),
    ← Matrix.conjTranspose_mul, mul_pinv, conjTranspose_rangeProjector,
    rangeProjector_mul_rangeProjector]

/-- The pseudoinverse through the Gram matrix:
$\mathbf{A}^{+} = (\mathbf{A}^{\mathsf{H}}\mathbf{A})^{+}\mathbf{A}^{\mathsf{H}}$. -/
theorem pinv_eq_pinv_conjTranspose_mul_self_mul (A : Matrix m n 𝕜) :
    pinv A = pinv (Aᴴ * A) * Aᴴ := by
  rw [pinv_conjTranspose_mul_self, Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
    (isPinv_pinv A).isHermitian_left.eq, ← Matrix.mul_assoc, pinv_mul_mul_pinv]

/-- The pseudoinverse through the other Gram matrix:
$\mathbf{A}^{+} = \mathbf{A}^{\mathsf{H}}(\mathbf{A}\mathbf{A}^{\mathsf{H}})^{+}$. The mirror of
`NLAlib.pinv_eq_pinv_conjTranspose_mul_self_mul`; it writes a right factor
$(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}$ through the Gram matrix of
$\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}$. -/
theorem pinv_eq_conjTranspose_mul_pinv_mul_conjTranspose_self (A : Matrix m n 𝕜) :
    pinv A = Aᴴ * pinv (A * Aᴴ) := by
  rw [pinv_mul_conjTranspose_self, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
    (isPinv_pinv A).isHermitian_right.eq, pinv_mul_mul_pinv]

/-! ### From a singular value decomposition -/

/-- **The pseudoinverse from a singular value decomposition.** For any thin SVD
$\mathbf{A} = \mathbf{U} \operatorname{diag}(\boldsymbol{\sigma}) \mathbf{V}^{\mathsf{H}}$,
$\mathbf{A}^{+} = \mathbf{V} \operatorname{diag}(\boldsymbol{\sigma}_i^{-1})
\mathbf{U}^{\mathsf{H}}$, where $0^{-1} = 0$ handles vanishing singular values.
[GolubVanLoan2013, §5.5.2]. Port of `NLAlib.moorePenroseInverse_eq_svd`, there with square factors
and a rectangular diagonal. -/
theorem IsSVD.pinv_eq [DecidableEq r] {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ}
    {V : Matrix n r 𝕜} (h : IsSVD A U σ V) :
    pinv A = V * Matrix.diagonal (fun i => (((σ i)⁻¹ : ℝ) : 𝕜)) * Uᴴ := by
  exact h.isPinv.pinv_eq

/-- An SVD of $\mathbf{A}$ gives an SVD of $\mathbf{A}^{+}$ with the factors exchanged and the
singular values inverted ($0^{-1} = 0$). -/
theorem IsSVD.pinv [DecidableEq r] {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ}
    {V : Matrix n r 𝕜} (h : IsSVD A U σ V) : IsSVD (pinv A) V (fun i => (σ i)⁻¹) U := by
  exact ⟨h.hasOrthonormalCols_right, h.hasOrthonormalCols_left,
    fun i => inv_nonneg.mpr (h.nonneg i), h.pinv_eq⟩

/-! ### Full rank -/

/-- **Full column rank.** If $\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ is injective then
$\mathbf{A}^{+} = (\mathbf{A}^{\mathsf{H}}\mathbf{A})^{-1}\mathbf{A}^{\mathsf{H}}$.
[GolubVanLoan2013, §5.5.2]. Port of `NLAlib.moorePenroseInverse_eq_pinvL`, there with the
hypothesis `IsUnit (Aᴴ * A)` and a separate definition `pinvL`. -/
theorem pinv_eq_inv_mul_conjTranspose [DecidableEq n] {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) : pinv A = (Aᴴ * A)⁻¹ * Aᴴ := by
  exact (isPinv_inv_mul_conjTranspose hA).pinv_eq

/-- **Full row rank.** If $\mathbf{x} \mapsto \mathbf{A}^{\mathsf{H}}\mathbf{x}$ is injective
then $\mathbf{A}^{+} = \mathbf{A}^{\mathsf{H}}(\mathbf{A}\mathbf{A}^{\mathsf{H}})^{-1}$.
Port of `NLAlib.moorePenroseInverse_eq_pinvR`. -/
theorem pinv_eq_conjTranspose_mul_inv [DecidableEq m] {A : Matrix m n 𝕜}
    (hA : Function.Injective Aᴴ.mulVec) : pinv A = Aᴴ * (A * Aᴴ)⁻¹ := by
  exact (isPinv_conjTranspose_mul_inv hA).pinv_eq

/-- With full column rank the pseudoinverse is a left inverse: $\mathbf{A}^{+}\mathbf{A} =
\mathbf{I}$. Port of `NLAlib.pinvL_mul`. -/
theorem pinv_mul_self_of_injective [DecidableEq n] {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) : pinv A * A = 1 := by
  rw [pinv_eq_inv_mul_conjTranspose hA]
  exact inv_conjTranspose_mul_self_mul_conjTranspose_mul hA

/-- With full row rank the pseudoinverse is a right inverse: $\mathbf{A}\mathbf{A}^{+} =
\mathbf{I}$. Port of `NLAlib.mul_pinvR`. -/
theorem mul_pinv_self_of_injective_conjTranspose [DecidableEq m] {A : Matrix m n 𝕜}
    (hA : Function.Injective Aᴴ.mulVec) : A * pinv A = 1 := by
  have h := congrArg Matrix.conjTranspose (pinv_mul_self_of_injective hA)
  rwa [pinv_conjTranspose, ← Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_one] at h

/-- With full column rank, $\mathbf{A}^{+}\mathbf{A}\mathbf{x} = \mathbf{x}$. -/
theorem pinv_mulVec_mulVec_of_injective {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec)
    (x : n → 𝕜) : pinv A *ᵥ (A *ᵥ x) = x := by
  classical
  rw [Matrix.mulVec_mulVec, pinv_mul_self_of_injective hA, Matrix.one_mulVec]

/-- **The reverse-order law.** If $\mathbf{A}$ has full column rank and $\mathbf{B}$ has full
row rank then $(\mathbf{A}\mathbf{B})^{+} = \mathbf{B}^{+}\mathbf{A}^{+}$.
[GolubVanLoan2013, §5.5.2]. -/
theorem pinv_mul_rev {A : Matrix l m 𝕜} {B : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) (hB : Function.Injective Bᴴ.mulVec) :
    pinv (A * B) = pinv B * pinv A := by
  classical
  have hA' : pinv A * A = 1 := pinv_mul_self_of_injective hA
  have hB' : B * pinv B = 1 := mul_pinv_self_of_injective_conjTranspose hB
  have h₁ : A * B * (pinv B * pinv A) = A * pinv A := by
    rw [Matrix.mul_assoc A, ← Matrix.mul_assoc B, hB', Matrix.one_mul]
  have h₂ : pinv B * pinv A * (A * B) = pinv B * B := by
    rw [Matrix.mul_assoc (pinv B), ← Matrix.mul_assoc (pinv A), hA', Matrix.one_mul]
  refine IsPinv.pinv_eq ⟨?_, ?_, ?_, ?_⟩
  · rw [h₁, ← Matrix.mul_assoc, mul_pinv_mul_self]
  · rw [h₂, ← Matrix.mul_assoc, pinv_mul_mul_pinv]
  · rw [h₁]
    exact (isPinv_pinv A).isHermitian_left
  · rw [h₂]
    exact (isPinv_pinv B).isHermitian_right

end NLAlib
