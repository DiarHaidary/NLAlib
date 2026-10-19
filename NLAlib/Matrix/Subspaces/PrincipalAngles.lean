/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import NLAlib.Matrix.Subspaces.ProjectorPair

/-!
# Principal angles between subspaces

The principal angles between the column spaces of two matrices $\mathbf{X}$ and $\mathbf{Y}$
are `NLAlib.principalAngle X Y k`, written $\theta_k(\mathbf{X}, \mathbf{Y})$, $k = 0, 1, \dots$, in
non-decreasing order. Their cosines are the singular values of the product
$\mathbf{P}_{\mathbf{X}}\mathbf{P}_{\mathbf{Y}}$ of the two orthogonal projectors; for matrices
$\mathbf{U}$, $\mathbf{V}$ with orthonormal columns these are the singular values of
$\mathbf{U}^{\mathsf{H}}\mathbf{V}$. The sines are the singular values of
$(\mathbf{I} - \mathbf{P}_{\mathbf{X}})\mathbf{P}_{\mathbf{Y}}$. The tangents are the singular
values of the tangent matrix, in `NLAlib.Matrix.Subspaces.Tangent`.

The angle depends only on the column spaces, so $\mathbf{X}$ and $\mathbf{Y}$ may be orthonormal
frames, arbitrary bases, or the projectors themselves. Beyond the smaller of the two dimensions
the angle is $\pi / 2$.

Statements about distances between subspaces are made with the matrices, in a norm:
$\|(\mathbf{I} - \mathbf{P})\mathbf{Q}\|_2$, $\|(\mathbf{I} - \mathbf{P})\mathbf{Q}\|_{\mathsf{F}}$.
This file identifies those norms with the angles.

## Main definitions

* `NLAlib.principalAngle`: the $k$-th principal angle between two column spaces.

## Main results

* `NLAlib.HasOrthonormalCols.principalAngle_mul_left`, `NLAlib.principalAngle_submatrix_equiv`:
  invariance under an isometry of the ambient space and under relabelling.
* `NLAlib.cos_principalAngle`, `NLAlib.HasOrthonormalCols.cos_principalAngle`: cosines.
* `NLAlib.singularValues_one_sub_rangeProjector_mul_rangeProjector`: sines.
* `NLAlib.specNorm_one_sub_rangeProjector_mul_rangeProjector`,
  `NLAlib.specNorm_rangeProjector_sub_rangeProjector`: the largest angle as a distance.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p q r : Type*} [Fintype n] [Fintype p] [Fintype q] [Fintype r]

/-- The **$k$-th principal angle** $\theta_k(\mathbf{X}, \mathbf{Y})$ between the column spaces of
$\mathbf{X}$ and $\mathbf{Y}$, $k = 0, 1, \dots$, in non-decreasing order: the angle in $[0, \pi/2]$
whose cosine is $\sigma_k(\mathbf{P}_{\mathbf{X}}\mathbf{P}_{\mathbf{Y}})$, the $k$-th singular
value of the product of the two orthogonal projectors. For $k$ at least the smaller of the two
dimensions it is $\pi / 2$.
[GolubVanLoan2013, §6.4.3]; [StewartSun1990, §I.5].
Port of `NLAlib.principalAnglesFintype`, there for two frames with the same number of columns. -/
noncomputable def principalAngle (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) : ℝ :=
  Real.arccos (singularValues (rangeProjector X * rangeProjector Y) k)

/-! ### Basic properties -/

/-- The singular values of a product of two orthogonal projectors are at most one. -/
private theorem singularValues_rangeProjector_mul_rangeProjector_le_one (X : Matrix n p 𝕜)
    (Y : Matrix n q 𝕜) (k : ℕ) : singularValues (rangeProjector X * rangeProjector Y) k ≤ 1 :=
  (singularValues_le_specNorm _ k).trans
    (((isStarProjection_rangeProjector X).specNorm_mul_le _).trans
      (isStarProjection_rangeProjector Y).specNorm_le_one)

/-- Principal angles lie in $[0, \pi/2]$. Port of `NLAlib.principalAngles_mem_Icc`. -/
theorem principalAngle_mem_Icc (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    principalAngle X Y k ∈ Set.Icc 0 (Real.pi / 2) := by
  exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr (singularValues_nonneg _ k)⟩

/-- Principal angles are non-decreasing in the index.
Port of `NLAlib.principalAngles_monotone`. -/
theorem principalAngle_monotone (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) :
    Monotone (principalAngle X Y) := by
  exact fun i j hij => Real.antitone_arccos (singularValues_antitone _ hij)

/-- Principal angles are symmetric in the two subspaces:
$\theta_k(\mathbf{X}, \mathbf{Y}) = \theta_k(\mathbf{Y}, \mathbf{X})$. Port of
`NLAlib.principalAngles_comm`. -/
theorem principalAngle_comm (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    principalAngle X Y k = principalAngle Y X k := by
  unfold principalAngle
  rw [← singularValues_conjTranspose, Matrix.conjTranspose_mul, conjTranspose_rangeProjector,
    conjTranspose_rangeProjector]

/-- Principal angles depend only on the column spaces.
Port of `NLAlib.principalAngles_eq_of_range_eq`. -/
theorem principalAngle_congr {X : Matrix n p 𝕜} {X' : Matrix n r 𝕜} {Y : Matrix n q 𝕜}
    {Y' : Matrix n r 𝕜} (hX : LinearMap.range X.mulVecLin = LinearMap.range X'.mulVecLin)
    (hY : LinearMap.range Y.mulVecLin = LinearMap.range Y'.mulVecLin) (k : ℕ) :
    principalAngle X Y k = principalAngle X' Y' k := by
  unfold principalAngle
  rw [rangeProjector_inj.mpr hX, rangeProjector_inj.mpr hY]

/-- The principal angles of a matrix and of its range projector agree. -/
@[simp]
theorem principalAngle_rangeProjector_left (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    principalAngle (rangeProjector X) Y k = principalAngle X Y k := by
  unfold principalAngle
  rw [(isStarProjection_rangeProjector X).rangeProjector_eq]

/-- The principal angles of a matrix and of its range projector agree. -/
@[simp]
theorem principalAngle_rangeProjector_right (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    principalAngle X (rangeProjector Y) k = principalAngle X Y k := by
  unfold principalAngle
  rw [(isStarProjection_rangeProjector Y).rangeProjector_eq]

/-- Beyond the smaller of the two dimensions the principal angle is $\pi / 2$:
$\theta_k(\mathbf{X}, \mathbf{Y}) = \pi / 2$ for
$\min(\operatorname{rank} \mathbf{X}, \operatorname{rank} \mathbf{Y}) \le k$. -/
theorem principalAngle_of_rank_le {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜} {k : ℕ}
    (h : min X.rank Y.rank ≤ k) : principalAngle X Y k = Real.pi / 2 := by
  have hr : (rangeProjector X * rangeProjector Y).rank ≤ k := by
    have h1 := Matrix.rank_mul_le (rangeProjector X) (rangeProjector Y)
    rw [rank_rangeProjector, rank_rangeProjector] at h1
    exact h1.trans h
  unfold principalAngle
  rw [(singularValues_eq_zero_iff _).mpr hr, Real.arccos_zero]

/-- The principal angles between a subspace and itself vanish, up to its dimension:
$\theta_k(\mathbf{X}, \mathbf{X}) = 0$ for $k < \operatorname{rank} \mathbf{X}$. -/
theorem principalAngle_self (X : Matrix n p 𝕜) {k : ℕ} (hk : k < X.rank) :
    principalAngle X X k = 0 := by
  unfold principalAngle
  rw [rangeProjector_mul_rangeProjector,
    (isStarProjection_rangeProjector X).singularValues_of_lt_rank (by rwa [rank_rangeProjector]),
    Real.arccos_one]

/-- If the column space of $\mathbf{Y}$ is inside that of $\mathbf{X}$, the principal angles
vanish up to the dimension of the smaller space: $\theta_k(\mathbf{X}, \mathbf{Y}) = 0$ for
$k < \operatorname{rank} \mathbf{Y}$. Port of `NLAlib.directedSubspaceGap_eq_zero_of_range_le`. -/
theorem principalAngle_eq_zero_of_range_le {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range X.mulVecLin) {k : ℕ} (hk : k < Y.rank) :
    principalAngle X Y k = 0 := by
  have h0 := principalAngle_self Y hk
  unfold principalAngle at h0 ⊢
  rwa [rangeProjector_mul_rangeProjector_of_range_le h, ← rangeProjector_mul_rangeProjector Y]

/-! ### Invariance -/

section Invariance

variable {m p' q' : Type*} [Fintype m] [Fintype p'] [Fintype q']

/-- **Principal angles are invariant under an isometry of the ambient space**: multiplying both
matrices on the left by a matrix $\mathbf{Q}$ with orthonormal columns, square or not, does not
change the angles between their column spaces. [StewartSun1990, §I.5]. -/
theorem HasOrthonormalCols.principalAngle_mul_left [DecidableEq n] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    principalAngle (Q * X) (Q * Y) k = principalAngle X Y k := by
  unfold principalAngle
  rw [hQ.rangeProjector_mul, hQ.rangeProjector_mul, Matrix.mul_assoc (Q * rangeProjector X),
    ← Matrix.mul_assoc Qᴴ, hQ.conjTranspose_mul_cancel_left, Matrix.mul_assoc Q,
    ← Matrix.mul_assoc (rangeProjector X), hQ.singularValues_mul_left,
    hQ.singularValues_mul_conjTranspose_right]

/-- Relabelling the columns by an equivalence does not change the column space. -/
private theorem rangeProjector_submatrix_id_equiv (X : Matrix n p 𝕜) (f : p' ≃ p) :
    rangeProjector (X.submatrix id f) = rangeProjector X := by
  rw [rangeProjector_inj, Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  exact congrArg _ (f.surjective.range_comp X.col)

/-- **Principal angles are invariant under relabelling**: a common relabelling of the rows by an
equivalence, together with any relabelling of the columns of either matrix, does not change the
angles. For `Matrix.reindex`, rewrite with `Matrix.reindex_apply` first.
[StewartSun1990, §I.5]. Port of `NLAlib.sinePrincipalAngles_reindex_rows`, there over
$\mathbb{R}$ for the matrix of sines of two frames and a relabelling of the rows only. -/
theorem principalAngle_submatrix_equiv (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (e : m ≃ n)
    (f : p' ≃ p) (g : q' ≃ q) (k : ℕ) :
    principalAngle (X.submatrix e f) (Y.submatrix e g) k = principalAngle X Y k := by
  classical
  have hQ : HasOrthonormalCols ((1 : Matrix n n 𝕜).submatrix e id) :=
    hasOrthonormalCols_one.submatrix e Function.injective_id
  have hX : X.submatrix e f = (1 : Matrix n n 𝕜).submatrix e id * X.submatrix id f := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
  have hY : Y.submatrix e g = (1 : Matrix n n 𝕜).submatrix e id * Y.submatrix id g := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
  rw [hX, hY, hQ.principalAngle_mul_left]
  unfold principalAngle
  rw [rangeProjector_submatrix_id_equiv, rangeProjector_submatrix_id_equiv]

end Invariance

/-! ### Cosines -/

/-- The cosines of the principal angles are the singular values of the product of the two
projectors: $\cos \theta_k(\mathbf{X}, \mathbf{Y}) =
\sigma_k(\mathbf{P}_{\mathbf{X}}\mathbf{P}_{\mathbf{Y}})$. -/
theorem cos_principalAngle (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    Real.cos (principalAngle X Y k) =
      singularValues (rangeProjector X * rangeProjector Y) k := by
  exact Real.cos_arccos
    (by linarith [singularValues_nonneg (rangeProjector X * rangeProjector Y) k])
    (singularValues_rangeProjector_mul_rangeProjector_le_one X Y k)

/-- **Cosines for orthonormal frames**: for $\mathbf{U}$ and $\mathbf{V}$ with orthonormal
columns, the cosines of the principal angles between their column spaces are the singular values
of $\mathbf{U}^{\mathsf{H}}\mathbf{V}$:
$\cos \theta_k(\mathbf{U}, \mathbf{V}) = \sigma_k(\mathbf{U}^{\mathsf{H}}\mathbf{V})$ for every
$k$.
[GolubVanLoan2013, §6.4.3]. Port of `NLAlib.cos_principalAngles`.
Result: principal-angles -/
theorem HasOrthonormalCols.cos_principalAngle [DecidableEq p] [DecidableEq q]
    {U : Matrix n p 𝕜} {V : Matrix n q 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) (k : ℕ) :
    Real.cos (principalAngle U V k) = singularValues (Uᴴ * V) k := by
  rw [NLAlib.cos_principalAngle, hU.rangeProjector_eq, hV.rangeProjector_eq, Matrix.mul_assoc,
    ← Matrix.mul_assoc Uᴴ, hU.singularValues_mul_left, hV.singularValues_mul_conjTranspose_right]

/-- Cosines when only the first frame is orthonormal: the singular values of
$\mathbf{U}^{\mathsf{H}}\mathbf{P}_{\mathbf{Y}}$. -/
theorem HasOrthonormalCols.cos_principalAngle_left [DecidableEq p] {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (Y : Matrix n q 𝕜) (k : ℕ) :
    Real.cos (principalAngle U Y k) = singularValues (Uᴴ * rangeProjector Y) k := by
  rw [NLAlib.cos_principalAngle, hU.rangeProjector_eq, Matrix.mul_assoc,
    hU.singularValues_mul_left]

/-! ### Sines -/

/-- The sine of a principal angle from its cosine:
$\sin \theta_k(\mathbf{X}, \mathbf{Y}) = \sqrt{1 -
\sigma_k(\mathbf{P}_{\mathbf{X}}\mathbf{P}_{\mathbf{Y}})^2}$.
Port of `NLAlib.sin_principalAngles`. -/
theorem sin_principalAngle (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    Real.sin (principalAngle X Y k) =
      √(1 - singularValues (rangeProjector X * rangeProjector Y) k ^ 2) := by
  exact Real.sin_arccos _

variable [DecidableEq n]

/-- **Sines of the principal angles**: the singular values of
$(\mathbf{I} - \mathbf{P}_{\mathbf{X}})\mathbf{P}_{\mathbf{Y}}$, in reverse order:
$\sigma_i((\mathbf{I} - \mathbf{P}_{\mathbf{X}})\mathbf{P}_{\mathbf{Y}}) = \sin \theta_j(\mathbf{X},
\mathbf{Y})$ for $i + j + 1 = \operatorname{rank} \mathbf{Y}$.
[GolubVanLoan2013, §2.5.3]; [StewartSun1990, Theorem I.5.5].
Result: principal-angles -/
theorem singularValues_one_sub_rangeProjector_mul_rangeProjector (X : Matrix n p 𝕜)
    (Y : Matrix n q 𝕜) {i j : ℕ} (hij : i + j + 1 = Y.rank) :
    singularValues ((1 - rangeProjector X) * rangeProjector Y) i =
      Real.sin (principalAngle X Y j) := by
  have h := (isStarProjection_rangeProjector Y).singularValues_one_sub_mul_sq
    (isStarProjection_rangeProjector X) (i := i) (j := j) (by rw [rank_rangeProjector, hij])
  rw [sin_principalAngle, ← h, Real.sqrt_sq (singularValues_nonneg _ _)]

/-- Sines for orthonormal frames: the singular values of
$(\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf{H}})\mathbf{V}$, in reverse order:
$\sigma_i((\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf{H}})\mathbf{V})
= \sin \theta_j(\mathbf{U}, \mathbf{V})$ for $i + j + 1 = \lvert q \rvert$.
Port of `NLAlib.transpose_sinePrincipalAngles_mul_self` and
`NLAlib.specNorm_sinePrincipalAngles_eq_residual`. -/
theorem HasOrthonormalCols.singularValues_one_sub_mul_conjTranspose_mul [DecidableEq p]
    [DecidableEq q]
    {U : Matrix n p 𝕜} {V : Matrix n q 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) {i j : ℕ} (hij : i + j + 1 = Fintype.card q) :
    singularValues ((1 - U * Uᴴ) * V) i = Real.sin (principalAngle U V j) := by
  rw [← singularValues_one_sub_rangeProjector_mul_rangeProjector U V (by rw [hV.rank_eq, hij]),
    hU.rangeProjector_eq, hV.rangeProjector_eq, ← Matrix.mul_assoc,
    hV.singularValues_mul_conjTranspose_right]

/-- **The largest principal angle as a distance**:
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{X}})\mathbf{P}_{\mathbf{Y}}\|_2 = \sin \theta_j(\mathbf{X},
\mathbf{Y})$ for $j + 1 = \operatorname{rank} \mathbf{Y}$, the sine of the largest principal angle
counted up to the dimension of the column space of $\mathbf{Y}$.
[GolubVanLoan2013, §2.5.3]. Port of `NLAlib.directedSubspaceGap_eq_sin_principalAngles`.
Result: principal-angles -/
theorem specNorm_one_sub_rangeProjector_mul_rangeProjector (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜)
    {j : ℕ} (hj : j + 1 = Y.rank) :
    specNorm ((1 - rangeProjector X) * rangeProjector Y) = Real.sin (principalAngle X Y j) := by
  rw [← singularValues_zero_eq_specNorm]
  exact singularValues_one_sub_rangeProjector_mul_rangeProjector X Y (by omega)

/-- The Frobenius norm of $(\mathbf{I} - \mathbf{P}_{\mathbf{X}})\mathbf{P}_{\mathbf{Y}}$ is the
root sum of squares of the sines of the principal angles:
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{X}})\mathbf{P}_{\mathbf{Y}}\|_{\mathsf{F}}^2
= \sum_{j < \operatorname{rank} \mathbf{Y}} \sin^2 \theta_j(\mathbf{X},
\mathbf{Y})$. Port of `NLAlib.frobNorm_sinePrincipalAngles_eq_residual`. -/
theorem frobNorm_one_sub_rangeProjector_mul_rangeProjector_sq (X : Matrix n p 𝕜)
    (Y : Matrix n q 𝕜) :
    frobNorm ((1 - rangeProjector X) * rangeProjector Y) ^ 2 =
      ∑ j ∈ Finset.range Y.rank, Real.sin (principalAngle X Y j) ^ 2 := by
  have hr : ((1 - rangeProjector X) * rangeProjector Y).rank ≤ Y.rank :=
    (Matrix.rank_mul_le_right _ _).trans (rank_rangeProjector Y).le
  rw [frobNorm_sq_eq_sum_range_singularValues_sq _ hr, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [singularValues_one_sub_rangeProjector_mul_rangeProjector X Y (j := j) (by omega)]

omit [DecidableEq n] in
/-- **The distance between two projectors of equal rank** is the sine of the largest principal
angle: if $\operatorname{rank} \mathbf{X} = \operatorname{rank} \mathbf{Y} = j + 1$, then
$\|\mathbf{P}_{\mathbf{X}} - \mathbf{P}_{\mathbf{Y}}\|_2 = \sin \theta_j(\mathbf{X}, \mathbf{Y})$.
[GolubVanLoan2013, §2.5.3].
Port of `NLAlib.specNorm_sinePrincipalAngles_eq_projector_distance`.
Result: projector-gap -/
theorem specNorm_rangeProjector_sub_rangeProjector {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜}
    (h : X.rank = Y.rank) {j : ℕ} (hj : j + 1 = Y.rank) :
    specNorm (rangeProjector X - rangeProjector Y) = Real.sin (principalAngle X Y j) := by
  classical
  rw [specNorm_sub_comm, (isStarProjection_rangeProjector Y).specNorm_sub_eq_of_rank_eq
    (isStarProjection_rangeProjector X) (by rw [rank_rangeProjector, rank_rangeProjector, h]),
    specNorm_one_sub_rangeProjector_mul_rangeProjector X Y hj]

omit [DecidableEq n] in
/-- For two subspaces of equal dimension,
$\|\mathbf{P}_{\mathbf{X}} - \mathbf{P}_{\mathbf{Y}}\|_{\mathsf{F}}^2
= 2 \sum_{j < \operatorname{rank} \mathbf{Y}} \sin^2 \theta_j(\mathbf{X}, \mathbf{Y})$.
Port of `NLAlib.frobSq_projector_distance_eq_two_mul_sinePrincipalAngles`. -/
theorem frobNorm_rangeProjector_sub_rangeProjector_sq {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜}
    (h : X.rank = Y.rank) :
    frobNorm (rangeProjector X - rangeProjector Y) ^ 2 =
      2 * ∑ j ∈ Finset.range Y.rank, Real.sin (principalAngle X Y j) ^ 2 := by
  classical
  rw [frobNorm_sub_comm, (isStarProjection_rangeProjector Y).frobNorm_sub_sq_of_rank_eq
    (isStarProjection_rangeProjector X) (by rw [rank_rangeProjector, rank_rangeProjector, h]),
    frobNorm_one_sub_rangeProjector_mul_rangeProjector_sq]

end NLAlib
