/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.ComplementaryProjector
public import NLAlib.Matrix.Norms.Projector
public import NLAlib.Matrix.Norms.UnitarilyInvariant

/-!
# Pairs of orthogonal projectors

Two subspaces are compared through their orthogonal projectors $\mathbf{P}$ and $\mathbf{Q}$
(star projections). The matrix $(\mathbf{I} - \mathbf{Q})\mathbf{P}$ measures how far the range of
$\mathbf{P}$ is from the range of $\mathbf{Q}$: its singular values are the sines of the principal
angles between the two ranges (see `NLAlib.Matrix.Subspaces.PrincipalAngles`), and it is the object
that perturbation theorems bound. This file relates it to the difference $\mathbf{P} - \mathbf{Q}$,
to the product $\mathbf{Q}\mathbf{P}$, and to the same quantity with the roles exchanged.

## Main results

* `NLAlib.singularValues_sq_eq_one_sub_of_conjTranspose_mul_self_add_eq_one`: if
  $\mathbf{A}^{\mathsf{H}}\mathbf{A} + \mathbf{B}^{\mathsf{H}}\mathbf{B} = \mathbf{I}$, the singular
  values of $\mathbf{B}$ are $\sqrt{1 - \sigma^2}$ for those $\sigma$ of $\mathbf{A}$, in reverse
  order (the value part of the thin CS decomposition).
* `IsStarProjection.singularValues_one_sub_mul_sq`: the singular values of
  $(\mathbf{I} - \mathbf{Q})\mathbf{P}$ from those of $\mathbf{Q}\mathbf{P}$.
* `IsStarProjection.singularValues_of_lt_rank`: the nonzero singular values of an orthogonal
  projector are $1$.
* `IsStarProjection.singularValues_one_sub_mul_eq_of_rank_eq`: for projectors of equal rank,
  $(\mathbf{I} - \mathbf{Q})\mathbf{P}$ and $(\mathbf{I} - \mathbf{P})\mathbf{Q}$ have the same
  singular values.
* `IsStarProjection.specNorm_sub_eq_max`, `IsStarProjection.specNorm_sub_eq_of_rank_eq`: the gap
  $\|\mathbf{P} - \mathbf{Q}\|_2$.
* `IsStarProjection.frobNorm_sub_sq`: the gap in the Frobenius norm.
* `IsStarProjection.matrixNorm_one_sub_mul_le_add`: the triangle inequality for directed gaps, in
  every unitarily invariant norm.
* `IsStarProjection.rank_eq_of_specNorm_sub_lt_one`: projectors at distance less than one have
  the same rank.
* `NLAlib.HasOrthonormalCols.frobNorm_one_sub_mul_sq`,
  `NLAlib.HasOrthonormalCols.frobNorm_mul_conjTranspose_sub_mul_conjTranspose`: the Frobenius
  distance between two frames.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

/-! ### Complementary Gram matrices -/

/-- **The value part of the thin CS decomposition.** If
$\mathbf{A}^{\mathsf{H}}\mathbf{A} + \mathbf{B}^{\mathsf{H}}\mathbf{B} = \mathbf{I}$, the squared
singular values of $\mathbf{B}$ are one minus those of $\mathbf{A}$, in reverse order:
$\sigma_i(\mathbf{B})^2 = 1 - \sigma_j(\mathbf{A})^2$ for $i + j + 1 = \lvert p \rvert$, the
number of columns.
[GolubVanLoan2013, Theorem 2.5.2]. -/
theorem singularValues_sq_eq_one_sub_of_conjTranspose_mul_self_add_eq_one [DecidableEq p]
    {A : Matrix m p 𝕜} {B : Matrix n p 𝕜} (h : Aᴴ * A + Bᴴ * B = 1) {i j : ℕ}
    (hij : i + j + 1 = Fintype.card p) :
    singularValues B i ^ 2 = 1 - singularValues A j ^ 2 := by
  have hB : Bᴴ * B = -(Aᴴ * A) + (1 : ℝ) • (1 : Matrix p p 𝕜) := by
    rw [one_smul, ← h]
    abel
  rw [singularValues_sq, singularValues_sq, hB,
    (Matrix.isHermitian_conjTranspose_mul_self A).neg.eigenvalue_add_smul_one 1 (by omega),
    eigenvalue_neg _ hij]
  ring

/-- If $\mathbf{A}^{\mathsf{H}}\mathbf{A} + \mathbf{B}^{\mathsf{H}}\mathbf{B} = \mathbf{I}$, the
singular values of $\mathbf{A}$ are at most one. -/
theorem singularValues_le_one_of_conjTranspose_mul_self_add_eq_one [DecidableEq p]
    {A : Matrix m p 𝕜} {B : Matrix n p 𝕜} (h : Aᴴ * A + Bᴴ * B = 1) (i : ℕ) :
    singularValues A i ≤ 1 := by
  rcases le_or_gt (Fintype.card p) i with hi | hi
  · rw [singularValues_of_card_cols_le A hi]
    exact zero_le_one
  · have hsq := singularValues_sq_eq_one_sub_of_conjTranspose_mul_self_add_eq_one h
      (i := Fintype.card p - 1 - i) (j := i) (by omega)
    have h1 : singularValues A i ^ 2 ≤ 1 := by
      have := sq_nonneg (singularValues B (Fintype.card p - 1 - i))
      linarith
    exact (sq_le_one_iff₀ (singularValues_nonneg A i)).mp h1

/-- If $\mathbf{U}\mathbf{U}^{\mathsf{H}} + \mathbf{W}\mathbf{W}^{\mathsf{H}} = \mathbf{I}$ and
$\mathbf{W}$ has orthonormal columns, then $\mathbf{W}^{\mathsf{H}}\mathbf{A}$ and
$(\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf{H}})\mathbf{A}$ have the same singular values: the
complement of a subspace can be given by a frame or by a projector. -/
theorem HasOrthonormalCols.singularValues_conjTranspose_mul_eq_of_mul_conjTranspose_add_eq_one
    [DecidableEq n]
    [DecidableEq q] {U : Matrix n p 𝕜} {W : Matrix n q 𝕜} (hW : HasOrthonormalCols W)
    (h : U * Uᴴ + W * Wᴴ = 1) (A : Matrix n m 𝕜) :
    singularValues (Wᴴ * A) = singularValues ((1 - U * Uᴴ) * A) := by
  rw [← h, add_sub_cancel_left, Matrix.mul_assoc, hW.singularValues_mul_left]

/-! ### Traces and diagonals of a projector -/

/-- The trace of an orthogonal projector is its rank:
$\operatorname{tr} \mathbf{P} = \operatorname{rank} \mathbf{P}$. -/
theorem _root_.IsStarProjection.trace_eq_rank {P : Matrix n n 𝕜} (hP : IsStarProjection P) :
    P.trace = P.rank := by
  have h := trace_rangeProjector P
  rwa [hP.rangeProjector_eq] at h

/-- The diagonal entries of an orthogonal projector (the leverage scores of its range) lie in
$[0, 1]$: $0 \le \operatorname{Re} \mathbf{P}_{i,i} \le 1$. -/
theorem _root_.IsStarProjection.re_apply_self_mem_Icc {P : Matrix n n 𝕜}
    (hP : IsStarProjection P) (i : n) : RCLike.re (P i i) ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  have h0 := (RCLike.nonneg_iff.mp (hP.posSemidef.diag_nonneg (i := i))).1
  have h1 := (RCLike.nonneg_iff.mp (hP.one_sub.posSemidef.diag_nonneg (i := i))).1
  rw [Matrix.sub_apply, Matrix.one_apply_eq, map_sub, RCLike.one_re] at h1
  exact ⟨h0, by linarith⟩

/-- The diagonal entries of an orthogonal projector sum to its rank:
$\sum_i \operatorname{Re} \mathbf{P}_{i,i} = \operatorname{rank} \mathbf{P}$. -/
theorem _root_.IsStarProjection.sum_re_apply_self {P : Matrix n n 𝕜} (hP : IsStarProjection P) :
    ∑ i, RCLike.re (P i i) = P.rank := by
  have h := congrArg RCLike.re hP.trace_eq_rank
  rwa [Matrix.trace, map_sum, RCLike.natCast_re] at h

/-- A diagonal entry of an orthogonal projector is the squared norm of the corresponding
column: $\operatorname{Re} \mathbf{P}_{i,i} = \|\mathbf{p}_i\|^2$ with $\mathbf{p}_i$ column $i$ of
$\mathbf{P}$. -/
theorem _root_.IsStarProjection.re_apply_self_eq_norm_sq {P : Matrix n n 𝕜}
    (hP : IsStarProjection P) (i : n) :
    RCLike.re (P i i) = ‖WithLp.toLp 2 (P.col i)‖ ^ 2 := by
  rw [EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct, ← conjTranspose_mul_self_apply,
    hP.conjTranspose_eq, hP.mul_self]

/-- The trace of a product of two orthogonal projectors is the squared Frobenius norm of the
product: $\operatorname{Re} \operatorname{tr}(\mathbf{P}\mathbf{Q})
= \|\mathbf{P}\mathbf{Q}\|_{\mathsf{F}}^2$. -/
theorem _root_.IsStarProjection.re_trace_mul {P Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : RCLike.re (P * Q).trace = frobNorm (P * Q) ^ 2 := by
  rw [frobNorm_sq_eq_re_trace, Matrix.conjTranspose_mul, hP.conjTranspose_eq,
    hQ.conjTranspose_eq, Matrix.mul_assoc, ← Matrix.mul_assoc P, hP.mul_self,
    Matrix.trace_mul_comm Q (P * Q), Matrix.mul_assoc, hQ.mul_self]

/-- Orthogonal projectors are ordered as their ranges: $\mathbf{P} \preceq \mathbf{Q}$ exactly
when $\mathbf{Q}\mathbf{P} = \mathbf{P}$. -/
theorem _root_.IsStarProjection.le_iff_mul_eq {P Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : P ≤ Q ↔ Q * P = P := by
  classical
  refine ⟨fun h => ?_, hP.le_of_mul_eq_right hQ⟩
  have h1 := conjTranspose_mul_mul_le_conjTranspose_mul_mul h (1 - Q)
  have hQ0 : (1 - Q)ᴴ * Q * (1 - Q) = 0 := by
    rw [Matrix.mul_assoc, hQ.mul_one_sub_self, Matrix.mul_zero]
  have hPP : (1 - Q)ᴴ * P * (1 - Q) = (P * (1 - Q))ᴴ * (P * (1 - Q)) := by
    rw [Matrix.conjTranspose_mul, hP.conjTranspose_eq, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc P P, hP.mul_self]
  rw [hQ0, hPP] at h1
  have h2 : (P * (1 - Q))ᴴ * (P * (1 - Q)) = 0 :=
    le_antisymm h1 (Matrix.posSemidef_conjTranspose_mul_self _).nonneg
  have h3 : P * Q = P := by
    have := Matrix.conjTranspose_mul_self_eq_zero.mp h2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  have h4 := congrArg Matrix.conjTranspose h3
  rwa [Matrix.conjTranspose_mul, hP.conjTranspose_eq, hQ.conjTranspose_eq] at h4

/-! ### The matrix $(\mathbf{I} - \mathbf{Q})\mathbf{P}$ -/

variable [DecidableEq n]

/-- The difference of two matrices in terms of the two one-sided products:
$\mathbf{P} - \mathbf{Q} = (\mathbf{I} - \mathbf{Q})\mathbf{P} - \mathbf{Q}(\mathbf{I} -
\mathbf{P})$. -/
theorem sub_eq_one_sub_mul_sub_mul_one_sub (P Q : Matrix n n 𝕜) :
    P - Q = (1 - Q) * P - Q * (1 - P) := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  abel

/-- The Gram matrix of $(\mathbf{I} - \mathbf{Q})\mathbf{P}$, for orthogonal projectors
$\mathbf{P}$, $\mathbf{Q}$: $((\mathbf{I} - \mathbf{Q})\mathbf{P})^{\mathsf{H}}(\mathbf{I} -
\mathbf{Q})\mathbf{P} = \mathbf{P} - \mathbf{P}\mathbf{Q}\mathbf{P}$. -/
theorem _root_.IsStarProjection.conjTranspose_one_sub_mul_mul_one_sub_mul {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    ((1 - Q) * P)ᴴ * ((1 - Q) * P) = P - P * Q * P := by
  rw [Matrix.conjTranspose_mul, hP.conjTranspose_eq, hQ.one_sub.conjTranspose_eq,
    Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Q), hQ.one_sub.mul_self, Matrix.sub_mul,
    Matrix.one_mul, Matrix.mul_sub, hP.mul_self, Matrix.mul_assoc]

/-- The products of a star projection $\mathbf{P} = \mathbf{U}\mathbf{U}^{\mathsf{H}}$ with
$\mathbf{Q}$ and $\mathbf{I} - \mathbf{Q}$ have the singular values of the complementary pair
$\mathbf{Q}\mathbf{U}$, $(\mathbf{I} - \mathbf{Q})\mathbf{U}$. -/
private theorem exists_complementary_pair {P Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) :
    ∃ (A B : Matrix n (Fin P.rank) 𝕜), Aᴴ * A + Bᴴ * B = 1 ∧
      singularValues (Q * P) = singularValues A ∧
      singularValues ((1 - Q) * P) = singularValues B := by
  obtain ⟨U, hU, hUP⟩ := hP.exists_hasOrthonormalCols_mul_conjTranspose_eq
    (p := Fin P.rank) (Fintype.card_fin _)
  have h1 : ∀ X : Matrix n n 𝕜, X * P = X * U * Uᴴ := fun X => by rw [Matrix.mul_assoc, hUP]
  refine ⟨Q * U, (1 - Q) * U, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQ.conjTranspose_eq,
      hQ.one_sub.conjTranspose_eq, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ.mul_self,
      Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Q), hQ.one_sub.mul_self, ← Matrix.mul_add,
      ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul, hU.conjTranspose_mul_self]
  · rw [h1, hU.singularValues_mul_conjTranspose_right]
  · rw [h1, hU.singularValues_mul_conjTranspose_right]

/-- **The singular values of $(\mathbf{I} - \mathbf{Q})\mathbf{P}$** in terms of those of
$\mathbf{Q}\mathbf{P}$, for orthogonal projectors: $\sigma_i((\mathbf{I} - \mathbf{Q})\mathbf{P})^2
= 1 - \sigma_j(\mathbf{Q}\mathbf{P})^2$ for $i + j + 1 = \operatorname{rank}
\mathbf{P}$. These are the squared sines and cosines of the principal angles between the ranges.
[GolubVanLoan2013, §2.5.3]. -/
theorem _root_.IsStarProjection.singularValues_one_sub_mul_sq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) {i j : ℕ} (hij : i + j + 1 = P.rank) :
    singularValues ((1 - Q) * P) i ^ 2 = 1 - singularValues (Q * P) j ^ 2 := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_complementary_pair hP hQ
  rw [hA, hB]
  exact singularValues_sq_eq_one_sub_of_conjTranspose_mul_self_add_eq_one hAB
    (by rw [Fintype.card_fin, hij])

omit [DecidableEq n] in
/-- The singular values of an orthogonal projector are $1$ below its rank:
$\sigma_k(\mathbf{P}) = 1$ for $k < \operatorname{rank} \mathbf{P}$. From the rank on they vanish,
as for every matrix (`NLAlib.singularValues_eq_zero_iff`). -/
theorem _root_.IsStarProjection.singularValues_of_lt_rank {P : Matrix n n 𝕜}
    (hP : IsStarProjection P) {k : ℕ} (hk : k < P.rank) : singularValues P k = 1 := by
  classical
  have h := hP.singularValues_one_sub_mul_sq hP (i := P.rank - 1 - k) (j := k) (by omega)
  rw [hP.one_sub_mul_self, singularValues_zero, hP.mul_self, Pi.zero_apply] at h
  refine (sq_eq_sq₀ (singularValues_nonneg P k) zero_le_one).mp ?_
  linarith

/-- The spectral norm of $(\mathbf{I} - \mathbf{Q})\mathbf{P}$ from the smallest relevant singular
value of $\mathbf{Q}\mathbf{P}$: $\|(\mathbf{I} - \mathbf{Q})\mathbf{P}\|_2^2 = 1 -
\sigma_k(\mathbf{Q}\mathbf{P})^2$ for $k + 1 = \operatorname{rank} \mathbf{P}$. -/
theorem _root_.IsStarProjection.specNorm_one_sub_mul_sq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) {k : ℕ} (hk : k + 1 = P.rank) :
    specNorm ((1 - Q) * P) ^ 2 = 1 - singularValues (Q * P) k ^ 2 := by
  rw [← singularValues_zero_eq_specNorm]
  exact hP.singularValues_one_sub_mul_sq hQ (by omega)

/-- The Frobenius norm of $(\mathbf{I} - \mathbf{Q})\mathbf{P}$:
$\|(\mathbf{I} - \mathbf{Q})\mathbf{P}\|_{\mathsf{F}}^2 = \operatorname{rank} \mathbf{P} -
\|\mathbf{Q}\mathbf{P}\|_{\mathsf{F}}^2$. -/
theorem _root_.IsStarProjection.frobNorm_one_sub_mul_sq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    frobNorm ((1 - Q) * P) ^ 2 = P.rank - frobNorm (Q * P) ^ 2 := by
  have h := hQ.frobNorm_sq_eq_add P
  have hr := frobNorm_rangeProjector_sq P
  rw [hP.rangeProjector_eq] at hr
  linarith

/-- $\|(\mathbf{I} - \mathbf{Q})\mathbf{P}\|_2 \le 1$ for orthogonal projectors $\mathbf{P}$,
$\mathbf{Q}$. -/
theorem _root_.IsStarProjection.specNorm_one_sub_mul_le_one {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) : specNorm ((1 - Q) * P) ≤ 1 :=
  (hQ.one_sub.specNorm_mul_le P).trans hP.specNorm_le_one

/-- The acute case. $\|(\mathbf{I} - \mathbf{Q})\mathbf{P}\|_2 < 1$ exactly when $\mathbf{Q}$ is
injective on the range of $\mathbf{P}$, that is, when
$\operatorname{rank}(\mathbf{Q}\mathbf{P}) = \operatorname{rank} \mathbf{P}$. -/
theorem _root_.IsStarProjection.specNorm_one_sub_mul_lt_one_iff {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    specNorm ((1 - Q) * P) < 1 ↔ (Q * P).rank = P.rank := by
  have hle : (Q * P).rank ≤ P.rank := Matrix.rank_mul_le_right Q P
  rcases Nat.eq_zero_or_pos P.rank with h0 | hpos
  · have hP0 : P = 0 := Matrix.rank_eq_zero.mp h0
    rw [hP0, Matrix.mul_zero, Matrix.mul_zero, specNorm_zero]
    exact iff_of_true zero_lt_one rfl
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = P.rank := ⟨P.rank - 1, by omega⟩
    have hsq := hP.specNorm_one_sub_mul_sq hQ hk
    have hpos' := singularValues_pos_iff (Q * P) (k := k)
    have hσ := singularValues_nonneg (Q * P) k
    have hn := specNorm_nonneg ((1 - Q) * P)
    constructor
    · intro hlt
      have : 0 < singularValues (Q * P) k := by
        refine lt_of_le_of_ne hσ fun h0 => ?_
        rw [← h0] at hsq
        nlinarith
      have := hpos'.mp this
      omega
    · intro heq
      have : 0 < singularValues (Q * P) k := hpos'.mpr (by omega)
      nlinarith

/-- The triangle inequality for directed gaps, in every unitarily invariant norm
$\|\cdot\|_{\Phi}$: for orthogonal projectors $\mathbf{P}$, $\mathbf{R}$ and any square
$\mathbf{Q}$,
$\|(\mathbf{I} - \mathbf{P})\mathbf{R}\|_{\Phi} \le \|(\mathbf{I} - \mathbf{P})\mathbf{Q}\|_{\Phi} +
\|(\mathbf{I} - \mathbf{Q})\mathbf{R}\|_{\Phi}$. It chains a perturbation bound with an
approximation bound. -/
theorem _root_.IsStarProjection.matrixNorm_one_sub_mul_le_add (Φ : SymmetricGauge)
    {P R : Matrix n n 𝕜} (hP : IsStarProjection P) (hR : IsStarProjection R)
    (Q : Matrix n n 𝕜) :
    Φ.matrixNorm ((1 - P) * R) ≤ Φ.matrixNorm ((1 - P) * Q) + Φ.matrixNorm ((1 - Q) * R) := by
  have hsplit : (1 - P) * R = (1 - P) * Q * R + (1 - P) * ((1 - Q) * R) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
  rw [hsplit]
  refine (Φ.matrixNorm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (Φ.matrixNorm_mul_le_mul_specNorm _ R).trans
      (mul_le_of_le_one_right (Φ.matrixNorm_nonneg _) hR.specNorm_le_one)
  · exact Φ.matrixNorm_mul_le_of_isStarProjection hP.one_sub _

/-- Monotonicity of the residual in the subspace, in every unitarily invariant norm
$\|\cdot\|_{\Phi}$: a larger projector leaves a smaller residual; for orthogonal projectors
$\mathbf{P} \preceq \mathbf{Q}$,
$\|(\mathbf{I} - \mathbf{Q})\mathbf{A}\|_{\Phi} \le \|(\mathbf{I} -
\mathbf{P})\mathbf{A}\|_{\Phi}$. -/
theorem _root_.IsStarProjection.matrixNorm_one_sub_mul_le_of_le (Φ : SymmetricGauge)
    {P Q : Matrix n n 𝕜} (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P ≤ Q)
    (A : Matrix n m 𝕜) : Φ.matrixNorm ((1 - Q) * A) ≤ Φ.matrixNorm ((1 - P) * A) := by
  have hQP := (hP.le_iff_mul_eq hQ).mp h
  have h0 : (1 - Q) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hQP, sub_self]
  have hfac : (1 - Q) * A = (1 - Q) * ((1 - P) * A) := by
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, h0, sub_zero]
  rw [hfac]
  exact Φ.matrixNorm_mul_le_of_isStarProjection hQ.one_sub _

/-- The triangle inequality for directed gaps in the spectral norm:
$\|(\mathbf{I} - \mathbf{P})\mathbf{R}\|_2 \le \|(\mathbf{I} - \mathbf{P})\mathbf{Q}\|_2 +
\|(\mathbf{I} - \mathbf{Q})\mathbf{R}\|_2$. -/
theorem _root_.IsStarProjection.specNorm_one_sub_mul_le_add {P R : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (Q : Matrix n n 𝕜) :
    specNorm ((1 - P) * R) ≤ specNorm ((1 - P) * Q) + specNorm ((1 - Q) * R) := by
  have h := hP.matrixNorm_one_sub_mul_le_add (lpGauge ⊤) hR Q
  rwa [lpGauge_top_matrixNorm, lpGauge_top_matrixNorm, lpGauge_top_matrixNorm] at h

/-- The triangle inequality for directed gaps in the Frobenius norm:
$\|(\mathbf{I} - \mathbf{P})\mathbf{R}\|_{\mathsf{F}} \le \|(\mathbf{I} -
\mathbf{P})\mathbf{Q}\|_{\mathsf{F}} + \|(\mathbf{I} - \mathbf{Q})\mathbf{R}\|_{\mathsf{F}}$. -/
theorem _root_.IsStarProjection.frobNorm_one_sub_mul_le_add {P R : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (Q : Matrix n n 𝕜) :
    frobNorm ((1 - P) * R) ≤ frobNorm ((1 - P) * Q) + frobNorm ((1 - Q) * R) := by
  have h := hP.matrixNorm_one_sub_mul_le_add (lpGauge 2) hR Q
  rwa [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at h

/-! ### Projectors of equal rank -/

/-- **Symmetry for equal ranks.** For orthogonal projectors of the same rank,
$(\mathbf{I} - \mathbf{Q})\mathbf{P}$ and $(\mathbf{I} - \mathbf{P})\mathbf{Q}$ have the same
singular values, hence the same norm in every unitarily invariant norm. [GolubVanLoan2013, Theorem
2.5.1 context]. -/
theorem _root_.IsStarProjection.singularValues_one_sub_mul_eq_of_rank_eq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P.rank = Q.rank) :
    singularValues ((1 - Q) * P) = singularValues ((1 - P) * Q) := by
  funext i
  rcases lt_or_ge i P.rank with hi | hi
  · have hPQ : singularValues (Q * P) = singularValues (P * Q) := by
      rw [← singularValues_conjTranspose (P * Q), Matrix.conjTranspose_mul, hP.conjTranspose_eq,
        hQ.conjTranspose_eq]
    have h1 := hP.singularValues_one_sub_mul_sq hQ (i := i) (j := P.rank - 1 - i) (by omega)
    have h2 := hQ.singularValues_one_sub_mul_sq hP (i := i) (j := P.rank - 1 - i) (by omega)
    rw [hPQ, ← h2] at h1
    exact (sq_eq_sq₀ (singularValues_nonneg _ _) (singularValues_nonneg _ _)).mp h1
  · rw [(singularValues_eq_zero_iff _).mpr ((Matrix.rank_mul_le_right _ P).trans hi),
      (singularValues_eq_zero_iff _).mpr ((Matrix.rank_mul_le_right _ Q).trans (h ▸ hi))]

/-- For projectors of equal rank the two directed gaps agree in every unitarily invariant norm:
$\|(\mathbf{I} - \mathbf{Q})\mathbf{P}\|_{\Phi} = \|(\mathbf{I} -
\mathbf{P})\mathbf{Q}\|_{\Phi}$. -/
theorem _root_.IsStarProjection.matrixNorm_one_sub_mul_eq_of_rank_eq (Φ : SymmetricGauge)
    {P Q : Matrix n n 𝕜} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (h : P.rank = Q.rank) : Φ.matrixNorm ((1 - Q) * P) = Φ.matrixNorm ((1 - P) * Q) :=
  Φ.matrixNorm_congr (hP.singularValues_one_sub_mul_eq_of_rank_eq hQ h)

/-- For projectors of equal rank the two directed gaps agree in the spectral norm:
$\|(\mathbf{I} - \mathbf{Q})\mathbf{P}\|_2 = \|(\mathbf{I} - \mathbf{P})\mathbf{Q}\|_2$. -/
theorem _root_.IsStarProjection.specNorm_one_sub_mul_eq_of_rank_eq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P.rank = Q.rank) :
    specNorm ((1 - Q) * P) = specNorm ((1 - P) * Q) := by
  rw [← singularValues_zero_eq_specNorm, ← singularValues_zero_eq_specNorm,
    hP.singularValues_one_sub_mul_eq_of_rank_eq hQ h]

/-- For projectors of equal rank the two directed gaps agree in the Frobenius norm:
$\|(\mathbf{I} - \mathbf{Q})\mathbf{P}\|_{\mathsf{F}} = \|(\mathbf{I} -
\mathbf{P})\mathbf{Q}\|_{\mathsf{F}}$. -/
theorem _root_.IsStarProjection.frobNorm_one_sub_mul_eq_of_rank_eq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P.rank = Q.rank) :
    frobNorm ((1 - Q) * P) = frobNorm ((1 - P) * Q) := by
  have h2 := hP.matrixNorm_one_sub_mul_eq_of_rank_eq (lpGauge 2) hQ h
  rwa [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at h2

/-! ### The difference of two projectors -/

/-- A sum of two matrices with orthogonal supports on a projector and its complement has spectral
norm at most the larger of the two: if $\mathbf{X}\mathbf{P} = \mathbf{X}$,
$\mathbf{Y}(\mathbf{I} - \mathbf{P}) = \mathbf{Y}$ and
$\mathbf{X}^{\mathsf{H}}\mathbf{Y} = \mathbf{0}$, then
$\|\mathbf{X} + \mathbf{Y}\|_2 \le \max(\|\mathbf{X}\|_2, \|\mathbf{Y}\|_2)$. -/
theorem _root_.IsStarProjection.specNorm_add_le_max {P : Matrix n n 𝕜} (hP : IsStarProjection P)
    {X Y : Matrix m n 𝕜} (hX : X * P = X) (hY : Y * (1 - P) = Y) (hXY : Xᴴ * Y = 0) :
    specNorm (X + Y) ≤ max (specNorm X) (specNorm Y) := by
  have hc0 : 0 ≤ max (specNorm X) (specNorm Y) := (specNorm_nonneg X).trans (le_max_left _ _)
  refine (specNorm_le_iff hc0).2 fun x => ?_
  have horth : inner 𝕜 (WithLp.toLp 2 (X *ᵥ x)) (WithLp.toLp 2 (Y *ᵥ x)) = 0 := by
    rw [EuclideanSpace.inner_toLp_toLp_eq_star_dotProduct, Matrix.star_mulVec,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hXY, Matrix.zero_mulVec, dotProduct_zero]
  have hsum := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [← WithLp.toLp_add, ← Matrix.add_mulVec] at hsum
  have hx := norm_toLp_mulVec_le X (P *ᵥ x)
  have hy := norm_toLp_mulVec_le Y ((1 - P) *ᵥ x)
  rw [Matrix.mulVec_mulVec, hX] at hx
  rw [Matrix.mulVec_mulVec, hY] at hy
  have hsplit := norm_toLp_sq_eq_add_one_sub_rangeProjector P x
  rw [hP.rangeProjector_eq] at hsplit
  have hx' : ‖WithLp.toLp 2 (X *ᵥ x)‖ ≤
      max (specNorm X) (specNorm Y) * ‖WithLp.toLp 2 (P *ᵥ x)‖ :=
    hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hy' : ‖WithLp.toLp 2 (Y *ᵥ x)‖ ≤
      max (specNorm X) (specNorm Y) * ‖WithLp.toLp 2 ((1 - P) *ᵥ x)‖ :=
    hy.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hx2 := pow_le_pow_left₀ (norm_nonneg _) hx' 2
  have hy2 := pow_le_pow_left₀ (norm_nonneg _) hy' 2
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc0 (norm_nonneg _))).mp ?_
  rw [mul_pow] at hx2 hy2 ⊢
  rw [hsplit, mul_add, sq, hsum]
  linarith

/-- **The gap between two orthogonal projectors**: $\|\mathbf{P} - \mathbf{Q}\|_2$ is the larger
of the two directed gaps, $\max(\|(\mathbf{I} - \mathbf{Q})\mathbf{P}\|_2, \|(\mathbf{I} -
\mathbf{P})\mathbf{Q}\|_2)$. [GolubVanLoan2013, §2.5.3]; [Kato1995, §I.6.8].
Result: projector-gap -/
theorem _root_.IsStarProjection.specNorm_sub_eq_max {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    specNorm (P - Q) = max (specNorm ((1 - Q) * P)) (specNorm ((1 - P) * Q)) := by
  have hflip : specNorm (Q * (1 - P)) = specNorm ((1 - P) * Q) := by
    rw [← specNorm_conjTranspose, Matrix.conjTranspose_mul, hQ.conjTranspose_eq,
      hP.one_sub.conjTranspose_eq]
  refine le_antisymm ?_ (max_le ?_ ?_)
  · have h := hP.specNorm_add_le_max (X := (1 - Q) * P) (Y := -(Q * (1 - P)))
      (by rw [Matrix.mul_assoc, hP.mul_self])
      (by rw [Matrix.neg_mul, Matrix.mul_assoc, hP.one_sub.mul_self])
      (by rw [Matrix.conjTranspose_mul, hQ.one_sub.conjTranspose_eq, Matrix.mul_neg,
        Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Q), hQ.one_sub_mul_self, Matrix.zero_mul,
        Matrix.mul_zero, neg_zero])
    rwa [← sub_eq_add_neg, ← sub_eq_one_sub_mul_sub_mul_one_sub, specNorm_neg, hflip] at h
  · have heq : (1 - Q) * P = (1 - Q) * (P - Q) := by
      rw [Matrix.mul_sub, hQ.one_sub_mul_self, sub_zero]
    rw [heq]
    exact hQ.one_sub.specNorm_mul_le _
  · have heq : (1 - P) * Q = (1 - P) * (Q - P) := by
      rw [Matrix.mul_sub, hP.one_sub_mul_self, sub_zero]
    rw [heq, specNorm_sub_comm P Q]
    exact hP.one_sub.specNorm_mul_le _

omit [DecidableEq n] in
/-- $\|\mathbf{P} - \mathbf{Q}\|_2 \le 1$ for orthogonal projectors. -/
theorem _root_.IsStarProjection.specNorm_sub_le_one {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) : specNorm (P - Q) ≤ 1 := by
  classical
  rw [hP.specNorm_sub_eq_max hQ]
  exact max_le (hP.specNorm_one_sub_mul_le_one hQ) (hQ.specNorm_one_sub_mul_le_one hP)

omit [DecidableEq n] in
/-- **Projectors at distance less than one have the same rank**: for orthogonal projectors with
$\|\mathbf{P} - \mathbf{Q}\|_2 < 1$, $\operatorname{rank} \mathbf{P} = \operatorname{rank}
\mathbf{Q}$.
[Kato1995, §I.6.8]. -/
theorem _root_.IsStarProjection.rank_eq_of_specNorm_sub_lt_one {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : specNorm (P - Q) < 1) :
    P.rank = Q.rank := by
  classical
  rw [hP.specNorm_sub_eq_max hQ, max_lt_iff] at h
  have h1 := (hP.specNorm_one_sub_mul_lt_one_iff hQ).mp h.1
  have h2 := (hQ.specNorm_one_sub_mul_lt_one_iff hP).mp h.2
  exact le_antisymm (h1 ▸ Matrix.rank_mul_le_left Q P) (h2 ▸ Matrix.rank_mul_le_left P Q)

/-- **The gap between orthogonal projectors of equal rank.** For orthogonal projectors of equal
rank, $\|\mathbf{P} - \mathbf{Q}\|_2 = \|(\mathbf{I} - \mathbf{Q})\mathbf{P}\|_2$.
Result: projector-gap -/
theorem _root_.IsStarProjection.specNorm_sub_eq_of_rank_eq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P.rank = Q.rank) :
    specNorm (P - Q) = specNorm ((1 - Q) * P) := by
  rw [hP.specNorm_sub_eq_max hQ, hP.specNorm_one_sub_mul_eq_of_rank_eq hQ h, max_self]

/-- For orthogonal projectors,
$\|\mathbf{P} - \mathbf{Q}\|_{\mathsf{F}}^2 = \|(\mathbf{I} - \mathbf{Q})\mathbf{P}\|_{\mathsf{F}}^2
+ \|(\mathbf{I} - \mathbf{P})\mathbf{Q}\|_{\mathsf{F}}^2$. -/
theorem _root_.IsStarProjection.frobNorm_sub_sq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    frobNorm (P - Q) ^ 2 = frobNorm ((1 - Q) * P) ^ 2 + frobNorm ((1 - P) * Q) ^ 2 := by
  have hflip : frobNorm (Q * (1 - P)) = frobNorm ((1 - P) * Q) := by
    rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, hQ.conjTranspose_eq,
      hP.one_sub.conjTranspose_eq]
  have h0 : frobInner ((1 - Q) * P) (Q * (1 - P)) = 0 := by
    rw [frobInner_comm]
    exact hQ.frobInner_mul_one_sub_mul _ _
  rw [sub_eq_one_sub_mul_sub_mul_one_sub, frobNorm_sub_sq_of_frobInner_eq_zero h0, hflip]

/-- For orthogonal projectors of equal rank,
$\|\mathbf{P} - \mathbf{Q}\|_{\mathsf{F}}^2 = 2\|(\mathbf{I} -
\mathbf{Q})\mathbf{P}\|_{\mathsf{F}}^2$. -/
theorem _root_.IsStarProjection.frobNorm_sub_sq_of_rank_eq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P.rank = Q.rank) :
    frobNorm (P - Q) ^ 2 = 2 * frobNorm ((1 - Q) * P) ^ 2 := by
  rw [hP.frobNorm_sub_sq hQ, hP.frobNorm_one_sub_mul_eq_of_rank_eq hQ h, two_mul]

/-! ### Frames -/

/-- The squared distance from a frame $\mathbf{Q}$ to the range of a frame $\mathbf{U}$ is the
number of columns of $\mathbf{Q}$ less the squared overlap:
$\|(\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf{H}})\mathbf{Q}\|_{\mathsf{F}}^2
= \lvert q \rvert - \|\mathbf{Q}^{\mathsf{H}}\mathbf{U}\|_{\mathsf{F}}^2$. -/
theorem HasOrthonormalCols.frobNorm_one_sub_mul_sq [DecidableEq p] [DecidableEq q]
    {U : Matrix n p 𝕜} {Q : Matrix n q 𝕜} (hU : HasOrthonormalCols U)
    (hQ : HasOrthonormalCols Q) :
    frobNorm ((1 - U * Uᴴ) * Q) ^ 2 = Fintype.card q - frobNorm (Qᴴ * U) ^ 2 := by
  have h := hU.isStarProjection_mul_conjTranspose.frobNorm_sq_eq_add Q
  rw [hQ.frobNorm_sq, Matrix.mul_assoc, hU.frobNorm_mul_left, ← frobNorm_conjTranspose (Uᴴ * Q),
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h
  linarith

/-- The projectors of two frames with the same number of columns are at Frobenius distance
$\sqrt{2} \, \|(\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf{H}})\mathbf{Q}\|_{\mathsf{F}}$:
$\|\mathbf{Q}\mathbf{Q}^{\mathsf{H}} - \mathbf{U}\mathbf{U}^{\mathsf{H}}\|_{\mathsf{F}}
= \sqrt{2} \, \|(\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf{H}})\mathbf{Q}\|_{\mathsf{F}}$. -/
theorem HasOrthonormalCols.frobNorm_mul_conjTranspose_sub_mul_conjTranspose [DecidableEq p]
    {U Q : Matrix n p 𝕜} (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q) :
    frobNorm (Q * Qᴴ - U * Uᴴ) = √2 * frobNorm ((1 - U * Uᴴ) * Q) := by
  have e : frobInner (Q * Qᴴ) (U * Uᴴ) = frobNorm (Qᴴ * U) ^ 2 := by
    rw [NLAlib.frobInner_mul_left, frobInner_comm, ← Matrix.mul_assoc,
      NLAlib.frobInner_mul_right, Matrix.conjTranspose_conjTranspose, frobInner_self]
  have h : frobNorm (Q * Qᴴ - U * Uᴴ) ^ 2 = 2 * frobNorm ((1 - U * Uᴴ) * Q) ^ 2 := by
    rw [frobNorm_sub_sq, e, hQ.frobNorm_mul_left, hU.frobNorm_mul_left, frobNorm_conjTranspose,
      frobNorm_conjTranspose, hQ.frobNorm_sq, hU.frobNorm_sq, hU.frobNorm_one_sub_mul_sq hQ]
    ring
  rw [← Real.sqrt_sq (frobNorm_nonneg (Q * Qᴴ - U * Uᴴ)), h, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (frobNorm_nonneg _)]

end NLAlib
