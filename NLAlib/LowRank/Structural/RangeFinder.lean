/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.NystromGram
public import NLAlib.Matrix.Factorizations.SketchedLowRank
public import NLAlib.Matrix.Norms.Projector
public import NLAlib.Matrix.Pseudoinverse.NormBounds
public import NLAlib.Matrix.Spectral.ProjectedLowRank
public import NLAlib.Sketching.Properties.LeastSquares

/-!
# The structural bound of the range finder

Fix $\mathbf{A} \in \Bbbk^{m \times n}$, a test matrix $\mathbf{\Omega} \in \Bbbk^{n \times l}$ and
any $\mathbf{Z} \in \Bbbk^{n \times r}$ with orthonormal columns for which
$\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ has full row rank, written `(Ωᴴ * Z).rank = Z.rank`
(the sketch $\mathbf{\Omega}^{\mathsf{H}}$ keeps the rank of $\mathbf{Z}$). With
$$\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}},\qquad
\mathbf{M} = \mathbf{E}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+},$$
spelled inline as `A - A * Z * Zᴴ` and `(A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)`, the error
$\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}$ of the randomized SVD,
`A - rsvd A Ω`, is bounded by $\mathbf{E}$ and $\mathbf{M}$ in every unitarily invariant norm: in
Gram form for the quadratic norms and in triangle form for all of them. The proof compares the
error with the competitor
$$\mathbf{C} = \mathbf{A}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}
\mathbf{Z}^{\mathsf{H}},$$
whose columns lie in $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$ and for which
$\mathbf{A} - \mathbf{C} = \mathbf{E} - \mathbf{M}\mathbf{Z}^{\mathsf{H}}$ exactly.

For a frame with $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket \mathbf{A} \rrbracket_k$
(`NLAlib.exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD`), rewriting with that
equation gives $\mathbf{E} = \mathbf{A} - \llbracket \mathbf{A} \rrbracket_k$ and the statements of
[HalkoMartinssonTropp2011, Theorem 9.1]; at rank at most $k$ they say `A - rsvd A Ω = 0`.

Degenerate cases: for empty `r` every bound is the contraction
$\|(\mathbf{I} - \mathbf{P})\mathbf{A}\| \le \|\mathbf{A}\|$. Without the rank hypothesis the
bounds fail ($\mathbf{A} = \mathbf{Z} = [1]$, $\mathbf{\Omega} = [0]$). Design:
`docs/design/LowRank-S1.md`.

## Main results

* `NLAlib.HasOrthonormalCols.sub_mul_mul_pinv_mul_conjTranspose_eq`,
  `NLAlib.HasOrthonormalCols.sub_mul_mul_pinv_mul_conjTranspose_mul_conjTranspose_eq`,
  `NLAlib.HasOrthonormalCols.frobNorm_sub_mul_mul_pinv_mul_conjTranspose_sq`,
  `NLAlib.rank_mul_mul_pinv_mul_conjTranspose_le`, `NLAlib.range_mul_mul_pinv_mul_conjTranspose_le`:
  the competitor.
* `NLAlib.SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_le`: the Gram form, every
  quadratic unitarily invariant norm.
* `NLAlib.SymmetricGauge.matrixNorm_sub_rsvd_le`: the triangle form, every unitarily invariant norm.
* `NLAlib.HasOrthonormalCols.specNorm_sub_rsvd_sq_le`,
  `NLAlib.HasOrthonormalCols.specNorm_sub_rsvd_le`,
  `NLAlib.HasOrthonormalCols.frobNorm_sub_rsvd_sq_le`: spectral and Frobenius forms.
* `NLAlib.HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_sq_le`: truncation for free.
* `NLAlib.IsSubspaceInjection.frobNorm_sub_rsvd_sq_le`: under a subspace injection.
* `NLAlib.HasOrthonormalCols.sub_mul_mul_pinv_eq`,
  `NLAlib.IsSubspaceInjection.matrixNorm_sub_mul_mul_pinv_le`: $\mathbf{M}$ through an
  approximate-multiplication error.
* `NLAlib.SymmetricGauge.matrixNorm_sub_nystrom_le_of_hasOrthonormalCols`: the structural bound of
  Nyström approximation.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n l r q : Type*} [Fintype m] [Fintype n] [Fintype l]
  [Fintype r] [Fintype q] {Ω : Matrix n l 𝕜} {Z : Matrix n r 𝕜}

/-! ### The competitor -/

omit [Fintype m] in
/-- The competitor has rank at most the number of columns of the frame:
$$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}
\mathbf{Z}^{\mathsf{H}}) \le \lvert r \rvert\,.$$ -/
theorem rank_mul_mul_pinv_mul_conjTranspose_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (Z : Matrix n r 𝕜) : (A * Ω * pinv (Zᴴ * Ω) * Zᴴ).rank ≤ Fintype.card r :=
  (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_card_height _)

omit [Fintype m] in
/-- The competitor lies in the range of the sketch:
$$\operatorname{range}(\mathbf{A}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}
\mathbf{Z}^{\mathsf{H}}) \subseteq \operatorname{range}(\mathbf{A}\mathbf{\Omega})\,.$$ -/
theorem range_mul_mul_pinv_mul_conjTranspose_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (Z : Matrix n r 𝕜) :
    LinearMap.range (A * Ω * pinv (Zᴴ * Ω) * Zᴴ).mulVecLin ≤ LinearMap.range (A * Ω).mulVecLin :=
  range_mulVecLin_le_iff_exists_mul.mpr ⟨pinv (Zᴴ * Ω) * Zᴴ, by simp only [Matrix.mul_assoc]⟩

variable [DecidableEq r]

/-- Under the rank hypothesis, $\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ has a right inverse, its
pseudoinverse. -/
private theorem mul_pinv_self_of_rank_eq (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) : Zᴴ * Ω * pinv (Zᴴ * Ω) = 1 := by
  refine mul_pinv_self_of_injective_conjTranspose ?_
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mulVec_injective_iff_rank_eq,
    hΩ, hZ.rank_eq]

omit [Fintype m] in
/-- The frame annihilates the error of its projection: $\mathbf{E}\mathbf{Z} = \mathbf{0}$. -/
private theorem sub_mul_mul_conjTranspose_mul_self (hZ : HasOrthonormalCols Z)
    (A : Matrix m n 𝕜) : (A - A * Z * Zᴴ) * Z = 0 := by
  rw [Matrix.sub_mul, hZ.mul_conjTranspose_mul_cancel_right, sub_self]

omit [Fintype m] in
/-- **The range-finder competitor.** For $\mathbf{Z}$ with orthonormal columns and
$\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ of full row rank, the matrix
$$\mathbf{C} = \mathbf{A}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}
\mathbf{Z}^{\mathsf{H}},$$
whose columns lie in $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$
(`NLAlib.range_mul_mul_pinv_mul_conjTranspose_le`) and whose rank is at most $\lvert r \rvert$
(`NLAlib.rank_mul_mul_pinv_mul_conjTranspose_le`), satisfies
$$\mathbf{A} - \mathbf{C} = \mathbf{E} - \mathbf{M}\mathbf{Z}^{\mathsf{H}}$$
with $\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ and
$\mathbf{M} = \mathbf{E}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}$.
[HalkoMartinssonTropp2011, Theorem 9.1 (proof)]; [Woodruff2014, Lemma 48 (proof)];
[TroppWebber2023, Proposition 8.5 (proof)]; there with a partitioned SVD and
$\mathbf{Z} = \mathbf{V}_1$, here any frame over any `RCLike` field.
Port of `NLAlib.sub_mul_pinvR_mul_transpose_eq`, there over $\mathbb{R}$ with SVD blocks. -/
theorem HasOrthonormalCols.sub_mul_mul_pinv_mul_conjTranspose_eq (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    A - A * Ω * pinv (Zᴴ * Ω) * Zᴴ =
      (A - A * Z * Zᴴ) - (A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω) * Zᴴ := by
  have hC : A * Z * Zᴴ * Ω * pinv (Zᴴ * Ω) * Zᴴ = A * Z * Zᴴ := by
    rw [Matrix.mul_assoc (A * Z) Zᴴ Ω, Matrix.mul_assoc (A * Z) (Zᴴ * Ω),
      mul_pinv_self_of_rank_eq hZ hΩ, Matrix.mul_one]
  rw [Matrix.sub_mul A (A * Z * Zᴴ) Ω, Matrix.sub_mul, Matrix.sub_mul, hC]
  abel

omit [Fintype m] in
/-- **Gram identity of the competitor**:
$$(\mathbf{A} - \mathbf{C})(\mathbf{A} - \mathbf{C})^{\mathsf{H}} =
\mathbf{E}\mathbf{E}^{\mathsf{H}} + \mathbf{M}\mathbf{M}^{\mathsf{H}}\,,$$
because $\mathbf{E}\mathbf{Z} = \mathbf{0}$ and $\mathbf{Z}^{\mathsf{H}}\mathbf{Z} = \mathbf{I}$.
[TroppWebber2023, Proposition 8.5 (proof)], there for a diagonal positive semidefinite matrix;
here any matrix and any frame. -/
theorem HasOrthonormalCols.sub_mul_mul_pinv_mul_conjTranspose_mul_conjTranspose_eq
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    (A - A * Ω * pinv (Zᴴ * Ω) * Zᴴ) * (A - A * Ω * pinv (Zᴴ * Ω) * Zᴴ)ᴴ =
      (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ +
        (A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω) * ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))ᴴ := by
  have hEZ := sub_mul_mul_conjTranspose_mul_self hZ A
  rw [hZ.sub_mul_mul_pinv_mul_conjTranspose_eq hΩ A]
  set E := A - A * Z * Zᴴ
  set M := E * Ω * pinv (Zᴴ * Ω)
  have h1 : E * (M * Zᴴ)ᴴ = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, hEZ,
      Matrix.zero_mul]
  have h2 : M * Zᴴ * Eᴴ = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hEZ, Matrix.conjTranspose_zero,
      Matrix.mul_zero]
  have h3 : M * Zᴴ * (M * Zᴴ)ᴴ = M * Mᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Zᴴ, hZ.conjTranspose_mul_self, Matrix.one_mul]
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h1, h2, h3]
  abel

/-- The squared Frobenius error of the competitor splits exactly:
$$\|\mathbf{A} - \mathbf{C}\|_{\mathsf{F}}^2 = \|\mathbf{E}\|_{\mathsf{F}}^2 +
\|\mathbf{M}\|_{\mathsf{F}}^2\,.$$
[Woodruff2014, Lemma 48 (proof)], there over $\mathbb{R}$.
Port of `NLAlib.frobSq_sub_mul_pinvR_mul_transpose_eq`. -/
theorem HasOrthonormalCols.frobNorm_sub_mul_mul_pinv_mul_conjTranspose_sq
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    frobNorm (A - A * Ω * pinv (Zᴴ * Ω) * Zᴴ) ^ 2 =
      frobNorm (A - A * Z * Zᴴ) ^ 2 + frobNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2 := by
  have hEZ := sub_mul_mul_conjTranspose_mul_self hZ A
  rw [hZ.sub_mul_mul_pinv_mul_conjTranspose_eq hΩ A, frobNorm_sub_sq_of_frobInner_eq_zero,
    frobNorm_mul_conjTranspose_right hZ]
  rw [frobInner_eq_re_trace_mul_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, hEZ, Matrix.zero_mul,
    Matrix.trace_zero, map_zero]

/-! ### The structural bound for any frame -/

/-- The error of the range finder is the projection residual of the error of any matrix
$\mathbf{A}\mathbf{\Omega}\mathbf{X}$ built from the sketch. -/
private theorem sub_rsvd_eq_one_sub_rangeProjector_mul_sub_mul [DecidableEq m]
    (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (X : Matrix l n 𝕜) :
    A - rsvd A Ω = (1 - rangeProjector (A * Ω)) * (A - A * Ω * X) := by
  rw [sub_rsvd, Matrix.mul_sub, ← Matrix.mul_assoc _ (A * Ω) X, one_sub_rangeProjector_mul_self,
    Matrix.zero_mul, sub_zero]

/-- The range finder is at least as good as any matrix $\mathbf{A}\mathbf{\Omega}\mathbf{X}$
built from the sketch, singular value by singular value. -/
private theorem singularValues_sub_rsvd_le_sub_mul (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (X : Matrix l n 𝕜) (i : ℕ) :
    singularValues (A - rsvd A Ω) i ≤ singularValues (A - A * Ω * X) i := by
  classical
  rw [sub_rsvd_eq_one_sub_rangeProjector_mul_sub_mul A Ω X]
  exact (isStarProjection_one_sub_rangeProjector _).singularValues_mul_le _ i

/-- **The structural bound of the range finder, Gram form.** For $\mathbf{Z}$ with orthonormal
columns and $\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ of full row rank, in every unitarily invariant
norm,
$$\bigl\|(\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A})^{\mathsf{H}}
(\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A})\bigr\|_{\Phi} \le
\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} + \|\mathbf{M}^{\mathsf{H}}\mathbf{M}\|_{\Phi}$$
with $\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ and
$\mathbf{M} = \mathbf{E}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}$: a bound on
$\Phi(\sigma(\cdot)^2)$ of the error, so on every quadratic unitarily invariant norm, squared
Schatten norms $\|\cdot\|_{S_p}^2$ for $p \ge 2$ included (never $p < 2$). With
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket \mathbf{A} \rrbracket_k$ (rewrite with it)
this is HMT Theorem 9.1 in every quadratic norm.
[MartinssonTropp2020, Theorem 11.4]; [TroppWebber2023, Proposition 8.5, (8.2)];
[HalkoMartinssonTropp2011, Theorem 9.1]; there for top-$k$ frames, in the spectral norm (MT, with
the remark that a related inequality holds for quadratic norms) or Schatten $p \ge 2$ (TW); here any
frame and every gauge of the Gram matrix.
Result: range-finder-structural-bound -/
theorem SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_le (Φ : SymmetricGauge)
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    Φ.matrixNorm ((A - rsvd A Ω)ᴴ * (A - rsvd A Ω)) ≤
      Φ.matrixNorm ((A - A * Z * Zᴴ)ᴴ * (A - A * Z * Zᴴ)) +
        Φ.matrixNorm (((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))ᴴ *
          ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))) := by
  have hle : Φ.matrixNorm ((A - rsvd A Ω)ᴴ * (A - rsvd A Ω)) ≤
      Φ.matrixNorm ((A - A * Ω * pinv (Zᴴ * Ω) * Zᴴ) * (A - A * Ω * pinv (Zᴴ * Ω) * Zᴴ)ᴴ) := by
    refine Φ.matrixNorm_le_of_singularValues_le fun i => ?_
    rw [singularValues_conjTranspose_mul_self, singularValues_mul_conjTranspose_self]
    have h := singularValues_sub_rsvd_le_sub_mul A Ω (pinv (Zᴴ * Ω) * Zᴴ) i
    rw [← Matrix.mul_assoc] at h
    exact pow_le_pow_left₀ (singularValues_nonneg _ _) h 2
  refine hle.trans ?_
  rw [hZ.sub_mul_mul_pinv_mul_conjTranspose_mul_conjTranspose_eq hΩ A,
    ← Φ.matrixNorm_mul_conjTranspose_self (A - A * Z * Zᴴ),
    ← Φ.matrixNorm_mul_conjTranspose_self ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))]
  exact Φ.matrixNorm_add_le _ _

/-- **The structural bound of the range finder, unsquared triangle form**, in every unitarily
invariant norm:
$$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_{\Phi} \le
\|\mathbf{E}\|_{\Phi} + \|\mathbf{M}\|_{\Phi}\,.$$
For every quadratic norm the Gram form
(`NLAlib.SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_le`) is at least as strong
($\sqrt{a^2 + b^2} \le a + b$); this form's own content is the norms the Gram form does not reach,
such as the nuclear, Ky Fan and Schatten $p < 2$ norms.
[MartinssonTropp2020, Theorem 11.4]; [HalkoMartinssonTropp2011, proof of Theorem 10.6]; there in
the spectral norm, here every unitarily invariant norm and any frame.
Result: range-finder-structural-bound -/
theorem SymmetricGauge.matrixNorm_sub_rsvd_le (Φ : SymmetricGauge) (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    Φ.matrixNorm (A - rsvd A Ω) ≤
      Φ.matrixNorm (A - A * Z * Zᴴ) + Φ.matrixNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) := by
  have hle : Φ.matrixNorm (A - rsvd A Ω) ≤ Φ.matrixNorm (A - A * Ω * pinv (Zᴴ * Ω) * Zᴴ) := by
    refine Φ.matrixNorm_le_of_singularValues_le fun i => ?_
    have h := singularValues_sub_rsvd_le_sub_mul A Ω (pinv (Zᴴ * Ω) * Zᴴ) i
    rwa [← Matrix.mul_assoc] at h
  refine hle.trans ?_
  rw [hZ.sub_mul_mul_pinv_mul_conjTranspose_eq hΩ A, sub_eq_add_neg (A - A * Z * Zᴴ)]
  refine (Φ.matrixNorm_add_le _ _).trans_eq ?_
  rw [Φ.matrixNorm_neg, Φ.matrixNorm_mul_conjTranspose_right_of_hasOrthonormalCols hZ]

/-- Spectral form of the structural bound:
$$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_2^2 \le
\|\mathbf{E}\|_2^2 + \|\mathbf{M}\|_2^2\,.$$
[HalkoMartinssonTropp2011, Theorem 9.1], there for a top-$k$ frame; here any frame.
Port of `NLAlib.specNorm_residual_sq_le_of_range_subset`.
Result: range-finder-structural-bound -/
theorem HasOrthonormalCols.specNorm_sub_rsvd_sq_le (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    specNorm (A - rsvd A Ω) ^ 2 ≤
      specNorm (A - A * Z * Zᴴ) ^ 2 + specNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2 := by
  have h := (lpGauge ⊤ le_top).matrixNorm_conjTranspose_mul_self_sub_rsvd_le hZ hΩ A
  simpa only [lpGauge_top_matrixNorm, specNorm_conjTranspose_mul_self] using h

/-- Unsquared spectral form of the structural bound:
$$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_2 \le
\|\mathbf{E}\|_2 + \|\mathbf{M}\|_2\,.$$
Dominated by `NLAlib.HasOrthonormalCols.specNorm_sub_rsvd_sq_le`, kept because HMT 10.6 uses this
simpler form (CONTRIBUTING §5.2, numerical bounds, rule 6).
[MartinssonTropp2020, Theorem 11.4]; [HalkoMartinssonTropp2011, proof of Theorem 10.6]; there for a
top-$k$ frame.
Port of `NLAlib.specNorm_residual_le_of_range_subset`.
Result: range-finder-structural-bound -/
theorem HasOrthonormalCols.specNorm_sub_rsvd_le (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    specNorm (A - rsvd A Ω) ≤
      specNorm (A - A * Z * Zᴴ) + specNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) := by
  have h := (lpGauge ⊤ le_top).matrixNorm_sub_rsvd_le hZ hΩ A
  simpa only [lpGauge_top_matrixNorm] using h

/-- Frobenius form of the structural bound:
$$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_{\mathsf{F}}^2 \le
\|\mathbf{E}\|_{\mathsf{F}}^2 + \|\mathbf{M}\|_{\mathsf{F}}^2\,.$$
[HalkoMartinssonTropp2011, Theorem 9.1]; [Woodruff2014, Lemma 48];
[CamanoEpperlyMeyerTropp2025, Imported Theorem 2.3]; there for a top-$k$ frame (HMT, CEMT) or any
frame over $\mathbb{R}$ (Woodruff).
Port of `NLAlib.frobSq_residual_le_of_range_subset`.
Result: range-finder-structural-bound -/
theorem HasOrthonormalCols.frobNorm_sub_rsvd_sq_le (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    frobNorm (A - rsvd A Ω) ^ 2 ≤
      frobNorm (A - A * Z * Zᴴ) ^ 2 + frobNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2 := by
  classical
  rw [← hZ.frobNorm_sub_mul_mul_pinv_mul_conjTranspose_sq hΩ A, sub_rsvd]
  have h := frobNorm_one_sub_rangeProjector_mul_le_frobNorm_sub_mul (A * Ω) A (pinv (Zᴴ * Ω) * Zᴴ)
  rw [← Matrix.mul_assoc] at h
  exact pow_le_pow_left₀ (frobNorm_nonneg _) h 2

/-- **Truncation for free.** For any $\mathbf{Q}$ with orthonormal columns whose range contains
$\operatorname{range}(\mathbf{A}\mathbf{\Omega})$ and any $k \ge \lvert r \rvert$,
$$\|\mathbf{A} -
\mathbf{Q}\llbracket \mathbf{Q}^{\mathsf{H}}\mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2
\le \|\mathbf{E}\|_{\mathsf{F}}^2 + \|\mathbf{M}\|_{\mathsf{F}}^2\,:$$
the rank-$k$ restricted projection keeps the bound of the untruncated range finder, since the
competitor has rank at most $\lvert r \rvert$ and lies in $\operatorname{range}\mathbf{Q}$. The
hypothesis $k \ge \lvert r \rvert$ is needed: take
$\mathbf{A} = \mathbf{\Omega} = \mathbf{Z} = \mathbf{I}_2$ and $k = 0$.
[Woodruff2014, Lemma 48], its middle inequality, there over $\mathbb{R}$ with the best rank-$k$
approximation in the column space of the sketch; here for any $\mathbf{Q}$ containing that column
space.
Port of `NLAlib.frobSq_sub_mul_le_of_isBestFrobRankApprox_of_range_subset`, there through an
optimality predicate.
Result: truncated-range-finder-structural-bound -/
theorem HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_sq_le [DecidableEq q] {A : Matrix m n 𝕜}
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (hQY : LinearMap.range (A * Ω).mulVecLin ≤ LinearMap.range Q.mulVecLin)
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) {k : ℕ}
    (hk : Fintype.card r ≤ k) :
    frobNorm (A - Q * truncatedSVD (Qᴴ * A) k) ^ 2 ≤
      frobNorm (A - A * Z * Zᴴ) ^ 2 + frobNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2 := by
  rw [← hZ.frobNorm_sub_mul_mul_pinv_mul_conjTranspose_sq hΩ A]
  have hQC : Q * (Qᴴ * (A * Ω * pinv (Zᴴ * Ω) * Zᴴ)) = A * Ω * pinv (Zᴴ * Ω) * Zᴴ := by
    rw [← Matrix.mul_assoc, ← hQ.rangeProjector_eq, rangeProjector_mul_eq_self_iff]
    exact (range_mul_mul_pinv_mul_conjTranspose_le A Ω Z).trans hQY
  have h := hQ.frobNorm_sub_mul_truncatedSVD_le_of_rank_le A
    (((Matrix.rank_mul_le_right _ _).trans (rank_mul_mul_pinv_mul_conjTranspose_le A Ω Z)).trans
      hk : (Qᴴ * (A * Ω * pinv (Zᴴ * Ω) * Zᴴ)).rank ≤ k)
  rw [hQC] at h
  exact pow_le_pow_left₀ (frobNorm_nonneg _) h 2

/-! ### Subspace injections, approximate multiplication, Nyström -/

/-- **The structural bound of the range finder, under a subspace injection** (the deterministic
core of CEMT Theorem 2.2): if $\mathbf{\Omega}^{\mathsf{H}}$ is a subspace injection for
$\operatorname{range}\mathbf{Z}$ with constant $a > 0$, then
$$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_{\mathsf{F}}^2 \le
\|\mathbf{E}\|_{\mathsf{F}}^2 + \frac{\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2}{a}\,.$$
The rank hypothesis follows from the injection (`NLAlib.IsSubspaceInjection.rank_mul_eq`).
[CamanoEpperlyMeyerTropp2025, Theorem 2.2 (proof), Lemma 2.1]; there with probability $9/10$ and an
unspecified constant, here the injection as a hypothesis and the constant $1/a$ explicit.
Result: range-finder-structural-bound -/
theorem IsSubspaceInjection.frobNorm_sub_rsvd_sq_le {a : ℝ} (h : IsSubspaceInjection Ωᴴ Z a)
    (hZ : HasOrthonormalCols Z) (ha : 0 < a) (A : Matrix m n 𝕜) :
    frobNorm (A - rsvd A Ω) ^ 2 ≤
      frobNorm (A - A * Z * Zᴴ) ^ 2 + frobNorm ((A - A * Z * Zᴴ) * Ω) ^ 2 / a := by
  refine (hZ.frobNorm_sub_rsvd_sq_le (h.rank_mul_eq ha) A).trans (add_le_add le_rfl ?_)
  have hM := h.frobNorm_mul_pinv_sq_le hZ ha ((A - A * Z * Zᴴ) * Ω)
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at hM

omit [Fintype m] in
/-- **The noise term as an approximate-multiplication error.** For any test matrix,
$$\mathbf{M} = \bigl(\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z} -
\mathbf{E}\mathbf{Z}\bigr)\bigl((\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z})^{\mathsf{H}}
\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}\bigr)^{+}\,.$$
The first factor is the error of the product of $\mathbf{E}$ and $\mathbf{Z}$ sketched by
$\mathbf{\Omega}^{\mathsf{H}}$, as an approximation of $\mathbf{E}\mathbf{Z}$: the left side of
`NLAlib.HasJLMoment.integral_frobNorm_conjTranspose_mul_sub_rpow_le` at
$\mathbf{E}^{\mathsf{H}}$, sketch $\mathbf{\Omega}^{\mathsf{H}}$ and $\mathbf{Z}$, after two
`Matrix.conjTranspose_conjTranspose` (that moment is over $\mathbb{R}$, this identity over any
`RCLike` field). The term $\mathbf{E}\mathbf{Z}$ is $\mathbf{0}$ for a frame and is kept only to
match that shape. No rank hypothesis.
[Woodruff2014, Lemma 45 (proof)], there as a change of basis with the sketch on the left. -/
theorem HasOrthonormalCols.sub_mul_mul_pinv_eq (hZ : HasOrthonormalCols Z) (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) :
    (A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω) =
      ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z) * pinv ((Ωᴴ * Z)ᴴ * (Ωᴴ * Z)) := by
  rw [sub_mul_mul_conjTranspose_mul_self hZ A, sub_zero,
    pinv_eq_conjTranspose_mul_pinv_mul_conjTranspose_self (Zᴴ * Ω), Matrix.conjTranspose_mul Zᴴ Ω,
    Matrix.conjTranspose_mul Ωᴴ Z, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- Under a subspace injection with constant $a > 0$, in every unitarily invariant norm,
$$\|\mathbf{M}\|_{\Phi} \le
\frac{\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z} -
\mathbf{E}\mathbf{Z}\|_{\Phi}}{a}\,:$$
the noise term is at most the approximate-multiplication error over $a$.
[Woodruff2014, Lemma 45 (proof)], there in the Frobenius norm with $a = 1 - \varepsilon$ for a
subspace embedding. -/
theorem IsSubspaceInjection.matrixNorm_sub_mul_mul_pinv_le {a : ℝ}
    (h : IsSubspaceInjection Ωᴴ Z a) (hZ : HasOrthonormalCols Z) (ha : 0 < a)
    (Φ : SymmetricGauge) (A : Matrix m n 𝕜) :
    Φ.matrixNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ≤
      Φ.matrixNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z) / a := by
  rw [hZ.sub_mul_mul_pinv_eq A Ω, div_eq_mul_inv]
  refine (Φ.matrixNorm_mul_le_mul_specNorm _ _).trans
    (mul_le_mul_of_nonneg_left ?_ (Φ.matrixNorm_nonneg _))
  rw [← specNorm_pinv_sq]
  exact specNorm_pinv_sq_le_inv_of_smul_one_le ha (hZ.isSubspaceInjection_iff.mp h)

open scoped MatrixOrder in
/-- **The structural bound of Nyström approximation**, in every unitarily invariant norm: for
positive semidefinite $\mathbf{H}$, $\mathbf{Z}$ with orthonormal columns and
$\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ of full row rank, with
$$\mathbf{H}_\perp = (\mathbf{I} - \mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{H}
(\mathbf{I} - \mathbf{Z}\mathbf{Z}^{\mathsf{H}}),$$
$$\|\mathbf{H} - \mathbf{H}\langle\mathbf{\Omega}\rangle\|_{\Phi} \le \|\mathbf{H}_\perp\|_{\Phi} +
\bigl\|((\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+})^{\mathsf{H}}\,\mathbf{\Omega}^{\mathsf{H}}
\mathbf{H}_\perp\mathbf{\Omega}\,(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\bigr\|_{\Phi}\,.$$
No square root appears: kernel and Gram matrices apply it directly. With
$\mathbf{H}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket \mathbf{H} \rrbracket_k$ (as
`NLAlib.exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD` provides),
$\mathbf{H}_\perp = \mathbf{H} - \llbracket \mathbf{H} \rrbracket_k$
(`Matrix.PosSemidef.one_sub_mul_mul_one_sub_eq_sub_truncatedSVD`). Positive semidefiniteness is
needed: for $\mathbf{H} = \begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix}$ and
$\mathbf{\Omega} = \mathbf{Z} = \mathbf{e}_1$ the right side vanishes.
[MartinssonTropp2020, Proposition 11.1, Theorem 11.4]; [TroppWebber2023, proof of Theorem 8.1 and
Corollary 8.2]; [CamanoEpperlyMeyerTropp2025, proof of Corollary 2.5]; there by the same composition
for the square root of $\mathbf{H}$ in trace or Schatten norms, here every unitarily invariant norm,
stated in $\mathbf{H}$ alone.
Result: nystrom-structural-bound -/
theorem SymmetricGauge.matrixNorm_sub_nystrom_le_of_hasOrthonormalCols [DecidableEq n]
    (Φ : SymmetricGauge) {H : Matrix n n 𝕜} (hH : H.PosSemidef) (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) :
    Φ.matrixNorm (H - nystrom H Ω) ≤
      Φ.matrixNorm ((1 - Z * Zᴴ) * H * (1 - Z * Zᴴ)) +
        Φ.matrixNorm ((pinv (Zᴴ * Ω))ᴴ * (Ωᴴ * ((1 - Z * Zᴴ) * H * (1 - Z * Zᴴ)) * Ω) *
          pinv (Zᴴ * Ω)) := by
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  rw [Matrix.star_eq_conjTranspose, conjTranspose_mul_self_sub_nystrom]
  have hP : (1 - Z * Zᴴ)ᴴ = 1 - Z * Zᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hE : (F - F * Z * Zᴴ)ᴴ * (F - F * Z * Zᴴ) = (1 - Z * Zᴴ) * (Fᴴ * F) * (1 - Z * Zᴴ) := by
    have hF : F - F * Z * Zᴴ = F * (1 - Z * Zᴴ) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    rw [hF, Matrix.conjTranspose_mul, hP]
    simp only [Matrix.mul_assoc]
  have hM : ((F - F * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))ᴴ * ((F - F * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) =
      (pinv (Zᴴ * Ω))ᴴ * (Ωᴴ * ((1 - Z * Zᴴ) * (Fᴴ * F) * (1 - Z * Zᴴ)) * Ω) *
        pinv (Zᴴ * Ω) := by
    rw [← hE]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h := Φ.matrixNorm_conjTranspose_mul_self_sub_rsvd_le hZ hΩ F
  rwa [hE, hM] at h

end NLAlib
