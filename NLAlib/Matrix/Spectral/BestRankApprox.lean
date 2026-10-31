/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Matrix.Rank
public import NLAlib.Matrix.Norms.Nuclear
public import NLAlib.Matrix.Norms.Projector
public import NLAlib.Matrix.Norms.UnitarilyInvariant
public import NLAlib.Matrix.Spectral.ProjectedLowRank

/-!
# Best approximations of rank at most $k$

`NLAlib.IsBestRankApprox C k Y` says that $\mathbf{Y}$ has rank at most $k$ and that no matrix of
rank at most $k$ is closer to $\mathbf{C}$ in the Frobenius norm. The truncated SVD
$\llbracket \mathbf{C} \rrbracket_k$ (`NLAlib.truncatedSVD`) is one; under a tie
$\sigma_{k-1}(\mathbf{C}) = \sigma_k(\mathbf{C})$ there are others, and an algorithm's output
$\mathbf{Q}\llbracket\mathbf{X}\rrbracket_k$ need not be `truncatedSVD (Q * X) k`. The predicate is
how such outputs enter a theorem. A best approximation has the error singular values
$\sigma_{k+i}(\mathbf{C})$, so it is best in every unitarily invariant norm.

The second half bounds the error of truncating an approximation $\hat{\mathbf{A}}$ of
$\mathbf{A}$: with constant one when the singular values of $\hat{\mathbf{A}}$ are dominated by
those of $\mathbf{A}$, with constant two in general, and through the $2k$ leading singular values of
the perturbation in the Frobenius norm (perturbed truncation). Reverse Eckart–Young bounds the
spectral error of any rank-$k$ matrix by its Frobenius or nuclear excess. The last results relate
the truncation of $\mathbf{G}^{\mathsf{H}}\mathbf{G}$ to that of $\mathbf{G}$.

Every statement holds for every choice of the truncations involved. Design:
`docs/design/LowRank-S2a.md`.

## Main definitions

* `NLAlib.IsBestRankApprox`: a best approximation of rank at most $k$.

## Main results

* `NLAlib.isBestRankApprox_truncatedSVD`, `NLAlib.isBestRankApprox_iff`,
  `NLAlib.isBestRankApprox_iff_isMinOn`, `NLAlib.isBestRankApprox_iff_singularValues_sub`:
  constructors and characterizations.
* `NLAlib.isBestRankApprox_zero_iff`, `NLAlib.isBestRankApprox_iff_eq_of_rank_le`: the degenerate
  cases $k = 0$ and $\operatorname{rank}\mathbf{C} \le k$, where the best approximation is
  unique.
* `NLAlib.isBestRankApprox_iff_exists_isSVD`: the best approximations are exactly the truncations
  of the thin SVDs of $\mathbf{C}$, ties and $k \ge \operatorname{rank}\mathbf{C}$ included.
* `NLAlib.IsBestRankApprox.singularValues_sub`, `NLAlib.IsBestRankApprox.matrixNorm_sub`,
  `NLAlib.IsBestRankApprox.frobNorm_sub`, `NLAlib.IsBestRankApprox.rangeProjector_mul`: API.
* `NLAlib.HasOrthonormalCols.isBestRankApprox_mul_iff`,
  `NLAlib.HasOrthonormalCols.isBestRankApprox_conjTranspose_mul_truncatedSVD`: the factored form,
  with `NLAlib.HasOrthonormalCols.mul_conjTranspose_mul_truncatedSVD`
  (`NLAlib.Matrix.Spectral.LowRank`).
* `NLAlib.IsBestRankApprox.matrixNorm_sub_le_add_of_singularValues_le`,
  `NLAlib.IsBestRankApprox.matrixNorm_sub_le_add_two_mul`: the truncation lemma.
* `NLAlib.specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_rank_le`,
  `NLAlib.specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_rank_le`: reverse Eckart–Young.
* `NLAlib.frobNorm_sub_truncatedSVD_le_nuclearNorm_div`,
  `Matrix.PosSemidef.frobNorm_sub_truncatedSVD_le_re_trace_div`: the Frobenius tail is at most
  $\|\mathbf{A}\|_*/(2\sqrt{r})$.
* `NLAlib.IsBestRankApprox.frobNorm_sub_le_add_frobNorm_truncatedSVD`,
  `NLAlib.IsBestRankApprox.frobNorm_sub_le_add_specNorm`: perturbed truncation.
* `NLAlib.nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD`,
  `NLAlib.SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_truncatedSVD`: Gram matrices, in
  trace and in every unitarily invariant norm. The Loewner order
  $\llbracket\mathbf{A}\rrbracket_k \preceq \mathbf{A}$ for positive semidefinite $\mathbf{A}$ is
  `Matrix.PosSemidef.truncatedSVD_le` (`NLAlib.Matrix.Spectral.LowRank`).
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]

/-! ### The predicate -/

/-- $\mathbf{Y}$ is a **best approximation of $\mathbf{C}$ of rank at most $k$**: it has rank at
most $k$ and no matrix of rank at most $k$ is closer to $\mathbf{C}$ in the Frobenius norm. Then
the error has the singular values $\sigma_{k+i}(\mathbf{C})$
(`NLAlib.IsBestRankApprox.singularValues_sub`), so $\mathbf{Y}$ is a best approximation in every
unitarily invariant norm (`NLAlib.IsBestRankApprox.matrixNorm_sub`). The truncated SVD is one
(`NLAlib.isBestRankApprox_truncatedSVD`); under ties $\sigma_{k-1} = \sigma_k$ there are others,
and an algorithm's $\mathbf{Q}\llbracket\mathbf{X}\rrbracket_k$ need not be
`truncatedSVD (Q * X) k`.
[GolubVanLoan2013, Theorem 2.4.8]; [HornJohnson2013, §7.4.9]; [HalkoMartinssonTropp2011, §2.1]. -/
structure IsBestRankApprox (C : Matrix m n 𝕜) (k : ℕ) (Y : Matrix m n 𝕜) : Prop where
  /-- A best approximation has rank at most $k$. -/
  rank_le : Y.rank ≤ k
  /-- No matrix of rank at most $k$ is closer in the Frobenius norm. -/
  frobNorm_sub_le : ∀ B : Matrix m n 𝕜, B.rank ≤ k → frobNorm (C - Y) ≤ frobNorm (C - B)

/-- **Eckart–Young**: the truncated SVD $\llbracket \mathbf{C} \rrbracket_k$ is a best
approximation of $\mathbf{C}$ of rank at most $k$.
[GolubVanLoan2013, Theorem 2.4.8]; [HornJohnson2013, §7.4.9]. -/
theorem isBestRankApprox_truncatedSVD (C : Matrix m n 𝕜) (k : ℕ) :
    IsBestRankApprox C k (truncatedSVD C k) :=
  ⟨rank_truncatedSVD_le C k, fun _ hB => frobNorm_sub_truncatedSVD_le_of_rank_le C hB⟩

/-- A matrix of rank at most $k$ is a best approximation as soon as it does as well as the
truncated SVD:
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}} \le
\|\mathbf{C} - \llbracket \mathbf{C} \rrbracket_k\|_{\mathsf{F}}\,.$$ -/
theorem isBestRankApprox_iff {C Y : Matrix m n 𝕜} {k : ℕ} :
    IsBestRankApprox C k Y ↔ Y.rank ≤ k ∧ frobNorm (C - Y) ≤ frobNorm (C - truncatedSVD C k) :=
  ⟨fun h => ⟨h.rank_le, h.frobNorm_sub_le _ (rank_truncatedSVD_le C k)⟩, fun h =>
    ⟨h.1, fun _ hB => h.2.trans (frobNorm_sub_truncatedSVD_le_of_rank_le C hB)⟩⟩

/-- The only best approximation of rank $0$ is $\mathbf{0}$. -/
theorem isBestRankApprox_zero_iff {C Y : Matrix m n 𝕜} : IsBestRankApprox C 0 Y ↔ Y = 0 := by
  refine ⟨fun h => Matrix.rank_eq_zero.mp (Nat.le_zero.mp h.rank_le), ?_⟩
  rintro rfl
  simpa only [truncatedSVD_zero] using isBestRankApprox_truncatedSVD C 0

/-- When $\operatorname{rank}\mathbf{C} \le k$, the only best approximation of $\mathbf{C}$ of
rank at most $k$ is $\mathbf{C}$ itself. -/
theorem isBestRankApprox_iff_eq_of_rank_le {C Y : Matrix m n 𝕜} {k : ℕ} (hk : C.rank ≤ k) :
    IsBestRankApprox C k Y ↔ Y = C := by
  refine ⟨fun h => ?_, ?_⟩
  · have h0 := h.frobNorm_sub_le C hk
    rw [sub_self, frobNorm_zero] at h0
    exact (sub_eq_zero.mp (frobNorm_eq_zero_iff.mp (le_antisymm h0 (frobNorm_nonneg _)))).symm
  · rintro rfl
    simpa only [truncatedSVD_of_rank_le Y hk] using isBestRankApprox_truncatedSVD Y k

/-- Bridge to Mathlib's minimizers: $\mathbf{Y}$ is a best approximation exactly when it has rank
at most $k$ and minimizes $\mathbf{B} \mapsto \|\mathbf{C} - \mathbf{B}\|_{\mathsf{F}}$ over the
matrices of rank at most $k$. -/
theorem isBestRankApprox_iff_isMinOn {C Y : Matrix m n 𝕜} {k : ℕ} :
    IsBestRankApprox C k Y ↔
      Y.rank ≤ k ∧ IsMinOn (fun B : Matrix m n 𝕜 => frobNorm (C - B)) {B | B.rank ≤ k} Y :=
  ⟨fun h => ⟨h.rank_le, isMinOn_iff.mpr fun B hB => h.frobNorm_sub_le B hB⟩, fun h =>
    ⟨h.1, fun B hB => isMinOn_iff.mp h.2 B hB⟩⟩

/-- A best approximation has the optimal Frobenius error:
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}} =
\|\mathbf{C} - \llbracket \mathbf{C} \rrbracket_k\|_{\mathsf{F}}\,.$$ -/
theorem IsBestRankApprox.frobNorm_sub {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) : frobNorm (C - Y) = frobNorm (C - truncatedSVD C k) :=
  le_antisymm (h.frobNorm_sub_le _ (rank_truncatedSVD_le C k))
    (frobNorm_sub_truncatedSVD_le_of_rank_le C h.rank_le)

/-- **The error of a best approximation has the tail singular values**:
$\sigma_i(\mathbf{C} - \mathbf{Y}) = \sigma_{k+i}(\mathbf{C})$ for every $i$, including the zero
padding. The equality case of Weyl's inequality for a rank-$k$ perturbation.
[HornJohnson2013, §7.4.9]; there for the truncated SVD. -/
theorem IsBestRankApprox.singularValues_sub {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) (i : ℕ) : singularValues (C - Y) i = singularValues C (k + i) := by
  have hle : ∀ j, singularValues C (k + j) ≤ singularValues (C - Y) j :=
    singularValues_add_le_singularValues_sub_of_rank_le C h.rank_le
  have hN : ∀ B : Matrix m n 𝕜, B.rank ≤ min (Fintype.card m) (Fintype.card n) :=
    fun B => le_min B.rank_le_card_height B.rank_le_card_width
  have hsum : ∑ j ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues C (k + j) ^ 2 =
      ∑ j ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues (C - Y) j ^ 2 := by
    rw [← frobNorm_sq_eq_sum_range_singularValues_sq _ (hN (C - Y)), h.frobNorm_sub,
      frobNorm_sq_eq_sum_range_singularValues_sq _ (hN _)]
    exact Finset.sum_congr rfl fun j _ => by rw [singularValues_sub_truncatedSVD]
  by_cases hi : i < min (Fintype.card m) (Fintype.card n)
  · have hall := (Finset.sum_eq_sum_iff_of_le fun j _ =>
      pow_le_pow_left₀ (singularValues_nonneg C (k + j)) (hle j) 2).mp hsum
    exact ((sq_eq_sq₀ (singularValues_nonneg C _) (singularValues_nonneg _ _)).mp
      (hall i (Finset.mem_range.mpr hi))).symm
  · have h0 : singularValues (C - Y) i = 0 :=
      (singularValues_eq_zero_iff _).mpr ((hN _).trans (not_lt.mp hi))
    rw [h0]
    exact (le_antisymm ((hle i).trans h0.le) (singularValues_nonneg C _)).symm

/-- A matrix of rank at most $k$ is a best approximation of $\mathbf{C}$ exactly when its error
has the tail singular values: $\sigma_i(\mathbf{C} - \mathbf{Y}) = \sigma_{k+i}(\mathbf{C})$ for
every $i$. -/
theorem isBestRankApprox_iff_singularValues_sub {C Y : Matrix m n 𝕜} {k : ℕ} :
    IsBestRankApprox C k Y ↔
      Y.rank ≤ k ∧ ∀ i, singularValues (C - Y) i = singularValues C (k + i) := by
  refine ⟨fun h => ⟨h.rank_le, h.singularValues_sub⟩, fun h =>
    isBestRankApprox_iff.mpr ⟨h.1, le_of_eq ?_⟩⟩
  rw [← lpGauge_two_matrixNorm, ← lpGauge_two_matrixNorm]
  exact SymmetricGauge.matrixNorm_congr _
    (funext fun i => by rw [h.2, singularValues_sub_truncatedSVD])

/-- A best approximation in the Frobenius norm is a best approximation in every unitarily
invariant norm:
$\|\mathbf{C} - \mathbf{Y}\|_{\Phi} = \|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\Phi}$.
[HornJohnson2013, §7.4.9]. -/
theorem IsBestRankApprox.matrixNorm_sub {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) (Φ : SymmetricGauge) :
    Φ.matrixNorm (C - Y) = Φ.matrixNorm (C - truncatedSVD C k) :=
  Φ.matrixNorm_congr (funext fun i => by rw [h.singularValues_sub, singularValues_sub_truncatedSVD])

/-- A best approximation lies in the column space:
$\mathbf{P}_{\mathbf{C}}\mathbf{Y} = \mathbf{Y}$. -/
theorem IsBestRankApprox.rangeProjector_mul {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) : rangeProjector C * Y = Y := by
  classical
  have hP := isStarProjection_rangeProjector C
  have hPC : rangeProjector C * C = C := rangeProjector_mul_self C
  have hsplit := hP.frobNorm_sq_eq_add (C - Y)
  have e1 : rangeProjector C * (C - Y) = C - rangeProjector C * Y := by rw [Matrix.mul_sub, hPC]
  have e2 : (1 - rangeProjector C) * (C - Y) = -((1 - rangeProjector C) * Y) := by
    rw [Matrix.mul_sub, Matrix.sub_mul (1 : Matrix m m 𝕜), Matrix.one_mul, hPC, sub_self, zero_sub]
  rw [e1, e2, frobNorm_neg] at hsplit
  have hopt := pow_le_pow_left₀ (frobNorm_nonneg _)
    (h.frobNorm_sub_le _ ((Matrix.rank_mul_le_right (rangeProjector C) Y).trans h.rank_le)) 2
  have hsq : frobNorm ((1 - rangeProjector C) * Y) ^ 2 = 0 :=
    le_antisymm (by linarith) (sq_nonneg _)
  have h0 := frobNorm_eq_zero_iff.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h0
  exact h0.symm

/-- Best approximations are preserved by an isometry on the left: $\mathbf{Q}\mathbf{Y}$ is a best
approximation of $\mathbf{Q}\mathbf{X}$ if and only if $\mathbf{Y}$ is one of $\mathbf{X}$.
[TroppYurtseverUdellCevher2017, §6.2]. -/
theorem HasOrthonormalCols.isBestRankApprox_mul_iff [DecidableEq q] {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) {X Y : Matrix q n 𝕜} {k : ℕ} :
    IsBestRankApprox (Q * X) k (Q * Y) ↔ IsBestRankApprox X k Y := by
  have hd : ∀ Z : Matrix q n 𝕜, frobNorm (Q * X - Q * Z) = frobNorm (X - Z) := fun Z => by
    rw [← Matrix.mul_sub, hQ.frobNorm_mul_left]
  constructor
  · intro h
    refine ⟨by rw [← hQ.rank_mul Y]; exact h.rank_le, fun B hB => ?_⟩
    rw [← hd, ← hd]
    exact h.frobNorm_sub_le (Q * B) ((Matrix.rank_mul_le_right Q B).trans hB)
  · intro h
    refine ⟨by rw [hQ.rank_mul]; exact h.rank_le, fun B hB => ?_⟩
    classical
    rw [hd]
    have h1 : frobNorm (X - Y) ≤ frobNorm (X - Qᴴ * B) :=
      h.frobNorm_sub_le _ ((Matrix.rank_mul_le_right _ _).trans hB)
    have hsplit := hQ.frobNorm_sub_mul_sq B X
    have h2 : frobNorm (X - Qᴴ * B) ≤ frobNorm (Q * X - B) := by
      rw [frobNorm_sub_comm, frobNorm_sub_comm (Q * X)]
      refine (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).mp ?_
      rw [hsplit]
      exact le_add_of_nonneg_left (sq_nonneg _)
    exact h1.trans h2

/-- **The factored form of a truncation**: for $\mathbf{Q}$ with orthonormal columns,
$\mathbf{Q}^{\mathsf{H}}\llbracket\mathbf{Q}\mathbf{X}\rrbracket_k$ is a best approximation of
$\mathbf{X}$ of rank at most $k$; with
`NLAlib.HasOrthonormalCols.mul_conjTranspose_mul_truncatedSVD`, a truncation of
$\mathbf{Q}\mathbf{X}$ is $\mathbf{Q}$ times a best approximation of $\mathbf{X}$.
[TroppYurtseverUdellCevher2017, §6.2, (6.3)]. -/
theorem HasOrthonormalCols.isBestRankApprox_conjTranspose_mul_truncatedSVD [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) (X : Matrix q n 𝕜) (k : ℕ) :
    IsBestRankApprox X k (Qᴴ * truncatedSVD (Q * X) k) :=
  hQ.isBestRankApprox_mul_iff.mp (by
    rw [hQ.mul_conjTranspose_mul_truncatedSVD]
    exact isBestRankApprox_truncatedSVD _ _)

/-! ### Best approximations are truncated SVDs -/

/-- A best approximation is the projection of $\mathbf{C}$ onto its own column space:
$\mathbf{Y}^{\mathsf{H}}(\mathbf{C} - \mathbf{Y}) = \mathbf{0}$. -/
private theorem IsBestRankApprox.conjTranspose_mul_sub {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) : Yᴴ * (C - Y) = 0 := by
  classical
  have hP := isStarProjection_rangeProjector Y
  have hPY : rangeProjector Y * Y = Y := rangeProjector_mul_self Y
  have hsplit := hP.frobNorm_sq_eq_add (C - Y)
  have e2 : (1 - rangeProjector Y) * (C - Y) = C - rangeProjector Y * C := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.one_mul, hPY,
      sub_self, sub_zero]
  have hrank : (rangeProjector Y * C).rank ≤ k := by
    exact (Matrix.rank_mul_le_left _ _).trans ((rank_rangeProjector Y).trans_le h.rank_le)
  have hopt := pow_le_pow_left₀ (frobNorm_nonneg _) (h.frobNorm_sub_le _ hrank) 2
  rw [e2] at hsplit
  have hsq : frobNorm (rangeProjector Y * (C - Y)) ^ 2 = 0 :=
    le_antisymm (by linarith) (sq_nonneg _)
  exact rangeProjector_mul_eq_zero_iff.mp
    (frobNorm_eq_zero_iff.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq))

/-- A best rank-$k$ approximation $\mathbf{Y}$ of $\mathbf{C}$ is the projection of
$\mathbf{C}$ onto its own column space: $\mathbf{P}_{\mathbf{Y}}\mathbf{C} = \mathbf{Y}$. -/
theorem IsBestRankApprox.rangeProjector_self_mul {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) : rangeProjector Y * C = Y := by
  have h0 := rangeProjector_mul_eq_zero_iff.mpr h.conjTranspose_mul_sub
  rwa [Matrix.mul_sub, rangeProjector_mul_self, sub_eq_zero] at h0

/-- Best approximations are preserved by the conjugate transpose. -/
private theorem IsBestRankApprox.conjTranspose {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) : IsBestRankApprox Cᴴ k Yᴴ := by
  refine ⟨by rw [Matrix.rank_conjTranspose]; exact h.rank_le, fun B hB => ?_⟩
  have h1 := h.frobNorm_sub_le Bᴴ (by rwa [Matrix.rank_conjTranspose])
  rwa [← frobNorm_conjTranspose (C - Y), ← frobNorm_conjTranspose (C - Bᴴ),
    Matrix.conjTranspose_sub, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose] at h1

/-- The leading singular values of a best approximation are those of $\mathbf{C}$:
$\sigma_i(\mathbf{Y}) = \sigma_i(\mathbf{C})$ for $i < k$. -/
private theorem IsBestRankApprox.singularValues_eq_of_lt {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) {i : ℕ} (hi : i < k) :
    singularValues Y i = singularValues C i := by
  classical
  have hYE := h.conjTranspose_mul_sub
  have hPC : rangeProjector Y * C = Y := h.rangeProjector_self_mul
  have hle : ∀ j, singularValues Y j ≤ singularValues C j := fun j => by
    have h1 := singularValues_mul_le_specNorm_mul (rangeProjector Y) C j
    rw [hPC] at h1
    exact h1.trans (mul_le_of_le_one_left (singularValues_nonneg C j)
      (isStarProjection_rangeProjector Y).specNorm_le_one)
  have hpyth : frobNorm C ^ 2 = frobNorm Y ^ 2 + frobNorm (C - Y) ^ 2 := by
    have h1 := frobNorm_add_sq_of_frobInner_eq_zero (A := Y) (B := C - Y)
      (by rw [frobInner_eq_re_trace, hYE, Matrix.trace_zero, map_zero])
    rwa [add_sub_cancel] at h1
  have hsum : ∑ j ∈ Finset.range k, singularValues Y j ^ 2 =
      ∑ j ∈ Finset.range k, singularValues C j ^ 2 := by
    rw [← frobNorm_sq_eq_sum_range_singularValues_sq Y h.rank_le, ← frobNorm_truncatedSVD_sq]
    have h2 := frobNorm_sq_eq_truncatedSVD_add C k
    rw [h.frobNorm_sub] at hpyth
    linarith
  have hall := (Finset.sum_eq_sum_iff_of_le fun j _ =>
    pow_le_pow_left₀ (singularValues_nonneg Y j) (hle j) 2).mp hsum
  exact (sq_eq_sq₀ (singularValues_nonneg _ _) (singularValues_nonneg _ _)).mp
    (hall i (Finset.mem_range.mpr hi))

/-- A matrix with a nonzero diagonal left factor in a vanishing product vanishes. -/
private theorem eq_zero_of_diagonal_mul_eq_zero {p q : Type*} [Fintype p] [DecidableEq p]
    {d : p → 𝕜}
    (hd : ∀ i, d i ≠ 0) {M : Matrix p q 𝕜} (h : Matrix.diagonal d * M = 0) : M = 0 := by
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [Matrix.diagonal_mul, Matrix.zero_apply] at hij
  exact (mul_eq_zero.mp hij).resolve_left (hd i)

/-- A matrix with a nonzero diagonal right factor in a vanishing product vanishes. -/
private theorem eq_zero_of_mul_diagonal_eq_zero {p q : Type*} [Fintype q] [DecidableEq q]
    {d : q → 𝕜}
    (hd : ∀ j, d j ≠ 0) {M : Matrix p q 𝕜} (h : M * Matrix.diagonal d = 0) : M = 0 := by
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.zero_apply] at hij
  exact (mul_eq_zero.mp hij).resolve_right (hd j)

omit [Fintype m] [Fintype n] in
/-- Frames multiply out a block diagonal middle factor:
$[\mathbf{U}_1\ \mathbf{U}_2]\operatorname{diag}(\boldsymbol{\sigma}_1, \boldsymbol{\sigma}_2)
[\mathbf{V}_1\ \mathbf{V}_2]^{\mathsf{H}} = \mathbf{U}_1\operatorname{diag}(\boldsymbol{\sigma}_1)
\mathbf{V}_1^{\mathsf{H}} + \mathbf{U}_2\operatorname{diag}(\boldsymbol{\sigma}_2)
\mathbf{V}_2^{\mathsf{H}}$. -/
private theorem fromCols_mul_diagonal_sumElim_mul_conjTranspose {r₁ r₂ : Type*} [Fintype r₁]
    [Fintype r₂] [DecidableEq r₁] [DecidableEq r₂] (U₁ : Matrix m r₁ 𝕜) (U₂ : Matrix m r₂ 𝕜)
    (σ₁ : r₁ → ℝ) (σ₂ : r₂ → ℝ) (V₁ : Matrix n r₁ 𝕜) (V₂ : Matrix n r₂ 𝕜) :
    Matrix.fromCols U₁ U₂ * Matrix.diagonal (fun i => ((Sum.elim σ₁ σ₂ i : ℝ) : 𝕜)) *
        (Matrix.fromCols V₁ V₂)ᴴ =
      U₁ * Matrix.diagonal (fun i => ((σ₁ i : ℝ) : 𝕜)) * V₁ᴴ +
        U₂ * Matrix.diagonal (fun i => ((σ₂ i : ℝ) : 𝕜)) * V₂ᴴ := by
  have hD : Matrix.diagonal (fun i => ((Sum.elim σ₁ σ₂ i : ℝ) : 𝕜)) =
      Matrix.fromBlocks (Matrix.diagonal fun i => ((σ₁ i : ℝ) : 𝕜)) 0 0
        (Matrix.diagonal fun i => ((σ₂ i : ℝ) : 𝕜)) := by
    rw [Matrix.fromBlocks_diagonal]
    congr 1
    funext i
    cases i <;> rfl
  rw [hD, Matrix.fromCols_mul_fromBlocks, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows, Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add]

/-- Evaluating a function on `Fin k ⊕ Fin d` along `Fin r ≃ Fin (k + d)`. -/
private theorem sumElim_finSumFinEquiv_symm_finCongr {α : Type*} {k d r : ℕ} (h : r = k + d)
    (f : Fin k → α) (g : Fin d → α) (i : Fin r) :
    Sum.elim f g (finSumFinEquiv.symm (finCongr h i)) =
      if hi : (i : ℕ) < k then f ⟨i, hi⟩ else g ⟨i - k, by omega⟩ := by
  split_ifs with hi
  · have he : finSumFinEquiv.symm (finCongr h i) = Sum.inl ⟨i, hi⟩ :=
      (Equiv.symm_apply_eq _).mpr (Fin.ext (by simp))
    rw [he, Sum.elim_inl]
  · have he : finSumFinEquiv.symm (finCongr h i) = Sum.inr ⟨i - k, by omega⟩ :=
      (Equiv.symm_apply_eq _).mpr (Fin.ext (by simp; omega))
    rw [he, Sum.elim_inr]

/-- The Frobenius norm and the rank of $\mathbf{U}\mathbf{D}\mathbf{V}^{\mathsf{H}}$ are those of
$\mathbf{D}$, for frames $\mathbf{U}$, $\mathbf{V}$. -/
private theorem frobNorm_mul_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (D : Matrix r r 𝕜) : frobNorm (U * D * Vᴴ) = frobNorm D := by
  rw [Matrix.mul_assoc, hU.frobNorm_mul_left, hV.frobNorm_mul_conjTranspose_right]

/-- The rank of $\mathbf{U}\mathbf{D}\mathbf{V}^{\mathsf{H}}$ is that of $\mathbf{D}$, for frames
$\mathbf{U}$, $\mathbf{V}$. -/
private theorem rank_mul_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (D : Matrix r r 𝕜) : (U * D * Vᴴ).rank = D.rank := by
  rw [Matrix.mul_assoc, hU.rank_mul, ← Matrix.rank_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hV.rank_mul, Matrix.rank_conjTranspose]

/-- The orthogonality step of `IsBestRankApprox.exists_isSVD_eq`: the error $\mathbf{C} -
\mathbf{Y}$ of a best approximation annihilates the singular frames of $\mathbf{Y}$. -/
private theorem IsBestRankApprox.conjTranspose_mul_sub_eq_zero_and_sub_mul_eq_zero
    {C Y : Matrix m n 𝕜} {k : ℕ} (h : IsBestRankApprox C k Y) {U₁ : Matrix m (Fin k) 𝕜}
    {V₁ : Matrix n (Fin k) 𝕜} (h₁ : IsSVD Y U₁ (fun i : Fin k => singularValues C i) V₁)
    (hpos : ∀ i : Fin k, ((singularValues C i : ℝ) : 𝕜) ≠ 0) :
    U₁ᴴ * (C - Y) = 0 ∧ (C - Y) * V₁ = 0 := by
  have hYE : Yᴴ * (C - Y) = 0 := h.conjTranspose_mul_sub
  have hEY : (C - Y) * Yᴴ = 0 := by
    have h0 := h.conjTranspose.conjTranspose_mul_sub
    rw [Matrix.conjTranspose_conjTranspose, ← Matrix.conjTranspose_sub] at h0
    have h1 := congrArg Matrix.conjTranspose h0
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] at h1
  constructor
  · refine eq_zero_of_diagonal_mul_eq_zero hpos ?_
    have h3 := congrArg Matrix.conjTranspose h₁.mul_right_eq
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_diagonal_ofReal] at h3
    rw [← Matrix.mul_assoc, ← h3, Matrix.mul_assoc, hYE, Matrix.mul_zero]
  · refine eq_zero_of_mul_diagonal_eq_zero hpos ?_
    have h3 := congrArg Matrix.conjTranspose h₁.conjTranspose_mul_eq
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_diagonal_ofReal] at h3
    rw [Matrix.mul_assoc, ← h3, ← Matrix.mul_assoc, hEY, Matrix.zero_mul]

/-- The completion step of `IsBestRankApprox.exists_isSVD_eq`: a matrix annihilated by frames
$\mathbf{U}_1$, $\mathbf{V}_1$ is $\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{E}\mathbf{R})
\mathbf{R}^{\mathsf{H}}$ for orthogonal completions $\mathbf{Q}$, $\mathbf{R}$. -/
private theorem mul_mul_conjTranspose_eq_of_mul_eq_zero {p₁ p₂ q₁ q₂ : Type*} [Fintype p₁]
    [Fintype p₂] [Fintype q₁] [Fintype q₂] [DecidableEq m] [DecidableEq n] {E : Matrix m n 𝕜}
    {U₁ : Matrix m p₁ 𝕜} {Q : Matrix m p₂ 𝕜} {V₁ : Matrix n q₁ 𝕜} {R : Matrix n q₂ 𝕜}
    (hQQ : Q * Qᴴ = 1 - U₁ * U₁ᴴ) (hRR : R * Rᴴ = 1 - V₁ * V₁ᴴ) (hU₁E : U₁ᴴ * E = 0)
    (hEV₁ : E * V₁ = 0) :
    Q * (Qᴴ * E * R) * Rᴴ = E := by
  have h1 : Q * Qᴴ * E = E := by
    rw [hQQ, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU₁E, Matrix.mul_zero, sub_zero]
  have h2 : E * (R * Rᴴ) = E := by
    rw [hRR, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hEV₁, Matrix.zero_mul,
      sub_zero]
  calc Q * (Qᴴ * E * R) * Rᴴ = Q * Qᴴ * E * (R * Rᴴ) := by simp only [Matrix.mul_assoc]
    _ = E := by rw [h1, h2]

/-- The relabelling step of `IsBestRankApprox.exists_isSVD_eq`: SVDs of $\mathbf{C}$ and
$\mathbf{Y}$ on `Fin k ⊕ Fin (r - k)` with common frames, the singular values of $\mathbf{C}$ in
order and those of $\mathbf{Y}$ truncated, give the conclusion on `Fin r`. -/
private theorem exists_isSVD_eq_of_sumElim {C Y : Matrix m n 𝕜} {k r : ℕ} (hkr : k ≤ r)
    {U : Matrix m (Fin k ⊕ Fin (r - k)) 𝕜} {V : Matrix n (Fin k ⊕ Fin (r - k)) 𝕜}
    (hC : IsSVD C U (Sum.elim (fun i : Fin k => singularValues C i)
      (fun j : Fin (r - k) => singularValues C (k + j))) V)
    (hY : IsSVD Y U (Sum.elim (fun i : Fin k => singularValues C i)
      (fun _ : Fin (r - k) => (0 : ℝ))) V) :
    ∃ (U : Matrix m (Fin r) 𝕜) (V : Matrix n (Fin r) 𝕜),
      IsSVD C U (fun i => singularValues C i) V ∧
        Y = U * Matrix.diagonal (fun i : Fin r =>
          if (i : ℕ) < k then ((singularValues C i : ℝ) : 𝕜) else 0) * Vᴴ := by
  have hrk : r = k + (r - k) := by omega
  obtain ⟨e, he⟩ : ∃ e : Fin r ≃ Fin k ⊕ Fin (r - k),
      e = (finCongr hrk).trans finSumFinEquiv.symm := ⟨_, rfl⟩
  have happ : ∀ {α : Type} (f : Fin k → α) (g : Fin (r - k) → α) (i : Fin r),
      Sum.elim f g (e i) = if hi : (i : ℕ) < k then f ⟨i, hi⟩ else g ⟨i - k, by omega⟩ :=
    fun f g i => by rw [he, Equiv.trans_apply, sumElim_finSumFinEquiv_symm_finCongr]
  refine ⟨U.submatrix id e, V.submatrix id e, ?_, (hY.reindex e).eq.trans ?_⟩
  · have hσ : (Sum.elim (fun i : Fin k => singularValues C i)
        (fun j : Fin (r - k) => singularValues C (k + j))) ∘ e =
          fun i : Fin r => singularValues C i := by
      funext i
      rw [Function.comp_apply, happ]
      split_ifs with hi
      · rfl
      · exact congrArg (singularValues C) (by simp only; omega)
    have h3 := hC.reindex e
    rwa [hσ] at h3
  · have hd : (fun i : Fin r => (((Sum.elim (fun i : Fin k => singularValues C i)
        (fun _ : Fin (r - k) => (0 : ℝ)) ∘ e) i : ℝ) : 𝕜)) =
          fun i : Fin r => if (i : ℕ) < k then ((singularValues C i : ℝ) : 𝕜) else 0 := by
      funext i
      rw [Function.comp_apply, happ]
      split_ifs with hi
      · rfl
      · exact RCLike.ofReal_zero
    rw [hd]

/-- Every best approximation is the truncation of a thin SVD of $\mathbf{C}$ with sorted singular
values: the direction (⇒) of `NLAlib.isBestRankApprox_iff_exists_isSVD`. -/
private theorem IsBestRankApprox.exists_isSVD_eq {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) :
    ∃ (U : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜)
      (V : Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜),
      IsSVD C U (fun i => singularValues C i) V ∧
        Y = U * Matrix.diagonal (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
          if (i : ℕ) < k then ((singularValues C i : ℝ) : 𝕜) else 0) * Vᴴ := by
  classical
  by_cases hk : C.rank ≤ k
  · refine ⟨svdU C, svdV C, isSVD_svdU_svdV C, ?_⟩
    rw [← truncatedSVD_def, truncatedSVD_of_rank_le C hk]
    exact (isBestRankApprox_iff_eq_of_rank_le hk).mp h
  rw [not_le] at hk
  set r := min (Fintype.card m) (Fintype.card n)
  have hkm : k ≤ Fintype.card m := hk.le.trans C.rank_le_card_height
  have hkn : k ≤ Fintype.card n := hk.le.trans C.rank_le_card_width
  have hpos : ∀ i : Fin k, ((singularValues C i : ℝ) : 𝕜) ≠ 0 := fun i =>
    RCLike.ofReal_ne_zero.mpr ((singularValues_pos_iff C).mpr (i.2.trans hk)).ne'
  -- the leading block: an SVD of `Y`
  obtain ⟨U₁, V₁, h₁⟩ := NLAlib.exists_isSVD Y h.rank_le hkm hkn
  have hσ₁ : (fun i : Fin k => singularValues Y i) = fun i : Fin k => singularValues C i :=
    funext fun i => h.singularValues_eq_of_lt i.2
  rw [hσ₁] at h₁
  obtain ⟨E, hE⟩ : ∃ E, E = C - Y := ⟨_, rfl⟩
  obtain ⟨hU₁E, hEV₁⟩ := hE ▸ h.conjTranspose_mul_sub_eq_zero_and_sub_mul_eq_zero h₁ hpos
  -- the error lives on the orthogonal completions of the leading frames
  obtain ⟨Q, hQ⟩ := h₁.hasOrthonormalCols_left.exists_fromCols
    (p := Fin (Fintype.card m - k)) (by simp only [Fintype.card_fin]; omega)
  obtain ⟨R, hR⟩ := h₁.hasOrthonormalCols_right.exists_fromCols
    (p := Fin (Fintype.card n - k)) (by simp only [Fintype.card_fin]; omega)
  obtain ⟨-, hQo, hU₁Q⟩ := hasOrthonormalCols_fromCols_iff.mp hQ
  obtain ⟨-, hRo, hV₁R⟩ := hasOrthonormalCols_fromCols_iff.mp hR
  have hQQ : Q * Qᴴ = 1 - U₁ * U₁ᴴ := eq_sub_of_add_eq'
    (hQ.mul_conjTranspose_add_mul_conjTranspose (by simp only [Fintype.card_fin]; omega))
  have hRR : R * Rᴴ = 1 - V₁ * V₁ᴴ := eq_sub_of_add_eq'
    (hR.mul_conjTranspose_add_mul_conjTranspose (by simp only [Fintype.card_fin]; omega))
  obtain ⟨M, hM⟩ : ∃ M, M = Qᴴ * E * R := ⟨_, rfl⟩
  have hEM : Q * M * Rᴴ = E := hM ▸ mul_mul_conjTranspose_eq_of_mul_eq_zero hQQ hRR hU₁E hEV₁
  have hsvM : ∀ j, singularValues M j = singularValues C (k + j) := fun j => by
    rw [← hQo.singularValues_mul_left M, ← hRo.singularValues_mul_conjTranspose_right (Q * M), hEM,
      hE, h.singularValues_sub]
  -- the trailing block: an SVD of the error
  have hMr : M.rank ≤ r - k := by
    have h1 := M.rank_le_card_height
    have h2 := M.rank_le_card_width
    simp only [Fintype.card_fin] at h1 h2
    omega
  obtain ⟨U', V', h'⟩ := NLAlib.exists_isSVD M hMr (by simp only [Fintype.card_fin]; omega)
    (by simp only [Fintype.card_fin]; omega)
  have hσ₂ : (fun j : Fin (r - k) => singularValues M j) =
      fun j : Fin (r - k) => singularValues C (k + j) :=
    funext fun j => hsvM j
  rw [hσ₂] at h'
  have h₂ := (h'.mul_left hQo).mul_conjTranspose_right hRo
  rw [hEM] at h₂
  have hU : HasOrthonormalCols (Matrix.fromCols U₁ (Q * U')) :=
    hasOrthonormalCols_fromCols_iff.mpr ⟨h₁.hasOrthonormalCols_left, h₂.hasOrthonormalCols_left,
      by rw [← Matrix.mul_assoc, hU₁Q, Matrix.zero_mul]⟩
  have hV : HasOrthonormalCols (Matrix.fromCols V₁ (R * V')) :=
    hasOrthonormalCols_fromCols_iff.mpr ⟨h₁.hasOrthonormalCols_right, h₂.hasOrthonormalCols_right,
      by rw [← Matrix.mul_assoc, hV₁R, Matrix.zero_mul]⟩
  have hC : IsSVD C (Matrix.fromCols U₁ (Q * U'))
      (Sum.elim (fun i : Fin k => singularValues C i)
        (fun j : Fin (r - k) => singularValues C (k + j))) (Matrix.fromCols V₁ (R * V')) := by
    refine ⟨hU, hV, fun i => ?_, ?_⟩
    · cases i <;> exact singularValues_nonneg _ _
    · rw [fromCols_mul_diagonal_sumElim_mul_conjTranspose, ← h₁.eq, ← h₂.eq, hE,
        add_sub_cancel]
  have hY : IsSVD Y (Matrix.fromCols U₁ (Q * U'))
      (Sum.elim (fun i : Fin k => singularValues C i) (fun _ : Fin (r - k) => (0 : ℝ)))
      (Matrix.fromCols V₁ (R * V')) := by
    refine ⟨hU, hV, fun i => ?_, ?_⟩
    · cases i
      · exact singularValues_nonneg _ _
      · exact le_rfl
    · rw [fromCols_mul_diagonal_sumElim_mul_conjTranspose, ← h₁.eq]
      simp only [RCLike.ofReal_zero, Matrix.diagonal_zero, Matrix.mul_zero, Matrix.zero_mul,
        add_zero]
  exact exists_isSVD_eq_of_sumElim (by omega) hC hY

/-- **Every best approximation is a truncated SVD**: $\mathbf{Y}$ is a best approximation of
$\mathbf{C}$ of rank at most $k$ if and only if, for some thin singular value decomposition
$\mathbf{C} = \mathbf{U}\operatorname{diag}(\sigma_0(\mathbf{C}), \dots,
\sigma_{r-1}(\mathbf{C}))\mathbf{V}^{\mathsf{H}}$ with $r = \min(\lvert m\rvert, \lvert n\rvert)$
orthonormal columns and the singular values in non-increasing order,
$$\mathbf{Y} = \mathbf{U}\operatorname{diag}\bigl(\sigma_0(\mathbf{C}), \dots,
\sigma_{k-1}(\mathbf{C}), 0, \dots, 0\bigr)\mathbf{V}^{\mathsf{H}}\,.$$
So the best approximations are exactly the truncations of the SVDs of $\mathbf{C}$, in the shape
of `NLAlib.truncatedSVD`, which is the one built from the chosen SVD (`NLAlib.svdU`,
`NLAlib.svdV`). It holds under ties $\sigma_{k-1}(\mathbf{C}) = \sigma_k(\mathbf{C})$, where there
are many, and for $k \ge \operatorname{rank}\mathbf{C}$, where $\mathbf{Y} = \mathbf{C}$.
[GolubVanLoan2013, Theorem 2.4.8]; [HornJohnson2013, §7.4.9]; there that the truncation of an SVD
is a best approximation, here also the converse, the equality case of Eckart–Young. -/
theorem isBestRankApprox_iff_exists_isSVD {C Y : Matrix m n 𝕜} {k : ℕ} :
    IsBestRankApprox C k Y ↔
      ∃ (U : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜)
        (V : Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜),
        IsSVD C U (fun i => singularValues C i) V ∧
          Y = U * Matrix.diagonal (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
            if (i : ℕ) < k then ((singularValues C i : ℝ) : 𝕜) else 0) * Vᴴ := by
  refine ⟨fun h => h.exists_isSVD_eq, ?_⟩
  rintro ⟨U, V, hC, rfl⟩
  have hS := isSVD_svdU_svdV C
  have hE : ∀ {U' : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜}
      {V' : Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜},
      IsSVD C U' (fun i => singularValues C i) V' →
        C - U' * Matrix.diagonal (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
            if (i : ℕ) < k then ((singularValues C i : ℝ) : 𝕜) else 0) * V'ᴴ =
          U' * (Matrix.diagonal (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
              ((singularValues C i : ℝ) : 𝕜)) -
            Matrix.diagonal (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
              if (i : ℕ) < k then ((singularValues C i : ℝ) : 𝕜) else 0)) * V'ᴴ :=
    fun h => by rw [Matrix.mul_sub, Matrix.sub_mul, ← h.eq]
  refine isBestRankApprox_iff.mpr ⟨?_, le_of_eq ?_⟩
  · rw [rank_mul_mul_conjTranspose hC.hasOrthonormalCols_left hC.hasOrthonormalCols_right,
      ← rank_mul_mul_conjTranspose hS.hasOrthonormalCols_left hS.hasOrthonormalCols_right,
      ← truncatedSVD_def]
    exact rank_truncatedSVD_le C k
  · rw [truncatedSVD_def, hE hC, hE hS,
      frobNorm_mul_mul_conjTranspose hC.hasOrthonormalCols_left hC.hasOrthonormalCols_right,
      frobNorm_mul_mul_conjTranspose hS.hasOrthonormalCols_left hS.hasOrthonormalCols_right]

/-! ### Truncating an approximation -/

/-- **Domination passes to the tails**: if $\sigma_i(\hat{\mathbf{A}}) \le \sigma_i(\mathbf{A})$
for every $i$, then in every unitarily invariant norm
$$\|\hat{\mathbf{A}} - \llbracket\hat{\mathbf{A}}\rrbracket_k\|_{\Phi} \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\Phi}\,.$$
[HalkoMartinssonTropp2011, Theorem 9.3 (proof)]. -/
theorem SymmetricGauge.matrixNorm_sub_truncatedSVD_le_of_singularValues_le (Φ : SymmetricGauge)
    {A Â : Matrix m n 𝕜} (h : ∀ i, singularValues Â i ≤ singularValues A i) (k : ℕ) :
    Φ.matrixNorm (Â - truncatedSVD Â k) ≤ Φ.matrixNorm (A - truncatedSVD A k) :=
  Φ.matrixNorm_le_of_singularValues_le fun i => by
    rw [singularValues_sub_truncatedSVD, singularValues_sub_truncatedSVD]
    exact h (k + i)

/-- **The truncation lemma, constant one.** If
$\sigma_i(\hat{\mathbf{A}}) \le \sigma_i(\mathbf{A})$ for every $i$ and $\mathbf{Y}$ is a
best rank-$k$ approximation of $\hat{\mathbf{A}}$, then in every unitarily invariant norm
$$\|\mathbf{A} - \mathbf{Y}\|_{\Phi} \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\Phi} +
\|\mathbf{A} - \hat{\mathbf{A}}\|_{\Phi}\,.$$
The hypothesis holds for $\hat{\mathbf{A}} = \mathbf{P}\mathbf{A}$ with $\mathbf{P}$ an orthogonal
projector (`IsStarProjection.singularValues_mul_le`) and for Nyström of a positive semidefinite
matrix (`Matrix.PosSemidef.singularValues_nystrom_le`); without it the constant is two
(`NLAlib.IsBestRankApprox.matrixNorm_sub_le_add_two_mul`).
[HalkoMartinssonTropp2011, Theorem 9.3]; there in the spectral norm, for $\mathbf{P}\mathbf{A}$
and a spectral-best $\mathbf{Y}$; here every gauge, any dominated $\hat{\mathbf{A}}$, Frobenius-best
$\mathbf{Y}$.
Result: truncation-lemma -/
theorem IsBestRankApprox.matrixNorm_sub_le_add_of_singularValues_le {A Â Y : Matrix m n 𝕜}
    {k : ℕ} (hY : IsBestRankApprox Â k Y) (h : ∀ i, singularValues Â i ≤ singularValues A i)
    (Φ : SymmetricGauge) :
    Φ.matrixNorm (A - Y) ≤ Φ.matrixNorm (A - truncatedSVD A k) + Φ.matrixNorm (A - Â) := by
  have e : A - Y = (A - Â) + (Â - Y) := by abel
  have h1 := Φ.matrixNorm_add_le (A - Â) (Â - Y)
  have h2 := Φ.matrixNorm_sub_truncatedSVD_le_of_singularValues_le h k
  rw [← e, hY.matrixNorm_sub Φ] at h1
  linarith

/-- **The truncation lemma, constant two.** For any $\hat{\mathbf{A}}$ and any best rank-$k$
approximation $\mathbf{Y}$ of it, in every unitarily invariant norm
$$\|\mathbf{A} - \mathbf{Y}\|_{\Phi} \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\Phi} +
2\|\mathbf{A} - \hat{\mathbf{A}}\|_{\Phi}\,.$$
[TroppYurtseverUdellCevher2017, Proposition 6.1, Remark 6.2];
[TroppYurtseverUdellCevher2017a, Proposition A.6]; there in the Frobenius, spectral and Schatten
norms, here every unitarily invariant norm.
Result: truncation-lemma -/
theorem IsBestRankApprox.matrixNorm_sub_le_add_two_mul {Â Y : Matrix m n 𝕜} {k : ℕ}
    (hY : IsBestRankApprox Â k Y) (Φ : SymmetricGauge) (A : Matrix m n 𝕜) :
    Φ.matrixNorm (A - Y) ≤ Φ.matrixNorm (A - truncatedSVD A k) + 2 * Φ.matrixNorm (A - Â) := by
  have e : A - Y = (A - Â) + (Â - Y) := by abel
  have h1 := Φ.matrixNorm_add_le (A - Â) (Â - Y)
  have h3 := Φ.matrixNorm_sub_truncatedSVD_le_of_rank_le Â (rank_truncatedSVD_le A k)
  have e4 : Â - truncatedSVD A k = -(A - Â) + (A - truncatedSVD A k) := by abel
  have h5 := Φ.matrixNorm_add_le (-(A - Â)) (A - truncatedSVD A k)
  rw [Φ.matrixNorm_neg] at h5
  rw [← e, hY.matrixNorm_sub Φ] at h1
  rw [e4] at h3
  linarith

/-- **Reverse Eckart–Young, Frobenius form.** For $\mathbf{B}$ of rank at most $k$, the spectral
error exceeds the optimal one by at most the Frobenius excess:
$$\|\mathbf{A} - \mathbf{B}\|_2^2 + \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
\le \sigma_k(\mathbf{A})^2 + \|\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}^2\,.$$
[Gu2015, Theorem 3.4]; [TroppYurtseverUdellCevher2017a, Proposition A.8 (proof)];
[TroppWebber2023, §9.1]; subtraction-free, indices from $0$.
Result: reverse-eckart-young -/
theorem specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_rank_le (A : Matrix m n 𝕜)
    {B : Matrix m n 𝕜} {k : ℕ} (hB : B.rank ≤ k) :
    specNorm (A - B) ^ 2 + frobNorm (A - truncatedSVD A k) ^ 2 ≤
      singularValues A k ^ 2 + frobNorm (A - B) ^ 2 := by
  have hN : ∀ M : Matrix m n 𝕜, M.rank ≤ min (Fintype.card m) (Fintype.card n) + 1 :=
    fun M => (le_min M.rank_le_card_height M.rank_le_card_width).trans (Nat.le_succ _)
  rw [frobNorm_sq_eq_sum_range_singularValues_sq _ (hN (A - truncatedSVD A k)),
    frobNorm_sq_eq_sum_range_singularValues_sq _ (hN (A - B)), Finset.sum_range_succ',
    Finset.sum_range_succ', ← singularValues_zero_eq_specNorm]
  simp only [singularValues_sub_truncatedSVD, add_zero]
  have hs : ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A (k + (i + 1)) ^ 2 ≤
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues (A - B) (i + 1) ^ 2 :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (singularValues_nonneg _ _)
      (singularValues_add_le_singularValues_sub_of_rank_le A hB (i + 1)) 2
  linarith

/-- **Reverse Eckart–Young, nuclear form.** For $\mathbf{B}$ of rank at most $k$,
$$\|\mathbf{A} - \mathbf{B}\|_2 + \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_*
\le \sigma_k(\mathbf{A}) + \|\mathbf{A} - \mathbf{B}\|_*\,.$$
[TroppYurtseverUdellCevher2017a, Proposition A.8]; [Gu2015, Theorem 3.4]; there
$$\|\mathbf{A} - \mathbf{B}\|_2 \le \sigma_{r+1}(\mathbf{A}) + \|\mathbf{A} - \mathbf{B}\|_* -
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_*$$
with indices from $1$, here subtraction-free.
Result: reverse-eckart-young -/
theorem specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_rank_le (A : Matrix m n 𝕜)
    {B : Matrix m n 𝕜} {k : ℕ} (hB : B.rank ≤ k) :
    specNorm (A - B) + nuclearNorm (A - truncatedSVD A k) ≤
      singularValues A k + nuclearNorm (A - B) := by
  have hN : ∀ M : Matrix m n 𝕜, M.rank ≤ min (Fintype.card m) (Fintype.card n) + 1 :=
    fun M => (le_min M.rank_le_card_height M.rank_le_card_width).trans (Nat.le_succ _)
  rw [nuclearNorm_eq_sum_range _ (hN (A - truncatedSVD A k)),
    nuclearNorm_eq_sum_range _ (hN (A - B)), Finset.sum_range_succ', Finset.sum_range_succ',
    ← singularValues_zero_eq_specNorm]
  simp only [singularValues_sub_truncatedSVD, add_zero]
  have hs : ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A (k + (i + 1)) ≤
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues (A - B) (i + 1) :=
    Finset.sum_le_sum fun i _ => singularValues_add_le_singularValues_sub_of_rank_le A hB (i + 1)
  linarith


/-- **The tail of the singular values in the nuclear norm.** For every $\mathbf{A}$ and every
$r \ge 1$,
$$\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}} \le
\frac{\|\mathbf{A}\|_*}{2\sqrt{r}}\,:$$
the tail $\sum_{i \ge r}\sigma_i^2$ is at most $\sigma_{r-1}\sum_{i \ge r}\sigma_i \le
(1/r)\bigl(\sum_{i < r}\sigma_i\bigr)\bigl(\sum_{i \ge r}\sigma_i\bigr) \le
\|\mathbf{A}\|_*^2/(4r)$. The positive semidefinite form, with
$\operatorname{Re}\operatorname{tr}\mathbf{A}$, is
`Matrix.PosSemidef.frobNorm_sub_truncatedSVD_le_re_trace_div`.
[GilbertStraussTroppVershynin2007, Lemma 7]; [MeyerMuscoMuscoWoodruff2021, Imported Lemma 13 and
§5 after Theorem 10]; [EpperlyTroppWebber2024, Fact 5.5]; GSTV state it for vectors and the
$\ell_1$ norm, MMMW for positive semidefinite matrices with the trace, remarking that the proof
gives the nuclear norm for any $\mathbf{A}$.
Result: frobenius-tail-nuclear-norm -/
theorem frobNorm_sub_truncatedSVD_le_nuclearNorm_div (A : Matrix m n 𝕜) {r : ℕ} (hr : 0 < r) :
    frobNorm (A - truncatedSVD A r) ≤ nuclearNorm A / (2 * √(r : ℝ)) := by
  set N := min (Fintype.card m) (Fintype.card n)
  set σ := singularValues A
  have hrN : A.rank ≤ r + N :=
    (le_min A.rank_le_card_height A.rank_le_card_width).trans (Nat.le_add_left _ _)
  set a := ∑ i ∈ Finset.range r, σ i
  set b := ∑ i ∈ Finset.Ico r (r + N), σ i
  have hnuc : nuclearNorm A = a + b := by
    rw [nuclearNorm_eq_sum_range A hrN, Finset.sum_range_add_sum_Ico _ (Nat.le_add_right r N)]
  have hσ := singularValues_nonneg A
  have hT : frobNorm (A - truncatedSVD A r) ^ 2 ≤ σ r * b := by
    rw [frobNorm_sub_truncatedSVD_sq, Finset.mul_sum]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right
      (Nat.le_add_left N r)) fun i _ _ => sq_nonneg _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [sq]
    exact mul_le_mul_of_nonneg_right (singularValues_antitone A (Finset.mem_Ico.mp hi).1) (hσ i)
  have ha : (r : ℝ) * σ r ≤ a := by
    have := Finset.sum_le_sum fun i (hi : i ∈ Finset.range r) =>
      singularValues_antitone A (Finset.mem_range.mp hi).le
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  have hb : 0 ≤ b := Finset.sum_nonneg fun i _ => hσ i
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hsq : (frobNorm (A - truncatedSVD A r) * (2 * √(r : ℝ))) ^ 2 ≤ nuclearNorm A ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hr'.le, hnuc]
    nlinarith [mul_le_mul_of_nonneg_right ha hb, sq_nonneg (a - b),
      mul_le_mul_of_nonneg_left hT hr'.le]
  rw [le_div_iff₀ (by positivity)]
  exact (pow_le_pow_iff_left₀ (by positivity) (nuclearNorm_nonneg A) two_ne_zero).mp hsq

/-- **The tail of the eigenvalues of a positive semidefinite matrix.** For positive semidefinite
$\mathbf{A}$ and $r \ge 1$,
$$\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}} \le
\frac{\operatorname{Re}\operatorname{tr}\mathbf{A}}{2\sqrt{r}}\,,$$
`NLAlib.frobNorm_sub_truncatedSVD_le_nuclearNorm_div` with
$\|\mathbf{A}\|_* = \operatorname{Re}\operatorname{tr}\mathbf{A}$.
[MeyerMuscoMuscoWoodruff2021, Imported Lemma 13]; [GilbertStraussTroppVershynin2007, Lemma 7];
MMMW's Lemma 3 is the same bound without the factor $1/2$. -/
theorem _root_.Matrix.PosSemidef.frobNorm_sub_truncatedSVD_le_re_trace_div {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {r : ℕ} (hr : 0 < r) :
    frobNorm (A - truncatedSVD A r) ≤ RCLike.re A.trace / (2 * √(r : ℝ)) := by
  rw [← hA.nuclearNorm_eq_re_trace]
  exact frobNorm_sub_truncatedSVD_le_nuclearNorm_div A hr

/-! ### Perturbed truncation, Gram matrices -/

/-- The Frobenius inner product with a matrix of rank at most $r$ only sees the $r$ leading
singular values: if $\operatorname{rank}\mathbf{X} \le r$ then
$$\langle\mathbf{X}, \mathbf{E}\rangle_{\mathsf{F}} \le
\|\mathbf{X}\|_{\mathsf{F}} \|\llbracket\mathbf{E}\rrbracket_r\|_{\mathsf{F}}\,,$$
and
$\|\llbracket\mathbf{E}\rrbracket_r\|_{\mathsf{F}} \le \sqrt{r}\,\|\mathbf{E}\|_2$ recovers
`NLAlib.frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le`.
[HornJohnson2013, Theorem 7.4.1.1]; von Neumann's trace inequality and Cauchy–Schwarz. -/
theorem frobInner_le_frobNorm_mul_frobNorm_truncatedSVD_of_rank_le {X : Matrix m n 𝕜} {r : ℕ}
    (hX : X.rank ≤ r) (E : Matrix m n 𝕜) :
    frobInner X E ≤ frobNorm X * frobNorm (truncatedSVD E r) := by
  have hN : ∀ B : Matrix m n 𝕜, B.rank ≤ min (Fintype.card m) (Fintype.card n) :=
    fun B => le_min B.rank_le_card_height B.rank_le_card_width
  have h1 := (le_abs_self _).trans (abs_frobInner_le_sum_singularValues_mul X E)
  have h2 : ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues X i * singularValues E i =
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues X i * singularValues (truncatedSVD E r) i :=
    Finset.sum_congr rfl fun i _ => by
      rw [singularValues_truncatedSVD]
      split_ifs with hi
      · rfl
      · rw [(singularValues_eq_zero_iff X).mpr (hX.trans (not_lt.mp hi)), zero_mul, zero_mul]
  refine h1.trans (h2.le.trans ((Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans_eq ?_))
  rw [← frobNorm_sq_eq_sum_range_singularValues_sq X (hN X),
    ← frobNorm_sq_eq_sum_range_singularValues_sq _ (hN _), Real.sqrt_sq (frobNorm_nonneg _),
    Real.sqrt_sq (frobNorm_nonneg _)]

/-- **Perturbed truncation.** For any $\mathbf{C}$, $\mathbf{E}$ and any best rank-$k$
approximation $\mathbf{Y}$ of $\mathbf{C} + \mathbf{E}$,
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}} \le
\|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}} +
2\,\|\llbracket\mathbf{E}\rrbracket_{2k}\|_{\mathsf{F}}\,:$$
truncating a perturbed matrix pays only the $2k$ leading singular values of the perturbation. In
the Frobenius norm it dominates the constant-two lemma
(`NLAlib.IsBestRankApprox.matrixNorm_sub_le_add_two_mul`), since
$\|\llbracket\mathbf{E}\rrbracket_{2k}\|_{\mathsf{F}} \le \|\mathbf{E}\|_{\mathsf{F}}$.
Proved without a literature source; the input is von Neumann's trace inequality
[HornJohnson2013, Theorem 7.4.1.1]. Related: [TroppYurtseverUdellCevher2017, Proposition 6.1].
Result: perturbed-truncation -/
theorem IsBestRankApprox.frobNorm_sub_le_add_frobNorm_truncatedSVD {C E Y : Matrix m n 𝕜}
    {k : ℕ} (hY : IsBestRankApprox (C + E) k Y) :
    frobNorm (C - Y) ≤
      frobNorm (C - truncatedSVD C k) + 2 * frobNorm (truncatedSVD E (2 * k)) := by
  have hopt := pow_le_pow_left₀ (frobNorm_nonneg _)
    (hY.frobNorm_sub_le (truncatedSVD C k) (rank_truncatedSVD_le C k)) 2
  have e1 : frobNorm (C - Y) ^ 2 =
      frobNorm (C + E - Y) ^ 2 - 2 * frobInner (C + E - Y) E + frobNorm E ^ 2 := by
    rw [← frobNorm_sub_sq, show C + E - Y - E = C - Y by abel]
  have e2 : frobNorm (C + E - truncatedSVD C k) ^ 2 =
      frobNorm (C - truncatedSVD C k) ^ 2 + 2 * frobInner (C - truncatedSVD C k) E +
        frobNorm E ^ 2 := by
    rw [← frobNorm_add_sq, show C - truncatedSVD C k + E = C + E - truncatedSVD C k by abel]
  have e3 : frobInner (C - truncatedSVD C k) E - frobInner (C + E - Y) E =
      frobInner (Y - truncatedSVD C k) E - frobNorm E ^ 2 := by
    rw [← frobInner_self, ← frobInner_sub_left, ← frobInner_sub_left]
    congr 1
    abel
  have hrank : (Y - truncatedSVD C k).rank ≤ 2 * k := by
    have := hY.rank_le
    have := rank_truncatedSVD_le C k
    exact (Matrix.rank_sub_le _ _).trans (by omega)
  have htri : frobNorm (Y - truncatedSVD C k) ≤
      frobNorm (C - Y) + frobNorm (C - truncatedSVD C k) := by
    rw [show Y - truncatedSVD C k = (C - truncatedSVD C k) - (C - Y) by abel]
    exact (_root_.NLAlib.frobNorm_sub_le _ _).trans_eq (add_comm _ _)
  have hβ := frobNorm_nonneg (truncatedSVD E (2 * k))
  have hinner : frobInner (Y - truncatedSVD C k) E ≤ frobNorm (truncatedSVD E (2 * k)) *
      (frobNorm (C - Y) + frobNorm (C - truncatedSVD C k)) :=
    (frobInner_le_frobNorm_mul_frobNorm_truncatedSVD_of_rank_le hrank E).trans
      (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left htri hβ)
  have hΔ := frobNorm_nonneg (C - truncatedSVD C k)
  by_contra hcon
  replace hcon := not_le.mp hcon
  have h1 : 0 < frobNorm (C - Y) + frobNorm (C - truncatedSVD C k) := by linarith
  have h2 : 0 < frobNorm (C - Y) - frobNorm (C - truncatedSVD C k) -
      2 * frobNorm (truncatedSVD E (2 * k)) := by linarith
  nlinarith [mul_pos h1 h2]

/-- **Perturbed truncation, spectral form**: for any best rank-$k$ approximation $\mathbf{Y}$ of
$\mathbf{C} + \mathbf{E}$,
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}} \le
\|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}} + 2\sqrt{2k}\,\|\mathbf{E}\|_2\,.$$
Better than the constant-two lemma when $\mathbf{E}$ has stable rank above $2k$, the case of the
core noise of sketched regression; a corollary of
`NLAlib.IsBestRankApprox.frobNorm_sub_le_add_frobNorm_truncatedSVD`.
Proved without a literature source. Related: [TroppYurtseverUdellCevher2017, Proposition 6.1].
Result: perturbed-truncation -/
theorem IsBestRankApprox.frobNorm_sub_le_add_specNorm {C E Y : Matrix m n 𝕜} {k : ℕ}
    (hY : IsBestRankApprox (C + E) k Y) :
    frobNorm (C - Y) ≤ frobNorm (C - truncatedSVD C k) + 2 * √(2 * (k : ℝ)) * specNorm E := by
  refine hY.frobNorm_sub_le_add_frobNorm_truncatedSVD.trans ?_
  have h : frobNorm (truncatedSVD E (2 * k)) ≤ √(2 * (k : ℝ)) * specNorm E := by
    refine (frobNorm_le_sqrt_rank_mul_specNorm _).trans
      (mul_le_mul ?_ ?_ (specNorm_nonneg _) (Real.sqrt_nonneg _))
    · have := rank_truncatedSVD_le E (2 * k)
      exact Real.sqrt_le_sqrt (by exact_mod_cast this)
    · rw [← singularValues_zero_eq_specNorm, ← singularValues_zero_eq_specNorm,
        singularValues_truncatedSVD]
      split_ifs
      exacts [le_rfl, singularValues_nonneg _ _]
  linarith

/-- **Truncation commutes with the Gram map in trace**: the nuclear error of truncating
$\mathbf{G}^{\mathsf{H}}\mathbf{G}$ is the squared Frobenius error of truncating $\mathbf{G}$,
$$\|\mathbf{G}^{\mathsf{H}}\mathbf{G} - \llbracket\mathbf{G}^{\mathsf{H}}\mathbf{G}\rrbracket_k\|_*
= \|\mathbf{G} - \llbracket\mathbf{G}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
for every choice of either truncation.
[TroppYurtseverUdellCevher2017a, App. A.5]; [MartinssonTropp2020, §14.2]; there inside the proof
of a Nyström bound for $\mathbf{A}^{1/2}$, here any factor. -/
theorem nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD (G : Matrix m n 𝕜) (k : ℕ) :
    nuclearNorm (Gᴴ * G - truncatedSVD (Gᴴ * G) k) = frobNorm (G - truncatedSVD G k) ^ 2 := by
  rw [nuclearNorm_eq_sum_range _ (Matrix.rank_le_card_width (Gᴴ * G - truncatedSVD (Gᴴ * G) k)),
    frobNorm_sq_eq_sum_range_singularValues_sq _
      (Matrix.rank_le_card_width (G - truncatedSVD G k))]
  exact Finset.sum_congr rfl fun i _ => by
    rw [singularValues_sub_truncatedSVD, singularValues_conjTranspose_mul_self,
      singularValues_sub_truncatedSVD]

/-- **Truncation commutes with the Gram map in every unitarily invariant norm**:
$$\|\mathbf{G}^{\mathsf{H}}\mathbf{G} - \llbracket\mathbf{G}^{\mathsf{H}}\mathbf{G}\rrbracket_k
\|_{\Phi} = \|(\mathbf{G} - \llbracket\mathbf{G}\rrbracket_k)^{\mathsf{H}}
(\mathbf{G} - \llbracket\mathbf{G}\rrbracket_k)\|_{\Phi}\,,$$
independent of the choice `truncatedSVD` makes on either side (both error matrices have the
singular values $\sigma_{k+i}(\mathbf{G})^2$). The nuclear case is
`NLAlib.nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD`. It moves the best errors of a
positive semidefinite $\mathbf{H} = \mathbf{G}^{\mathsf{H}}\mathbf{G}$ to those of a factor, with
no square root.
[TroppYurtseverUdellCevher2017a, App. A.5]; [TroppWebber2023, proof of Corollary 8.8]; there the
trace and Schatten forms, implicitly inside proofs, with $\mathbf{G} = \mathbf{A}^{1/2}$. -/
theorem SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_truncatedSVD (Φ : SymmetricGauge)
    (G : Matrix m n 𝕜) (k : ℕ) :
    Φ.matrixNorm (Gᴴ * G - truncatedSVD (Gᴴ * G) k) =
      Φ.matrixNorm ((G - truncatedSVD G k)ᴴ * (G - truncatedSVD G k)) :=
  Φ.matrixNorm_congr (funext fun i => by
    rw [singularValues_sub_truncatedSVD, singularValues_conjTranspose_mul_self,
      singularValues_conjTranspose_mul_self, singularValues_sub_truncatedSVD])

end NLAlib
