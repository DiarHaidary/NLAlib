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
* `NLAlib.IsBestRankApprox.frobNorm_sub_le_add_frobNorm_truncatedSVD`,
  `NLAlib.IsBestRankApprox.frobNorm_sub_le_add_specNorm`: perturbed truncation.
* `NLAlib.nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD`: Gram matrices. The Loewner order
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
[GolubVanLoan2013, Theorem 2.4.8]; [HornJohnson2013, §7.4.9]; [HalkoMartinssonTropp2011, §2.1].
Port of `NLAlib.IsBestFrobRankApprox`, there through the squared Frobenius norm. -/
structure IsBestRankApprox (C : Matrix m n 𝕜) (k : ℕ) (Y : Matrix m n 𝕜) : Prop where
  /-- A best approximation has rank at most $k$. -/
  rank_le : Y.rank ≤ k
  /-- No matrix of rank at most $k$ is closer in the Frobenius norm. -/
  frobNorm_sub_le : ∀ B : Matrix m n 𝕜, B.rank ≤ k → frobNorm (C - Y) ≤ frobNorm (C - B)

/-- **Eckart–Young**: the truncated SVD $\llbracket \mathbf{C} \rrbracket_k$ is a best
approximation of $\mathbf{C}$ of rank at most $k$.
[GolubVanLoan2013, Theorem 2.4.8]; [HornJohnson2013, §7.4.9].
Port of `NLAlib.exists_isBestFrobRankApprox`. -/
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
  have hx := frobNorm_nonneg (C - Y)
  have hΔ := frobNorm_nonneg (C - truncatedSVD C k)
  have hquad : frobNorm (C - Y) ^ 2 ≤ frobNorm (C - truncatedSVD C k) ^ 2 +
      2 * frobNorm (truncatedSVD E (2 * k)) *
        (frobNorm (C - Y) + frobNorm (C - truncatedSVD C k)) := by
    linarith
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

end NLAlib
