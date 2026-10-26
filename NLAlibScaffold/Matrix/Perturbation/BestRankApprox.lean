/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Majorization.TraceInequalities
public import NLAlib.Matrix.Norms.Compare
public import NLAlib.Matrix.Norms.Nuclear
public import NLAlib.Matrix.Norms.Projector
public import NLAlib.Matrix.Spectral.BestRankApprox
public import NLAlib.Matrix.Spectral.LowRank
public import NLAlib.Matrix.Spectral.SVD
public import NLAlib.Matrix.Spectral.SingularValues

/-!
# Perturbed best rank-$k$ approximation, localized at the truncation level (research)

For $\mathbf{B}, \mathbf{N} \in \mathbb{R}^{m \times n}$ and any best rank-$k$ approximation
$\mathbf{Y}$ of $\mathbf{B} + \mathbf{N}$, the excess
$\|\mathbf{B} - \mathbf{Y}\|_{\mathsf{F}}^2 - \|\mathbf{B} - \llbracket\mathbf{B}\rrbracket_k
\|_{\mathsf{F}}^2$ is bounded by $k\|\mathbf{N}\|_2^2$ plus $\theta\min(k, p)\,\mu$, where
$\theta = \sigma_{k-1}(\mathbf{B})$ (indices from $0$), the window $a \le k \le b$ collects the
singular values in $[\theta/2, 2\theta]$, $p = b - k$, and $\mu$ is the spectral norm of
$\mathbf{N}$ compressed to the left and right singular subspaces of the window. The window
projectors are differences of range projectors of truncations of $\mathbf{B}$, all built from the
one chosen SVD (`NLAlib.truncatedSVD_def`), so no new definition is needed.

Research statements for the truncated generalized Nyström upper bound
(`docs/design/research/TruncatedGN-Upper.md`, D-series). Not for `main`. Real throughout.
No printed source. New (maintainer's derivation, 2026-10-26). Proofs deferred.

## Main results

* `NLAlib.sq_mul_frobNorm_mul_sub_rangeProjector_sq_le`: singular-value floor on a block (S1).
* `NLAlib.exists_singularValues_window`: the window $[\theta/2, 2\theta]$ (W1).
* `NLAlib.IsBestRankApprox.frobNorm_sub_sq_eq_add`: the excess identity (D1).
* `NLAlib.IsBestRankApprox.frobNorm_one_sub_rangeProjector_mul_sq_sub_le`: optimality (D2).
* `NLAlib.frobNorm_one_sub_mul_sq_sub_eq_add`: the weighted identity (D3).
* `NLAlib.mul_frobNorm_mul_truncatedSVD_sq_add_le`, `NLAlib.mul_frobNorm_mul_one_sub_sq_add_le`:
  the head and tail weights (D4, D5).
* `NLAlib.frobNorm_sub_mul_mul_sq_le`, `NLAlib.rank_sub_mul_mul_le`: the off-window part (D6, D7).
* `NLAlib.nuclearNorm_mul_sub_mul_le`: the trace balance on the window (D8).
* `NLAlib.IsBestRankApprox.frobNorm_sub_sq_le_add_singularValues_mul_specNorm`: large noise (D9).
* `NLAlib.IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_sq_add_window`: the localized
  perturbed truncation (D10).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-! ### Blocks of the chosen SVD -/

omit [DecidableEq m] in
/-- **A singular-value floor on a block**: for $\mathbf{B} \in \mathbb{R}^{m \times n}$,
$a \le j$, $c \ge 0$ with $c \le \sigma_i(\mathbf{B})$ for $a \le i < j$, and any
$\mathbf{W}$, writing $\mathbf{P}_i$ for the range projector of
$\llbracket\mathbf{B}\rrbracket_i$,
$$c^2\,\|\mathbf{W}(\mathbf{P}_j - \mathbf{P}_a)\|_{\mathsf{F}}^2 \le
\|\mathbf{W}(\llbracket\mathbf{B}\rrbracket_j - \llbracket\mathbf{B}\rrbracket_a)
\|_{\mathsf{F}}^2\,.$$
Both truncations come from the one chosen SVD, so their difference is the block
$\sum_{a \le i < j}\sigma_i\mathbf{u}_i\mathbf{v}_i^{\mathsf{T}}$ and
$\mathbf{P}_j - \mathbf{P}_a$ projects onto the span of its left singular vectors.
No printed source.
Proof: M, about 60 lines. Write $\mathbf{U} = $ `svdU B`, $\mathbf{V} = $ `svdV B`
(`isSVD_svdU_svdV`, `truncatedSVD_def`): $\llbracket\mathbf{B}\rrbracket_j -
\llbracket\mathbf{B}\rrbracket_a = \mathbf{U}\mathbf{D}\mathbf{V}^{\mathsf{H}}$ with
$\mathbf{D} = \operatorname{diag}(\sigma_i [a \le i < j])$. If $c = 0$ the claim is
`frobNorm_nonneg`. If $c > 0$ every $\sigma_i$, $a \le i < j$, is positive, and
$\mathbf{P}_j - \mathbf{P}_a = \mathbf{U}\mathbf{E}\mathbf{U}^{\mathsf{H}}$ with
$\mathbf{E} = \operatorname{diag}([a \le i < j])$ (both sides are the range projector of
$\mathbf{U}\mathbf{E}$: `HasOrthonormalCols.rangeProjector_eq`, `rangeProjector_inj`, and
`rangeProjector_mul_rangeProjector_of_range_le` with `range_truncatedSVD_mono`). Then
$\|\mathbf{W}\mathbf{U}\mathbf{D}\mathbf{V}^{\mathsf{H}}\|_{\mathsf{F}}^2 =
\sum_i \sigma_i^2[a \le i < j]\,\|\mathbf{W}\mathbf{u}_i\|^2$ (`frobNorm_sq_eq_sum_col`,
right orthonormal factor: `HasOrthonormalCols.frobNorm_mul_left` on the transpose) and the same
with $1$ in place of $\sigma_i^2$ for $\mathbf{W}\mathbf{U}\mathbf{E}\mathbf{U}^{\mathsf{H}}$;
compare termwise. -/
theorem sq_mul_frobNorm_mul_sub_rangeProjector_sq_le {p : Type*} [Fintype p] (B : Matrix m n ℝ)
    (W : Matrix p m ℝ) {a j : ℕ} (haj : a ≤ j) {c : ℝ} (hc : 0 ≤ c)
    (hσ : ∀ i, a ≤ i → i < j → c ≤ singularValues B i) :
    c ^ 2 * frobNorm (W * (rangeProjector (truncatedSVD B j) -
        rangeProjector (truncatedSVD B a))) ^ 2 ≤
      frobNorm (W * (truncatedSVD B j - truncatedSVD B a)) ^ 2 := by
  sorry

omit [DecidableEq m] in
/-- **The window of the truncation level**: for $\mathbf{B} \in \mathbb{R}^{m \times n}$ and
$k \ge 1$, with $\theta = \sigma_{k-1}(\mathbf{B})$, there are $a \le k \le b$ with
$2\theta \le \sigma_i(\mathbf{B})$ for $i < a$, $\sigma_a(\mathbf{B}) \le 2\theta$,
$\sigma_b(\mathbf{B}) \le \theta/2$ and
$$(b - k)\,\theta^2 \le 4\,\|\mathbf{B} - \llbracket\mathbf{B}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
No printed source.
Proof: S, about 40 lines. If $\theta = 0$ take $a = b = k$ (`singularValues_antitone`,
`singularValues_nonneg`). Otherwise $a$ is the least $i$ with $\sigma_i \le 2\theta$ (`Nat.find`;
$i = k - 1$ qualifies, so $a \le k - 1$) and $b$ the least $i$ with $\sigma_i < \theta/2$ ($i =
\min(\lvert m\rvert, \lvert n\rvert)$ qualifies by `singularValues_eq_zero_iff` and
`Matrix.rank_le_card_width`; $b \ge k$ since $\sigma_{k-1} = \theta$). For
$k \le i < b$, $\theta/2 \le \sigma_i$ by `Nat.find_min`, and
`frobNorm_sub_truncatedSVD_sq` writes the right side as $\sum_{k \le i < r}\sigma_i^2 \ge
(b - k)\theta^2/4$ (`Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.card_Ico`, $b \le r$). -/
theorem exists_singularValues_window (B : Matrix m n ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∃ a b : ℕ, a ≤ k ∧ k ≤ b ∧
      (∀ i < a, 2 * singularValues B (k - 1) ≤ singularValues B i) ∧
      singularValues B a ≤ 2 * singularValues B (k - 1) ∧
      singularValues B b ≤ singularValues B (k - 1) / 2 ∧
      ((b - k : ℕ) : ℝ) * singularValues B (k - 1) ^ 2 ≤
        4 * frobNorm (B - truncatedSVD B k) ^ 2 := by
  rcases eq_or_lt_of_le (singularValues_nonneg B (k - 1)) with hθ | hθ
  · refine ⟨k, k, le_rfl, le_rfl, ?_, ?_, ?_, ?_⟩
    · intro i _
      rw [← hθ]
      linarith [singularValues_nonneg B i]
    · have h1 := singularValues_antitone B (show k - 1 ≤ k by omega)
      linarith
    · have h1 := singularValues_antitone B (show k - 1 ≤ k by omega)
      linarith
    · simp only [Nat.sub_self, Nat.cast_zero, zero_mul]
      positivity
  · have hex1 : ∃ i, singularValues B i ≤ 2 * singularValues B (k - 1) :=
      ⟨k - 1, by linarith⟩
    have hr0 : singularValues B (min (Fintype.card m) (Fintype.card n)) = 0 :=
      (singularValues_eq_zero_iff B).mpr
        (le_min (Matrix.rank_le_card_height B) (Matrix.rank_le_card_width B))
    have hr_lt : singularValues B (min (Fintype.card m) (Fintype.card n)) <
        singularValues B (k - 1) / 2 := by
      rw [hr0]; linarith
    have hex2 : ∃ i, singularValues B i < singularValues B (k - 1) / 2 := ⟨_, hr_lt⟩
    have ha_min : ∀ i < Nat.find hex1, 2 * singularValues B (k - 1) ≤ singularValues B i :=
      fun i hi => (not_le.mp (Nat.find_min hex1 hi)).le
    have hb_min : ∀ i < Nat.find hex2, singularValues B (k - 1) / 2 ≤ singularValues B i :=
      fun i hi => not_lt.mp (Nat.find_min hex2 hi)
    have ha_k : Nat.find hex1 ≤ k - 1 :=
      Nat.find_min' hex1 (show singularValues B (k - 1) ≤ 2 * singularValues B (k - 1) by linarith)
    have hbr : Nat.find hex2 ≤ min (Fintype.card m) (Fintype.card n) := Nat.find_min' hex2 hr_lt
    have hkb : k ≤ Nat.find hex2 := by
      by_contra h
      have h1 := singularValues_antitone B (show Nat.find hex2 ≤ k - 1 by omega)
      linarith [Nat.find_spec hex2]
    have hsum : ((Nat.find hex2 - k : ℕ) : ℝ) * (singularValues B (k - 1) / 2) ^ 2 ≤
        ∑ i ∈ Finset.Ico k (min (Fintype.card m) (Fintype.card n)), singularValues B i ^ 2 := by
      have hsub : Finset.Ico k (Nat.find hex2) ⊆
          Finset.Ico k (min (Fintype.card m) (Fintype.card n)) :=
        Finset.Ico_subset_Ico_right hbr
      calc ((Nat.find hex2 - k : ℕ) : ℝ) * (singularValues B (k - 1) / 2) ^ 2
          = ∑ i ∈ Finset.Ico k (Nat.find hex2), (singularValues B (k - 1) / 2) ^ 2 := by
            simp [Finset.sum_const, Nat.card_Ico]
        _ ≤ ∑ i ∈ Finset.Ico k (Nat.find hex2), singularValues B i ^ 2 :=
            Finset.sum_le_sum fun i hi =>
              pow_le_pow_left₀ (by positivity)
                (hb_min i (Finset.mem_Ico.mp hi).2) 2
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => sq_nonneg _
    refine ⟨Nat.find hex1, Nat.find hex2, by omega, hkb, fun i hi => ha_min i hi,
      (Nat.find_spec hex1), (Nat.find_spec hex2).le, ?_⟩
    rw [frobNorm_sub_truncatedSVD_sq]
    nlinarith [hsum]

/-! ### The excess and the optimality of the perturbed truncation -/

/-- A best approximation is the projection of the target onto its own column space. -/
private theorem rangeProjector_mul_eq_of_isBestRankApprox {M Y : Matrix m n ℝ} {k : ℕ}
    (hY : IsBestRankApprox M k Y) : rangeProjector Y * M = Y := by
  have hsplit := (isStarProjection_rangeProjector Y).frobNorm_sq_eq_add (M - Y)
  have e1 : rangeProjector Y * (M - Y) = rangeProjector Y * M - Y := by
    rw [Matrix.mul_sub, rangeProjector_mul_self]
  have e2 : (1 - rangeProjector Y) * (M - Y) = M - rangeProjector Y * M := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.one_mul,
      rangeProjector_mul_self, sub_self, sub_zero]
  rw [e1, e2] at hsplit
  have hopt := pow_le_pow_left₀ (frobNorm_nonneg _) (hY.frobNorm_sub_le _
    ((Matrix.rank_mul_le_left (rangeProjector Y) M).trans
      (by rw [rank_rangeProjector]; exact hY.rank_le))) 2
  have hsq : frobNorm (rangeProjector Y * M - Y) ^ 2 = 0 :=
    le_antisymm (by linarith) (sq_nonneg _)
  exact sub_eq_zero.mp (frobNorm_eq_zero_iff.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq))

/-- **The excess identity**: for $\mathbf{B}, \mathbf{N} \in \mathbb{R}^{m \times n}$ and a best
rank-$k$ approximation $\mathbf{Y}$ of $\mathbf{B} + \mathbf{N}$, with
$\widehat{\mathbf{P}} = \mathbf{P}_{\mathbf{Y}}$,
$$\|\mathbf{B} - \mathbf{Y}\|_{\mathsf{F}}^2 =
\|(\mathbf{I} - \widehat{\mathbf{P}})\mathbf{B}\|_{\mathsf{F}}^2 +
\|\widehat{\mathbf{P}}\mathbf{N}\|_{\mathsf{F}}^2\,.$$
No printed source.
Proof: S, about 25 lines. $\mathbf{Y} = \widehat{\mathbf{P}}(\mathbf{B} + \mathbf{N})$: the
argument of the private rangeProjector_self_mul of `NLAlib/LowRank/Structural/Truncation.lean`
(copy it: `IsStarProjection.frobNorm_sq_eq_add` for $\mathbf{M} - \mathbf{Y}$, optimality
`IsBestRankApprox.frobNorm_sub_le` against $\widehat{\mathbf{P}}\mathbf{M}$, of rank at most $k$
by `Matrix.rank_mul_le_left` and `rank_rangeProjector`). Then $\mathbf{B} - \mathbf{Y} =
(\mathbf{I} - \widehat{\mathbf{P}})\mathbf{B} - \widehat{\mathbf{P}}\mathbf{N}$, and the two
terms are orthogonal (`frobNorm_sub_sq_of_frobInner_eq_zero`, `frobInner_mul_left`,
`IsStarProjection.conjTranspose_eq`, `IsStarProjection.mul_self`,
`isStarProjection_rangeProjector`). -/
theorem IsBestRankApprox.frobNorm_sub_sq_eq_add {B N Y : Matrix m n ℝ} {k : ℕ}
    (hY : IsBestRankApprox (B + N) k Y) :
    frobNorm (B - Y) ^ 2 =
      frobNorm ((1 - rangeProjector Y) * B) ^ 2 + frobNorm (rangeProjector Y * N) ^ 2 := by
  classical
  have hZ := isStarProjection_rangeProjector Y
  have hZY : rangeProjector Y * (B + N) = Y := rangeProjector_mul_eq_of_isBestRankApprox hY
  have hY1 : Y = rangeProjector Y * B + rangeProjector Y * N := by
    rw [← Matrix.mul_add, hZY]
  have hsub : B - Y = (1 - rangeProjector Y) * B - rangeProjector Y * N := by
    conv_lhs => rw [hY1]
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  have horth : frobInner ((1 - rangeProjector Y) * B) (rangeProjector Y * N) = 0 := by
    rw [frobInner_mul_left, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      hZ.conjTranspose_eq, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hZ.mul_self,
      sub_self]
    simp
  rw [hsub]
  exact frobNorm_sub_sq_of_frobInner_eq_zero horth

omit [DecidableEq m] in
/-- A best approximation is the projection of the target onto its own column space. -/
private theorem rangeProjector_self_mul' {M Y : Matrix m n ℝ} {k : ℕ}
    (hY : IsBestRankApprox M k Y) : rangeProjector Y * M = Y := by
  classical
  have hsplit := (isStarProjection_rangeProjector Y).frobNorm_sq_eq_add (M - Y)
  have e1 : rangeProjector Y * (M - Y) = rangeProjector Y * M - Y := by
    rw [Matrix.mul_sub, rangeProjector_mul_self]
  have e2 : (1 - rangeProjector Y) * (M - Y) = M - rangeProjector Y * M := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.one_mul,
      rangeProjector_mul_self, sub_self, sub_zero]
  rw [e1, e2] at hsplit
  have hopt := pow_le_pow_left₀ (frobNorm_nonneg _) (hY.frobNorm_sub_le _
    ((Matrix.rank_mul_le_left (rangeProjector Y) M).trans
      (by rw [rank_rangeProjector]; exact hY.rank_le))) 2
  have hsq : frobNorm (rangeProjector Y * M - Y) ^ 2 = 0 :=
    le_antisymm (by linarith) (sq_nonneg _)
  exact sub_eq_zero.mp (frobNorm_eq_zero_iff.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq))

/-- Pythagoras for the complement of a star projection, in the form `(1 - Q) * A`. -/
private theorem frobNorm_one_sub_mul_sq' {Q : Matrix m m ℝ} (hQ : IsStarProjection Q)
    (A : Matrix m n ℝ) :
    frobNorm ((1 - Q) * A) ^ 2 = frobNorm A ^ 2 - frobNorm (Q * A) ^ 2 := by
  have h := hQ.frobNorm_sq_eq_add A
  linarith

omit [DecidableEq m] in
/-- Expansion of `‖Q (B + N)‖²` for a star projection `Q`. -/
private theorem frobNorm_mul_add_sq' {Q : Matrix m m ℝ} (hQ : IsStarProjection Q)
    (B N : Matrix m n ℝ) :
    frobNorm (Q * (B + N)) ^ 2 =
      frobNorm (Q * B) ^ 2 + 2 * frobInner (Q * B) N + frobNorm (Q * N) ^ 2 := by
  classical
  have hcross : frobInner (Q * B) (Q * N) = frobInner (Q * B) N := by
    rw [frobInner_mul_left, hQ.conjTranspose_eq, ← Matrix.mul_assoc, hQ.mul_self,
      frobInner_mul_left, hQ.conjTranspose_eq]
  rw [Matrix.mul_add, frobNorm_add_sq, hcross]

/-- **The optimality of the perturbed truncation**: for $\mathbf{B}, \mathbf{N} \in
\mathbb{R}^{m \times n}$ and a best rank-$k$ approximation $\mathbf{Y}$ of
$\mathbf{B} + \mathbf{N}$, with $\widehat{\mathbf{P}} = \mathbf{P}_{\mathbf{Y}}$ and
$\mathbf{P}$ the range projector of $\llbracket\mathbf{B}\rrbracket_k$,
$$\|(\mathbf{I} - \widehat{\mathbf{P}})\mathbf{B}\|_{\mathsf{F}}^2 -
\|(\mathbf{I} - \mathbf{P})\mathbf{B}\|_{\mathsf{F}}^2 \le
2\langle(\widehat{\mathbf{P}} - \mathbf{P})\mathbf{B}, \mathbf{N}\rangle_{\mathsf{F}} +
\|\widehat{\mathbf{P}}\mathbf{N}\|_{\mathsf{F}}^2 - \|\mathbf{P}\mathbf{N}\|_{\mathsf{F}}^2\,.$$
No printed source.
Proof: S, about 35 lines. $\mathbf{Y} = \widehat{\mathbf{P}}(\mathbf{B} + \mathbf{N})$ (as in
`IsBestRankApprox.frobNorm_sub_sq_eq_add`). Optimality against
$\mathbf{P}(\mathbf{B} + \mathbf{N})$ (rank at most $k$: `Matrix.rank_mul_le_left`,
`rank_rangeProjector`, `rank_truncatedSVD_le`) via `IsBestRankApprox.frobNorm_sub_le`, squared;
both errors are projection residuals, so by `IsStarProjection.frobNorm_sq_eq_add` it reads
$\|\mathbf{P}(\mathbf{B} + \mathbf{N})\|_{\mathsf{F}}^2 \le
\|\widehat{\mathbf{P}}(\mathbf{B} + \mathbf{N})\|_{\mathsf{F}}^2$. Expand both with
`frobNorm_add_sq` and $\langle\mathbf{Q}\mathbf{B}, \mathbf{Q}\mathbf{N}\rangle =
\langle\mathbf{Q}\mathbf{B}, \mathbf{N}\rangle$ for a star projection $\mathbf{Q}$
(`frobInner_mul_left`, `IsStarProjection.mul_self`); also
$\|(\mathbf{I} - \mathbf{Q})\mathbf{B}\|^2 = \|\mathbf{B}\|^2 - \|\mathbf{Q}\mathbf{B}\|^2$;
`frobInner_sub_left`; `linarith`. -/
theorem IsBestRankApprox.frobNorm_one_sub_rangeProjector_mul_sq_sub_le {B N Y : Matrix m n ℝ}
    {k : ℕ} (hY : IsBestRankApprox (B + N) k Y) :
    frobNorm ((1 - rangeProjector Y) * B) ^ 2 -
        frobNorm ((1 - rangeProjector (truncatedSVD B k)) * B) ^ 2 ≤
      2 * frobInner ((rangeProjector Y - rangeProjector (truncatedSVD B k)) * B) N +
        frobNorm (rangeProjector Y * N) ^ 2 -
        frobNorm (rangeProjector (truncatedSVD B k) * N) ^ 2 := by
  have hZ := isStarProjection_rangeProjector Y
  have hP := isStarProjection_rangeProjector (truncatedSVD B k)
  have hYM : (B + N) - Y = (1 - rangeProjector Y) * (B + N) := by
    rw [Matrix.sub_mul, Matrix.one_mul, rangeProjector_self_mul' hY]
  have hrank : (rangeProjector (truncatedSVD B k) * (B + N)).rank ≤ k :=
    (Matrix.rank_mul_le_left _ _).trans (by
      rw [rank_rangeProjector]; exact rank_truncatedSVD_le B k)
  have hopt := pow_le_pow_left₀ (frobNorm_nonneg _)
    (hY.frobNorm_sub_le _ hrank) 2
  have hPM : (B + N) - rangeProjector (truncatedSVD B k) * (B + N) =
      (1 - rangeProjector (truncatedSVD B k)) * (B + N) := by
    rw [Matrix.sub_mul, Matrix.one_mul]
  rw [hYM, hPM, frobNorm_one_sub_mul_sq' hZ, frobNorm_one_sub_mul_sq' hP] at hopt
  rw [frobNorm_one_sub_mul_sq' hZ, frobNorm_one_sub_mul_sq' hP, Matrix.sub_mul,
    frobInner_sub_left]
  rw [frobNorm_mul_add_sq' hZ, frobNorm_mul_add_sq' hP] at hopt
  linarith

/-! ### The weighted identity and its two weights -/

/-- Right Pythagoras for a star projection `Q`: `‖X‖² = ‖X Q‖² + ‖X (1 - Q)‖²`. -/
private lemma frobNorm_sq_eq_add_mul_right_proj {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq q] {Q : Matrix q q ℝ} (hQ : IsStarProjection Q) (X : Matrix p q ℝ) :
    frobNorm X ^ 2 = frobNorm (X * Q) ^ 2 + frobNorm (X * (1 - Q)) ^ 2 := by
  have h := IsStarProjection.frobNorm_sq_eq_add hQ Xᴴ
  have e1 : frobNorm (Q * Xᴴ) = frobNorm (X * Q) := by
    rw [← frobNorm_conjTranspose (Q * Xᴴ), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hQ.conjTranspose_eq]
  have e2 : frobNorm ((1 - Q) * Xᴴ) = frobNorm (X * (1 - Q)) := by
    rw [← frobNorm_conjTranspose ((1 - Q) * Xᴴ), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      hQ.conjTranspose_eq]
  rw [frobNorm_conjTranspose, e1, e2] at h
  exact h

/-- **The weighted identity**: for $\mathbf{B} \in \mathbb{R}^{m \times n}$, an orthogonal
projector $\mathbf{Z}$, any $k$ and any real $\theta$, with $\mathbf{P}$ the range projector of
$\llbracket\mathbf{B}\rrbracket_k$ and $\mathbf{B}_k = \llbracket\mathbf{B}\rrbracket_k$,
$$\|(\mathbf{I} - \mathbf{Z})\mathbf{B}\|_{\mathsf{F}}^2 -
\|(\mathbf{I} - \mathbf{P})\mathbf{B}\|_{\mathsf{F}}^2 =
\bigl(\|(\mathbf{I} - \mathbf{Z})\mathbf{B}_k\|_{\mathsf{F}}^2 -
\theta^2\|(\mathbf{I} - \mathbf{Z})\mathbf{P}\|_{\mathsf{F}}^2\bigr) +
\bigl(\theta^2\|\mathbf{Z}(\mathbf{I} - \mathbf{P})\|_{\mathsf{F}}^2 -
\|\mathbf{Z}(\mathbf{B} - \mathbf{B}_k)\|_{\mathsf{F}}^2\bigr) +
\theta^2\bigl(\|\mathbf{P}\|_{\mathsf{F}}^2 - \|\mathbf{Z}\|_{\mathsf{F}}^2\bigr)\,.$$
At $\theta = \sigma_{k-1}(\mathbf{B})$ the two brackets are nonnegative (head and tail weights,
`NLAlib.mul_frobNorm_mul_truncatedSVD_sq_add_le`, `NLAlib.mul_frobNorm_mul_one_sub_sq_add_le`).
No printed source.
Proof: S, about 40 lines. Pure algebra. Both sides equal
$\|\mathbf{B}_k\|_{\mathsf{F}}^2 - \|\mathbf{Z}\mathbf{B}\|_{\mathsf{F}}^2$: the left by
`IsStarProjection.frobNorm_sq_eq_add` twice and $\mathbf{P}\mathbf{B} = \mathbf{B}_k$
(`rangeProjector_truncatedSVD_mul`); on the right, expand each squared norm as a trace
(`frobNorm_sq_eq_re_trace` or `frobInner_self` with `frobInner_mul_left`), use
$\mathbf{Z}^2 = \mathbf{Z}$, $\mathbf{P}^2 = \mathbf{P}$, $\mathbf{P}\mathbf{B}_k = \mathbf{B}_k$,
$\mathbf{P}(\mathbf{B} - \mathbf{B}_k) = \mathbf{0}$ and
$\mathbf{B}_k(\mathbf{B} - \mathbf{B}_k)^{\mathsf{H}} = \mathbf{0}$
(`truncatedSVD_mul_conjTranspose_sub`), so that
$\mathbf{B}\mathbf{B}^{\mathsf{H}} = \mathbf{B}_k\mathbf{B}_k^{\mathsf{H}} +
(\mathbf{B} - \mathbf{B}_k)(\mathbf{B} - \mathbf{B}_k)^{\mathsf{H}}$; the $\theta^2$ terms cancel
($\operatorname{tr}((\mathbf{I} - \mathbf{Z})\mathbf{P}) + \operatorname{tr}(\mathbf{Z}(\mathbf{I}
- \mathbf{P})) + \operatorname{tr}\mathbf{P} - \operatorname{tr}\mathbf{Z} = 2\operatorname{tr}
\mathbf{P} - 2\operatorname{tr}(\mathbf{Z}\mathbf{P})$ minus the same, i.e. they sum to $0$). -/
theorem frobNorm_one_sub_mul_sq_sub_eq_add (B : Matrix m n ℝ) (k : ℕ) {Z : Matrix m m ℝ}
    (hZ : IsStarProjection Z) (θ : ℝ) :
    frobNorm ((1 - Z) * B) ^ 2 - frobNorm ((1 - rangeProjector (truncatedSVD B k)) * B) ^ 2 =
      (frobNorm ((1 - Z) * truncatedSVD B k) ^ 2 -
          θ ^ 2 * frobNorm ((1 - Z) * rangeProjector (truncatedSVD B k)) ^ 2) +
        (θ ^ 2 * frobNorm (Z * (1 - rangeProjector (truncatedSVD B k))) ^ 2 -
          frobNorm (Z * (B - truncatedSVD B k)) ^ 2) +
        θ ^ 2 * (frobNorm (rangeProjector (truncatedSVD B k)) ^ 2 - frobNorm Z ^ 2) := by
  classical
  have hPB : rangeProjector (truncatedSVD B k) * B = truncatedSVD B k :=
    rangeProjector_truncatedSVD_mul B k
  have hBP : B * rangeProjector (truncatedSVD B k)ᴴ = truncatedSVD B k :=
    mul_rangeProjector_conjTranspose_truncatedSVD B k
  have hL : frobNorm ((1 - Z) * B) ^ 2 -
      frobNorm ((1 - rangeProjector (truncatedSVD B k)) * B) ^ 2 =
      frobNorm (rangeProjector (truncatedSVD B k) * B) ^ 2 - frobNorm (Z * B) ^ 2 := by
    linarith [IsStarProjection.frobNorm_sq_eq_add hZ B,
      IsStarProjection.frobNorm_sq_eq_add (isStarProjection_rangeProjector (truncatedSVD B k)) B]
  have hR1 : frobNorm ((1 - Z) * truncatedSVD B k) ^ 2 =
      frobNorm (truncatedSVD B k) ^ 2 - frobNorm (Z * truncatedSVD B k) ^ 2 := by
    linarith [IsStarProjection.frobNorm_sq_eq_add hZ (truncatedSVD B k)]
  have hR2 : frobNorm ((1 - Z) * rangeProjector (truncatedSVD B k)) ^ 2 =
      frobNorm (rangeProjector (truncatedSVD B k)) ^ 2 -
        frobNorm (Z * rangeProjector (truncatedSVD B k)) ^ 2 := by
    linarith [IsStarProjection.frobNorm_sq_eq_add hZ (rangeProjector (truncatedSVD B k))]
  have hR3 : frobNorm (Z * (1 - rangeProjector (truncatedSVD B k))) ^ 2 =
      frobNorm Z ^ 2 - frobNorm (Z * rangeProjector (truncatedSVD B k)) ^ 2 := by
    linarith [frobNorm_sq_eq_add_mul_right_proj
      (isStarProjection_rangeProjector (truncatedSVD B k)) Z]
  have hk1 : Z * B * (1 - rangeProjector (truncatedSVD B k)ᴴ) = Z * (B - truncatedSVD B k) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hBP, Matrix.mul_sub]
  have hk2 : Z * B * rangeProjector (truncatedSVD B k)ᴴ = Z * truncatedSVD B k := by
    rw [Matrix.mul_assoc, hBP]
  have hR4 : frobNorm (Z * (B - truncatedSVD B k)) ^ 2 =
      frobNorm (Z * B) ^ 2 - frobNorm (Z * truncatedSVD B k) ^ 2 := by
    have e := frobNorm_sq_eq_add_mul_right_proj (isStarProjection_rangeProjector
      (truncatedSVD B k)ᴴ) (Z * B)
    rw [hk1, hk2] at e
    linarith
  rw [hL, hPB, hR1, hR2, hR3, hR4]
  ring

omit [DecidableEq m] in
/-- **The head weight**: for $\mathbf{B} \in \mathbb{R}^{m \times n}$, $1 \le k$,
$\theta = \sigma_{k-1}(\mathbf{B})$, $a \le k$ with $2\theta \le \sigma_i(\mathbf{B})$ for
$i < a$, and any $\mathbf{W}$, writing $\mathbf{B}_i = \llbracket\mathbf{B}\rrbracket_i$ and
$\mathbf{P}_i$ for its range projector,
$$\tfrac38\|\mathbf{W}\mathbf{B}_a\|_{\mathsf{F}}^2 +
\tfrac32\theta^2\|\mathbf{W}\mathbf{P}_a\|_{\mathsf{F}}^2 \le
\|\mathbf{W}\mathbf{B}_k\|_{\mathsf{F}}^2 - \theta^2\|\mathbf{W}\mathbf{P}_k\|_{\mathsf{F}}^2\,.$$
No printed source.
Proof: S, about 40 lines. Split at $a$: $\|\mathbf{W}\mathbf{B}_k\|^2 =
\|\mathbf{W}\mathbf{B}_a\|^2 + \|\mathbf{W}(\mathbf{B}_k - \mathbf{B}_a)\|^2$ (orthogonal row
spaces: $\mathbf{B}_a = \mathbf{B}\mathbf{P}'_a$ and $\mathbf{B}_k - \mathbf{B}_a =
\mathbf{B}(\mathbf{P}'_k - \mathbf{P}'_a)$ with $\mathbf{P}'_i$ the range projector of
$\mathbf{B}_i^{\mathsf{H}}$, `mul_rangeProjector_conjTranspose_truncatedSVD`,
`rangeProjector_mul_rangeProjector_of_range_le`, `range_truncatedSVD_mono`;
`frobNorm_add_sq_of_frobInner_eq_zero`) and likewise $\|\mathbf{W}\mathbf{P}_k\|^2 =
\|\mathbf{W}\mathbf{P}_a\|^2 + \|\mathbf{W}(\mathbf{P}_k - \mathbf{P}_a)\|^2$. Then
`NLAlib.sq_mul_frobNorm_mul_sub_rangeProjector_sq_le` on $[a, k)$ with $c = \theta$
($\sigma_i \ge \sigma_{k-1}$ for $i \le k - 1$, `singularValues_antitone`) and on $[0, a)$ with
$c = 2\theta$ ($\mathbf{B}_0 = \mathbf{0}$, `truncatedSVD_zero`, `rangeProjector_zero`), so
$\|\mathbf{W}\mathbf{B}_a\|^2 \ge 4\theta^2\|\mathbf{W}\mathbf{P}_a\|^2$; `nlinarith`. -/
theorem mul_frobNorm_mul_truncatedSVD_sq_add_le (B : Matrix m n ℝ) {k a : ℕ} (hk : 1 ≤ k)
    (hak : a ≤ k) (ha : ∀ i < a, 2 * singularValues B (k - 1) ≤ singularValues B i)
    (W : Matrix m m ℝ) :
    3 / 8 * frobNorm (W * truncatedSVD B a) ^ 2 +
        3 / 2 * singularValues B (k - 1) ^ 2 *
          frobNorm (W * rangeProjector (truncatedSVD B a)) ^ 2 ≤
      frobNorm (W * truncatedSVD B k) ^ 2 -
        singularValues B (k - 1) ^ 2 * frobNorm (W * rangeProjector (truncatedSVD B k)) ^ 2 := by
  sorry

/-- **The tail weight**: for $\mathbf{B} \in \mathbb{R}^{m \times n}$, $1 \le k$,
$\theta = \sigma_{k-1}(\mathbf{B})$, $b \ge k$ with $\sigma_b(\mathbf{B}) \le \theta/2$, and any
$\mathbf{W}$, writing $\mathbf{B}_i = \llbracket\mathbf{B}\rrbracket_i$ and $\mathbf{P}_i$ for
its range projector,
$$\tfrac38\theta^2\|\mathbf{W}(\mathbf{I} - \mathbf{P}_b)\|_{\mathsf{F}}^2 +
\tfrac32\|\mathbf{W}(\mathbf{B} - \mathbf{B}_b)\|_{\mathsf{F}}^2 \le
\theta^2\|\mathbf{W}(\mathbf{I} - \mathbf{P}_k)\|_{\mathsf{F}}^2 -
\|\mathbf{W}(\mathbf{B} - \mathbf{B}_k)\|_{\mathsf{F}}^2\,.$$
No printed source.
Proof: S, about 40 lines. Split at $b$: $\mathbf{I} - \mathbf{P}_k = (\mathbf{P}_b -
\mathbf{P}_k) + (\mathbf{I} - \mathbf{P}_b)$ (orthogonal projectors,
`rangeProjector_mul_rangeProjector_of_range_le`, `range_truncatedSVD_mono`) and
$\mathbf{B} - \mathbf{B}_k = (\mathbf{B}_b - \mathbf{B}_k) + (\mathbf{B} - \mathbf{B}_b)$ with
orthogonal row spaces (`mul_rangeProjector_conjTranspose_truncatedSVD`). Upper bounds:
$\mathbf{B}_b - \mathbf{B}_k = (\mathbf{P}_b - \mathbf{P}_k)(\mathbf{B} - \mathbf{B}_k)$ and
$\mathbf{B} - \mathbf{B}_b = (\mathbf{I} - \mathbf{P}_b)(\mathbf{B} - \mathbf{B}_b)$
(`rangeProjector_truncatedSVD_mul`), so by `frobNorm_mul_le_frobNorm_mul_specNorm` and
`specNorm_sub_truncatedSVD` the pieces are at most $\sigma_k\|\mathbf{W}(\mathbf{P}_b -
\mathbf{P}_k)\|_{\mathsf{F}}$ ($\sigma_k \le \theta$, `singularValues_antitone`) and
$\sigma_b\|\mathbf{W}(\mathbf{I} - \mathbf{P}_b)\|_{\mathsf{F}} \le
\tfrac{\theta}{2}\|\mathbf{W}(\mathbf{I} - \mathbf{P}_b)\|_{\mathsf{F}}$; `nlinarith`. -/
theorem mul_frobNorm_mul_one_sub_sq_add_le (B : Matrix m n ℝ) {k b : ℕ} (hk : 1 ≤ k)
    (hkb : k ≤ b) (hb : singularValues B b ≤ singularValues B (k - 1) / 2)
    (W : Matrix m m ℝ) :
    3 / 8 * singularValues B (k - 1) ^ 2 *
          frobNorm (W * (1 - rangeProjector (truncatedSVD B b))) ^ 2 +
        3 / 2 * frobNorm (W * (B - truncatedSVD B b)) ^ 2 ≤
      singularValues B (k - 1) ^ 2 * frobNorm (W * (1 - rangeProjector (truncatedSVD B k))) ^ 2 -
        frobNorm (W * (B - truncatedSVD B k)) ^ 2 := by
  sorry

/-! ### The off-window part and the trace balance -/

/-- **The off-window part of the subspace error is controlled by the misalignment**: for
$\mathbf{B} \in \mathbb{R}^{m \times n}$, $1 \le k$, $\theta = \sigma_{k-1}(\mathbf{B})$, a window
$a \le k \le b$ with $2\theta \le \sigma_i(\mathbf{B})$ for $i < a$, $\sigma_a(\mathbf{B}) \le
2\theta$ and $\sigma_b(\mathbf{B}) \le \theta/2$, and an orthogonal projector $\mathbf{Z}$ of
rank at most $k$, with $\mathbf{P}_i$, $\mathbf{P}'_i$ the range projectors of
$\llbracket\mathbf{B}\rrbracket_i$ and of its transpose, $\mathbf{L} = \mathbf{P}_b -
\mathbf{P}_a$, $\mathbf{L}' = \mathbf{P}'_b - \mathbf{P}'_a$ and
$\mathbf{\Delta} = \mathbf{Z} - \mathbf{P}_k$,
$$\|\mathbf{\Delta}\mathbf{B} - \mathbf{L}\mathbf{\Delta}\mathbf{B}\mathbf{L}'\|_{\mathsf{F}}^2
\le 15\bigl(\|(\mathbf{I} - \mathbf{Z})\mathbf{B}\|_{\mathsf{F}}^2 -
\|(\mathbf{I} - \mathbf{P}_k)\mathbf{B}\|_{\mathsf{F}}^2\bigr)\,.$$
No printed source.
Proof: M, about 70 lines. With $\mathbf{B}_i = \llbracket\mathbf{B}\rrbracket_i$:
$\mathbf{B}\mathbf{L}' = \mathbf{B}_b - \mathbf{B}_a$
(`mul_rangeProjector_conjTranspose_truncatedSVD`), and the left side is
$\mathbf{\Delta}\mathbf{B}_a + \mathbf{\Delta}(\mathbf{B} - \mathbf{B}_b) +
(\mathbf{I} - \mathbf{L})\mathbf{\Delta}(\mathbf{B}_b - \mathbf{B}_a)$, three matrices with
orthogonal row spaces. Since $a \le k \le b$: $\mathbf{\Delta}\mathbf{B}_a =
-(\mathbf{I} - \mathbf{Z})\mathbf{B}_a$, $\mathbf{\Delta}(\mathbf{B} - \mathbf{B}_b) =
\mathbf{Z}(\mathbf{B} - \mathbf{B}_b)$ and $(\mathbf{I} - \mathbf{L})\mathbf{\Delta}(\mathbf{B}_b
- \mathbf{B}_a) = (\mathbf{I} - \mathbf{L})\mathbf{Z}\mathbf{L}(\mathbf{B}_b - \mathbf{B}_a)$,
the last of Frobenius norm at most $2\theta\,\|(\mathbf{I} - \mathbf{L})\mathbf{Z}\mathbf{L}
\|_{\mathsf{F}}$ ($\|\mathbf{B}_b - \mathbf{B}_a\|_2 = \|\mathbf{L}(\mathbf{B} - \mathbf{B}_a)
\|_2 \le \sigma_a \le 2\theta$, `specNorm_sub_truncatedSVD`,
`IsStarProjection.specNorm_mul_le`), and $\|(\mathbf{I} - \mathbf{L})\mathbf{Z}\mathbf{L}
\|_{\mathsf{F}}^2 \le \|(\mathbf{I} - \mathbf{Z})\mathbf{P}_a\|_{\mathsf{F}}^2 +
\|\mathbf{Z}(\mathbf{I} - \mathbf{P}_b)\|_{\mathsf{F}}^2$ ($\mathbf{I} - \mathbf{L} =
\mathbf{P}_a + (\mathbf{I} - \mathbf{P}_b)$, $\mathbf{P}_a\mathbf{Z}\mathbf{L} =
-\mathbf{P}_a(\mathbf{I} - \mathbf{Z})\mathbf{L}$, `IsStarProjection.frobNorm_mul_le`,
`frobNorm_conjTranspose`). Then `NLAlib.frobNorm_one_sub_mul_sq_sub_eq_add` at
$\theta$, whose last term is nonnegative ($\|\mathbf{P}_k\|_{\mathsf{F}}^2 = k \ge
\operatorname{rank}\mathbf{Z} = \|\mathbf{Z}\|_{\mathsf{F}}^2$ when $\theta > 0$,
`IsStarProjection.frobNorm_sq_eq_rank`, `frobNorm_rangeProjector_sq`, `rank_truncatedSVD`,
`singularValues_pos_iff`; zero when $\theta = 0$), with
`NLAlib.mul_frobNorm_mul_truncatedSVD_sq_add_le` at $\mathbf{W} = \mathbf{I} - \mathbf{Z}$ and
`NLAlib.mul_frobNorm_mul_one_sub_sq_add_le` at $\mathbf{W} = \mathbf{Z}$: the left side is at
most $\tfrac83$ head $+ \tfrac{17}{3}$ tail $\le 6\,(\ldots)$. Alternatively
(research note OP6, Lemma 3.4(b)): the triangle inequality on the two pieces
$\mathbf{B}(\mathbf{I} - \mathbf{L}')\ldots$ gives $15D$. -/
theorem frobNorm_sub_mul_mul_sq_le (B : Matrix m n ℝ) {k a b : ℕ} (hk : 1 ≤ k) (hak : a ≤ k)
    (hkb : k ≤ b) (ha : ∀ i < a, 2 * singularValues B (k - 1) ≤ singularValues B i)
    (ha₂ : singularValues B a ≤ 2 * singularValues B (k - 1))
    (hb : singularValues B b ≤ singularValues B (k - 1) / 2) {Z : Matrix m m ℝ}
    (hZ : IsStarProjection Z) (hZk : Z.rank ≤ k) :
    frobNorm ((Z - rangeProjector (truncatedSVD B k)) * B -
        (rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a)) *
          (Z - rangeProjector (truncatedSVD B k)) * B *
          (rangeProjector (truncatedSVD B b)ᴴ - rangeProjector (truncatedSVD B a)ᴴ)) ^ 2 ≤
      15 * (frobNorm ((1 - Z) * B) ^ 2 -
        frobNorm ((1 - rangeProjector (truncatedSVD B k)) * B) ^ 2) := by
  sorry

omit [DecidableEq m] in
/-- The off-window part has rank at most $4k$: for $\mathbf{B} \in \mathbb{R}^{m \times n}$,
any $\mathbf{Z}$ of rank at most $k$, any $a, b$ and any
$\mathbf{L}$, $\mathbf{L}'$, with $\mathbf{\Delta} = \mathbf{Z} - \mathbf{P}_k$
($\mathbf{P}_k$ the range projector of $\llbracket\mathbf{B}\rrbracket_k$),
$$\operatorname{rank}(\mathbf{\Delta}\mathbf{B} - \mathbf{L}\mathbf{\Delta}\mathbf{B}\mathbf{L}')
\le 4k\,.$$
No printed source.
Proof: S, about 15 lines. `Matrix.rank_sub_le`; each term has rank at most
$\operatorname{rank}\mathbf{\Delta} \le \operatorname{rank}\mathbf{Z} +
\operatorname{rank}\mathbf{P}_k \le 2k$ (`Matrix.rank_mul_le_left`, `Matrix.rank_mul_le_right`,
`Matrix.rank_sub_le`, `rank_rangeProjector`, `rank_truncatedSVD_le`); `omega`. -/
theorem rank_sub_mul_mul_le (B : Matrix m n ℝ) (k : ℕ) {Z : Matrix m m ℝ} (hZk : Z.rank ≤ k)
    (L : Matrix m m ℝ) (L' : Matrix n n ℝ) :
    ((Z - rangeProjector (truncatedSVD B k)) * B -
        L * (Z - rangeProjector (truncatedSVD B k)) * B * L').rank ≤ 4 * k := by
  sorry

/-- **The trace balance on the window**: for $\mathbf{B} \in \mathbb{R}^{m \times n}$, $1 \le k$,
$\theta = \sigma_{k-1}(\mathbf{B}) > 0$, $a \le k \le b$ with $\sigma_b(\mathbf{B}) \le
\theta/2$, and an orthogonal projector $\mathbf{Z}$ of rank at most $k$, with $\mathbf{P}_i$ the
range projector of $\llbracket\mathbf{B}\rrbracket_i$, $\mathbf{L} = \mathbf{P}_b -
\mathbf{P}_a$ and $D = \|(\mathbf{I} - \mathbf{Z})\mathbf{B}\|_{\mathsf{F}}^2 -
\|(\mathbf{I} - \mathbf{P}_k)\mathbf{B}\|_{\mathsf{F}}^2$,
$$\|\mathbf{L}(\mathbf{Z} - \mathbf{P}_k)\mathbf{L}\|_* \le 4\min(k, b - k) +
6\,\frac{D}{\theta^2}\,.$$
No printed source.
Proof: M, about 80 lines. Write $\mathbf{L}_a = \mathbf{P}_k - \mathbf{P}_a$ (rank $k - a$) and
$\mathbf{L}_b = \mathbf{P}_b - \mathbf{P}_k$ (rank at most $b - k$: `rank_truncatedSVD`, and
$\operatorname{rank}\mathbf{P}_k = k$ since $\sigma_{k-1} > 0$, `singularValues_pos_iff`); they
are orthogonal projectors with $\mathbf{L} = \mathbf{L}_a + \mathbf{L}_b$ and
$\mathbf{L}\mathbf{P}_k\mathbf{L} = \mathbf{L}_a$. Bound 1:
$\|\mathbf{L}\mathbf{Z}\mathbf{L}\|_* + \|\mathbf{L}_a\|_* \le k + k$ (`nuclearNorm_add_le`,
`Matrix.PosSemidef.nuclearNorm_eq_re_trace`, $\operatorname{tr}(\mathbf{L}\mathbf{Z}\mathbf{L}) =
\|\mathbf{Z}\mathbf{L}\|_{\mathsf{F}}^2 \le \|\mathbf{Z}\|_{\mathsf{F}}^2$,
`IsStarProjection.frobNorm_sq_eq_rank`). Bound 2: split
$\mathbf{L}\mathbf{Z}\mathbf{L} - \mathbf{L}_a$ into the four blocks; with
$\alpha = \|(\mathbf{I} - \mathbf{Z})\mathbf{L}_a\|_{\mathsf{F}}^2$ the diagonal blocks have
nuclear norms $\alpha$ and $\|\mathbf{Z}\mathbf{L}_b\|_{\mathsf{F}}^2 \le b - k$, the off-diagonal
ones at most $\sqrt{\alpha(b - k)}$ each (`nuclearNorm_mul_le_frobNorm_mul_frobNorm`,
$\mathbf{L}_a\mathbf{Z}\mathbf{L}_b = -\mathbf{L}_a(\mathbf{I} - \mathbf{Z})\mathbf{L}_b$), so at
most $2\alpha + 2(b - k)$. Balance: $\|\mathbf{Z}\|_{\mathsf{F}}^2 = \|\mathbf{Z}\mathbf{P}_a\|^2 +
\|\mathbf{Z}\mathbf{L}_a\|^2 + \|\mathbf{Z}\mathbf{L}_b\|^2 + \|\mathbf{Z}(\mathbf{I} -
\mathbf{P}_b)\|^2$ gives $\alpha \le (k - \operatorname{rank}\mathbf{Z}) + (b - k) +
\|\mathbf{Z}(\mathbf{I} - \mathbf{P}_b)\|_{\mathsf{F}}^2$, and
`NLAlib.frobNorm_one_sub_mul_sq_sub_eq_add` with the head weight
`NLAlib.mul_frobNorm_mul_truncatedSVD_sq_add_le` at $a = 0$ (nonnegative) and the tail weight
`NLAlib.mul_frobNorm_mul_one_sub_sq_add_le` gives $(k - \operatorname{rank}\mathbf{Z}) +
\tfrac38\|\mathbf{Z}(\mathbf{I} - \mathbf{P}_b)\|_{\mathsf{F}}^2 \le D/\theta^2$, so bound 2 is
at most $4(b - k) + \tfrac{16}{3}D/\theta^2$. Take the minimum of the two bounds (research note
OP6, Lemma 3.5, proves the sharper $2\min(k, q) + \tfrac43 D/\theta^2$ through Weyl's
inequalities). -/
theorem nuclearNorm_mul_sub_mul_le (B : Matrix m n ℝ) {k a b : ℕ} (hk : 1 ≤ k) (hak : a ≤ k)
    (hkb : k ≤ b) (hθ : 0 < singularValues B (k - 1))
    (hb : singularValues B b ≤ singularValues B (k - 1) / 2) {Z : Matrix m m ℝ}
    (hZ : IsStarProjection Z) (hZk : Z.rank ≤ k) :
    nuclearNorm ((rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a)) *
        (Z - rangeProjector (truncatedSVD B k)) *
        (rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a))) ≤
      4 * ((min k (b - k) : ℕ) : ℝ) +
        6 * ((frobNorm ((1 - Z) * B) ^ 2 -
          frobNorm ((1 - rangeProjector (truncatedSVD B k)) * B) ^ 2) /
            singularValues B (k - 1) ^ 2) := by
  sorry

/-! ### The localized perturbed truncation -/

omit [DecidableEq m] in
/-- **Perturbed truncation, large-noise form**: for $\mathbf{B}, \mathbf{N} \in
\mathbb{R}^{m \times n}$ and a best rank-$k$ approximation $\mathbf{Y}$ of
$\mathbf{B} + \mathbf{N}$,
$$\|\mathbf{B} - \mathbf{Y}\|_{\mathsf{F}}^2 \le
\|\mathbf{B} - \llbracket\mathbf{B}\rrbracket_k\|_{\mathsf{F}}^2 +
4k\,\sigma_k(\mathbf{B})\,\|\mathbf{N}\|_2 + 12k\,\|\mathbf{N}\|_2^2\,.$$
No printed source; the core form of
`NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm_mul_frobNorm`.
Proof: S, about 100 lines, copied. The private lemma
IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_mul_frobNorm of
`NLAlib/LowRank/Structural/Truncation.lean` proves the bound with
$4\sqrt k\,\|\mathbf{N}\|_2\,\gamma_k$, $\gamma_k = \|\llbracket\mathbf{B} -
\llbracket\mathbf{B}\rrbracket_k\rrbracket_k\|_{\mathsf{F}}$; copy it and its private helpers
(the scalar step and the optimality step, each a few lines; they use only
`frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le`,
`frobInner_le_frobNorm_mul_frobNorm_truncatedSVD_of_rank_le`, `frobNorm_sq_le_rank_mul_specNorm_sq`,
`mul_rangeProjector_conjTranspose_truncatedSVD`, `frobInner_truncatedSVD_sub` and projector
algebra) as private lemmas here. Then $\gamma_k \le \sqrt k\,\sigma_k(\mathbf{B})$:
`frobNorm_le_sqrt_rank_mul_specNorm`, `rank_truncatedSVD_le`, the bound
$\|\llbracket\mathbf{M}\rrbracket_k\|_2 \le \|\mathbf{M}\|_2$ (`singularValues_truncatedSVD`,
`singularValues_zero_eq_specNorm`) and `specNorm_sub_truncatedSVD`. -/
theorem IsBestRankApprox.frobNorm_sub_sq_le_add_singularValues_mul_specNorm
    {B N Y : Matrix m n ℝ} {k : ℕ} (hY : IsBestRankApprox (B + N) k Y) :
    frobNorm (B - Y) ^ 2 ≤ frobNorm (B - truncatedSVD B k) ^ 2 +
      4 * k * singularValues B k * specNorm N + 12 * k * specNorm N ^ 2 := by
  sorry

omit [DecidableEq m] in
/-- **The localized perturbed truncation**: for $\mathbf{B}, \mathbf{N} \in
\mathbb{R}^{m \times n}$, $1 \le k$, $\theta = \sigma_{k-1}(\mathbf{B})$, a window
$a \le k \le b$ with $2\theta \le \sigma_i(\mathbf{B})$ for $i < a$,
$\sigma_a(\mathbf{B}) \le 2\theta$ and $\sigma_b(\mathbf{B}) \le \theta/2$, and a best rank-$k$
approximation $\mathbf{Y}$ of $\mathbf{B} + \mathbf{N}$, with $\mathbf{P}_i$, $\mathbf{P}'_i$
the range projectors of $\llbracket\mathbf{B}\rrbracket_i$ and of its transpose and
$\mu = \|(\mathbf{P}_b - \mathbf{P}_a)\mathbf{N}(\mathbf{P}'_b - \mathbf{P}'_a)\|_2$,
$$\|\mathbf{B} - \mathbf{Y}\|_{\mathsf{F}}^2 \le
\|\mathbf{B} - \llbracket\mathbf{B}\rrbracket_k\|_{\mathsf{F}}^2 + 500k\,\|\mathbf{N}\|_2^2 +
40\,\theta\min(k, b - k)\,\mu\,.$$
The noise enters the cross term only through its compression $\mu$ to the singular subspaces
within a factor $2$ of the truncation level, and with weight $\min(k, b - k)$ instead of $k$.
No printed source. New (maintainer's derivation, 2026-10-26).
Proof: L, about 120 lines. Let $\mathbf{Z} = \mathbf{P}_{\mathbf{Y}}$
(`isStarProjection_rangeProjector`, rank at most $k$ by `rank_rangeProjector` and
`IsBestRankApprox.rank_le`), $\eta = \|\mathbf{N}\|_2$, $\mathbf{L} = \mathbf{P}_b -
\mathbf{P}_a$, $\mathbf{L}' = \mathbf{P}'_b - \mathbf{P}'_a$, $\mathbf{\Delta} = \mathbf{Z} -
\mathbf{P}_k$, $D = \|(\mathbf{I} - \mathbf{Z})\mathbf{B}\|^2 - \|(\mathbf{I} -
\mathbf{P}_k)\mathbf{B}\|^2$. By `NLAlib.IsBestRankApprox.frobNorm_sub_sq_eq_add` and
$\mathbf{B} - \llbracket\mathbf{B}\rrbracket_k = (\mathbf{I} - \mathbf{P}_k)\mathbf{B}$
(`rangeProjector_truncatedSVD_mul`) the excess is $D + \|\mathbf{Z}\mathbf{N}\|^2$, and
$\|\mathbf{Z}\mathbf{N}\|^2 \le k\eta^2$ (`frobNorm_sq_le_rank_mul_specNorm_sq`,
`IsStarProjection.specNorm_mul_le`). Case $\theta \le 100\mu$: $\mu \le \eta$
(`IsStarProjection.specNorm_mul_le` on both sides, via `specNorm_conjTranspose`), and
`NLAlib.IsBestRankApprox.frobNorm_sub_sq_le_add_singularValues_mul_specNorm` with
$\sigma_k \le \theta \le 100\eta$ gives $412k\eta^2$. Case $100\mu < \theta$ (so $\theta > 0$):
`NLAlib.IsBestRankApprox.frobNorm_one_sub_rangeProjector_mul_sq_sub_le` gives
$D \le 2\langle\mathbf{\Delta}\mathbf{B}, \mathbf{N}\rangle + k\eta^2$. Split
$\mathbf{\Delta}\mathbf{B} = \mathbf{R} + \mathbf{L}\mathbf{\Delta}\mathbf{B}\mathbf{L}'$: by
`abs_frobInner_le_nuclearNorm_mul_specNorm`, `nuclearNorm_le_sqrt_rank_mul_frobNorm`,
`NLAlib.rank_sub_mul_mul_le` and `NLAlib.frobNorm_sub_mul_mul_sq_le`,
$|\langle\mathbf{R}, \mathbf{N}\rangle| \le 2\sqrt k\sqrt{15D}\,\eta$. Next
$\mathbf{L}\mathbf{\Delta}\mathbf{B}\mathbf{L}' = (\mathbf{L}\mathbf{\Delta}\mathbf{L})
\mathbf{M}$ with $\mathbf{M} = \mathbf{B}_b - \mathbf{B}_a = \mathbf{L}\mathbf{M} =
\mathbf{M}\mathbf{L}'$ (`rangeProjector_truncatedSVD_mul`,
`mul_rangeProjector_conjTranspose_truncatedSVD`), so
$\langle\mathbf{L}\mathbf{\Delta}\mathbf{L}\mathbf{M}, \mathbf{N}\rangle =
\langle\mathbf{L}\mathbf{\Delta}\mathbf{L}, \mathbf{L}\mathbf{N}\mathbf{L}'\mathbf{M}^{\mathsf{H}}
\mathbf{L}\rangle$ (`frobInner_mul_left`, `frobInner_mul_right`) is at most
$\|\mathbf{L}\mathbf{\Delta}\mathbf{L}\|_*\,\mu\,\|\mathbf{M}\|_2 \le
(4\min(k, b - k) + 6D/\theta^2)\,2\theta\mu$ (`NLAlib.nuclearNorm_mul_sub_mul_le`,
`specNorm_mul_le`, $\|\mathbf{M}\|_2 \le \sigma_a \le 2\theta$ by `specNorm_sub_truncatedSVD`).
So $D \le 4\sqrt{15kD}\,\eta + 16\theta\mu\min(k, b - k) + 24(\mu/\theta)D + k\eta^2$; with
$24\mu/\theta \le 1/4$ and $4\sqrt{15kD}\,\eta \le D/4 + 240k\eta^2$ this gives
$D \le 482k\eta^2 + 32\theta\mu\min(k, b - k)$, and the excess is at most
$483k\eta^2 + 32\theta\mu\min(k, b - k)$ (research note OP6, Proposition 3.6, there $965$ with a
cruder split). -/
theorem IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_sq_add_window {B N Y : Matrix m n ℝ}
    {k : ℕ} (hY : IsBestRankApprox (B + N) k Y) (hk : 1 ≤ k) {a b : ℕ} (hak : a ≤ k)
    (hkb : k ≤ b) (ha : ∀ i < a, 2 * singularValues B (k - 1) ≤ singularValues B i)
    (ha₂ : singularValues B a ≤ 2 * singularValues B (k - 1))
    (hb : singularValues B b ≤ singularValues B (k - 1) / 2) :
    frobNorm (B - Y) ^ 2 ≤ frobNorm (B - truncatedSVD B k) ^ 2 + 500 * k * specNorm N ^ 2 +
      40 * singularValues B (k - 1) * ((min k (b - k) : ℕ) : ℝ) *
        specNorm ((rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a)) * N *
          (rangeProjector (truncatedSVD B b)ᴴ - rangeProjector (truncatedSVD B a)ᴴ)) := by
  sorry

end NLAlib
