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
  have h := isSVD_svdU_svdV B
  have hU := h.hasOrthonormalCols_left
  have hV := h.hasOrthonormalCols_right
  set U := svdU B
  set V := svdV B
  have hdiag : ∀ d : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ,
      rangeProjector (Matrix.diagonal d * Vᴴ) =
        Matrix.diagonal (fun i => if d i = 0 then 0 else 1) := by
    intro d
    set e : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ := fun i => if d i = 0 then 0 else 1
    have hed : Matrix.diagonal e * Matrix.diagonal d = Matrix.diagonal d := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases hi : d i = 0 <;> simp [e, hi]
    have hdd : Matrix.diagonal d * Matrix.diagonal d⁻¹ = Matrix.diagonal e := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases hi : d i = 0 <;> simp [e, hi]
    have hP : IsStarProjection (Matrix.diagonal e) := by
      rw [Matrix.isStarProjection_iff]
      refine ⟨?_, ?_⟩
      · rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        by_cases hi : d i = 0 <;> simp [e, hi]
      · exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by
          ext i; simp [e])
    rw [← hP.rangeProjector_eq, rangeProjector_inj]
    refine le_antisymm (range_le_iff_exists_mul.mpr ⟨Matrix.diagonal d * Vᴴ, ?_⟩)
      (range_le_iff_exists_mul.mpr ⟨V * Matrix.diagonal d⁻¹, ?_⟩)
    · rw [← Matrix.mul_assoc, hed]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV.conjTranspose_mul_self, Matrix.one_mul, hdd]
  -- the truncated singular values and their supports
  set s : ℕ → Fin (min (Fintype.card m) (Fintype.card n)) → ℝ :=
    fun k i => if (i : ℕ) < k then singularValues B i else 0
  set e : ℕ → Fin (min (Fintype.card m) (Fintype.card n)) → ℝ :=
    fun k i => if s k i = 0 then 0 else 1
  have hT : ∀ k, truncatedSVD B k = U * (Matrix.diagonal (s k) * Vᴴ) := fun k => by
    rw [truncatedSVD_def, Matrix.mul_assoc]
    rfl
  have hP : ∀ k, rangeProjector (truncatedSVD B k) = U * Matrix.diagonal (e k) * Uᴴ := fun k => by
    rw [hT, hU.rangeProjector_mul, hdiag]
  have hL : W * (rangeProjector (truncatedSVD B j) - rangeProjector (truncatedSVD B a)) =
      W * U * Matrix.diagonal (e j - e a) * Uᴴ := by
    rw [hP, hP, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
    simp only [Matrix.mul_assoc]
    rfl
  have hR : W * (truncatedSVD B j - truncatedSVD B a) =
      W * U * Matrix.diagonal (s j - s a) * Vᴴ := by
    rw [hT, hT, ← Matrix.mul_sub, ← Matrix.sub_mul, Matrix.diagonal_sub]
    simp only [Matrix.mul_assoc]
    rfl
  rw [hL, hR, hU.frobNorm_mul_conjTranspose_right, hV.frobNorm_mul_conjTranspose_right,
    frobNorm_sq_eq_sum_sq, frobNorm_sq_eq_sum_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Matrix.mul_diagonal, Pi.sub_apply]
  have key : (c * (e j i - e a i)) ^ 2 ≤ (s j i - s a i) ^ 2 := by
    by_cases hia : (i : ℕ) < a
    · simp [s, e, hia, hia.trans_le haj]
    by_cases hij : (i : ℕ) < j
    · by_cases h0 : singularValues B i = 0
      · simp [s, e, hia, hij, h0]
      · have := hσ i (not_lt.mp hia) hij
        simp [s, e, hia, hij, h0]
        nlinarith
    · simp [s, e, hia, hij]
  nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg ((W * U) p i))]

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
  set θ := singularValues B (k - 1)
  have hθ : 0 ≤ θ := singularValues_nonneg B (k - 1)
  have hle := range_truncatedSVD_mono B hak
  -- `P_a P_k = P_a = P_k P_a`
  have hPP := rangeProjector_mul_rangeProjector_of_range_le' hle
  have hPP' := rangeProjector_mul_rangeProjector_of_range_le hle
  -- row orthogonality: `(B_k - B_a) B_aᴴ = 0`
  have hBaP : truncatedSVD B a * rangeProjector (truncatedSVD B a)ᴴ = truncatedSVD B a := by
    have h := congrArg Matrix.conjTranspose (rangeProjector_mul_self (truncatedSVD B a)ᴴ)
    rwa [Matrix.conjTranspose_mul, conjTranspose_rangeProjector,
      Matrix.conjTranspose_conjTranspose] at h
  have hBaPk : truncatedSVD B a * rangeProjector (truncatedSVD B k)ᴴ = truncatedSVD B a := by
    conv_lhs => rw [← rangeProjector_truncatedSVD_mul B a]
    rw [Matrix.mul_assoc, mul_rangeProjector_conjTranspose_truncatedSVD,
      ← rangeProjector_truncatedSVD_mul B k, ← Matrix.mul_assoc, hPP,
      rangeProjector_truncatedSVD_mul]
  have horth : (truncatedSVD B k - truncatedSVD B a) * (truncatedSVD B a)ᴴ = 0 := by
    have e : ∀ j, truncatedSVD B a * (truncatedSVD B j)ᴴ =
        truncatedSVD B a * rangeProjector (truncatedSVD B j)ᴴ * Bᴴ := by
      intro j
      conv_lhs => rw [← mul_rangeProjector_conjTranspose_truncatedSVD B j]
      rw [Matrix.conjTranspose_mul, conjTranspose_rangeProjector, Matrix.mul_assoc]
    rw [← Matrix.conjTranspose_conjTranspose (truncatedSVD B k - truncatedSVD B a),
      ← Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.mul_sub, e k, e a, hBaPk,
      hBaP, sub_self, Matrix.conjTranspose_zero]
  have h1 : frobNorm (W * truncatedSVD B k) ^ 2 = frobNorm (W * truncatedSVD B a) ^ 2 +
      frobNorm (W * (truncatedSVD B k - truncatedSVD B a)) ^ 2 := by
    rw [← frobNorm_add_sq_of_frobInner_eq_zero, ← Matrix.mul_add, add_sub_cancel]
    rw [frobInner_mul_right, Matrix.mul_assoc, horth, Matrix.mul_zero, frobInner_zero_right]
  have h2 : frobNorm (W * rangeProjector (truncatedSVD B k)) ^ 2 =
      frobNorm (W * rangeProjector (truncatedSVD B a)) ^ 2 +
      frobNorm (W * (rangeProjector (truncatedSVD B k) -
        rangeProjector (truncatedSVD B a))) ^ 2 := by
    rw [← frobNorm_add_sq_of_frobInner_eq_zero, ← Matrix.mul_add, add_sub_cancel]
    rw [frobInner_mul_right, Matrix.mul_assoc, conjTranspose_rangeProjector, Matrix.sub_mul, hPP',
      rangeProjector_mul_rangeProjector, sub_self, Matrix.mul_zero, frobInner_zero_right]
  have h3 := sq_mul_frobNorm_mul_sub_rangeProjector_sq_le B W hak hθ fun i _ hi =>
    singularValues_antitone B (by omega : i ≤ k - 1)
  have h4 := sq_mul_frobNorm_mul_sub_rangeProjector_sq_le B W (Nat.zero_le a)
    (by positivity : 0 ≤ 2 * θ) fun i _ hi => ha i hi
  rw [truncatedSVD_zero, rangeProjector_zero, sub_zero, sub_zero] at h4
  nlinarith [mul_nonneg (sq_nonneg θ)
    (sq_nonneg (frobNorm (W * rangeProjector (truncatedSVD B a))))]

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
  set θ := singularValues B (k - 1)
  set P := rangeProjector (truncatedSVD B k)
  set Q := rangeProjector (truncatedSVD B b)
  have hP := isStarProjection_rangeProjector (truncatedSVD B k)
  have hQ := isStarProjection_rangeProjector (truncatedSVD B b)
  have hR := isStarProjection_rangeProjector (truncatedSVD B b)ᴴ
  have hQP : Q * P = P :=
    rangeProjector_mul_rangeProjector_of_range_le (range_truncatedSVD_mono B hkb)
  have hBk : Q * truncatedSVD B k = truncatedSVD B k := by
    rw [← rangeProjector_truncatedSVD_mul B k, ← Matrix.mul_assoc, hQP]
  -- the two orthogonal splittings
  have h1 : frobNorm (W * (1 - P)) ^ 2 =
      frobNorm (W * (Q - P)) ^ 2 + frobNorm (W * (1 - Q)) ^ 2 := by
    have h0 : (1 - Q) * (Q - P)ᴴ = 0 := by
      rw [Matrix.conjTranspose_sub, hQ.conjTranspose_eq, hP.conjTranspose_eq, Matrix.mul_sub,
        Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.one_mul, hQ.mul_self, hQP,
        sub_self, sub_self, sub_zero]
    rw [← sub_add_sub_cancel' Q P 1, Matrix.mul_add]
    refine frobNorm_add_sq_of_frobInner_eq_zero ?_
    rw [frobInner_mul_right, Matrix.mul_assoc, h0, Matrix.mul_zero, frobInner_zero_right]
  have h2 : frobNorm (W * (B - truncatedSVD B k)) ^ 2 =
      frobNorm (W * (truncatedSVD B b - truncatedSVD B k)) ^ 2 +
        frobNorm (W * (B - truncatedSVD B b)) ^ 2 := by
    classical
    set R := rangeProjector (truncatedSVD B b)ᴴ
    have hPQ : P * Q = P :=
      rangeProjector_mul_rangeProjector_of_range_le' (range_truncatedSVD_mono B hkb)
    have e1 : truncatedSVD B b - truncatedSVD B k = (1 - P) * B * R := by
      rw [Matrix.mul_assoc, mul_rangeProjector_conjTranspose_truncatedSVD, Matrix.sub_mul,
        Matrix.one_mul, ← rangeProjector_truncatedSVD_mul B b, ← Matrix.mul_assoc, hPQ,
        rangeProjector_truncatedSVD_mul, rangeProjector_truncatedSVD_mul]
    have e2 : B - truncatedSVD B b = B * (1 - R) := by
      rw [Matrix.mul_sub, Matrix.mul_one, mul_rangeProjector_conjTranspose_truncatedSVD]
    rw [← sub_add_sub_cancel' (truncatedSVD B b) (truncatedSVD B k) B, Matrix.mul_add]
    refine frobNorm_add_sq_of_frobInner_eq_zero ?_
    have h00 : B * (1 - R) * R = 0 := by
      rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hR.mul_self, sub_self, Matrix.mul_zero]
    rw [e1, e2, ← Matrix.mul_assoc, frobInner_mul_right, hR.conjTranspose_eq, Matrix.mul_assoc W,
      h00, Matrix.mul_zero, frobInner_zero_right]
  -- the two upper bounds: both pieces factor through a projector difference
  have hQB : Q * B = truncatedSVD B b := rangeProjector_truncatedSVD_mul B b
  have h3 : frobNorm (W * (truncatedSVD B b - truncatedSVD B k)) ^ 2 ≤
      θ ^ 2 * frobNorm (W * (Q - P)) ^ 2 := by
    have e : (Q - P) * (B - truncatedSVD B k) = truncatedSVD B b - truncatedSVD B k := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hQB, hBk,
        rangeProjector_truncatedSVD_mul, rangeProjector_mul_self, sub_self, sub_zero]
    have hσ : specNorm (B - truncatedSVD B k) ≤ θ :=
      (specNorm_sub_truncatedSVD B k).trans_le (singularValues_antitone B (by omega))
    rw [← e, ← Matrix.mul_assoc, mul_comm (θ ^ 2), ← mul_pow]
    gcongr
    exact (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
      (mul_le_mul_of_nonneg_left hσ (frobNorm_nonneg _))
  have h4 : frobNorm (W * (B - truncatedSVD B b)) ^ 2 ≤
      θ ^ 2 / 4 * frobNorm (W * (1 - Q)) ^ 2 := by
    have e : (1 - Q) * (B - truncatedSVD B b) = B - truncatedSVD B b := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hQB, rangeProjector_mul_self, sub_self,
        sub_zero]
    rw [← e, ← Matrix.mul_assoc,
      show θ ^ 2 / 4 * frobNorm (W * (1 - Q)) ^ 2 = (frobNorm (W * (1 - Q)) * (θ / 2)) ^ 2 by ring]
    gcongr
    exact (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans (mul_le_mul_of_nonneg_left
      ((specNorm_sub_truncatedSVD B b).trans_le hb) (frobNorm_nonneg _))
  rw [h1, h2]
  linarith

/-! ### The off-window part and the trace balance -/

omit [DecidableEq m] in
/-- The range projectors of nested truncations of the chosen SVD compose to the smaller one. -/
private theorem rangeProjector_truncatedSVD_mul_of_le (B : Matrix m n ℝ) {i j : ℕ}
    (hij : i ≤ j) :
    rangeProjector (truncatedSVD B j) * rangeProjector (truncatedSVD B i) =
        rangeProjector (truncatedSVD B i) ∧
      rangeProjector (truncatedSVD B i) * rangeProjector (truncatedSVD B j) =
        rangeProjector (truncatedSVD B i) :=
  ⟨rangeProjector_mul_rangeProjector_of_range_le (range_truncatedSVD_mono B hij),
    rangeProjector_mul_rangeProjector_of_range_le' (range_truncatedSVD_mono B hij)⟩

omit [DecidableEq m] in
/-- The residual of a truncation is row-orthogonal to every smaller truncation:
$(\mathbf{B} - \mathbf{B}_j)\mathbf{B}_i^{\mathsf{H}} = \mathbf{0}$ for $i \le j$. -/
private theorem sub_truncatedSVD_mul_conjTranspose_of_le (B : Matrix m n ℝ) {i j : ℕ}
    (hij : i ≤ j) : (B - truncatedSVD B j) * (truncatedSVD B i)ᴴ = 0 := by
  have hP := isStarProjection_rangeProjector (truncatedSVD B j)ᴴ
  have h0 : (B - truncatedSVD B j) * (truncatedSVD B j)ᴴ = 0 := by
    rw [← mul_rangeProjector_conjTranspose_truncatedSVD B j, Matrix.conjTranspose_mul,
      hP.conjTranspose_eq, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_assoc B,
      hP.mul_self, sub_self, Matrix.zero_mul]
  rw [← rangeProjector_truncatedSVD_mul B i, ← (rangeProjector_truncatedSVD_mul_of_le B hij).2,
    Matrix.mul_assoc, rangeProjector_truncatedSVD_mul, Matrix.conjTranspose_mul,
    conjTranspose_rangeProjector, ← Matrix.mul_assoc, h0, Matrix.zero_mul]

/-- The cross block of a projector between two nested projectors: for orthogonal projectors
$\mathbf{P}_a\mathbf{P}_b = \mathbf{P}_a$, $\mathbf{Z}$ and $\mathbf{L} = \mathbf{P}_b -
\mathbf{P}_a$, $\|(\mathbf{I} - \mathbf{L})\mathbf{Z}\mathbf{L}\|_{\mathsf{F}}^2 \le
\|(\mathbf{I} - \mathbf{Z})\mathbf{P}_a\|_{\mathsf{F}}^2 +
\|\mathbf{Z}(\mathbf{I} - \mathbf{P}_b)\|_{\mathsf{F}}^2$. -/
private theorem frobNorm_one_sub_sub_mul_mul_sub_sq_le {Pa Pb Z : Matrix m m ℝ}
    (hPa : IsStarProjection Pa) (hPb : IsStarProjection Pb) (hZ : IsStarProjection Z)
    (hab : Pa * Pb = Pa) :
    frobNorm ((1 - (Pb - Pa)) * Z * (Pb - Pa)) ^ 2 ≤
      frobNorm ((1 - Z) * Pa) ^ 2 + frobNorm (Z * (1 - Pb)) ^ 2 := by
  have hL : IsStarProjection (Pb - Pa) := hPa.sub_of_mul_eq_left hPb hab
  have hZ1 : (1 - Z)ᴴ = 1 - Z := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hZ.conjTranspose_eq]
  have hPaL : Pa * (Pb - Pa) = 0 := by rw [Matrix.mul_sub, hab, hPa.mul_self, sub_self]
  have horth : frobInner (Pa * Z * (Pb - Pa)) ((1 - Pb) * Z * (Pb - Pa)) = 0 := by
    rw [Matrix.mul_assoc Pa, frobInner_mul_left, hPa.conjTranspose_eq, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_sub Pa 1 Pb, Matrix.mul_one, hab, sub_self,
      Matrix.zero_mul, Matrix.zero_mul, frobInner_zero_right]
  have h1 : frobNorm (Pa * Z * (Pb - Pa)) ≤ frobNorm ((1 - Z) * Pa) := by
    have h : Pa * Z * (Pb - Pa) = -(Pa * (1 - Z) * (Pb - Pa)) := by
      rw [Matrix.mul_sub Pa, Matrix.mul_one, Matrix.sub_mul, hPaL, zero_sub, neg_neg]
    rw [h, frobNorm_neg, ← frobNorm_conjTranspose ((1 - Z) * Pa), Matrix.conjTranspose_mul,
      hZ1, hPa.conjTranspose_eq]
    exact hL.frobNorm_mul_right_le _
  have h2 : frobNorm ((1 - Pb) * Z * (Pb - Pa)) ≤ frobNorm (Z * (1 - Pb)) := by
    rw [← frobNorm_conjTranspose (Z * (1 - Pb)), Matrix.conjTranspose_mul,
      hPb.one_sub.conjTranspose_eq, hZ.conjTranspose_eq]
    exact hL.frobNorm_mul_right_le _
  rw [show 1 - (Pb - Pa) = Pa + (1 - Pb) by abel, Matrix.add_mul, Matrix.add_mul,
    frobNorm_add_sq_of_frobInner_eq_zero horth]
  exact add_le_add (pow_le_pow_left₀ (frobNorm_nonneg _) h1 2)
    (pow_le_pow_left₀ (frobNorm_nonneg _) h2 2)

omit [DecidableEq m] in
/-- At $\theta = \sigma_{k-1}(\mathbf{B})$, an orthogonal projector of rank at most $k$ has
$\theta^2(\|\mathbf{P}_k\|_{\mathsf{F}}^2 - \|\mathbf{Z}\|_{\mathsf{F}}^2) \ge 0$. -/
private theorem sq_singularValues_mul_frobNorm_sq_sub_nonneg (B : Matrix m n ℝ) {k : ℕ}
    (hk : 1 ≤ k) {Z : Matrix m m ℝ} (hZ : IsStarProjection Z) (hZk : Z.rank ≤ k) :
    0 ≤ singularValues B (k - 1) ^ 2 *
      (frobNorm (rangeProjector (truncatedSVD B k)) ^ 2 - frobNorm Z ^ 2) := by
  rcases (singularValues_nonneg B (k - 1)).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · have hr := (singularValues_pos_iff B).1 h0
    rw [frobNorm_rangeProjector_sq, rank_truncatedSVD, min_eq_left (by omega),
      hZ.frobNorm_sq_eq_rank]
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.2 (by exact_mod_cast hZk))

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
  rw [Matrix.mul_assoc _ B, Matrix.mul_sub B, mul_rangeProjector_conjTranspose_truncatedSVD,
    mul_rangeProjector_conjTranspose_truncatedSVD]
  have hD := frobNorm_one_sub_mul_sq_sub_eq_add B k hZ (singularValues B (k - 1))
  have hhi := mul_frobNorm_mul_truncatedSVD_sq_add_le B hk hak ha (1 - Z)
  have hlo := mul_frobNorm_mul_one_sub_sq_add_le B hk hkb hb Z
  have hak' := rangeProjector_truncatedSVD_mul_of_le B hak
  have hkb' := rangeProjector_truncatedSVD_mul_of_le B hkb
  have hab' := rangeProjector_truncatedSVD_mul_of_le B (hak.trans hkb)
  have hBa := rangeProjector_truncatedSVD_mul B a
  have hBb := rangeProjector_truncatedSVD_mul B b
  have hBk := rangeProjector_truncatedSVD_mul B k
  have hPa := isStarProjection_rangeProjector (truncatedSVD B a)
  have hPb := isStarProjection_rangeProjector (truncatedSVD B b)
  have hPk := isStarProjection_rangeProjector (truncatedSVD B k)
  have H1 := sub_truncatedSVD_mul_conjTranspose_of_le B (hak.trans hkb)
  have H2 := sub_truncatedSVD_mul_conjTranspose_of_le B le_rfl (i := a)
  have H3 := sub_truncatedSVD_mul_conjTranspose_of_le B le_rfl (i := b)
  have hσa := (specNorm_sub_truncatedSVD B a).trans_le ha₂
  have hrank := sq_singularValues_mul_frobNorm_sq_sub_nonneg B hk hZ hZk
  set θ := singularValues B (k - 1) with hθ
  set Pa := rangeProjector (truncatedSVD B a) with hPa_def
  set Pb := rangeProjector (truncatedSVD B b) with hPb_def
  set Pk := rangeProjector (truncatedSVD B k) with hPk_def
  set Ba := truncatedSVD B a with hBa_def
  set Bb := truncatedSVD B b with hBb_def
  set Bk := truncatedSVD B k with hBk_def
  have hLB : (Pb - Pa) * (B - Ba) = Bb - Ba := by
    rw [← hBa, ← hBb]
    simp only [Matrix.sub_mul, Matrix.mul_sub, ← Matrix.mul_assoc, hab'.1, hPa.mul_self]
    abel
  have e1 : (Z - Pk) * Ba = -((1 - Z) * Ba) := by
    rw [← hBa]
    simp only [Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc, hak'.1]
    abel
  have e2 : (Z - Pk) * (B - Bb) = Z * (B - Bb) := by
    rw [← hBb, Matrix.sub_mul, Matrix.mul_sub Pk, ← Matrix.mul_assoc Pk, hkb'.2, hBk, sub_self,
      sub_zero]
  have e3 : (1 - (Pb - Pa)) * (Z - Pk) * (Bb - Ba) = (1 - (Pb - Pa)) * Z * (Bb - Ba) := by
    have hPkL : (1 - (Pb - Pa)) * Pk * (Pb - Pa) = 0 := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, hkb'.1, hkb'.2, hak'.1,
        hak'.2, hab'.2, hPa.mul_self]
      abel
    rw [← hLB, ← Matrix.mul_assoc ((1 - (Pb - Pa)) * (Z - Pk)),
      ← Matrix.mul_assoc ((1 - (Pb - Pa)) * Z), Matrix.mul_sub (1 - (Pb - Pa)) Z Pk,
      Matrix.sub_mul _ _ (Pb - Pa), hPkL, sub_zero]
  have hdec : (Z - Pk) * B - (Pb - Pa) * (Z - Pk) * (Bb - Ba) =
      -((1 - Z) * Ba) + Z * (B - Bb) + (1 - (Pb - Pa)) * Z * (Bb - Ba) := by
    rw [← e1, ← e2, ← e3]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul]
    abel
  have K2 : (Bb - Ba) * Baᴴ = 0 := by
    rw [show Bb - Ba = (B - Ba) - (B - Bb) by abel, Matrix.sub_mul, H2, H1, sub_zero]
  have K3 : (B - Bb) * (Bb - Ba)ᴴ = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.mul_sub, H3, H1, sub_zero]
  have o1 : frobInner (-((1 - Z) * Ba)) (Z * (B - Bb)) = 0 := by
    rw [frobInner_neg_left, frobInner_mul_right, Matrix.mul_assoc, H1, Matrix.mul_zero,
      frobInner_zero_right, neg_zero]
  have o2 : frobInner (-((1 - Z) * Ba) + Z * (B - Bb)) ((1 - (Pb - Pa)) * Z * (Bb - Ba)) = 0 := by
    rw [frobInner_add_left, frobInner_neg_left, frobInner_mul_right, Matrix.mul_assoc _ (Bb - Ba),
      K2, Matrix.mul_zero, frobInner_zero_right, frobInner_comm, frobInner_mul_right,
      Matrix.mul_assoc Z, K3, Matrix.mul_zero, frobInner_zero_right, neg_zero, add_zero]
  have hpy : frobNorm ((Z - Pk) * B - (Pb - Pa) * (Z - Pk) * (Bb - Ba)) ^ 2 =
      frobNorm ((1 - Z) * Ba) ^ 2 + frobNorm (Z * (B - Bb)) ^ 2 +
        frobNorm ((1 - (Pb - Pa)) * Z * (Bb - Ba)) ^ 2 := by
    rw [hdec, frobNorm_add_sq_of_frobInner_eq_zero o2, frobNorm_add_sq_of_frobInner_eq_zero o1,
      frobNorm_neg]
  have hw : frobNorm ((1 - (Pb - Pa)) * Z * (Bb - Ba)) ≤
      frobNorm ((1 - (Pb - Pa)) * Z * (Pb - Pa)) * (2 * θ) := by
    rw [← hLB, ← Matrix.mul_assoc]
    refine (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans ?_
    gcongr
  have hY := frobNorm_one_sub_sub_mul_mul_sub_sq_le hPa hPb hZ hab'.2
  have hT : frobNorm ((1 - (Pb - Pa)) * Z * (Bb - Ba)) ^ 2 ≤
      4 * θ ^ 2 * frobNorm ((1 - Z) * Pa) ^ 2 + 4 * θ ^ 2 * frobNorm (Z * (1 - Pb)) ^ 2 := by
    have h4 := mul_le_mul_of_nonneg_left hY (by positivity : (0 : ℝ) ≤ 4 * θ ^ 2)
    nlinarith [pow_le_pow_left₀ (frobNorm_nonneg _) hw 2]
  nlinarith [hpy, mul_nonneg (sq_nonneg θ) (sq_nonneg (frobNorm ((1 - Z) * Pa))),
    mul_nonneg (sq_nonneg θ) (sq_nonneg (frobNorm (Z * (1 - Pb)))),
    sq_nonneg (frobNorm ((1 - Z) * Ba)), sq_nonneg (frobNorm (Z * (B - Bb)))]

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
  have hP : (rangeProjector (truncatedSVD B k)).rank ≤ k := by
    rw [rank_rangeProjector]
    exact rank_truncatedSVD_le B k
  have hD : (Z - rangeProjector (truncatedSVD B k)).rank ≤ 2 * k :=
    (Matrix.rank_sub_le _ _).trans (by omega)
  have hX : ((Z - rangeProjector (truncatedSVD B k)) * B).rank ≤ 2 * k :=
    (Matrix.rank_mul_le_left _ _).trans hD
  have hY : (L * (Z - rangeProjector (truncatedSVD B k)) * B * L').rank ≤ 2 * k := by
    rw [show L * (Z - rangeProjector (truncatedSVD B k)) * B * L' =
      L * ((Z - rangeProjector (truncatedSVD B k)) * B) * L' by simp only [Matrix.mul_assoc]]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hX)
  have := Matrix.rank_sub_le ((Z - rangeProjector (truncatedSVD B k)) * B)
    (L * (Z - rangeProjector (truncatedSVD B k)) * B * L')
  omega

omit [DecidableEq m] in
/-- The compression of a star projection by a star projection is a Gram matrix:
$\|\mathbf{R}\mathbf{Q}\mathbf{R}\|_* = \|\mathbf{Q}\mathbf{R}\|_{\mathsf{F}}^2$. -/
private theorem nuclearNorm_mul_mul_eq_frobNorm_sq {Q R : Matrix m m ℝ}
    (hQ : IsStarProjection Q) (hR : IsStarProjection R) :
    nuclearNorm (R * Q * R) = frobNorm (Q * R) ^ 2 := by
  rw [← nuclearNorm_conjTranspose_mul_self, Matrix.conjTranspose_mul, hQ.conjTranspose_eq,
    hR.conjTranspose_eq, ← Matrix.mul_assoc, Matrix.mul_assoc R Q Q, hQ.mul_self]

/-- **Pythagoras on the right** for an orthogonal projector $\mathbf{Q}$:
$\|\mathbf{A}\|_{\mathsf{F}}^2 = \|\mathbf{A}\mathbf{Q}\|_{\mathsf{F}}^2 +
\|\mathbf{A}(\mathbf{I} - \mathbf{Q})\|_{\mathsf{F}}^2$. -/
private theorem frobNorm_sq_eq_add_mul_right {p : Type*} [Fintype p] {Q : Matrix m m ℝ}
    (hQ : IsStarProjection Q) (A : Matrix p m ℝ) :
    frobNorm A ^ 2 = frobNorm (A * Q) ^ 2 + frobNorm (A * (1 - Q)) ^ 2 := by
  rw [← frobNorm_conjTranspose (A * Q), ← frobNorm_conjTranspose (A * (1 - Q)),
    ← frobNorm_conjTranspose A, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hQ.conjTranspose_eq, hQ.one_sub.conjTranspose_eq]
  exact hQ.frobNorm_sq_eq_add Aᴴ

/-- The window compression for nested orthogonal projectors
$\mathbf{P}_a \le \mathbf{P} \le \mathbf{P}_b$ and an orthogonal projector $\mathbf{Z}$, with
$\mathbf{L} = \mathbf{P}_b - \mathbf{P}_a$:
$$\|\mathbf{L}(\mathbf{Z} - \mathbf{P})\mathbf{L}\|_* \le
(\|\mathbf{P}_b\|_{\mathsf{F}}^2 - \|\mathbf{P}\|_{\mathsf{F}}^2) +
(\|\mathbf{P}_b\|_{\mathsf{F}}^2 - \|\mathbf{Z}\|_{\mathsf{F}}^2) +
\|\mathbf{Z}(\mathbf{I} - \mathbf{P}_b)\|_{\mathsf{F}}^2\,.$$ -/
private theorem nuclearNorm_mul_sub_mul_le_of_mul_eq {Pa P Pb Z : Matrix m m ℝ}
    (hPa : IsStarProjection Pa) (hP : IsStarProjection P) (hPb : IsStarProjection Pb)
    (hZ : IsStarProjection Z) (h1 : Pa * P = Pa) (h2 : P * Pa = Pa) (h3 : P * Pb = P)
    (h4 : Pb * P = P) (h5 : Pa * Pb = Pa) (h6 : Pb * Pa = Pa) :
    nuclearNorm ((Pb - Pa) * (Z - P) * (Pb - Pa)) ≤
      (frobNorm Pb ^ 2 - frobNorm P ^ 2) + (frobNorm Pb ^ 2 - frobNorm Z ^ 2) +
        frobNorm (Z * (1 - Pb)) ^ 2 := by
  have hL : IsStarProjection (Pb - Pa) := hPa.sub_of_mul_eq_left hPb h5
  have hLb : IsStarProjection (Pb - P) := hP.sub_of_mul_eq_left hPb h3
  have hLP : (Pb - Pa) * P * (Pb - Pa) = P - Pa := by
    rw [Matrix.sub_mul Pb Pa P, h4, h1, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, h3, h2,
      h5, hPa.mul_self]
    abel
  have e : (Pb - Pa) * (Z - P) * (Pb - Pa) =
      (Pb - P) + -((Pb - Pa) * (1 - Z) * (Pb - Pa)) := by
    rw [Matrix.mul_sub (Pb - Pa) Z P, Matrix.sub_mul _ _ (Pb - Pa), hLP,
      Matrix.mul_sub (Pb - Pa) 1 Z, Matrix.mul_one, Matrix.sub_mul _ _ (Pb - Pa), hL.mul_self]
    abel
  rw [e]
  refine (nuclearNorm_add_le _ _).trans ?_
  rw [nuclearNorm_neg, nuclearNorm_mul_mul_eq_frobNorm_sq hZ.one_sub hL]
  have hLb₁ := nuclearNorm_conjTranspose_mul_self (Pb - P)
  rw [hLb.conjTranspose_eq, hLb.mul_self] at hLb₁
  have hLb₂ := hP.frobNorm_sq_eq_add Pb
  rw [h3, Matrix.sub_mul, Matrix.one_mul, h3] at hLb₂
  have e' : (1 - Z) * (Pb - Pa) = (1 - Z) * Pb * (1 - Pa) := by
    rw [Matrix.mul_assoc, Matrix.mul_sub Pb, Matrix.mul_one, h6]
  have := pow_le_pow_left₀ (frobNorm_nonneg _)
    (hPa.one_sub.frobNorm_mul_right_le ((1 - Z) * Pb)) 2
  rw [← e'] at this
  have := hZ.frobNorm_sq_eq_add Pb
  have := frobNorm_sq_eq_add_mul_right hPb Z
  linarith

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
  set θ := singularValues B (k - 1) with hθdef
  set Pa := rangeProjector (truncatedSVD B a) with hPadef
  set P := rangeProjector (truncatedSVD B k) with hPdef
  set Pb := rangeProjector (truncatedSVD B b) with hPbdef
  have hPa : IsStarProjection Pa := isStarProjection_rangeProjector _
  have hP : IsStarProjection P := isStarProjection_rangeProjector _
  have hPb : IsStarProjection Pb := isStarProjection_rangeProjector _
  have hak' := range_truncatedSVD_mono B hak
  have hkb' := range_truncatedSVD_mono B hkb
  have hab' := range_truncatedSVD_mono B (hak.trans hkb)
  have h1 : Pa * P = Pa := rangeProjector_mul_rangeProjector_of_range_le' hak'
  have h2 : P * Pa = Pa := rangeProjector_mul_rangeProjector_of_range_le hak'
  have h3 : P * Pb = P := rangeProjector_mul_rangeProjector_of_range_le' hkb'
  have h4 : Pb * P = P := rangeProjector_mul_rangeProjector_of_range_le hkb'
  have h5 : Pa * Pb = Pa := rangeProjector_mul_rangeProjector_of_range_le' hab'
  have h6 : Pb * Pa = Pa := rangeProjector_mul_rangeProjector_of_range_le hab'
  have hL : IsStarProjection (Pb - Pa) := hPa.sub_of_mul_eq_left hPb h5
  -- the norms of the projectors
  have hPk : frobNorm P ^ 2 = k := by
    have := (singularValues_pos_iff B).1 hθ
    rw [frobNorm_rangeProjector_sq, rank_truncatedSVD, min_eq_left (by omega)]
  have hPbb : frobNorm Pb ^ 2 ≤ b := by
    rw [frobNorm_rangeProjector_sq]; exact_mod_cast rank_truncatedSVD_le B b
  have hZ2 : frobNorm Z ^ 2 ≤ k := by
    rw [hZ.frobNorm_sq_eq_rank]; exact_mod_cast hZk
  -- the weights
  have hD := frobNorm_one_sub_mul_sq_sub_eq_add B k hZ θ
  have hhead := mul_frobNorm_mul_truncatedSVD_sq_add_le B hk (Nat.zero_le k)
    (fun i hi => absurd hi (Nat.not_lt_zero i)) (1 - Z)
  have htail := mul_frobNorm_mul_one_sub_sq_add_le B hk hkb hb Z
  rw [← hPdef] at hD hhead htail
  rw [← hPbdef] at htail
  rw [← hθdef] at hhead htail
  set E := (frobNorm ((1 - Z) * B) ^ 2 - frobNorm ((1 - P) * B) ^ 2) / θ ^ 2 with hEdef
  have hE : frobNorm P ^ 2 - frobNorm Z ^ 2 + 3 / 8 * frobNorm (Z * (1 - Pb)) ^ 2 ≤ E := by
    rw [hEdef, le_div_iff₀ (by positivity), hD]
    have h0 : 0 ≤ 3 / 8 * frobNorm ((1 - Z) * truncatedSVD B 0) ^ 2 +
        3 / 2 * θ ^ 2 * frobNorm ((1 - Z) * rangeProjector (truncatedSVD B 0)) ^ 2 := by
      positivity
    nlinarith [frobNorm_nonneg (Z * (B - truncatedSVD B b))]
  -- bound A
  have hA : nuclearNorm ((Pb - Pa) * (Z - P) * (Pb - Pa)) ≤ 2 * k := by
    have e : (Pb - Pa) * (Z - P) * (Pb - Pa) =
        (Pb - Pa) * Z * (Pb - Pa) + -((Pb - Pa) * P * (Pb - Pa)) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [e]
    refine (nuclearNorm_add_le _ _).trans ?_
    rw [nuclearNorm_neg, nuclearNorm_mul_mul_eq_frobNorm_sq hZ hL,
      nuclearNorm_mul_mul_eq_frobNorm_sq hP hL]
    have := pow_le_pow_left₀ (frobNorm_nonneg _) (hL.frobNorm_mul_right_le Z) 2
    have := pow_le_pow_left₀ (frobNorm_nonneg _) (hL.frobNorm_mul_right_le P) 2
    linarith
  have hB := nuclearNorm_mul_sub_mul_le_of_mul_eq hPa hP hPb hZ h1 h2 h3 h4 h5 h6
  have hs := frobNorm_nonneg (Z * (1 - Pb))
  rcases le_total k (b - k) with h | h
  · rw [min_eq_left h]
    have : (k : ℝ) ≤ ((b - k : ℕ) : ℝ) := by exact_mod_cast h
    nlinarith
  · rw [min_eq_right h, Nat.cast_sub hkb]
    have : (k : ℝ) ≤ b := by exact_mod_cast hkb
    nlinarith

/-! ### The localized perturbed truncation -/

/-- A best approximation is the projection of the target onto its own column space:
$\mathbf{P}_{\mathbf{Y}}\mathbf{M} = \mathbf{Y}$. -/
private theorem IsBestRankApprox.rangeProjector_self_mul'
    {m₁ n₁ : Type*} [Fintype m₁] [Fintype n₁] {M Y : Matrix m₁ n₁ ℝ} {k : ℕ}
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

/-- The scalar step of the next-$k$ perturbed truncation. -/
private theorem le_add_mul_of_le_two_mul' {S a w u q γ s r e : ℝ} (hs : 0 ≤ s) (he : 0 ≤ e)
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hr2 : r ^ 2 = 2) (hqγ : q ≤ γ)
    (h1 : S ≤ 2 * (r * s * u * e + w)) (h2 : S = a - q ^ 2 + w) (h3 : u ^ 2 = a + q ^ 2)
    (hw : w ≤ s ^ 2 * e ^ 2) :
    S ≤ 4 * s * e * γ + 12 * s ^ 2 * e ^ 2 := by
  have hr3 : r ≤ 3 / 2 := by nlinarith
  have hsq : (u - r * s * e) ^ 2 ≤ (2 * s * e + r * q) ^ 2 := by
    have e1 : (u - r * s * e) ^ 2 = u ^ 2 - 2 * (r * s * u * e) + r ^ 2 * (s * e) ^ 2 := by ring
    have e2 : (2 * s * e + r * q) ^ 2 =
        4 * (s * e) ^ 2 + 4 * (r * s * e * q) + r ^ 2 * q ^ 2 := by ring
    rw [e1, e2, hr2]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hr hs) he) hq]
  have hu' : u ≤ (r + 2) * s * e + r * q := by
    nlinarith [(abs_le_of_sq_le_sq' hsq (by positivity)).2]
  have hse : 0 ≤ r * s * e := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hu' hse, mul_le_mul_of_nonneg_left hqγ (mul_nonneg hs he),
    mul_le_mul_of_nonneg_right hr3 (sq_nonneg (s * e))]

/-- The optimality step of perturbed truncation: for any best rank-$k$ approximation
$\mathbf{Y}$ of $\mathbf{C} + \mathbf{E}$,
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}}^2 -
\|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}}^2 \le
2\langle\mathbf{Y} - \llbracket\mathbf{C}\rrbracket_k, \mathbf{E}\rangle_{\mathsf{F}}\,.$$ -/
private theorem IsBestRankApprox.frobNorm_sub_sq_sub_le_two_mul_frobInner'
    {m₁ n₁ : Type*} [Fintype m₁] [Fintype n₁]
    {C E Y : Matrix m₁ n₁ ℝ} {k : ℕ} (hY : IsBestRankApprox (C + E) k Y) :
    frobNorm (C - Y) ^ 2 - frobNorm (C - truncatedSVD C k) ^ 2 ≤
      2 * frobInner (Y - truncatedSVD C k) E := by
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
  linarith

/-- The next-$k$ perturbed truncation in core coordinates: for any best rank-$k$ approximation
$\mathbf{Y}$ of $\mathbf{C} + \mathbf{E}$, with $\gamma_k =
\|\llbracket\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\rrbracket_k\|_{\mathsf{F}}$,
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}}^2 \le
\|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}}^2 +
4\sqrt{k}\,\|\mathbf{E}\|_2\,\gamma_k + 12k\,\|\mathbf{E}\|_2^2\,.$$ -/
private theorem IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_mul_frobNorm'
    {m₁ n₁ : Type*} [Fintype m₁] [Fintype n₁]
    {C E Y : Matrix m₁ n₁ ℝ} {k : ℕ} (hY : IsBestRankApprox (C + E) k Y) :
    frobNorm (C - Y) ^ 2 ≤ frobNorm (C - truncatedSVD C k) ^ 2 +
      4 * √(k : ℝ) * specNorm E * frobNorm (truncatedSVD (C - truncatedSVD C k) k) +
      12 * k * specNorm E ^ 2 := by
  classical
  set T := truncatedSVD C k with hT
  set B₂ := C - T with hB₂
  set P := rangeProjector Y with hPdef
  have hP : IsStarProjection P := isStarProjection_rangeProjector Y
  have hPY : P * (C + E) = Y := hY.rangeProjector_self_mul'
  have hY' : Y = P * C + P * E := by rw [← hPY, Matrix.mul_add]
  have hrP : P.rank ≤ k := by rw [hPdef, rank_rangeProjector]; exact hY.rank_le
  have hrT : T.rank ≤ k := rank_truncatedSVD_le C k
  -- (D1) the optimality of `Y` against `T`
  have hS : frobNorm (C - Y) ^ 2 - frobNorm B₂ ^ 2 ≤ 2 * frobInner (Y - T) E :=
    hY.frobNorm_sub_sq_sub_le_two_mul_frobInner'
  -- (D2) the row spaces of `T` and `B₂` are orthogonal
  have hTPB : frobInner T (P * B₂) = 0 := by
    have hCQ : C * rangeProjector Tᴴ = T := mul_rangeProjector_conjTranspose_truncatedSVD C k
    have hTQ : T * rangeProjector Tᴴ = T :=
      calc T * rangeProjector Tᴴ = C * rangeProjector Tᴴ * rangeProjector Tᴴ := by
            rw [hCQ]
        _ = T := by rw [Matrix.mul_assoc, rangeProjector_mul_rangeProjector, hCQ]
    have hBQ : B₂ * rangeProjector Tᴴ = 0 := by rw [hB₂, Matrix.sub_mul, hCQ, hTQ, sub_self]
    nth_rw 1 [← hTQ]
    rw [frobInner_mul_right, conjTranspose_rangeProjector, Matrix.mul_assoc, hBQ, Matrix.mul_zero,
      frobInner_zero_right]
  have hCY : frobNorm (C - Y) ^ 2 = frobNorm (T - P * T) ^ 2 +
      (frobNorm B₂ ^ 2 - frobNorm (P * B₂) ^ 2) + frobNorm (P * E) ^ 2 := by
    have h1 : C - Y = (C - P * C) - P * E := by rw [hY']; abel
    have h0 : frobInner (C - P * C) (P * E) = 0 := by
      rw [frobInner_comm, frobInner_mul_left, hP.conjTranspose_eq, Matrix.mul_sub,
        ← Matrix.mul_assoc, hP.mul_self, sub_self, frobInner_zero_right]
    have h2 : C - P * C = (T - P * T) + (B₂ - P * B₂) := by rw [hB₂, Matrix.mul_sub]; abel
    have h3 : frobInner (T - P * T) (B₂ - P * B₂) = 0 := by
      rw [hP.frobInner_sub_mul_sub_mul, frobInner_sub_left, frobInner_mul_left,
        hP.conjTranspose_eq, hTPB, frobInner_truncatedSVD_sub C k, sub_zero]
    have h4 := hP.frobNorm_sq_eq_add B₂
    rw [Matrix.sub_mul, Matrix.one_mul] at h4
    rw [h1, frobNorm_sub_sq_of_frobInner_eq_zero h0, h2, frobNorm_add_sq_of_frobInner_eq_zero h3]
    linarith
  have hD : frobNorm (P * C - T) ^ 2 = frobNorm (T - P * T) ^ 2 + frobNorm (P * B₂) ^ 2 := by
    have h1 : P * C - T = P * B₂ - (T - P * T) := by rw [hB₂, Matrix.mul_sub]; abel
    have h0 : frobInner (P * B₂) (T - P * T) = 0 := by
      rw [frobInner_sub_right, frobInner_mul_left, frobInner_mul_left, hP.conjTranspose_eq,
        ← Matrix.mul_assoc, hP.mul_self, sub_self]
    rw [h1, frobNorm_sub_sq_of_frobInner_eq_zero h0]
    ring
  have hYT : frobInner (Y - T) E = frobInner (P * C - T) E + frobNorm (P * E) ^ 2 := by
    rw [hY', show P * C + P * E - T = (P * C - T) + P * E by abel, frobInner_add_left,
      ← frobInner_self, frobInner_mul_left P E (P * E), hP.conjTranspose_eq, ← Matrix.mul_assoc,
      hP.mul_self, frobInner_comm (P * E) E]
  -- the cross term sees rank `2k`, the noise term rank `k`
  have hDE : frobInner (P * C - T) E ≤
      √2 * √(k : ℝ) * frobNorm (P * C - T) * specNorm E := by
    have hrank : (P * C - T).rank ≤ 2 * k := (Matrix.rank_sub_le _ _).trans
      (by have := (Matrix.rank_mul_le_left P C).trans hrP; omega)
    have h := frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le hrank E
    rwa [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul zero_le_two] at h
  have hw : frobNorm (P * E) ^ 2 ≤ √(k : ℝ) ^ 2 * specNorm E ^ 2 := by
    rw [Real.sq_sqrt (Nat.cast_nonneg k)]
    exact (frobNorm_sq_le_rank_mul_specNorm_sq _).trans (mul_le_mul
      (by exact_mod_cast (Matrix.rank_mul_le_left P E).trans hrP)
      (pow_le_pow_left₀ (specNorm_nonneg _) (hP.specNorm_mul_le E) 2) (sq_nonneg _)
      (Nat.cast_nonneg k))
  -- Ky Fan for the rank-`k` projector `P`
  have hg : frobNorm (P * B₂) ≤ frobNorm (truncatedSVD B₂ k) := by
    have h1 := frobInner_le_frobNorm_mul_frobNorm_truncatedSVD_of_rank_le
      ((Matrix.rank_mul_le_left P B₂).trans hrP) B₂
    have h2 : frobInner (P * B₂) B₂ = frobNorm (P * B₂) ^ 2 := by
      rw [← frobInner_self, frobInner_mul_left P B₂ (P * B₂), frobInner_mul_left P B₂ B₂,
        hP.conjTranspose_eq, ← Matrix.mul_assoc, hP.mul_self]
    nlinarith [frobNorm_nonneg (P * B₂), frobNorm_nonneg (truncatedSVD B₂ k)]
  have h := le_add_mul_of_le_two_mul' (S := frobNorm (C - Y) ^ 2 - frobNorm B₂ ^ 2)
    (a := frobNorm (T - P * T) ^ 2) (w := frobNorm (P * E) ^ 2) (Real.sqrt_nonneg (k : ℝ))
    (specNorm_nonneg E) (frobNorm_nonneg _) (Real.sqrt_nonneg 2) (Real.sq_sqrt zero_le_two)
    hg (by linarith) (by linarith) hD hw
  rw [Real.sq_sqrt (Nat.cast_nonneg k)] at h
  linarith


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
  have hγ : frobNorm (truncatedSVD (B - truncatedSVD B k) k) ≤
      √(k : ℝ) * singularValues B k := by
    set M := B - truncatedSVD B k
    have hs : specNorm (truncatedSVD M k) ≤ singularValues B k := by
      rw [← specNorm_sub_truncatedSVD, ← singularValues_zero_eq_specNorm,
        ← singularValues_zero_eq_specNorm, singularValues_truncatedSVD]
      split_ifs
      · exact le_rfl
      · exact singularValues_nonneg _ _
    refine (frobNorm_le_sqrt_rank_mul_specNorm _).trans ?_
    gcongr
    exact_mod_cast rank_truncatedSVD_le M k
  have h := hY.frobNorm_sub_sq_le_add_specNorm_mul_frobNorm'
  have h2 := mul_le_mul_of_nonneg_left hγ
    (mul_nonneg (Real.sqrt_nonneg (k : ℝ)) (specNorm_nonneg N))
  rw [show √(k : ℝ) * specNorm N * (√(k : ℝ) * singularValues B k) =
    (√(k : ℝ) * √(k : ℝ)) * singularValues B k * specNorm N by ring,
    Real.mul_self_sqrt (Nat.cast_nonneg k)] at h2
  linarith

/-- The scalar absorption step of the localized perturbed truncation. -/
private theorem le_add_of_le_two_mul_add_window {D x y r ν k η θ μ q : ℝ} (hk : 0 ≤ k)
    (hμ : 0 ≤ μ) (hq : 0 ≤ q) (hθμ : 100 * μ < θ)
    (hD : D ≤ 2 * (x + y) + k * η ^ 2) (hx : |x| ≤ √(4 * k) * r * η)
    (hr : r ^ 2 ≤ 15 * D) (hy : |y| ≤ ν * (μ * (2 * θ))) (hν : ν ≤ 4 * q + 6 * (D / θ ^ 2)) :
    D ≤ 482 * k * η ^ 2 + 32 * θ * μ * q := by
  have hθ : 0 < θ := by linarith
  rcases le_or_gt D 0 with hD0 | hD0
  · nlinarith [mul_nonneg (mul_nonneg hθ.le hμ) hq, mul_nonneg hk (sq_nonneg η)]
  set s := √k
  have hs : s ^ 2 = k := Real.sq_sqrt hk
  have h4 : √(4 * k) = 2 * s := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  -- the off-window term, by Young's inequality
  have hx' : 2 * x ≤ r ^ 2 / 60 + 240 * k * η ^ 2 := by
    rw [h4] at hx
    nlinarith [le_abs_self x, sq_nonneg (r - 120 * s * η)]
  -- the window term, absorbed since `100 μ < θ`
  have hw : D / θ ^ 2 * θ ^ 2 = D := div_mul_cancel₀ D (by positivity)
  have hy' : 2 * y ≤ 16 * θ * μ * q + 24 / 100 * D := by
    have h1 : 2 * y ≤ 4 * θ * μ * (4 * q + 6 * (D / θ ^ 2)) := by
      nlinarith [le_abs_self y, mul_le_mul_of_nonneg_left hν (mul_nonneg hμ hθ.le)]
    have h2 : μ * θ * (D / θ ^ 2) ≤ θ / 100 * θ * (D / θ ^ 2) := by
      gcongr
      linarith
    nlinarith
  nlinarith

/-- The row spaces of the truncations are nested:
$\operatorname{range}\llbracket\mathbf{B}\rrbracket_a^{\mathsf{H}} \subseteq
\operatorname{range}\llbracket\mathbf{B}\rrbracket_b^{\mathsf{H}}$ for $a \le b$. -/
private theorem range_conjTranspose_truncatedSVD_le {m' n' : Type*} [Fintype m'] [Fintype n']
    (B : Matrix m' n' ℝ) {a b : ℕ} (hab : a ≤ b) :
    LinearMap.range (truncatedSVD B a)ᴴ.mulVecLin ≤
      LinearMap.range (truncatedSVD B b)ᴴ.mulVecLin := by
  have hPab : rangeProjector (truncatedSVD B a) * rangeProjector (truncatedSVD B b) =
      rangeProjector (truncatedSVD B a) :=
    rangeProjector_mul_rangeProjector_of_range_le' (range_truncatedSVD_mono B hab)
  refine range_le_iff_exists_mul.mpr ⟨rangeProjector (truncatedSVD B a), ?_⟩
  rw [← conjTranspose_rangeProjector, ← Matrix.conjTranspose_mul,
    ← rangeProjector_truncatedSVD_mul B b, ← Matrix.mul_assoc, hPab,
    rangeProjector_truncatedSVD_mul]

/-- The window part of the cross term: with $\mathbf{L} = \mathbf{P}_b - \mathbf{P}_a$ and
$\mathbf{L}' = \mathbf{P}'_b - \mathbf{P}'_a$,
$|\langle\mathbf{L}\mathbf{\Delta}\mathbf{B}\mathbf{L}', \mathbf{N}\rangle| \le
\|\mathbf{L}\mathbf{\Delta}\mathbf{L}\|_*\,\|\mathbf{L}\mathbf{N}\mathbf{L}'\|_2\,\sigma_a$. -/
private theorem abs_frobInner_mul_mul_le_nuclearNorm_mul {m' n' : Type*} [Fintype m'] [Fintype n']
    (B N : Matrix m' n' ℝ) {a b : ℕ} (hab : a ≤ b) (Δ : Matrix m' m' ℝ) :
    |frobInner ((rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a)) * Δ * B *
        (rangeProjector (truncatedSVD B b)ᴴ - rangeProjector (truncatedSVD B a)ᴴ)) N| ≤
      nuclearNorm ((rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a)) * Δ *
          (rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a))) *
        (specNorm ((rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a)) * N *
          (rangeProjector (truncatedSVD B b)ᴴ - rangeProjector (truncatedSVD B a)ᴴ)) *
          singularValues B a) := by
  set Pa := rangeProjector (truncatedSVD B a)
  set Pb := rangeProjector (truncatedSVD B b)
  have hPba : Pb * Pa = Pa :=
    rangeProjector_mul_rangeProjector_of_range_le (range_truncatedSVD_mono B hab)
  set L := Pb - Pa
  set L' := rangeProjector (truncatedSVD B b)ᴴ - rangeProjector (truncatedSVD B a)ᴴ
  have hLs : IsStarProjection L := (isStarProjection_rangeProjector _).sub_of_mul_eq_right
    (isStarProjection_rangeProjector _) hPba
  have hL's : IsStarProjection L' := (isStarProjection_rangeProjector _).sub_of_mul_eq_right
    (isStarProjection_rangeProjector _)
    (rangeProjector_mul_rangeProjector_of_range_le (range_conjTranspose_truncatedSVD_le B hab))
  have hLL : L * L = L := hLs.mul_self
  have hL'L' : L' * L' = L' := hL's.mul_self
  have hLh : Lᴴ = L := hLs.conjTranspose_eq
  have hL'h : L'ᴴ = L' := hL's.conjTranspose_eq
  have hLB : L * B = B * L' := by
    simp only [L, L', Matrix.sub_mul, Matrix.mul_sub, rangeProjector_truncatedSVD_mul,
      mul_rangeProjector_conjTranspose_truncatedSVD, Pa, Pb]
  have hL2 : ∀ X : Matrix m' n' ℝ, L * (L * X) = L * X := fun X => by
    rw [← Matrix.mul_assoc, hLL]
  have hLBL : L * (B * L') = B * L' := by rw [← hLB, hL2]
  have hBL : B * L' * L' = B * L' := by rw [Matrix.mul_assoc, hL'L']
  have hM : specNorm (B * L') ≤ singularValues B a := by
    rw [← hLB, ← specNorm_sub_truncatedSVD B a]
    have : L * B = Pb * (B - truncatedSVD B a) :=
      calc L * B = Pb * B - Pb * (Pa * B) := by rw [← Matrix.mul_assoc, hPba, Matrix.sub_mul]
        _ = _ := by rw [Matrix.mul_sub, ← rangeProjector_truncatedSVD_mul B a]
    rw [this]
    exact (isStarProjection_rangeProjector _).specNorm_mul_le _
  have hEq : frobInner (L * Δ * B * L') N =
      frobInner (L * Δ * L) (L * N * L' * (B * L')ᴴ) := by
    calc frobInner (L * Δ * B * L') N = frobInner (L * (L * Δ * L * (B * L'))) N := by
          congr 1
          simp only [Matrix.mul_assoc, hL2, hLBL]
      _ = _ := by
          rw [frobInner_mul_left, hLh, frobInner_mul_right]
          congr 1
          conv_lhs => rw [← hBL]
          rw [Matrix.conjTranspose_mul (B * L'), hL'h]
          simp only [Matrix.mul_assoc]
  rw [hEq]
  refine (abs_frobInner_le_nuclearNorm_mul_specNorm _ _).trans ?_
  gcongr
  refine (specNorm_mul_le _ _).trans ?_
  rw [specNorm_conjTranspose]
  gcongr

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
  classical
  have hab := hak.trans hkb
  have hZ := isStarProjection_rangeProjector Y
  have hZk : (rangeProjector Y).rank ≤ k := by rw [rank_rangeProjector]; exact hY.rank_le
  have hLs : IsStarProjection (rangeProjector (truncatedSVD B b) -
      rangeProjector (truncatedSVD B a)) :=
    (isStarProjection_rangeProjector _).sub_of_mul_eq_right (isStarProjection_rangeProjector _)
      (rangeProjector_mul_rangeProjector_of_range_le (range_truncatedSVD_mono B hab))
  have hL's : IsStarProjection (rangeProjector (truncatedSVD B b)ᴴ -
      rangeProjector (truncatedSVD B a)ᴴ) :=
    (isStarProjection_rangeProjector _).sub_of_mul_eq_right (isStarProjection_rangeProjector _)
      (rangeProjector_mul_rangeProjector_of_range_le (range_conjTranspose_truncatedSVD_le B hab))
  set θ := singularValues B (k - 1)
  set η := specNorm N
  set q : ℝ := ((min k (b - k) : ℕ) : ℝ)
  set μ := specNorm ((rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a)) * N *
    (rangeProjector (truncatedSVD B b)ᴴ - rangeProjector (truncatedSVD B a)ᴴ))
  have hη : 0 ≤ η := specNorm_nonneg N
  have hμ0 : 0 ≤ μ := specNorm_nonneg _
  have hμη : μ ≤ η := (hL's.specNorm_mul_right_le _).trans (hLs.specNorm_mul_le N)
  have hθ0 : 0 ≤ θ := singularValues_nonneg _ _
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hwin : 0 ≤ 40 * θ * q * μ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hθ0) hq0) hμ0
  rcases le_or_gt θ (100 * μ) with hA | hB
  · -- large noise: `θ ≤ 100 μ ≤ 100 η`
    have hσ : singularValues B k ≤ θ := singularValues_antitone B (Nat.sub_le k 1)
    have h1 : singularValues B k * η ≤ 100 * η ^ 2 := by
      nlinarith [singularValues_nonneg B k]
    nlinarith [hY.frobNorm_sub_sq_le_add_singularValues_mul_specNorm,
      mul_le_mul_of_nonneg_left h1 hk0, mul_nonneg hk0 (sq_nonneg η)]
  · -- small window noise: absorb the cross term
    have hθ : 0 < θ := by linarith
    have hBk : B - truncatedSVD B k = (1 - rangeProjector (truncatedSVD B k)) * B := by
      rw [Matrix.sub_mul, Matrix.one_mul, rangeProjector_truncatedSVD_mul]
    have hZN : frobNorm (rangeProjector Y * N) ^ 2 ≤ k * η ^ 2 := by
      refine (frobNorm_sq_le_rank_mul_specNorm_sq _).trans ?_
      exact mul_le_mul (Nat.cast_le.mpr ((Matrix.rank_mul_le_left _ _).trans hZk))
        (pow_le_pow_left₀ (specNorm_nonneg _) (hZ.specNorm_mul_le N) 2) (by positivity) hk0
    have hopt := hY.frobNorm_one_sub_rangeProjector_mul_sq_sub_le
    rw [← sub_add_cancel ((rangeProjector Y - rangeProjector (truncatedSVD B k)) * B)
      ((rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a)) *
        (rangeProjector Y - rangeProjector (truncatedSVD B k)) * B *
        (rangeProjector (truncatedSVD B b)ᴴ - rangeProjector (truncatedSVD B a)ᴴ)),
      frobInner_add_left] at hopt
    have hx := (abs_frobInner_le_nuclearNorm_mul_specNorm _ N).trans
      (mul_le_mul_of_nonneg_right ((nuclearNorm_le_sqrt_rank_mul_frobNorm _).trans
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (Nat.cast_le.mpr
          (rank_sub_mul_mul_le B k hZk (rangeProjector (truncatedSVD B b) -
            rangeProjector (truncatedSVD B a)) (rangeProjector (truncatedSVD B b)ᴴ -
              rangeProjector (truncatedSVD B a)ᴴ)))) (frobNorm_nonneg _))) hη)
    rw [Nat.cast_mul, Nat.cast_ofNat] at hx
    have hy := (abs_frobInner_mul_mul_le_nuclearNorm_mul B N hab
      (rangeProjector Y - rangeProjector (truncatedSVD B k))).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha₂ hμ0) (nuclearNorm_nonneg _))
    have hD := le_add_of_le_two_mul_add_window hk0 hμ0 hq0 hB
      (by nlinarith [sq_nonneg (frobNorm (rangeProjector (truncatedSVD B k) * N))]) hx
      (frobNorm_sub_mul_mul_sq_le B hk hak hkb ha ha₂ hb hZ hZk) hy
      (nuclearNorm_mul_sub_mul_le B hk hak hkb hθ hb hZ hZk)
    rw [hY.frobNorm_sub_sq_eq_add, hBk]
    nlinarith

end NLAlib