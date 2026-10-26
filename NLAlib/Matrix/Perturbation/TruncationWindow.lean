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
# The window of singular values at the truncation level

For $\mathbf{B} \in \Bbbk^{m \times n}$ ($\Bbbk$ any `RCLike` field),
$k \ge 1$ and $\theta = \sigma_{k-1}(\mathbf{B})$
(indices from $0$), the window $a \le k \le b$ collects the singular values in
$[\theta/2, 2\theta]$ (`NLAlib.exists_singularValues_window`). The window projectors are
differences of range projectors of truncations of $\mathbf{B}$, all built from the one chosen SVD
(`NLAlib.truncatedSVD_def`), so no new definition is needed: $\mathbf{L} = \mathbf{P}_b -
\mathbf{P}_a$ on the left and $\mathbf{L}' = \mathbf{P}'_b - \mathbf{P}'_a$ on the right, with
$\mathbf{P}_i$, $\mathbf{P}'_i$ the range projectors of $\llbracket\mathbf{B}\rrbracket_i$ and of
its conjugate transpose. For an orthogonal projector $\mathbf{Z}$ of rank at most $k$, the
subspace error
$D = \|(\mathbf{I} - \mathbf{Z})\mathbf{B}\|_{\mathsf{F}}^2 - \|(\mathbf{I} -
\mathbf{P}_k)\mathbf{B}\|_{\mathsf{F}}^2$ controls the part of $\mathbf{Z} - \mathbf{P}_k$ outside
the window (in Frobenius norm) and its compression to the window (in nuclear norm). These are the
deterministic tools of the localized perturbed truncation
`NLAlib.IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_sq_add_window`. Design:
`docs/design/research/TruncatedGN-Upper.md` (research note OP6 of the NLAlib workflow, §3).

## Main results

* `NLAlib.sq_mul_frobNorm_mul_sub_rangeProjector_sq_le`: a singular-value floor on a block.
* `NLAlib.exists_singularValues_window`: the window $[\theta/2, 2\theta]$.
* `NLAlib.frobNorm_one_sub_mul_sq_sub_eq_add`: the weighted identity for the subspace error.
* `NLAlib.mul_frobNorm_mul_truncatedSVD_sq_add_le`, `NLAlib.mul_frobNorm_mul_one_sub_sq_add_le`:
  the head and tail weights.
* `NLAlib.frobNorm_sub_mul_mul_sq_le`, `NLAlib.rank_sub_mul_mul_le`: the off-window part.
* `NLAlib.nuclearNorm_mul_sub_mul_le`: the trace balance on the window.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-! ### Blocks of the chosen SVD -/

omit [DecidableEq m] in
/-- A singular-value floor on a block: for $\mathbf{B} \in \Bbbk^{m \times n}$,
$a \le j$, $c \ge 0$ with $c \le \sigma_i(\mathbf{B})$ for $a \le i < j$, and any
$\mathbf{W}$, writing $\mathbf{P}_i$ for the range projector of
$\llbracket\mathbf{B}\rrbracket_i$,
$$c^2\,\|\mathbf{W}(\mathbf{P}_j - \mathbf{P}_a)\|_{\mathsf{F}}^2 \le
\|\mathbf{W}(\llbracket\mathbf{B}\rrbracket_j - \llbracket\mathbf{B}\rrbracket_a)
\|_{\mathsf{F}}^2\,.$$
Both truncations come from the one chosen SVD, so their difference is the block
$\sum_{a \le i < j}\sigma_i\mathbf{u}_i\mathbf{v}_i^{\mathsf{H}}$ and
$\mathbf{P}_j - \mathbf{P}_a$ projects onto the span of its left singular vectors.
No printed source. -/
theorem sq_mul_frobNorm_mul_sub_rangeProjector_sq_le {p : Type*} [Fintype p] (B : Matrix m n 𝕜)
    (W : Matrix p m 𝕜) {a j : ℕ} (haj : a ≤ j) {c : ℝ} (hc : 0 ≤ c)
    (hσ : ∀ i, a ≤ i → i < j → c ≤ singularValues B i) :
    c ^ 2 * frobNorm (W * (rangeProjector (truncatedSVD B j) -
        rangeProjector (truncatedSVD B a))) ^ 2 ≤
      frobNorm (W * (truncatedSVD B j - truncatedSVD B a)) ^ 2 := by
  have h := isSVD_svdU_svdV B
  have hU := h.hasOrthonormalCols_left
  have hV := h.hasOrthonormalCols_right
  set U := svdU B
  set V := svdV B
  have hdiag : ∀ d : Fin (min (Fintype.card m) (Fintype.card n)) → 𝕜,
      rangeProjector (Matrix.diagonal d * Vᴴ) =
        Matrix.diagonal (fun i => if d i = 0 then 0 else 1) := by
    intro d
    set e : Fin (min (Fintype.card m) (Fintype.card n)) → 𝕜 := fun i => if d i = 0 then 0 else 1
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
  set s : ℕ → Fin (min (Fintype.card m) (Fintype.card n)) → 𝕜 :=
    fun k i => if (i : ℕ) < k then ((singularValues B i : ℝ) : 𝕜) else 0
  set e : ℕ → Fin (min (Fintype.card m) (Fintype.card n)) → 𝕜 :=
    fun k i => if s k i = 0 then 0 else 1
  have hT : ∀ k, truncatedSVD B k = U * (Matrix.diagonal (s k) * Vᴴ) := fun k => by
    rw [truncatedSVD_def, Matrix.mul_assoc]
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
    frobNorm_sq_eq_sum, frobNorm_sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Matrix.mul_diagonal, Pi.sub_apply]
  have key : c ^ 2 * ‖e j i - e a i‖ ^ 2 ≤ ‖s j i - s a i‖ ^ 2 := by
    by_cases hia : (i : ℕ) < a
    · simp [s, e, hia, hia.trans_le haj]
    by_cases hij : (i : ℕ) < j
    · by_cases h0 : singularValues B i = 0
      · simp [s, e, hia, hij, h0]
      · have := hσ i (not_lt.mp hia) hij
        simp [s, e, hia, hij, h0, abs_of_nonneg (singularValues_nonneg B i)]
        nlinarith
    · simp [s, e, hia, hij]
  rw [norm_mul, norm_mul, mul_pow, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg ‖(W * U) p i‖)]

omit [DecidableEq m] in
/-- The window of the truncation level: for $\mathbf{B} \in \Bbbk^{m \times n}$ and
$k \ge 1$, with $\theta = \sigma_{k-1}(\mathbf{B})$, there are $a \le k \le b$ with
$2\theta \le \sigma_i(\mathbf{B})$ for $i < a$, $\sigma_a(\mathbf{B}) \le 2\theta$,
$\sigma_b(\mathbf{B}) \le \theta/2$ and
$$(b - k)\,\theta^2 \le 4\,\|\mathbf{B} - \llbracket\mathbf{B}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
No printed source. -/
theorem exists_singularValues_window (B : Matrix m n 𝕜) {k : ℕ} (hk : 1 ≤ k) :
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

/-! ### The weighted identity and its two weights -/

/-- The weighted identity: for $\mathbf{B} \in \Bbbk^{m \times n}$, an orthogonal
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
No printed source. -/
theorem frobNorm_one_sub_mul_sq_sub_eq_add (B : Matrix m n 𝕜) (k : ℕ) {Z : Matrix m m 𝕜}
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
    linarith [(isStarProjection_rangeProjector (truncatedSVD B k)).frobNorm_sq_eq_add_mul_right Z]
  have hk1 : Z * B * (1 - rangeProjector (truncatedSVD B k)ᴴ) = Z * (B - truncatedSVD B k) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hBP, Matrix.mul_sub]
  have hk2 : Z * B * rangeProjector (truncatedSVD B k)ᴴ = Z * truncatedSVD B k := by
    rw [Matrix.mul_assoc, hBP]
  have hR4 : frobNorm (Z * (B - truncatedSVD B k)) ^ 2 =
      frobNorm (Z * B) ^ 2 - frobNorm (Z * truncatedSVD B k) ^ 2 := by
    have e := (isStarProjection_rangeProjector (truncatedSVD B k)ᴴ).frobNorm_sq_eq_add_mul_right
      (Z * B)
    rw [hk1, hk2] at e
    linarith
  rw [hL, hPB, hR1, hR2, hR3, hR4]
  ring

omit [DecidableEq m] in
/-- The head weight: for $\mathbf{B} \in \Bbbk^{m \times n}$, $1 \le k$,
$\theta = \sigma_{k-1}(\mathbf{B})$, $a \le k$ with $2\theta \le \sigma_i(\mathbf{B})$ for
$i < a$, and any $\mathbf{W}$, writing $\mathbf{B}_i = \llbracket\mathbf{B}\rrbracket_i$ and
$\mathbf{P}_i$ for its range projector,
$$\tfrac38\|\mathbf{W}\mathbf{B}_a\|_{\mathsf{F}}^2 +
\tfrac32\theta^2\|\mathbf{W}\mathbf{P}_a\|_{\mathsf{F}}^2 \le
\|\mathbf{W}\mathbf{B}_k\|_{\mathsf{F}}^2 - \theta^2\|\mathbf{W}\mathbf{P}_k\|_{\mathsf{F}}^2\,.$$
No printed source. -/
theorem mul_frobNorm_mul_truncatedSVD_sq_add_le (B : Matrix m n 𝕜) {k a : ℕ} (hk : 1 ≤ k)
    (hak : a ≤ k) (ha : ∀ i < a, 2 * singularValues B (k - 1) ≤ singularValues B i)
    (W : Matrix m m 𝕜) :
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

/-- The tail weight: for $\mathbf{B} \in \Bbbk^{m \times n}$, $1 \le k$,
$\theta = \sigma_{k-1}(\mathbf{B})$, $b \ge k$ with $\sigma_b(\mathbf{B}) \le \theta/2$, and any
$\mathbf{W}$, writing $\mathbf{B}_i = \llbracket\mathbf{B}\rrbracket_i$ and $\mathbf{P}_i$ for
its range projector,
$$\tfrac38\theta^2\|\mathbf{W}(\mathbf{I} - \mathbf{P}_b)\|_{\mathsf{F}}^2 +
\tfrac32\|\mathbf{W}(\mathbf{B} - \mathbf{B}_b)\|_{\mathsf{F}}^2 \le
\theta^2\|\mathbf{W}(\mathbf{I} - \mathbf{P}_k)\|_{\mathsf{F}}^2 -
\|\mathbf{W}(\mathbf{B} - \mathbf{B}_k)\|_{\mathsf{F}}^2\,.$$
No printed source. -/
theorem mul_frobNorm_mul_one_sub_sq_add_le (B : Matrix m n 𝕜) {k b : ℕ} (hk : 1 ≤ k)
    (hkb : k ≤ b) (hb : singularValues B b ≤ singularValues B (k - 1) / 2)
    (W : Matrix m m 𝕜) :
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
private theorem rangeProjector_truncatedSVD_mul_of_le (B : Matrix m n 𝕜) {i j : ℕ}
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
private theorem sub_truncatedSVD_mul_conjTranspose_of_le (B : Matrix m n 𝕜) {i j : ℕ}
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
private theorem frobNorm_one_sub_sub_mul_mul_sub_sq_le {Pa Pb Z : Matrix m m 𝕜}
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
private theorem sq_singularValues_mul_frobNorm_sq_sub_nonneg (B : Matrix m n 𝕜) {k : ℕ}
    (hk : 1 ≤ k) {Z : Matrix m m 𝕜} (hZ : IsStarProjection Z) (hZk : Z.rank ≤ k) :
    0 ≤ singularValues B (k - 1) ^ 2 *
      (frobNorm (rangeProjector (truncatedSVD B k)) ^ 2 - frobNorm Z ^ 2) := by
  rcases (singularValues_nonneg B (k - 1)).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · have hr := (singularValues_pos_iff B).1 h0
    rw [frobNorm_rangeProjector_sq, rank_truncatedSVD, min_eq_left (by omega),
      hZ.frobNorm_sq_eq_rank]
    exact mul_nonneg (sq_nonneg _) (sub_nonneg.2 (by exact_mod_cast hZk))

/-- The off-window part of the subspace error is controlled by the misalignment: for
$\mathbf{B} \in \Bbbk^{m \times n}$, $1 \le k$, $\theta = \sigma_{k-1}(\mathbf{B})$, a window
$a \le k \le b$ with $2\theta \le \sigma_i(\mathbf{B})$ for $i < a$, $\sigma_a(\mathbf{B}) \le
2\theta$ and $\sigma_b(\mathbf{B}) \le \theta/2$, and an orthogonal projector $\mathbf{Z}$ of
rank at most $k$, with $\mathbf{P}_i$, $\mathbf{P}'_i$ the range projectors of
$\llbracket\mathbf{B}\rrbracket_i$ and of its conjugate transpose, $\mathbf{L} = \mathbf{P}_b -
\mathbf{P}_a$, $\mathbf{L}' = \mathbf{P}'_b - \mathbf{P}'_a$ and
$\mathbf{\Delta} = \mathbf{Z} - \mathbf{P}_k$,
$$\|\mathbf{\Delta}\mathbf{B} - \mathbf{L}\mathbf{\Delta}\mathbf{B}\mathbf{L}'\|_{\mathsf{F}}^2
\le 15\bigl(\|(\mathbf{I} - \mathbf{Z})\mathbf{B}\|_{\mathsf{F}}^2 -
\|(\mathbf{I} - \mathbf{P}_k)\mathbf{B}\|_{\mathsf{F}}^2\bigr)\,.$$
No printed source; it is research note OP6, Lemma 3.4(b). -/
theorem frobNorm_sub_mul_mul_sq_le (B : Matrix m n 𝕜) {k a b : ℕ} (hk : 1 ≤ k) (hak : a ≤ k)
    (hkb : k ≤ b) (ha : ∀ i < a, 2 * singularValues B (k - 1) ≤ singularValues B i)
    (ha₂ : singularValues B a ≤ 2 * singularValues B (k - 1))
    (hb : singularValues B b ≤ singularValues B (k - 1) / 2) {Z : Matrix m m 𝕜}
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
    have h6 : (frobNorm ((1 - (Pb - Pa)) * Z * (Pb - Pa)) * (2 * θ)) ^ 2 =
        4 * θ ^ 2 * frobNorm ((1 - (Pb - Pa)) * Z * (Pb - Pa)) ^ 2 := by ring
    linarith [pow_le_pow_left₀ (frobNorm_nonneg _) hw 2]
  linarith [mul_nonneg (sq_nonneg θ) (sq_nonneg (frobNorm ((1 - Z) * Pa))),
    mul_nonneg (sq_nonneg θ) (sq_nonneg (frobNorm (Z * (1 - Pb)))),
    sq_nonneg (frobNorm ((1 - Z) * Ba)), sq_nonneg (frobNorm (Z * (B - Bb)))]

omit [DecidableEq m] in
/-- The off-window part has rank at most $4k$: for $\mathbf{B} \in \Bbbk^{m \times n}$,
any $\mathbf{Z}$ of rank at most $k$, any $a, b$ and any
$\mathbf{L}$, $\mathbf{L}'$, with $\mathbf{\Delta} = \mathbf{Z} - \mathbf{P}_k$
($\mathbf{P}_k$ the range projector of $\llbracket\mathbf{B}\rrbracket_k$),
$$\operatorname{rank}(\mathbf{\Delta}\mathbf{B} - \mathbf{L}\mathbf{\Delta}\mathbf{B}\mathbf{L}')
\le 4k\,.$$
No printed source. -/
theorem rank_sub_mul_mul_le (B : Matrix m n 𝕜) (k : ℕ) {Z : Matrix m m 𝕜} (hZk : Z.rank ≤ k)
    (L : Matrix m m 𝕜) (L' : Matrix n n 𝕜) :
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
private theorem nuclearNorm_mul_mul_eq_frobNorm_sq {Q R : Matrix m m 𝕜}
    (hQ : IsStarProjection Q) (hR : IsStarProjection R) :
    nuclearNorm (R * Q * R) = frobNorm (Q * R) ^ 2 := by
  rw [← nuclearNorm_conjTranspose_mul_self, Matrix.conjTranspose_mul, hQ.conjTranspose_eq,
    hR.conjTranspose_eq, ← Matrix.mul_assoc, Matrix.mul_assoc R Q Q, hQ.mul_self]

/-- The window compression for nested orthogonal projectors
$\mathbf{P}_a \le \mathbf{P} \le \mathbf{P}_b$ and an orthogonal projector $\mathbf{Z}$, with
$\mathbf{L} = \mathbf{P}_b - \mathbf{P}_a$:
$$\|\mathbf{L}(\mathbf{Z} - \mathbf{P})\mathbf{L}\|_* \le
(\|\mathbf{P}_b\|_{\mathsf{F}}^2 - \|\mathbf{P}\|_{\mathsf{F}}^2) +
(\|\mathbf{P}_b\|_{\mathsf{F}}^2 - \|\mathbf{Z}\|_{\mathsf{F}}^2) +
\|\mathbf{Z}(\mathbf{I} - \mathbf{P}_b)\|_{\mathsf{F}}^2\,.$$ -/
private theorem nuclearNorm_mul_sub_mul_le_of_mul_eq {Pa P Pb Z : Matrix m m 𝕜}
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
  have := hPb.frobNorm_sq_eq_add_mul_right Z
  linarith

/-- The trace balance on the window: for $\mathbf{B} \in \Bbbk^{m \times n}$, $1 \le k$,
$\theta = \sigma_{k-1}(\mathbf{B}) > 0$, $a \le k \le b$ with $\sigma_b(\mathbf{B}) \le
\theta/2$, and an orthogonal projector $\mathbf{Z}$ of rank at most $k$, with $\mathbf{P}_i$ the
range projector of $\llbracket\mathbf{B}\rrbracket_i$, $\mathbf{L} = \mathbf{P}_b -
\mathbf{P}_a$ and $D = \|(\mathbf{I} - \mathbf{Z})\mathbf{B}\|_{\mathsf{F}}^2 -
\|(\mathbf{I} - \mathbf{P}_k)\mathbf{B}\|_{\mathsf{F}}^2$,
$$\|\mathbf{L}(\mathbf{Z} - \mathbf{P}_k)\mathbf{L}\|_* \le 4\min(k, b - k) +
6\,\frac{D}{\theta^2}\,.$$
No printed source; research note OP6, Lemma 3.5, proves the sharper
$2\min(k, b - k) + \tfrac43 D/\theta^2$ through Weyl's inequalities. -/
theorem nuclearNorm_mul_sub_mul_le (B : Matrix m n 𝕜) {k a b : ℕ} (hk : 1 ≤ k) (hak : a ≤ k)
    (hkb : k ≤ b) (hθ : 0 < singularValues B (k - 1))
    (hb : singularValues B b ≤ singularValues B (k - 1) / 2) {Z : Matrix m m 𝕜}
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

end NLAlib
