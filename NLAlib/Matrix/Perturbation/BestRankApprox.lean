/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.TruncationWindow

/-!
# Perturbed best rank-$k$ approximation

For $\mathbf{C}, \mathbf{E} \in \Bbbk^{m \times n}$ and any best rank-$k$ approximation
$\mathbf{Y}$ of $\mathbf{C} + \mathbf{E}$, the error $\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}}^2$
exceeds the optimal $\|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}}^2$ by a
cross term and a noise term. The next-$k$ form bounds the cross term by the spectral norm of
$\mathbf{E}$ and the next $k$ singular values of $\mathbf{C}$. The localized form sees the noise
in the cross term only through its compression $\mu$ to the left and
right singular subspaces of $\mathbf{C}$ whose singular values lie within a factor $2$ of
$\theta = \sigma_{k-1}(\mathbf{C})$:
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}}^2 \le
\|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}}^2 + 500k\,\|\mathbf{E}\|_2^2 +
40\,\theta\min(k, b - k)\,\mu\,,$$
with the window $a \le k \le b$ of `NLAlib.exists_singularValues_window`. The window tools are in
`NLAlib/Matrix/Perturbation/TruncationWindow.lean`. Every statement holds for every best
approximation, so in particular for every choice of `truncatedSVD`. Design:
`docs/design/research/TruncatedGN-Upper.md` (research note OP6 of the NLAlib workflow).

## Main results

* `NLAlib.IsBestRankApprox.frobNorm_sub_sq_sub_le_two_mul_frobInner`: the optimality step.
* `NLAlib.IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_mul_frobNorm`: perturbed truncation
  with the next-$k$ tail in the cross term.
* `NLAlib.IsBestRankApprox.frobNorm_sub_sq_eq_add`: the excess identity.
* `NLAlib.IsBestRankApprox.frobNorm_one_sub_rangeProjector_mul_sq_sub_le`: the optimality of the
  perturbed truncation in projector form.
* `NLAlib.IsBestRankApprox.frobNorm_sub_sq_le_add_singularValues_mul_specNorm`: the large-noise
  form.
* `NLAlib.IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_sq_add_window`: the localized
  perturbed truncation.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The scalar step of the next-$k$ perturbed truncation. -/
private theorem le_add_mul_of_le_two_mul {S a w u q γ s r e : ℝ} (hs : 0 ≤ s) (he : 0 ≤ e)
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

/-- The optimality step of perturbed truncation: for $\mathbf{C}, \mathbf{E} \in
\Bbbk^{m \times n}$ and any best rank-$k$ approximation $\mathbf{Y}$ of
$\mathbf{C} + \mathbf{E}$,
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}}^2 -
\|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}}^2 \le
2\langle\mathbf{Y} - \llbracket\mathbf{C}\rrbracket_k, \mathbf{E}\rangle_{\mathsf{F}}\,.$$ -/
theorem IsBestRankApprox.frobNorm_sub_sq_sub_le_two_mul_frobInner
    {C E Y : Matrix m n 𝕜} {k : ℕ} (hY : IsBestRankApprox (C + E) k Y) :
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

/-- Perturbed truncation with the next-$k$ tail: for $\mathbf{C}, \mathbf{E} \in
\Bbbk^{m \times n}$ and any best rank-$k$ approximation $\mathbf{Y}$ of
$\mathbf{C} + \mathbf{E}$, with $\gamma_k =
\|\llbracket\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\rrbracket_k\|_{\mathsf{F}}$,
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}}^2 \le
\|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}}^2 +
4\sqrt{k}\,\|\mathbf{E}\|_2\,\gamma_k + 12k\,\|\mathbf{E}\|_2^2\,.$$ -/
theorem IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_mul_frobNorm
    {C E Y : Matrix m n 𝕜} {k : ℕ} (hY : IsBestRankApprox (C + E) k Y) :
    frobNorm (C - Y) ^ 2 ≤ frobNorm (C - truncatedSVD C k) ^ 2 +
      4 * √(k : ℝ) * specNorm E * frobNorm (truncatedSVD (C - truncatedSVD C k) k) +
      12 * k * specNorm E ^ 2 := by
  classical
  set T := truncatedSVD C k with hT
  set B₂ := C - T with hB₂
  set P := rangeProjector Y with hPdef
  have hP : IsStarProjection P := isStarProjection_rangeProjector Y
  have hPY : P * (C + E) = Y := hY.rangeProjector_self_mul
  have hY' : Y = P * C + P * E := by rw [← hPY, Matrix.mul_add]
  have hrP : P.rank ≤ k := by rw [hPdef, rank_rangeProjector]; exact hY.rank_le
  have hrT : T.rank ≤ k := rank_truncatedSVD_le C k
  -- (D1) the optimality of `Y` against `T`
  have hS : frobNorm (C - Y) ^ 2 - frobNorm B₂ ^ 2 ≤ 2 * frobInner (Y - T) E :=
    hY.frobNorm_sub_sq_sub_le_two_mul_frobInner
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
  have h := le_add_mul_of_le_two_mul (S := frobNorm (C - Y) ^ 2 - frobNorm B₂ ^ 2)
    (a := frobNorm (T - P * T) ^ 2) (w := frobNorm (P * E) ^ 2) (Real.sqrt_nonneg (k : ℝ))
    (specNorm_nonneg E) (frobNorm_nonneg _) (Real.sqrt_nonneg 2) (Real.sq_sqrt zero_le_two)
    hg (by linarith) (by linarith) hD hw
  rw [Real.sq_sqrt (Nat.cast_nonneg k)] at h
  linarith

end RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-! ### The excess and the optimality of the perturbed truncation -/

/-- The excess identity: for $\mathbf{B}, \mathbf{N} \in \Bbbk^{m \times n}$ and a best
rank-$k$ approximation $\mathbf{Y}$ of $\mathbf{B} + \mathbf{N}$, with
$\widehat{\mathbf{P}} = \mathbf{P}_{\mathbf{Y}}$,
$$\|\mathbf{B} - \mathbf{Y}\|_{\mathsf{F}}^2 =
\|(\mathbf{I} - \widehat{\mathbf{P}})\mathbf{B}\|_{\mathsf{F}}^2 +
\|\widehat{\mathbf{P}}\mathbf{N}\|_{\mathsf{F}}^2\,.$$
No printed source. -/
theorem IsBestRankApprox.frobNorm_sub_sq_eq_add {B N Y : Matrix m n 𝕜} {k : ℕ}
    (hY : IsBestRankApprox (B + N) k Y) :
    frobNorm (B - Y) ^ 2 =
      frobNorm ((1 - rangeProjector Y) * B) ^ 2 + frobNorm (rangeProjector Y * N) ^ 2 := by
  classical
  have hZ := isStarProjection_rangeProjector Y
  have hZY : rangeProjector Y * (B + N) = Y := hY.rangeProjector_self_mul
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

/-- Pythagoras for the complement of a star projection, in the form `(1 - Q) * A`. -/
private theorem frobNorm_one_sub_mul_sq {Q : Matrix m m 𝕜} (hQ : IsStarProjection Q)
    (A : Matrix m n 𝕜) :
    frobNorm ((1 - Q) * A) ^ 2 = frobNorm A ^ 2 - frobNorm (Q * A) ^ 2 := by
  have h := hQ.frobNorm_sq_eq_add A
  linarith

omit [DecidableEq m] in
/-- Expansion of `‖Q (B + N)‖²` for a star projection `Q`. -/
private theorem frobNorm_mul_add_sq {Q : Matrix m m 𝕜} (hQ : IsStarProjection Q)
    (B N : Matrix m n 𝕜) :
    frobNorm (Q * (B + N)) ^ 2 =
      frobNorm (Q * B) ^ 2 + 2 * frobInner (Q * B) N + frobNorm (Q * N) ^ 2 := by
  classical
  have hcross : frobInner (Q * B) (Q * N) = frobInner (Q * B) N := by
    rw [frobInner_mul_left, hQ.conjTranspose_eq, ← Matrix.mul_assoc, hQ.mul_self,
      frobInner_mul_left, hQ.conjTranspose_eq]
  rw [Matrix.mul_add, frobNorm_add_sq, hcross]

/-- The optimality of the perturbed truncation: for $\mathbf{B}, \mathbf{N} \in
\Bbbk^{m \times n}$ and a best rank-$k$ approximation $\mathbf{Y}$ of
$\mathbf{B} + \mathbf{N}$, with $\widehat{\mathbf{P}} = \mathbf{P}_{\mathbf{Y}}$ and
$\mathbf{P}$ the range projector of $\llbracket\mathbf{B}\rrbracket_k$,
$$\|(\mathbf{I} - \widehat{\mathbf{P}})\mathbf{B}\|_{\mathsf{F}}^2 -
\|(\mathbf{I} - \mathbf{P})\mathbf{B}\|_{\mathsf{F}}^2 \le
2\langle(\widehat{\mathbf{P}} - \mathbf{P})\mathbf{B}, \mathbf{N}\rangle_{\mathsf{F}} +
\|\widehat{\mathbf{P}}\mathbf{N}\|_{\mathsf{F}}^2 - \|\mathbf{P}\mathbf{N}\|_{\mathsf{F}}^2\,.$$
No printed source. -/
theorem IsBestRankApprox.frobNorm_one_sub_rangeProjector_mul_sq_sub_le {B N Y : Matrix m n 𝕜}
    {k : ℕ} (hY : IsBestRankApprox (B + N) k Y) :
    frobNorm ((1 - rangeProjector Y) * B) ^ 2 -
        frobNorm ((1 - rangeProjector (truncatedSVD B k)) * B) ^ 2 ≤
      2 * frobInner ((rangeProjector Y - rangeProjector (truncatedSVD B k)) * B) N +
        frobNorm (rangeProjector Y * N) ^ 2 -
        frobNorm (rangeProjector (truncatedSVD B k) * N) ^ 2 := by
  have hZ := isStarProjection_rangeProjector Y
  have hP := isStarProjection_rangeProjector (truncatedSVD B k)
  have hYM : (B + N) - Y = (1 - rangeProjector Y) * (B + N) := by
    rw [Matrix.sub_mul, Matrix.one_mul, hY.rangeProjector_self_mul]
  have hrank : (rangeProjector (truncatedSVD B k) * (B + N)).rank ≤ k :=
    (Matrix.rank_mul_le_left _ _).trans (by
      rw [rank_rangeProjector]; exact rank_truncatedSVD_le B k)
  have hopt := pow_le_pow_left₀ (frobNorm_nonneg _)
    (hY.frobNorm_sub_le _ hrank) 2
  have hPM : (B + N) - rangeProjector (truncatedSVD B k) * (B + N) =
      (1 - rangeProjector (truncatedSVD B k)) * (B + N) := by
    rw [Matrix.sub_mul, Matrix.one_mul]
  rw [hYM, hPM, frobNorm_one_sub_mul_sq hZ, frobNorm_one_sub_mul_sq hP] at hopt
  rw [frobNorm_one_sub_mul_sq hZ, frobNorm_one_sub_mul_sq hP, Matrix.sub_mul,
    frobInner_sub_left]
  rw [frobNorm_mul_add_sq hZ, frobNorm_mul_add_sq hP] at hopt
  linarith

/-! ### Large noise and the localized perturbed truncation -/

omit [DecidableEq m] in
/-- Perturbed truncation, large-noise form: for $\mathbf{B}, \mathbf{N} \in
\Bbbk^{m \times n}$ and a best rank-$k$ approximation $\mathbf{Y}$ of
$\mathbf{B} + \mathbf{N}$,
$$\|\mathbf{B} - \mathbf{Y}\|_{\mathsf{F}}^2 \le
\|\mathbf{B} - \llbracket\mathbf{B}\rrbracket_k\|_{\mathsf{F}}^2 +
4k\,\sigma_k(\mathbf{B})\,\|\mathbf{N}\|_2 + 12k\,\|\mathbf{N}\|_2^2\,.$$
Since the next $k$ singular values are at most $\sigma_k(\mathbf{B})$, this follows from
`NLAlib.IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_mul_frobNorm`. No printed source. -/
theorem IsBestRankApprox.frobNorm_sub_sq_le_add_singularValues_mul_specNorm
    {B N Y : Matrix m n 𝕜} {k : ℕ} (hY : IsBestRankApprox (B + N) k Y) :
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
  have h := hY.frobNorm_sub_sq_le_add_specNorm_mul_frobNorm
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
    (B : Matrix m' n' 𝕜) {a b : ℕ} (hab : a ≤ b) :
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
    (B N : Matrix m' n' 𝕜) {a b : ℕ} (hab : a ≤ b) (Δ : Matrix m' m' 𝕜) :
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
  have hL2 : ∀ X : Matrix m' n' 𝕜, L * (L * X) = L * X := fun X => by
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
/-- **Localized hard truncation**: for $\mathbf{B}, \mathbf{N} \in
\Bbbk^{m \times n}$, $1 \le k$, $\theta = \sigma_{k-1}(\mathbf{B})$, a window
$a \le k \le b$ with $2\theta \le \sigma_i(\mathbf{B})$ for $i < a$,
$\sigma_a(\mathbf{B}) \le 2\theta$ and $\sigma_b(\mathbf{B}) \le \theta/2$, and a best rank-$k$
approximation $\mathbf{Y}$ of $\mathbf{B} + \mathbf{N}$, with $\mathbf{P}_i$, $\mathbf{P}'_i$
the range projectors of $\llbracket\mathbf{B}\rrbracket_i$ and of its conjugate transpose and
$\mu = \|(\mathbf{P}_b - \mathbf{P}_a)\mathbf{N}(\mathbf{P}'_b - \mathbf{P}'_a)\|_2$,
$$\|\mathbf{B} - \mathbf{Y}\|_{\mathsf{F}}^2 \le
\|\mathbf{B} - \llbracket\mathbf{B}\rrbracket_k\|_{\mathsf{F}}^2 + 500k\,\|\mathbf{N}\|_2^2 +
40\,\theta\min(k, b - k)\,\mu\,.$$
The noise enters the cross term only through its compression $\mu$ to the singular subspaces
within a factor $2$ of the truncation level, and with weight $\min(k, b - k)$ instead of $k$.
The proof gives $483$ and $32$ in place of $500$ and $40$. No printed source; research note
OP6, Proposition 3.6, has $965$ in place of $500$, from a cruder split.
Result: localized-hard-truncation -/
theorem IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_sq_add_window {B N Y : Matrix m n 𝕜}
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
