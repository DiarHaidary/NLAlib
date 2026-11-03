/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.TruncationWindow

/-!
# Nuclear norm of a reciprocal truncation window

A reciprocal spectral cutoff gives a compressed nuclear-norm bound with the competing rank
and the normalized subspace-error excess. The proof uses nested orthogonal projectors and
the weighted tail estimate, over any RCLike field and arbitrary finite index types.
Design: docs/design/research/Nystrom-Constants.md.

## Main results

* [Tail weight](https://nla-lib.org/explore/#d/NLAlib.mul_frobNorm_mul_one_sub_sq_le_of_one_lt).
* [Rank deficit](https://nla-lib.org/explore/#d/NLAlib.frobNorm_sq_sub_add_mul_le_div).
* [Compressed nuclear norm](https://nla-lib.org/explore/#d/NLAlib.nuclearNorm_mul_sub_mul_le_of_one_lt).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- The unsplit reciprocal-window tail weight: for $\mathbf{B}\in\Bbbk^{m\times n}$,
$k\ge1$, $b\ge k$, $c>1$, $\theta=\sigma_{k-1}(\mathbf{B})$,
$\sigma_b(\mathbf{B})\le\theta/c$, any $\mathbf{W}$ and
$\mathbf{P}_j=\mathbf{P}_{\llbracket\mathbf{B}\rrbracket_j}$,
$$(1-c^{-2})\theta^2\|\mathbf{W}(\mathbf{I}-\mathbf{P}_b)\|_{\mathsf{F}}^2
\le \theta^2\|\mathbf{W}(\mathbf{I}-\mathbf{P}_k)\|_{\mathsf{F}}^2
-\|\mathbf{W}(\mathbf{B}-\llbracket\mathbf{B}\rrbracket_k)\|_{\mathsf{F}}^2\,.$$
No printed source. -/
theorem mul_frobNorm_mul_one_sub_sq_le_of_one_lt (B : Matrix m n 𝕜) {k b : ℕ}
    (hk : 1 ≤ k) (hkb : k ≤ b) {c : ℝ} (hc : 1 < c)
    (hb : singularValues B b ≤ singularValues B (k - 1) / c) (W : Matrix m m 𝕜) :
    (1 - c⁻¹ ^ 2) * singularValues B (k - 1) ^ 2 *
        frobNorm (W * (1 - rangeProjector (truncatedSVD B b))) ^ 2 ≤
      singularValues B (k - 1) ^ 2 *
          frobNorm (W * (1 - rangeProjector (truncatedSVD B k))) ^ 2 -
        frobNorm (W * (B - truncatedSVD B k)) ^ 2 := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
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
      (θ / c) ^ 2 * frobNorm (W * (1 - Q)) ^ 2 := by
    have e : (1 - Q) * (B - truncatedSVD B b) = B - truncatedSVD B b := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hQB, rangeProjector_mul_self, sub_self,
        sub_zero]
    rw [← e, ← Matrix.mul_assoc,
      show (θ / c) ^ 2 * frobNorm (W * (1 - Q)) ^ 2 =
        (frobNorm (W * (1 - Q)) * (θ / c)) ^ 2 by ring]
    gcongr
    exact (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans (mul_le_mul_of_nonneg_left
      ((specNorm_sub_truncatedSVD B b).trans_le hb) (frobNorm_nonneg _))
  rw [h1, h2]
  have he : (θ / c) ^ 2 = c⁻¹ ^ 2 * θ ^ 2 := by
    rw [div_eq_mul_inv, mul_pow]
    ring
  rw [he] at h4
  nlinarith


/-- The rank deficit and the reciprocal-window tail are controlled by the subspace-error
excess: for $\mathbf{B}\in\Bbbk^{m\times n}$, $k\ge1$, $b\ge k$, $c>1$,
$\theta=\sigma_{k-1}(\mathbf{B})>0$, $\sigma_b(\mathbf{B})\le\theta/c$ and an orthogonal
projector $\mathbf{Z}$, write $\mathbf{P}_j=\mathbf{P}_{\llbracket\mathbf{B}\rrbracket_j}$ and
$D=\|(\mathbf{I}-\mathbf{Z})\mathbf{B}\|_{\mathsf{F}}^2
-\|(\mathbf{I}-\mathbf{P}_k)\mathbf{B}\|_{\mathsf{F}}^2$. Then
$$\|\mathbf{P}_k\|_{\mathsf{F}}^2-\|\mathbf{Z}\|_{\mathsf{F}}^2+
(1-c^{-2})\|\mathbf{Z}(\mathbf{I}-\mathbf{P}_b)\|_{\mathsf{F}}^2\le D/\theta^2\,.$$
No printed source. -/
theorem frobNorm_sq_sub_add_mul_le_div (B : Matrix m n 𝕜) {k b : ℕ}
    (hk : 1 ≤ k) (hkb : k ≤ b) {c : ℝ} (hc : 1 < c)
    (hθ : 0 < singularValues B (k - 1))
    (hb : singularValues B b ≤ singularValues B (k - 1) / c)
    {Z : Matrix m m 𝕜} (hZ : IsStarProjection Z) :
    frobNorm (rangeProjector (truncatedSVD B k)) ^ 2 - frobNorm Z ^ 2 +
        (1 - c⁻¹ ^ 2) * frobNorm (Z * (1 - rangeProjector (truncatedSVD B b))) ^ 2 ≤
      (frobNorm ((1 - Z) * B) ^ 2 -
        frobNorm ((1 - rangeProjector (truncatedSVD B k)) * B) ^ 2) /
          singularValues B (k - 1) ^ 2 := by
  have hhead := mul_frobNorm_mul_truncatedSVD_sq_add_le B hk (Nat.zero_le k)
    (fun i hi => absurd hi (Nat.not_lt_zero i)) (1 - Z)
  simp only [truncatedSVD_zero, rangeProjector_zero, Matrix.mul_zero, frobNorm_zero,
    zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] at hhead
  have htail := mul_frobNorm_mul_one_sub_sq_le_of_one_lt B hk hkb hc hb Z
  have hD := frobNorm_one_sub_mul_sq_sub_eq_add B k hZ (singularValues B (k - 1))
  rw [le_div_iff₀ (sq_pos_of_pos hθ)]
  nlinarith


/-- The compressed subspace error in a reciprocal window: for
$\mathbf{B}\in\Bbbk^{m\times n}$, $1\le k$, $a\le k\le b$, $c>1$,
$\theta=\sigma_{k-1}(\mathbf{B})>0$, $\sigma_b(\mathbf{B})\le\theta/c$ and an orthogonal
projector $\mathbf{Z}$ of rank at most $k$, write
$\mathbf{P}_j=\mathbf{P}_{\llbracket\mathbf{B}\rrbracket_j}$,
$\mathbf{L}=\mathbf{P}_b-\mathbf{P}_a$ and
$D=\|(\mathbf{I}-\mathbf{Z})\mathbf{B}\|_{\mathsf{F}}^2
-\|(\mathbf{I}-\mathbf{P}_k)\mathbf{B}\|_{\mathsf{F}}^2$. Then
$$\|\mathbf{L}(\mathbf{Z}-\mathbf{P}_k)\mathbf{L}\|_*
\le 2\min(k,b-k)+\frac{c^2}{c^2-1}\frac{D}{\theta^2}\,.$$
No printed source. -/
theorem nuclearNorm_mul_sub_mul_le_of_one_lt (B : Matrix m n 𝕜) {k a b : ℕ}
    (hk : 1 ≤ k) (hak : a ≤ k) (hkb : k ≤ b) {c : ℝ} (hc : 1 < c)
    (hθ : 0 < singularValues B (k - 1))
    (hb : singularValues B b ≤ singularValues B (k - 1) / c)
    {Z : Matrix m m 𝕜} (hZ : IsStarProjection Z) (hZk : Z.rank ≤ k) :
    nuclearNorm ((rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a)) *
        (Z - rangeProjector (truncatedSVD B k)) *
        (rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a))) ≤
      2 * ((min k (b - k) : ℕ) : ℝ) +
        c ^ 2 / (c ^ 2 - 1) *
          ((frobNorm ((1 - Z) * B) ^ 2 -
            frobNorm ((1 - rangeProjector (truncatedSVD B k)) * B) ^ 2) /
              singularValues B (k - 1) ^ 2) := by
  set Pa := rangeProjector (truncatedSVD B a)
  set P := rangeProjector (truncatedSVD B k)
  set Pb := rangeProjector (truncatedSVD B b)
  have hPa : IsStarProjection Pa := isStarProjection_rangeProjector _
  have hP : IsStarProjection P := isStarProjection_rangeProjector _
  have hPb : IsStarProjection Pb := isStarProjection_rangeProjector _
  have h1 : Pa * P = Pa := rangeProjector_mul_rangeProjector_of_range_le'
    (range_truncatedSVD_mono B hak)
  have h2 : P * Pa = Pa := rangeProjector_mul_rangeProjector_of_range_le
    (range_truncatedSVD_mono B hak)
  have h3 : P * Pb = P := rangeProjector_mul_rangeProjector_of_range_le'
    (range_truncatedSVD_mono B hkb)
  have h4 : Pb * P = P := rangeProjector_mul_rangeProjector_of_range_le
    (range_truncatedSVD_mono B hkb)
  have h5 : Pa * Pb = Pa := rangeProjector_mul_rangeProjector_of_range_le'
    (range_truncatedSVD_mono B (hak.trans hkb))
  have h6 : Pb * Pa = Pa := rangeProjector_mul_rangeProjector_of_range_le
    (range_truncatedSVD_mono B (hak.trans hkb))
  have hL : IsStarProjection (Pb - Pa) := hPa.sub_of_mul_eq_left hPb h5
  have hPk : frobNorm P ^ 2 = k := by
    have hr := (singularValues_pos_iff B).1 hθ
    rw [frobNorm_rangeProjector_sq, rank_truncatedSVD, min_eq_left (by omega)]
  have hPbb : frobNorm Pb ^ 2 ≤ b := by
    rw [frobNorm_rangeProjector_sq]; exact_mod_cast rank_truncatedSVD_le B b
  have hZ2 : frobNorm Z ^ 2 ≤ k := by
    rw [hZ.frobNorm_sq_eq_rank]; exact_mod_cast hZk
  have hA : nuclearNorm ((Pb - Pa) * (Z - P) * (Pb - Pa)) ≤ 2 * k := by
    rw [show (Pb - Pa) * (Z - P) * (Pb - Pa) =
      (Pb - Pa) * Z * (Pb - Pa) + -((Pb - Pa) * P * (Pb - Pa)) by
        simp only [Matrix.mul_sub, Matrix.sub_mul]; abel]
    refine (nuclearNorm_add_le _ _).trans ?_
    rw [nuclearNorm_neg, nuclearNorm_mul_mul_eq_frobNorm_sq hZ hL,
      nuclearNorm_mul_mul_eq_frobNorm_sq hP hL]
    have hh := pow_le_pow_left₀ (frobNorm_nonneg _) (hL.frobNorm_mul_right_le Z) 2
    have hh' := pow_le_pow_left₀ (frobNorm_nonneg _) (hL.frobNorm_mul_right_le P) 2
    linarith
  set E := (frobNorm ((1 - Z) * B) ^ 2 - frobNorm ((1 - P) * B) ^ 2) /
    singularValues B (k - 1) ^ 2
  set β := c ^ 2 / (c ^ 2 - 1)
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hc2 : 0 < c ^ 2 - 1 := by nlinarith
  have hβ0 : 0 ≤ β := by positivity
  have hβ1 : 1 ≤ β := (le_div_iff₀ hc2).2 (by linarith)
  have hα : 0 < 1 - c⁻¹ ^ 2 := by
    rw [inv_pow]
    have hh := (inv_lt_one₀ (sq_pos_of_pos hc0)).2 (show 1 < c ^ 2 by nlinarith)
    linarith
  have hβα : β * (1 - c⁻¹ ^ 2) = 1 := by
    dsimp only [β]
    field_simp
  have hE := frobNorm_sq_sub_add_mul_le_div B hk hkb hc hθ hb hZ
  change frobNorm P ^ 2 - frobNorm Z ^ 2 +
    (1 - c⁻¹ ^ 2) * frobNorm (Z * (1 - Pb)) ^ 2 ≤ E at hE
  have hδ : 0 ≤ frobNorm P ^ 2 - frobNorm Z ^ 2 := by linarith
  have hE0 : 0 ≤ E := by nlinarith [mul_nonneg hα.le (sq_nonneg (frobNorm (Z * (1 - Pb))))]
  have hEt : frobNorm P ^ 2 - frobNorm Z ^ 2 +
      frobNorm (Z * (1 - Pb)) ^ 2 ≤ β * E := by
    have hh := mul_le_mul_of_nonneg_left hE hβ0
    simp only [mul_add, ← mul_assoc, hβα, one_mul] at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hβ1) hδ]
  have hB := nuclearNorm_mul_sub_mul_le_of_mul_eq hPa hP hPb hZ h1 h2 h3 h4 h5 h6
  rcases le_total k (b - k) with h | h
  · rw [min_eq_left h]
    nlinarith [mul_nonneg hβ0 hE0]
  · rw [min_eq_right h, Nat.cast_sub hkb]
    nlinarith


end NLAlib
