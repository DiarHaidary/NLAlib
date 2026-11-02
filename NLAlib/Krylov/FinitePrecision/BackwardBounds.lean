/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.NormalizedBackward

/-!
# Backward error in the small-roundoff regime

A common bound on the computed coefficients gives local errors independent of the iteration
index. The exact backward model supplies that coefficient bound. Under an additional quadratic
small-roundoff condition, its perturbation can then be absorbed into the estimate.
The general estimate retains the absorption denominator; the quadratic corollary bounds
its reciprocal by a constant. They require only the run's local accuracy bound
$\varepsilon \le 1/100$.
The matrix need only be symmetric, and terminal breakdown is allowed.

## Main results

* `NLAlib.lanczosSmallRoundoffBackwardFactor`: the conditional factor,
  with value <!-- value lanczosSmallRoundoffBackwardFactor k --> $1000k^2$.
* `NLAlib.LanczosRun.frobNorm_backwardH_sub_dilatedH_le_of_coefficients_le`:
  coefficient certificates.
* `NLAlib.LanczosRun.frobNorm_backwardH_sub_dilatedH_le_geom_sum`: accumulated coefficient growth.
* `NLAlib.LanczosRun.frobNorm_backwardH_sub_dilatedH_le_of_sq_mul_lt`: the estimate with
  the absorption denominator retained.
* `NLAlib.LanczosRun.frobNorm_backwardH_sub_dilatedH_le_of_sq_mul_le`: the quadratic estimate.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- The factor for the Lanczos backward model under the quadratic small-roundoff condition,
with value <!-- value lanczosSmallRoundoffBackwardFactor k --> $1000k^2$.
No printed source. This estimate uses absorption of the model's own coefficient bound. -/
noncomputable irreducible_def lanczosSmallRoundoffBackwardFactor (k : ℕ) : ℝ :=
  1000 * (k : ℝ) ^ 2

/-- The small-roundoff backward factor is nonnegative. -/
theorem lanczosSmallRoundoffBackwardFactor_nonneg (k : ℕ) :
    0 ≤ lanczosSmallRoundoffBackwardFactor k := by
  rw [lanczosSmallRoundoffBackwardFactor_def]
  positivity

/-- The small-roundoff backward factor has the comparison
bound <!-- value lanczosSmallRoundoffBackwardFactor k --> $1000k^2$. -/
theorem lanczosSmallRoundoffBackwardFactor_le (k : ℕ) :
    lanczosSmallRoundoffBackwardFactor k ≤ 1000 * (k : ℝ) ^ 2 := by
  rw [lanczosSmallRoundoffBackwardFactor_def]

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

private theorem norm_w_le_of_coefficients_le {B : ℝ} {j : ℕ} (hj : j < k)
    (hH : specNorm L.H ≤ B) (hβ : L.β j ≤ B) :
    ‖WithLp.toLp 2 (L.w (j + 1))‖ ≤ 21 / 10 * B := by
  have hB0 := (specNorm_nonneg L.H).trans hH
  have hε := L.ε_nonneg
  have hu : ‖WithLp.toLp 2 (L.u (j + 1))‖ ≤ 21 / 20 * B :=
    (L.norm_u_le hj).trans (by gcongr)
  have hv : ‖WithLp.toLp 2 (L.v j)‖ ≤ 201 / 200 :=
    (L.norm_v_le hj.le).trans (by linarith [L.ε_le])
  have hb : |L.β j| ≤ B := by rwa [abs_of_nonneg (L.β_nonneg j hj.le)]
  have hbase : ‖WithLp.toLp 2 (L.u (j + 1))‖ +
      |L.β j| * ‖WithLp.toLp 2 (L.v j)‖ ≤ 411 / 200 * B := by
    calc _ ≤ 21 / 20 * B + B * (201 / 200) := by gcongr
      _ = _ := by ring
  have hew := (L.norm_ew_le j hj).trans (mul_le_mul_of_nonneg_left hbase hε)
  have ht : ‖WithLp.toLp 2 (L.w (j + 1))‖ ≤
      ‖WithLp.toLp 2 (L.u (j + 1))‖ + |L.β j| * ‖WithLp.toLp 2 (L.v j)‖ +
        ‖WithLp.toLp 2 (L.ew (j + 1))‖ := by
    rw [L.w_eq j hj, WithLp.toLp_add, WithLp.toLp_sub, WithLp.toLp_smul]
    have hsub := norm_sub_le (WithLp.toLp 2 (L.u (j + 1)))
      (L.β j • WithLp.toLp 2 (L.v j))
    rw [norm_smul, Real.norm_eq_abs] at hsub
    have hadd := norm_add_le (WithLp.toLp 2 (L.u (j + 1)) -
      L.β j • WithLp.toLp 2 (L.v j)) (WithLp.toLp 2 (L.ew (j + 1)))
    linarith only [hsub, hadd]
  have hεB := mul_le_mul_of_nonneg_right L.ε_le hB0
  nlinarith only [ht, hbase, hew, hεB, hB0]

private theorem norm_z_le_of_coefficients_le {B : ℝ} {j : ℕ} (hj : j < k)
    (hH : specNorm L.H ≤ B) (hα : |L.α (j + 1)| ≤ B) (hβ : L.β j ≤ B) :
    ‖WithLp.toLp 2 (L.z (j + 1))‖ ≤ 16 / 5 * B := by
  have hB0 := (specNorm_nonneg L.H).trans hH
  have hε := L.ε_nonneg
  have hw := L.norm_w_le_of_coefficients_le hj hH hβ
  have hv : ‖WithLp.toLp 2 (L.v (j + 1))‖ ≤ 201 / 200 :=
    (L.norm_v_le (by omega)).trans (by linarith [L.ε_le])
  have hbase : ‖WithLp.toLp 2 (L.w (j + 1))‖ +
      |L.α (j + 1)| * ‖WithLp.toLp 2 (L.v (j + 1))‖ ≤ 621 / 200 * B := by
    calc _ ≤ 21 / 10 * B + B * (201 / 200) := by gcongr
      _ = _ := by ring
  have hez := (L.norm_ez_le j hj).trans (mul_le_mul_of_nonneg_left hbase hε)
  have ht : ‖WithLp.toLp 2 (L.z (j + 1))‖ ≤
      ‖WithLp.toLp 2 (L.w (j + 1))‖ + |L.α (j + 1)| * ‖WithLp.toLp 2 (L.v (j + 1))‖ +
        ‖WithLp.toLp 2 (L.ez (j + 1))‖ := by
    rw [L.z_eq j hj, WithLp.toLp_add, WithLp.toLp_sub, WithLp.toLp_smul]
    have hsub := norm_sub_le (WithLp.toLp 2 (L.w (j + 1)))
      (L.α (j + 1) • WithLp.toLp 2 (L.v (j + 1)))
    rw [norm_smul, Real.norm_eq_abs] at hsub
    have hadd := norm_add_le (WithLp.toLp 2 (L.w (j + 1)) -
      L.α (j + 1) • WithLp.toLp 2 (L.v (j + 1))) (WithLp.toLp 2 (L.ez (j + 1)))
    linarith only [hsub, hadd]
  have hεB := mul_le_mul_of_nonneg_right L.ε_le hB0
  nlinarith only [ht, hbase, hez, hεB, hB0]

private theorem norm_recurrenceError_le_of_coefficients_le {B : ℝ} {j : ℕ} (hj : j < k)
    (hH : specNorm L.H ≤ B) (hα : |L.α (j + 1)| ≤ B) (hβ : L.β j ≤ B) :
    ‖WithLp.toLp 2 (L.recurrenceError j)‖ ≤ 10 * L.ε * B := by
  have hB0 := (specNorm_nonneg L.H).trans hH
  have hε := L.ε_nonneg
  have hu : ‖WithLp.toLp 2 (L.u (j + 1))‖ ≤ 21 / 20 * B :=
    (L.norm_u_le hj).trans (by gcongr)
  have hw := L.norm_w_le_of_coefficients_le hj hH hβ
  have hz := L.norm_z_le_of_coefficients_le hj hH hα hβ
  have hv0 : ‖WithLp.toLp 2 (L.v j)‖ ≤ 201 / 200 :=
    (L.norm_v_le hj.le).trans (by linarith [L.ε_le])
  have hv1 : ‖WithLp.toLp 2 (L.v (j + 1))‖ ≤ 201 / 200 :=
    (L.norm_v_le (by omega)).trans (by linarith [L.ε_le])
  have hb : |L.β j| ≤ B := by rwa [abs_of_nonneg (L.β_nonneg j hj.le)]
  have heu : ‖WithLp.toLp 2 (L.eu (j + 1))‖ ≤ 201 / 200 * L.ε * B := by
    refine (L.norm_eu_le j hj).trans ?_
    calc _ = L.ε * (specNorm L.H * ‖WithLp.toLp 2 (L.v (j + 1))‖) := by ring
      _ ≤ L.ε * (B * (201 / 200)) := by gcongr
      _ = _ := by ring
  have hew : ‖WithLp.toLp 2 (L.ew (j + 1))‖ ≤ 411 / 200 * L.ε * B := by
    refine (L.norm_ew_le j hj).trans ?_
    calc _ ≤ L.ε * (21 / 20 * B + B * (201 / 200)) := by gcongr
      _ = _ := by ring
  have hez : ‖WithLp.toLp 2 (L.ez (j + 1))‖ ≤ 621 / 200 * L.ε * B := by
    refine (L.norm_ez_le j hj).trans ?_
    calc _ ≤ L.ε * (21 / 10 * B + B * (201 / 200)) := by gcongr
      _ = _ := by ring
  have hδ : ‖WithLp.toLp 2 (L.δ (j + 1))‖ ≤ 16 / 5 * L.ε * B :=
    (L.norm_δ_le j hj).trans (by nlinarith [mul_le_mul_of_nonneg_left hz hε])
  rw [L.recurrenceError_eq hj, WithLp.toLp_neg, norm_neg, WithLp.toLp_add,
    WithLp.toLp_add, WithLp.toLp_add]
  have hsum := (norm_add_le
    (WithLp.toLp 2 (L.eu (j + 1)) + WithLp.toLp 2 (L.ew (j + 1)) +
      WithLp.toLp 2 (L.ez (j + 1))) (WithLp.toLp 2 (L.δ (j + 1))))
  have hsum2 := norm_add_le (WithLp.toLp 2 (L.eu (j + 1)) +
    WithLp.toLp 2 (L.ew (j + 1))) (WithLp.toLp 2 (L.ez (j + 1)))
  have hsum3 := norm_add_le (WithLp.toLp 2 (L.eu (j + 1))) (WithLp.toLp 2 (L.ew (j + 1)))
  nlinarith only [hsum, hsum2, hsum3, heu, hew, hez, hδ, mul_nonneg hε hB0]

private theorem abs_adjacentInner_le_of_coefficients_le {B : ℝ} {j : ℕ} (hj : j < k)
    (hH : specNorm L.H ≤ B) (hα : |L.α (j + 1)| ≤ B) (hβ : L.β j ≤ B) :
    |L.adjacentInner j| ≤ 19 / 2 * L.ε * B := by
  have hB0 := (specNorm_nonneg L.H).trans hH
  have hε := L.ε_nonneg
  have hw := L.norm_w_le_of_coefficients_le hj hH hβ
  have hz := L.norm_z_le_of_coefficients_le hj hH hα hβ
  have hv : ‖WithLp.toLp 2 (L.v (j + 1))‖ ≤ 201 / 200 :=
    (L.norm_v_le (by omega)).trans (by linarith [L.ε_le])
  have hg := L.abs_norm_v_sq_sub_one_le (j + 1) (by omega) (by omega)
  have h1 : |L.eα (j + 1)| ≤ 201 / 200 * (21 / 10) * L.ε * B := by
    refine (L.abs_eα_le j hj).trans ?_
    calc _ = L.ε * (‖WithLp.toLp 2 (L.v (j + 1))‖ *
        ‖WithLp.toLp 2 (L.w (j + 1))‖) := by ring
      _ ≤ L.ε * ((201 / 200) * (21 / 10 * B)) := by gcongr
      _ = _ := by ring
  have h2 : |(‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 - 1) * L.α (j + 1)| ≤ L.ε * B := by
    rw [abs_mul]
    exact mul_le_mul hg hα (abs_nonneg _) hε
  have hez : ‖WithLp.toLp 2 (L.ez (j + 1))‖ ≤ 621 / 200 * L.ε * B := by
    refine (L.norm_ez_le j hj).trans ?_
    calc _ ≤ L.ε * (21 / 10 * B + B * (201 / 200)) := by gcongr
      _ = _ := by ring
  have hδ : ‖WithLp.toLp 2 (L.δ (j + 1))‖ ≤ 16 / 5 * L.ε * B :=
    (L.norm_δ_le j hj).trans (by nlinarith [mul_le_mul_of_nonneg_left hz hε])
  have h3 : |L.v (j + 1) ⬝ᵥ L.ez (j + 1)| ≤ 201 / 200 * (621 / 200 * L.ε * B) :=
    (EuclideanSpace.abs_dotProduct_le_norm _ _).trans
      (mul_le_mul hv hez (norm_nonneg _) (by norm_num))
  have h4 : |L.v (j + 1) ⬝ᵥ L.δ (j + 1)| ≤ 201 / 200 * (16 / 5 * L.ε * B) :=
    (EuclideanSpace.abs_dotProduct_le_norm _ _).trans
      (mul_le_mul hv hδ (norm_nonneg _) (by norm_num))
  rw [L.adjacentInner_eq hj]
  have htri := abs_add_le (-L.eα (j + 1) -
    (‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 - 1) * L.α (j + 1) +
    L.v (j + 1) ⬝ᵥ L.ez (j + 1)) (L.v (j + 1) ⬝ᵥ L.δ (j + 1))
  have htri2 := abs_add_le (-L.eα (j + 1) -
    (‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 - 1) * L.α (j + 1)) (L.v (j + 1) ⬝ᵥ L.ez (j + 1))
  have htri3 := abs_sub (-L.eα (j + 1))
    ((‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 - 1) * L.α (j + 1))
  rw [abs_neg] at htri3
  nlinarith only [htri, htri2, htri3, h1, h2, h3, h4, mul_nonneg hε hB0]

private theorem specNorm_tridiagonalSucc_le_backwardH :
    specNorm L.tridiagonalSucc ≤ specNorm L.H + frobNorm (L.backwardH - L.dilatedH) := by
  have hQs := L.hasOrthonormalCols_dilatedBasisSucc
  have hQ := L.hasOrthonormalCols_dilatedBasis
  have hgram : L.dilatedBasisSuccᵀ * L.dilatedBasisSucc = 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQs.conjTranspose_mul_self
  have hT : L.tridiagonalSucc =
      L.dilatedBasisSuccᵀ * (L.backwardH * L.dilatedBasis) := by
    rw [L.backwardH_mul_dilatedBasis, ← Matrix.mul_assoc, hgram, Matrix.one_mul]
  have hQt : specNorm L.dilatedBasisSuccᵀ ≤ 1 := by
    rw [specNorm_transpose]
    exact hQs.specNorm_le_one
  have ht : specNorm L.tridiagonalSucc ≤ specNorm L.backwardH := by
    rw [hT]
    calc _ ≤ specNorm L.dilatedBasisSuccᵀ *
          (specNorm L.backwardH * specNorm L.dilatedBasis) :=
        (specNorm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left (specNorm_mul_le _ _) (specNorm_nonneg _))
      _ ≤ 1 * (specNorm L.backwardH * 1) := by gcongr; exact hQ.specNorm_le_one
      _ = _ := by ring
  have hd : specNorm L.dilatedH = specNorm L.H := specNorm_blockDiagonal_const L.H
  have hb := specNorm_add_le (L.backwardH - L.dilatedH) L.dilatedH
  rw [sub_add_cancel, hd] at hb
  have he := specNorm_le_frobNorm (L.backwardH - L.dilatedH)
  linarith

private theorem abs_α_le_specNorm_tridiagonalSucc {j : ℕ} (hj : j < k) :
    |L.α (j + 1)| ≤ specNorm L.tridiagonalSucc := by
  have h := norm_apply_le_specNorm L.tridiagonalSucc ⟨j, by omega⟩ ⟨j, hj⟩
  simpa [tridiagonalSucc, LanczosData.tridiagonalSucc, toLanczosData, Real.norm_eq_abs] using h

private theorem β_le_specNorm_tridiagonalSucc {i : ℕ} (hi : i ≤ k) :
    L.β i ≤ specNorm L.tridiagonalSucc := by
  by_cases hzero : i = 0
  · rw [hzero, L.β_zero]
    exact specNorm_nonneg _
  have hip : 0 < i := by omega
  have h := norm_apply_le_specNorm L.tridiagonalSucc ⟨i, by omega⟩ ⟨i - 1, by omega⟩
  have hne : i ≠ i - 1 := by omega
  have heq : i = i - 1 + 1 := by omega
  change ‖(if i = i - 1 then L.α (i + 1) else if i = i - 1 + 1 then L.β i
    else if i - 1 = i + 1 then L.β (i - 1) else 0)‖ ≤ specNorm L.tridiagonalSucc at h
  rw [if_neg hne, if_pos heq, Real.norm_eq_abs, abs_of_nonneg (L.β_nonneg i hi)] at h
  exact h

/-- **Coefficient-certified Lanczos backward error**: a common bound on the matrix and computed
coefficients controls the backward error.
This certificate estimate needs local accuracy only, without an iteration-horizon condition.
No printed source. It combines the coefficient bounds with the normalized model.
Result: lanczos-backward-model -/
theorem frobNorm_backwardH_sub_dilatedH_le_of_coefficients_le {B : ℝ}
    (hH : specNorm L.H ≤ B)
    (hα : ∀ j < k, |L.α (j + 1)| ≤ B) (hβ : ∀ i ≤ k, L.β i ≤ B) :
    frobNorm (L.backwardH - L.dilatedH) ≤
      normalizedBackwardBound k (15 * L.ε * B) (10 * L.ε * B) := by
  have hB0 := (specNorm_nonneg L.H).trans hH
  have hεB : 0 ≤ L.ε * B := mul_nonneg L.ε_nonneg hB0
  have hf : ∀ j < k, ‖WithLp.toLp 2 (L.toNormalizedLanczosData.recurrenceError j)‖ ≤
      15 * L.ε * B := by
    intro j hj
    have hr := L.norm_recurrenceError_le_of_coefficients_le hj hH (hα j hj) (hβ j hj.le)
    have hn := L.norm_normalized_recurrenceError_le_of_le hj hr
      (fun i hi => hβ i (by omega))
    change ‖WithLp.toLp 2 (L.normalized.recurrenceError j)‖ ≤ _
    nlinarith only [hn, hεB]
  have hp : ∀ j < k, |L.toNormalizedLanczosData.adjacentInner j| ≤ 10 * L.ε * B := by
    intro j hj
    have hr := L.abs_adjacentInner_le_of_coefficients_le hj hH (hα j hj) (hβ j hj.le)
    have hn := L.abs_normalized_adjacentInner_le_of_le hj hr
    change |L.normalized.adjacentInner j| ≤ _
    nlinarith only [hn, hεB]
  have h := L.toNormalizedLanczosData.frobNorm_backwardH_sub_dilatedH_le hf hp
  change frobNorm (L.backwardH - L.dilatedH) ≤ normalizedBackwardBound k _ _ at h
  exact h

private theorem frobNorm_backwardH_sub_dilatedH_le_mul_of_coefficients_le {B : ℝ}
    (hH : specNorm L.H ≤ B)
    (hα : ∀ j < k, |L.α (j + 1)| ≤ B) (hβ : ∀ i ≤ k, L.β i ≤ B) :
    frobNorm (L.backwardH - L.dilatedH) ≤ 500 * (k : ℝ) ^ 2 * L.ε * B := by
  have h := L.frobNorm_backwardH_sub_dilatedH_le_of_coefficients_le hH hα hβ
  have hB0 := (specNorm_nonneg L.H).trans hH
  have hεB : 0 ≤ L.ε * B := mul_nonneg L.ε_nonneg hB0
  rw [normalizedBackwardBound] at h
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.k_pos
  have hs : Real.sqrt (k : ℝ) ≤ k := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have he : 170 * (k : ℝ) * Real.sqrt k * (L.ε * B) ≤ 170 * k ^ 2 * (L.ε * B) := by
    calc _ ≤ 170 * k * k * (L.ε * B) := by gcongr
      _ = _ := by ring
  change frobNorm (L.backwardH - L.dilatedH) ≤ 500 * (k : ℝ) ^ 2 * L.ε * B
  nlinarith only [h, he]

private theorem frobNorm_backwardH_sub_dilatedH_le_mul_add :
    frobNorm (L.backwardH - L.dilatedH) ≤ 500 * (k : ℝ) ^ 2 * L.ε *
      (specNorm L.H + frobNorm (L.backwardH - L.dilatedH)) := by
  set B := specNorm L.H + frobNorm (L.backwardH - L.dilatedH)
  have hH : specNorm L.H ≤ B := le_add_of_nonneg_right (frobNorm_nonneg _)
  have hc : specNorm L.tridiagonalSucc ≤ B := L.specNorm_tridiagonalSucc_le_backwardH
  have hα (j : ℕ) (hj : j < k) : |L.α (j + 1)| ≤ B :=
    (L.abs_α_le_specNorm_tridiagonalSucc hj).trans hc
  have hβ (i : ℕ) (hi : i ≤ k) : L.β i ≤ B :=
    (L.β_le_specNorm_tridiagonalSucc hi).trans hc
  exact L.frobNorm_backwardH_sub_dilatedH_le_mul_of_coefficients_le hH hα hβ

/-- **Geometric Lanczos backward error**: the backward error with coefficient growth retained as a
finite geometric sum.
Writing $G_k=(1+\varepsilon)\sum_{i<k}(1+8\varepsilon)^{i+1}$, the bound
is <!-- value lanczosSmallRoundoffBackwardFactor k -->
$1000k^2\varepsilon(1+G_k)\|\mathbf H\|_2$.
Only local accuracy is assumed, and terminal breakdown is allowed. The geometric sum may
be large; this theorem does not assert convergence as the number of steps increases.
No printed source. It uses `NLAlib.LanczosRun.β_le_geom_sum` as a coefficient certificate.
Result: lanczos-backward-model -/
theorem frobNorm_backwardH_sub_dilatedH_le_geom_sum :
    frobNorm (L.backwardH - L.dilatedH) ≤
      lanczosSmallRoundoffBackwardFactor k * L.ε *
        (1 + (1 + L.ε) * ∑ i ∈ Finset.range k, (1 + 8 * L.ε) ^ (i + 1)) * specNorm L.H := by
  have hε := L.ε_nonneg
  have hH0 := specNorm_nonneg L.H
  set G := (1 + L.ε) * ∑ i ∈ Finset.range k, (1 + 8 * L.ε) ^ (i + 1) with hG
  have hG0 : 0 ≤ G := by positivity
  set B := 2 * (1 + G) * specNorm L.H with hB
  have hH : specNorm L.H ≤ B := by dsimp [B]; nlinarith
  have hbG (i : ℕ) (hi : i ≤ k) : L.β i ≤ G * specNorm L.H := by
    have hs : ∑ j ∈ Finset.range i, (1 + 8 * L.ε) ^ (j + 1) ≤
        ∑ j ∈ Finset.range k, (1 + 8 * L.ε) ^ (j + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi) (fun _ _ _ => by positivity)
    calc L.β i ≤ (1 + L.ε) * specNorm L.H *
          ∑ j ∈ Finset.range i, (1 + 8 * L.ε) ^ (j + 1) := L.β_le_geom_sum hi
      _ ≤ (1 + L.ε) * specNorm L.H *
          ∑ j ∈ Finset.range k, (1 + 8 * L.ε) ^ (j + 1) := by gcongr
      _ = G * specNorm L.H := by rw [hG]; ring
  have hα (j : ℕ) (hj : j < k) : |L.α (j + 1)| ≤ B := by
    calc |L.α (j + 1)| ≤ 2 * (specNorm L.H + L.β j) := L.abs_α_le_β hj
      _ ≤ 2 * (specNorm L.H + G * specNorm L.H) := by gcongr; exact hbG j hj.le
      _ = B := by rw [hB]; ring
  have hβ (i : ℕ) (hi : i ≤ k) : L.β i ≤ B :=
    (hbG i hi).trans (by dsimp [B]; nlinarith)
  have h := L.frobNorm_backwardH_sub_dilatedH_le_mul_of_coefficients_le hH hα hβ
  rw [lanczosSmallRoundoffBackwardFactor_def]
  calc frobNorm (L.backwardH - L.dilatedH) ≤ 500 * (k : ℝ) ^ 2 * L.ε * B := h
    _ = _ := by rw [hB, hG]; ring

/-- **Lanczos backward error with an explicit margin**: backward error with the absorption
denominator retained: for a $k$-step
finite-precision Lanczos run with $k^2\varepsilon < 1/500$, let $F_k$ be
`NLAlib.lanczosSmallRoundoffBackwardFactor k`, with
value <!-- value lanczosSmallRoundoffBackwardFactor k --> $F_k = 1000k^2$.
Then the same exact model satisfies
$$\|\tilde{\mathbf{H}}-\mathbf{I}_{k+1}\otimes\mathbf{H}\|_{\mathsf{F}}
\le \frac{F_k\varepsilon}{2-F_k\varepsilon}\|\mathbf{H}\|_2 \,.$$
The denominator is positive under the hypothesis. No positive definiteness is required;
terminal breakdown is allowed. The run assumes only local accuracy $\varepsilon \le 1/100$.
No printed source. This is absorption of the model's own coefficient bound.
Result: lanczos-backward-model -/
theorem frobNorm_backwardH_sub_dilatedH_le_of_sq_mul_lt
    (hsmall : (k : ℝ) ^ 2 * L.ε < 1 / 500) :
    frobNorm (L.backwardH - L.dilatedH) ≤
      (lanczosSmallRoundoffBackwardFactor k * L.ε /
        (2 - lanczosSmallRoundoffBackwardFactor k * L.ε)) * specNorm L.H := by
  have h := L.frobNorm_backwardH_sub_dilatedH_le_mul_add
  rw [lanczosSmallRoundoffBackwardFactor_def]
  have hd : 0 < 2 - 1000 * (k : ℝ) ^ 2 * L.ε := by nlinarith only [hsmall]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).2
  nlinarith only [h]

/-- **Quadratic backward error under small roundoff**: for a $k$-step finite-precision
Lanczos run with $k^2\varepsilon \le 10^{-3}$, the same exact backward model satisfies the bound
with factor <!-- value lanczosSmallRoundoffBackwardFactor k -->
$$\|\tilde{\mathbf{H}}-\mathbf{I}_{k+1}\otimes\mathbf{H}\|_{\mathsf{F}}
\le 1000k^2\varepsilon\|\mathbf{H}\|_2 \,.$$
No printed source. The exact model bounds its own coefficients; the additional smallness
condition absorbs its perturbation into the right-hand side. Terminal breakdown is allowed.
Result: lanczos-backward-model-small-roundoff -/
theorem frobNorm_backwardH_sub_dilatedH_le_of_sq_mul_le
    (hsmall : (k : ℝ) ^ 2 * L.ε ≤ 1 / 1000) :
    frobNorm (L.backwardH - L.dilatedH) ≤
      lanczosSmallRoundoffBackwardFactor k * L.ε * specNorm L.H := by
  have h := L.frobNorm_backwardH_sub_dilatedH_le_of_sq_mul_lt (by nlinarith only [hsmall])
  have hc : lanczosSmallRoundoffBackwardFactor k * L.ε ≤ 1 := by
    rw [lanczosSmallRoundoffBackwardFactor_def]
    nlinarith only [hsmall]
  have hq : lanczosSmallRoundoffBackwardFactor k * L.ε /
      (2 - lanczosSmallRoundoffBackwardFactor k * L.ε) ≤
      lanczosSmallRoundoffBackwardFactor k * L.ε :=
    div_le_self (mul_nonneg (lanczosSmallRoundoffBackwardFactor_nonneg k) L.ε_nonneg)
      (by linarith only [hc])
  exact h.trans (mul_le_mul_of_nonneg_right hq (specNorm_nonneg L.H))

end LanczosRun

end NLAlib
