/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.JensenFormula

/-!
# The submean inequality for the regularized logarithm

The disk average of the regularized log-norm bounds the value at its center. This
version of Jensen's inequality applies to holomorphic functions with zeros. Upstream
candidate for `Mathlib.Analysis.Complex.JensenFormula`.

The proof adapts the original formalization in `tchen-research/NLAlib@77514ce`.

## Main results

* `AnalyticOnNhd.log_sqrt_norm_sq_add_sq_le_circleAverage`: the disk submean inequality.
-/

@[expose] public section

section

open Real Set Metric MeromorphicOn
open scoped ComplexConjugate

namespace Complex

/-- The scalar Jensen lower bound at a nonzero center. -/
private theorem _root_.AnalyticOnNhd.log_norm_center_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ Real.circleAverage (fun z => Real.log ‖f z‖) c R := by
  have hf' : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa only [abs_of_pos hR] using hf
  have h := hf'.circleAverage_log_norm hR.ne' hc
  rw [abs_of_pos hR] at h
  rw [h]
  apply le_add_of_nonneg_left
  apply finsum_nonneg
  intro u
  by_cases hu : u ∈ closedBall c R
  · have hcoeff : (0 : ℝ) ≤ MeromorphicOn.divisor f (closedBall c R) u :=
      by exact_mod_cast hf.divisor_nonneg u
    apply mul_nonneg hcoeff
    by_cases huc : u = c
    · simp [huc]
    · apply Real.log_nonneg
      rw [← div_eq_mul_inv]
      apply (one_le_div (by exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc)))).2
      simpa only [mem_closedBall, dist_eq_norm'] using hu
  · simp [hu]

/-- The holomorphic scalar Cauchy--Schwarz witness used for regularization. -/
private noncomputable def regularizedLogWitness (a : ℂ) (ε : ℝ) (z : ℂ) : ℂ :=
  (conj a * z + ((ε ^ 2 : ℝ) : ℂ)) / ((ε * sqrt (normSq a + ε ^ 2) : ℝ) : ℂ)

private theorem regularizedLogWitness_self (a : ℂ) {ε : ℝ} (hε : 0 < ε) :
    regularizedLogWitness a ε a = ((sqrt (normSq a + ε ^ 2) / ε : ℝ) : ℂ) := by
  have hP : 0 < normSq a + ε ^ 2 := add_pos_of_nonneg_of_pos (normSq_nonneg _) (sq_pos_of_pos hε)
  have hS : sqrt (normSq a + ε ^ 2) ≠ 0 := ne_of_gt (sqrt_pos.2 hP)
  unfold regularizedLogWitness
  rw [← normSq_eq_conj_mul_self, ← ofReal_add, ← ofReal_div]
  apply congrArg ofReal
  apply (div_eq_iff (mul_ne_zero (ne_of_gt hε) hS)).2
  rw [show sqrt (normSq a + ε ^ 2) / ε * (ε * sqrt (normSq a + ε ^ 2)) =
    sqrt (normSq a + ε ^ 2) ^ 2 by field_simp]
  exact (sq_sqrt hP.le).symm

private theorem normSq_regularizedLogWitness_numerator_le (a z : ℂ) (ε : ℝ) :
    normSq (conj a * z + ((ε ^ 2 : ℝ) : ℂ)) ≤
      (normSq a + ε ^ 2) * (normSq z + ε ^ 2) := by
  have hid : (normSq a + ε ^ 2) * (normSq z + ε ^ 2) -
      normSq (conj a * z + ((ε ^ 2 : ℝ) : ℂ)) = ε ^ 2 * normSq (a - z) := by
    simp only [normSq_apply, add_re, add_im, mul_re, mul_im, conj_re, conj_im,
      ofReal_re, ofReal_im, sub_re, sub_im]
    ring
  have hpos := mul_nonneg (sq_nonneg ε) (normSq_nonneg (a - z))
  linarith

/-- The witness's norm is bounded by the regularized norm of its input. -/
private theorem norm_regularizedLogWitness_le (a z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ‖regularizedLogWitness a ε z‖ ≤ sqrt (normSq z + ε ^ 2) / ε := by
  have hPa : 0 < normSq a + ε ^ 2 := add_pos_of_nonneg_of_pos (normSq_nonneg _) (sq_pos_of_pos hε)
  have hPz : 0 < normSq z + ε ^ 2 := add_pos_of_nonneg_of_pos (normSq_nonneg _) (sq_pos_of_pos hε)
  have hSa : 0 < sqrt (normSq a + ε ^ 2) := sqrt_pos.2 hPa
  have hSz : 0 < sqrt (normSq z + ε ^ 2) := sqrt_pos.2 hPz
  rw [regularizedLogWitness, norm_div, norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos hε hSa)]
  apply (div_le_iff₀ (mul_pos hε hSa)).2
  rw [show sqrt (normSq z + ε ^ 2) / ε * (ε * sqrt (normSq a + ε ^ 2)) =
    sqrt (normSq z + ε ^ 2) * sqrt (normSq a + ε ^ 2) by field_simp]
  have h := normSq_regularizedLogWitness_numerator_le a z ε
  rw [normSq_eq_norm_sq] at h
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hSz.le hSa.le)).mp
  rw [mul_pow, sq_sqrt hPz.le, sq_sqrt hPa.le]
  simpa only [mul_comm] using h

/-- The regularized logarithm of the norm of a holomorphic function satisfies the disk
submean inequality, including when the function vanishes at the center. -/
theorem _root_.AnalyticOnNhd.log_sqrt_norm_sq_add_sq_le_circleAverage
    {f : ℂ → ℂ} {c : ℂ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) :
    Real.log (sqrt (‖f c‖ ^ 2 + ε ^ 2)) ≤
      Real.circleAverage (fun z => Real.log (sqrt (‖f z‖ ^ 2 + ε ^ 2))) c R := by
  let Q (z : ℂ) := sqrt (normSq (f z) + ε ^ 2)
  have hQpos (z : ℂ) : 0 < Q z := sqrt_pos.2
    (add_pos_of_nonneg_of_pos (normSq_nonneg _) (sq_pos_of_pos hε))
  have hQge (z : ℂ) : ε ≤ Q z := by
    calc
      ε = sqrt (ε ^ 2) := (sqrt_sq hε.le).symm
      _ ≤ Q z := sqrt_le_sqrt (le_add_of_nonneg_left (normSq_nonneg _))
  have hMpos (z : ℂ) : 0 < Q z / ε := div_pos (hQpos z) hε
  have hMone (z : ℂ) : 1 ≤ Q z / ε := (le_div_iff₀ hε).2 (by simpa using hQge z)
  let W (z : ℂ) := regularizedLogWitness (f c) ε (f z)
  have hW : AnalyticOnNhd ℂ W (closedBall c R) := by
    intro z hz
    dsimp [W, regularizedLogWitness]
    exact ((analyticAt_const.mul (hf z hz)).add analyticAt_const).div_const
  have hWnorm : ‖W c‖ = Q c / ε := by
    dsimp [W]
    rw [regularizedLogWitness_self _ hε, norm_real, Real.norm_eq_abs, abs_of_pos (hMpos c)]
  have hWne : W c ≠ 0 := norm_ne_zero_iff.mp (by rw [hWnorm]; exact ne_of_gt (hMpos c))
  have hj := hW.log_norm_center_le_circleAverage hR hWne
  rw [hWnorm, Real.log_div (ne_of_gt (hQpos c)) (ne_of_gt hε)] at hj
  have hupper (z : ℂ) : Real.log ‖W z‖ ≤ Real.log (Q z) - Real.log ε := by
    rw [← Real.log_div (ne_of_gt (hQpos z)) (ne_of_gt hε)]
    by_cases hzero : W z = 0
    · rw [hzero, norm_zero, Real.log_zero]
      exact Real.log_nonneg (hMone z)
    · exact Real.log_le_log (norm_pos_iff.mpr hzero) (norm_regularizedLogWitness_le _ _ hε)
  have hcont : ContinuousOn (fun z => Real.log (Q z)) (closedBall c R) := by
    apply ContinuousOn.log _ (fun z _ => ne_of_gt (hQpos z))
    dsimp [Q]
    simp_rw [normSq_eq_norm_sq]
    exact ((hf.continuousOn.norm.pow 2).add continuousOn_const).sqrt
  have hQint := (hcont.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hW' : AnalyticOnNhd ℂ W (closedBall c |R|) := by simpa only [abs_of_pos hR] using hW
  have hWint := (hW'.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hHInt : CircleIntegrable (fun z => Real.log (Q z) - Real.log ε) c R :=
    hQint.sub (continuousOn_const.circleIntegrable hR.le)
  have hm := Real.circleAverage_mono hWint hHInt (fun z _ => hupper z)
  rw [Real.circleAverage_fun_sub hQint (continuousOn_const.circleIntegrable hR.le),
    Real.circleAverage_const] at hm
  have hfinal : Real.log (Q c) ≤ Real.circleAverage (fun z => Real.log (Q z)) c R := by linarith
  simpa only [Q, normSq_eq_norm_sq] using hfinal

end Complex

end
