/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Restricted moments from Hölder's inequality

A second moment restricted to a set is controlled by a higher global moment and the measure
of the set. Upstream candidate for `Mathlib.MeasureTheory.Integral.Bochner.Set`.

## Main results

* `MeasureTheory.setIntegral_sq_le_integral_rpow_mul_measureReal_rpow`.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- Hölder controls a restricted second moment by a global $p$th moment, for $p>2$:
$$\int_s f^2\,d\mu \le \left(\int f^p\,d\mu\right)^{2/p}
\mu(s)^{1-2/p}\,.$$
The function is almost everywhere nonnegative and belongs to $L^p$. -/
theorem setIntegral_sq_le_integral_rpow_mul_measureReal_rpow
    {f : α → ℝ} {p : ℝ} (hp : 2 < p) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hf0 : 0 ≤ᵐ[μ] f) (s : Set α) :
    ∫ x in s, f x ^ 2 ∂μ ≤
      (∫ x, f x ^ p ∂μ) ^ (2 / p) * (μ.real s) ^ (1 - 2 / p) := by
  have hp0 : 0 < p := by linarith
  have hp2 : 1 < p / 2 := by linarith
  have hpq := Real.HolderConjugate.conjExponent hp2
  have hf2 : MemLp (fun x => f x ^ 2) (ENNReal.ofReal (p / 2)) μ := by
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_ofNat, ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
      hf.norm_rpow_div (2 : ℝ≥0∞)
  have hconst : MemLp (fun _ : α => (1 : ℝ))
      (ENNReal.ofReal (Real.conjExponent (p / 2))) (μ.restrict s) := memLp_const 1
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (ae_of_all _ fun x => sq_nonneg (f x)) (ae_of_all _ fun _ => zero_le_one)
    (hf2.restrict s) hconst
  simp only [mul_one, Real.one_rpow] at h
  have hpow : ∫ x in s, (f x ^ 2) ^ (p / 2) ∂μ = ∫ x in s, f x ^ p ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hf0] with x hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hpq' : 1 / Real.conjExponent (p / 2) = 1 - 2 / p := by
    have hsum := hpq.one_div_add_one_div
    have hdiv : 1 / (p / 2) = 2 / p := by ring
    rw [hdiv] at hsum
    linarith
  rw [hpow, show 1 / (p / 2) = 2 / p by ring, hpq'] at h
  have hi : Integrable (fun x => f x ^ p) μ := by
    have hh := hf.integrable_norm_rpow
      (by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hp0)
      ENNReal.ofReal_ne_top
    simp only [ENNReal.toReal_ofReal hp0.le] at hh
    exact hh.congr (hf0.mono fun x hx => by
      change ‖f x‖ ^ p = f x ^ p
      rw [Real.norm_of_nonneg hx])
  have hle := setIntegral_le_integral (s := s) hi (hf0.mono fun x hx => Real.rpow_nonneg hx p)
  have hn : 0 ≤ ∫ x in s, f x ^ p ∂μ :=
    integral_nonneg_of_ae (ae_restrict_of_ae (hf0.mono fun x hx => Real.rpow_nonneg hx p))
  have hmono := Real.rpow_le_rpow hn hle (by positivity : 0 ≤ 2 / p)
  have hmeasure : ∫ _ : α, (1 : ℝ) ∂μ.restrict s = μ.real s := by simp
  rw [hmeasure] at h
  exact h.trans (mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg (measureReal_nonneg) _))

end MeasureTheory
