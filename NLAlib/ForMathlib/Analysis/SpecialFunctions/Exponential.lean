/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# Exponential limits of noncommutative powers

If the first-order increments of a sequence converge to a generator, taking the corresponding
powers yields its exponential. Upstream candidate for
`Mathlib.Analysis.SpecialFunctions.Exponential`.

## Main results

* `NormedSpace.tendsto_pow_exp_of_tangent`: the Euler product limit in a real Banach algebra.
-/

@[expose] public section

open Filter
open scoped Topology

variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
/-- A direct noncommutative power comparison on a common norm ball. -/
private theorem norm_pow_sub_pow_le_mul_pow (a b : A) {R : ℝ} (hR : 1 ≤ R)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ (n : ℝ) * R ^ n * ‖a - b‖ := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  induction n with
  | zero => simp
  | succ n ih =>
    have he : a ^ (n + 1) - b ^ (n + 1) =
        a ^ n * (a - b) + (a ^ n - b ^ n) * b := by
      simp only [pow_succ]
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖a ^ n * (a - b)‖ + ‖(a ^ n - b ^ n) * b‖ := norm_add_le _ _
      _ ≤ ‖a ^ n‖ * ‖a - b‖ + ‖a ^ n - b ^ n‖ * ‖b‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ R ^ n * ‖a - b‖ + ((n : ℝ) * R ^ n * ‖a - b‖) * R := by
        gcongr
        exact (norm_pow_le a n).trans (pow_le_pow_left₀ (norm_nonneg _) ha n)
      _ ≤ ((n + 1 : ℕ) : ℝ) * R ^ (n + 1) * ‖a - b‖ := by
        rw [Nat.cast_add_one, pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right hR
          (mul_nonneg (pow_nonneg hR0 n) (norm_nonneg (a - b)))]

namespace NormedSpace

/-- Equal first-order steps at the identity have asymptotically equal powers.
No commutation between either sequence or their limit is assumed. -/
private theorem tendsto_pow_sub_pow_zero_of_tangent_eq {F G : ℕ → A} {H : A}
    (hF : Tendsto (fun n : ℕ => (n : ℝ) • (F n - 1)) atTop (𝓝 H))
    (hG : Tendsto (fun n : ℕ => (n : ℝ) • (G n - 1)) atTop (𝓝 H)) :
    Tendsto (fun n => (F n) ^ n - (G n) ^ n) atTop (𝓝 0) := by
  let K := ‖H‖ + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hFb : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ) • (F n - 1)‖ ≤ K :=
    (hF.norm.eventually (gt_mem_nhds (by dsimp [K]; linarith))).mono (fun _ h => h.le)
  have hGb : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ) • (G n - 1)‖ ≤ K :=
    (hG.norm.eventually (gt_mem_nhds (by dsimp [K]; linarith))).mono (fun _ h => h.le)
  have hdiff : Tendsto (fun n : ℕ => (n : ℝ) • (F n - G n)) atTop (𝓝 0) := by
    simpa only [← smul_sub, sub_sub_sub_cancel_right, sub_self] using hF.sub hG
  have hmajor := hdiff.norm.const_mul (Real.exp K)
  simp only [norm_zero, mul_zero] at hmajor
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hmajor
  filter_upwards [hFb, hGb, eventually_gt_atTop (0 : ℕ)] with n hnF hnG hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnorm (X : A) (hX : ‖(n : ℝ) • (X - 1)‖ ≤ K) :
      ‖X‖ ≤ Real.exp (K / n) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hn0] at hX
    calc
      ‖X‖ = ‖1 + (X - 1)‖ := by congr 1; abel
      _ ≤ 1 + ‖X - 1‖ := by simpa only [norm_one] using norm_add_le (1 : A) (X - 1)
      _ ≤ 1 + K / n := by gcongr; exact (le_div_iff₀ hn0).mpr (by nlinarith [hX])
      _ ≤ Real.exp (K / n) := by simpa only [add_comm] using Real.add_one_le_exp (K / n)
  have hR : 1 ≤ Real.exp (K / n) := Real.one_le_exp (div_nonneg hK hn0.le)
  have hbound := norm_pow_sub_pow_le_mul_pow (F n) (G n) hR (hnorm _ hnF) (hnorm _ hnG) n
  have he : Real.exp (K / n) ^ n = Real.exp K := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [he] at hbound
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hn0, mul_left_comm, mul_assoc] using hbound

variable [CompleteSpace A]

/-- First-order steps at the identity converge under repeated powers to the
Banach-algebra exponential. See [SutterBertaTomamichel2017, Corollary 3.3] for the product limit
used in multivariate trace inequalities. -/
theorem tendsto_pow_exp_of_tangent {F : ℕ → A} {H : A}
    (hF : Tendsto (fun n : ℕ => (n : ℝ) • (F n - 1)) atTop (𝓝 H)) :
    Tendsto (fun n => (F n) ^ n) atTop (𝓝 (NormedSpace.exp H)) := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  let G : ℕ → A := fun n => NormedSpace.exp ((n : ℝ)⁻¹ • H)
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • H)) H 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      (hasDerivAt_exp_smul_const H (0 : ℝ))
  have hG : Tendsto (fun n : ℕ => (n : ℝ) • (G n - 1)) atTop (𝓝 H) := by
    have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝[>] 0) :=
      tendsto_inv_atTop_nhdsGT_zero.comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, zero_add, zero_smul, NormedSpace.exp_zero, inv_inv]
      using hd.tendsto_slope_zero_right.comp hi
  have hdiff := tendsto_pow_sub_pow_zero_of_tangent_eq hF hG
  have hGeq : ∀ᶠ n in atTop, (G n) ^ n = NormedSpace.exp H := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    change (NormedSpace.exp ((n : ℝ)⁻¹ • H)) ^ n = _
    rw [← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'),
      one_smul]
  have hlimit := hdiff.add_const (NormedSpace.exp H)
  simp only [zero_add] at hlimit
  apply hlimit.congr'
  filter_upwards [hGeq] with n hn
  rw [← hn, sub_add_cancel]

end NormedSpace

/-- The Euler power limit for a differentiable curve through the identity of a Banach algebra. -/
theorem HasDerivAt.tendsto_pow_inv_nat {𝕜 A : Type*} [RCLike 𝕜] [NormedRing A] [NormOneClass A]
    [NormedAlgebra 𝕜 A] [NormedAlgebra ℝ A] [CompleteSpace A] {f : 𝕜 → A} {D : A}
    (hf : HasDerivAt f D 0) (h0 : f 0 = 1) :
    Tendsto (fun k : ℕ => (f (k : 𝕜)⁻¹) ^ k) atTop (𝓝 (NormedSpace.exp D)) := by
  apply NormedSpace.tendsto_pow_exp_of_tangent
  have ht : Tendsto (fun k : ℕ => (k : 𝕜)⁻¹) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    exact inv_ne_zero (Nat.cast_ne_zero.mpr hk.ne')
  simpa only [Function.comp_def, zero_add, h0, inv_inv, Nat.cast_smul_eq_nsmul] using
    hf.tendsto_slope_zero.comp ht
