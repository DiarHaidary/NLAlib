/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Approximation.ChebyshevSeries
public import NLAlib.Polynomial.Approximation.BernsteinEllipse
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Analytic decay of canonical Chebyshev coefficients

A compatible holomorphic extension bounded on an open Bernstein ellipse gives geometric decay
of the canonical coefficients. Contour estimates use smaller radii and a limit, without continuity
on the outer boundary. All contour expressions are private proof machinery.

## Main results

* `NLAlib.norm_chebyshevCoeff_le_of_open_ellipse`: positive coefficients obey $2M/\rho^k$.
-/

@[expose] public section

open MeasureTheory Polynomial Polynomial.Chebyshev Complex Set Filter Metric
open scoped Topology

namespace NLAlib

attribute [local instance] Polynomial.instTwoPiPos

private lemma joukowski_unit {w : ℂ} (hw : ‖w‖ = 1) :
    (w + w⁻¹) / 2 = (w.re : ℂ) := by
  rw [Complex.inv_eq_conj hw, Complex.add_conj]
  push_cast
  ring

private lemma fourier_one_circleMap (θ : ℝ) :
    fourier 1 (θ : AddCircle (2 * Real.pi)) = circleMap 0 1 θ := by
  rw [fourier_coe_apply]
  simp only [circleMap, Complex.ofReal_one, one_mul, zero_add]
  congr 1
  push_cast
  field_simp

private lemma fourier_nat_pow (k : ℕ) (θ : AddCircle (2 * Real.pi)) :
    fourier (k : ℤ) θ = fourier 1 θ ^ k := by
  induction k with
  | zero => simp only [Nat.cast_zero, fourier_zero, pow_zero]
  | succ k ih => rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

private lemma fourier_contour (F : ℂ → ℂ) (k : ℕ) :
    fourierCoeff (fun θ : AddCircle (2 * Real.pi) => F ((fourier 1 θ).re)) (k : ℤ) =
      (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ w in C(0, 1), F ((w + w⁻¹) / 2) / w ^ (k + 1)) := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add, circleIntegral]
  have heq : ∀ θ : ℝ,
      deriv (circleMap (0 : ℂ) 1) θ •
        (F ((circleMap 0 1 θ + (circleMap 0 1 θ)⁻¹) / 2) / circleMap 0 1 θ ^ (k + 1)) =
        I * (fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) •
          F ((fourier 1 (θ : AddCircle (2 * Real.pi))).re)) := by
    intro θ
    rw [deriv_circleMap, ← fourier_one_circleMap, fourier_neg, fourier_nat_pow]
    have hn : ‖fourier (1 : ℤ) (θ : AddCircle (2 * Real.pi))‖ = 1 := Circle.norm_coe _
    have hz : fourier (1 : ℤ) (θ : AddCircle (2 * Real.pi)) ≠ 0 :=
      norm_ne_zero_iff.mp (by rw [hn]; norm_num)
    rw [map_pow, ← Complex.inv_eq_conj hn, inv_pow, pow_succ, joukowski_unit hn]
    simp only [smul_eq_mul]
    field_simp
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  field_simp

private lemma annulus_image {ρ r : ℝ} (hρ : 1 < ρ) (hr : r < ρ) {w : ℂ}
    (hw : w ∈ closedBall (0 : ℂ) r \ ball 0 1) :
    (w + w⁻¹) / 2 ∈ openBernsteinEllipse ρ := by
  have hn : 1 ≤ ‖w‖ ∧ ‖w‖ ≤ r := by
    simpa only [Set.mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt] using
      And.intro hw.2 hw.1
  apply joukowski_mem_openBernsteinEllipse hρ
  exact ⟨((inv_lt_one₀ (zero_lt_one.trans hρ)).mpr hρ).trans_le hn.1, hn.2.trans_lt hr⟩

private lemma contour_radius {F : ℂ → ℂ} {ρ r : ℝ} (hρ : 1 < ρ)
    (hr : 1 < r) (hrρ : r < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ)) (k : ℕ) :
    (∮ w in C(0, 1), F ((w + w⁻¹) / 2) / w ^ (k + 1)) =
      ∮ w in C(0, r), F ((w + w⁻¹) / 2) / w ^ (k + 1) := by
  have hnonzero : ∀ w ∈ closedBall (0 : ℂ) r \ ball 0 1, w ≠ 0 := by
    intro w hw hzero
    have h := hw.2
    norm_num [hzero] at h
  have hj : ContinuousOn (fun w : ℂ => (w + w⁻¹) / 2)
      (closedBall (0 : ℂ) r \ ball 0 1) :=
    (continuousOn_id.add (continuousOn_id.inv₀ hnonzero)).div_const 2
  have hc : ContinuousOn (fun w : ℂ => F ((w + w⁻¹) / 2) / w ^ (k + 1))
      (closedBall (0 : ℂ) r \ ball 0 1) :=
    (hFd.continuousOn.comp hj (fun w hw => annulus_image hρ hrρ hw)).div
      (continuousOn_id.pow _) (fun w hw => pow_ne_zero _ (hnonzero w hw))
  have hd : ∀ w ∈ (ball (0 : ℂ) r \ closedBall 0 1) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun w : ℂ => F ((w + w⁻¹) / 2) / w ^ (k + 1)) w := by
    intro w hw
    have hwc : w ∈ closedBall (0 : ℂ) r \ ball 0 1 :=
      ⟨mem_closedBall.mpr (le_of_lt (mem_ball.mp hw.1.1)), fun h =>
        hw.1.2 (mem_closedBall.mpr (le_of_lt (mem_ball.mp h)))⟩
    have hw0 := hnonzero w hwc
    have hF := hFd.differentiableAt ((isOpen_openBernsteinEllipse ρ).mem_nhds
      (annulus_image hρ hrρ hwc))
    have hJ := ((differentiableAt_id.add (differentiableAt_id.inv hw0)).div_const (2 : ℂ))
    exact (hF.comp w hJ).div (differentiableAt_id.pow _) (pow_ne_zero _ hw0)
  exact (Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    (by norm_num : (0 : ℝ) < 1) hr.le countable_empty hc hd).symm

private lemma contour_norm {F : ℂ → ℂ} {ρ r M : ℝ} (hρ : 1 < ρ)
    (hr : 1 < r) (hrρ : r < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M) (k : ℕ) :
    ‖(2 * Real.pi * I : ℂ)⁻¹ *
      (∮ w in C(0, 1), F ((w + w⁻¹) / 2) / w ^ (k + 1))‖ ≤ M / r ^ k := by
  rw [contour_radius hρ hr hrρ hFd]
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hb : ∀ w ∈ sphere (0 : ℂ) r,
      ‖F ((w + w⁻¹) / 2) / w ^ (k + 1)‖ ≤ M / r ^ (k + 1) := by
    intro w hw
    have hn : ‖w‖ = r := by simpa only [mem_sphere, dist_zero_right] using hw
    rw [norm_div, norm_pow, hn]
    apply div_le_div_of_nonneg_right _ (pow_nonneg hr0.le _)
    have hj : (w + w⁻¹) / 2 ∈ openBernsteinEllipse ρ := by
      apply joukowski_mem_openBernsteinEllipse hρ
      rw [hn]
      exact ⟨((inv_lt_one₀ (zero_lt_one.trans hρ)).mpr hρ).trans hr, hrρ⟩
    simpa only [dist_zero_right] using hM.apply hj
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr0.le hb
  change ‖(2 * Real.pi * I : ℂ)⁻¹ * _‖ ≤ _ at h
  refine h.trans_eq ?_
  rw [pow_succ]
  field_simp

private lemma complex_coeff_radius {F : ℂ → ℂ} {ρ r M : ℝ} (hρ : 1 < ρ)
    (hr : 1 < r) (hrρ : r < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    {k : ℕ} (hk : 0 < k) :
    ‖chebyshevCoeff (fun x : ℝ => F (x : ℂ)) k‖ ≤ 2 * M / r ^ k := by
  have hf : ContinuousOn (fun x : ℝ => F (x : ℂ)) (Icc (-1 : ℝ) 1) :=
    hFd.continuousOn.comp Complex.continuous_ofReal.continuousOn
      (fun x hx => ofReal_mem_openBernsteinEllipse hρ hx)
  have hd := fourierCoeff_cosinePullback_eq_chebyshevCoeff hf (k : ℤ)
  simp only [Int.natAbs_natCast, Nat.cast_eq_zero, if_neg hk.ne'] at hd
  rw [fourier_contour] at hd
  have h := contour_norm hρ hr hrρ hFd hM k
  rw [hd, norm_div, Complex.norm_two] at h
  rw [mul_div_assoc]
  linarith

/-- A compatible extension holomorphic and bounded by $M$ on the OPEN Bernstein ellipse gives
$$\|a_k\|\le\frac{2M}{\rho^k}\quad(k>0).$$
[Trefethen2019, Theorem 8.1], generalized to RCLike values via the compatible complex extension.
The proof takes smaller radii up to $\rho$; no outer-boundary continuity is assumed. The zero
coefficient has the more general bound `norm_chebyshevCoeff_zero_le`.

Result: chebyshev-coeff-analytic-decay
-/
theorem norm_chebyshevCoeff_le_of_open_ellipse
    {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun x => RCLike.toComplex (f x))
      (fun x : ℝ => F (x : ℂ)) (Set.Icc (-1 : ℝ) 1)) {k : ℕ} (hk : 0 < k) :
    ‖chebyshevCoeff f k‖ ≤ 2 * M / ρ ^ k := by
  have hc : RCLike.toComplex (chebyshevCoeff f k) =
      chebyshevCoeff (fun x : ℝ => F (x : ℂ)) k := by
    rw [toComplex_chebyshevCoeff]
    unfold chebyshevCoeff
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact congrArg (fun z : ℂ => z * (Real.cos ((k : ℝ) * θ) : ℂ))
      (hExt ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
  have hb : ∀ r ∈ Ioo (1 : ℝ) ρ, ‖chebyshevCoeff f k‖ ≤ 2 * M / r ^ k := by
    intro r hr
    rw [← RCLike.norm_toComplex (chebyshevCoeff f k), hc]
    exact complex_coeff_radius hρ hr.1 hr.2 hFd hM hk
  have ht : ContinuousAt (fun r : ℝ => 2 * M / r ^ k) ρ :=
    continuousAt_const.div (continuousAt_id.pow _) (pow_ne_zero _ (zero_lt_one.trans hρ).ne')
  have : NeBot (𝓝[Ioo (1 : ℝ) ρ] ρ) := right_nhdsWithin_Ioo_neBot hρ
  exact ge_of_tendsto ht.continuousWithinAt.tendsto
    (Filter.mem_of_superset self_mem_nhdsWithin (fun r hr => hb r hr))

end NLAlib
