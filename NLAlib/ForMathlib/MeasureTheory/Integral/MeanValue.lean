/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Connected.Basic

/-!
# A mean value theorem for integrals of pointwise intermediate values

If $F(x) = D(\xi_x)W(x)$ almost everywhere with $\xi_x$ in a connected set $s$, $D$ continuous
on $s$ and $W$ of constant sign, then $\int F = D(\xi)\int W$ for a single $\xi \in s$. The
pointwise points $\xi_x$ need not depend measurably on $x$: the proof compares $\int F$ with
$d\int W$ for the average $d$ and uses only that $D(s)$ is an interval. This turns a pointwise
interpolation remainder into the integral (quadrature) remainder. Mathlib's
`exists_eq_const_mul_setIntegral_of_ae_nonneg` needs the integrand in the form $f(x)g(x)$ with
$f$ continuous, which a pointwise remainder is not. Upstream candidate for
`Mathlib.MeasureTheory.Integral.MeanValue`.

Design: stage KS8 (`docs/design/Polynomial-QuadratureRemainder.md`, F4, F5).

## Main results

* `exists_integral_eq_mul_integral_of_ae_nonneg`: nonnegative weight.
* `exists_integral_eq_mul_integral_of_ae_nonpos`: nonpositive weight.
-/

@[expose] public section

open MeasureTheory

/-- If $F(x) = D(\xi_x)W(x)$ a.e. with $W \ge 0$, $D < d$ on the points $\xi_x$ and
$\int F = d\int W$, then $W = 0$ a.e. -/
private lemma ae_eq_zero_of_forall_lt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F W : Ω → ℝ} (hF : Integrable F μ) (hW : Integrable W μ) (hW0 : ∀ᵐ x ∂μ, 0 ≤ W x)
    {s : Set ℝ} {D : ℝ → ℝ} {d : ℝ} (h : ∀ᵐ x ∂μ, ∃ ξ ∈ s, F x = D ξ * W x)
    (hall : ∀ ξ ∈ s, D ξ < d) (hFd : ∫ x, F x ∂μ = d * ∫ x, W x ∂μ) : W =ᵐ[μ] 0 := by
  have hle : 0 ≤ᵐ[μ] fun x => d * W x - F x := by
    filter_upwards [h, hW0] with x ⟨ξ, hξ, hFx⟩ hWx
    rw [Pi.zero_apply, hFx, ← sub_mul]
    exact mul_nonneg (sub_nonneg.2 (hall ξ hξ).le) hWx
  have hz := (integral_eq_zero_iff_of_nonneg_ae hle ((hW.const_mul d).sub hF)).mp
    (by rw [integral_sub (hW.const_mul d) hF, integral_const_mul, hFd, sub_self])
  filter_upwards [h, hz] with x ⟨ξ, hξ, hFx⟩ hzx
  have : (d - D ξ) * W x = 0 := by
    simp only [Pi.zero_apply] at hzx
    linear_combination hzx + hFx
  exact (mul_eq_zero.mp this).resolve_left (sub_pos.2 (hall ξ hξ)).ne'

/-- The integral mean value theorem for pointwise intermediate values: for a measure $\mu$,
integrable $F$ and $W$ with $W \ge 0$ almost everywhere, a connected $s \subseteq \mathbb{R}$
and $D$ continuous on $s$, if for almost every $x$ there is $\xi_x \in s$ with
$F(x) = D(\xi_x)W(x)$, then $\int F\,d\mu = D(\xi)\int W\,d\mu$ for some $\xi \in s$. No
measurability of $x \mapsto \xi_x$ is assumed, and $\int W\,d\mu = 0$ is allowed. -/
theorem exists_integral_eq_mul_integral_of_ae_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F W : Ω → ℝ} (hF : Integrable F μ) (hW : Integrable W μ)
    (hW0 : ∀ᵐ x ∂μ, 0 ≤ W x) {s : Set ℝ} (hs : IsConnected s) {D : ℝ → ℝ}
    (hD : ContinuousOn D s) (h : ∀ᵐ x ∂μ, ∃ ξ ∈ s, F x = D ξ * W x) :
    ∃ ξ ∈ s, ∫ x, F x ∂μ = D ξ * ∫ x, W x ∂μ := by
  obtain ⟨ξ0, hξ0⟩ := hs.nonempty
  by_cases hW0' : ∫ x, W x ∂μ = 0
  · -- degenerate case: `W = 0` a.e., hence `F = 0` a.e.
    have hWz : W =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hW0 hW).mp hW0'
    have hFz : ∫ x, F x ∂μ = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [h, hWz] with x hx hwx
      obtain ⟨ξ, -, hFx⟩ := hx
      simp [hFx, hwx]
    exact ⟨ξ0, hξ0, by rw [hFz, hW0', mul_zero]⟩
  set d := (∫ x, F x ∂μ) / ∫ x, W x ∂μ
  have hFd : ∫ x, F x ∂μ = d * ∫ x, W x ∂μ := (div_mul_cancel₀ _ hW0').symm
  by_contra hcon
  push Not at hcon
  have hmiss : ∀ ξ ∈ s, D ξ ≠ d := fun ξ hξ heq => hcon ξ hξ (by rw [hFd, heq])
  -- `D(s)` is an interval missing `d`, so it lies on one side of `d`
  have hside : ∀ ξ ∈ s, ∀ η ∈ s, D ξ < d → d < D η → False := fun ξ hξ η hη h₁ h₂ => by
    obtain ⟨θ, hθ, hθd⟩ := (hs.isPreconnected.image D hD).Icc_subset ⟨ξ, hξ, rfl⟩ ⟨η, hη, rfl⟩
      ⟨h₁.le, h₂.le⟩
    exact hmiss θ hθ hθd
  refine hW0' (integral_eq_zero_of_ae ?_)
  rcases (hmiss ξ0 hξ0).lt_or_gt with hlt | hgt
  · exact ae_eq_zero_of_forall_lt hF hW hW0 h
      (fun ξ hξ => (hmiss ξ hξ).lt_or_gt.resolve_right (hside ξ0 hξ0 ξ hξ hlt)) hFd
  · refine ae_eq_zero_of_forall_lt (D := -D) hF.neg hW hW0
      (h.mono fun x ⟨ξ, hξ, hx⟩ => ⟨ξ, hξ, by simp [hx]⟩)
      (fun ξ hξ => neg_lt_neg ((hmiss ξ hξ).lt_or_gt.resolve_left (hside ξ hξ ξ0 hξ0 · hgt)))
      (d := -d) ?_
    rw [Pi.neg_def, integral_neg, hFd, neg_mul]

/-- The integral mean value theorem for pointwise intermediate values, nonpositive weight:
as `exists_integral_eq_mul_integral_of_ae_nonneg` with $W \le 0$ almost everywhere: for a
measure $\mu$, integrable $F$ and $W$ with $W \le 0$ a.e., a connected $s \subseteq \mathbb{R}$
and $D$ continuous on $s$, if for almost every $x$ there is $\xi_x \in s$ with
$F(x) = D(\xi_x)W(x)$, then $\int F\,d\mu = D(\xi)\int W\,d\mu$ for some $\xi \in s$. -/
theorem exists_integral_eq_mul_integral_of_ae_nonpos {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F W : Ω → ℝ} (hF : Integrable F μ) (hW : Integrable W μ)
    (hW0 : ∀ᵐ x ∂μ, W x ≤ 0) {s : Set ℝ} (hs : IsConnected s) {D : ℝ → ℝ}
    (hD : ContinuousOn D s) (h : ∀ᵐ x ∂μ, ∃ ξ ∈ s, F x = D ξ * W x) :
    ∃ ξ ∈ s, ∫ x, F x ∂μ = D ξ * ∫ x, W x ∂μ := by
  obtain ⟨ξ, hξ, hint⟩ := exists_integral_eq_mul_integral_of_ae_nonneg
    hF.neg hW.neg (hW0.mono fun x hx => by simpa using hx) hs hD
    (h.mono fun x ⟨ξ, hξ, hx⟩ => ⟨ξ, hξ, by simp [hx]⟩)
  refine ⟨ξ, hξ, ?_⟩
  simp only [Pi.neg_apply, integral_neg, mul_neg, neg_inj] at hint
  exact hint
