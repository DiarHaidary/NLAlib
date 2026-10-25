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

/-- **The integral mean value theorem for pointwise intermediate values**: for a measure $\mu$,
integrable $F$ and $W$ with $W \ge 0$ almost everywhere, a connected $s \subseteq \mathbb{R}$
and $D$ continuous on $s$, if for almost every $x$ there is $\xi_x \in s$ with
$F(x) = D(\xi_x)W(x)$, then $\int F\,d\mu = D(\xi)\int W\,d\mu$ for some $\xi \in s$. No
measurability of $x \mapsto \xi_x$ is assumed, and $\int W\,d\mu = 0$ is allowed.
Proof: M, about 50 lines; the prototype proves it
(`MeasureTheory.exists_integral_eq_mul_integral_of_pointwise`,
`NLAlib/ForMathlib/MeasureTheory/IntegralMeanValue.lean`). If $\int W = 0$ then $W = 0$ and
$F = 0$ a.e. (`integral_eq_zero_iff_of_nonneg_ae`). Otherwise let $d = \int F/\int W$; if no
$\xi$ has $D(\xi) = d$, then $D(s)$ lies on one side of $d$ (`IsPreconnected.mapsTo_Ioi_or_Iio`
style, or `IsPreconnected.image` and the intermediate value property), so $F \ge dW$ a.e. (or
$\le$) with equal integrals, hence $F = dW$ a.e. (`integral_eq_iff_of_ae_le`), which forces
$W = 0$ a.e., a contradiction. -/
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
  set d := (∫ x, F x ∂μ) / ∫ x, W x ∂μ with hd
  have hFd : ∫ x, F x ∂μ = d * ∫ x, W x ∂μ := (div_mul_cancel₀ _ hW0').symm
  by_contra hcon
  push_neg at hcon
  have hmiss : ∀ ξ ∈ s, D ξ ≠ d := fun ξ hξ heq => hcon ξ hξ (by rw [hFd, heq])
  have hsD : IsPreconnected (D '' s) := hs.isPreconnected.image D hD
  rcases lt_or_gt_of_ne (hmiss ξ0 hξ0) with hlt | hgt
  · -- all values of `D` on `s` lie below `d`
    have hall : ∀ ξ ∈ s, D ξ < d := by
      intro ξ hξ
      rcases lt_or_gt_of_ne (hmiss ξ hξ) with h1 | h1
      · exact h1
      · exfalso
        have hmem : d ∈ D '' s := hsD.Icc_subset ⟨ξ0, hξ0, rfl⟩ ⟨ξ, hξ, rfl⟩ ⟨hlt.le, h1.le⟩
        obtain ⟨η, hη, hηd⟩ := hmem
        exact hmiss η hη hηd
    have hle : ∀ᵐ x ∂μ, F x ≤ d * W x := by
      filter_upwards [h, hW0] with x hx hwx
      obtain ⟨ξ, hξ, hFx⟩ := hx
      rw [hFx]
      exact mul_le_mul_of_nonneg_right (hall ξ hξ).le hwx
    have hint : ∫ x, (d * W x - F x) ∂μ = 0 := by
      rw [integral_sub (hW.const_mul d) hF, integral_const_mul, hFd, sub_self]
    have hz : (fun x => d * W x - F x) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (by filter_upwards [hle] with x hx; simpa using hx)
        ((hW.const_mul d).sub hF)).mp hint
    have hWz : W =ᵐ[μ] 0 := by
      filter_upwards [h, hz, hW0] with x hx hzx hwx
      obtain ⟨ξ, hξ, hFx⟩ := hx
      simp only [Pi.zero_apply] at hzx ⊢
      have hpos : 0 < d - D ξ := by linarith [hall ξ hξ]
      have : (d - D ξ) * W x = 0 := by linarith [hFx, hzx]
      exact (mul_eq_zero.mp this).resolve_left hpos.ne'
    exact hW0' (integral_eq_zero_of_ae hWz)
  · -- all values of `D` on `s` lie above `d`
    have hall : ∀ ξ ∈ s, d < D ξ := by
      intro ξ hξ
      rcases lt_or_gt_of_ne (hmiss ξ hξ) with h1 | h1
      · exfalso
        have hmem : d ∈ D '' s := hsD.Icc_subset ⟨ξ, hξ, rfl⟩ ⟨ξ0, hξ0, rfl⟩ ⟨h1.le, hgt.le⟩
        obtain ⟨η, hη, hηd⟩ := hmem
        exact hmiss η hη hηd
      · exact h1
    have hle : ∀ᵐ x ∂μ, d * W x ≤ F x := by
      filter_upwards [h, hW0] with x hx hwx
      obtain ⟨ξ, hξ, hFx⟩ := hx
      rw [hFx]
      exact mul_le_mul_of_nonneg_right (hall ξ hξ).le hwx
    have hint : ∫ x, (F x - d * W x) ∂μ = 0 := by
      rw [integral_sub hF (hW.const_mul d), integral_const_mul, hFd, sub_self]
    have hz : (fun x => F x - d * W x) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (by filter_upwards [hle] with x hx; simpa using hx)
        (hF.sub (hW.const_mul d))).mp hint
    have hWz : W =ᵐ[μ] 0 := by
      filter_upwards [h, hz, hW0] with x hx hzx hwx
      obtain ⟨ξ, hξ, hFx⟩ := hx
      simp only [Pi.zero_apply] at hzx ⊢
      have hpos : 0 < D ξ - d := by linarith [hall ξ hξ]
      have : (D ξ - d) * W x = 0 := by linarith [hFx, hzx]
      exact (mul_eq_zero.mp this).resolve_left hpos.ne'
    exact hW0' (integral_eq_zero_of_ae hWz)

/-- **The integral mean value theorem for pointwise intermediate values, nonpositive weight**:
as `exists_integral_eq_mul_integral_of_ae_nonneg` with $W \le 0$ almost everywhere: for a
measure $\mu$, integrable $F$ and $W$ with $W \le 0$ a.e., a connected $s \subseteq \mathbb{R}$
and $D$ continuous on $s$, if for almost every $x$ there is $\xi_x \in s$ with
$F(x) = D(\xi_x)W(x)$, then $\int F\,d\mu = D(\xi)\int W\,d\mu$ for some $\xi \in s$.
Proof: S, about 10 lines. Apply `exists_integral_eq_mul_integral_of_ae_nonneg` to $-F$ and $-W$
(`Integrable.neg`, `integral_neg`, `mul_neg`), as the prototype's
`exists_integral_eq_mul_integral_of_pointwise_of_weight_constant_sign`. -/
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
