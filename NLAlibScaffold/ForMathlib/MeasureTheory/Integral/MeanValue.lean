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
  sorry

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
  sorry
