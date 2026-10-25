/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Integrals against a composition of a measure and a kernel, and convex order

The integral against $\kappa \circ \mu$ is the iterated integral
(`MeasureTheory.Measure.integral_comp`, the measure form of
`ProbabilityTheory.Kernel.integral_comp`). Its first consequence is the easy direction of
Strassen's theorem: if $X$ is the conditional barycenter of $Y$ under a Markov kernel, Jensen's
inequality in each fibre and integration give $\mathbb{E} f(X) \le \mathbb{E} f(Y)$ for every
convex $f$ (`ConvexOn.integral_comp_le_integral_comp_of_integral_eq`). Hoeffding's comparison of
sampling without and with replacement is its instance in `NLAlib.Probability.ConvexOrder`.
Upstream candidates for `Mathlib.Probability.Kernel.Composition.IntegralCompProd`.

## Main results

* `MeasureTheory.Measure.integral_comp`: the integral against $\kappa \circ \mu$.
* `ConvexOn.integral_comp_le_integral_comp_of_integral_eq`: convex order from a conditional
  barycenter, in kernel form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

variable {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {s : Set E} {f : E → ℝ}

namespace MeasureTheory

/-- The integral against a composition $\kappa \circ \mu$ is the iterated integral; the measure
form of `ProbabilityTheory.Kernel.integral_comp`. -/
theorem Measure.integral_comp {μ : Measure α} {κ : Kernel α β} {g : β → ℝ}
    (hg : Integrable g (κ ∘ₘ μ)) :
    ∫ b, g b ∂(κ ∘ₘ μ) = ∫ a, ∫ b, g b ∂(κ a) ∂μ := by
  have hc : κ ∘ₘ μ = (κ ∘ₖ Kernel.const Unit μ) () := Measure.comp_eq_comp_const_apply
  rw [hc] at hg ⊢
  rw [Kernel.integral_comp hg, Kernel.const_apply]

end MeasureTheory

/-- Convex order from a conditional barycenter: let $\kappa$ be a Markov kernel from $\alpha$
to $\beta$, $\mu$ a measure on $\alpha$, and $X : \alpha \to E$, $Y : \beta \to E$ with
$Y$ integrable under almost every $\kappa(a)$ and with barycenter
$\int Y \, d\kappa(a) = X(a)$. Then for every $f$ convex and continuous on a closed set $s$
holding the values of $Y$,
$$\int f(X(a)) \, d\mu(a) \le \int f(Y(b)) \, d(\kappa \circ \mu)(b) \,.$$
Jensen's inequality (`ConvexOn.map_integral_le`) in each fibre, then integration in $a$. This is
the easy direction of Strassen's theorem (Strassen 1965, not in hand); proved from Jensen's
inequality alone. The integrability of $f \circ X$ is a hypothesis: it follows from that of
$f \circ Y$ only through a supporting hyperplane and a measurability argument, and every consumer
has it from finiteness. -/
theorem ConvexOn.integral_comp_le_integral_comp_of_integral_eq (hf : ConvexOn ℝ s f)
    (hfc : ContinuousOn f s) (hs : IsClosed s) {μ : Measure α} {κ : Kernel α β}
    [IsMarkovKernel κ] {X : α → E} {Y : β → E} (hY : ∀ᵐ a ∂μ, Integrable Y (κ a))
    (hYs : ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), Y b ∈ s) (hbar : ∀ᵐ a ∂μ, ∫ b, Y b ∂(κ a) = X a)
    (hfX : Integrable (fun a => f (X a)) μ) (hfY : Integrable (fun b => f (Y b)) (κ ∘ₘ μ)) :
    ∫ a, f (X a) ∂μ ≤ ∫ b, f (Y b) ∂(κ ∘ₘ μ) := by
  have hc : κ ∘ₘ μ = (κ ∘ₖ Kernel.const Unit μ) () := Measure.comp_eq_comp_const_apply
  have hfY' : Integrable (fun b => f (Y b)) ((κ ∘ₖ Kernel.const Unit μ) ()) := hc ▸ hfY
  have hint : Integrable (fun a => ∫ b, f (Y b) ∂(κ a)) μ := by
    simpa only [Kernel.const_apply] using hfY'.integral_comp
  have hfYa : ∀ᵐ a ∂μ, Integrable (fun b => f (Y b)) (κ a) :=
    Measure.ae_integrable_of_integrable_comp hfY
  rw [Measure.integral_comp hfY]
  refine integral_mono_ae hfX hint ?_
  filter_upwards [hY, hYs, hbar, hfYa] with a h1 h2 h3 h4
  rw [← h3]
  exact hf.map_integral_le hfc hs h2 h1 h4
