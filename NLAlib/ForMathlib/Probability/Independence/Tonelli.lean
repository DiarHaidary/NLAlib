/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Independence.Basic

/-!
# Iterated integrals against an independent pair

If $U$ and $W$ are independent, the lower integral of a measurable $f \ge 0$ of the pair is the
iterated integral against the two laws,
$\int f(U, W)\,d\mu = \int\!\int f(u, w)\,d\mu_W(w)\,d\mu_U(u)$: the joint law is the product
(`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`) and Tonelli's theorem applies
(`MeasureTheory.lintegral_prod`). This is the conditioning step of every expectation of two
independent random matrices. Upstream candidate for `Mathlib/Probability/Independence/Basic.lean`;
a side file that merges into `NLAlib/ForMathlib/Probability/Independence/Basic.lean`
(`docs/design/LowRank-S6.md` §4, L1).

## Main results

* `ProbabilityTheory.IndepFun.lintegral_comp_eq_lintegral_lintegral`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Iterated integral against an independent pair** (Tonelli): for independent $U$, $W$ and a
measurable $f \ge 0$,
$$\int f(U, W)\,d\mu = \int\!\!\int f(u, w)\,d\mu_W(w)\,d\mu_U(u)\,,$$
with $\mu_U$, $\mu_W$ the laws of $U$ and $W$. Upstream candidate. -/
theorem IndepFun.lintegral_comp_eq_lintegral_lintegral [IsFiniteMeasure μ] {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {U : Ω → α} {W : Ω → β} (hUW : IndepFun U W μ)
    (hU : AEMeasurable U μ) (hW : AEMeasurable W μ) {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (U ω, W ω) ∂μ = ∫⁻ u, ∫⁻ w, f (u, w) ∂(μ.map W) ∂(μ.map U) := by
  rw [← lintegral_map' hf.aemeasurable (hU.prodMk hW),
    (indepFun_iff_map_prod_eq_prod_map_map hU hW).1 hUW, lintegral_prod _ hf.aemeasurable]

end ProbabilityTheory
