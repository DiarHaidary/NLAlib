/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.InfinitePi
public import NLAlib.ForMathlib.Probability.Independence.Basic

/-!
# Conditioning on the past of an i.i.d. sequence

An i.i.d. sequence with law $\nu$ is a random variable $\xi : \Omega \to (\mathbb{N} \to \beta)$
with law `Measure.infinitePi fun _ : ℕ => ν`. A measurable function $F$ of the sequence that
depends only on its first $q$ terms is independent of the $q$-th term, so an expectation of a
function of the pair $(F(\xi), \xi_q)$ is the expectation over the past of the average over a
fresh sample, $\int f(F(\xi), \xi_q)\,d\mu = \int\!\int f(F(\xi), s)\,d\nu(s)\,d\mu$. This is the
one probabilistic step of every expectation bound for an iterated random method (randomized
Kaczmarz, sketch-and-project) without conditional expectations.

Mathlib has the product measure and the independence of its coordinates
(`ProbabilityTheory.iIndepFun_iff_hasLaw_Pi_infinitePi`) but not this statement. Upstream
candidate for `Mathlib/Probability/Independence/InfinitePi.lean`.

Design: `docs/design/Regression-Kaczmarz.md` §4.

## Main results

* `ProbabilityTheory.HasLaw.integral_comp_eq_integral_integral_of_dependsOn`: conditioning on
  the past of an i.i.d. sequence.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Conditioning on the past of an i.i.d. sequence** (Fubini): for an i.i.d. sequence
$\xi = (\xi_0, \xi_1, \dots)$ with law $\nu$ (the hypothesis
`HasLaw ξ (Measure.infinitePi fun _ : ℕ => ν) μ`), a measurable $F$ of the sequence that depends
only on $\xi_0, \dots, \xi_{q-1}$, and $f$ integrable for the product of the law of $F(\xi)$ and
$\nu$,
$$\int f(F(\xi), \xi_q)\,d\mu = \int\!\!\int f(F(\xi), s)\,d\nu(s)\,d\mu\,.$$
The $q$-th term is independent of $F(\xi)$
(`ProbabilityTheory.iIndepFun.indepFun_comp_of_dependsOn`), and the joint law is the product.
Upstream candidate. -/
theorem HasLaw.integral_comp_eq_integral_integral_of_dependsOn {β α E : Type*}
    [MeasurableSpace β] [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν : Measure β} [IsProbabilityMeasure ν] {ξ : Ω → ℕ → β}
    (hξ : HasLaw ξ (Measure.infinitePi fun _ : ℕ => ν) μ) {q : ℕ} {F : (ℕ → β) → α}
    (hF : Measurable F) (hFq : DependsOn F (Set.Iio q))
    {f : α × β → E} (hf : Integrable f ((μ.map fun ω => F (ξ ω)).prod ν)) :
    ∫ ω, f (F (ξ ω), ξ ω q) ∂μ = ∫ ω, ∫ s, f (F (ξ ω), s) ∂ν ∂μ := by
  have : IsProbabilityMeasure μ := hξ.isProbabilityMeasure
  have hev : ∀ i, HasLaw (fun ω => ξ ω i) ν μ := fun i =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) i).fun_comp_hasLaw hξ
  have hind : iIndepFun (fun i ω => ξ ω i) μ :=
    (iIndepFun_iff_hasLaw_Pi_infinitePi hev hξ.aemeasurable).2 hξ
  have hFq' : DependsOn F ↑(Finset.range q) := by
    rwa [Finset.coe_range]
  have hUW : IndepFun (fun ω => F (ξ ω)) (fun ω => ξ ω q) μ :=
    hind.indepFun_comp_of_dependsOn (fun i => (hev i).aemeasurable) (by simp) hF hFq'
  have hU : AEMeasurable (fun ω => F (ξ ω)) μ := hF.comp_aemeasurable hξ.aemeasurable
  have hW : AEMeasurable (fun ω => ξ ω q) μ := (hev q).aemeasurable
  have hWmap : μ.map (fun ω => ξ ω q) = ν := (hev q).map_eq
  rw [IndepFun.integral_comp_eq_integral_integral hUW hU hW (by rwa [hWmap]), hWmap]
  exact integral_map hU hf.integral_prod_left.aestronglyMeasurable

end ProbabilityTheory
