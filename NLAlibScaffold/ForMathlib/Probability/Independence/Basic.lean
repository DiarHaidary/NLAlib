/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import NLAlib.ForMathlib.Probability.Independence.Basic

/-!
# The freezing lemma: the theorems of stage LB-A

Statements for `NLAlib/ForMathlib/Probability/Independence/Basic.lean` whose proofs are deferred
(`docs/design/Probability-MatvecQueryModel.md`, §3.3). If $Z$ is independent of $T$, then in a
function $F(T, Z)$ the variable $T$ may be frozen: the joint law of $(T, F(T, Z))$ is determined
by the laws $F(t, Z)$ for fixed $t$. This is the step of every deferred-decision argument where a
transcript-dependent rotation or projection acts on an independent Gaussian or Haar matrix.
Upstream candidates.

## Main results

* `ProbabilityTheory.IndepFun.identDistrib_prodMk_of_forall_map_eq`: equal laws for every frozen
  $t$ give equal joint laws.
* `ProbabilityTheory.IndepFun.hasLaw_prodMk_prod_of_forall_map_eq`: a law $\nu$ not depending on
  $t$ makes $F(T, Z)$ independent of $T$ with law $\nu$.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {α γ δ : Type*}
  [MeasurableSpace α] [MeasurableSpace γ] [MeasurableSpace δ]

/-- The freezing lemma: let $Z$ be independent of $T$ and $F$, $G$ jointly measurable. If for
every fixed $t$ the variables $F(t, Z)$ and $G(t, Z)$ have the same law, then $(T, F(T, Z))$ and
$(T, G(T, Z))$ have the same joint law.
Proof: M, about 25 lines. With $\mu_T$, $\mu_Z$ the laws, the law of $(T, Z)$ is
`(μ.map T).prod (μ.map Z)` (`indepFun_iff_map_prod_eq_prod_map_map`); the two pairs are its
images under $(t, z) \mapsto (t, F(t, z))$ and $(t, G(t, z))$
(`AEMeasurable.map_map_of_aemeasurable`). Two finite measures on `α × δ` agree when they agree on
measurable sets $E$ (`Measure.ext`); by `Measure.map_apply` and `Measure.prod_apply` both are
$\int \mu_Z\{z \mid (t, F(t, z)) \in E\}\,d\mu_T(t)$, and the integrands agree pointwise since
$\{z \mid (t, F(t, z)) \in E\} = F(t, \cdot)^{-1}(E_t)$ with $E_t$ the section
(`measurable_prodMk_left`) and `h t` evaluated at $E_t$. -/
theorem IndepFun.identDistrib_prodMk_of_forall_map_eq [IsFiniteMeasure μ] {T : Ω → α}
    {Z : Ω → γ} (hTZ : IndepFun T Z μ) (hT : AEMeasurable T μ) (hZ : AEMeasurable Z μ)
    {F G : α → γ → δ} (hF : Measurable (Function.uncurry F))
    (hG : Measurable (Function.uncurry G))
    (h : ∀ t, (μ.map Z).map (F t) = (μ.map Z).map (G t)) :
    IdentDistrib (fun ω => (T ω, F (T ω) (Z ω))) (fun ω => (T ω, G (T ω) (Z ω))) μ μ := by
  sorry

/-- Freezing with a fixed law: let $Z$ be independent of $T$ and $F$ jointly measurable. If
$F(t, Z)$ has the same law $\nu$ for every fixed $t$, then $(T, F(T, Z))$ has law
$\mu_T \otimes \nu$: $F(T, Z)$ has law $\nu$ and is independent of $T$ (by
`ProbabilityTheory.indepFun_iff_hasLaw_prodMk_prod`). A Gaussian matrix multiplied by an
independent random orthogonal matrix is the typical use.
Proof: S, about 10 lines. The computation of
`ProbabilityTheory.IndepFun.identDistrib_prodMk_of_forall_map_eq`: by `Measure.map_apply` and
`Measure.prod_apply` the law of the pair at a measurable $E$ is
$\int \nu(E_t)\,d\mu_T(t) = (\mu_T \otimes \nu)(E)$ (`Measure.prod_apply` again). -/
theorem IndepFun.hasLaw_prodMk_prod_of_forall_map_eq [IsFiniteMeasure μ] {T : Ω → α}
    {Z : Ω → γ} (hTZ : IndepFun T Z μ) (hT : AEMeasurable T μ) (hZ : AEMeasurable Z μ)
    {F : α → γ → δ} (hF : Measurable (Function.uncurry F)) {ν : Measure δ}
    (h : ∀ t, (μ.map Z).map (F t) = ν) :
    HasLaw (fun ω => (T ω, F (T ω) (Z ω))) ((μ.map T).prod ν) μ := by
  sorry

end ProbabilityTheory
