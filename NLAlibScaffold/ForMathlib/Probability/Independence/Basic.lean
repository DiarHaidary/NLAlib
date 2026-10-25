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

/-- Auxiliary: pushing a product measure forward along `(t, z) ↦ (t, H t z)` depends only on the
laws `σ.map (H t)`. -/
private lemma map_prod_prodMk_eq_of_forall_map_eq (ρ : Measure α) [SFinite ρ] (σ : Measure γ)
    [SFinite σ] {F G : α → γ → δ} (hF : Measurable (Function.uncurry F))
    (hG : Measurable (Function.uncurry G)) (h : ∀ t, σ.map (F t) = σ.map (G t)) :
    (ρ.prod σ).map (fun p : α × γ => (p.1, F p.1 p.2)) =
      (ρ.prod σ).map (fun p : α × γ => (p.1, G p.1 p.2)) := by
  have hF' : Measurable (fun p : α × γ => (p.1, F p.1 p.2)) := measurable_fst.prodMk hF
  have hG' : Measurable (fun p : α × γ => (p.1, G p.1 p.2)) := measurable_fst.prodMk hG
  ext E hE
  rw [Measure.map_apply hF' hE, Measure.map_apply hG' hE, Measure.prod_apply (hF' hE),
    Measure.prod_apply (hG' hE)]
  refine lintegral_congr fun t => ?_
  have key : ∀ (H : α → γ → δ), Measurable (Function.uncurry H) →
      σ (Prod.mk t ⁻¹' ((fun p : α × γ => (p.1, H p.1 p.2)) ⁻¹' E)) =
        (σ.map (H t)) (Prod.mk t ⁻¹' E) := by
    intro H hH
    rw [Measure.map_apply hH.of_uncurry_left (measurable_prodMk_left hE)]
    rfl
  rw [key F hF, key G hG, h t]

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
  have hpair := (indepFun_iff_map_prod_eq_prod_map_map hT hZ).1 hTZ
  have hp := hT.prodMk hZ
  have hF' : Measurable (fun p : α × γ => (p.1, F p.1 p.2)) := measurable_fst.prodMk hF
  have hG' : Measurable (fun p : α × γ => (p.1, G p.1 p.2)) := measurable_fst.prodMk hG
  refine ⟨hF'.comp_aemeasurable hp, hG'.comp_aemeasurable hp, ?_⟩
  change μ.map ((fun p : α × γ => (p.1, F p.1 p.2)) ∘ (fun ω => (T ω, Z ω))) =
    μ.map ((fun p : α × γ => (p.1, G p.1 p.2)) ∘ (fun ω => (T ω, Z ω)))
  rw [← AEMeasurable.map_map_of_aemeasurable hF'.aemeasurable hp,
    ← AEMeasurable.map_map_of_aemeasurable hG'.aemeasurable hp, hpair]
  exact map_prod_prodMk_eq_of_forall_map_eq _ _ hF hG h

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
  have hp := (measurable_fst.prodMk hF).comp_aemeasurable (hT.prodMk hZ)
  rcases isEmpty_or_nonempty α with hα | ⟨⟨t₀⟩⟩
  · exact ⟨hp, (Measure.eq_zero_of_isEmpty _).trans (Measure.eq_zero_of_isEmpty _).symm⟩
  -- Freeze `T` at `t₀`: `(T, F T Z)` has the law of `(T, F t₀ Z)`, an independent pair.
  have hF₀ : Measurable (F t₀) := hF.comp measurable_prodMk_left
  have h₀ := hTZ.identDistrib_prodMk_of_forall_map_eq hT hZ hF (G := fun _ => F t₀)
    (hF₀.comp measurable_snd) fun t => (h t).trans (h t₀).symm
  refine ⟨hp, h₀.map_eq.trans ?_⟩
  rw [← h t₀, AEMeasurable.map_map_of_aemeasurable hF₀.aemeasurable hZ]
  exact (indepFun_iff_map_prod_eq_prod_map_map hT (hF₀.comp_aemeasurable hZ)).1
    (hTZ.comp measurable_id hF₀)

end ProbabilityTheory
