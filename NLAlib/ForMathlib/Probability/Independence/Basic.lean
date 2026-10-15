/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic

/-!
# Events of two independent random variables, through their sections

If $X$ and $Y$ are independent, the probability of an event $(X, Y) \in E$ is the average over the
law of $Y$ of the probabilities of its sections $\{X \in E_y\}$ (Fubini on the joint law
$\mu_X \otimes \mu_Y$). This file bounds it by a uniform bound $\delta_1$ on the sections over a
good set $G$ plus the probability $\delta_2$ that $Y$ leaves $G$. Mathlib has the ingredients
(`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`, `MeasureTheory.Measure.prod_apply_symm`)
but not the bound. Upstream candidate for `Mathlib/Probability/Independence/Basic.lean`.

This file is part of the skeleton of Sketching stage S6 (`docs/design/Sketching-S6.md` §3.1,
§8 item 15).

## Main results

* `ProbabilityTheory.IndepFun.measureReal_mem_le_add`: the sections bound.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Sections of an event of two independent variables.** If $X$ and $Y$ are independent, the
section $\{\omega \mid (X(\omega), y) \in E\}$ has probability at most $\delta_1$ for every
$y \in G$, and $Y \notin G$ has probability at most $\delta_2$, then $(X, Y) \in E$ has
probability at most $\delta_1 + \delta_2$. Fubini on the joint law $\mu_X \otimes \mu_Y$. Upstream
candidate. -/
theorem IndepFun.measureReal_mem_le_add [IsProbabilityMeasure μ] {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {X : Ω → α} {Y : Ω → β} (hXY : IndepFun X Y μ)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) {E : Set (α × β)} (hE : MeasurableSet E)
    {G : Set β} (hG : MeasurableSet G) {δ₁ δ₂ : ℝ} (hδ₁ : 0 ≤ δ₁)
    (hsec : ∀ y ∈ G, μ.real {ω | (X ω, y) ∈ E} ≤ δ₁) (hGc : μ.real {ω | Y ω ∉ G} ≤ δ₂) :
    μ.real {ω | (X ω, Y ω) ∈ E} ≤ δ₁ + δ₂ := by
  have hδ₂ : 0 ≤ δ₂ := measureReal_nonneg.trans hGc
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX
  have : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY
  have hslice (y : β) : MeasurableSet ((fun x => (x, y)) ⁻¹' E) :=
    measurable_prodMk_right hE
  have hjoint : μ {ω | (X ω, Y ω) ∈ E} =
      ∫⁻ y, μ {ω | (X ω, y) ∈ E} ∂(μ.map Y) := by
    have h1 : μ {ω | (X ω, Y ω) ∈ E} = (μ.map fun ω => (X ω, Y ω)) E := by
      rw [Measure.map_apply_of_aemeasurable (hX.prodMk hY) hE]
      rfl
    rw [h1, (indepFun_iff_map_prod_eq_prod_map_map hX hY).1 hXY, Measure.prod_apply_symm hE]
    exact lintegral_congr fun y => Measure.map_apply_of_aemeasurable hX (hslice y)
  have hG' : (μ.map Y) Gᶜ = μ {ω | Y ω ∉ G} := by
    rw [Measure.map_apply_of_aemeasurable hY hG.compl]
    rfl
  have hle : μ {ω | (X ω, Y ω) ∈ E} ≤ ENNReal.ofReal δ₁ + ENNReal.ofReal δ₂ := by
    rw [hjoint, ← lintegral_add_compl _ hG]
    gcongr
    · calc ∫⁻ y in G, μ {ω | (X ω, y) ∈ E} ∂(μ.map Y) ≤ ∫⁻ _ in G, ENNReal.ofReal δ₁ ∂(μ.map Y) :=
            setLIntegral_mono' hG fun y hy => by
              rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
              exact ENNReal.ofReal_le_ofReal (hsec y hy)
        _ ≤ ENNReal.ofReal δ₁ := by
            rw [setLIntegral_const]
            exact mul_le_of_le_one_right' prob_le_one
    · calc ∫⁻ y in Gᶜ, μ {ω | (X ω, y) ∈ E} ∂(μ.map Y) ≤ ∫⁻ _ in Gᶜ, 1 ∂(μ.map Y) :=
            setLIntegral_mono' hG.compl fun _ _ => prob_le_one
        _ = μ {ω | Y ω ∉ G} := by rw [setLIntegral_const, one_mul, hG']
        _ ≤ ENNReal.ofReal δ₂ := by
            rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
            exact ENNReal.ofReal_le_ofReal hGc
  rw [← ENNReal.ofReal_add hδ₁ hδ₂] at hle
  exact ENNReal.toReal_le_of_le_ofReal (add_nonneg hδ₁ hδ₂) hle

end ProbabilityTheory
