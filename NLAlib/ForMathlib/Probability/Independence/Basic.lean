/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Independence.Basic

/-!
# Integrals and events of two independent random variables

If $X$ and $Y$ are independent, their joint law is the product $\mu_X \otimes \mu_Y$
(`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`), so integrals and probabilities of
the pair are iterated ones against the two laws. This file records three consequences.

* The lower integral of a measurable $f \ge 0$ of the pair is the iterated integral against the
  two laws, $\int f(X, Y)\,d\mu = \int\!\int f(x, y)\,d\mu_Y(y)\,d\mu_X(x)$ (Tonelli,
  `MeasureTheory.lintegral_prod`). This is the conditioning step of every expectation of two
  independent random matrices.
* The probability of an event $(X, Y) \in E$ is the average over the law of $Y$ of the
  probabilities of its sections $\{X \in E_y\}$ (Fubini, `MeasureTheory.Measure.prod_apply_symm`);
  it is bounded by a uniform bound $\delta_1$ on the sections over a good set $G$ plus the
  probability $\delta_2$ that $Y$ leaves $G$.
* The Bochner integral of a function of the pair, integrable for the product of the two laws, is
  the iterated integral (Fubini, `MeasureTheory.integral_prod`), the conditioning step of a mean
  or a variance of a function of two independent random matrices.

Mathlib has the ingredients but not these statements. Upstream candidates for
`Mathlib/Probability/Independence/Basic.lean`.

Design: Sketching stage S6 (`docs/design/Sketching-S6.md` §3.1, §8 item 15); LowRank stage S6
(`docs/design/LowRank-S6.md` §4, L1); Hutch++ (`docs/design/Estimation-HutchPP.md` §2.2, P1).

## Main results

* `ProbabilityTheory.IndepFun.lintegral_comp_eq_lintegral_lintegral`: Tonelli for an independent
  pair.
* `ProbabilityTheory.IndepFun.measureReal_mem_le_add`: the sections bound.
* `ProbabilityTheory.IndepFun.integral_comp_eq_integral_integral`: Fubini for an independent pair.
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

-- Stage TE-1

/-- **Iterated integral against an independent pair** (Fubini): for independent, almost
everywhere measurable $U$, $W$ on a finite measure space and $f$ integrable for the product
$\mu_U \otimes \mu_W$ of their laws,
$$\int f(U, W)\,d\mu = \int\!\!\int f(u, w)\,d\mu_W(w)\,d\mu_U(u)\,.$$
The Bochner form of `ProbabilityTheory.IndepFun.lintegral_comp_eq_lintegral_lintegral`; with
it the mean and the mean-square error of Hutch++ are averages over the sketch of those of the
Girard–Hutchinson estimator. Upstream candidate.
[MeyerMuscoMuscoWoodruff2021, proof of Theorem 10]; there as conditioning on the sketch. -/
theorem IndepFun.integral_comp_eq_integral_integral [IsFiniteMeasure μ] {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Ω → α} {W : Ω → β} (hUW : IndepFun U W μ) (hU : AEMeasurable U μ)
    (hW : AEMeasurable W μ) {f : α × β → E} (hf : Integrable f ((μ.map U).prod (μ.map W))) :
    ∫ ω, f (U ω, W ω) ∂μ = ∫ u, ∫ w, f (u, w) ∂(μ.map W) ∂(μ.map U) := by
  sorry

end ProbabilityTheory
