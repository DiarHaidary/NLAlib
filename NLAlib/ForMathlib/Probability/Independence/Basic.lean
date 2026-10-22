/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Logic.Function.DependsOn

/-!
# Integrals and events of two independent random variables

If $X$ and $Y$ are independent, their joint law is the product $\mu_X \otimes \mu_Y$
(`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`), so integrals and probabilities of
the pair are iterated ones against the two laws. This file records four consequences, and one
fact about independent families.

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
* When one factor $W$ has a named law $\nu$, it is integrated out against $\nu$:
  $\int f(U, W)\,d\mu = \int\!\int f(U(\omega), w)\,d\nu(w)\,d\mu(\omega)$, and a bound $H$ on
  the inner integral gives integrability and $\int f(U, W)\,d\mu \le \int H\,d\mu$.
* A measurable function of the coordinates in a finite set $s$ of an independent family is
  independent of every coordinate outside $s$: the step that conditions an iterated random
  method on its past.

Mathlib has the ingredients but not these statements. Upstream candidates for
`Mathlib/Probability/Independence/Basic.lean`.

Design: Sketching stage S6 (`docs/design/Sketching-S6.md` §3.1, §8 item 15); LowRank stage S6
(`docs/design/LowRank-S6.md` §4, L1); Hutch++ (`docs/design/Estimation-HutchPP.md` §2.2, P1);
randomized Kaczmarz (`docs/design/Regression-Kaczmarz.md` §4).

## Main results

* `ProbabilityTheory.IndepFun.lintegral_comp_eq_lintegral_lintegral`: Tonelli for an independent
  pair.
* `ProbabilityTheory.IndepFun.measureReal_mem_le_add`: the sections bound.
* `ProbabilityTheory.IndepFun.integral_comp_eq_integral_integral`: Fubini for an independent pair.
* `ProbabilityTheory.IndepFun.lintegral_comp_eq_lintegral_lintegral_of_hasLaw`,
  `ProbabilityTheory.IndepFun.lintegral_ofReal_comp_eq_lintegral_ofReal_integral`: integrating
  out an independent factor of known law.
* `ProbabilityTheory.IndepFun.integrable_comp_of_integral_le`,
  `ProbabilityTheory.IndepFun.integral_comp_le_of_integral_le`: integrability and a bound from a
  bound on the inner integral.
* `ProbabilityTheory.IndepFun.integrable_comp_iff`: integrability against $\mu$ is integrability
  against the product of the two laws.
* `ProbabilityTheory.iIndepFun.indepFun_comp_of_dependsOn`: a function of some coordinates of an
  independent family is independent of another coordinate.
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
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hU hW).1 hUW
  rw [← integral_prod _ hf, ← hmap,
    integral_map (hU.prodMk hW) (hmap ▸ hf.aestronglyMeasurable)]

/-- Integrating out an independent factor, in $[0, \infty]$: if $W$ has law $\nu$ and is
independent of $U$, and $f \ge 0$ is measurable, then
$$\int^- f(U, W)\,d\mu = \int^- \int^- f(U(\omega), w)\,d\nu(w)\,d\mu(\omega)\,.$$
The conditioning step of a two-sketch proof, with the inner integral against the named law.
Upstream candidate. -/
theorem IndepFun.lintegral_comp_eq_lintegral_lintegral_of_hasLaw [IsFiniteMeasure μ]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {U : Ω → α} {W : Ω → β}
    {ν : Measure β} (hUW : IndepFun U W μ) (hU : AEMeasurable U μ) (hW : HasLaw W ν μ)
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (U ω, W ω) ∂μ = ∫⁻ ω, ∫⁻ w, f (U ω, w) ∂ν ∂μ := by
  rw [hUW.lintegral_comp_eq_lintegral_lintegral hU hW.aemeasurable hf]
  obtain ⟨-, rfl⟩ := hW
  exact lintegral_map' hf.lintegral_prod_right'.aemeasurable hU

/-- Integrating out an independent factor, real form: if $W$ has law $\nu$ and is
independent of $U$, and $F \ge 0$ is measurable with $F(U(\omega), \cdot)$ integrable against
$\nu$ for almost every $\omega$, then
$$\int^- F(U, W)\,d\mu = \int^- \Bigl(\int F(U(\omega), w)\,d\nu(w)\Bigr)\,d\mu(\omega)\,.$$
The real form of `ProbabilityTheory.IndepFun.lintegral_comp_eq_lintegral_lintegral_of_hasLaw`.
Upstream candidate. -/
theorem IndepFun.lintegral_ofReal_comp_eq_lintegral_ofReal_integral [IsFiniteMeasure μ]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {U : Ω → α} {W : Ω → β}
    {ν : Measure β} (hUW : IndepFun U W μ) (hU : AEMeasurable U μ) (hW : HasLaw W ν μ)
    {F : α × β → ℝ} (hF : Measurable F) (hF0 : ∀ q, 0 ≤ F q)
    (hint : ∀ᵐ ω ∂μ, Integrable (fun w => F (U ω, w)) ν) :
    ∫⁻ ω, ENNReal.ofReal (F (U ω, W ω)) ∂μ = ∫⁻ ω, ENNReal.ofReal (∫ w, F (U ω, w) ∂ν) ∂μ := by
  rw [hUW.lintegral_comp_eq_lintegral_lintegral_of_hasLaw hU hW
    (f := fun q => ENNReal.ofReal (F q)) (ENNReal.measurable_ofReal.comp hF)]
  refine lintegral_congr_ae ?_
  filter_upwards [hint] with ω hω
  exact (ofReal_integral_eq_lintegral_ofReal hω (ae_of_all _ fun w => hF0 _)).symm

/-- Integrability from a bound on the inner integral: if $W$ has law $\nu$ and is independent
of $U$, $F \ge 0$ is measurable, $F(U(\omega), \cdot)$ is integrable against $\nu$ and
$\int F(U(\omega), w)\,d\nu(w) \le H(\omega)$ for almost every $\omega$, with $H$ integrable,
then $F(U, W)$ is integrable. Upstream candidate. -/
theorem IndepFun.integrable_comp_of_integral_le [IsFiniteMeasure μ] {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {U : Ω → α} {W : Ω → β} {ν : Measure β}
    (hUW : IndepFun U W μ) (hU : AEMeasurable U μ) (hW : HasLaw W ν μ) {F : α × β → ℝ}
    (hF : Measurable F) (hF0 : ∀ q, 0 ≤ F q) {H : Ω → ℝ}
    (hint : ∀ᵐ ω ∂μ, Integrable (fun w => F (U ω, w)) ν)
    (hle : ∀ᵐ ω ∂μ, ∫ w, F (U ω, w) ∂ν ≤ H ω) (hH : Integrable H μ) :
    Integrable (fun ω => F (U ω, W ω)) μ := by
  refine ⟨(hF.comp_aemeasurable (hU.prodMk hW.aemeasurable)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => hF0 _),
    hUW.lintegral_ofReal_comp_eq_lintegral_ofReal_integral hU hW hF hF0 hint]
  exact (lintegral_mono_ae (hle.mono fun ω h => ENNReal.ofReal_le_ofReal h)).trans_lt
    hH.lintegral_lt_top

/-- Integrating out an independent factor under a bound: if $W$ has law $\nu$ and is
independent of $U$, $F \ge 0$ is measurable, $F(U(\omega), \cdot)$ is integrable against $\nu$
and $\int F(U(\omega), w)\,d\nu(w) \le H(\omega)$ for almost every $\omega$, with $H$
integrable, then
$$\int F(U, W)\,d\mu \le \int H\,d\mu\,.$$
Upstream candidate. -/
theorem IndepFun.integral_comp_le_of_integral_le [IsFiniteMeasure μ] {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {U : Ω → α} {W : Ω → β} {ν : Measure β}
    (hUW : IndepFun U W μ) (hU : AEMeasurable U μ) (hW : HasLaw W ν μ) {F : α × β → ℝ}
    (hF : Measurable F) (hF0 : ∀ q, 0 ≤ F q) {H : Ω → ℝ}
    (hint : ∀ᵐ ω ∂μ, Integrable (fun w => F (U ω, w)) ν)
    (hle : ∀ᵐ ω ∂μ, ∫ w, F (U ω, w) ∂ν ≤ H ω) (hH : Integrable H μ) :
    ∫ ω, F (U ω, W ω) ∂μ ≤ ∫ ω, H ω ∂μ := by
  have hFi := hUW.integrable_comp_of_integral_le hU hW hF hF0 hint hle hH
  have hH0 : 0 ≤ᵐ[μ] H := by
    filter_upwards [hle] with ω h
    exact (integral_nonneg fun w => hF0 _).trans h
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => hF0 _) hFi.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hH0 hH.aestronglyMeasurable,
    hUW.lintegral_ofReal_comp_eq_lintegral_ofReal_integral hU hW hF hF0 hint]
  exact ENNReal.toReal_mono hH.lintegral_lt_top.ne
    (lintegral_mono_ae (hle.mono fun ω h => ENNReal.ofReal_le_ofReal h))

/-- Integrability of a function of an independent pair: for independent, almost everywhere
measurable $U$, $W$ on a finite measure space and $f$ almost everywhere strongly measurable for
the product $\mu_U \otimes \mu_W$ of their laws, $f(U, W)$ is integrable against $\mu$ if and
only if $f$ is integrable against $\mu_U \otimes \mu_W$. The integrability side condition of
`ProbabilityTheory.IndepFun.integral_comp_eq_integral_integral`. Upstream candidate. -/
theorem IndepFun.integrable_comp_iff [IsFiniteMeasure μ] {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [NormedAddCommGroup E] {U : Ω → α} {W : Ω → β}
    (hUW : IndepFun U W μ) (hU : AEMeasurable U μ) (hW : AEMeasurable W μ) {f : α × β → E}
    (hf : AEStronglyMeasurable f ((μ.map U).prod (μ.map W))) :
    Integrable (fun ω => f (U ω, W ω)) μ ↔ Integrable f ((μ.map U).prod (μ.map W)) := by
  rw [← (indepFun_iff_map_prod_eq_prod_map_map hU hW).1 hUW] at hf ⊢
  exact (integrable_map_measure hf (hU.prodMk hW)).symm

/-- **A function of some coordinates is independent of another coordinate**: for an independent
family $(X_i)_i$ of almost everywhere measurable random variables, a measurable $F$ of the whole
family that depends only on the coordinates in a finite set $s$, and an index $t \notin s$, the
random variables $F((X_i)_i)$ and $X_t$ are independent. With $s = \{0, \dots, q - 1\}$ and
$t = q$ it is the independence of the $q$-th sample of an i.i.d. sequence from everything computed
from the earlier ones. Upstream candidate. -/
theorem iIndepFun.indepFun_comp_of_dependsOn {ι γ : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] [MeasurableSpace γ] {X : (i : ι) → Ω → β i}
    (hX : iIndepFun X μ) (hXm : ∀ i, AEMeasurable (X i) μ) {s : Finset ι} {t : ι} (ht : t ∉ s)
    {F : ((i : ι) → β i) → γ} (hF : Measurable F) (hFs : DependsOn F s) :
    IndepFun (fun ω => F fun i => X i ω) (X t) μ := by
  classical
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω₀⟩⟩
  · rw [Measure.eq_zero_of_isEmpty μ]
    simp [IndepFun]
  have hst : Disjoint s {t} := Finset.disjoint_singleton_right.mpr ht
  have h := hX.indepFun_finset₀ s {t} hst hXm
  let G : ((i : s) → β i) → γ :=
    fun y => F fun i => if hi : i ∈ s then y ⟨i, hi⟩ else X i ω₀
  have hG : Measurable G := by
    refine hF.comp (measurable_pi_iff.mpr fun i => ?_)
    by_cases hi : i ∈ s
    · simp only [hi, dif_pos]
      exact measurable_pi_apply _
    · simp only [hi, dif_neg, not_false_eq_true]
      exact measurable_const
  have hFG : (fun ω => F fun i => X i ω) = G ∘ fun ω (i : s) => X i ω := by
    funext ω
    refine hFs fun i hi => ?_
    simp [Finset.mem_coe.mp hi]
  rw [hFG]
  exact h.comp hG (measurable_pi_apply ⟨t, Finset.mem_singleton_self t⟩)

end ProbabilityTheory
