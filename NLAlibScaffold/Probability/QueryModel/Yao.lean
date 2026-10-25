/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Independence.Basic
public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlibScaffold.Probability.QueryModel.Basic

/-!
# Yao's principle for query algorithms

A randomized algorithm is a measurable family of deterministic ones indexed by a seed
(`NLAlib.QueryAlgorithm.IsMeasurableFamily`). Two forms of Yao's minimax principle (the easy
direction, which is what lower bounds use), both Fubini on the product of the seed law and the
input law (`docs/design/Probability-MatvecQueryModel.md`, §3.2):

* distributional: if every measurable deterministic algorithm has failure probability at most
  $\delta$ on a random input, so does every randomized one whose seed is independent of the input;
* worst case: if every measurable deterministic algorithm fails with probability at least
  $\delta$ under an input law, every randomized algorithm fails with probability at least
  $\delta$ on some input.

Failure (or success) is membership of the pair (input, output) in a measurable set `B`.

## Main results

* `NLAlib.QueryAlgorithm.IsMeasurableFamily.measureReal_run_mem_le_of_indepFun`.
* `NLAlib.QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

namespace QueryAlgorithm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {Q R β S M : Type*} {q : ℕ}
  [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace β] [MeasurableSpace S]
  [MeasurableSpace M]

/-- **Yao's principle, distributional form**: let the seed $s$ be independent of the random input
$X$, and let $B$ be a measurable set of (input, output) pairs. If every measurable deterministic
algorithm puts $(X, \text{output})$ in $B$ with probability at most $\delta$, then so does the
randomized algorithm with seed $s$:
$\mathbb{P}[(X, \mathcal{A}_s(X)) \in B] \le \delta$.
[Yao1977, Section 3]; there as the minimax principle for finite problems, here the averaging
half on a probability space, any seed and input spaces, any oracle depending measurably on the
input.
Proof: M, about 25 lines. The law of $(s, X)$ is the product of the two laws
(`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`). The event is
$\{(s, x) \mid (x, (\mathcal{A}_s).\mathrm{run}(O_x)) \in B\}$, measurable by
`QueryAlgorithm.IsMeasurableFamily.measurable_run`. Fubini (`Measure.prod_apply`) writes its
probability as the integral over the seed law of the probability of the section at $s$, which
is the failure probability of the deterministic algorithm `alg s` under the law of $X$, at most
$\delta$ by `h` (with `QueryAlgorithm.IsMeasurableFamily.isMeasurable` and `Measure.map_apply`).
`IndepFun.measureReal_mem_le_add` (with $\delta_2 = 0$, `G = univ`) does exactly this step. -/
theorem IsMeasurableFamily.measureReal_run_mem_le_of_indepFun [IsProbabilityMeasure μ]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {O : M → Q → R}
    (hO : Measurable (Function.uncurry O)) {s : Ω → S} {X : Ω → M} (hs : AEMeasurable s μ)
    (hX : AEMeasurable X μ) (hsX : IndepFun s X μ) {B : Set (M × β)} (hB : MeasurableSet B)
    {δ : ℝ}
    (h : ∀ a : QueryAlgorithm Q R q β, a.IsMeasurable →
      μ.real {ω | (X ω, a.run (O (X ω))) ∈ B} ≤ δ) :
    μ.real {ω | (X ω, (alg (s ω)).run (O (X ω))) ∈ B} ≤ δ := by
  have hmeas : Measurable fun p : M × S => (p.1, (alg p.2).run (O p.1)) :=
    measurable_fst.prodMk ((halg.measurable_run hO).comp measurable_swap)
  have hE : MeasurableSet {p : M × S | (p.1, (alg p.2).run (O p.1)) ∈ B} :=
    hmeas hB
  have hsec : ∀ y ∈ (Set.univ : Set S), μ.real {ω | (X ω, y) ∈
      {p : M × S | (p.1, (alg p.2).run (O p.1)) ∈ B}} ≤ δ := fun y _ =>
    h (alg y) (halg.isMeasurable y)
  have hGc : μ.real {ω | s ω ∉ (Set.univ : Set S)} ≤ 0 := by
    simp
  have hδ : 0 ≤ δ := by
    obtain ⟨ω⟩ : (Set.univ : Set Ω).Nonempty :=
      nonempty_of_measure_ne_zero (μ := μ) (by simp)
    exact measureReal_nonneg.trans (h (alg (s ω)) (halg.isMeasurable _))
  have key := hsX.symm.measureReal_mem_le_add hX hs hE MeasurableSet.univ (δ₁ := δ) (δ₂ := 0)
    hδ hsec hGc
  simpa using key

/-- **Yao's principle, worst-case form**: let $\rho$ be a seed law and $\nu$ an input law, both
probability measures, and $B$ a measurable set of (input, output) pairs. If every measurable
deterministic algorithm has $\nu$-probability at least $\delta$ of $(x, \text{output}) \in B$,
then for the randomized algorithm some input $x$ has
$\rho$-probability at least $\delta$ of $(x, \mathcal{A}_s(x)) \in B$. Read with $B$ the failure
set: a lower bound against one input distribution is a lower bound for randomized algorithms in
the worst case.
[Yao1977, Section 3]; [ZhangEtAl2026, Section 8]; there for finite or implicit input spaces.
Proof: M, about 25 lines. By Tonelli on `ρ.prod ν` (`Measure.prod_apply`,
`Measure.prod_apply_symm`, the event measurable by
`QueryAlgorithm.IsMeasurableFamily.measurable_run`),
$\int \rho(B^x)\,d\nu(x) = \int \nu(B_s)\,d\rho(s) \ge \delta$; if every $\rho(B^x) < \delta$ the
left side is $< \delta$ (`MeasureTheory.lintegral_mono`, `ν` a probability measure; work in
`ℝ≥0∞` with `ENNReal.ofReal δ` and convert with `measureReal_def` at the end; the case
$\delta \le 0$ is immediate from `measureReal_nonneg` and `Nonempty M`, which `ν` gives). -/
theorem IsMeasurableFamily.exists_le_measureReal_run_mem {alg : S → QueryAlgorithm Q R q β}
    (halg : IsMeasurableFamily alg) {O : M → Q → R} (hO : Measurable (Function.uncurry O))
    (ρ : Measure S) [IsProbabilityMeasure ρ] (ν : Measure M) [IsProbabilityMeasure ν]
    {B : Set (M × β)} (hB : MeasurableSet B) {δ : ℝ}
    (h : ∀ a : QueryAlgorithm Q R q β, a.IsMeasurable → δ ≤ ν.real {x | (x, a.run (O x)) ∈ B}) :
    ∃ x, δ ≤ ρ.real {s | (x, (alg s).run (O x)) ∈ B} := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  set E : Set (S × M) := {p | (p.2, (alg p.1).run (O p.2)) ∈ B} with hEdef
  have hE : MeasurableSet E :=
    hB.preimage (measurable_snd.prodMk (halg.measurable_run hO))
  have hlow : ∀ s, ENNReal.ofReal δ ≤ ν (Prod.mk s ⁻¹' E) := fun s => by
    have := h (alg s) (halg.isMeasurable s)
    rw [measureReal_def] at this
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 this
  have hup : ∀ x, ρ ((fun s => (s, x)) ⁻¹' E) < ENNReal.ofReal δ := fun x => by
    have := hcon x
    rw [measureReal_def] at this
    exact (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).2 this
  have h1 : ENNReal.ofReal δ ≤ (ρ.prod ν) E := by
    rw [Measure.prod_apply hE]
    calc ENNReal.ofReal δ = ∫⁻ _ : S, ENNReal.ofReal δ ∂ρ := by simp
      _ ≤ _ := lintegral_mono hlow
  have h2 : (ρ.prod ν) E < ENNReal.ofReal δ := by
    rw [Measure.prod_apply_symm hE]
    calc _ < ∫⁻ _ : M, ENNReal.ofReal δ ∂ν := by
          refine lintegral_strict_mono (IsProbabilityMeasure.ne_zero ν) aemeasurable_const ?_
            (ae_of_all _ hup)
          refine ne_top_of_le_ne_top (b := ∫⁻ _ : M, ENNReal.ofReal δ ∂ν) (by simp)
            (lintegral_mono fun x => (hup x).le)
      _ = ENNReal.ofReal δ := by simp
  exact absurd h1 (not_le.2 h2)

end QueryAlgorithm

end NLAlib
