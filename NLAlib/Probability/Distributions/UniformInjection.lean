/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Probability.UniformOn

/-!
# Sampling without replacement: the uniform law on injections

Sampling $\lvert k \rvert$ indices from a finite population $n$ without replacement, in order, is
a uniformly random injection $\iota : k \to n$. Its law is Mathlib's
`uniformOn {f : k → n | Function.Injective f}` on `k → n` with the product measurable space
(discrete, since `k` is finite); no new definition is introduced. This file gives its basic API:
it is a probability measure when $\lvert k \rvert \le \lvert n \rvert$ and the zero measure
otherwise (junk value), each injection has mass $1 / (\lvert n \rvert)_{\lvert k \rvert}$ (the
falling factorial), the law is invariant under relabelling the population and reordering the
sample, and each single draw is uniform on $n$.

Degenerate cases. For empty `k` there is exactly one injection, the empty map, and the law is a
Dirac mass. For $\lvert n \rvert < \lvert k \rvert$ there is none and the law is $0$, so a random
injection with this law lives on the zero measure.

Design: `docs/design/Sketching-S5.md` §3.1, §8.

## Main results

* `NLAlib.isProbabilityMeasure_uniformOn_injective`, `NLAlib.uniformOn_injective_of_card_lt`:
  probability measure, and the junk value.
* `NLAlib.uniformOn_injective_singleton`: the mass of one injection.
* `NLAlib.map_perm_comp_uniformOn_injective`, `NLAlib.map_comp_perm_uniformOn_injective`:
  invariance under permutations of the population and of the sample.
* `NLAlib.map_eval_uniformOn_injective`: one draw without replacement is uniform.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NLAlib

variable {k n : Type*} [Fintype k] [Fintype n] [MeasurableSpace n] [MeasurableSingletonClass n]

/-- The uniform law on injections $k \to n$, sampling $\lvert k \rvert$ indices without
replacement and in order, is a probability measure when $\lvert k \rvert \le \lvert n \rvert$
(then an injection exists). -/
theorem isProbabilityMeasure_uniformOn_injective (hk : Fintype.card k ≤ Fintype.card n) :
    IsProbabilityMeasure (uniformOn {f : k → n | Function.Injective f}) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hk
  exact isProbabilityMeasure_uniformOn (Set.toFinite _) ⟨e, e.injective⟩

omit [MeasurableSingletonClass n] in
/-- Junk value of the uniform law on injections: when $\lvert n \rvert < \lvert k \rvert$ there is
no injection $k \to n$ and the law is the zero measure. -/
theorem uniformOn_injective_of_card_lt (hk : Fintype.card n < Fintype.card k) :
    uniformOn {f : k → n | Function.Injective f} = 0 := by
  have h : {f : k → n | Function.Injective f} = ∅ := Set.eq_empty_of_forall_notMem fun f hf =>
    absurd hk (not_lt.2 (Fintype.card_le_of_injective f hf))
  rw [h, uniformOn_empty_meas]

/-- Under the uniform law on injections, each injection $f : k \to n$ has mass
$1 / (\lvert n \rvert)_{\lvert k \rvert}$, the falling factorial
$\lvert n \rvert (\lvert n \rvert - 1) \cdots (\lvert n \rvert - \lvert k \rvert + 1)$, which is
the number of injections. -/
theorem uniformOn_injective_singleton {f : k → n} (hf : Function.Injective f) :
    uniformOn {g : k → n | Function.Injective g} {f} =
      ((Fintype.card n).descFactorial (Fintype.card k) : ℝ≥0∞)⁻¹ := by
  have hs : MeasurableSet {g : k → n | Function.Injective g} := (Set.toFinite _).measurableSet
  have hc : Measure.count {g : k → n | Function.Injective g} =
      ((Fintype.card n).descFactorial (Fintype.card k) : ℝ≥0∞) := by
    have he : ENat.card {g : k → n | Function.Injective g} = ENat.card (k ↪ n) :=
      ENat.card_congr (Equiv.subtypeInjectiveEquivEmbedding k n)
    rw [Measure.count_apply hs, Set.encard, he, ENat.card_eq_coe_fintype_card,
      Fintype.card_embedding_eq]
    simp
  rw [uniformOn, cond_apply hs, Set.inter_singleton_of_mem hf, Measure.count_singleton,
    mul_one, hc]

omit [Fintype k] [Fintype n] in
/-- Two maps that are both injective or both not have the same mass under the uniform law on
injections. -/
private theorem uniformOn_injective_singleton_eq [Finite k] [Finite n] {f g : k → n}
    (h : Function.Injective f ↔ Function.Injective g) :
    uniformOn {h : k → n | Function.Injective h} {f} =
      uniformOn {h : k → n | Function.Injective h} {g} := by
  have hs : MeasurableSet {h : k → n | Function.Injective h} := (Set.toFinite _).measurableSet
  rw [uniformOn, cond_apply hs, cond_apply hs]
  by_cases hf : Function.Injective f
  · rw [Set.inter_singleton_of_mem hf, Set.inter_singleton_of_mem (h.1 hf),
      Measure.count_singleton, Measure.count_singleton]
  · rw [Set.inter_singleton_eq_empty.2 hf, Set.inter_singleton_eq_empty.2 (mt h.2 hf)]

omit [Fintype k] [Fintype n] in
/-- Invariance under relabelling the population: for a permutation $\sigma$ of $n$, the
uniform law on injections $\iota : k \to n$ is invariant under
$\iota \mapsto \sigma \circ \iota$. -/
theorem map_perm_comp_uniformOn_injective [Finite k] [Finite n] (σ : Equiv.Perm n) :
    (uniformOn {f : k → n | Function.Injective f}).map (fun f => ⇑σ ∘ f) =
      uniformOn {f : k → n | Function.Injective f} := by
  refine Measure.ext_of_singleton fun f => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton f)]
  have hpre : (fun g : k → n => ⇑σ ∘ g) ⁻¹' {f} = {⇑σ.symm ∘ f} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      ext j
      simp
    · rintro rfl
      ext j
      simp
  rw [hpre]
  exact uniformOn_injective_singleton_eq (σ.symm.injective.of_comp_iff f)

omit [Fintype k] [Fintype n] in
/-- Invariance under reordering the sample: for a permutation $\tau$ of $k$, the uniform law
on injections $\iota : k \to n$ is invariant under $\iota \mapsto \iota \circ \tau$. -/
theorem map_comp_perm_uniformOn_injective [Finite k] [Finite n] (τ : Equiv.Perm k) :
    (uniformOn {f : k → n | Function.Injective f}).map (fun f => f ∘ ⇑τ) =
      uniformOn {f : k → n | Function.Injective f} := by
  refine Measure.ext_of_singleton fun f => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton f)]
  have hpre : (fun g : k → n => g ∘ ⇑τ) ⁻¹' {f} = {f ∘ ⇑τ.symm} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      ext j
      simp
    · rintro rfl
      ext j
      simp
  rw [hpre]
  exact uniformOn_injective_singleton_eq
    (Function.Injective.of_comp_iff' f τ.symm.bijective)

/-- One draw without replacement is uniform: for $\lvert k \rvert \le \lvert n \rvert$ and
every position $j$, the law of $\iota(j)$ under the uniform law on injections $\iota : k \to n$ is
the uniform law on $n$. -/
theorem map_eval_uniformOn_injective (hk : Fintype.card k ≤ Fintype.card n) (j : k) :
    (uniformOn {f : k → n | Function.Injective f}).map (fun f => f j) =
      uniformOn (Set.univ : Set n) := by
  classical
  set μ := uniformOn {f : k → n | Function.Injective f} with hμ
  have := isProbabilityMeasure_uniformOn_injective hk
  have hm : Measurable fun f : k → n => f j := measurable_of_countable _
  have hν : IsProbabilityMeasure (μ.map fun f => f j) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  -- every index has the same mass, by invariance under a transposition
  have heq (i i' : n) : μ.map (fun f => f j) {i} = μ.map (fun f => f j) {i'} := by
    have h1 := congrArg (fun ν : Measure (k → n) => ν {f | f j = i'})
      (map_perm_comp_uniformOn_injective (k := k) (Equiv.swap i i'))
    rw [Measure.map_apply (measurable_of_countable _) (Set.toFinite _).measurableSet] at h1
    rw [Measure.map_apply hm (measurableSet_singleton _),
      Measure.map_apply hm (measurableSet_singleton _), hμ]
    refine Eq.trans ?_ h1
    congr 1
    ext f
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, Function.comp_apply,
      Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  refine Measure.ext_of_singleton fun i => ?_
  have hsum : ∑ i' : n, μ.map (fun f => f j) {i'} = 1 := by
    rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
  simp only [heq _ i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [uniformOn_univ, Measure.count_singleton, one_div]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum)

end NLAlib
