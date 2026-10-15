/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.UniformOn
public import NLAlib.ForMathlib.Data.NNReal.Basic

/-!
# Sampling an index from a finite probability vector

`NLAlib.samplingMeasure p` is the law of a random index $i$ drawn with probability $p_i$, for
weights $p_i \ge 0$ (`p : ι → ℝ≥0`) on a finite type. The definition takes any weights, so
statements carry no proof term; it is a probability measure when $\sum_i p_i = 1$. Uniform
sampling is the case $p_i = 1 / \lvert \iota \rvert$, which is Mathlib's `uniformOn Set.univ`, and
the bridge to `PMF` is `NLAlib.samplingMeasure_toNNReal_eq_toMeasure`.

## Main definitions

* `NLAlib.samplingMeasure p`: $\sum_i p_i \delta_i$.

## Main results

* `NLAlib.isProbabilityMeasure_samplingMeasure`.
* `NLAlib.integral_samplingMeasure`: $\int f = \sum_i p_i f(i)$.
* `NLAlib.measureReal_eq_of_hasLaw_samplingMeasure`: $\mathbb{P}(X = i) = p_i$.
* `NLAlib.measureReal_pi_samplingMeasure_setOf_apply_eq_apply`: two coordinates of an i.i.d.
  sample collide with probability $\sum_r p_r^2$.
* `NLAlib.samplingMeasure_const_inv_card`: uniform weights give Mathlib's uniform measure; they
  sum to one by `NNReal.sum_const_inv_card`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (p : ι → ℝ≥0)

/-- The law of a random index that equals $i$ with probability $p_i$, the measure
$\sum_i p_i \delta_i$. It is a probability measure when $\sum_i p_i = 1$
(`isProbabilityMeasure_samplingMeasure`); the definition takes any weights so that statements
carry no proof term. -/
noncomputable def samplingMeasure : Measure ι :=
  ∑ i, (p i : ℝ≥0∞) • Measure.dirac i

/-- The sampling law is a finite measure, for any weights $p_i$. -/
instance isFiniteMeasure_samplingMeasure : IsFiniteMeasure (samplingMeasure p) := by
  constructor
  simp only [samplingMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.coe_lt_top

omit [MeasurableSingletonClass ι] in
/-- With weights summing to one, `samplingMeasure p` is a probability measure. -/
theorem isProbabilityMeasure_samplingMeasure (hp : ∑ i, p i = 1) :
    IsProbabilityMeasure (samplingMeasure p) := by
  constructor
  simp only [samplingMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact_mod_cast hp

/-- The probability of a set of indices is the sum of their weights: the measure of a finite set
$s$ is $\sum_{i \in s} p_i$. -/
theorem samplingMeasure_real_apply (s : Finset ι) :
    (samplingMeasure p).real (s : Set ι) = ∑ i ∈ s, (p i : ℝ) := by
  classical
  simp only [measureReal_def, samplingMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, Measure.dirac_apply, smul_eq_mul, Set.indicator_apply, Finset.mem_coe,
    Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ENNReal.toReal_sum fun i _ => ENNReal.coe_ne_top]
  rfl

/-- Every function is integrable for `samplingMeasure p`. -/
theorem integrable_samplingMeasure {E : Type*} [NormedAddCommGroup E] (f : ι → E) :
    Integrable f (samplingMeasure p) := by
  exact integrable_finsetSum_measure.2 fun i _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.coe_ne_top

/-- The integral against `samplingMeasure p` is the weighted sum:
$\int f = \sum_i p_i f(i)$, for $f$ with values in any real Banach space. -/
theorem integral_samplingMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ι → E) :
    ∫ i, f i ∂samplingMeasure p = ∑ i, (p i : ℝ) • f i := by
  rw [samplingMeasure, integral_finsetSum_measure fun i _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.coe_ne_top]
  simp only [integral_smul_measure, integral_dirac, ENNReal.coe_toReal]

/-- A random index with law `samplingMeasure p` equals $i$ with probability $p_i$. -/
theorem measureReal_eq_of_hasLaw_samplingMeasure {X : Ω → ι}
    (hX : HasLaw X (samplingMeasure p) μ) (i : ι) : μ.real {ω | X ω = i} = p i := by
  have h := Measure.map_apply_of_aemeasurable hX.aemeasurable (measurableSet_singleton i)
  rw [hX.map_eq] at h
  have hs := samplingMeasure_real_apply p {i}
  rw [Finset.coe_singleton, Finset.sum_singleton] at hs
  rw [← hs, measureReal_def, measureReal_def, h]
  rfl

/-- The mass of a single index is its weight: the measure of $\{i\}$ is $p_i$. -/
theorem samplingMeasure_singleton (i : ι) : samplingMeasure p {i} = p i := by
  classical
  simp only [samplingMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, smul_eq_mul, Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Collision probability.** Two distinct coordinates of an i.i.d. sample from
`NLAlib.samplingMeasure p`, with weights summing to $1$, agree with probability $\sum_r p_r^2$;
at uniform weights $1/\lvert \iota \rvert$ this is $1/\lvert \iota \rvert$. The hash-collision
step of CountSketch (`NLAlib.Sketching.Sparse.CountSketch`). -/
theorem measureReal_pi_samplingMeasure_setOf_apply_eq_apply {κ : Type*} [Fintype κ]
    (hp : ∑ i, p i = 1) {i j : κ} (hij : i ≠ j) :
    (Measure.pi fun _ : κ => samplingMeasure p).real {f | f i = f j} = ∑ r, (p r : ℝ) ^ 2 := by
  have := isProbabilityMeasure_samplingMeasure p hp
  set P := Measure.pi fun _ : κ => samplingMeasure p
  have hind : IndepFun (fun f : κ → ι => f i) (fun f => f j) P :=
    (iIndepFun_pi (μ := fun _ : κ => samplingMeasure p) (X := fun _ (x : ι) => x)
      fun _ => aemeasurable_id).indepFun hij
  have hev (l : κ) (r : ι) : P ((fun f : κ → ι => f l) ⁻¹' {r}) = p r := by
    rw [(measurePreserving_eval (fun _ : κ => samplingMeasure p) l).measure_preimage
      (measurableSet_singleton r).nullMeasurableSet, samplingMeasure_singleton]
  have hU : {f : κ → ι | f i = f j} =
      ⋃ r ∈ (Finset.univ : Finset ι),
        (fun f : κ → ι => f i) ⁻¹' {r} ∩ (fun f : κ → ι => f j) ⁻¹' {r} := by
    ext f
    simp only [Set.mem_ofPred_eq, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨f j, h, rfl⟩, fun ⟨_, h1, h2⟩ => h1.trans h2.symm⟩
  have hmeas (r : ι) : MeasurableSet
      ((fun f : κ → ι => f i) ⁻¹' {r} ∩ (fun f : κ → ι => f j) ⁻¹' {r}) :=
    ((measurable_pi_apply i) (measurableSet_singleton r)).inter
      ((measurable_pi_apply j) (measurableSet_singleton r))
  rw [measureReal_def, hU, measure_biUnion_finset (fun r _ s _ hrs => ?_) fun r _ => hmeas r]
  · rw [ENNReal.toReal_sum fun r _ => measure_ne_top _ _]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hind.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton r)
      (measurableSet_singleton r), hev, hev, ENNReal.toReal_mul, ENNReal.coe_toReal, sq]
  · exact Set.disjoint_left.2 fun f hf hf' => hrs (hf.1.symm.trans hf'.1)

/-- The bridge to `PMF`. -/
theorem samplingMeasure_toNNReal_eq_toMeasure (q : PMF ι) :
    samplingMeasure (fun i => (q i).toNNReal) = q.toMeasure := by
  refine Measure.ext_of_singleton fun a => ?_
  rw [samplingMeasure_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
    ENNReal.coe_toNNReal (q.apply_ne_top a)]

/-- Uniform weights give Mathlib's uniform measure. -/
theorem samplingMeasure_const_inv_card :
    samplingMeasure (fun _ : ι => (Fintype.card ι : ℝ≥0)⁻¹) = uniformOn Set.univ := by
  refine Measure.ext_of_singleton fun a => ?_
  have : (Fintype.card ι : ℝ≥0) ≠ 0 := by
    have : Nonempty ι := ⟨a⟩
    exact_mod_cast Fintype.card_ne_zero
  rw [samplingMeasure_singleton, uniformOn_univ, Measure.count_singleton, ENNReal.coe_inv this,
    one_div, ENNReal.coe_natCast]

/-! ### Deprecated aliases -/

@[deprecated NNReal.sum_const_inv_card (since := "2026-10-15")]
alias sum_const_inv_card := NNReal.sum_const_inv_card

end NLAlib
