/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# A union bound for adaptively chosen events with fresh samples (scaffold)

Statement for a new file `NLAlib/Probability/AdaptiveUnionBound.lean` (stage HDIAG, wave W4,
design note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.7). A randomized recursion
draws a fresh sample $\zeta_i$ at each node $i$ of a countable index set; the state $X_i$ of the
node (its input, or "not reached") is computed from earlier samples, takes countably many values
and is independent of $\zeta_i$. If for every state $y$ the bad set $S_i(y)$ of the node has
probability at most the mean of a charge $q_i(y, \cdot)$, and the charges along every run sum to
at most $\theta$, then some node fails with probability at most $\theta$. It is the bookkeeping of
[Shah2024, proof of Theorem 4.2] ("we apply union bound"), with the charge carrying the expected
number of nodes and of splits.

## Main results

* `NLAlib.measureReal_exists_mem_le_of_forall_measure_le_lintegral`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NLAlib

/-- **Union bound over adaptively chosen events with fresh samples**: let $\zeta_i$ ($i$ in a
countable set) be random samples of law $\nu$, and $X_i$ random states with countably many
values, each event $\{X_i = y\}$ measurable and independent of $\zeta_i$. Let $S_i(y)$ be
sets (not necessarily measurable) and $q_i(y, \cdot) \ge 0$ measurable charges with
$\nu(S_i(y)) \le \int q_i(y, z)\,d\nu(z)$ for every $y$, and suppose
$\sum_i q_i(X_i, \zeta_i) \le \theta$ surely. Then
$$\mathbb{P}[\exists i,\ \zeta_i \in S_i(X_i)] \le \theta \,.$$
No printed source; [Shah2024, proof of Theorem 4.2] applies the union bound informally.
Proof: replace $S_i(y)$ by `MeasureTheory.toMeasurable` $\nu$ $S_i(y)$, measurable with the same
measure (`MeasureTheory.measure_toMeasurable`, `MeasureTheory.subset_toMeasurable`); then
$\mathbb{P}[\exists i, \cdot] \le \sum_i \mathbb{P}[\zeta_i \in S_i(X_i)]$
(`MeasureTheory.measure_iUnion_le`); split each by the countably many values $y$ of $X_i$
(`MeasureTheory.measure_biUnion_le` or `tsum` over `Set.Countable.toEncodable`), use
independence of $\{X_i = y\}$ and $\zeta_i$
(`ProbabilityTheory.IndepFun.measure_inter_preimage_eq_mul` with $\{\mathrm{True}\}$, measurable
in `Prop.instMeasurableSpace` $= \top$)
and the law, bound $\nu(S_i(y))$ by the mean of $q_i(y, \cdot)$, reassemble with independence
again into $\int q_i(X_i, \zeta_i)\,d\mu$ (`MeasureTheory.lintegral_tsum`,
`ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun` on each fibre),
exchange sum and integral, and bound by $\theta$ (`MeasureTheory.lintegral_mono`,
`MeasureTheory.measureReal_def`). L, about 80 lines. -/
theorem measureReal_exists_mem_le_of_forall_measure_le_lintegral {ι γ β Ω : Type*} [Countable ι]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [MeasurableSpace β]
    {ν : Measure β} {ζ : ι → Ω → β} {X : ι → Ω → γ} (hζ : ∀ i, HasLaw (ζ i) ν μ)
    (hXc : ∀ i, (Set.range (X i)).Countable) (hXm : ∀ i y, MeasurableSet {ω | X i ω = y})
    (hind : ∀ i y, IndepFun (fun ω => X i ω = y) (ζ i) μ) {S : ι → γ → Set β}
    {q : ι → γ → β → ℝ≥0∞} (hq : ∀ i y, Measurable (q i y))
    (hSq : ∀ i y, ν (S i y) ≤ ∫⁻ z, q i y z ∂ν) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsum : ∀ ω, ∑' i, q i (X i ω) (ζ i ω) ≤ ENNReal.ofReal θ) :
    μ.real {ω | ∃ i, ζ i ω ∈ S i (X i ω)} ≤ θ := by
  sorry

end NLAlib
