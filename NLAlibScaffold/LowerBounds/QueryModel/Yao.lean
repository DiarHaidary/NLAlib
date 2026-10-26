/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.QueryModel.Yao

/-!
# Yao's principle with a bound for the members of the family (scaffold)

Statement for `NLAlib/LowerBounds/QueryModel/Yao.lean` (stage LB-C1, design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.1): the worst-case form of Yao's
principle needs the distributional bound only for the deterministic algorithms of the family, so
it applies to classes of algorithms (two-pass, one-sided) whose lower bound does not hold for
every algorithm.

## Main results

* `NLAlib.QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem_of_forall`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

namespace QueryAlgorithm

variable {Q R β S M : Type*} {q : ℕ} [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace β]
  [MeasurableSpace S] [MeasurableSpace M]

/-- **Yao's principle for a class of algorithms, worst-case form**: let $\rho$ be a seed law and
$\nu$ an input law, both probability measures, and $B$ a measurable set of (input, output) pairs.
If for every seed $s$ the deterministic algorithm $\mathcal{A}_s$ has $\nu$-probability at least
$\delta$ of $(x, \mathcal{A}_s(x)) \in B$, then some input $x$ has $\rho$-probability at least
$\delta$ of $(x, \mathcal{A}_s(x)) \in B$. The bound is needed only for the members of the family,
so a lower bound for a class of algorithms (pass-structured, one-sided) transfers to the
randomized algorithms of that class.
[Yao1977, Section 3] (locator to check); the averaging half, as
`NLAlib.QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem`, which follows from it.
Proof: the proof of `NLAlib.QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem`
verbatim, with `h (alg s) (halg.isMeasurable s)` replaced by `h s` (Fubini on
`MeasureTheory.Measure.prod`, `MeasureTheory.Measure.prod_apply`,
`MeasureTheory.Measure.prod_apply_symm`, `MeasureTheory.lintegral_mono`,
`MeasureTheory.lintegral_strict_mono`). S, about 30 lines. -/
theorem IsMeasurableFamily.exists_le_measureReal_run_mem_of_forall
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {O : M → Q → R}
    (hO : Measurable (Function.uncurry O)) (ρ : Measure S) [IsProbabilityMeasure ρ]
    (ν : Measure M) [IsProbabilityMeasure ν] {B : Set (M × β)} (hB : MeasurableSet B) {δ : ℝ}
    (h : ∀ s, δ ≤ ν.real {x | (x, (alg s).run (O x)) ∈ B}) :
    ∃ x, δ ≤ ρ.real {s | (x, (alg s).run (O x)) ∈ B} := by
  sorry

end QueryAlgorithm

end NLAlib
