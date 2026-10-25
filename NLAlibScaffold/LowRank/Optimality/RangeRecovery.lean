/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Probability.QueryModel.Yao
public import NLAlibScaffold.RandomMatrix.DeferredDecision
public import NLAlibScaffold.RandomMatrix.Gaussian.Rank

/-!
# Exact range recovery needs as many queries as the rank

For $\mathbf{A} = \mathbf{X}\mathbf{X}^{\mathsf{H}}$ with $\mathbf{X}$ a standard Gaussian
$d \times k$ matrix, an algorithm that makes fewer than $k$ adaptive products with $\mathbf{A}$
outputs, with probability one, a matrix whose range does not contain the range of $\mathbf{A}$,
unless that output has full rank $d$. In particular no algorithm with fewer than $k$ queries
outputs a rank-$k$ projector $\mathbf{P}$ with $\mathbf{A}(\mathbf{I} - \mathbf{P}) = \mathbf{0}$
with positive probability, for any $k < d$. This is the first end-to-end theorem of the query
model (`docs/design/Probability-MatvecQueryModel.md`, §3.6): Yao's principle, the Gram simulation
and the adaptive Gaussian deferred decision. Since $\mathbf{A}$ is Hermitian, products with
$\mathbf{A}^{\mathsf{H}}$ are products with $\mathbf{A}$, so the bound counts all products.

## Main results

In the `NLAlib.QueryAlgorithm` namespace:

* `IsMeasurable.ae_rank_conjTranspose_mul_toRows₁_queryMatrix_gramSimulation`: the left
  responses of the Gram simulation are in general position.
* `IsMeasurable.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix`: deterministic
  algorithms.
* `IsMeasurableFamily.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix`: randomized
  algorithms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

namespace QueryAlgorithm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {d k : Type*} [Fintype d]
  [Fintype k] {q : ℕ}

/-- **The left responses of the Gram simulation are in general position**: for a measurable
algorithm making $q \le k$ queries to $\mathbf{X}\mathbf{X}^{\mathsf{H}}$, with $\mathbf{X}$ a
standard Gaussian $d \times k$ matrix, let $\mathbf{U}$ be the $d \times 2q$ matrix of left
queries of its Gram simulation (columns $\mathbf{x}_i$ and zeros). Almost surely
$\operatorname{rank}(\mathbf{X}^{\mathsf{H}}\mathbf{U}) = \operatorname{rank}\mathbf{U}$: no
nonzero combination of the queries is annihilated by $\mathbf{X}^{\mathsf{H}}$.
[ZhangEtAl2026, proof of Lemma 4.2]; there inside the block decomposition of Lemma 4.1.
Proof: L, about 60 lines. `rank (Xᴴ * U) ≤ rank U` always (`Matrix.rank_mul_le_right`). For the
reverse, induction on the number of original queries, through the truncated algorithm. At query
`i` the right queries so far are $\mathbf{X}^{\mathsf{H}}\mathbf{x}_l$, $l < i$, so
$\mathbf{F}$ projects onto the complement of their span, of dimension at least $k - i \ge 1$.
Write $\mathbf{x}_i = \mathbf{a} + \mathbf{b}$ with $\mathbf{a}$ in the span of the earlier
left queries and $\mathbf{b} = \mathbf{E}\mathbf{x}_i$. If $\mathbf{b} = \mathbf{0}$ both ranks
stay. Otherwise the rank of $\mathbf{X}^{\mathsf{H}}\mathbf{U}$ grows unless
$\mathbf{F}\mathbf{X}^{\mathsf{H}}\mathbf{E}\mathbf{x}_i = \mathbf{0}$; by
`QueryAlgorithm.IsMeasurable.identDistrib_resample_of_hasLaw_gaussianMatrix` (for the truncated
simulation, $2i$ queries) $\mathbf{E}\mathbf{X}\mathbf{F}$ may be replaced by
$\mathbf{E}\mathbf{X}'\mathbf{F}$ with $\mathbf{X}'$ independent, and for fixed history the event
$\mathbf{b}^{\mathsf{H}}\mathbf{X}'\mathbf{F} = \mathbf{0}$ has probability zero
(`NLAlib.measure_mul_mul_eq_eq_zero_of_hasLaw_gaussianMatrix` with
$\mathbf{N} = \mathbf{b}^{\mathsf{H}} \ne \mathbf{0}$, $\mathbf{F} \ne \mathbf{0}$, after
freezing: `ProbabilityTheory.IndepFun.measureReal_mem_le_add` with $\delta_1 = \delta_2 = 0$).
Uses `QueryAlgorithm.rank_toRows₂_queryMatrix_gramSimulation_le` for the dimension count. -/
theorem IsMeasurable.ae_rank_conjTranspose_mul_toRows₁_queryMatrix_gramSimulation
    {β : Type*} [MeasurableSpace β] {alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β}
    (halg : alg.IsMeasurable) {X : Ω → Matrix d k ℝ} (hX : HasLaw X (gaussianMatrix d k) μ)
    (hq : q ≤ Fintype.card k) :
    ∀ᵐ ω ∂μ, ((X ω)ᴴ * ((alg.gramSimulation k).queryMatrix
        ((alg.gramSimulation k).transcript (dilation (X ω)).mulVec)).toRows₁).rank =
      ((alg.gramSimulation k).queryMatrix
        ((alg.gramSimulation k).transcript (dilation (X ω)).mulVec)).toRows₁.rank := by
  sorry

/-- **Exact range recovery needs $k$ queries, deterministic algorithms**: let $\mathbf{X}$ be a
standard Gaussian $d \times k$ matrix and $\mathbf{A} = \mathbf{X}\mathbf{X}^{\mathsf{H}}$. A
measurable deterministic algorithm making $q < k$ adaptive queries $\mathbf{x} \mapsto
\mathbf{A}\mathbf{x}$ and outputting $\mathbf{V} \in \mathbb{R}^{d \times p}$ satisfies
$$\mathbb{P}\bigl[\operatorname{range}\mathbf{A} \subseteq \operatorname{range}\mathbf{V}
\text{ and } \operatorname{rank}\mathbf{V} < d\bigr] = 0\,.$$
For an output rank-$k$ projector $\mathbf{P}$ ($k < d$) the event is
$\mathbf{A}(\mathbf{I} - \mathbf{P}) = \mathbf{0}$.
[ZhangEtAl2026, Lemma 4.2]; there for rank-$k$ projector outputs and success probability bounded
below, here any output with rank below $d$, success probability zero, $k \ge d$ allowed (then
$\operatorname{range}\mathbf{A} = \mathbb{R}^d$ almost surely and the event is impossible).
Proof: L, about 70 lines. By `QueryAlgorithm.run_gramSimulation` the output is that of
`alg.gramSimulation k` on the dilation of $\mathbf{X}$ (measurable by
`QueryAlgorithm.IsMeasurable.gramSimulation`), and
$\operatorname{range}\mathbf{A} = \operatorname{range}\mathbf{X}$ over $\mathbb{R}$. Extend
$\Omega$ by an independent Gaussian $\mathbf{X}'$ (`Measure.prod`); by
`QueryAlgorithm.IsMeasurable.identDistrib_resample_of_hasLaw_gaussianMatrix` and
`QueryAlgorithm.transcript_resample` the event has the probability of the same event for
$\widetilde{\mathbf{X}} = \mathbf{X} - \mathbf{E}\mathbf{X}\mathbf{F} +
\mathbf{E}\mathbf{X}'\mathbf{F}$ with the same output $\mathbf{V}$ (the event is measurable:
$\operatorname{range}\mathbf{A} \subseteq \operatorname{range}\mathbf{V}$ iff
$(\mathbf{I} - \mathbf{P}_{\mathbf{V}})\mathbf{A} = \mathbf{0}$, `measurable_rangeProjector`,
`measurable_rank`). Condition on $\mathbf{X}$ (`ProbabilityTheory.IndepFun.measureReal_mem_le_add`
with the good set of
`QueryAlgorithm.IsMeasurable.ae_rank_conjTranspose_mul_toRows₁_queryMatrix_gramSimulation`).
For fixed $\mathbf{X}$ in the good set, with $\mathbf{N} = \mathbf{I} - \mathbf{P}_{\mathbf{V}}
\ne \mathbf{0}$ (rank below $d$), the event is
$\mathbf{N}\mathbf{E}\mathbf{X}'\mathbf{F}
= -\mathbf{N}(\mathbf{X} - \mathbf{E}\mathbf{X}\mathbf{F})$.
$\mathbf{F} \ne \mathbf{0}$ by `QueryAlgorithm.rank_toRows₂_queryMatrix_gramSimulation_le` and
$q < k$. If $\mathbf{N}\mathbf{E} \ne \mathbf{0}$ the probability is zero
(`NLAlib.measure_mul_mul_eq_eq_zero_of_hasLaw_gaussianMatrix`). If
$\mathbf{N}\mathbf{E} = \mathbf{0}$ the rows of $\mathbf{N}$ lie in the span of the left
queries and the event says $\mathbf{N}\mathbf{X} = \mathbf{0}$, which contradicts the good set: a
nonzero row $\mathbf{n} = \mathbf{U}\mathbf{c}$ with $\mathbf{X}^{\mathsf{H}}\mathbf{U}\mathbf{c}
= \mathbf{0}$ forces $\operatorname{rank}(\mathbf{X}^{\mathsf{H}}\mathbf{U}) <
\operatorname{rank}\mathbf{U}$ (`Matrix.rank_mul_le`, rank–nullity). Split the case analysis
into a private lemma. -/
theorem IsMeasurable.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix {p : Type*}
    [Fintype p] {alg : QueryAlgorithm (d → ℝ) (d → ℝ) q (Matrix d p ℝ)}
    (halg : alg.IsMeasurable) {X : Ω → Matrix d k ℝ} (hX : HasLaw X (gaussianMatrix d k) μ)
    (hq : q < Fintype.card k) :
    μ {ω | LinearMap.range (X ω * (X ω)ᴴ).mulVecLin ≤
        LinearMap.range (alg.run (X ω * (X ω)ᴴ).mulVec).mulVecLin ∧
      (alg.run (X ω * (X ω)ᴴ).mulVec).rank < Fintype.card d} = 0 := by
  sorry

/-- **Exact range recovery needs $k$ queries**: let $\mathbf{X}$ be a standard Gaussian
$d \times k$ matrix and $\mathbf{A} = \mathbf{X}\mathbf{X}^{\mathsf{H}}$. A randomized algorithm
(a measurable family of algorithms indexed by a seed $s$ independent of $\mathbf{X}$) making
$q < k$ adaptive queries $\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ and outputting
$\mathbf{V} \in \mathbb{R}^{d \times p}$ satisfies
$$\mathbb{P}\bigl[\operatorname{range}\mathbf{A} \subseteq \operatorname{range}\mathbf{V}
\text{ and } \operatorname{rank}\mathbf{V} < d\bigr] = 0\,.$$
So exact recovery of the range of a rank-$k$ positive semidefinite matrix by a rank-$k$ projector
($k < d$) needs at least $k$ matrix–vector products, for every success probability $> 0$.
[ZhangEtAl2026, Lemma 4.2]; there for rank-$k$ projector outputs.
Proof: S, about 15 lines. `QueryAlgorithm.IsMeasurableFamily.measureReal_run_mem_le_of_indepFun`
with $\delta = 0$, oracle `fun X => (X * Xᴴ).mulVec` (measurable: `Measurable.matrix_mulVec`,
`Continuous.matrix_mul`), and $B$ the measurable set
$\{(\mathbf{X}, \mathbf{V}) \mid
(\mathbf{I} - \mathbf{P}_{\mathbf{V}})\mathbf{X}\mathbf{X}^{\mathsf{H}} = \mathbf{0} \wedge
\operatorname{rank}\mathbf{V} < d\}$ (`measurable_rangeProjector`,
`measurable_rank`; it equals the event, `range_le_iff_exists_mul` or the projector form);
each deterministic case is
`QueryAlgorithm.IsMeasurable.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix`
(`measureReal_eq_zero_iff`). Back to `μ` with `measureReal_eq_zero_iff`.
Result: range-recovery-k-queries -/
theorem IsMeasurableFamily.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix
    {S p : Type*} [MeasurableSpace S] [Fintype p]
    {alg : S → QueryAlgorithm (d → ℝ) (d → ℝ) q (Matrix d p ℝ)} (halg : IsMeasurableFamily alg)
    {s : Ω → S} (hs : AEMeasurable s μ) {X : Ω → Matrix d k ℝ}
    (hX : HasLaw X (gaussianMatrix d k) μ) (hsX : IndepFun s X μ) (hq : q < Fintype.card k) :
    μ {ω | LinearMap.range (X ω * (X ω)ᴴ).mulVecLin ≤
        LinearMap.range ((alg (s ω)).run (X ω * (X ω)ᴴ).mulVec).mulVecLin ∧
      ((alg (s ω)).run (X ω * (X ω)ᴴ).mulVec).rank < Fintype.card d} = 0 := by
  sorry

end QueryAlgorithm

end NLAlib
