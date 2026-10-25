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

* `NLAlib.rank_mul_of_snoc_eq_rank_of_snoc`: the rank step of general position.

In the `NLAlib.QueryAlgorithm` namespace:

* `IsMeasurable.measure_queryAt_notMem_span_and_mulVec_mem_span_eq_zero`: one query at a time,
  a new direction is almost surely not collapsed by $\mathbf{X}^{\mathsf{H}}$.
* `IsMeasurable.ae_rank_conjTranspose_mul_leftQueryMatrix_gramSimulation`: the left
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

private lemma finrank_sup_span_singleton_of_notMem {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] {p : Submodule K V} [FiniteDimensional K p] {v : V}
    (hv : v ∉ p) : Module.finrank K ↥(p ⊔ K ∙ v) = Module.finrank K p + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ p.zero_mem)
  have hinf : p ⊓ K ∙ v = ⊥ :=
    (Submodule.disjoint_span_singleton' hv0).mpr hv |>.eq_bot
  have := Submodule.finrank_sup_add_finrank_inf_eq p (K ∙ v)
  rw [hinf, finrank_bot, finrank_span_singleton hv0] at this
  omega

/-- **Rank step of general position**: let $\mathbf{B} \in \Bbbk^{k \times d}$ preserve the rank
of $\mathbf{U} \in \Bbbk^{d \times i}$, $\operatorname{rank}(\mathbf{B}\mathbf{U}) =
\operatorname{rank}\mathbf{U}$, and append a column $\mathbf{x}$. If $\mathbf{x}$ lies in the
column span of $\mathbf{U}$, or $\mathbf{B}\mathbf{x}$ does not lie in the column span of
$\mathbf{B}\mathbf{U}$, then $\mathbf{B}$ preserves the rank of $[\mathbf{U}\;\mathbf{x}]$.
Proof: M, about 40 lines. `Matrix.rank_eq_finrank_span_cols` on all four matrices; the columns of
`Matrix.of fun r => Fin.snoc (U r) (x r)` are those of $\mathbf{U}$ and $\mathbf{x}$
(`Fin.snoc_castSucc`, `Fin.snoc_last`, `Fin.lastCases`), so its column span is
`span (range Uᵀ) ⊔ span {x}` (`Submodule.span_insert`, `Set.range` of a `Fin.snoc`), and
likewise for $\mathbf{B}[\mathbf{U}\;\mathbf{x}] = [\mathbf{B}\mathbf{U}\;\mathbf{B}\mathbf{x}]$
(`Matrix.mul_apply`, `Matrix.mulVec`). First case: both spans are unchanged
(`Submodule.span_insert_eq_span`; $\mathbf{B}\mathbf{x}$ is in the image span by linearity,
`Submodule.span_image` with `Matrix.mulVecLin`). Second case: then $\mathbf{x}$ is not in the span
of $\mathbf{U}$ either (else $\mathbf{B}\mathbf{x}$ would be in the image), and both finranks
grow by one (`Submodule.span_insert` and a `finrank` count for adding a vector outside a
subspace, e.g. through `Submodule.finrank_add_eq_of_isCompl` or
`finrank_sup_add_finrank_inf_eq`). -/
theorem rank_mul_of_snoc_eq_rank_of_snoc {𝕜 : Type*} [Field 𝕜] {d k : Type*} [Fintype d] {i : ℕ}
    (B : Matrix k d 𝕜) (U : Matrix d (Fin i) 𝕜) (x : d → 𝕜)
    (hU : (B * U).rank = U.rank)
    (hx : x ∈ Submodule.span 𝕜 (Set.range Uᵀ) ∨ B *ᵥ x ∉ Submodule.span 𝕜 (Set.range (B * U)ᵀ)) :
    (B * Matrix.of fun r => Fin.snoc (α := fun _ => 𝕜) (U r) (x r)).rank =
      (Matrix.of fun r => Fin.snoc (α := fun _ => 𝕜) (U r) (x r)).rank := by
  set M : Matrix d (Fin (i + 1)) 𝕜 := Matrix.of fun r => Fin.snoc (α := fun _ => 𝕜) (U r) (x r)
  have hcolBU : Set.range (B * U).col = Matrix.mulVecLin B '' Set.range U.col := by
    rw [← Set.range_comp]
    congr 1
  have hMcol : M.col = Fin.snoc U.col x := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [Fin.snoc_last]; funext r; simp [M]
    · rw [Fin.snoc_castSucc]; funext r; simp [M]
  have hcolM : Set.range M.col = insert x (Set.range U.col) := by
    rw [hMcol, Fin.range_snoc]
  have hcolBM : Set.range (B * M).col = insert (B *ᵥ x) (Set.range (B * U).col) := by
    have : (B * M).col = Fin.snoc (B * U).col (B *ᵥ x) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last]; funext r; simp [M, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      · rw [Fin.snoc_castSucc]; funext r; simp [M, Matrix.mul_apply]
    rw [this, Fin.range_snoc]
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols] at hU ⊢
  rw [hcolBM, hcolM, Submodule.span_insert, Submodule.span_insert]
  change x ∈ Submodule.span 𝕜 (Set.range U.col) ∨
    B *ᵥ x ∉ Submodule.span 𝕜 (Set.range (B * U).col) at hx
  rw [hcolBU, Submodule.span_image] at hU hx ⊢
  have hW : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range U.col)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  generalize Submodule.span 𝕜 (Set.range U.col) = W at hU hx hW ⊢
  have hBx : B *ᵥ x = B.mulVecLin x := rfl
  rw [hBx] at hx ⊢
  rcases em (x ∈ W) with h | h
  · rw [sup_eq_right.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr h),
      sup_eq_right.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr
        (Submodule.mem_map_of_mem h)), hU]
  · have h' : B.mulVecLin x ∉ W.map B.mulVecLin := hx.resolve_left h
    rw [sup_comm, finrank_sup_span_singleton_of_notMem h',
      sup_comm, finrank_sup_span_singleton_of_notMem h, hU]

namespace QueryAlgorithm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {d k : Type*} [Fintype d]
  [Fintype k] {q : ℕ}

/-- **One step of general position**: for a measurable algorithm making adaptive queries
$\mathbf{x}_0, \mathbf{x}_1, \dots$ to $\mathbf{X}\mathbf{X}^{\mathsf{H}}$, with $\mathbf{X}$ a
standard Gaussian $d \times k$ matrix, and $i < q$, $i < k$: almost surely, either
$\mathbf{x}_i$ lies in the span of $\mathbf{x}_0, \dots, \mathbf{x}_{i-1}$, or
$\mathbf{X}^{\mathsf{H}}\mathbf{x}_i$ does not lie in the span of
$\mathbf{X}^{\mathsf{H}}\mathbf{x}_0, \dots, \mathbf{X}^{\mathsf{H}}\mathbf{x}_{i-1}$.
[ZhangEtAl2026, proof of Lemma 4.2]; there inside the block decomposition of Lemma 4.1.
Proof: L, about 70 lines. Let $T$ be the Gram simulation truncated to its first `2 * i` rounds,
`(alg.gramSimulation k).truncate (2 * i)` (measurable: `QueryAlgorithm.IsMeasurable.truncate` of
`QueryAlgorithm.IsMeasurable.gramSimulation`, `2 * i ≤ 2 * q`), with transcript
`(alg.gramSimulation k).history (twoSidedMulVec X) (2 * i)`
(`QueryAlgorithm.transcript_truncate`). By
`QueryAlgorithm.history_gramSimulation` and `QueryAlgorithm.history_apply`, the queries
$\mathbf{x}_l$ ($l \le i$) are functions of that transcript, the left query matrix of $T$ has
columns $\mathbf{x}_l$ and zeros, and its right query matrix has columns
$\mathbf{X}^{\mathsf{H}}\mathbf{x}_l$ (second components of the even responses) and zeros; so with
$\mathbf{E}$, $\mathbf{F}$ as in `QueryAlgorithm.resample` for $T$, the first condition is
$\mathbf{E}\mathbf{x}_i \ne \mathbf{0}$ and the second
$\mathbf{F}\mathbf{X}^{\mathsf{H}}\mathbf{x}_i = \mathbf{0}$ (`rangeProjector`, range of the
complement projector). Extend $\Omega$ by an independent Gaussian $\mathbf{X}'$ (`Measure.prod`
with `gaussianMatrix d k`). By
`QueryAlgorithm.IsMeasurable.identDistrib_resample_of_hasLaw_gaussianMatrix` for $T$, the event has
the probability of the same event for $\widetilde{\mathbf{X}} = \mathbf{X} -
\mathbf{E}\mathbf{X}\mathbf{F} + \mathbf{E}\mathbf{X}'\mathbf{F}$ with the transcript of
$\mathbf{X}$, and $\mathbf{F}\widetilde{\mathbf{X}}^{\mathsf{H}}\mathbf{x}_i
= \mathbf{F}\mathbf{X}'^{\mathsf{H}}\mathbf{E}\mathbf{x}_i$ ($\mathbf{F}\mathbf{X}^{\mathsf{H}}
(\mathbf{I} - \mathbf{E})\mathbf{x}_i = \mathbf{0}$ since $(\mathbf{I} - \mathbf{E})\mathbf{x}_i$
is in the left query span). Freeze the transcript
(`ProbabilityTheory.IndepFun.measureReal_mem_le_add` with $\delta_1 = \delta_2 = 0$, the
transcript of $\mathbf{X}$ independent of $\mathbf{X}'$): for a fixed transcript with
$\mathbf{E}\mathbf{x}_i \ne \mathbf{0}$, the event
$(\mathbf{E}\mathbf{x}_i)^{\mathsf{H}}\mathbf{X}'\mathbf{F} = \mathbf{0}$ has probability zero
by `NLAlib.measure_mul_mul_eq_eq_zero_of_hasLaw_gaussianMatrix` (row matrix
$\mathbf{N} = (\mathbf{E}\mathbf{x}_i)^{\mathsf{H}} \ne \mathbf{0}$, and $\mathbf{F} \ne
\mathbf{0}$ because the range of the right query matrix of $T$ is the span of the
$\mathbf{X}^{\mathsf{H}}\mathbf{x}_l$, $l < i$, of finrank at most $i < k$
(`finrank_span_le_card`; the width of that matrix is `2 * i`, so `Matrix.rank_le_width` does not
suffice)). Split off the identification of the event with the $\mathbf{E}$, $\mathbf{F}$
form as a private lemma. -/
theorem IsMeasurable.measure_queryAt_notMem_span_and_mulVec_mem_span_eq_zero {β : Type*}
    [MeasurableSpace β] {alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β} (halg : alg.IsMeasurable)
    {X : Ω → Matrix d k ℝ} (hX : HasLaw X (gaussianMatrix d k) μ) {i : ℕ} (hi : i < q)
    (hik : i < Fintype.card k) :
    μ {ω | alg.queryAt (X ω * (X ω)ᴴ).mulVec i ∉
        Submodule.span ℝ (Set.range fun l : Fin i => alg.queryAt (X ω * (X ω)ᴴ).mulVec l) ∧
      (X ω)ᴴ *ᵥ alg.queryAt (X ω * (X ω)ᴴ).mulVec i ∈
        Submodule.span ℝ
          (Set.range fun l : Fin i => (X ω)ᴴ *ᵥ alg.queryAt (X ω * (X ω)ᴴ).mulVec l)} = 0 := by
  sorry

/-- **The left queries of the Gram simulation are in general position**: for a measurable
algorithm making $q \le k$ queries to $\mathbf{X}\mathbf{X}^{\mathsf{H}}$, with $\mathbf{X}$ a
standard Gaussian $d \times k$ matrix, let $\mathbf{U}$ be the $d \times 2q$ left query matrix of
its Gram simulation (columns $\mathbf{x}_i$ and zeros). Almost surely
$\operatorname{rank}(\mathbf{X}^{\mathsf{H}}\mathbf{U}) = \operatorname{rank}\mathbf{U}$: no
nonzero combination of the queries is annihilated by $\mathbf{X}^{\mathsf{H}}$.
[ZhangEtAl2026, proof of Lemma 4.2]; there inside the block decomposition of Lemma 4.1.
Proof: M, about 50 lines. Almost surely the events of
`QueryAlgorithm.IsMeasurable.measure_queryAt_notMem_span_and_mulVec_mem_span_eq_zero` fail for
every `i < q` (`ae_all_iff` over `Fin q`, `measure_eq_zero_iff_ae_notMem`; `i < k` from `hq`). On
that set, with $\mathbf{U}_i$ = `Matrix.of fun r (l : Fin i) => alg.queryAt (X * Xᴴ).mulVec l r`,
show $\operatorname{rank}(\mathbf{X}^{\mathsf{H}}\mathbf{U}_i) = \operatorname{rank}\mathbf{U}_i$
for `i ≤ q` by induction: `i = 0` both sides are `0` (`Matrix.rank_le_width`); the step is
`NLAlib.rank_mul_of_snoc_eq_rank_of_snoc` with `B = Xᴴ` ($\mathbf{U}_{i+1}$ is the `Fin.snoc` of
$\mathbf{U}_i$ and
$\mathbf{x}_i$, `Matrix.ext`, `Fin.lastCases`), whose hypothesis is the negation of the bad event
(`not_and_or`, `not_not`; the column spans are `Set.range` of the queries, `Matrix.mul_apply`).
Finally the left query matrix of the simulation has the columns of $\mathbf{U}_q$ (at the even
indices, by `QueryAlgorithm.history_gramSimulation` and
`QueryAlgorithm.queryAt_eq_queries_transcript`) and zero columns, and $\mathbf{X}^{\mathsf{H}}$
times it the columns of $\mathbf{X}^{\mathsf{H}}\mathbf{U}_q$ and zeros, so both column spans
agree (`Matrix.rank_eq_finrank_span_cols`, `Submodule.span_insert_zero`-type rewriting) and the
ranks transfer. -/
theorem IsMeasurable.ae_rank_conjTranspose_mul_leftQueryMatrix_gramSimulation
    {β : Type*} [MeasurableSpace β] {alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β}
    (halg : alg.IsMeasurable) {X : Ω → Matrix d k ℝ} (hX : HasLaw X (gaussianMatrix d k) μ)
    (hq : q ≤ Fintype.card k) :
    ∀ᵐ ω ∂μ, ((X ω)ᴴ * (alg.gramSimulation k).leftQueryMatrix
        ((alg.gramSimulation k).transcript (twoSidedMulVec (X ω)))).rank =
      ((alg.gramSimulation k).leftQueryMatrix
        ((alg.gramSimulation k).transcript (twoSidedMulVec (X ω)))).rank := by
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
`alg.gramSimulation k` on `twoSidedMulVec X` (measurable by
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
`QueryAlgorithm.IsMeasurable.ae_rank_conjTranspose_mul_leftQueryMatrix_gramSimulation`).
For fixed $\mathbf{X}$ in the good set, with $\mathbf{N} = \mathbf{I} - \mathbf{P}_{\mathbf{V}}
\ne \mathbf{0}$ (rank below $d$), the event is
$\mathbf{N}\mathbf{E}\mathbf{X}'\mathbf{F}
= -\mathbf{N}(\mathbf{X} - \mathbf{E}\mathbf{X}\mathbf{F})$.
$\mathbf{F} \ne \mathbf{0}$ by `QueryAlgorithm.rank_rightQueryMatrix_gramSimulation_le` and
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
