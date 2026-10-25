/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import NLAlib.ForMathlib.MeasureTheory.Matrix
public import NLAlib.Probability.QueryModel.Basic

/-!
# Adaptive query algorithms: the theorems of stage LB-A

Statements for `NLAlib/Probability/QueryModel/Basic.lean` whose proofs are deferred
(`docs/design/Probability-MatvecQueryModel.md`, §3.1). The responses of an algorithm are the
oracle's values at its queries; two oracles that agree at the queries made on one of them give the
same transcript (indistinguishability); non-adaptive queries do not depend on the transcript;
measurable algorithms have measurable transcripts and outputs; the rank of the right (left)
query matrix of pair queries is at most the number of right (left) products; the Gram simulation
runs an algorithm for $\mathbf{X}\mathbf{X}^{\mathsf{H}}$ on two-sided queries to $\mathbf{X}$,
with `q` products on each side.

## Main results

* `NLAlib.QueryAlgorithm.history_apply`, `NLAlib.QueryAlgorithm.queryAt_eq_queries_transcript`.
* `NLAlib.QueryAlgorithm.transcript_eq_of_forall_apply_queries_eq`,
  `NLAlib.QueryAlgorithm.run_eq_of_forall_apply_queries_eq`: indistinguishability.
* `NLAlib.QueryAlgorithm.IsNonAdaptive.queries_eq`.
* `NLAlib.QueryAlgorithm.IsMeasurable.measurable_transcript`,
  `NLAlib.QueryAlgorithm.IsMeasurable.measurable_run`,
  `NLAlib.QueryAlgorithm.IsMeasurable.measurable_queryMatrix`,
  `NLAlib.QueryAlgorithm.IsMeasurable.measurable_rightQueryMatrix`,
  `NLAlib.QueryAlgorithm.IsMeasurable.measurable_leftQueryMatrix`,
  `NLAlib.QueryAlgorithm.IsMeasurableFamily.measurable_run`,
  `NLAlib.QueryAlgorithm.IsMeasurableFamily.isMeasurable`.
* `NLAlib.QueryAlgorithm.rank_rightQueryMatrix_le_rightCount`,
  `NLAlib.QueryAlgorithm.rank_leftQueryMatrix_le_leftCount`: query spans and costs.
* `NLAlib.QueryAlgorithm.history_gramSimulation`, `NLAlib.QueryAlgorithm.run_gramSimulation`,
  `NLAlib.QueryAlgorithm.IsMeasurable.gramSimulation`,
  `NLAlib.QueryAlgorithm.rightCount_gramSimulation_le`,
  `NLAlib.QueryAlgorithm.leftCount_gramSimulation_le`,
  `NLAlib.QueryAlgorithm.rank_rightQueryMatrix_gramSimulation_le`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib

namespace QueryAlgorithm

variable {Q R β : Type*} {q : ℕ}

/-! ### Running an algorithm -/

/-- **Responses are oracle values**: the `j`-th of the first `i` responses of an algorithm run
against the oracle $f$ is $f$ at the `j`-th query, $h_j = f(x_j)$.
Proof: S, about 8 lines. Induction on `i`; `Fin.lastCases j`; `history` unfolds by `Fin.snoc`
(`Fin.snoc_castSucc` for the induction hypothesis, `Fin.snoc_last` and `queryAt` by `rfl` for
the new entry). -/
theorem history_apply (alg : QueryAlgorithm Q R q β) (f : Q → R) (i : ℕ) (j : Fin i) :
    alg.history f i j = f (alg.queryAt f j) := by
  induction i with
  | zero => exact j.elim0
  | succ i ih =>
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [history, Fin.snoc_last]
      rfl
    · rw [history, Fin.snoc_castSucc, ih]
      rfl

/-- **The queries made are the queries of the transcript**: the `j`-th query of an algorithm run
against $f$ is `queries` evaluated at its transcript.
Proof: S, about 6 lines. Unfold `queries`, `queryAt`; `congr 1`, `funext l`; both sides are
$f(x_l)$ by `QueryAlgorithm.history_apply` (on the left `history f j`, on the right
`transcript f = history f q` at `Fin.castLE _ l`, whose value is `l`). -/
theorem queryAt_eq_queries_transcript (alg : QueryAlgorithm Q R q β) (f : Q → R) (j : Fin q) :
    alg.queryAt f j = alg.queries (alg.transcript f) j := by
  sorry

/-- **Indistinguishability**: if a second oracle $g$ agrees with $f$ at every query the algorithm
makes against $f$, then the algorithm makes the same queries against $g$ and gets the same
transcript. This is the deterministic half of every adversary and deferred-decision argument.
Proof: M, about 20 lines. Show `∀ i ≤ q, alg.history g i = alg.history f i` by induction on `i`:
the step is `Fin.snoc` congruence with `alg.query i (history g i) = alg.query i (history f i)`
(induction hypothesis) and `h ⟨i, _⟩`, rewritten by `QueryAlgorithm.queryAt_eq_queries_transcript`
(the `i`-th query against $f$ is `alg.queries (alg.transcript f) i`). -/
theorem transcript_eq_of_forall_apply_queries_eq (alg : QueryAlgorithm Q R q β) {f g : Q → R}
    (h : ∀ j, g (alg.queries (alg.transcript f) j) = f (alg.queries (alg.transcript f) j)) :
    alg.transcript g = alg.transcript f := by
  sorry

/-- **Indistinguishability of outputs**: if $g$ agrees with $f$ at every query the algorithm makes
against $f$, the algorithm outputs the same value against both.
Proof: S, one line. `run`, `congrArg alg.output` of
`QueryAlgorithm.transcript_eq_of_forall_apply_queries_eq`. -/
theorem run_eq_of_forall_apply_queries_eq (alg : QueryAlgorithm Q R q β) {f g : Q → R}
    (h : ∀ j, g (alg.queries (alg.transcript f) j) = f (alg.queries (alg.transcript f) j)) :
    alg.run g = alg.run f := by
  sorry

/-- **Non-adaptive queries are fixed**: a non-adaptive algorithm makes the same queries whatever
the responses, so `queries` does not depend on the transcript.
Proof: S, two lines. `funext j`; `h j j.isLt _ _`. -/
theorem IsNonAdaptive.queries_eq {alg : QueryAlgorithm Q R q β} (h : alg.IsNonAdaptive)
    (τ τ' : Fin q → R) : alg.queries τ = alg.queries τ' := by
  funext j
  exact h j j.isLt _ _

/-! ### Measurability -/

section Measurable

variable [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace β] {M : Type*}
  [MeasurableSpace M]

/-- **The transcript is measurable in the input**: for a measurable algorithm and an oracle
$O_x$ depending jointly measurably on an input $x$ and the query, $x \mapsto$ transcript is
measurable.
Proof: M, about 15 lines. Show `Measurable fun x => alg.history (O x) i` for every `i ≤ q` by
induction: `measurable_pi_iff.2`, `Fin.lastCases`; the old entries by the induction hypothesis
(`Fin.snoc_castSucc`), the new one is
`hO.comp (measurable_id.prodMk ((halg.measurable_query i hi).comp ih))` (`Fin.snoc_last`). -/
theorem IsMeasurable.measurable_transcript {alg : QueryAlgorithm Q R q β}
    (halg : alg.IsMeasurable) {O : M → Q → R} (hO : Measurable (Function.uncurry O)) :
    Measurable fun x => alg.transcript (O x) := by
  have key : ∀ i ≤ q, Measurable fun x => alg.history (O x) i := by
    intro i
    induction i with
    | zero => intro _; exact measurable_pi_iff.2 fun j => j.elim0
    | succ i ih =>
      intro hi
      refine measurable_pi_iff.2 fun j => ?_
      induction j using Fin.lastCases with
      | last =>
        simp only [QueryAlgorithm.history, Fin.snoc_last]
        exact hO.comp (measurable_id.prodMk
          ((halg.measurable_query i (by omega)).comp (ih (by omega))))
      | cast j =>
        simp only [QueryAlgorithm.history, Fin.snoc_castSucc]
        exact (measurable_pi_apply j).comp (ih (by omega))
  exact key q le_rfl

/-- **The output is measurable in the input**, for a measurable algorithm and a jointly
measurable oracle.
Proof: S, one line. `halg.measurable_output.comp (halg.measurable_transcript hO)`
(`QueryAlgorithm.IsMeasurable.measurable_transcript`). -/
theorem IsMeasurable.measurable_run {alg : QueryAlgorithm Q R q β} (halg : alg.IsMeasurable)
    {O : M → Q → R} (hO : Measurable (Function.uncurry O)) :
    Measurable fun x => alg.run (O x) := by
  sorry

/-- **The query matrix is measurable in the transcript**, for a measurable algorithm with vector
queries. This is what makes the projectors onto the query spans random matrices.
Proof: S, about 6 lines. `measurable_pi_iff` twice (entries of `Matrix.of`); entry `(r, j)` is
`(measurable_pi_apply r).comp ((halg.measurable_query j j.isLt).comp (measurable_pi_iff.2 fun l =>
measurable_pi_apply _))`. -/
theorem IsMeasurable.measurable_queryMatrix {𝕜 n : Type*} [MeasurableSpace 𝕜]
    {alg : QueryAlgorithm (n → 𝕜) R q β} (halg : alg.IsMeasurable) :
    Measurable (alg.queryMatrix : (Fin q → R) → Matrix n (Fin q) 𝕜) := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun j => ?_
  exact (measurable_pi_apply r).comp ((halg.measurable_query j j.isLt).comp
    (measurable_pi_iff.2 fun l => measurable_pi_apply _))

/-- **The right query matrix is measurable in the transcript**, for a measurable algorithm with
pair queries $(\mathbf{x}, \mathbf{y})$.
Proof: S, about 6 lines. As `QueryAlgorithm.IsMeasurable.measurable_queryMatrix`, with
`measurable_fst` after the query map: entry `(r, j)` is `(measurable_pi_apply r).comp
(measurable_fst.comp ((halg.measurable_query j j.isLt).comp _))`. -/
theorem IsMeasurable.measurable_rightQueryMatrix {𝕜 m n : Type*} [MeasurableSpace 𝕜]
    {alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β} (halg : alg.IsMeasurable) :
    Measurable (alg.rightQueryMatrix : (Fin q → R) → Matrix n (Fin q) 𝕜) := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun j => ?_
  exact (measurable_pi_apply r).comp (measurable_fst.comp
    ((halg.measurable_query j j.isLt).comp (measurable_pi_iff.2 fun l => measurable_pi_apply _)))

/-- **The left query matrix is measurable in the transcript**, for a measurable algorithm with
pair queries $(\mathbf{x}, \mathbf{y})$.
Proof: S, about 6 lines. As `QueryAlgorithm.IsMeasurable.measurable_rightQueryMatrix`, with
`measurable_snd`. -/
theorem IsMeasurable.measurable_leftQueryMatrix {𝕜 m n : Type*} [MeasurableSpace 𝕜]
    {alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β} (halg : alg.IsMeasurable) :
    Measurable (alg.leftQueryMatrix : (Fin q → R) → Matrix m (Fin q) 𝕜) := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun j => ?_
  exact (measurable_pi_apply r).comp
    (measurable_snd.comp ((halg.measurable_query j j.isLt).comp
      (measurable_pi_iff.2 fun l => measurable_pi_apply _)))

/-- The histories of a measurable seeded family, jointly measurable in the seed and the input. -/
private theorem measurable_history_family {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {O : M → Q → R}
    (hO : Measurable (Function.uncurry O)) :
    ∀ i, i ≤ q → Measurable fun p : S × M => (alg p.1).history (O p.2) i := by
  intro i
  induction i with
  | zero => intro _; exact measurable_const
  | succ i ih =>
    intro hi
    have hq : Measurable fun p : S × M => (alg p.1).query i ((alg p.1).history (O p.2) i) :=
      (halg.measurable_query i (by omega)).comp (measurable_fst.prodMk (ih (by omega)))
    have hv : Measurable fun p : S × M =>
        O p.2 ((alg p.1).query i ((alg p.1).history (O p.2) i)) :=
      hO.comp (measurable_snd.prodMk hq)
    refine measurable_pi_iff.2 fun j => ?_
    induction j using Fin.lastCases with
    | last =>
      change Measurable fun p : S × M => Fin.snoc (α := fun _ => R)
        ((alg p.1).history (O p.2) i) (O p.2 ((alg p.1).query i ((alg p.1).history (O p.2) i)))
        (Fin.last i)
      simpa only [Fin.snoc_last] using hv
    | cast k =>
      change Measurable fun p : S × M => Fin.snoc (α := fun _ => R)
        ((alg p.1).history (O p.2) i) (O p.2 ((alg p.1).query i ((alg p.1).history (O p.2) i)))
        (Fin.castSucc k)
      simp only [Fin.snoc_castSucc]
      exact (measurable_pi_apply k).comp (ih (by omega))

/-- **A randomized algorithm has a jointly measurable output**: for a measurable seeded family
and a jointly measurable oracle, (seed, input) $\mapsto$ output is measurable.
Proof: M, about 15 lines. As `QueryAlgorithm.IsMeasurable.measurable_transcript`, by induction
on the history length `i ≤ q`, with `halg.measurable_query i hi` composed with
`measurable_fst.prodMk ih`; then `halg.measurable_output.comp (measurable_fst.prodMk _)`. -/
theorem IsMeasurableFamily.measurable_run {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {O : M → Q → R}
    (hO : Measurable (Function.uncurry O)) :
    Measurable fun p : S × M => (alg p.1).run (O p.2) :=
  halg.measurable_output.comp
    (measurable_fst.prodMk (measurable_history_family halg hO q le_rfl))

/-- **Each member of a measurable family is measurable**: fixing the seed of a measurable
randomized algorithm gives a measurable deterministic one.
Proof: S, two lines. Compose the joint maps with `measurable_prodMk_left` (`fun h => (s, h)`),
`fun i hi => (halg.measurable_query i hi).comp measurable_prodMk_left`. -/
theorem IsMeasurableFamily.isMeasurable {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) (s : S) :
    (alg s).IsMeasurable := by
  have hq : ∀ i < q, Measurable ((alg s).query i) := fun i hi =>
    (halg.measurable_query i hi).comp measurable_prodMk_left
  have ho : Measurable (alg s).output := halg.measurable_output.comp measurable_prodMk_left
  exact ⟨hq, ho⟩

/-- **Truncating a measurable algorithm keeps it measurable**, for `i ≤ q`.
Proof: S, two lines. `⟨fun j hj => halg.measurable_query j (by omega), measurable_const⟩`
(`QueryAlgorithm.truncate`). -/
theorem IsMeasurable.truncate {alg : QueryAlgorithm Q R q β} (halg : alg.IsMeasurable) {i : ℕ}
    (hi : i ≤ q) : (alg.truncate i).IsMeasurable := by
  exact ⟨fun j hj => halg.measurable_query j (by omega), measurable_const⟩

end Measurable

/-! ### Costs of pair queries -/

section Count

variable {𝕜 m n : Type*} [Field 𝕜]

/-- **The right query span is bounded by the number of right products**: the rank of the right
query matrix is at most the number of rounds with a nonzero right part.
Proof: S, about 10 lines. `Matrix.rank_eq_finrank_span_cols`; the span of all columns is the span
of the nonzero ones (`Submodule.span_le`, zero columns lie in every submodule), whose finrank is
at most their number (`finrank_span_le_card`, `Set.ncard_eq_toFinset_card'`). -/
theorem rank_rightQueryMatrix_le_rightCount (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β)
    (τ : Fin q → R) : (alg.rightQueryMatrix τ).rank ≤ alg.rightCount τ := by
  classical
  set J : Set (Fin q) := {j | (alg.queries τ j).1 ≠ 0} with hJ
  set s : Set (n → 𝕜) := (fun j => (alg.queries τ j).1) '' J with hs
  have hspan : Submodule.span 𝕜 (Set.range (alg.rightQueryMatrix τ).col) ≤
      Submodule.span 𝕜 s := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases h : (alg.queries τ j).1 = 0
    · have hcol : (alg.rightQueryMatrix τ).col j = 0 := by
        ext r
        simp [rightQueryMatrix, h]
      rw [hcol]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨j, h, rfl⟩
  have hcard : s.ncard ≤ J.ncard := Set.ncard_image_le (Set.toFinite J)
  have : Module.Finite 𝕜 (Submodule.span 𝕜 s) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.toFinite s)
  rw [Matrix.rank_eq_finrank_span_cols]
  calc Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range (alg.rightQueryMatrix τ).col))
      ≤ Module.finrank 𝕜 (Submodule.span 𝕜 s) := Submodule.finrank_mono hspan
    _ ≤ s.toFinset.card := finrank_span_le_card s
    _ = s.ncard := (Set.ncard_eq_toFinset_card' s).symm
    _ ≤ J.ncard := hcard

/-- **The left query span is bounded by the number of left products**: the rank of the left query
matrix is at most the number of rounds with a nonzero left part.
Proof: S, about 10 lines. As `QueryAlgorithm.rank_rightQueryMatrix_le_rightCount`. -/
theorem rank_leftQueryMatrix_le_leftCount (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β)
    (τ : Fin q → R) : (alg.leftQueryMatrix τ).rank ≤ alg.leftCount τ := by
  sorry

end Count

/-! ### The Gram simulation -/

section Gram

variable {𝕜 d k : Type*} [RCLike 𝕜]

/-- **The Gram simulation reproduces the history**: after `2 * i` rounds of `alg.gramSimulation k`
against `twoSidedMulVec X`, the first components of the odd responses are the first `i`
responses of `alg` against $\mathbf{X}\mathbf{X}^{\mathsf{H}}$. Holds for every `i`.
Proof: M, about 50 lines. Prefer, to `Fin.snoc` rewriting under `Fin (2 * (i + 1))`, a pointwise
strong induction on the entry `l`: by `QueryAlgorithm.history_apply` on both sides, entry `l` is
`(f (queryAt (2 * l + 1))).1 = X *ᵥ (f (queryAt (2 * l))).2`, and that is
`X *ᵥ (Xᴴ *ᵥ alg.query l (decoded history of length 2 * l))`, which the induction hypothesis
at the entries below `l` identifies with `(X * Xᴴ) *ᵥ alg.queryAt _ l`. Round `2i` is
$(\mathbf{0}, \mathbf{x}_i)$ with $\mathbf{x}_i$ = `alg.query i` of the decoded history, equal to
`alg.history (X * Xᴴ).mulVec i` by the induction hypothesis (the decoding at `2 * i + 1` and at
`2 * i` read the same odd entries, `Fin.snoc_castSucc`); its response has second component
$\mathbf{X}^{\mathsf{H}}\mathbf{x}_i$. Round `2i + 1` is
$(\mathbf{X}^{\mathsf{H}}\mathbf{x}_i, \mathbf{0})$, whose first component response is
$\mathbf{X}\mathbf{X}^{\mathsf{H}}\mathbf{x}_i$ (`twoSidedMulVec`, `Matrix.mulVec_mulVec`);
`Nat.mul_mod_right`, `Nat.mul_div_cancel_left`, `Nat.add_mod` and `omega` for the parity
bookkeeping. -/
theorem history_gramSimulation [Fintype d] [Fintype k] (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β)
    (X : Matrix d k 𝕜) (i : ℕ) :
    (fun l : Fin i => ((alg.gramSimulation k).history (twoSidedMulVec X) (2 * i)
        ⟨2 * l + 1, by have := l.isLt; omega⟩).1) = alg.history (X * Xᴴ).mulVec i := by
  sorry

/-- **The Gram simulation runs the original algorithm**: the `2q`-round algorithm
`alg.gramSimulation k` against `twoSidedMulVec X`, $\mathbf{X} \in \Bbbk^{d \times k}$, outputs
what `alg` outputs against $\mathbf{X}\mathbf{X}^{\mathsf{H}}$. Two-sided queries to the factor
$\mathbf{X}$ therefore simulate products with $\mathbf{X}\mathbf{X}^{\mathsf{H}}$, at `q` products
with each of $\mathbf{X}$ and $\mathbf{X}^{\mathsf{H}}$
(`QueryAlgorithm.rightCount_gramSimulation_le`, `QueryAlgorithm.leftCount_gramSimulation_le`).
[ZhangEtAl2026, Section 4]; there implicit in the reduction of the Wishart oracle to its factor.
Proof: S, about 3 lines. Unfold `run`, `transcript`, `gramSimulation`; `congrArg alg.output` of
`QueryAlgorithm.history_gramSimulation` at `i = q`. -/
theorem run_gramSimulation [Fintype d] [Fintype k] (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β)
    (X : Matrix d k 𝕜) :
    (alg.gramSimulation k).run (twoSidedMulVec X) = alg.run (X * Xᴴ).mulVec := by
  sorry

/-- **The Gram simulation of a measurable algorithm is measurable.**
Proof: S, about 10 lines. Each query map, for `j < 2 * q`, is a `dite` on the fixed index `j`;
both branches are pairs of measurable maps (`Measurable.prodMk`, `measurable_const`), the even
one through `halg.measurable_query (j / 2) (by omega)` composed with the measurable decoding
`fun h l => (h ⟨2 * l + 1, _⟩).1` (`measurable_pi_iff`, `measurable_fst`), the odd one
`measurable_snd.comp (measurable_pi_apply _)`; the output likewise. -/
theorem IsMeasurable.gramSimulation [MeasurableSpace 𝕜] [MeasurableSpace β]
    {alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β} (halg : alg.IsMeasurable) :
    (alg.gramSimulation k).IsMeasurable := by
  refine ⟨fun j hj => ?_, ?_⟩
  · unfold QueryAlgorithm.gramSimulation
    by_cases hjm : j % 2 = 0
    · simp only [hjm, dite_true]
      refine measurable_const.prodMk ((halg.measurable_query (j / 2) (by omega)).comp ?_)
      exact measurable_pi_iff.2 fun l => measurable_fst.comp (measurable_pi_apply _)
    · simp only [hjm, dite_false]
      exact (measurable_snd.comp (measurable_pi_apply _)).prodMk measurable_const
  · refine halg.measurable_output.comp ?_
    exact measurable_pi_iff.2 fun l => measurable_fst.comp (measurable_pi_apply _)

/-- **The Gram simulation makes at most `q` products with $\mathbf{X}$**: for every transcript,
only odd-numbered rounds have a nonzero right part.
Proof: S, about 10 lines. The set of rounds with a nonzero right part is contained in the odd
indices (`gramSimulation`, the even query is `(0, _)`), on which `fun j => (j : ℕ) / 2` into
`Fin q` is injective (`omega`); `Set.ncard_le_ncard_of_injOn` and `Set.ncard_univ`,
`Nat.card_eq_fintype_card`, `Fintype.card_fin`. -/
theorem rightCount_gramSimulation_le (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β)
    (τ : Fin (2 * q) → (d → 𝕜) × (k → 𝕜)) : (alg.gramSimulation k).rightCount τ ≤ q := by
  sorry

/-- **The Gram simulation makes at most `q` products with $\mathbf{X}^{\mathsf{H}}$**: for every
transcript, only even-numbered rounds have a nonzero left part.
Proof: S, about 10 lines. As `QueryAlgorithm.rightCount_gramSimulation_le`, with the even indices
(the odd query is `(_, 0)`). -/
theorem leftCount_gramSimulation_le (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β)
    (τ : Fin (2 * q) → (d → 𝕜) × (k → 𝕜)) : (alg.gramSimulation k).leftCount τ ≤ q := by
  sorry

/-- **The right queries of the Gram simulation span at most `q` dimensions**: for every
transcript, the right query matrix has rank at most `q`.
Proof: S, one line. `(QueryAlgorithm.rank_rightQueryMatrix_le_rightCount _ τ).trans
(QueryAlgorithm.rightCount_gramSimulation_le alg τ)`. -/
theorem rank_rightQueryMatrix_gramSimulation_le
    (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β) (τ : Fin (2 * q) → (d → 𝕜) × (k → 𝕜)) :
    ((alg.gramSimulation k).rightQueryMatrix τ).rank ≤ q := by
  sorry

end Gram

end QueryAlgorithm

end NLAlib
