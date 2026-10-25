/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Rank
public import NLAlib.ForMathlib.MeasureTheory.Matrix
public import NLAlib.Matrix.Basic.Dilation
public import NLAlib.Probability.QueryModel.Basic

/-!
# Adaptive query algorithms: the theorems of stage LB-A

Statements for `NLAlib/Probability/QueryModel/Basic.lean` whose proofs are deferred
(`docs/design/Probability-MatvecQueryModel.md`, §3.1). The responses of an algorithm are the
oracle's values at its queries; two oracles that agree at the queries made on one of them give the
same transcript (indistinguishability); non-adaptive queries do not depend on the transcript;
measurable algorithms have measurable transcripts and outputs; the Gram simulation runs an
algorithm for $\mathbf{X}\mathbf{X}^{\mathsf{H}}$ on two-sided queries to $\mathbf{X}$, with at
most `q` right queries.

## Main results

* `NLAlib.QueryAlgorithm.history_apply`, `NLAlib.QueryAlgorithm.queryAt_eq_queries_transcript`.
* `NLAlib.QueryAlgorithm.transcript_eq_of_forall_apply_queries_eq`,
  `NLAlib.QueryAlgorithm.run_eq_of_forall_apply_queries_eq`: indistinguishability.
* `NLAlib.QueryAlgorithm.IsNonAdaptive.queries_eq`.
* `NLAlib.QueryAlgorithm.IsMeasurable.measurable_transcript`,
  `NLAlib.QueryAlgorithm.IsMeasurable.measurable_run`,
  `NLAlib.QueryAlgorithm.IsMeasurable.measurable_queryMatrix`,
  `NLAlib.QueryAlgorithm.IsMeasurableFamily.measurable_run`,
  `NLAlib.QueryAlgorithm.IsMeasurableFamily.isMeasurable`.
* `NLAlib.QueryAlgorithm.run_gramSimulation`, `NLAlib.QueryAlgorithm.IsMeasurable.gramSimulation`,
  `NLAlib.QueryAlgorithm.rank_toRows₂_queryMatrix_gramSimulation_le`.
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
  sorry

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
  sorry

/-! ### Measurability -/

section Measurable

variable [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace β] {M : Type*}
  [MeasurableSpace M]

/-- **The transcript is measurable in the input**: for a measurable algorithm and an oracle
$O_x$ depending jointly measurably on an input $x$ and the query, $x \mapsto$ transcript is
measurable.
Proof: M, about 15 lines. Show `Measurable fun x => alg.history (O x) i` for every `i` by
induction: `measurable_pi_iff.2`, `Fin.lastCases`; the old entries by the induction hypothesis
(`Fin.snoc_castSucc`), the new one is
`hO.comp (measurable_id.prodMk ((halg.measurable_query i).comp ih))` (`Fin.snoc_last`). -/
theorem IsMeasurable.measurable_transcript {alg : QueryAlgorithm Q R q β}
    (halg : alg.IsMeasurable) {O : M → Q → R} (hO : Measurable (Function.uncurry O)) :
    Measurable fun x => alg.transcript (O x) := by
  sorry

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
`(measurable_pi_apply r).comp ((halg.measurable_query j).comp (measurable_pi_iff.2 fun l =>
measurable_pi_apply _))`. -/
theorem IsMeasurable.measurable_queryMatrix {𝕜 n : Type*} [MeasurableSpace 𝕜]
    {alg : QueryAlgorithm (n → 𝕜) R q β} (halg : alg.IsMeasurable) :
    Measurable (alg.queryMatrix : (Fin q → R) → Matrix n (Fin q) 𝕜) := by
  sorry

/-- **A randomized algorithm has a jointly measurable output**: for a measurable seeded family
and a jointly measurable oracle, (seed, input) $\mapsto$ output is measurable.
Proof: M, about 15 lines. As `QueryAlgorithm.IsMeasurable.measurable_transcript`, by induction
on the history length, with `halg.measurable_query i` composed with
`measurable_fst.prodMk ih`; then `halg.measurable_output.comp (measurable_fst.prodMk _)`. -/
theorem IsMeasurableFamily.measurable_run {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {O : M → Q → R}
    (hO : Measurable (Function.uncurry O)) :
    Measurable fun p : S × M => (alg p.1).run (O p.2) := by
  sorry

/-- **Each member of a measurable family is measurable**: fixing the seed of a measurable
randomized algorithm gives a measurable deterministic one.
Proof: S, two lines. Compose the joint maps with `measurable_prodMk_left` (`fun h => (s, h)`). -/
theorem IsMeasurableFamily.isMeasurable {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) (s : S) :
    (alg s).IsMeasurable := by
  sorry

end Measurable

/-! ### The Gram simulation -/

section Gram

variable {𝕜 d k : Type*} [RCLike 𝕜]

/-- **The Gram simulation runs the original algorithm**: the `2q`-query algorithm
`alg.gramSimulation k` against the dilation of $\mathbf{X} \in \Bbbk^{d \times k}$ outputs what
`alg` outputs against $\mathbf{X}\mathbf{X}^{\mathsf{H}}$. Two-sided queries to the factor
$\mathbf{X}$ therefore simulate products with $\mathbf{X}\mathbf{X}^{\mathsf{H}}$ at twice the
cost. [ZhangEtAl2026, Section 4]; there implicit in the reduction of the Wishart oracle to its
factor.
Proof: M, about 30 lines. Show that the decoded history (`d`-blocks of the odd responses) of the
simulation after `2 * i` queries is `alg.history (X * Xᴴ).mulVec i`, by induction on `i`, with
`QueryAlgorithm.history_apply` on both sides: response `2i` is `dilation X *ᵥ Sum.elim x 0`,
whose `k`-block is $\mathbf{X}^{\mathsf{H}}\mathbf{x}$; response `2i + 1` is
`dilation X *ᵥ Sum.elim 0 (Xᴴ *ᵥ x)`, whose `d`-block is `(X * Xᴴ) *ᵥ x`
(`dilation`, `Matrix.fromBlocks_mulVec`, `Matrix.mulVec_mulVec`); `Nat.mul_mod_right`,
`Nat.mul_div_cancel_left` and `omega` for the parity bookkeeping. -/
theorem run_gramSimulation [Fintype d] [Fintype k] (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β)
    (X : Matrix d k 𝕜) :
    (alg.gramSimulation k).run (dilation X).mulVec = alg.run (X * Xᴴ).mulVec := by
  sorry

/-- **The Gram simulation of a measurable algorithm is measurable.**
Proof: S, about 10 lines. Each query map is a `dite` on the fixed index `j`; both branches are
`Sum.elim` of measurable maps (`measurable_pi_iff`, `Measurable.sumElim` or entrywise
`Sum.forall`), the first through `halg.measurable_query (j / 2)` composed with the measurable
decoding `fun h l r => h ⟨2 * l + 1, _⟩ (Sum.inl r)`; the output likewise. -/
theorem IsMeasurable.gramSimulation [MeasurableSpace β]
    {alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β} (halg : alg.IsMeasurable) :
    (alg.gramSimulation k).IsMeasurable := by
  sorry

/-- **The Gram simulation makes at most `q` right queries**: for every transcript, the `k`-blocks
of its `2q` queries span a space of dimension at most `q`, since the even-numbered ones vanish.
Proof: M, about 15 lines. The matrix is `B * Matrix.of fun (l : Fin q) (j : Fin (2 * q)) => if
(j : ℕ) = 2 * l + 1 then 1 else 0` with `B : Matrix k (Fin q) 𝕜` the odd columns
(`Matrix.ext`, `Fintype.sum_eq_single`, the even columns are `Sum.elim _ 0` at `Sum.inr`); then
`Matrix.rank_mul_le_left` and `Matrix.rank_le_width`. -/
theorem rank_toRows₂_queryMatrix_gramSimulation_le (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β)
    (τ : Fin (2 * q) → (d ⊕ k → 𝕜)) :
    ((alg.gramSimulation k).queryMatrix τ).toRows₂.rank ≤ q := by
  sorry

end Gram

end QueryAlgorithm

end NLAlib
