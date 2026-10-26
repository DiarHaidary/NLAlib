/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.QueryModel.Basic

/-!
# Passes, response maps and output maps of query algorithms (scaffold)

Statements for `NLAlib/LowerBounds/QueryModel/Basic.lean` (stage LB-C1, design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.1): reading responses through a map
(`QueryAlgorithm.comapResponse`) runs the algorithm against the composed oracle, post-processing
the output (`QueryAlgorithm.mapOutput`) changes nothing else, both keep measurability and the
pass structure, every algorithm is pass-structured one query per pass, and one pass is
non-adaptivity.

## Main results

* `NLAlib.QueryAlgorithm.history_comapResponse`, `NLAlib.QueryAlgorithm.run_comapResponse`.
* `NLAlib.QueryAlgorithm.history_mapOutput`, `NLAlib.QueryAlgorithm.run_mapOutput`.
* `NLAlib.QueryAlgorithm.IsMeasurable.comapResponse`,
  `NLAlib.QueryAlgorithm.IsMeasurable.mapOutput`,
  `NLAlib.QueryAlgorithm.IsMeasurableFamily.comapResponse`,
  `NLAlib.QueryAlgorithm.IsMeasurableFamily.mapOutput`.
* `NLAlib.QueryAlgorithm.IsPassStructured.comapResponse`,
  `NLAlib.QueryAlgorithm.IsPassStructured.mapOutput`,
  `NLAlib.QueryAlgorithm.isPassStructured_id`,
  `NLAlib.QueryAlgorithm.isPassStructured_zero_iff_isNonAdaptive`.
-/

@[expose] public section

namespace NLAlib

namespace QueryAlgorithm

variable {Q R R' β β' : Type*} {q : ℕ}

/-- Reading the responses through $f$ reproduces the history: the history of
`alg.comapResponse f` against an oracle $O'$, read through $f$, is the history of `alg` against
$f \circ O'$, at every length $i$.
Proof: induction on `i`; both sides are `Fin.snoc` of the previous history and the response to
the same query (`QueryAlgorithm.history`, `Fin.comp_snoc`). S, about 8 lines. -/
theorem history_comapResponse (f : R' → R) (alg : QueryAlgorithm Q R q β) (O : Q → R')
    (i : ℕ) : f ∘ (alg.comapResponse f).history O i = alg.history (f ∘ O) i := by
  induction i with
  | zero => funext x; exact x.elim0
  | succ i ih =>
    rw [history, history, Fin.comp_snoc, ← ih]
    rfl

/-- An algorithm reading its responses through $f$ against the oracle $O'$ outputs what `alg`
outputs against $f \circ O'$. So a lower bound for an oracle $O$ holds for every weaker oracle
$f \circ O$: the matrix–vector oracle is the first component of `hiddenRotationOracle`.
Proof: `QueryAlgorithm.run` unfolds to `output` of the transcript; rewrite with
`QueryAlgorithm.history_comapResponse` at `i = q`. S, 2 lines. -/
theorem run_comapResponse (f : R' → R) (alg : QueryAlgorithm Q R q β) (O : Q → R') :
    (alg.comapResponse f).run O = alg.run (f ∘ O) := by
  sorry

/-- Post-processing the output does not change the history.
Proof: induction on `i`; `QueryAlgorithm.mapOutput` has the same `query` field, so each step is
`rfl` after `QueryAlgorithm.history`. S, 4 lines. -/
theorem history_mapOutput (g : β → β') (alg : QueryAlgorithm Q R q β) (O : Q → R) (i : ℕ) :
    (alg.mapOutput g).history O i = alg.history O i := by
  induction i with
  | zero => rfl
  | succ n ih => rw [history, history, ih]; rfl

/-- The output of `alg.mapOutput g` is $g$ of the output of `alg`.
Proof: unfold `QueryAlgorithm.run`, `QueryAlgorithm.transcript`; rewrite with
`QueryAlgorithm.history_mapOutput`. S, 2 lines. -/
theorem run_mapOutput (g : β → β') (alg : QueryAlgorithm Q R q β) (O : Q → R) :
    (alg.mapOutput g).run O = g (alg.run O) := by
  sorry

section Measurable

variable [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace R'] [MeasurableSpace β]
  [MeasurableSpace β']

private theorem measurable_comp_left {n : ℕ} {f : R' → R} (hf : Measurable f) :
    Measurable fun h : Fin n → R' => f ∘ h :=
  measurable_pi_iff.2 fun j => hf.comp (measurable_pi_apply j)

/-- Reading the responses through a measurable map keeps an algorithm measurable.
Proof: each query map is `alg.query i ∘ (f ∘ ·)`; post-composition with a measurable map is
measurable on the product σ-algebra (`measurable_pi_iff`, `Measurable.comp`), the same for the
output. S, 5 lines. -/
theorem IsMeasurable.comapResponse {alg : QueryAlgorithm Q R q β} (halg : alg.IsMeasurable)
    {f : R' → R} (hf : Measurable f) : (alg.comapResponse f).IsMeasurable :=
  { measurable_query := fun i hi => (halg.measurable_query i hi).comp (measurable_comp_left hf)
    measurable_output := halg.measurable_output.comp (measurable_comp_left hf) }

/-- Post-processing the output by a measurable map keeps an algorithm measurable.
Proof: the queries are those of `alg`; the output is `g ∘ alg.output` (`Measurable.comp`).
S, 3 lines. -/
theorem IsMeasurable.mapOutput {alg : QueryAlgorithm Q R q β} (halg : alg.IsMeasurable)
    {g : β → β'} (hg : Measurable g) : (alg.mapOutput g).IsMeasurable := by
  exact ⟨halg.measurable_query, hg.comp halg.measurable_output⟩

/-- A measurable seeded family reading its responses through a measurable map is measurable.
Proof: as `QueryAlgorithm.IsMeasurable.comapResponse`, with the seed carried along
(`Measurable.prodMk`, `measurable_fst`, `measurable_pi_iff`). S, 6 lines. -/
theorem IsMeasurableFamily.comapResponse {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {f : R' → R}
    (hf : Measurable f) : IsMeasurableFamily fun s => (alg s).comapResponse f := by
  refine ⟨fun i hi => ?_, ?_⟩
  · exact (halg.measurable_query i hi).comp (measurable_fst.prodMk
      (measurable_pi_iff.2 fun j => hf.comp ((measurable_pi_apply j).comp measurable_snd)))
  · exact (halg.measurable_output).comp (measurable_fst.prodMk
      (measurable_pi_iff.2 fun j => hf.comp ((measurable_pi_apply j).comp measurable_snd)))

/-- A measurable seeded family with its output post-processed by a measurable map is measurable.
Proof: the query maps are unchanged; the output is `g` after the joint output map
(`Measurable.comp`). S, 3 lines. -/
theorem IsMeasurableFamily.mapOutput {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {g : β → β'}
    (hg : Measurable g) : IsMeasurableFamily fun s => (alg s).mapOutput g :=
  ⟨halg.measurable_query, hg.comp halg.measurable_output⟩

end Measurable

/-- Reading the responses through a map keeps the pass structure.
Proof: `QueryAlgorithm.IsPassStructured.monotone` is unchanged; for `query_eq`, two histories that
agree on the earlier passes still agree after composing with `f`. S, 4 lines. -/
theorem IsPassStructured.comapResponse {alg : QueryAlgorithm Q R q β} {pass : ℕ → ℕ}
    (h : alg.IsPassStructured pass) (f : R' → R) :
    (alg.comapResponse f).IsPassStructured pass :=
  ⟨h.monotone, fun i hi u u' huu' =>
    h.query_eq i hi _ _ fun j hj => by simp only [Function.comp_apply]; rw [huu' j hj]⟩

/-- Post-processing the output keeps the pass structure.
Proof: the `query` field is that of `alg`; `QueryAlgorithm.IsPassStructured.query_eq` applies as
is. S, 1 line. -/
theorem IsPassStructured.mapOutput {alg : QueryAlgorithm Q R q β} {pass : ℕ → ℕ}
    (h : alg.IsPassStructured pass) (g : β → β') :
    (alg.mapOutput g).IsPassStructured pass := by
  exact ⟨h.monotone, h.query_eq⟩

/-- **Every algorithm is pass-structured with one query per pass**: with `pass = id` the
condition is that query $i$ depends only on the $i$ responses before it, which is the definition
of an adaptive algorithm. The fully adaptive model is the $q$-pass case.
Proof: `monotone_id`; for `query_eq`, the hypothesis gives `h = h'` by `funext` (every `j : Fin i`
has `j < i`). S, 3 lines. -/
theorem isPassStructured_id (alg : QueryAlgorithm Q R q β) : alg.IsPassStructured id := by
  sorry

/-- **One pass is non-adaptivity**: an algorithm is pass-structured with every round in pass
$0$ if and only if it is non-adaptive.
Proof: with the constant map the agreement hypothesis of `query_eq` is vacuous (`lt_irrefl`), so
both sides say every query is independent of the history (`QueryAlgorithm.IsNonAdaptive`);
`monotone_const`. S, 5 lines. -/
theorem isPassStructured_zero_iff_isNonAdaptive (alg : QueryAlgorithm Q R q β) :
    alg.IsPassStructured (fun _ => 0) ↔ alg.IsNonAdaptive := by
  sorry

end QueryAlgorithm

end NLAlib
