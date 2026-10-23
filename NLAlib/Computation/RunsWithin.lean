/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import NLAlib.Computation.Exec

/-!
# Running within a budget

`NLAlib.Computation.RunsWithin I s st₀ c m Q` is the interface every realisation theorem
concludes: the run of `s` from `st₀` under `I` succeeds, its counts grow by at most `c`, its peak
memory plus the read-only data is at most `m p` cells at each tag `p`, and its final state
satisfies `Q`. It is an upper bound (D5): a program that does less work, such as Gram–Schmidt
meeting a zero column, still runs within the budget.

A tail bound for the specification of a program transfers to the program
(`NLAlib.Computation.measureReal_not_runsWithin_le`): if the program computes `F ω` within the
budget for every `ω`, the probability that it fails to compute a value satisfying `G` within the
budget is at most the probability that `F ω` fails `G`. Design: `docs/design/Computation.md`
(D3, D5, D14).

## Main definitions

* `NLAlib.Computation.RunsWithin`.

## Main results

* `NLAlib.Computation.measureReal_not_runsWithin_le`: the transfer of a tail bound.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib.Computation

variable {P ι K : Type} [DecidableEq P]

/-- **A run within a budget**: the run of `s` from `st₀` under `I` succeeds in a state `st` whose
counts are at most `c` more than at the start, whose peak memory plus the read-only data is at
most `m p` cells at each tag `p`, and which satisfies `Q`. -/
def RunsWithin {C : Type} [AddMonoid C] [Preorder C] (I : Interp P ι K C) (s : Stmt P ι ℕ ℕ)
    (st₀ : St P K C) (c : C) (m : P → ℕ) (Q : St P K C → Prop) : Prop :=
  ∃ st, exec I s st₀ = some st ∧ st.cnt ≤ st₀.cnt + c ∧ (∀ p, st.peak p + I.romSize p ≤ m p) ∧
    Q st

/-- **Transfer of a tail from a specification to a program.** If for every $\omega$ the program
$s$ runs within the budget and its output, read by `out`, is $F(\omega)$, then
$$\mathbb{P}\bigl[\text{the program does not compute, within the budget, a value satisfying } G
\bigr] \le \mathbb{P}\bigl[F(\omega) \text{ does not satisfy } G\bigr] \le \delta\,.$$
The interpretation may depend on $\omega$ (through its tape or its oracles). No printed source.
Result: computation-tail-transfer -/
theorem measureReal_not_runsWithin_le {Ω C β : Type} [AddMonoid C] [Preorder C]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {I : Ω → Interp P ι K C} {s : Stmt P ι ℕ ℕ} {st₀ : St P K C} {c : C} {m : P → ℕ}
    {out : St P K C → Option β} {F : Ω → β} {G : β → Prop}
    (hP : ∀ ω, RunsWithin (I ω) s st₀ c m (fun st => out st = some (F ω))) {δ : ℝ}
    (hδ : μ.real {ω | ¬ G (F ω)} ≤ δ) :
    μ.real {ω | ¬ RunsWithin (I ω) s st₀ c m (fun st => ∃ v, out st = some v ∧ G v)} ≤ δ := by
  refine le_trans (measureReal_mono (s₂ := {ω | ¬ G (F ω)}) ?_ (measure_ne_top _ _)) hδ
  intro ω hω hG
  obtain ⟨st, hrun, hc, hm, hv⟩ := hP ω
  exact hω ⟨st, hrun, hc, hm, F ω, hv, hG⟩

end NLAlib.Computation
