/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exec

/-!
# Costs of a straight-line run do not depend on the value semantics

A statement is **straight-line** (`NLAlib.Computation.Stmt.StraightLine`) when it has no
conditional (`ite`) and no loop on a comparison (`whileFuel`): its control flow is fixed by its
syntax. The tape positions, counts and memory of a successful run of a straight-line statement
(`NLAlib.Computation.St.usage`) are then a function of the syntax, the charge and the widths only,
not of the value semantics, the tapes, the oracles or the stored values
(`NLAlib.Computation.usage_eq_of_exec_eq_some_of_straightLine`). So a floating-point analysis
of a straight-line kernel takes its counts and memory from the exact specification of the kernel,
and becomes a `NLAlib.Computation.RunsWithin` statement. To move into
`NLAlib/Computation/Exec.lean` when proved. Design: `docs/design/Computation-Rounding.md` (R5).

## Main definitions

* `NLAlib.Computation.Stmt.StraightLine`: no `ite` and no `whileFuel`.
* `NLAlib.Computation.St.usage`: the tape positions, counts and memory of a state.

## Main results

* `NLAlib.Computation.usage_eq_of_exec_eq_some_of_straightLine`: two successful runs of a
  straight-line statement, under interpretations with the same charge and widths, from states
  with the same usage and store shape, end with the same usage.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι VB VI : Type}

/-- A statement is **straight-line** if it has no conditional (`ite`) and no loop on a comparison
(`whileFuel`), in any loop or allocation body: which instructions it runs is fixed by its syntax
and its index values, not by the stored values. -/
def Stmt.StraightLine : Stmt P ι VB VI → Prop
  | .skip => True
  | .seq s t => s.StraightLine ∧ t.StraightLine
  | .instr _ => True
  | .apply .. => True
  | .rom .. => True
  | .alloc _ _ body => ∀ b, (body b).StraightLine
  | .loop _ body => ∀ i, (body i).StraightLine
  | .whileFuel .. => False
  | .ite .. => False
  | .named _ _ body => body.StraightLine

/-- The **usage** of a state: the tape positions, the counts, and the current and peak memory,
in cells per tag and in bits; the state without its store. -/
def St.usage {K C : Type} (st : St P K C) : (Dist → ℕ) × C × (P → ℕ) × (P → ℕ) × ℕ × ℕ :=
  (st.pos, st.cnt, st.cur, st.peak, st.curW, st.peakW)

variable [DecidableEq P] {K K' C : Type} [AddMonoid C]

/-- **The costs of a straight-line run do not depend on the value semantics**: for interpretations
`I` and `I'` (over any carriers) with the same charge and the same widths, and a straight-line
statement $s$, if the runs of $s$ under `I` from $\mathit{st}_0$ and under `I'` from
$\mathit{st}'_0$ both succeed, and the two start states have the same usage and the same store
shape, then the two end states have the same usage: the same tape positions, counts, and current
and peak memory. The value semantics, tapes, oracles, read-only data and stored values may
differ. No printed source. -/
theorem usage_eq_of_exec_eq_some_of_straightLine (I : Interp P ι K C) (I' : Interp P ι K' C)
    (hc : I.charge = I'.charge) (hw : I.width = I'.width) {s : Stmt P ι ℕ ℕ}
    (hs : s.StraightLine) {st₀ st₁ : St P K C} {st₀' st₁' : St P K' C}
    (hshape : st₀.store.shape = st₀'.store.shape) (husage : st₀.usage = st₀'.usage)
    (h : exec I s st₀ = some st₁) (h' : exec I' s st₀' = some st₁') :
    st₁.usage = st₁'.usage := by
  sorry

end NLAlib.Computation
