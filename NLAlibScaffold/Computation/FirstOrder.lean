/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.FirstOrder

/-!
# Kernel calls in the run of a first-order program (scaffold)

Statements for `NLAlib/Computation/FirstOrder.lean` (stage COMPDYN S1a, design note
`docs/design/Computation-DynamicPrograms.md`, "S1 implementation status"): the run of a
first-order kernel call.

## Main results

* `NLAlib.Computation.FStmt.exec_kcall`: the run of a first-order kernel call.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- **The run of a first-order kernel call**: in the environment of handles `ρB` and of index
values `ρI`, it runs `NLAlib.Computation.Interp.kcallStore` at the values of its dimensions and
offsets, the handles renamed by `ρB`, and charges one call of its kind at those dimensions.
No printed source.
Proof: `rw [FStmt.exec]`. S, 1 line. -/
theorem FStmt.exec_kcall (I : Interp P ι K C) {nb ni : ℕ} (o : ι) (p : P)
    (dims : List (IExp (Fin ni))) (ins outs : List (Fin nb × IExp (Fin ni))) (ρB : Fin nb → ℕ)
    (ρI : Fin ni → ℕ) (st : St P K C) :
    (FStmt.kcall o p dims ins outs).exec I ρB ρI st =
      (I.kcallStore o p (dims.map (·.evalIn ρI)) (ins.map fun x => (ρB x.1, x.2.evalIn ρI))
        (outs.map fun x => (ρB x.1, x.2.evalIn ρI)) st.store).map fun s =>
          { st with
            store := s
            cnt := st.cnt + I.charge (.kcall p o (dims.map (·.evalIn ρI))) } := by
  sorry

end NLAlib.Computation
