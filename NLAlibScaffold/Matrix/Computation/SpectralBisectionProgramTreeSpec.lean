/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.ProgramLogic
public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree

/-!
# The guarded block of the spectral bisection program as a specification (scaffold)

The rule for `NLAlib.eighWhen` (stage PROG-LOGIC, design note
`docs/design/Computation-ProgramLogic.md` §4.5). Final home:
`NLAlib/Matrix/Computation/SpectralBisectionProgramTree.lean` or the first S2 file that
specifies a guarded block.

## Main results

* `NLAlib.spec_eighWhen`: a guarded block runs its body once if the guard is positive and
  nothing otherwise.
-/

@[expose] public section

namespace NLAlib

open Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] {I : Interp P ι K C}

/-- **A guarded block as a specification**: `NLAlib.eighWhen e body` (a loop of
$1 - (1 - e)$ trips) leaves the state unchanged if $e = 0$ and meets the body's specification if
$e > 0$. No printed source. -/
theorem spec_eighWhen {m : Mode} {e : IExp ℕ} {body : Builder P ι ℕ ℕ Unit}
    {pre : St P K C → Prop} {fp : List (ℕ × ℕ × ℕ)} {post : St P K C → St P K C → Prop}
    (h : 0 < e.eval → Spec m I pre body.run fp post) :
    RoutineSpec m I pre (eighWhen e body) fp
      fun st st' => (e.eval = 0 → st' = st) ∧ (0 < e.eval → post st st') := by
  sorry

end NLAlib
