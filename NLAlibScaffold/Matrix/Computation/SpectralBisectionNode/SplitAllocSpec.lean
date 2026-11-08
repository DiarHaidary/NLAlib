/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineSpec
public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree

/-!
# The scratch prefix of the split block as a specification (scaffold, pilot gate 3)

Gate 3 of the PROG-LOGIC pilot (design note `docs/design/Computation-ProgramLogic.md` §7.3, job
J1): the eight scoped allocations of `NLAlib.eighSplitBlock`, discharged by
`NLAlib.Computation.Spec.allocBind` with named states, so that a specification of the block's
body at the relative scratch handles $b, \dots, b + 7$ gives the block's specification. Final
home: `NLAlib/Matrix/Computation/SpectralBisectionNode/Split.lean`.

## Main results

* `NLAlib.spec_eighSplitBlock_of_body`: the eight scratch buffers of a split.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] {I : Interp P ι K C}

/-- **The scratch prefix of a split.** If the store has $b$ buffers in every state satisfying
`pre`, and the body of `NLAlib.eighSplitBlock` (two deflations, two compressions and four size
literals) at the scratch handles $b, \dots, b + 7$ meets a specification from the state after
the eight allocations of $2n^2$ cells, modifying `fp` and the eight scratch buffers, then the
split block meets the specification whose footprint is `fp` and whose postcondition is the
body's after the eight releases. No printed source. -/
theorem spec_eighSplitBlock_of_body {m : Mode} (p : P) (mm qr : ι) (n d lo k kp : IExp ℕ)
    (Sg Pp Pm Ma Qa Sz Kd Kp : ℕ) (two sg nsg sq : Cell ℕ ℕ) {b : ℕ}
    {pre pre' : St P K C → Prop} {post post' : St P K C → St P K C → Prop}
    {fp : List (ℕ × ℕ × ℕ)} (hb : ∀ st, pre st → st.store.size = b)
    (hpre : ∀ st, pre st →
      pre' ((fun s => s.allocate p (2 * (n * n) : IExp ℕ).eval (I.width p))^[8] st))
    (h : Spec m I pre' (do
        eighDeflateBlock p mm qr n k kp lo 0 Sg sq Pp b (b + 1) (b + 2) (b + 3) Qa
          (eighBlockOff n d lo)
        eighDeflateBlock p mm qr n k (k - kp) lo 1 Sg sq Pm b (b + 1) (b + 2) (b + 3) Qa
          (eighBlockOff n d lo + 2 * (k * kp))
        eighCompressBlock p mm k kp Qa (eighBlockOff n d lo) Ma (eighBlockOff n d lo)
          (eighBlockOff n (d + 1) lo) two sg (b + 4) (b + 5) (b + 6) (b + 7)
        eighCompressBlock p mm k (k - kp) Qa (eighBlockOff n d lo + 2 * (k * kp)) Ma
          (eighBlockOff n d lo) (eighBlockOff n (d + 1) (lo + kp)) two nsg (b + 4) (b + 5)
          (b + 6) (b + 7)
        ins (.litIdx p ⟨Sz, eighSlotOff n (d + 1) lo⟩ kp)
        ins (.litIdx p ⟨Sz, eighSlotOff n (d + 1) (lo + kp)⟩ (k - kp))
        ins (.litIdx p ⟨Kd, eighSlotOff n d lo⟩ 4)
        ins (.litIdx p ⟨Kp, eighSlotOff n d lo⟩ kp) : Builder P ι ℕ ℕ Unit).run
      (fp ++ (List.range 8).map fun j => (b + j, 0, (2 * (n * n) : IExp ℕ).eval)) post')
    (hpost : ∀ st st', pre st →
      post' ((fun s => s.allocate p (2 * (n * n) : IExp ℕ).eval (I.width p))^[8] st) st' →
      post st ((fun s => s.release p (2 * (n * n) : IExp ℕ).eval (I.width p))^[8] st')) :
    RoutineSpec m I pre (eighSplitBlock p mm qr n d lo k kp Sg Pp Pm Ma Qa Sz Kd Kp two sg nsg sq)
      fp post := by
  sorry

end NLAlib
