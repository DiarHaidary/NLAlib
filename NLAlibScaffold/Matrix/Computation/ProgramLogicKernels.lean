/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Computation.ProgramLogic
public import NLAlib.Matrix.Computation.KernelContracts
public import NLAlib.Matrix.Computation.OrthRoutine
public import NLAlib.Matrix.Computation.InterpMachine

/-!
# Kernel contracts and orthogonalization certificates as specifications (scaffold)

Statements for the program-logic bridges of the matrix layer (stage PROG-LOGIC, design note
`docs/design/Computation-ProgramLogic.md` §3.3 and §4.6). Final homes: the `EntryLayout` and
`IsMatMulKernel` statements in `NLAlib/Matrix/Computation/KernelContracts.lean`, the
`IsOrthRoutine` statement in `NLAlib/Matrix/Computation/OrthRoutine.lean`, the arithmetic
records in `NLAlib/Matrix/Computation/InterpMachine.lean` (next to
`NLAlib.Computation.ScalarSem.DecidesFlags`).

The certificate bridges (`NLAlib.Computation.IsOrthRoutine.routineSpec` here,
`NLAlib.Computation.IsBlockRoutine.routineSpec` and
`NLAlib.Computation.IsMatvecRoutine.routineSpec` in the logic) are total-only: a certificate
asserts success. A mode-generic proof uses them at `liberal` through
`NLAlib.Computation.Triple.liberal`, with their preconditions (writability included) proved in
both modes.

## Main definitions

* `NLAlib.Computation.IsControlExactSem`: exact control arithmetic (indices, flags, `≤`).
* `NLAlib.Computation.IsRoutineSem`: the standard model and exact control, in one record.

## Main results

* `NLAlib.Computation.readsOnly_entryLayoutHolds`: a stored matrix reads only its block.
* `NLAlib.Computation.IsMatMulKernel.spec_kcall`: a product kernel call as a specification.
* `NLAlib.Computation.IsOrthRoutine.routineSpec`: a certified orthogonalization routine as a
  specification.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P]

/-- A matrix stored in a layout reads only its block. -/
theorem readsOnly_entryLayoutHolds {E : Type} (L : EntryLayout K E) {l m : ℕ} (p : P)
    (b off : ℕ) (Y : Matrix (Fin l) (Fin m) E) :
    ReadsOnly (fun s : Store P K => L.Holds s p b off Y) [matBlock b off l m L.width] := by
  sorry

omit [DecidableEq P] in
/-- **Exact control arithmetic** at tag `p` and decoding `dec`: exact index arithmetic (integer
literals up to `B`, the conversion to an index the floor), flags decided, and the comparison `≤`
exact on decoded values. What the refinement of a program with data-dependent control flow
assumes, in both modes; it does not assume the standard model. -/
structure IsControlExactSem (dec : P → K → ℝ) (B : ℕ) (sem : ScalarSem P K) (p : P) : Prop where
  /-- Exact index arithmetic. -/
  index : IsIndexExactSem dec B sem
  /-- Flags are decided. -/
  flags : sem.DecidesFlags p
  /-- The comparison `≤` is exact. -/
  cmp_le : ∀ x y : K, sem.cmp p .le x y = some (decide (dec p x ≤ dec p y))

omit [DecidableEq P] in
/-- Exact control up to a literal bound holds up to every smaller bound. -/
theorem IsControlExactSem.mono {dec : P → K → ℝ} {B B' : ℕ} {sem : ScalarSem P K} {p : P}
    (h : IsControlExactSem dec B sem p) (hB : B' ≤ B) : IsControlExactSem dec B' sem p := by
  sorry

omit [DecidableEq P] in
/-- **The arithmetic assumptions of a routine**, in one record: the standard model at unit
roundoff `u` with decoding `dec` and safe set `safe` (a parameter, so a bounded-format range is
carried), and exact control. A mode-generic specification takes the standard model under
`m.Needs` and the control part unwrapped. -/
structure IsRoutineSem (u : P → ℝ) (dec : P → K → ℝ) (safe : P → ℝ → Prop) (B : ℕ)
    (sem : ScalarSem P K) (p : P) : Prop where
  /-- The standard model of rounding. -/
  relErr : IsRelErrSem u dec safe sem
  /-- Exact control. -/
  control : IsControlExactSem dec B sem p

variable [AddMonoid C]

/-- **A product kernel call as a specification**: on held factors and an output block disjoint
from them, the call writes the product into the output block only, charges one call and keeps
the tape positions; in mode `total` it also succeeds, given the output block writable. -/
theorem IsMatMulKernel.spec_kcall [Inhabited K] {E : Type} {I : Interp P ι K C} {o : ι}
    {L : EntryLayout K E} {mm : MatMulMap E} (h : IsMatMulKernel I o L mm)
    (hL : ∀ e, L.get (L.put e) = e) (md : Mode) (p : P) {l m n : ℕ} (a b c : ℕ × IExp ℕ)
    (A : Matrix (Fin l) (Fin m) E) (B : Matrix (Fin m) (Fin n) E) :
    Spec md I (fun st => L.Holds st.store p a.1 a.2.eval A ∧ L.Holds st.store p b.1 b.2.eval B ∧
        blockDisjoint (matBlock c.1 c.2.eval l n L.width) (matBlock a.1 a.2.eval l m L.width) =
          true ∧
        blockDisjoint (matBlock c.1 c.2.eval l n L.width) (matBlock b.1 b.2.eval m n L.width) =
          true ∧
        md.Needs (Writable st.store p c.1 c.2.eval (l * n * L.width)))
      (.kcall o p [.const l, .const m, .const n] [a, b] [c]) [matBlock c.1 c.2.eval l n L.width]
      fun st st' => L.Holds st'.store p c.1 c.2.eval (mm A B) ∧
        Costs (I.charge (.kcall p o [l, m, n])) st st' ∧ PosKept st st' := by
  sorry

/-- **A certified orthogonalization routine as a specification**, for each stored basis
$\mathbf{V}$ and vector $\mathbf{w}$, with distinct buffers: it modifies only the reduced vector
and coefficient blocks, which then decode to values meeting `NLAlib.IsOrthErr`. -/
theorem IsOrthRoutine.routineSpec {I : Interp P ι K C} {dec : P → K → ℝ} {tag : P} {N j : ℕ}
    {η₀ ε₁ ε₂ ε₃ : ℝ} {pre : Store P K → Prop} {Vb wb hb : ℕ} {wo ho : IExp ℕ}
    {r : Builder P ι ℕ ℕ Unit}
    (h : IsOrthRoutine I dec tag N j η₀ ε₁ ε₂ ε₃ pre Vb wb hb wo ho r) (hbw : hb ≠ wb)
    (hbV : hb ≠ Vb) (hwV : wb ≠ Vb) (V : Matrix (Fin N) (Fin j) ℝ) (w : Fin N → ℝ) :
    RoutineSpec .total I (fun st => pre st.store ∧ HoldsDecoded st.store dec tag Vb 0 V ∧
        ReadsDecoded st.store dec tag wb wo.eval w ∧ Writable st.store tag wb wo.eval N ∧
        Writable st.store tag hb ho.eval j) r [(wb, wo.eval, N), (hb, ho.eval, j)]
      fun _ st' => ∃ (W : Fin N → ℝ) (H : Fin j → ℝ), ReadsDecoded st'.store dec tag wb wo.eval W ∧
        ReadsDecoded st'.store dec tag hb ho.eval H ∧ IsOrthErr η₀ ε₁ ε₂ ε₃ V w H W := by
  sorry

end NLAlib.Computation
