/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Computation.ProgramLogic
public import NLAlib.Matrix.Computation.KernelContracts
public import NLAlib.Matrix.Computation.OrthRoutine

/-!
# Kernel contracts and orthogonalization certificates as specifications (scaffold)

Statements for the program-logic bridges of the matrix layer (stage PROG-LOGIC, design note
`docs/design/Computation-ProgramLogic.md` §4.6, ids PL70–PL72). Final homes: the
`EntryLayout` and `IsMatMulKernel` statements in
`NLAlib/Matrix/Computation/KernelContracts.lean`, the `IsOrthRoutine` statement in
`NLAlib/Matrix/Computation/OrthRoutine.lean`.

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
    ReadsOnly (fun s : Store P K => L.Holds s p b off Y) [(b, off, l * m * L.width)] := by
  sorry

variable [AddMonoid C]

/-- **A product kernel call as a specification**: on held factors and a writable output block
disjoint from them, the call succeeds (in every mode), writes the product into the output block
only, charges one call and keeps the tape positions. -/
theorem IsMatMulKernel.spec_kcall [Inhabited K] {E : Type} {I : Interp P ι K C} {o : ι}
    {L : EntryLayout K E} {mm : MatMulMap E} (h : IsMatMulKernel I o L mm)
    (hL : ∀ e, L.get (L.put e) = e) (md : Mode) (p : P) {l m n : ℕ} (a b c : ℕ × IExp ℕ)
    (A : Matrix (Fin l) (Fin m) E) (B : Matrix (Fin m) (Fin n) E) :
    Spec md I (fun st => L.Holds st.store p a.1 a.2.eval A ∧ L.Holds st.store p b.1 b.2.eval B ∧
        Writable st.store p c.1 c.2.eval (n * l * L.width) ∧
        blockDisjoint (c.1, c.2.eval, n * l * L.width) (a.1, a.2.eval, m * l * L.width) = true ∧
        blockDisjoint (c.1, c.2.eval, n * l * L.width) (b.1, b.2.eval, n * m * L.width) = true)
      (.kcall o p [.const l, .const m, .const n] [a, b] [c]) [(c.1, c.2.eval, n * l * L.width)]
      fun st st' => L.Holds st'.store p c.1 c.2.eval (mm A B) ∧
        Costs (I.charge (.kcall p o [l, m, n])) st st' ∧ st'.pos = st.pos := by
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
