/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.MatrixKernels
public import NLAlib.Computation.Model
public import NLAlib.Krylov.LinearSystems.CGRecurrence

/-!
# Proposed matrix-free conjugate gradient implementation

A distinct fixed program uses one oracle application per active iteration, preserving the
cached-residual update order and guarded terminal behavior of the stored implementation.
The zero-length reserved matrix slot permits sharing the existing physical scalar addresses.
The design and exact proposed resources are in `docs/design/CG-Matrix-Free-Program.md`.

## Main definitions

* `NLAlib.cgOracleProg`, `NLAlib.cgOracleProg.compiled`: the proposed oracle program and tree.
* `NLAlib.cgOracleCount`: the componentwise upper count formula.
* `NLAlib.MatrixFreeConjugateGradient`: the exact proposed target, not registered yet.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

/-- The oracle CG variant from zero, with cached squared residuals and guarded divisions.
Its matrix access is a one-column oracle application; there is no stored matrix or ROM read.
The empty scratch slot keeps the canonical vector/scalar buffer addresses. -/
def cgOracleProg {P ι VB VI : Type} (tag : P) (o : ι) (N q : IExp VI)
    (b x r p status : VB) : Builder P ι VB VI Unit := scope do
  let _matrixSlot ← alloc tag 0
  let s ← alloc tag N
  let scalars ← alloc tag 9
  ins (.lit tag ⟨scalars, 6⟩ 0)
  ins (.lit tag ⟨scalars, 7⟩ 1)
  ins (.un tag .neg ⟨scalars, 8⟩ ⟨scalars, 7⟩)
  ins (.copy tag ⟨status, 0⟩ ⟨scalars, 6⟩)
  forRange N fun i => ins (.lit tag ⟨x, .var i⟩ 0)
  copyv tag b 0 r 0 N
  copyv tag b 0 p 0 N
  dot tag ⟨scalars, 0⟩ r 0 r 0 N
  ifThenElse tag .eq ⟨scalars, 0⟩ ⟨scalars, 6⟩
    (ins (.copy tag ⟨status, 0⟩ ⟨scalars, 7⟩)) (pure ())
  forRange q fun _ => ifThenElse tag .eq ⟨status, 0⟩ ⟨scalars, 6⟩
    (do
      stmt (.apply o tag s 0 p 0 1)
      dot tag ⟨scalars, 2⟩ p 0 s 0 N
      ifThenElse tag .lt ⟨scalars, 6⟩ ⟨scalars, 2⟩ (do
        ins (.bin tag .div ⟨scalars, 3⟩ ⟨scalars, 0⟩ ⟨scalars, 2⟩)
        axpy tag ⟨scalars, 3⟩ p 0 x 0 N
        ins (.un tag .neg ⟨scalars, 5⟩ ⟨scalars, 3⟩)
        axpy tag ⟨scalars, 5⟩ s 0 r 0 N
        dot tag ⟨scalars, 1⟩ r 0 r 0 N
        ins (.bin tag .div ⟨scalars, 4⟩ ⟨scalars, 1⟩ ⟨scalars, 0⟩)
        forRange N fun i => do
          ins (.bin tag .mul ⟨scalars, 2⟩ ⟨scalars, 4⟩ ⟨p, .var i⟩)
          ins (.bin tag .add ⟨p, .var i⟩ ⟨r, .var i⟩ ⟨scalars, 2⟩)
        ins (.copy tag ⟨scalars, 0⟩ ⟨scalars, 1⟩)
        ifThenElse tag .eq ⟨scalars, 0⟩ ⟨scalars, 6⟩
          (ins (.copy tag ⟨status, 0⟩ ⟨scalars, 7⟩)) (pure ()))
        (ins (.copy tag ⟨status, 0⟩ ⟨scalars, 8⟩))) (pure ())


/-- The proposed matrix-free tree, compiled once at symbolic dimension and step count. -/
def cgOracleProg.compiled {P ι : Type} (tag : P) (o : ι) : Prog P ι 1 5 :=
  (ProgFamily.compile fun _ _ N q h =>
    (cgOracleProg tag o N (q 0) (h 0) (h 1) (h 2) (h 3) (h 4)).run).get rfl

/-- The symbolic tree instantiates to the displayed oracle builder. -/
theorem cgOracleProg.toStmt_compiled {P ι : Type} (tag : P) (o : ι) (N q : ℕ) :
    (cgOracleProg.compiled tag o).toStmt N ![q] =
      (cgOracleProg tag o (.const N) (.const q) 0 1 2 3 4).run := rfl

/-- Componentwise upper counts for q requested iterations of the guarded oracle variant.
Oracle loads and one-column matvecs are charged separately; there are no matrix ROM reads. -/
noncomputable def cgOracleCount {P ι : Type} (tag : P) (o : ι) (N q : ℕ) : OpCount P ι :=
  Finsupp.single (.load tag o) q + Finsupp.single (.matvec tag o) q +
  Finsupp.single (.bin tag .mul) (N + 5 * q * N) +
  Finsupp.single (.bin tag .add) (N + 5 * q * N) +
  Finsupp.single (.un tag .conj) (N + 2 * q * N) +
  Finsupp.single (.bin tag .div) (2 * q) + Finsupp.single (.un tag .neg) (q + 1) +
  Finsupp.single (.lit tag) (N + 3 + 2 * q) +
  Finsupp.single (.cmp tag) (1 + 3 * q) + Finsupp.single (.copy tag) (2 * N + 2 * q + 2)

/-- Proposed oracle target: all real inputs execute with legal status and preserved input;
for SPD A, x/r/p agree with the total exact recurrence, padded after zero termination.
The statement fixes the program before quantifying matrices, dimensions and input data. -/
def MatrixFreeConjugateGradient : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (tag : P) (o : ι),
    MatrixFree (𝕜 := ℝ) tag (cgOracleProg.compiled tag o)
      (fun _ _ => True) (fun N _ => Fin N → ℝ)
      (fun N _ b => ![(Array.ofFn b).map some, Array.replicate N none,
        Array.replicate N none, Array.replicate N none, Array.replicate 1 none])
      (fun N q => cgOracleCount tag o N (q 0))
      (fun N _ p => if p = tag then 5 * N + 11 else 0)
      (fun _ q b A _ st =>
        ∃ status : ℝ, st.store.read tag 4 0 = some status ∧
          (status = 0 ∨ status = 1 ∨ status = -1) ∧
          Holds st.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
          (A.PosDef →
            Holds st.store tag 1 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).x i) ∧
            Holds st.store tag 2 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).r i) ∧
            Holds st.store tag 3 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).p i) ∧
            (status = 1 ↔ (cgState A b 0 (q 0)).r = 0) ∧ status ≠ -1))

end NLAlib
