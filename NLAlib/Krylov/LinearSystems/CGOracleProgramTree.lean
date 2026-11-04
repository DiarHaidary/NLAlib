/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.MatrixKernels
public import NLAlib.Computation.Model

/-!
# The fixed matrix-free conjugate gradient tree

The cached-residual CG program uses one oracle application per active iteration. Its guarded
termination and vector-update order match the stored-entry implementation.

## Main definitions

* `NLAlib.cgOracleProg`, `NLAlib.cgOracleProg.compiled`: the oracle builder and fixed tree.

## Main results

* `NLAlib.cgOracleProg.toStmt_compiled`: its exact builder instantiation.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

/-- The oracle CG variant from zero, with cached squared residuals and guarded divisions.
Its matrix access is a one-column oracle application; there is no stored matrix or ROM read.
The empty scratch slot keeps the canonical vector/scalar buffer addresses.
Algorithm: cg -/
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


/-- The matrix-free tree, compiled once at symbolic dimension and step count. -/
def cgOracleProg.compiled {P ι : Type} (tag : P) (o : ι) : Prog P ι 1 5 :=
  (ProgFamily.compile fun _ _ N q h =>
    (cgOracleProg tag o N (q 0) (h 0) (h 1) (h 2) (h 3) (h 4)).run).get rfl

/-- The symbolic tree instantiates to the displayed oracle builder. -/
theorem cgOracleProg.toStmt_compiled {P ι : Type} (tag : P) (o : ι) (N q : ℕ) :
    (cgOracleProg.compiled tag o).toStmt N ![q] =
      (cgOracleProg tag o (.const N) (.const q) 0 1 2 3 4).run := rfl


end NLAlib
