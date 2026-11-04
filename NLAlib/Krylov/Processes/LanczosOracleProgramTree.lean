/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.MatrixKernels
public import NLAlib.Computation.Model

/-!
# Matrix-free Lanczos program and fixed tree

The oracle program approved on 2026-11-04 preserves the stored implementation's Paige order,
actual normalization and terminal zero continuation, with one oracle application per step.
The reserved matrix slot is empty. Oracle backend storage and arithmetic are outside the
matrix-free access model. Design: `docs/design/Lanczos-Matrix-Free-Program.md`.

## Main definitions

* `NLAlib.lanczosOracleProg`: the concrete matrix-free builder.
* `NLAlib.lanczosOracleProg.compiled`: its fixed first-order tree.

## Main results

* `NLAlib.lanczosOracleProg.toStmt_compiled`: instantiation to the actual builder.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

/-- The proposed matrix-free Lanczos program. Declared buffers are the unchanged
input, all basis columns through the final state, alpha, beta, input norm and final previous
vector. Work storage is scoped; slot 6 is reserved empty. Initialization uses actual `nrm2`
and `rscl`, and
zero continuation performs every requested step without dividing by a zero norm.
The oracle's hidden storage and implementation arithmetic are outside this access model.
Algorithm: lanczos -/
def lanczosOracleProg {P ι VB VI : Type} (tag : P) (o : ι) (N q : IExp VI)
    (b V alpha beta inputNorm prev : VB) : Builder P ι VB VI Unit := scope do
  let _matrixSlot ← alloc tag 0
  let work ← alloc tag N
  let scalars ← alloc tag 2
  ins (.lit tag ⟨scalars, 0⟩ 0)
  ins (.lit tag ⟨beta, 0⟩ 0)
  forRange N fun i => ins (.lit tag ⟨prev, .var i⟩ 0)
  nrm2 tag ⟨inputNorm, 0⟩ b 0 N
  ifThenElse tag .eq ⟨inputNorm, 0⟩ ⟨scalars, 0⟩
    (forRange N fun i => ins (.lit tag ⟨V, .var i⟩ 0)) (do
      copyv tag b 0 V 0 N
      rscl tag ⟨inputNorm, 0⟩ V 0 N)
  forRange q fun j => do
    stmt (.apply o tag work 0 V (N * .var j) 1)
    ins (.un tag .neg ⟨scalars, 1⟩ ⟨beta, .var j⟩)
    axpy tag ⟨scalars, 1⟩ prev 0 work 0 N
    dot tag ⟨alpha, .var j⟩ V (N * .var j) work 0 N
    ins (.un tag .neg ⟨scalars, 1⟩ ⟨alpha, .var j⟩)
    axpy tag ⟨scalars, 1⟩ V (N * .var j) work 0 N
    nrm2 tag ⟨beta, .var j + 1⟩ work 0 N
    copyv tag V (N * .var j) prev 0 N
    ifThenElse tag .eq ⟨beta, .var j + 1⟩ ⟨scalars, 0⟩
      (forRange N fun i => ins (.lit tag ⟨V, N * (.var j + 1) + .var i⟩ 0)) (do
        copyv tag work 0 V (N * (.var j + 1)) N
        rscl tag ⟨beta, .var j + 1⟩ V (N * (.var j + 1)) N)

/-- The proposed first-order tree, compiled once at symbolic dimension and step count.
It has six free buffers and uses one oracle call per Paige step. -/
def lanczosOracleProg.compiled {P ι : Type} (tag : P) (o : ι) : Prog P ι 1 6 :=
  (ProgFamily.compile fun _ _ N q h =>
    (lanczosOracleProg tag o N (q 0) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5)).run).get rfl

/-- The proposed tree instantiates to the concrete builder for every dimension and
requested step count. -/
theorem lanczosOracleProg.toStmt_compiled {P ι : Type} (tag : P) (o : ι) (N q : ℕ) :
    (lanczosOracleProg.compiled (ι := ι) tag o).toStmt N ![q] =
      (lanczosOracleProg tag o (.const N) (.const q) 0 1 2 3 4 5).run := rfl

end NLAlib
