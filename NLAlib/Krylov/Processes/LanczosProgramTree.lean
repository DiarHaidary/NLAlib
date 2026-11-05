/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.MatrixKernels
public import NLAlib.Computation.Model

/-!
# Lanczos as a program: the builder and registered tree

The fixed concrete stored-entry implementation approved on 2026-11-04. Its builder uses
scoped buffers and the existing scalar-loop BLAS kernels; its first-order tree is compiled
once at symbolic sizes. `StoredEntriesLanczos` fixes its exact output, count and memory guarantees.
The recurrence and program remain distinct objects, connected by the target proof.
Design: `docs/design/Krylov-Implementation-Integration.md`.

## Main definitions

* `NLAlib.lanczosProg`: the concrete builder.
* `NLAlib.lanczosProg.compiled`: its registered symbolic tree.

## Main results

* `NLAlib.lanczosProg.toStmt_compiled`: the tree instantiates to the actual builder.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

/-- The concrete stored-matrix Lanczos program. Declared buffers are the unchanged
input, all basis columns through the final state, alpha, beta, input norm and final previous
vector. Matrix and work storage are scoped. Initialization uses actual `nrm2` and `rscl`, and
zero continuation performs every requested step without dividing by a zero norm.
Rounded execution of this same tree is proved by
`NLAlib.LanczosImplementation.exec_rounded_compiled`; its active-prefix backward model and
input-direction certificate are in `NLAlib.LanczosImplementation.exec_rounded_compiled_backward`.
Algorithm: lanczos -/
def lanczosProg {P ι VB VI : Type} (tag : P) (N q : IExp VI)
    (b V alpha beta inputNorm prev : VB) : Builder P ι VB VI Unit := scope do
  let A ← alloc tag (N * N)
  let work ← alloc tag N
  let scalars ← alloc tag 2
  forRange (N * N) fun i => stmt (.rom tag ⟨A, .var i⟩ (.var i))
  ins (.lit tag ⟨scalars, 0⟩ 0)
  ins (.lit tag ⟨beta, 0⟩ 0)
  forRange N fun i => ins (.lit tag ⟨prev, .var i⟩ 0)
  nrm2 tag ⟨inputNorm, 0⟩ b 0 N
  ifThenElse tag .eq ⟨inputNorm, 0⟩ ⟨scalars, 0⟩
    (forRange N fun i => ins (.lit tag ⟨V, .var i⟩ 0)) (do
      copyv tag b 0 V 0 N
      rscl tag ⟨inputNorm, 0⟩ V 0 N)
  forRange q fun j => do
    gemv tag N N A 0 V (N * .var j) work 0
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

/-- The registered first-order tree, compiled once at symbolic dimension and step count.
It has six free buffers and uses no matrix-vector oracle or random tape. -/
def lanczosProg.compiled {P ι : Type} (tag : P) : Prog P ι 1 6 :=
  (ProgFamily.compile fun _ _ N q h =>
    (lanczosProg tag N (q 0) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5)).run).get rfl

/-- The registered tree instantiates to the concrete builder for every dimension and
requested step count. -/
theorem lanczosProg.toStmt_compiled {P ι : Type} (tag : P) (N q : ℕ) :
    (lanczosProg.compiled (ι := ι) tag).toStmt N ![q] =
      (lanczosProg tag (.const N) (.const q) 0 1 2 3 4 5).run := rfl

end NLAlib
