/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.MatrixKernels
public import NLAlib.Computation.Model

/-!
# CG as a program: the builder and registered tree

The fixed concrete stored-entry implementation approved on 2026-11-04. Its builder uses
scoped buffers and the existing scalar-loop BLAS kernels; its first-order tree is compiled
once at symbolic sizes. `StoredEntriesConjugateGradient` fixes its exact output, count and
memory guarantees.
The recurrence and program remain distinct objects, connected by the target proof.
Design: `docs/design/Krylov-Implementation-Integration.md`.

## Main definitions

* `NLAlib.cgProg`: the concrete builder.
* `NLAlib.cgProg.compiled`: its registered symbolic tree.

## Main results

* `NLAlib.cgProg.toStmt_compiled`: the tree instantiates to the actual builder.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

/-- The canonical CG program from zero. Declared buffers are input right-hand side,
output iterate, residual, direction, and one status cell. Matrix entries are read column-major
from ROM; all scratch is scoped. A zero cached squared residual sets positive status, while a
nonpositive curvature sets negative status. Zero status after the requested loop means budget
exhausted. Each subsequent loop iteration skips the body after either stop.
Rounded execution under the relative-error scalar contract is proved by
`NLAlib.CGImplementation.exec_rounded_compiled`; the returned iterate's backward model and
physical energy comparison are in `NLAlib.CGImplementation.exec_rounded_compiled_backward`.
Algorithm: cg -/
def cgProg {P ι VB VI : Type} (tag : P) (N q : IExp VI)
    (b x r p status : VB) : Builder P ι VB VI Unit := scope do
  let A ← alloc tag (N * N)
  let s ← alloc tag N
  let scalars ← alloc tag 9
  forRange (N * N) fun i => stmt (.rom tag ⟨A, .var i⟩ (.var i))
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
      gemv tag N N A 0 p 0 s 0
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

/-- The registered CG tree compiled once at symbolic dimension and step budget. Its only five
free buffers are the declared input, three output vectors and status. The tree is named by the
approved exact stored-entry target. -/
def cgProg.compiled {P ι : Type} (tag : P) : Prog P ι 1 5 :=
  (ProgFamily.compile fun _ _ N q h =>
    (cgProg tag N (q 0) (h 0) (h 1) (h 2) (h 3) (h 4)).run).get rfl

/-- The one compiled tree instantiates to the concrete builder at every dimension and
requested step budget; the program has no access to their values before instantiation. -/
theorem cgProg.toStmt_compiled {P ι : Type} (tag : P) (N q : ℕ) :
    (cgProg.compiled (ι := ι) tag).toStmt N ![q] =
      (cgProg tag (.const N) (.const q) 0 1 2 3 4).run := by
  rfl

end NLAlib
