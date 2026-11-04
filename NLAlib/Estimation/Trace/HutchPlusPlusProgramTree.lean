/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Dense
public import NLAlib.Computation.Sparse
public import NLAlib.Matrix.Factorizations.GramSchmidtProgramTree

/-!
# Hutch++ as a program: the builder and the registered trees

Hutch++ as a builder over memory buffers (`NLAlib.hutchppProg`), and the trees the targets of
`NLAlib/Estimation/Trace/HutchPlusPlusTargets.lean` are about, each compiled once at symbolic
sizes into one first-order program for all sizes: the matrix-free tree
`NLAlib.hutchppProg.compiled`, the dense tree `NLAlib.hutchppProg.compiledDense` (the oracle calls
served by `NLAlib.Computation.denseImpl`) and the sparse tree `NLAlib.hutchppProg.compiledCoo`
(served by `NLAlib.Computation.cooImpl`, one tree per public pattern). The results about the
builder and the proofs of the targets are in `NLAlib/Estimation/Trace/HutchPlusPlusProgram.lean`.
The builder and the trees live upstream of the targets, so that the statements are fixed before
the file that proves them. Design: `docs/design/Computation.md` (§5, F8).

## Main definitions

* `NLAlib.hutchppProg`: Hutch++ as a program.
* `NLAlib.hutchppProg.compiled`, `NLAlib.hutchppProg.compiledDense`: registered trees.
* `NLAlib.hutchppProg.compiledCoo`: the sparse tree, one per pattern.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

variable {P ι VB VI : Type}

/-- **Hutch++ as a program.** It draws an $N \times k$ sketch $\mathbf{S}$ and $N \times \ell$
probes $\mathbf{G}$ from the tape of `d`, forms $\mathbf{Y} = \mathbf{A}\mathbf{S}$ (load 1),
orthonormalises $\mathbf{Y}$ in place by rank-revealing modified Gram–Schmidt into
$\mathbf{Q}$, projects the probes in place,
$\mathbf{G}' = (\mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{G}$, forms
$\mathbf{A}[\mathbf{Q}\ \mathbf{G}']$ (load 2, batched), and writes
$\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}) +
\operatorname{tr}(\mathbf{G}'^{\mathsf{H}}\mathbf{A}\mathbf{G}')/\ell$ into `out`.
[MeyerMuscoMuscoWoodruff2021, Algorithm 1].
Algorithm: hutchpp -/
def hutchppProg (p : P) (o : ι) (d : Dist) (N k ℓ : IExp VI) (out : Cell VB VI) :
    Builder P ι VB VI Unit := do
  let B ← alloc p (N * (k + ℓ))
  scope do
    let S ← alloc p (N * k)
    forRange (N * k) fun i => ins (.draw p d ⟨S, .var i⟩)
    stmt (.apply o p B 0 S 0 k)
  forRange (N * ℓ) fun i => ins (.draw p d ⟨B, N * k + .var i⟩)
  gramSchmidtProg p N k B
  let t ← alloc p 2
  forRange ℓ fun j => orthAgainst p N B k B (N * (k + .var j)) ⟨t, 0⟩
  let C ← alloc p (N * (k + ℓ))
  stmt (.apply o p C 0 B 0 (k + ℓ))
  ins (.lit p out 0)
  forRange k fun j => do
    dot p ⟨t, 0⟩ B (N * .var j) C (N * .var j) N
    ins (.bin p .add out out ⟨t, 0⟩)
  ins (.lit p ⟨t, 1⟩ 0)
  forRange ℓ fun j => do
    dot p ⟨t, 0⟩ B (N * (k + .var j)) C (N * (k + .var j)) N
    ins (.bin p .add ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩)
  ins (.litIdx p ⟨t, 0⟩ ℓ)
  ins (.bin p .div ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩)
  ins (.bin p .add out out ⟨t, 1⟩)

/-- **The registered tree of Hutch++**: `NLAlib.hutchppProg` with its output in cell $0$ of
declared buffer $0$, compiled once at symbolic sizes ($N$ and $n = (k, \ell)$) into one
first-order program for all sizes; compilation succeeds by evaluation. -/
def hutchppProg.compiled (p : P) (o : ι) (d : Dist) : Prog P ι 2 1 :=
  (ProgFamily.compile fun _ _ N n h => (hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run).get rfl

/-- **The registered tree of dense Hutch++**: `NLAlib.hutchppProg` with its oracle calls replaced
by `NLAlib.Computation.denseImpl` (the $N^2$ entries read from the read-only data), compiled once
at symbolic sizes; compilation succeeds by evaluation. -/
def hutchppProg.compiledDense (p : P) (o : ι) (d : Dist) : Prog P ι 2 1 :=
  (ProgFamily.compile fun _ _ N n h =>
    ((hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run).substOracle (denseImpl N)).get rfl

/-- **The tree of sparse Hutch++** for a public COO pattern: `NLAlib.hutchppProg` with its oracle
calls replaced by `NLAlib.Computation.cooImpl`, which unrolls the pattern, compiled once at
symbolic sizes. The tree is a function of the pattern. Compilation succeeds for every pattern
(`NLAlib.hutchppProg.exists_compile_coo`), so the default `skip` is never taken. -/
def hutchppProg.compiledCoo (p : P) (o : ι) (d : Dist) (pattern : List (ℕ × ℕ)) :
    Prog P ι 2 1 :=
  (ProgFamily.compile fun _ _ N n h =>
    ((hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run).substOracle (cooImpl N pattern)).getD .skip

end NLAlib
