/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Computation.Model

/-!
# Gram–Schmidt as a program: the builder and the registered tree

In-place rank-revealing modified Gram–Schmidt on the $k$ columns of an $N \times k$ buffer, as a
builder (`NLAlib.gramSchmidtProg`, with the sweep `NLAlib.orthAgainst`), and its registered tree
`NLAlib.gramSchmidtProg.compiled`: the builder compiled once, at symbolic sizes, into one
first-order program for all sizes. The target `NLAlib.MatrixFreeGramSchmidt` is about this tree;
its proof and the results about the builder are in
`NLAlib/Matrix/Factorizations/GramSchmidtProgram.lean`. The builder and the tree live upstream of
the target, so that the statement is fixed before the file that proves it. Design:
`docs/design/Computation.md` (D6, §5, F8).

## Main definitions

* `NLAlib.orthAgainst`: one modified Gram–Schmidt sweep of a vector.
* `NLAlib.gramSchmidtProg`: Gram–Schmidt as a program.
* `NLAlib.gramSchmidtProg.compiled`: its registered tree.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

variable {P ι VB VI : Type}

/-- One modified Gram–Schmidt sweep, $\mathbf{v} \leftarrow \mathbf{v} -
(\mathbf{q}_i^{\mathsf{H}}\mathbf{v})\mathbf{q}_i$ for the columns $\mathbf{q}_0, \dots,
\mathbf{q}_{k-1}$ of the $N$-row buffer $Q$ in turn, each coefficient computed from the partially
reduced vector; the cell $r$ holds the coefficients. -/
def orthAgainst (p : P) (N : IExp VI) (Q : VB) (k : IExp VI) (v : VB) (vo : IExp VI)
    (r : Cell VB VI) : Builder P ι VB VI Unit :=
  forRange k fun i => do
    dot p r Q (N * .var i) v vo N
    ins (.un p .neg r r)
    axpy p r Q (N * .var i) v vo N

/-- **Gram–Schmidt as a program**: in-place rank-revealing modified Gram–Schmidt on the $k$
columns of the $N$-row buffer $Y$. Column $j$ is swept against the earlier columns, its squared
norm is computed, and it is divided by its norm unless the squared norm is exactly zero. Two
scratch cells, freed at the end (`scope`). -/
def gramSchmidtProg (p : P) (N k : IExp VI) (Y : VB) : Builder P ι VB VI Unit := scope do
  let t ← alloc p 2
  forRange k fun j => do
    orthAgainst p N Y (.var j) Y (N * .var j) ⟨t, 0⟩
    dot p ⟨t, 1⟩ Y (N * .var j) Y (N * .var j) N
    ins (.lit p ⟨t, 0⟩ 0)
    ifThenElse p .eq ⟨t, 1⟩ ⟨t, 0⟩ (pure ()) do
      ins (.un p .sqrt ⟨t, 1⟩ ⟨t, 1⟩)
      rscl p ⟨t, 1⟩ Y (N * .var j) N

/-- **The registered tree of Gram–Schmidt**: `NLAlib.gramSchmidtProg` on the $N \times k$ buffer
held as declared buffer $0$, compiled once at symbolic sizes ($N$ and $n = (k)$) into one
first-order program for all sizes; compilation succeeds by evaluation. -/
def gramSchmidtProg.compiled (p : P) : Prog P ι 1 1 :=
  (ProgFamily.compile fun _ _ N n h => (gramSchmidtProg p N (n 0) (h 0)).run).get rfl

end NLAlib
