/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.MatrixKernels
public import NLAlib.Computation.Model
public import NLAlib.Matrix.Computation.ClassicalGramSchmidt

/-!
# Lanczos with full reorthogonalization as a program: builders and trees

`NLAlib.lanczosReorthLoop` is the body shared by both access models: main's Lanczos program
(`NLAlib.lanczosProg`) in Paige's order with two insertions per step, the stored norm
$\nu_j = \|\mathbf{z}_j\|$ before orthogonalization and one call of an orthogonalization routine
against the columns $0, \dots, j$ of the basis. It is generic in the product and the
orthogonalization routine (the routine family of `docs/design/Krylov-LanczosReorth.md` §1.4);
the registered trees instantiate it with `gemv` on the matrix read from ROM
(`NLAlib.lanczosReorthProg`) or the oracle (`NLAlib.lanczosReorthOracleProg`), and with
`NLAlib.cgs2`. Buffers: `b` ($N$), `V` ($N(q+1)$), `alpha` ($q$), `beta` ($q+1$), `inputNorm`
($1$), `prev` ($N$), `nu` ($q$). Scoped: the matrix (stored tree) or an empty slot (oracle tree),
then `work` ($N$, handle $8$ at run time), `scalars` ($2$, handle $9$), `coef` ($q + 1$, handle
$10$). The targets are in `LanczosReorthTargets.lean` and `LanczosReorthOracleTargets.lean`.

## Main definitions

* `NLAlib.lanczosReorthLoop`: the generic builder.
* `NLAlib.lanczosReorthProg`, `NLAlib.lanczosReorthOracleProg`: the CGS2 instances.
* `NLAlib.lanczosReorthProg.compiled`, `NLAlib.lanczosReorthOracleProg.compiled`: their trees.

## Main results

* `NLAlib.lanczosReorthProg.toStmt_compiled`, `NLAlib.lanczosReorthOracleProg.toStmt_compiled`.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

/-- **Lanczos with full reorthogonalization, generic in the product and the orthogonalization
routine**: `mv work j` writes $\mathbf{H}\mathbf{v}_j$ (column $j$ of `V`) into `work`;
`orth work coef j` reduces `work` against the columns $0, \dots, j$ of `V` with coefficients in
`coef`. Initialization, zero test and zero continuation as in `NLAlib.lanczosProg`.
Algorithm: lanczos-reorth -/
def lanczosReorthLoop {P ι VB VI : Type} (tag : P) (N q : IExp VI)
    (b V alpha beta inputNorm prev nu : VB) (mv : VB → IExp VI → Builder P ι VB VI Unit)
    (orth : VB → VB → IExp VI → Builder P ι VB VI Unit) : Builder P ι VB VI Unit := scope do
  let work ← alloc tag N
  let scalars ← alloc tag 2
  let coef ← alloc tag (q + 1)
  ins (.lit tag ⟨scalars, 0⟩ 0)
  ins (.lit tag ⟨beta, 0⟩ 0)
  forRange N fun i => ins (.lit tag ⟨prev, .var i⟩ 0)
  nrm2 tag ⟨inputNorm, 0⟩ b 0 N
  ifThenElse tag .eq ⟨inputNorm, 0⟩ ⟨scalars, 0⟩
    (forRange N fun i => ins (.lit tag ⟨V, .var i⟩ 0)) (do
      copyv tag b 0 V 0 N
      rscl tag ⟨inputNorm, 0⟩ V 0 N)
  forRange q fun j => do
    mv work (.var j)
    ins (.un tag .neg ⟨scalars, 1⟩ ⟨beta, .var j⟩)
    axpy tag ⟨scalars, 1⟩ prev 0 work 0 N
    dot tag ⟨alpha, .var j⟩ V (N * .var j) work 0 N
    ins (.un tag .neg ⟨scalars, 1⟩ ⟨alpha, .var j⟩)
    axpy tag ⟨scalars, 1⟩ V (N * .var j) work 0 N
    nrm2 tag ⟨nu, .var j⟩ work 0 N
    orth work coef (.var j)
    nrm2 tag ⟨beta, .var j + 1⟩ work 0 N
    copyv tag V (N * .var j) prev 0 N
    ifThenElse tag .eq ⟨beta, .var j + 1⟩ ⟨scalars, 0⟩
      (forRange N fun i => ins (.lit tag ⟨V, N * (.var j + 1) + .var i⟩ 0)) (do
        copyv tag work 0 V (N * (.var j + 1)) N
        rscl tag ⟨beta, .var j + 1⟩ V (N * (.var j + 1)) N)

/-- **Lanczos with full reorthogonalization, stored matrix**: the matrix is read from ROM into a
scoped buffer, products by `gemv`, orthogonalization by `NLAlib.cgs2`.
Algorithm: lanczos-reorth -/
def lanczosReorthProg {P ι VB VI : Type} (tag : P) (N q : IExp VI)
    (b V alpha beta inputNorm prev nu : VB) : Builder P ι VB VI Unit := scope do
  let A ← alloc tag (N * N)
  forRange (N * N) fun i => stmt (.rom tag ⟨A, .var i⟩ (.var i))
  lanczosReorthLoop tag N q b V alpha beta inputNorm prev nu
    (fun work j => gemv tag N N A 0 V (N * j) work 0)
    (fun work coef j => cgs2 tag N (j + 1) V work 0 coef 0)

/-- **Lanczos with full reorthogonalization, matrix-free**: one oracle call per step (an empty
slot keeps the run-time handles of the stored tree), orthogonalization by `NLAlib.cgs2`.
Algorithm: lanczos-reorth -/
def lanczosReorthOracleProg {P ι VB VI : Type} (tag : P) (o : ι) (N q : IExp VI)
    (b V alpha beta inputNorm prev nu : VB) : Builder P ι VB VI Unit := scope do
  let _matrixSlot ← alloc tag 0
  lanczosReorthLoop tag N q b V alpha beta inputNorm prev nu
    (fun work j => stmt (.apply o tag work 0 V (N * j) 1))
    (fun work coef j => cgs2 tag N (j + 1) V work 0 coef 0)

/-- The first-order tree of the stored-matrix program, compiled once at symbolic sizes. -/
def lanczosReorthProg.compiled {P ι : Type} (tag : P) : Prog P ι 1 7 :=
  (ProgFamily.compile fun _ _ N q h =>
    (lanczosReorthProg tag N (q 0) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6)).run).get rfl

/-- The tree instantiates to the builder for every dimension and step count. -/
theorem lanczosReorthProg.toStmt_compiled {P ι : Type} (tag : P) (N q : ℕ) :
    (lanczosReorthProg.compiled (ι := ι) tag).toStmt N ![q] =
      (lanczosReorthProg tag (.const N) (.const q) 0 1 2 3 4 5 6).run := rfl

/-- The first-order tree of the matrix-free program, compiled once at symbolic sizes. -/
def lanczosReorthOracleProg.compiled {P ι : Type} (tag : P) (o : ι) : Prog P ι 1 7 :=
  (ProgFamily.compile fun _ _ N q h =>
    (lanczosReorthOracleProg tag o N (q 0) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6)).run).get rfl

/-- The tree instantiates to the builder for every dimension and step count. -/
theorem lanczosReorthOracleProg.toStmt_compiled {P ι : Type} (tag : P) (o : ι) (N q : ℕ) :
    (lanczosReorthOracleProg.compiled tag o).toStmt N ![q] =
      (lanczosReorthOracleProg tag o (.const N) (.const q) 0 1 2 3 4 5 6).run := rfl

end NLAlib
