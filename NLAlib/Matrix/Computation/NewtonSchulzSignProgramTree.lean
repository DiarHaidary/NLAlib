/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Computation.Model

/-!
# The Newton–Schulz sign algorithm as a program: the builder and the registered tree

The Newton–Schulz sign algorithm of [Shah2024, Algorithm 1], as the shallow
`NLAlib.newtonSchulzSign` computes it on a floating-point machine, written as a builder over
memory buffers (`NLAlib.newtonSchulzSignProg`) and compiled once at symbolic sizes into one
first-order tree (`NLAlib.newtonSchulzSignProg.compiled`). Every operation on data is an
instruction of the model or a call of the black-box matrix-multiplication kernel `mm`
(`NLAlib.Computation.Stmt.kcall`): complex matrices are interleaved pairs of real words, the
entrywise steps are the complex kernels of `NLAlib/Computation/BLAS.lean`, the stopping test is a
loop of counted comparisons into a flag cell, and the iteration is a `whileFuel` loop on that
flag with fuel $F + 1$ for the step limit $F$ (a size). The stored tolerance $\varepsilon$ and
scale $b$ are declared inputs; the threshold $\mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$ and the
constants $3$, $4$, $1$ are computed by the program as the machine computes them. The product
$\mathrm{mm}(\mathbf{A}_k, \mathbf{A}_k)$ of the test is reused by the next step, which the
shallow definition computes twice: the kernel is a function, so the values agree.

The refinement theorems (the run computes `NLAlib.newtonSchulzSign` on the machine of its
semantics and kernel, and it succeeds when the test passes within the fuel) and the counts are in
the design note `docs/design/Computation-SignDeflatePrograms.md` (stage COMPDYN S1d).

## Main definitions

* `NLAlib.newtonSchulzTestBlock`: the product, the shift by the identity and the test.
* `NLAlib.newtonSchulzStepBlock`: the rounded step.
* `NLAlib.newtonSchulzSignProg`: the Newton–Schulz sign algorithm as a program.
* `NLAlib.newtonSchulzSignProg.compiled`: its registered tree.
* `NLAlib.newtonSchulzSignCount`: an upper bound on its counts.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

variable {P ι VB VI : Type}

/-- **The Newton–Schulz stopping test as a block**: $\mathbf{W} \leftarrow
\mathrm{mm}(\mathbf{X}, \mathbf{X})$ (a kernel call), $\mathbf{V} \leftarrow \mathbf{W} -
\mathbf{I}$ stored Hermitian (`NLAlib.Computation.zhermShift` by the stored one in `one`), and
`flag` the result of the max-modulus test of $\mathbf{V}$ at the thresholds `lo` $= -\eta$ and
`hi` $= \eta$ (`NLAlib.Computation.zboxTest`): $0$ if it passes, $1$ if not. All matrices
$n \times n$ complex, packed from offset $0$ of their buffers except $\mathbf{X}$. -/
def newtonSchulzTestBlock (p : P) (mm : ι) (n : IExp VI) (X : VB) (xo : IExp VI) (W V : VB)
    (one lo hi flag : Cell VB VI) : Builder P ι VB VI Unit := do
  stmt (.kcall mm p [n, n, n] [(X, xo), (X, xo)] [(W, 0)])
  zhermShift p n W 0 one V 0
  zboxTest p n n V 0 lo hi flag

/-- **The rounded Newton–Schulz step as a block**, from $\mathbf{W} = \mathrm{mm}(\mathbf{X},
\mathbf{X})$ (left by the test): $\mathbf{V} \leftarrow -(\mathbf{W} - \mathrm{fl}(3)\mathbf{I})$
stored Hermitian (`NLAlib.Computation.zhermShift` by the literal $3$ in the cell `c`, then
`NLAlib.Computation.zneg` in place), $\mathbf{W} \leftarrow \mathrm{mm}(\mathbf{X}, \mathbf{V})$
(a kernel call), and $\mathbf{X} \leftarrow (\mathbf{W} + \mathbf{W}^{\mathsf{H}})/\mathrm{fl}(4)$
stored Hermitian (`NLAlib.Computation.zhermAvg` by the literal $4$ in `c`). All matrices
$n \times n$ complex, packed from offset $0$ of their buffers except $\mathbf{X}$. -/
def newtonSchulzStepBlock (p : P) (mm : ι) (n : IExp VI) (X : VB) (xo : IExp VI) (W V : VB)
    (c : Cell VB VI) : Builder P ι VB VI Unit := do
  ins (.litIdx p c 3)
  zhermShift p n W 0 c V 0
  zneg p n n V 0 V 0
  stmt (.kcall mm p [n, n, n] [(X, xo), (V, 0)] [(W, 0)])
  ins (.litIdx p c 4)
  zhermAvg p n W 0 c X xo

/-- **The Newton–Schulz sign algorithm as a program**: from the stored Hermitian $n \times n$
matrix $\mathbf{A}$ (interleaved pairs at `A` from `ao`) and the stored $\varepsilon$, $b$ (cells
`po`, `po + 1` of `par`), it writes $\mathbf{X}_0 = \mathbf{A}/b$ stored Hermitian at `X` from
`xo`, computes $\eta = \mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$, tests $\mathbf{X}_0$
(`NLAlib.newtonSchulzTestBlock`), and while the test fails, at most $F + 1$ times, takes the
rounded step $\mathbf{X} \leftarrow (\mathbf{Y} + \mathbf{Y}^{\mathsf{H}})/\mathrm{fl}(4)$,
$\mathbf{Y} = \mathrm{mm}(\mathbf{X}, -(\mathrm{mm}(\mathbf{X}, \mathbf{X}) - \mathrm{fl}(3)
\mathbf{I}))$, and tests again. It fails if the test still fails after $F$ steps. Scratch: six
cells and two $n \times n$ complex matrices, freed at the end (`scope`). [Shah2024, Algorithm 1],
as `NLAlib.newtonSchulzSign` with step limit $F$.
Algorithm: newton-schulz-sign -/
def newtonSchulzSignProg (p : P) (mm : ι) (n F : IExp VI) (A : VB) (ao : IExp VI) (par : VB)
    (po : IExp VI) (X : VB) (xo : IExp VI) : Builder P ι VB VI Unit := scope do
  -- t: 0 the threshold η, 1 the flag, 2 a literal, 3 the stored one, 4 the negated threshold
  let t ← alloc p 5
  let W ← alloc p (2 * (n * n))
  let V ← alloc p (2 * (n * n))
  ins (.litIdx p ⟨t, 2⟩ (4 * n))
  ins (.bin p .div ⟨t, 0⟩ ⟨par, po⟩ ⟨t, 2⟩)
  ins (.un p .neg ⟨t, 4⟩ ⟨t, 0⟩)
  ins (.lit p ⟨t, 3⟩ 1)
  zhermScale p n A ao ⟨par, po + 1⟩ X xo
  newtonSchulzTestBlock p mm n X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
  stmt (.whileFuel (F + 1) p .eq ⟨t, 1⟩ ⟨t, 3⟩ (Builder.run do
    newtonSchulzStepBlock p mm n X xo W V ⟨t, 2⟩
    newtonSchulzTestBlock p mm n X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩))

/-- **The registered tree of the Newton–Schulz sign algorithm**: `NLAlib.newtonSchulzSignProg`
with the stored matrix in declared buffer $0$, the stored $\varepsilon$ and $b$ in cells $0$ and
$1$ of declared buffer $1$ and the output in declared buffer $2$, all from offset $0$, compiled
once at symbolic sizes ($n = N$ and the step limit $F$) into one first-order program for all
sizes; compilation succeeds by evaluation. -/
def newtonSchulzSignProg.compiled (p : P) (mm : ι) : Prog P ι 1 3 :=
  (ProgFamily.compile fun _ _ N n h =>
    (newtonSchulzSignProg p mm N (n 0) (h 0) 0 (h 1) 0 (h 2) 0).run).get rfl

/-- **An upper bound on the counts** of `NLAlib.newtonSchulzSignProg` at size $n$ and step
limit $F$: $F + 2$ times, two calls of `mm` at the dimensions $[n, n, n]$ and $4n^2 + 4n + 4$
operations of each kind used (additions, subtractions, divisions, negations, copies, literals,
comparisons). One test and the set-up, and at most $F + 1$ steps with their tests and loop
comparisons, each fit in one such term. -/
noncomputable def newtonSchulzSignCount {ι : Type} (p : P) (mm : ι) (n F : ℕ) : OpCount P ι :=
  (F + 2) • (Finsupp.single (.kcall p mm [n, n, n]) 2 +
    Finsupp.single (.bin p .add) (4 * n ^ 2 + 4 * n + 4) +
    Finsupp.single (.bin p .sub) (4 * n ^ 2 + 4 * n + 4) +
    Finsupp.single (.bin p .div) (4 * n ^ 2 + 4 * n + 4) +
    Finsupp.single (.un p .neg) (4 * n ^ 2 + 4 * n + 4) +
    Finsupp.single (.copy p) (4 * n ^ 2 + 4 * n + 4) +
    Finsupp.single (.lit p) (4 * n ^ 2 + 4 * n + 4) +
    Finsupp.single (.cmp p) (4 * n ^ 2 + 4 * n + 4))

end NLAlib
