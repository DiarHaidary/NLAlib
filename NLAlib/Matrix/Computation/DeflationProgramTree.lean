/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Computation.Model

/-!
# Randomized deflation as a program: the builder and the registered tree

Randomized deflation of [Shah2024, Algorithm 2], as the shallow `NLAlib.deflate` computes it on a
floating-point machine, written as a builder over memory buffers (`NLAlib.deflateProg`) and
compiled once at symbolic sizes into one first-order tree (`NLAlib.deflateProg.compiled`). The
complex Gaussian test matrix is drawn from the tape: two real Gaussian draws per entry, each
multiplied by the stored $\mathrm{fl}(\sqrt{\mathrm{fl}(1/2)})$, which the program computes. The
product and the QR factorization are calls of the black-box kernels `mm` and `qr`
(`NLAlib.Computation.Stmt.kcall`); the first $\min(r, n)$ columns of the $\mathbf{Q}$ factor are
copied to the output and the columns beyond the $n$-th are stored zeros, as in the shallow
definition. The rank $r$ is a size.

The refinement theorems (the run computes `NLAlib.deflate` on the machine of its semantics,
kernels and tape, and it always succeeds under the standard model) and the counts are in the
design note `docs/design/Computation-SignDeflatePrograms.md` (stage COMPDYN S1d).

## Main definitions

* `NLAlib.deflateProg`: randomized deflation as a program.
* `NLAlib.deflateProg.compiled`: its registered tree.
* `NLAlib.deflateCount`: its counts.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

variable {P ι VB VI : Type}

/-- **Randomized deflation as a program**: from the stored $n \times n$ complex matrix
$\mathbf{P}$ (interleaved pairs at `Pm` from `po`) it computes the stored
$s = \mathrm{fl}(\sqrt{\mathrm{fl}(1/2)})$, draws the complex test matrix
$\widetilde{\mathbf{G}}$ (entry $k$ in column-major order from the Gaussian draws $2k$ and
$2k + 1$, each times $s$ and rounded), forms $\mathbf{Y} = \mathrm{mm}(\mathbf{P},
\widetilde{\mathbf{G}})$ and $(\mathbf{Q}, \mathbf{R}) = \mathrm{qr}(\mathbf{Y})$ by kernel
calls, and writes the first $\min(r, n)$ columns of $\mathbf{Q}$ and $r - n$ (truncated) zero
columns at `Q` from `qo`, an $n \times r$ complex matrix. Scratch: two cells and four $n \times n$
complex matrices, freed at the end (`scope`). [Shah2024, Algorithm 2], as `NLAlib.deflate`.
Algorithm: deflate -/
def deflateProg (p : P) (mm qr : ι) (n r : IExp VI) (Pm : VB) (po : IExp VI) (Q : VB)
    (qo : IExp VI) : Builder P ι VB VI Unit := scope do
  let t ← alloc p 2
  let G ← alloc p (2 * (n * n))
  let Y ← alloc p (2 * (n * n))
  let Qf ← alloc p (2 * (n * n))
  let Rf ← alloc p (2 * (n * n))
  ins (.lit p ⟨t, 0⟩ 1)
  ins (.litIdx p ⟨t, 1⟩ 2)
  ins (.bin p .div ⟨t, 0⟩ ⟨t, 0⟩ ⟨t, 1⟩)
  ins (.un p .sqrt ⟨t, 0⟩ ⟨t, 0⟩)
  forRange (2 * (n * n)) fun w => do
    ins (.draw p .gaussian ⟨G, .var w⟩)
    ins (.bin p .mul ⟨G, .var w⟩ ⟨G, .var w⟩ ⟨t, 0⟩)
  stmt (.kcall mm p [n, n, n] [(Pm, po), (G, 0)] [(Y, 0)])
  stmt (.kcall qr p [n, n] [(Y, 0)] [(Qf, 0), (Rf, 0)])
  zcopy p n (r - (r - n)) Qf 0 Q qo
  zzero p n (r - n) Q (qo + 2 * (n * (r - (r - n))))

/-- **The registered tree of randomized deflation**: `NLAlib.deflateProg` with the stored matrix
in declared buffer $0$ and the output in declared buffer $1$, both from offset $0$, compiled once
at symbolic sizes ($n = N$ and the rank $r$) into one first-order program for all sizes;
compilation succeeds by evaluation. -/
def deflateProg.compiled (p : P) (mm qr : ι) : Prog P ι 1 2 :=
  (ProgFamily.compile fun _ _ N n h => (deflateProg p mm qr N (n 0) (h 0) 0 (h 1) 0).run).get rfl

/-- **The counts** of `NLAlib.deflateProg` at size $n$ and rank $r$: the literals $1$, $2$ and
$2n(r - n)$ zeros (truncated subtraction), one division and one square root, $2n^2$ Gaussian
draws and multiplications, one call of `mm` at $[n, n, n]$ and one of `qr` at $[n, n]$, and
$2n\min(r, n)$ copies. -/
noncomputable def deflateCount {ι : Type} (p : P) (mm qr : ι) (n r : ℕ) : OpCount P ι :=
  Finsupp.single (.lit p) (2 + 2 * (n * (r - n))) + Finsupp.single (.bin p .div) 1 +
    Finsupp.single (.un p .sqrt) 1 + Finsupp.single (.draw p .gaussian) (2 * (n * n)) +
    Finsupp.single (.bin p .mul) (2 * (n * n)) + Finsupp.single (.kcall p mm [n, n, n]) 1 +
    Finsupp.single (.kcall p qr [n, n]) 1 + Finsupp.single (.copy p) (2 * (n * min r n))

end NLAlib
