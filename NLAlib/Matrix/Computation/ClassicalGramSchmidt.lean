/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Classical Gram–Schmidt with reorthogonalization as a program

`NLAlib.cgsPass` is one classical Gram–Schmidt pass of a vector $\mathbf{w}$ against the first
$j$ columns of an $N$-row buffer $\mathbf{V}$: $\mathbf{h} \leftarrow \mathbf{V}^{\mathsf{T}}
\mathbf{w}$ ($j$ dots), $\mathbf{s} \leftarrow \mathbf{V}\mathbf{h}$ (`gemv`),
$\mathbf{w} \leftarrow \mathbf{w} - \mathbf{s}$ (`axpy` with the literal $-1$, which is rounded
like any literal). `NLAlib.cgs2` is two passes with the coefficients summed: CGS2, "twice is
enough" [DanielGraggKaufmanStewart1976], [GiraudLangouRozloznikVandenEshof2005]. Its rounding
error coefficient is
`NLAlib.cgsPassBound`, <!-- value cgsPassBound N j u \eta_0 -->$2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$.
Design: `docs/design/Krylov-LanczosReorth.md` §2.2.

## Main definitions

* `NLAlib.cgsPass`, `NLAlib.cgs2`: the builders.
* `NLAlib.cgsPassBound`: the error coefficient of one rounded pass.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

variable {P ι VB VI : Type}

/-- **One classical Gram–Schmidt pass** of `w[wo..wo+N)` against the first $j$ columns of the
$N$-row buffer `V` (column-major from offset $0$): coefficients into `h[ho..ho+j)`, then
$\mathbf{w} \leftarrow \mathbf{w} - \mathbf{V}\mathbf{h}$. Scratch: $N + 1$ cells.
Algorithm: gram-schmidt -/
def cgsPass (p : P) (N j : IExp VI) (V w : VB) (wo : IExp VI) (h : VB) (ho : IExp VI) :
    Builder P ι VB VI Unit := scope do
  let s ← alloc p N
  let t ← alloc p 1
  forRange j fun i => dot p ⟨h, ho + .var i⟩ V (N * .var i) w wo N
  gemv p N j V 0 h ho s 0
  ins (.lit p ⟨t, 0⟩ (-1))
  axpy p ⟨t, 0⟩ s 0 w wo N

/-- **Classical Gram–Schmidt with one reorthogonalization (CGS2)**: two passes of
`NLAlib.cgsPass`, the second one's coefficients added to the first one's. Scratch: $j$ cells
besides those of the passes.
Algorithm: gram-schmidt -/
def cgs2 (p : P) (N j : IExp VI) (V w : VB) (wo : IExp VI) (h : VB) (ho : IExp VI) :
    Builder P ι VB VI Unit := scope do
  let h₂ ← alloc p j
  cgsPass p N j V w wo h ho
  cgsPass p N j V w wo h₂ 0
  forRange j fun i => ins (.bin p .add ⟨h, ho + .var i⟩ ⟨h, ho + .var i⟩ ⟨h₂, .var i⟩)

/-- **The error coefficient of one rounded classical Gram–Schmidt pass** against $j$ columns of
length $N$ with $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0$:
the value <!-- value cgsPassBound N j u \eta_0 -->$c_1 = 2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$,
a safe multiple of the first-order count
$(1+\eta_0)\sqrt{j}\,(\gamma_N + \gamma_j) + 4u$. -/
noncomputable irreducible_def cgsPassBound (N j : ℕ) (u η₀ : ℝ) : ℝ :=
  2 * (1 + η₀) * Real.sqrt ((j : ℝ) + 1) * ((N + j + 2 : ℕ) : ℝ) * u

end NLAlib
