/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS

/-!
# Triangular solve as a BLAS kernel

`NLAlib.Computation.trsvLower` solves $\mathbf{T}\mathbf{x} = \mathbf{b}$ in place for a stored
lower triangular $n \times n$ matrix $\mathbf{T}$ by forward substitution in the inner-product
(row) order of [Higham2002, Lemma 8.4]: $x_i \leftarrow (b_i - \sum_{j<i} t_{ij}x_j)/t_{ii}$, the
sum subtracted term by term from $b_i$. The definition moves into
`NLAlib/Computation/BLAS.lean` (the only BLAS file that may build `named` nodes, rule E8);
its exact specification and error analysis are in `NLAlib/Computation/BLAS/Triangular.lean`.
Design: `docs/design/Computation-Rounding.md` (R5).

## Main definitions

* `NLAlib.Computation.trsvLower`.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι VB VI : Type}

/-- `trsv` (lower, no transpose, non-unit diagonal): $\mathbf{x} \leftarrow \mathbf{T}^{-1}
\mathbf{x}$ in place, for a stored lower triangular $n \times n$ matrix $\mathbf{T}$
(column-major from $\mathit{tOff}$; the entries above the diagonal are not read), row by row:
$x_i \leftarrow (x_i - \sum_{j<i} t_{ij}x_j)/t_{ii}$, subtracting in the order $j = 0, 1, \ldots$.
One scratch cell. -/
def trsvLower (p : P) (n : IExp VI) (T : VB) (tOff : IExp VI) (x : VB) (xo : IExp VI) :
    Builder P ι VB VI Unit :=
  named "trsvLower" [.idx n, .buf T, .idx tOff, .buf x, .idx xo] do
    let t ← alloc p 1
    forRange n fun i => do
      forRange (.var i) fun j => do
        ins (.bin p .mul ⟨t, 0⟩ ⟨T, tOff + .var i + n * .var j⟩ ⟨x, xo + .var j⟩)
        ins (.bin p .sub ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩ ⟨t, 0⟩)
      ins (.bin p .div ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩ ⟨T, tOff + .var i + n * .var i⟩)

end NLAlib.Computation
