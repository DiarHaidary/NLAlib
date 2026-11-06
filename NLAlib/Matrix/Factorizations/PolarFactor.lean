/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.HermitianCalculus

/-!
# The orthonormal polar factor

`NLAlib.polarFactor V` $= \mathbf{V}(\mathbf{V}^{\mathsf{T}}\mathbf{V})^{-1/2}$, the orthonormal
factor of the polar decomposition of a real matrix of full column rank, the orthonormal matrix
nearest to $\mathbf{V}$ [Higham2008, Theorem 8.4]. For a nearly orthonormal $\mathbf{V}$ it is
within $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_{\mathsf F}$ of $\mathbf{V}$; the
backward model of Lanczos with full reorthogonalization is built on it. Design:
`docs/design/Krylov-LanczosReorth.md` §3.3.

## Main definitions

* `NLAlib.polarFactor`: $\mathbf{V}(\mathbf{V}^{\mathsf{T}}\mathbf{V})^{-1/2}$.
-/

@[expose] public section

namespace NLAlib

/-- **The orthonormal polar factor** $\mathbf{V}(\mathbf{V}^{\mathsf{T}}\mathbf{V})^{-1/2}$ of a
real matrix, through the continuous functional calculus of the Gram matrix (with
$0^{-1/2} = 0$, so the definition is total). -/
noncomputable def polarFactor {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (V : Matrix m n ℝ) : Matrix m n ℝ :=
  V * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (V.transpose * V)

end NLAlib
