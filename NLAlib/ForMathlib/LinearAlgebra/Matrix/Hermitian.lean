/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Star projections of matrices

A square matrix is a star projection (Mathlib's `IsStarProjection`, an idempotent self-adjoint
element) exactly when it is idempotent and Hermitian. Upstream candidate for
`Mathlib.LinearAlgebra.Matrix.Hermitian`.

## Main results

* `Matrix.isStarProjection_iff`: $\mathbf{P}$ is a star projection iff
  $\mathbf{P}\mathbf{P} = \mathbf{P}$ and $\mathbf{P}$ is Hermitian.
-/

@[expose] public section

namespace Matrix

/-- A matrix is a star projection exactly when it is idempotent and Hermitian. -/
theorem isStarProjection_iff {m α : Type*} [Fintype m] [Mul α] [AddCommMonoid α] [Star α]
    {P : Matrix m m α} : IsStarProjection P ↔ P * P = P ∧ P.IsHermitian :=
  _root_.isStarProjection_iff P

end Matrix
