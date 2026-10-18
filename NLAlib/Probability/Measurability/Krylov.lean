/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.MeasureTheory.Matrix
public import NLAlib.Krylov.Basic.BlockSpace

/-!
# Measurability of Krylov quantities

For a random starting block, the block Krylov matrix is a measurable function of the block: it is
linear in it. With `NLAlib.measurable_rsvd` this makes randomized block Krylov iteration, the
randomized SVD at the test matrix
$\mathbf{K}_q(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{\Omega})$, a measurable function of
$\mathbf{\Omega}$. Matrices carry the product σ-algebra `Matrix.instMeasurableSpace`.

## Main results

* `NLAlib.measurable_blockKrylovMatrix`: $\mathbf{B} \mapsto \mathbf{K}_q(\mathbf{A}, \mathbf{B})$
  is measurable.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p : Type*} [Fintype n] [DecidableEq n]

-- Stage B0

/-- The block Krylov matrix $\mathbf{B} \mapsto \mathbf{K}_q(\mathbf{A}, \mathbf{B})$ is a
measurable function of the starting block. -/
theorem measurable_blockKrylovMatrix (A : Matrix n n 𝕜) (q : ℕ) :
    Measurable fun B : Matrix n p 𝕜 => blockKrylovMatrix A B q := by
  sorry

end NLAlib
