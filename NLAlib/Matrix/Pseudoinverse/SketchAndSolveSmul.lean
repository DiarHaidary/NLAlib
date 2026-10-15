/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.LeastSquares

/-!
# Rescaling the sketch of sketch-and-solve

The sketch-and-solve solution does not change when the sketch is multiplied by a nonzero scalar,
so the normalisations $\lvert k \rvert^{-1/2}\mathbf{G}$ and
$\sqrt{\lvert n \rvert / \lvert k \rvert}\,\mathbf{Q}^{\mathsf{H}}$ of Gaussian and Haar sketches do
not matter for it. A side file that merges into `NLAlib/Matrix/Pseudoinverse/LeastSquares.lean`,
beside `NLAlib.sketchAndSolve` (`docs/design/LowRank-S6.md` §4, L4).

## Main results

* `NLAlib.sketchAndSolve_smul_sketch`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {k m n p : Type*} [Fintype k] [Fintype m] [Fintype n]

/-- **Rescaling the sketch does not change the sketch-and-solve solution**:
$\mathsf{sketchAndSolve}(\mathbf{A}, c\mathbf{S}, \mathbf{B}) =
\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B})$ for $c \ne 0$, for instance the
normalisations $\lvert k \rvert^{-1/2}\mathbf{G}$ and
$\sqrt{\lvert n \rvert / \lvert k \rvert}\,\mathbf{Q}^{\mathsf{H}}$ of Gaussian and Haar sketches;
a real scalar is the case `RCLike.real_smul_eq_coe_smul`. The fitted values are the case
`NLAlib.obliqueProjector_smul_right`. -/
theorem sketchAndSolve_smul_sketch (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (B : Matrix m p 𝕜)
    {c : 𝕜} (hc : c ≠ 0) : sketchAndSolve A (c • S) B = sketchAndSolve A S B := by
  simp only [sketchAndSolve, Matrix.smul_mul, pinv_smul, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, mul_inv_cancel₀ hc, one_smul]

end NLAlib
