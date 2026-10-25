/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.GirardHutchinson

/-!
# The Girard–Hutchinson estimator: the addition of stage SLQ

Statements for `NLAlib/Estimation/Trace/GirardHutchinson.lean` whose proofs are deferred
(`docs/design/Estimation-SLQ.md`, §3.1, G1): the estimate is linear in the matrix, the step that
turns a tail for $\mathbf{1}_S(\mathbf{A})$ into one for $\mathbf{1}_S(\mathbf{A})/\lvert n\rvert$.

## Main results

* `NLAlib.girardHutchinson_smul`: homogeneity in the matrix.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [Fintype m]

/-- The Girard–Hutchinson estimate is homogeneous in the matrix: for every scalar $c$, square
$\mathbf{B}$ and test matrix $\mathbf{\Omega}$,
$\mathsf{girardHutchinson}(c\mathbf{B}, \mathbf{\Omega}) =
c\,\mathsf{girardHutchinson}(\mathbf{B}, \mathbf{\Omega})$.
Proof: S, about 5 lines. Unfold `girardHutchinson`; `Matrix.mul_smul`, `Matrix.smul_mul`,
`Matrix.trace_smul`, `smul_eq_mul`, `mul_div_assoc`. -/
theorem girardHutchinson_smul (c : 𝕜) (B : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) :
    girardHutchinson (c • B) Ω = c * girardHutchinson B Ω := by
  unfold girardHutchinson
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    mul_div_assoc]

end NLAlib
