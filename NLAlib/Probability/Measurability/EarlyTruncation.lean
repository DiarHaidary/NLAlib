/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Measurability.Matrix

/-!
# Measurability of the early-truncated outputs

The early-truncated randomized SVD and early-truncated generalized Nyström are Borel measurable
functions of their test matrices: they are built from the truncated SVD of the sketch
(`NLAlib.measurable_truncatedSVD`), the range projector and the pseudoinverse. A side file that
merges into `NLAlib/Probability/Measurability/Matrix.lean`, beside `NLAlib.measurable_rsvd` and
`NLAlib.measurable_generalizedNystrom` (`docs/design/LowRank-S6.md` §4, L2 and L3).

## Main results

* `NLAlib.measurable_earlyTruncatedRSVD`.
* `NLAlib.measurable_earlyTruncatedGeneralizedNystrom`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n l p : Type*} [Fintype m] [Fintype n] [Fintype l]
  [Fintype p]

/-- The early-truncated randomized SVD
$\mathbf{\Omega} \mapsto \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$ is a
measurable function of the test matrix. -/
theorem measurable_earlyTruncatedRSVD (A : Matrix m n 𝕜) (k : ℕ) :
    Measurable fun Ω : Matrix n l 𝕜 => earlyTruncatedRSVD A Ω k :=
  (measurable_rangeProjector.comp
    ((measurable_const.matrix_mul measurable_id).truncatedSVD k)).matrix_mul measurable_const

/-- Early-truncated generalized Nyström
$(\mathbf{\Omega}, \mathbf{\Psi}) \mapsto \mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi}, k)$ is a measurable function of the two test matrices. -/
theorem measurable_earlyTruncatedGeneralizedNystrom (A : Matrix m n 𝕜) (k : ℕ) :
    Measurable fun ΩΨ : Matrix n l 𝕜 × Matrix m p 𝕜 =>
      earlyTruncatedGeneralizedNystrom A ΩΨ.1 ΩΨ.2 k := by
  have hΨ : Measurable fun ΩΨ : Matrix n l 𝕜 × Matrix m p 𝕜 => ΩΨ.2ᴴ :=
    (continuous_id.matrix_conjTranspose.measurable).comp measurable_snd
  have hT : Measurable fun ΩΨ : Matrix n l 𝕜 × Matrix m p 𝕜 => truncatedSVD (A * ΩΨ.1) k :=
    (measurable_const.matrix_mul measurable_fst).truncatedSVD k
  simp only [earlyTruncatedGeneralizedNystrom, obliqueProjector]
  exact ((hT.matrix_mul (measurable_pinv.comp (hΨ.matrix_mul hT))).matrix_mul hΨ).matrix_mul
    measurable_const

end NLAlib
