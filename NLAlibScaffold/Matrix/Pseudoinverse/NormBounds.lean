/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.NormBounds

/-!
# Weighting does not shrink the pseudoinverse (stage S10)

Epperly and Webber's Lemma 5.8: for an invertible weight $\mathbf{R}$,
$\|\mathbf{M}^{+}\|_{\mathsf{F}} \le
\|(\mathbf{R}^{\mathsf{H}}\mathbf{M})^{+}\mathbf{R}^{\mathsf{H}}\|_{\mathsf{F}}$.
It is the deterministic step of their sketch-and-solve lower bound (Theorem 2.2): a sketch with
non-orthonormal columns $\mathbf{\Omega} = \mathbf{Q}\mathbf{R}$ is never better than its
orthonormal factor. It joins `NLAlib/Matrix/Pseudoinverse/NormBounds.lean`; its proof is deferred.
Design: `docs/design/LowRank-EstimatorLowerBounds.md` §3.3.

## Main results

* `NLAlib.frobNorm_pinv_le_frobNorm_pinv_conjTranspose_mul_mul_conjTranspose`
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l r : Type*} [Fintype l] [Fintype r] [DecidableEq l]

/-- **Weighting does not shrink the pseudoinverse** (Epperly and Webber's "weighting hurts"): for
$\mathbf{M} \in \Bbbk^{\ell \times r}$ and invertible $\mathbf{R} \in \Bbbk^{\ell \times \ell}$,
$$\|\mathbf{M}^{+}\|_{\mathsf{F}} \le
\|(\mathbf{R}^{\mathsf{H}}\mathbf{M})^{+}\mathbf{R}^{\mathsf{H}}\|_{\mathsf{F}}\,.$$
Any $\mathbf{M}$ (no rank hypothesis).
[EpperlyWebber2026, Lemma 5.8].
Proof: M, about 60 lines. EW's route: $\mathbf{P}_{\mathbf{M}} \preceq \mathbf{I}$; conjugate by
$\mathbf{R}\mathbf{R}^{\mathsf{H}}\mathbf{M}$ to get
$(\mathbf{M}^{\mathsf{H}}\mathbf{R}\mathbf{R}^{\mathsf{H}}\mathbf{M})
(\mathbf{M}^{\mathsf{H}}\mathbf{M})^{+}
(\mathbf{M}^{\mathsf{H}}\mathbf{R}\mathbf{R}^{\mathsf{H}}\mathbf{M}) \preceq
\mathbf{M}^{\mathsf{H}}(\mathbf{R}\mathbf{R}^{\mathsf{H}})^2\mathbf{M}$
(`Matrix.PosSemidef.conjTranspose_mul_mul_same`);
$\mathbf{M}^{\mathsf{H}}\mathbf{R}\mathbf{R}^{\mathsf{H}}\mathbf{M}$ has the range of
$\mathbf{M}^{\mathsf{H}}$
($\mathbf{R}$ invertible), so conjugating by its pseudoinverse gives
$(\mathbf{M}^{\mathsf{H}}\mathbf{M})^{+} \preceq (\mathbf{R}^{\mathsf{H}}\mathbf{M})^{+}
\mathbf{R}^{\mathsf{H}}\mathbf{R}\,((\mathbf{R}^{\mathsf{H}}\mathbf{M})^{+})^{\mathsf{H}}$; take
traces
(`frobNorm_pinv_sq_eq_re_trace_pinv`, trace monotone in the Loewner order). Alternatively: the
right side is $\min\|\mathbf{X}\|_{\mathsf{F}}$ over $\mathbf{X}\mathbf{M} =
\mathbf{P}_{\mathbf{M}^{\mathsf{H}}}$
of a weighted problem. -/
theorem frobNorm_pinv_le_frobNorm_pinv_conjTranspose_mul_mul_conjTranspose (M : Matrix l r 𝕜)
    {R : Matrix l l 𝕜} (hR : IsUnit R) :
    frobNorm (pinv M) ≤ frobNorm (pinv (Rᴴ * M) * Rᴴ) := by
  sorry

end NLAlib
