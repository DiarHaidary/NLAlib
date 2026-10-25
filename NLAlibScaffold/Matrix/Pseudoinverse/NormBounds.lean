/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Projector
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

omit [DecidableEq l] in
private theorem pinv_mul_self_eq (A : Matrix l r 𝕜) : pinv A * A = Aᴴ * (pinv A)ᴴ := by
  rw [pinv_mul, ← pinv_conjTranspose, mul_pinv]

omit [DecidableEq l] in
private theorem pinv_mul_self_conjTranspose (A : Matrix l r 𝕜) :
    (pinv A * A)ᴴ = pinv A * A := by
  rw [pinv_mul]
  exact (isStarProjection_rangeProjector Aᴴ).conjTranspose_eq

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
  obtain ⟨S, hS⟩ := hR.exists_right_inv
  -- `Mᴴ = (RᴴM)ᴴ S`, since `R S = 1`
  have hMH : Mᴴ = (Rᴴ * M)ᴴ * S := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hS,
      Matrix.mul_one]
  -- the projector `(RᴴM)⁺(RᴴM)` fixes `Mᴴ`
  have hQMH : pinv (Rᴴ * M) * (Rᴴ * M) * Mᴴ = Mᴴ := by
    have hQ := pinv_mul_self_conjTranspose (Rᴴ * M)
    have h1 : pinv (Rᴴ * M) * (Rᴴ * M) * (Rᴴ * M)ᴴ = (Rᴴ * M)ᴴ := by
      calc pinv (Rᴴ * M) * (Rᴴ * M) * (Rᴴ * M)ᴴ
          = ((Rᴴ * M) * (pinv (Rᴴ * M) * (Rᴴ * M)))ᴴ := by
            rw [Matrix.conjTranspose_mul (Rᴴ * M) (pinv (Rᴴ * M) * (Rᴴ * M)), hQ]
        _ = (Rᴴ * M)ᴴ := by rw [← Matrix.mul_assoc, mul_pinv_mul_self]
    rw [hMH, ← Matrix.mul_assoc, h1]
  -- hence `(RᴴM)⁺(RᴴM) M⁺ = M⁺`
  have hZ : pinv M = Mᴴ * ((pinv M)ᴴ * pinv M) := by
    calc pinv M = pinv M * M * pinv M := (pinv_mul_mul_pinv M).symm
      _ = Mᴴ * (pinv M)ᴴ * pinv M := by rw [pinv_mul_self_eq M]
      _ = Mᴴ * ((pinv M)ᴴ * pinv M) := Matrix.mul_assoc _ _ _
  have hQP : pinv (Rᴴ * M) * (Rᴴ * M) * pinv M = pinv M := by
    calc pinv (Rᴴ * M) * (Rᴴ * M) * pinv M
        = pinv (Rᴴ * M) * (Rᴴ * M) * (Mᴴ * ((pinv M)ᴴ * pinv M)) := by rw [← hZ]
      _ = (pinv (Rᴴ * M) * (Rᴴ * M) * Mᴴ) * ((pinv M)ᴴ * pinv M) := by
            rw [Matrix.mul_assoc _ Mᴴ]
      _ = Mᴴ * ((pinv M)ᴴ * pinv M) := by rw [hQMH]
      _ = pinv M := hZ.symm
  have key : pinv M = pinv (Rᴴ * M) * Rᴴ * (rangeProjector M) := by
    rw [← mul_pinv M]
    calc pinv M = pinv (Rᴴ * M) * (Rᴴ * M) * pinv M := hQP.symm
      _ = pinv (Rᴴ * M) * Rᴴ * (M * pinv M) := by simp only [Matrix.mul_assoc]
  rw [key]
  exact (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
    (mul_le_of_le_one_right (frobNorm_nonneg _)
      (isStarProjection_rangeProjector M).specNorm_le_one)

end NLAlib
