/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Subspaces.Oblique
public import NLAlib.Matrix.Subspaces.ObliqueProjector

/-!
# Idempotents and frames as oblique projectors

The section "The oblique projector of two bases" of `NLAlib.Matrix.Subspaces.Oblique`, restated on
`NLAlib.obliqueProjector` in every rank the statements allow: every idempotent $\mathbf{P}$ is
$\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$ for any $\mathbf{X}$ spanning its range and any $\mathbf{S}$
whose adjoint spans the range of $\mathbf{P}^{\mathsf{H}}$, with no independence of the columns; and
the norm of the oblique projector of two frames, of any widths and any overlap, is the norm of the
pseudoinverse of their overlap.

This file holds the LowRank stage S0 additions to `NLAlib.Matrix.Subspaces.Oblique` and merges into
it at the round's wrap-up, when the deprecated two-bases lemmas there point to these by name.
Design: `docs/design/LowRank-S0.md` §3.2, §8.

## Main results

* `IsIdempotentElem.obliqueProjector_eq`: every idempotent is an oblique projector.
* `NLAlib.HasOrthonormalCols.specNorm_obliqueProjector`,
  `NLAlib.HasOrthonormalCols.specNorm_obliqueProjector_mul_cos`: the norm of the oblique projector
  of two frames.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {k n p q : Type*} [Fintype k] [Fintype n] [Fintype p]

/-- **Every idempotent is an oblique projector**:
$\mathbf{P} = \mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$ whenever
$\operatorname{range}\mathbf{X} = \operatorname{range}\mathbf{P}$ and
$\operatorname{range}\mathbf{S}^{\mathsf{H}} = \operatorname{range}\mathbf{P}^{\mathsf{H}}$. No
independence of the columns of $\mathbf{X}$ or of the rows of $\mathbf{S}$ is needed (for example
$\mathbf{X} = \mathbf{S} = \mathbf{P}$), and $\mathbf{P} = \mathbf{0}$ is allowed. This is the
converse of `NLAlib.isIdempotentElem_obliqueProjector`.
[HornJohnson2013, Corollary 3.4.3.3 context]; there with two bases of full rank. -/
theorem _root_.IsIdempotentElem.obliqueProjector_eq {P : Matrix n n 𝕜} (hP : IsIdempotentElem P)
    {X : Matrix n p 𝕜} {S : Matrix k n 𝕜}
    (hX : LinearMap.range X.mulVecLin = LinearMap.range P.mulVecLin)
    (hS : LinearMap.range Sᴴ.mulVecLin = LinearMap.range Pᴴ.mulVecLin) :
    obliqueProjector X S = P := by
  obtain ⟨C, hC⟩ := range_le_iff_exists_mul.mp hS.le
  obtain ⟨D, hD⟩ := range_le_iff_exists_mul.mp hS.ge
  have hSP : S * P = S := by
    have e : S = Cᴴ * P := by
      rw [← Matrix.conjTranspose_conjTranspose S, hC, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    rw [e, Matrix.mul_assoc, hP.eq]
  have hPS : P = Dᴴ * S := by
    rw [← Matrix.conjTranspose_conjTranspose P, hD, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hrank : (S * X).rank = X.rank := by
    rw [Matrix.rank_mul_eq_iff_injOn, hX]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    simp only [Matrix.mulVecLin_apply] at hab ⊢
    have h0 : S *ᵥ (P *ᵥ a - P *ᵥ b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    have h1 : P *ᵥ (P *ᵥ a - P *ᵥ b) = 0 := by
      have e : P *ᵥ (P *ᵥ a - P *ᵥ b) = Dᴴ *ᵥ (S *ᵥ (P *ᵥ a - P *ᵥ b)) := by
        rw [Matrix.mulVec_mulVec, ← hPS]
      rw [e, h0, Matrix.mulVec_zero]
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP.eq] at h1
    exact sub_eq_zero.mp h1
  calc obliqueProjector X S = obliqueProjector X S * P := by
        rw [obliqueProjector, Matrix.mul_assoc _ S P, hSP]
    _ = P := obliqueProjector_mul_eq_self_of_range_le hrank hX.ge

/-- **The norm of the oblique projector of two frames**: for $\mathbf{U}$, $\mathbf{V}$ with
orthonormal columns, of any widths and any overlap,
$$\|\mathbf{\Pi}_{\mathbf{U},\mathbf{V}^{\mathsf{H}}}\|_2 =
\|(\mathbf{V}^{\mathsf{H}}\mathbf{U})^{+}\|_2\,.$$
When $\mathbf{V}^{\mathsf{H}}\mathbf{U}$ is square and invertible this is the secant of the largest
principal angle (`NLAlib.HasOrthonormalCols.specNorm_obliqueProjector_mul_cos`).
[Szyld2006]; there for invertible $\mathbf{V}^{\mathsf{H}}\mathbf{U}$.
Result: oblique-projection-norm -/
theorem HasOrthonormalCols.specNorm_obliqueProjector [Fintype q] [DecidableEq p] [DecidableEq q]
    {U : Matrix n p 𝕜} {V : Matrix n q 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) :
    specNorm (obliqueProjector U Vᴴ) = specNorm (pinv (Vᴴ * U)) := by
  rw [obliqueProjector, Matrix.mul_assoc, hU.specNorm_mul_left,
    hV.specNorm_mul_conjTranspose_right]

/-- **The norm of an oblique projector and the largest principal angle**: for $\mathbf{U}$,
$\mathbf{V}$ with orthonormal columns indexed by $p$ and $\mathbf{V}^{\mathsf{H}}\mathbf{U}$
invertible,
$\|\mathbf{\Pi}_{\mathbf{U},\mathbf{V}^{\mathsf{H}}}\|_2 \cos\theta_j(\mathbf{U}, \mathbf{V}) = 1$
for $j + 1 = \lvert p \rvert$.
[Szyld2006]; [HornJohnson2013, Corollary 3.4.3.3].
Result: oblique-projection-norm -/
theorem HasOrthonormalCols.specNorm_obliqueProjector_mul_cos [DecidableEq p]
    {U V : Matrix n p 𝕜} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (h : IsUnit (Vᴴ * U)) {j : ℕ} (hj : j + 1 = Fintype.card p) :
    specNorm (obliqueProjector U Vᴴ) * Real.cos (principalAngle U V j) = 1 := by
  have hr : (Vᴴ * U).rank = Fintype.card p := Matrix.rank_of_isUnit _ h
  rw [hU.specNorm_obliqueProjector hV, specNorm_pinv _ (k := j) (by rw [hr, hj]),
    hU.cos_principalAngle hV, ← singularValues_conjTranspose (Uᴴ * V), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  exact inv_mul_cancel₀ (ne_of_gt ((singularValues_pos_iff _).mpr (by omega)))

end NLAlib
