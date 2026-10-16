/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Norms.UnitarilyInvariant
public import NLAlib.Matrix.Pseudoinverse.NormBounds
public import NLAlib.Matrix.Subspaces.ObliqueProjector
public import NLAlib.Regression.Embedding

/-!
# Sketched least squares through the oblique projector

A subspace injection for $\operatorname{range}\mathbf{A}$ controls the sketched term of the exact
error split of `NLAlib.frobNorm_one_sub_obliqueProjector_mul_sq`:
$$\|\mathbf{\Pi}_{\mathbf{A},\mathbf{S}}\mathbf{Y}\|_{\mathsf{F}}^2 \le
\|\mathbf{S}\mathbf{Y}\|_{\mathsf{F}}^2 / a\,.$$
With the split this gives the sketch-and-solve bound
`NLAlib.IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le` of
`NLAlib.Regression.Embedding`, whose left side is
$(\mathbf{I} - \mathbf{\Pi}_{\mathbf{A},\mathbf{S}})\mathbf{Y}$ by `NLAlib.mul_sketchAndSolve`.

The same injection bounds the sketched term in every unitarily invariant norm by an
approximate-multiplication error,
$\|\mathbf{\Pi}_{\mathbf{A},\mathbf{S}}\mathbf{Y}\|_{\Phi} \le
\|\mathbf{P}_{\mathbf{A}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{Y}\|_{\Phi} / a$, which decays
with the sketch size when $\mathbf{P}_{\mathbf{A}}\mathbf{Y} = \mathbf{0}$ (LowRank stage S7).

The oblique-projector bounds complement `NLAlib.Regression.Embedding`.
Design: `docs/design/LowRank-S0.md` §3.7, §8; placement:
`docs/design/Regression-Organization.md`.

## Main results

* `NLAlib.IsSubspaceInjection.frobNorm_obliqueProjector_mul_sq_le`: the sketched term of the split.
* `NLAlib.IsSubspaceInjection.matrixNorm_obliqueProjector_mul_le`: the same term through
  approximate multiplication, every unitarily invariant norm.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {k n q r : Type*} [Fintype k] [Fintype n] [Fintype q]
  {S : Matrix k n 𝕜} {A : Matrix n q 𝕜} {a : ℝ}

/-- **The sketched part of the error split is controlled by the injection**: for a subspace
injection for $\operatorname{range}\mathbf{A}$ with constant $a > 0$ and every $\mathbf{Y}$,
$$\|\mathbf{\Pi}_{\mathbf{A},\mathbf{S}}\mathbf{Y}\|_{\mathsf{F}}^2 \le
\frac{\|\mathbf{S}\mathbf{Y}\|_{\mathsf{F}}^2}{a}\,.$$
The columns of $\mathbf{W} = \mathbf{\Pi}_{\mathbf{A},\mathbf{S}}\mathbf{Y}$ lie in
$\operatorname{range}\mathbf{A}$ and
$\mathbf{S}\mathbf{W} = \mathbf{P}_{\mathbf{S}\mathbf{A}}\mathbf{S}\mathbf{Y}$.
[CamanoEpperlyMeyerTropp2025, Lemma 2.6, proof]; [TroppYurtseverUdellCevher2017, Lemma A.4]; there
for the residual of the sketched problem. -/
theorem IsSubspaceInjection.frobNorm_obliqueProjector_mul_sq_le [Fintype r]
    (h : IsSubspaceInjection S A a) (ha : 0 < a) (Y : Matrix n r 𝕜) :
    frobNorm (obliqueProjector A S * Y) ^ 2 ≤ frobNorm (S * Y) ^ 2 / a := by
  have hP := isStarProjection_rangeProjector (S * A)
  rw [le_div_iff₀ ha, frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have hw : A *ᵥ (pinv (S * A) * S * Y).col j = (obliqueProjector A S * Y).col j := by
    change (A * (pinv (S * A) * S * Y)).col j = _
    simp only [obliqueProjector, Matrix.mul_assoc]
  have hSw : S *ᵥ (obliqueProjector A S * Y).col j =
      rangeProjector (S * A) *ᵥ (S * Y).col j := by
    change (S * (obliqueProjector A S * Y)).col j = (rangeProjector (S * A) * (S * Y)).col j
    simp only [← mul_pinv, obliqueProjector, Matrix.mul_assoc]
  have hinj := isSubspaceInjection_iff_forall_mem_range.mp h _ ⟨_, hw⟩
  rw [mul_comm]
  refine hinj.trans ?_
  rw [hSw]
  exact pow_le_pow_left₀ (norm_nonneg _) (hP.norm_toLp_mulVec_le _) 2

/-- **Sketch-and-solve error through approximate multiplication**: if $\mathbf{S}$ injects
$\operatorname{range}\mathbf{A}$ with constant $a > 0$, then for every $\mathbf{Y}$ and every
unitarily invariant norm
$$\|\mathbf{\Pi}_{\mathbf{A},\mathbf{S}}\mathbf{Y}\|_{\Phi} \le
\frac{\|\mathbf{P}_{\mathbf{A}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{Y}\|_{\Phi}}{a}\,.$$
For $\mathbf{Y}$ with $\mathbf{P}_{\mathbf{A}}\mathbf{Y} = \mathbf{0}$ the right side is an
approximate-multiplication error, which decays with the sketch size; the bound in
$\|\mathbf{S}\mathbf{Y}\|_{\mathsf{F}}$, which does not, is
`NLAlib.IsSubspaceInjection.frobNorm_obliqueProjector_mul_sq_le`.
[Woodruff2014, proof of Theorem 23]; there for an orthonormal basis and a $(1 \pm 1/2)$
embedding; here basis-free, any injection constant, every unitarily invariant norm. -/
theorem IsSubspaceInjection.matrixNorm_obliqueProjector_mul_le [Fintype r]
    (h : IsSubspaceInjection S A a) (ha : 0 < a) (Φ : SymmetricGauge) (Y : Matrix n r 𝕜) :
    Φ.matrixNorm (obliqueProjector A S * Y) ≤
      Φ.matrixNorm (rangeProjector A * Sᴴ * S * Y) / a := by
  classical
  obtain ⟨Q, hQ, hQA⟩ := exists_hasOrthonormalCols_range_eq A (Fintype.card_fin A.rank)
  have hPi : obliqueProjector A S = obliqueProjector Q S :=
    obliqueProjector_eq_of_range_eq (h.rank_mul_eq ha) hQA.symm
  have hPA : rangeProjector A = Q * Qᴴ := by rw [← hQ.rangeProjector_eq, rangeProjector_inj, hQA]
  have hG : a • (1 : Matrix (Fin A.rank) (Fin A.rank) 𝕜) ≤ (S * Q)ᴴ * (S * Q) :=
    hQ.isSubspaceInjection_iff.1 (h.of_range_le hQA.le)
  have hpinv : specNorm (pinv ((S * Q)ᴴ * (S * Q))) ≤ a⁻¹ := by
    rw [← specNorm_pinv_sq]
    exact specNorm_pinv_sq_le_inv_of_smul_one_le ha hG
  have hW : obliqueProjector Q S * Y =
      Q * (pinv ((S * Q)ᴴ * (S * Q)) * (Qᴴ * (Sᴴ * S * Y))) := by
    rw [obliqueProjector, pinv_eq_pinv_conjTranspose_mul_self_mul (S * Q),
      Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have h2 : Φ.matrixNorm (rangeProjector A * Sᴴ * S * Y) =
      Φ.matrixNorm (Qᴴ * (Sᴴ * S * Y)) := by
    rw [hPA, show Q * Qᴴ * Sᴴ * S * Y = Q * (Qᴴ * (Sᴴ * S * Y)) by simp only [Matrix.mul_assoc],
      Φ.matrixNorm_mul_left_of_hasOrthonormalCols hQ]
  rw [hPi, hW, Φ.matrixNorm_mul_left_of_hasOrthonormalCols hQ, h2, le_div_iff₀ ha]
  calc Φ.matrixNorm (pinv ((S * Q)ᴴ * (S * Q)) * (Qᴴ * (Sᴴ * S * Y))) * a
      ≤ specNorm (pinv ((S * Q)ᴴ * (S * Q))) * Φ.matrixNorm (Qᴴ * (Sᴴ * S * Y)) * a := by
        gcongr
        exact Φ.matrixNorm_mul_le_specNorm_mul _ _
    _ ≤ a⁻¹ * Φ.matrixNorm (Qᴴ * (Sᴴ * S * Y)) * a := by gcongr
    _ = Φ.matrixNorm (Qᴴ * (Sᴴ * S * Y)) := by field_simp

end NLAlib
