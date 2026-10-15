/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Subspaces.ObliqueProjector
public import NLAlib.Sketching.Properties.LeastSquares

/-!
# Sketched least squares through the oblique projector

A subspace injection for $\operatorname{range}\mathbf{A}$ controls the sketched term of the exact
error split of `NLAlib.frobNorm_one_sub_obliqueProjector_mul_sq`:
$$\|\mathbf{\Pi}_{\mathbf{A},\mathbf{S}}\mathbf{Y}\|_{\mathsf{F}}^2 \le
\|\mathbf{S}\mathbf{Y}\|_{\mathsf{F}}^2 / a\,.$$
With the split this gives the sketch-and-solve bound
`NLAlib.IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le` of
`NLAlib.Sketching.Properties.LeastSquares`, whose left side is
$(\mathbf{I} - \mathbf{\Pi}_{\mathbf{A},\mathbf{S}})\mathbf{Y}$ by `NLAlib.mul_sketchAndSolve`.

This file holds the LowRank stage S0 addition to `NLAlib.Sketching.Properties.LeastSquares` and
merges into it at the round's wrap-up, where `frobNorm_sub_mul_pinv_mul_sq_le` is reproved from the
split and this lemma. Design: `docs/design/LowRank-S0.md` §3.7, §8.

## Main results

* `NLAlib.IsSubspaceInjection.frobNorm_obliqueProjector_mul_sq_le`: the sketched term of the split.
-/

@[expose] public section

open scoped Matrix

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

end NLAlib
