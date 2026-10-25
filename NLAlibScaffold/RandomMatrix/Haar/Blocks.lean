/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Haar.Blocks
public import NLAlib.RandomMatrix.UnitaryInvariance
public import NLAlibScaffold.Matrix.Pseudoinverse.NormBounds

/-!
# The random orthonormal sketching inequality with a weight (stage S10)

Epperly and Webber's Proposition 5.7 for a general invertible weight $\mathbf{R}$: the Haar block
moment `NLAlib.integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame` (the case
$\mathbf{R} = \mathbf{I}$, an equality) becomes a lower bound. It joins
`NLAlib/RandomMatrix/Haar/Blocks.lean`; its proof is deferred. Design:
`docs/design/LowRank-EstimatorLowerBounds.md` §3.3.

## Main results

* `NLAlib.mul_le_integral_frobNorm_pinv_conjTranspose_mul_mul_sq_of_hasLaw_haarFrame`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m p r s a : Type*} [Fintype m]
  [Fintype p] [Fintype r] [Fintype s] [Fintype a] {Q : Ω → Matrix m p ℝ}

/-- **A weight does not help a random orthonormal sketch** (Epperly and Webber's
Proposition 5.7): for an $m \times p$ Haar frame $\mathbf{Q}$ with $p \le m$, orthonormal
$\mathbf{V}_1 \in \mathbb{R}^{m \times r}$, $\mathbf{V}_2 \in \mathbb{R}^{m \times s}$ with
orthogonal
ranges and $r + s = m$, $r + 2 \le p$, any $\mathbf{B} \in \mathbb{R}^{s \times a}$ and any
invertible $\mathbf{R} \in \mathbb{R}^{p \times p}$,
$$\frac{m - p}{m - r}\cdot\frac{r}{p - r - 1}\,\|\mathbf{B}\|_{\mathsf{F}}^2 \le
\mathbb{E}\bigl\|(\mathbf{R}^{\mathsf{H}}\mathbf{Q}^{\mathsf{H}}\mathbf{V}_1)^{+}
\mathbf{R}^{\mathsf{H}}\mathbf{Q}^{\mathsf{H}}\mathbf{V}_2\mathbf{B}\bigr\|_{\mathsf{F}}^2\,,$$
with equality at $\mathbf{R} = \mathbf{I}$
(`NLAlib.integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame`). The integrand is integrable
(it is at most $\|\mathbf{R}\|_2^2\|\mathbf{R}^{-1}\|_2^2$ times the $\mathbf{R} = \mathbf{I}$ one).
[EpperlyWebber2026, Proposition 5.7]; there over $\mathbb{R}$ and $\mathbb{C}$ with the rows of
$\mathbf{\Omega}$ split, here with the blocks $\mathbf{V}_1^{\mathsf{H}}\mathbf{Q}$,
$\mathbf{V}_2^{\mathsf{H}}\mathbf{Q}$.
Proof: L, about 120 lines. EW's proof. (1) With $\mathbf{\Omega}_i =
\mathbf{V}_i^{\mathsf{H}}\mathbf{Q}$
and $F(\mathbf{x}) = \mathbf{R}(\mathbf{x}\mathbf{R})^{+}((\mathbf{x}\mathbf{R})^{+})^{\mathsf{H}}
\mathbf{R}^{\mathsf{H}}$, the matrix
$\mathbf{\Omega}_2 F(\mathbf{\Omega}_1)\mathbf{\Omega}_2^{\mathsf{H}}$ has mean a multiple of
$\mathbf{I}_s$ (`integral_conjTranspose_mul_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant`,
`isLeftUnitarilyInvariant_haarFrame`), so the expectation is
$\|\mathbf{B}\|_{\mathsf{F}}^2\,\mathbb{E}\operatorname{tr}(\cdots)/s$. (2) The trace: with
$\mathbf{\Omega}_1^{\mathsf{H}}\mathbf{\Omega}_1 + \mathbf{\Omega}_2^{\mathsf{H}}\mathbf{\Omega}_2 =
\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{I}$ and
$\mathbf{\Omega}_1 F(\mathbf{\Omega}_1)\mathbf{\Omega}_1^{\mathsf{H}}$ a rank-$r$ projector
(a.s. $\mathbf{\Omega}_1$ has full row rank, `ae_rank_mul_eq_min_of_hasLaw_haarFrame`),
$\operatorname{tr}(\mathbf{\Omega}_2 F\mathbf{\Omega}_2^{\mathsf{H}})$ equals
$\|(\mathbf{R}^{\mathsf{H}}\mathbf{\Omega}_1^{\mathsf{H}})^{+}
\mathbf{R}^{\mathsf{H}}\|_{\mathsf{F}}^2 - r$.
(3) `frobNorm_pinv_le_frobNorm_pinv_conjTranspose_mul_mul_conjTranspose` with
$\mathbf{M} = \mathbf{\Omega}_1^{\mathsf{H}}$, then the Beta trace
`integral_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame`:
$\mathbb{E}\|(\mathbf{\Omega}_1^{\mathsf{H}})^{+}\|_{\mathsf{F}}^2 = r(1 + (m - p)/(p - r - 1))$.
Arithmetic: $(r(1 + \frac{m-p}{p-r-1}) - r)/(m - r)$. -/
theorem mul_le_integral_frobNorm_pinv_conjTranspose_mul_mul_sq_of_hasLaw_haarFrame [DecidableEq p]
    [DecidableEq r] [DecidableEq s] (hQ : HasLaw Q (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) {V₁ : Matrix m r ℝ} {V₂ : Matrix m s ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0)
    (hrs : Fintype.card r + Fintype.card s = Fintype.card m)
    (hrp : Fintype.card r + 2 ≤ Fintype.card p) (B : Matrix s a ℝ) {R : Matrix p p ℝ}
    (hR : IsUnit R) :
    frobNorm B ^ 2 * (((Fintype.card m : ℝ) - Fintype.card p) /
        ((Fintype.card m : ℝ) - Fintype.card r) *
          ((Fintype.card r : ℝ) / ((Fintype.card p : ℝ) - Fintype.card r - 1))) ≤
      ∫ ω, frobNorm (pinv (Rᴴ * ((Q ω)ᴴ * V₁)) * (Rᴴ * ((Q ω)ᴴ * V₂)) * B) ^ 2 ∂μ := by
  sorry

end NLAlib
