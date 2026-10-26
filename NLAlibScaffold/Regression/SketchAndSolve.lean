/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.Pinv
public import NLAlib.Regression.SketchAndSolve
public import NLAlibScaffold.RandomMatrix.Gaussian.BlockMoments

/-!
# The Gaussian sketch-and-solve excess seen through a left factor (research)

For a standard Gaussian sketch $\mathbf{S}$, a basis $\mathbf{X}$ and
$\mathbf{E} = (\mathbf{I} - \mathbf{P}_{\mathbf{X}})\mathbf{B}$, the first spectral moment of
$\mathbf{F}\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}\mathbf{E}$ is at most
`gaussianPinvSpecNormBound` times
$\|\mathbf{E}\|_2\|\mathbf{F}\|_{\mathsf{F}} + \|\mathbf{E}\|_{\mathsf{F}}\|\mathbf{F}\|_2$:
compressed to a subspace of dimension $w$ on both sides the core noise of generalized Nyström has
size $\sqrt{w/p}$, not $\sqrt{\operatorname{rank}\mathbf{X}/p}$. Joins
`NLAlib/Regression/SketchAndSolve.lean`. Research statement for
`docs/design/research/TruncatedGN-Upper.md` (G2). Not for `main`. Proofs deferred.

## Main results

* (G2)
`integral_specNorm_mul_obliqueProjector_mul_one_sub_rangeProjector_mul_le_of_hasLaw_gaussianMatrix`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m p r s a : Type*} [Fintype m]
  [Fintype p] [Fintype r] [Fintype s] [Fintype a] [DecidableEq m] {S : Ω → Matrix p m ℝ}

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The Gaussian sketch-and-solve excess through a left factor**: for a standard Gaussian
sketch $\mathbf{S} \in \mathbb{R}^{p \times m}$, $\mathbf{X} \in \mathbb{R}^{m \times s}$ with
$\operatorname{rank}\mathbf{X} + 2 \le p$, any $\mathbf{B} \in \mathbb{R}^{m \times r}$ and
$\mathbf{F} \in \mathbb{R}^{a \times m}$, with $\mathbf{E} = (\mathbf{I} -
\mathbf{P}_{\mathbf{X}})\mathbf{B}$, $q = \operatorname{rank}\mathbf{X}$ and
$\beta = \frac{e}{p - q}\sqrt{(p + q - 1)/2}$ the value of `gaussianPinvSpecNormBound`,
$$\mathbb{E}\|\mathbf{F}\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}\mathbf{E}\|_2 \le
\beta\,\bigl(\|\mathbf{E}\|_2\|\mathbf{F}\|_{\mathsf{F}} +
\|\mathbf{E}\|_{\mathsf{F}}\|\mathbf{F}\|_2\bigr)\,.$$
No printed source.
Proof: M, about 50 lines. Frames $\mathbf{Q}_1$, $\mathbf{Q}_2$ from
`exists_hasOrthonormalCols_frames_range_compl`; almost surely
$\operatorname{rank}(\mathbf{S}\mathbf{X}) = \operatorname{rank}\mathbf{X}$
(`ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix` with
`hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`, as in the private `ae_rank_mul_eq` of the
library file) and then
`obliqueProjector_mul_one_sub_rangeProjector_mul_eq` gives
$\mathbf{F}\mathbf{\Pi}\mathbf{E} = (\mathbf{F}\mathbf{Q}_1)(\mathbf{S}\mathbf{Q}_1)^{+}
(\mathbf{S}\mathbf{Q}_2)(\mathbf{Q}_2^{\mathsf{H}}\mathbf{E})$ (`integral_congr_ae`). Take the
transpose (`specNorm_conjTranspose`, `pinv_conjTranspose`, `Matrix.conjTranspose_mul`): it is
$\mathbf{S}'\mathbf{G}_2\mathbf{G}_1^{+}\mathbf{T}'$ with $\mathbf{X}_{\mathrm{G}} =
\mathbf{S}^{\mathsf{H}}$ Gaussian $m \times p$, $\mathbf{G}_i =
\mathbf{Q}_i^{\mathsf{H}}\mathbf{X}_{\mathrm{G}}$, $\mathbf{S}' =
\mathbf{E}^{\mathsf{H}}\mathbf{Q}_2$ and $\mathbf{T}' = \mathbf{Q}_1^{\mathsf{H}}
\mathbf{F}^{\mathsf{H}}$; apply
`NLAlib.integral_specNorm_mul_mul_pinv_mul_le_of_hasLaw_gaussianMatrix` (with
`Fintype.card_fin`), and $\|\mathbf{S}'\|_2 = \|\mathbf{E}\|_2$,
$\|\mathbf{S}'\|_{\mathsf{F}} = \|\mathbf{E}\|_{\mathsf{F}}$
(`HasOrthonormalCols.specNorm_mul_left`,
`HasOrthonormalCols.frobNorm_mul_left` and the frame identity), $\|\mathbf{T}'\|_2 \le
\|\mathbf{F}\|_2$, $\|\mathbf{T}'\|_{\mathsf{F}} \le \|\mathbf{F}\|_{\mathsf{F}}$
(`specNorm_mul_le`, `frobNorm_mul_le_specNorm_mul_frobNorm`,
`HasOrthonormalCols.specNorm_le_one`-type bound $\|\mathbf{Q}_1^{\mathsf{H}}\|_2 \le 1$). The
library's
`integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_of_hasLaw_gaussianMatrix`
is the same route at $\mathbf{F} = \mathbf{I}$, second moment. -/
theorem
    integral_specNorm_mul_obliqueProjector_mul_one_sub_rangeProjector_mul_le_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) (F : Matrix a m ℝ) :
    ∫ ω, specNorm (F * (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B))) ∂μ ≤
      gaussianPinvSpecNormBound X.rank (Fintype.card p) *
        (specNorm ((1 - rangeProjector X) * B) * frobNorm F +
          frobNorm ((1 - rangeProjector X) * B) * specNorm F) := by
  sorry

end NLAlib
