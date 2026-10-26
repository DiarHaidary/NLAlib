/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.BlockMoments
public import NLAlib.RandomMatrix.Gaussian.InverseMoments.Spectral
public import NLAlib.RandomMatrix.Gaussian.SpectralNorm

/-!
# The Gaussian block with a factor on both sides (research)

For a standard Gaussian $\mathbf{G}$, frames $\mathbf{V}_1 \perp \mathbf{V}_2$ and fixed
$\mathbf{S}$, $\mathbf{T}$, the first spectral moment of
$\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\mathbf{T}$ is at most
`gaussianPinvSpecNormBound` times Chevet's bound for $\mathbf{S}$ and $\mathbf{T}$. With
$\mathbf{T}$ of small rank this is the noise seen through a window: nothing of the dimension of
$\mathbf{G}_1$ survives. Joins `NLAlib/RandomMatrix/Gaussian/BlockMoments.lean`. Research
statement for `docs/design/research/TruncatedGN-Upper.md` (G1). Not for `main`. Proofs deferred.

## Main results

* `NLAlib.integral_specNorm_mul_mul_pinv_mul_le_of_hasLaw_gaussianMatrix` (G1).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k r s a b : Type*} [Fintype n]
  [Fintype k] [Fintype r] [Fintype s] [Fintype a] [Fintype b] {X : Ω → Matrix n k ℝ}

/-- **The Gaussian block with factors on both sides**: for a random
$\mathbf{X} \in \mathbb{R}^{n \times k}$ with independent standard Gaussian entries,
$\mathbf{V}_1 \in \mathbb{R}^{n \times r}$ and $\mathbf{V}_2 \in \mathbb{R}^{n \times s}$ with
orthonormal columns and $\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$,
$\lvert r \rvert + 2 \le \lvert k \rvert$, $\mathbf{G}_i = \mathbf{V}_i^{\mathsf{H}}\mathbf{X}$
and any $\mathbf{S} \in \mathbb{R}^{a \times s}$, $\mathbf{T} \in \mathbb{R}^{r \times b}$,
with $\beta = \frac{e}{\lvert k\rvert - \lvert r\rvert}\sqrt{(\lvert k\rvert + \lvert r\rvert -
1)/2}$ the value of `gaussianPinvSpecNormBound`,
$$\mathbb{E}\|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\mathbf{T}\|_2 \le
\beta\,\bigl(\|\mathbf{S}\|_2\|\mathbf{T}\|_{\mathsf{F}} +
\|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_2\bigr)\,.$$
No printed source; the two-sided form of [HalkoMartinssonTropp2011, proof of Theorem 10.6].
Proof: M, about 45 lines. As in `integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix`:
`integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix_of_indepFun` with the Gaussian
$\mathbf{G}_2$ (`hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix`), the variable
$\mathbf{G}_1$ independent of it (`indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix`), left
factor the constant $\mathbf{S}$ (`measurable_const`) and right factor
$\mathbf{G}_1 \mapsto \mathbf{G}_1^{+}\mathbf{T}$ (`measurable_pinv`, `Measurable.matrix_mul`);
then pointwise $\|\mathbf{G}_1^{+}\mathbf{T}\|_{\mathsf{F}} \le \|\mathbf{G}_1^{+}\|_2
\|\mathbf{T}\|_{\mathsf{F}}$ (`frobNorm_mul_le_specNorm_mul_frobNorm`) and
$\|\mathbf{G}_1^{+}\mathbf{T}\|_2 \le \|\mathbf{G}_1^{+}\|_2\|\mathbf{T}\|_2$
(`specNorm_mul_le`), so the right side is at most
$(\|\mathbf{S}\|_2\|\mathbf{T}\|_{\mathsf{F}} + \|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_2)\,
\mathbb{E}\|\mathbf{G}_1^{+}\|_2$ (`integral_mono`, `integral_const_mul`), and
`integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix` with `gaussianPinvSpecNormBound_def`.
Integrability of the Chevet bound: it is dominated by a constant times
$\|\mathbf{G}_1^{+}\|_2$, integrable by `integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix`
at exponent $1$ (`Real.rpow_one`). -/
theorem integral_specNorm_mul_mul_pinv_mul_le_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ)
    (T : Matrix r b ℝ) :
    ∫ ω, specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω) * T) ∂μ ≤
      gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k) *
        (specNorm S * frobNorm T + frobNorm S * specNorm T) := by
  sorry

end NLAlib
