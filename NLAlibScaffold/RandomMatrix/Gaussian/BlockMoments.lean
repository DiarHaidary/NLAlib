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
  have hY := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁
  have hrk' : Fintype.card r < Fintype.card k := by omega
  have hspec := integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix hY one_pos
    (q := 1) (by linarith [show (Fintype.card r : ℝ) + 1 ≤ Fintype.card k by exact_mod_cast hrk'])
  simp only [Real.rpow_one] at hspec
  have hc : 0 ≤ specNorm S * frobNorm T + frobNorm S * specNorm T := by positivity
  have hpt : ∀ ω, specNorm S * frobNorm (pinv (V₁ᴴ * X ω) * T) +
      frobNorm S * specNorm (pinv (V₁ᴴ * X ω) * T) ≤
      (specNorm S * frobNorm T + frobNorm S * specNorm T) * specNorm (pinv (V₁ᴴ * X ω)) := by
    intro ω
    have h1 := frobNorm_mul_le_specNorm_mul_frobNorm (pinv (V₁ᴴ * X ω)) T
    have h2 := specNorm_mul_le (pinv (V₁ᴴ * X ω)) T
    nlinarith [mul_le_mul_of_nonneg_left h1 (specNorm_nonneg S),
      mul_le_mul_of_nonneg_left h2 (frobNorm_nonneg S)]
  have hint : Integrable (fun ω => specNorm S * frobNorm (pinv (V₁ᴴ * X ω) * T) +
      frobNorm S * specNorm (pinv (V₁ᴴ * X ω) * T)) μ := by
    refine Integrable.mono' (hspec.const_mul (specNorm S * frobNorm T + frobNorm S * specNorm T))
      ?_ (ae_of_all _ fun ω => ?_)
    · have hG : Measurable (fun M : Matrix r k ℝ =>pinv M * T) :=
        measurable_pinv.matrix_mul measurable_const
      have hm : Measurable (fun M : Matrix r k ℝ =>specNorm S * frobNorm (pinv M * T) +
          frobNorm S * specNorm (pinv M * T)) :=
        ((continuous_frobNorm.measurable.comp hG).const_mul _).add
          ((continuous_specNorm.measurable.comp hG).const_mul _)
      exact (hm.comp_aemeasurable hY.aemeasurable).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      exact hpt ω
  have hmain := integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix_of_indepFun hY.aemeasurable
    (hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₂)
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂)
    (S := fun _ => S) (T := fun G => pinv G * T) measurable_const
    (measurable_pinv.matrix_mul measurable_const) hint
  simp only [Matrix.mul_assoc] at hmain ⊢
  refine hmain.trans ?_
  have hβ := integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix hY hrk'
  rw [gaussianPinvSpecNormBound_def]
  calc _ ≤ ∫ ω, (specNorm S * frobNorm T + frobNorm S * specNorm T) *
        specNorm (pinv (V₁ᴴ * X ω)) ∂μ := integral_mono hint (hspec.const_mul _) hpt
    _ = (specNorm S * frobNorm T + frobNorm S * specNorm T) *
        ∫ ω, specNorm (pinv (V₁ᴴ * X ω)) ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hβ hc
    _ = _ := mul_comm _ _

end NLAlib
