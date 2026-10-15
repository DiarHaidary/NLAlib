/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.BlockMoments
public import NLAlib.RandomMatrix.Gaussian.SpectralNormSq

/-!
# The second spectral moments of the Gaussian blocks

For a standard Gaussian $n \times k$ matrix $\mathbf{G}$, frames $\mathbf{V}_1$ ($n \times r$) and
$\mathbf{V}_2$ ($n \times s$) with $\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$, the
blocks $\mathbf{G}_1 = \mathbf{V}_1^{\mathsf{H}}\mathbf{G}$ and
$\mathbf{G}_2 = \mathbf{V}_2^{\mathsf{H}}\mathbf{G}$ and a fixed $\mathbf{S}$, this file
bounds the second spectral moment of $\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}$. The route is,
conditionally on $\mathbf{G}_1$, the second moment of a Gaussian product
(`NLAlib.integral_specNorm_mul_mul_sq_le_of_hasLaw_gaussianMatrix_of_indepFun`) with
$\mathbf{T} = \mathbf{G}_1^{+}$, then Cauchy–Schwarz and the moments of $\mathbf{G}_1^{+}$:
$\mathbb{E}\|\mathbf{G}_1^{+}\|_{\mathsf{F}}^2 = r/(k - r - 1)$
(`NLAlib.integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix`) and the spectral moment
`NLAlib.integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix` at exponent $2$. The transposed
form is the sketch-and-solve noise. A side file that merges into
`NLAlib/RandomMatrix/Gaussian/BlockMoments.lean`, beside the Frobenius and first spectral block
moments (`docs/design/LowRank-S6.md` §4, L8 to L11).

## Main results

* `NLAlib.integral_specNorm_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_specNorm_pinv_mul_mul_sq_le_of_hasLaw_gaussianMatrix`: the transposed form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k r s a : Type*} [Fintype n]
  [Fintype k] [Fintype r] [Fintype s] [Fintype a] {X : Ω → Matrix n k ℝ}

/-- Cauchy–Schwarz for nonnegative square-integrable functions,
$\int fg \le \sqrt{\int f^2}\sqrt{\int g^2}$. -/
private theorem integral_mul_le_sqrt_mul_sqrt {f g : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hg0 : ∀ ω, 0 ≤ g ω) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ ω, f ω * g ω ∂μ ≤ √(∫ ω, f ω ^ 2 ∂μ) * √(∫ ω, g ω ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ hf0) (ae_of_all _ hg0) (by simpa using hf) (by simpa using hg)
  simp only [Real.rpow_two] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h

/-- Chevet's conditional bound is integrable when its random factors are square-integrable. -/
private theorem integrable_chevet_sq {F P : Ω → ℝ} (a b : ℝ)
    (hF2 : Integrable (fun ω => F ω ^ 2) μ) (hP2 : Integrable (fun ω => P ω ^ 2) μ)
    (hFP : Integrable (fun ω => F ω * P ω) μ) :
    Integrable (fun ω => (a * F ω + b * P ω) ^ 2 + (a * P ω) ^ 2) μ := by
  have h : Integrable (fun ω => a ^ 2 * F ω ^ 2 + 2 * (a * b) * (F ω * P ω) +
      (a ^ 2 + b ^ 2) * P ω ^ 2) μ :=
    ((hF2.const_mul _).add (hFP.const_mul _)).add (hP2.const_mul _)
  exact h.congr (ae_of_all _ fun ω => by ring)

/-- The arithmetic of the second block moment: Chevet's conditional bound integrates to at most
$(a\sqrt h + b\beta)^2 + a^2\beta^2$ when $\mathbb{E}F^2 = h$, $\mathbb{E}P^2 \le \beta^2$ and
$\mathbb{E}FP \le \sqrt h\,\beta$. -/
private theorem integral_chevet_sq_le {F P : Ω → ℝ} {a b h β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hh : 0 ≤ h) (hF2 : Integrable (fun ω => F ω ^ 2) μ) (hP2 : Integrable (fun ω => P ω ^ 2) μ)
    (hFP : Integrable (fun ω => F ω * P ω) μ) (hEF : ∫ ω, F ω ^ 2 ∂μ = h)
    (hEP : ∫ ω, P ω ^ 2 ∂μ ≤ β ^ 2) (hEFP : ∫ ω, F ω * P ω ∂μ ≤ √h * β) :
    ∫ ω, ((a * F ω + b * P ω) ^ 2 + (a * P ω) ^ 2) ∂μ ≤ (a * √h + b * β) ^ 2 + (a * β) ^ 2 := by
  have h1 : Integrable (fun ω => a ^ 2 * F ω ^ 2 + 2 * (a * b) * (F ω * P ω)) μ :=
    (hF2.const_mul _).add (hFP.const_mul _)
  have e : ∫ ω, ((a * F ω + b * P ω) ^ 2 + (a * P ω) ^ 2) ∂μ =
      a ^ 2 * h + 2 * (a * b) * ∫ ω, F ω * P ω ∂μ + (a ^ 2 + b ^ 2) * ∫ ω, P ω ^ 2 ∂μ := by
    rw [integral_congr_ae (ae_of_all _ fun ω => (by ring :
        (a * F ω + b * P ω) ^ 2 + (a * P ω) ^ 2 =
          a ^ 2 * F ω ^ 2 + 2 * (a * b) * (F ω * P ω) + (a ^ 2 + b ^ 2) * P ω ^ 2)),
      integral_add h1 (hP2.const_mul _), integral_add (hF2.const_mul _) (hFP.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul, hEF]
  rw [e]
  have hs : √h ^ 2 = h := Real.sq_sqrt hh
  nlinarith [mul_le_mul_of_nonneg_left hEFP (by positivity : 0 ≤ 2 * (a * b)),
    mul_le_mul_of_nonneg_left hEP (by positivity : 0 ≤ a ^ 2 + b ^ 2)]

/-- The squared spectral norm of the Gaussian block $\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}$ is
integrable, for $\lvert r \rvert + 2 \le \lvert k \rvert$. -/
theorem integrable_specNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    Integrable (fun ω => specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ^ 2) μ := by
  refine (integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂ hrk
    S).mono' ?_ (ae_of_all _ fun ω => ?_)
  · have hm : Measurable fun x : Matrix n k ℝ => specNorm (S * (V₂ᴴ * x) * pinv (V₁ᴴ * x)) ^ 2 :=
      (continuous_specNorm.measurable.comp ((measurable_const.matrix_mul
        (measurable_const.matrix_mul measurable_id)).matrix_mul
          (measurable_pinv.comp (measurable_const.matrix_mul measurable_id)))).pow_const 2
    exact (hm.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_le_frobNorm _) 2

/-- **The second spectral moment of a Gaussian block**: with
$\mathbf{G}_1 = \mathbf{V}_1^{\mathsf{H}}\mathbf{X}$ and
$\mathbf{G}_2 = \mathbf{V}_2^{\mathsf{H}}\mathbf{X}$ independent, $r = \lvert r \rvert$,
$k = \lvert k \rvert$ and $r + 2 \le k$, <!-- value gaussianPinvSpecNormBound r k -->
$$\mathbb{E}\|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\|_2^2 \le \Bigl(\|\mathbf{S}\|_2
\sqrt{\tfrac{r}{k-r-1}} + \|\mathbf{S}\|_{\mathsf{F}}\,\frac{e}{k - r}\sqrt{(k + r - 1)/2}\Bigr)^2 +
\|\mathbf{S}\|_2^2\Bigl(\frac{e}{k - r}\sqrt{(k + r - 1)/2}\Bigr)^2\,,$$
the second-moment twin of `NLAlib.integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix`,
with the constant `gaussianPinvSpecNormBound r k`.
[HalkoMartinssonTropp2011, proof of Theorem 10.6]; [TroppWebber2023, Lemmas B.1, B.3]; there the
first moment (HMT) or the second without the last term (TW). -/
theorem integral_specNorm_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    ∫ ω, specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ^ 2 ∂μ ≤
      (specNorm S * √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) +
          frobNorm S * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)) ^ 2 +
        (specNorm S * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)) ^ 2 := by
  have := hX.isProbabilityMeasure
  have hY := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁
  have hrk' : (Fintype.card r : ℝ) + 2 ≤ Fintype.card k := by exact_mod_cast hrk
  have hβ0 : 0 ≤ gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k) :=
    gaussianPinvSpecNormBound_nonneg (by omega)
  have hh : 0 ≤ (Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1) :=
    div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hF2 : Integrable (fun ω => frobNorm (pinv (V₁ᴴ * X ω)) ^ 2) μ :=
    integrable_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hY hrk
  have hP2 : Integrable (fun ω => specNorm (pinv (V₁ᴴ * X ω)) ^ 2) μ := by
    have := integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix hY two_pos (by linarith)
    simpa only [Real.rpow_two] using this
  have hFL : MemLp (fun ω => frobNorm (pinv (V₁ᴴ * X ω))) 2 μ :=
    (memLp_two_iff_integrable_sq (((continuous_frobNorm.measurable.comp
      measurable_pinv).comp_aemeasurable hY.aemeasurable).aestronglyMeasurable)).2 hF2
  have hPL : MemLp (fun ω => specNorm (pinv (V₁ᴴ * X ω))) 2 μ :=
    (memLp_two_iff_integrable_sq (((continuous_specNorm.measurable.comp
      measurable_pinv).comp_aemeasurable hY.aemeasurable).aestronglyMeasurable)).2 hP2
  have hFP : Integrable (fun ω => frobNorm (pinv (V₁ᴴ * X ω)) * specNorm (pinv (V₁ᴴ * X ω))) μ :=
    hFL.integrable_mul hPL
  have hEF := integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hY hrk
  have hEP : ∫ ω, specNorm (pinv (V₁ᴴ * X ω)) ^ 2 ∂μ ≤
      gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k) ^ 2 := by
    have := integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix hY two_pos (by linarith)
    simpa only [Real.rpow_two, ← gaussianPinvSpecNormBound_def] using this
  have hsqP : √(∫ ω, specNorm (pinv (V₁ᴴ * X ω)) ^ 2 ∂μ) ≤
      gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k) := by
    rw [← Real.sqrt_sq hβ0]
    exact Real.sqrt_le_sqrt hEP
  have hEFP : ∫ ω, frobNorm (pinv (V₁ᴴ * X ω)) * specNorm (pinv (V₁ᴴ * X ω)) ∂μ ≤
      √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) *
        gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k) := by
    refine (integral_mul_le_sqrt_mul_sqrt (fun _ => frobNorm_nonneg _)
      (fun _ => specNorm_nonneg _) hFL hPL).trans ?_
    rw [hEF]
    exact mul_le_mul_of_nonneg_left hsqP (Real.sqrt_nonneg _)
  refine (integral_specNorm_mul_mul_sq_le_of_hasLaw_gaussianMatrix_of_indepFun hY.aemeasurable
    (hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₂)
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂)
    (S := fun _ => S) measurable_const measurable_pinv
    (integrable_chevet_sq (specNorm S) (frobNorm S) hF2 hP2 hFP)).trans ?_
  exact integral_chevet_sq_le (specNorm_nonneg S) (frobNorm_nonneg S) hh hF2 hP2 hFP hEF hEP hEFP

private theorem specNorm_pinv_mul_mul_eq (A : Matrix n k ℝ) (V₁ : Matrix n r ℝ)
    (V₂ : Matrix n s ℝ) (S : Matrix s a ℝ) :
    specNorm (pinv (Aᴴ * V₁) * (Aᴴ * V₂) * S) = specNorm (Sᴴ * (V₂ᴴ * A) * pinv (V₁ᴴ * A)) := by
  rw [← specNorm_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← pinv_conjTranspose,
    Matrix.mul_assoc]

/-- The squared spectral norm of the transposed Gaussian block
$\mathbf{G}_1^{\mathsf{H}+}\mathbf{G}_2^{\mathsf{H}}\mathbf{S}$ is integrable, for
$\lvert r \rvert + 2 \le \lvert k \rvert$; the sketch-and-solve noise. -/
theorem integrable_specNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix s a ℝ) :
    Integrable (fun ω => specNorm (pinv ((X ω)ᴴ * V₁) * ((X ω)ᴴ * V₂) * S) ^ 2) μ := by
  simp only [specNorm_pinv_mul_mul_eq]
  exact integrable_specNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂ hrk Sᴴ

/-- **The second spectral moment of the transposed Gaussian block**: under the hypotheses of
`NLAlib.integral_specNorm_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix`, the sketch-and-solve
noise satisfies <!-- value gaussianPinvSpecNormBound r k -->
$$\mathbb{E}\|\mathbf{G}_1^{\mathsf{H}+}\mathbf{G}_2^{\mathsf{H}}\mathbf{S}\|_2^2 \le
\Bigl(\|\mathbf{S}\|_2\sqrt{\tfrac{r}{k-r-1}} +
\|\mathbf{S}\|_{\mathsf{F}}\,\frac{e}{k - r}\sqrt{(k + r - 1)/2}\Bigr)^2 +
\|\mathbf{S}\|_2^2\Bigl(\frac{e}{k - r}\sqrt{(k + r - 1)/2}\Bigr)^2\,,$$
with $\mathbf{G}_i = \mathbf{V}_i^{\mathsf{H}}\mathbf{X}$ and the constant
`gaussianPinvSpecNormBound r k`.
[HalkoMartinssonTropp2011, proof of Theorem 10.6]; [TroppWebber2023, Lemmas B.1, B.3]; there the
first moment (HMT) or the second without the last term (TW), not transposed. -/
theorem integral_specNorm_pinv_mul_mul_sq_le_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix s a ℝ) :
    ∫ ω, specNorm (pinv ((X ω)ᴴ * V₁) * ((X ω)ᴴ * V₂) * S) ^ 2 ∂μ ≤
      (specNorm S * √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) +
          frobNorm S * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)) ^ 2 +
        (specNorm S * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)) ^ 2 := by
  simp only [specNorm_pinv_mul_mul_eq]
  have h := integral_specNorm_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂ hrk Sᴴ
  rwa [specNorm_conjTranspose, frobNorm_conjTranspose] at h

end NLAlib
