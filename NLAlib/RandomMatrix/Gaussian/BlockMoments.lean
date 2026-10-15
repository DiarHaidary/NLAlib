/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.InverseMoments.Spectral
public import NLAlib.RandomMatrix.Gaussian.Moments
public import NLAlib.RandomMatrix.Gaussian.SpectralNorm

/-!
# The block bound of the randomized range finder

For a standard Gaussian $n \times k$ test matrix $\mathbf{G}$, frames (orthonormal columns)
$\mathbf{V}_1$ of size $n \times r$ and $\mathbf{V}_2$ of size $n \times s$ with
$\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$, and a fixed $\mathbf{S}$, the blocks
$\mathbf{G}_1 = \mathbf{V}_1^{\mathsf{H}}\mathbf{G}$ and
$\mathbf{G}_2 = \mathbf{V}_2^{\mathsf{H}}\mathbf{G}$ are independent standard Gaussian matrices,
and
$\mathbb{E} \|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\|_{\mathsf{F}}^2
= \|\mathbf{S}\|_{\mathsf{F}}^2 \, r / (k - r - 1)$, writing $r$ and $k$ for the sizes of the
index types (Halko, Martinsson and Tropp 2011, proof of Theorem 10.5). The spectral-norm analogue
(their Theorem 10.6) is Chevet's inequality with factors independent of the Gaussian matrix
(`NLAlib.integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix_of_indepFun`) applied with
$\mathbf{T} = \mathbf{G}_1^{+}$, followed by the moments of $\mathbf{G}_1^{+}$:
$$\mathbb{E} \|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\|_2
\le \|\mathbf{S}\|_2 \, \mathbb{E} \|\mathbf{G}_1^{+}\|_{\mathsf{F}} +
  \|\mathbf{S}\|_{\mathsf{F}} \, \mathbb{E} \|\mathbf{G}_1^{+}\|_2 \,.$$

## Main definitions

* `NLAlib.gaussianProjectionFactor k l`: the factor $1 + \frac{k}{l - k - 1}$.

## Main results

* `NLAlib.integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix`: the transposed form.
* `NLAlib.integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix`: the spectral block bound;
  `NLAlib.integral_specNorm_mul_mul_pinv_le_add_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix`:
  the form of Halko, Martinsson and Tropp.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k r s a : Type*} [Fintype n]
  [Fintype k] [Fintype r] [Fintype s] [Fintype a] {X : Ω → Matrix n k ℝ}

/-! ### The Gaussian projection factor -/

/-- **The Gaussian projection factor** $1 + \frac{k}{l - k - 1}$ (casts to $\mathbb{R}$). For a
real $k \times l$ standard Gaussian matrix $\mathbf{G}$ it is
$1 + \mathbb{E}\|\mathbf{G}^{+}\|_{\mathsf{F}}^2$, the factor in front of the optimal Frobenius
error in the expected error of the randomized SVD [HalkoMartinssonTropp2011, Theorem 10.5], and
in Gaussian sketch-and-solve it is the completion factor $1 + \frac{q}{p - q - 1}$. Junk for
$l \le k + 1$, where the denominator is at most $0$ (and Lean's $x/0 = 0$ at $l = k + 1$);
theorems carry `k + 2 ≤ l`. A plain definition, because its body is the source's formula. -/
noncomputable def gaussianProjectionFactor (k l : ℕ) : ℝ := 1 + (k : ℝ) / ((l : ℝ) - k - 1)

/-- The body of `gaussianProjectionFactor`, as a simp lemma. -/
@[simp]
theorem gaussianProjectionFactor_def (k l : ℕ) :
    gaussianProjectionFactor k l = 1 + (k : ℝ) / ((l : ℝ) - k - 1) :=
  rfl

/-- The Gaussian projection factor is at least $1$ for $k + 2 \le l$. -/
theorem one_le_gaussianProjectionFactor {k l : ℕ} (h : k + 2 ≤ l) :
    1 ≤ gaussianProjectionFactor k l := by
  have h' : (k : ℝ) + 2 ≤ l := by exact_mod_cast h
  rw [gaussianProjectionFactor_def, le_add_iff_nonneg_right]
  exact div_nonneg (Nat.cast_nonneg k) (by linarith)

/-- The Gaussian projection factor is monotone in the target rank $k$ while $k + 2 \le l$. -/
theorem gaussianProjectionFactor_le_gaussianProjectionFactor {k k' l : ℕ} (hk : k ≤ k')
    (h : k' + 2 ≤ l) : gaussianProjectionFactor k l ≤ gaussianProjectionFactor k' l := by
  have hk' : (k : ℝ) ≤ k' := by exact_mod_cast hk
  have h' : (k' : ℝ) + 2 ≤ l := by exact_mod_cast h
  simp only [gaussianProjectionFactor_def, add_le_add_iff_left]
  exact div_le_div₀ (Nat.cast_nonneg _) hk' (by linarith) (by linarith)


omit [Fintype s] [Fintype a] in
private theorem hasLaw_conjTranspose_mul [DecidableEq r] (hX : HasLaw X (gaussianMatrix n k) μ)
    {V : Matrix n r ℝ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => Vᴴ * X ω) (gaussianMatrix r k) μ :=
  hasLaw_const_mul_of_hasLaw_gaussianMatrix hX (by rwa [Matrix.conjTranspose_conjTranspose])

private theorem integrable_chevet_pinv [DecidableEq r] (hX : HasLaw X (gaussianMatrix n k) μ)
    {V₁ : Matrix n r ℝ} (hV₁ : HasOrthonormalCols V₁) (hrk : Fintype.card r + 2 ≤ Fintype.card k)
    (S : Matrix a s ℝ) :
    Integrable (fun ω => specNorm S * frobNorm (pinv (V₁ᴴ * X ω)) +
      frobNorm S * specNorm (pinv (V₁ᴴ * X ω))) μ := by
  have hY := hasLaw_conjTranspose_mul hX hV₁
  have hspec := integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix hY one_pos
    (q := 1) (by linarith [show (Fintype.card r : ℝ) + 2 ≤ Fintype.card k by exact_mod_cast hrk])
  simp only [Real.rpow_one] at hspec
  exact ((integrable_frobNorm_pinv_of_hasLaw_gaussianMatrix hY hrk).const_mul _).add
    (hspec.const_mul _)

/-- The squared norm in the range finder's block bound is integrable. -/
theorem integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    Integrable (fun ω => frobNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ^ 2) μ := by
  have hY := hasLaw_conjTranspose_mul hX hV₁
  refine (integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun
    (hasLaw_conjTranspose_mul hX hV₂) hY.aemeasurable
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂)
    (S := fun _ => S) measurable_const measurable_pinv).2 ?_
  exact (integrable_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hY hrk).const_mul _

/-- **The range finder's block bound** (Halko, Martinsson and Tropp 2011, proof of
Theorem 10.5): for a standard Gaussian $n \times k$ matrix $\mathbf{G}$, frames $\mathbf{V}_1$
($n \times r$) and $\mathbf{V}_2$ ($n \times s$) with
$\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$, and $\lvert r \rvert + 2 \le \lvert k \rvert$,
$$\mathbb{E} \|\mathbf{S} (\mathbf{V}_2^{\mathsf{H}}\mathbf{G})
  (\mathbf{V}_1^{\mathsf{H}}\mathbf{G})^{+}\|_{\mathsf{F}}^2
= \frac{\|\mathbf{S}\|_{\mathsf{F}}^2 \lvert r \rvert}{\lvert k \rvert - \lvert r \rvert - 1} \,.$$
-/
theorem integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    ∫ ω, frobNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ^ 2 ∂μ =
      frobNorm S ^ 2 * Fintype.card r / ((Fintype.card k : ℝ) - Fintype.card r - 1) := by
  have hY := hasLaw_conjTranspose_mul hX hV₁
  refine (integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun
    (hasLaw_conjTranspose_mul hX hV₂) hY.aemeasurable
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂)
    (S := fun _ => S) measurable_const measurable_pinv).trans ?_
  rw [integral_const_mul, integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hY hrk, mul_div_assoc]

private theorem frobNorm_pinv_mul_mul_eq (A : Matrix n k ℝ) (V₁ : Matrix n r ℝ)
    (V₂ : Matrix n s ℝ) (S : Matrix s a ℝ) :
    frobNorm (pinv (Aᴴ * V₁) * (Aᴴ * V₂) * S) = frobNorm (Sᴴ * (V₂ᴴ * A) * pinv (V₁ᴴ * A)) := by
  rw [← frobNorm_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← pinv_conjTranspose,
    Matrix.mul_assoc]

/-- The squared norm in the transposed block bound is integrable. -/
theorem integrable_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix s a ℝ) :
    Integrable (fun ω => frobNorm (pinv ((X ω)ᴴ * V₁) * ((X ω)ᴴ * V₂) * S) ^ 2) μ := by
  simp only [frobNorm_pinv_mul_mul_eq]
  exact integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂ hrk Sᴴ

/-- **The transposed block bound** (Halko, Martinsson and Tropp 2011, proof of Theorem 10.5,
conjugate-transposed): under the hypotheses of
`integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix`,
$$\mathbb{E} \|(\mathbf{G}^{\mathsf{H}}\mathbf{V}_1)^{+} (\mathbf{G}^{\mathsf{H}}\mathbf{V}_2)
  \mathbf{S}\|_{\mathsf{F}}^2
= \frac{\|\mathbf{S}\|_{\mathsf{F}}^2 \lvert r \rvert}{\lvert k \rvert - \lvert r \rvert - 1} \,.$$
This is the form the Nyström approximation's completion step uses. -/
theorem integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix s a ℝ) :
    ∫ ω, frobNorm (pinv ((X ω)ᴴ * V₁) * ((X ω)ᴴ * V₂) * S) ^ 2 ∂μ =
      frobNorm S ^ 2 * Fintype.card r / ((Fintype.card k : ℝ) - Fintype.card r - 1) := by
  simp only [frobNorm_pinv_mul_mul_eq]
  rw [integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂ hrk Sᴴ,
    frobNorm_conjTranspose]

/-- The spectral norm in the range finder's block bound is integrable. -/
theorem integrable_specNorm_mul_mul_pinv_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    Integrable (fun ω => specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω))) μ := by
  exact integrable_specNorm_mul_mul_of_hasLaw_gaussianMatrix_of_indepFun
    (hasLaw_conjTranspose_mul hX hV₁).aemeasurable (hasLaw_conjTranspose_mul hX hV₂)
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂)
    (S := fun _ => S) measurable_const measurable_pinv (integrable_chevet_pinv hX hV₁ hrk S)

/-- **The range finder's spectral block bound**:
$\mathbb{E} \|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\|_2
\le \|\mathbf{S}\|_2 \, \mathbb{E} \|\mathbf{G}_1^{+}\|_{\mathsf{F}} +
\|\mathbf{S}\|_{\mathsf{F}} \, \mathbb{E} \|\mathbf{G}_1^{+}\|_2$ with
$\mathbf{G}_i = \mathbf{V}_i^{\mathsf{H}}\mathbf{G}$ and the moments of $\mathbf{G}_1^{+}$, that
is, under the hypotheses of `integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix`,
$$\mathbb{E} \|\mathbf{S} (\mathbf{V}_2^{\mathsf{H}}\mathbf{G})
  (\mathbf{V}_1^{\mathsf{H}}\mathbf{G})^{+}\|_2
\le \|\mathbf{S}\|_2 \sqrt{\frac{\lvert r \rvert}{\lvert k \rvert - \lvert r \rvert - 1}} +
  \|\mathbf{S}\|_{\mathsf{F}} \frac{e}{\lvert k \rvert - \lvert r \rvert}
  \sqrt{\frac{\lvert k \rvert + \lvert r \rvert - 1}{2}} \,.$$
[HalkoMartinssonTropp2011, proof of Theorem 10.6], there with
$e \sqrt{\lvert k \rvert} / (\lvert k \rvert - \lvert r \rvert)$ in the second term;
`NLAlib.integral_specNorm_mul_mul_pinv_le_add_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix`
is that form. -/
theorem integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    ∫ ω, specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ∂μ ≤
      specNorm S * √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) +
        frobNorm S * (Real.exp 1 / ((Fintype.card k : ℝ) - Fintype.card r) *
          √(((Fintype.card k : ℝ) + Fintype.card r - 1) / 2)) := by
  have hY := hasLaw_conjTranspose_mul hX hV₁
  have hrk' : Fintype.card r < Fintype.card k := by omega
  refine (integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix_of_indepFun hY.aemeasurable
    (hasLaw_conjTranspose_mul hX hV₂)
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂)
    (S := fun _ => S) measurable_const measurable_pinv
    (integrable_chevet_pinv hX hV₁ hrk S)).trans ?_
  have hspec := integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix hY one_pos
    (q := 1) (by linarith [show (Fintype.card r : ℝ) + 1 ≤ Fintype.card k by exact_mod_cast hrk'])
  simp only [Real.rpow_one] at hspec
  change ∫ ω, (specNorm S * frobNorm (pinv (V₁ᴴ * X ω)) +
    frobNorm S * specNorm (pinv (V₁ᴴ * X ω))) ∂μ ≤ _
  rw [integral_add ((integrable_frobNorm_pinv_of_hasLaw_gaussianMatrix hY hrk).const_mul _)
    (hspec.const_mul _), integral_const_mul, integral_const_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (integral_frobNorm_pinv_le_of_hasLaw_gaussianMatrix hY hrk)
      (specNorm_nonneg _))
    (mul_le_mul_of_nonneg_left (integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix hY hrk')
      (frobNorm_nonneg _))

/-- The spectral block bound in the form of Halko, Martinsson and Tropp,
$$\mathbb{E} \|\mathbf{S} (\mathbf{V}_2^{\mathsf{H}}\mathbf{G})
  (\mathbf{V}_1^{\mathsf{H}}\mathbf{G})^{+}\|_2
\le \|\mathbf{S}\|_2 \sqrt{\frac{\lvert r \rvert}{\lvert k \rvert - \lvert r \rvert - 1}} +
  \|\mathbf{S}\|_{\mathsf{F}} \frac{e \sqrt{\lvert k \rvert}}{\lvert k \rvert - \lvert r \rvert}
  \,.$$
[HalkoMartinssonTropp2011, Theorem 10.6]. It is dominated by
`NLAlib.integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix` and proved from it; it keeps
a name spelling its right side, as its moment bound
`NLAlib.integral_specNorm_pinv_le_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix` does, because
the range finder cites it (R4 §7 Q1, `docs/design/RandomMatrix-R4.md`). -/
theorem integral_specNorm_mul_mul_pinv_le_add_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix
    [DecidableEq r] [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    ∫ ω, specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ∂μ ≤
      specNorm S * √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) +
        frobNorm S * (Real.exp 1 * √(Fintype.card k : ℝ) /
          ((Fintype.card k : ℝ) - Fintype.card r)) := by
  have hrk' : (Fintype.card r : ℝ) + 2 ≤ Fintype.card k := by exact_mod_cast hrk
  refine (integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂ hrk S).trans ?_
  rw [div_mul_eq_mul_div]
  gcongr <;> linarith

end NLAlib
