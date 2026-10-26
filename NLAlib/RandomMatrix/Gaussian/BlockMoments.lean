/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.InverseMoments.Frobenius
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
The second spectral moment of $\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}$ follows the same route,
conditionally on $\mathbf{G}_1$, through the second moment of a Gaussian product
(`NLAlib.integral_specNorm_mul_mul_sq_le_of_hasLaw_gaussianMatrix_of_indepFun`), then
Cauchy–Schwarz and the moments $\mathbb{E}\|\mathbf{G}_1^{+}\|_{\mathsf{F}}^2 = r/(k - r - 1)$
(`NLAlib.integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix`) and
`NLAlib.integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix` at exponent $2$. The transposed
forms are the sketch-and-solve noise.

## Main definitions

* `NLAlib.gaussianProjectionFactor k l`: the factor <!-- value gaussianProjectionFactor k l -->
  $1 + k/(l - k - 1)$.

## Main results

* `NLAlib.integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix`: the transposed form.
* `NLAlib.integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix`: the spectral block bound;
  `NLAlib.integral_specNorm_mul_mul_pinv_le_add_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix`:
  the form of Halko, Martinsson and Tropp.
* `NLAlib.integral_specNorm_mul_mul_pinv_mul_le_of_hasLaw_gaussianMatrix`: the spectral block
  bound with a factor on both sides.
* `NLAlib.integral_specNorm_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix`: the second spectral
  moment; `NLAlib.integral_specNorm_pinv_mul_mul_sq_le_of_hasLaw_gaussianMatrix`: the transposed
  form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k r s a b : Type*} [Fintype n]
  [Fintype k] [Fintype r] [Fintype s] [Fintype a] [Fintype b] {X : Ω → Matrix n k ℝ}

/-! ### The Gaussian projection factor -/

/-- **The Gaussian projection factor** <!-- value gaussianProjectionFactor k l -->
$1 + k/(l - k - 1)$ (casts to $\mathbb{R}$). For a
real $k \times l$ standard Gaussian matrix $\mathbf{G}$ it is
$1 + \mathbb{E}\|\mathbf{G}^{+}\|_{\mathsf{F}}^2$, the factor in front of the optimal Frobenius
error in the expected error of the randomized SVD [HalkoMartinssonTropp2011, Theorem 10.5], and
in Gaussian sketch-and-solve it is the completion factor $1 + q/(p - q - 1)$. Junk for
$l \le k + 1$, where the denominator is at most $0$ (and Lean's $x/0 = 0$ at $l = k + 1$);
theorems carry $k + 2 \le l$. A plain definition, because its body is the source's formula. -/
noncomputable def gaussianProjectionFactor (k l : ℕ) : ℝ := 1 + (k : ℝ) / ((l : ℝ) - k - 1)

/-- The body of `gaussianProjectionFactor`, <!-- value gaussianProjectionFactor k l -->
$1 + k/(l - k - 1)$, as a simp lemma. -/
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

/-- The Gaussian projection factor is bounded: for $q + 2 \le c$, the factor
satisfies <!-- value gaussianProjectionFactor q c --> $1 + q/(c - q - 1) \le 1 + c$, the bound
that makes the factor at a random rank integrable. -/
theorem gaussianProjectionFactor_le_one_add {q c : ℕ} (h : q + 2 ≤ c) :
    gaussianProjectionFactor q c ≤ 1 + c := by
  have h' : (q : ℝ) + 2 ≤ c := by exact_mod_cast h
  rw [gaussianProjectionFactor_def, add_le_add_iff_left, div_le_iff₀ (by linarith)]
  nlinarith

/-- The Gaussian projection factor is monotone in the target rank $k$ while $k + 2 \le l$. -/
theorem gaussianProjectionFactor_le_gaussianProjectionFactor {k k' l : ℕ} (hk : k ≤ k')
    (h : k' + 2 ≤ l) : gaussianProjectionFactor k l ≤ gaussianProjectionFactor k' l := by
  have hk' : (k : ℝ) ≤ k' := by exact_mod_cast hk
  have h' : (k' : ℝ) + 2 ≤ l := by exact_mod_cast h
  simp only [gaussianProjectionFactor_def, add_le_add_iff_left]
  exact div_le_div₀ (Nat.cast_nonneg _) hk' (by linarith) (by linarith)


/-- The Gaussian projection factor at $\ell \ge 3k/\varepsilon$: for $k \ge 1$,
$0 < \varepsilon \le 1$ and $3k/\varepsilon \le \ell$, the size condition $k + 2 \le \ell$ holds
and <!-- value gaussianProjectionFactor k \ell --> $1 + k/(\ell - k - 1) \le 1 + \varepsilon$. The
arithmetic of the asymptotic forms of the
expected-error bounds with HMT's factor. -/
theorem gaussianProjectionFactor_le_one_add_of_three_mul_div_le {k l : ℕ} {ε : ℝ} (hk : 0 < k)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hl : 3 * ((k : ℝ) / ε) ≤ l) :
    k + 2 ≤ l ∧ gaussianProjectionFactor k l ≤ 1 + ε := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl' : 3 * (k : ℝ) ≤ l * ε := by rwa [← mul_div_assoc, div_le_iff₀ hε] at hl
  have hεk := mul_le_mul_of_nonneg_right hε1 (Nat.cast_nonneg (α := ℝ) k)
  have hεl := mul_le_mul_of_nonneg_right hε1 (Nat.cast_nonneg (α := ℝ) l)
  have hkl : k + 2 ≤ l := by
    have : (k : ℝ) + 2 ≤ l := by linarith
    exact_mod_cast this
  refine ⟨hkl, ?_⟩
  have hden : 0 < (l : ℝ) - k - 1 := by linarith
  rw [gaussianProjectionFactor_def, add_le_add_iff_left, div_le_iff₀ hden]
  nlinarith


private theorem integrable_chevet_pinv [DecidableEq r] (hX : HasLaw X (gaussianMatrix n k) μ)
    {V₁ : Matrix n r ℝ} (hV₁ : HasOrthonormalCols V₁) (hrk : Fintype.card r + 2 ≤ Fintype.card k)
    (S : Matrix a s ℝ) :
    Integrable (fun ω => specNorm S * frobNorm (pinv (V₁ᴴ * X ω)) +
      frobNorm S * specNorm (pinv (V₁ᴴ * X ω))) μ := by
  have hY := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁
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
  have hY := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁
  refine (integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun
    (hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₂) hY.aemeasurable
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂)
    (S := fun _ => S) measurable_const measurable_pinv).2 ?_
  exact (integrable_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hY hrk).const_mul _

/-- The range finder's block bound (Halko, Martinsson and Tropp 2011, proof of
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
  have hY := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁
  refine (integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun
    (hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₂) hY.aemeasurable
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

/-- The transposed block bound (Halko, Martinsson and Tropp 2011, proof of Theorem 10.5,
conjugate-transposed): for a random
$\mathbf{G} \in \mathbb{R}^{n \times k}$ with independent standard Gaussian entries
(`HasLaw X (gaussianMatrix n k) μ`), $\mathbf{V}_1 \in \mathbb{R}^{n \times r}$ and
$\mathbf{V}_2 \in \mathbb{R}^{n \times s}$ with orthonormal columns and
$\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$, $\lvert r \rvert + 2 \le \lvert k \rvert$
and any $\mathbf{S} \in \mathbb{R}^{s \times a}$,
$$\mathbb{E} \|(\mathbf{G}^{\mathsf{H}}\mathbf{V}_1)^{+} (\mathbf{G}^{\mathsf{H}}\mathbf{V}_2)
  \mathbf{S}\|_{\mathsf{F}}^2
= \frac{\|\mathbf{S}\|_{\mathsf{F}}^2 \lvert r \rvert}{\lvert k \rvert - \lvert r \rvert - 1} \,.$$
The conjugate transpose of
`NLAlib.integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix`.
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
    (hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁).aemeasurable
    (hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₂)
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂)
    (S := fun _ => S) measurable_const measurable_pinv (integrable_chevet_pinv hX hV₁ hrk S)

/-- **The range finder's spectral block bound**: for a random
$\mathbf{G} \in \mathbb{R}^{n \times k}$ with independent standard Gaussian entries
(`HasLaw X (gaussianMatrix n k) μ`), $\mathbf{V}_1 \in \mathbb{R}^{n \times r}$ and
$\mathbf{V}_2 \in \mathbb{R}^{n \times s}$ with orthonormal columns and
$\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$, $\lvert r \rvert + 2 \le \lvert k \rvert$
and any $\mathbf{S} \in \mathbb{R}^{a \times s}$,
$$\mathbb{E} \|\mathbf{S} (\mathbf{V}_2^{\mathsf{H}}\mathbf{G})
  (\mathbf{V}_1^{\mathsf{H}}\mathbf{G})^{+}\|_2
\le \|\mathbf{S}\|_2 \sqrt{\frac{\lvert r \rvert}{\lvert k \rvert - \lvert r \rvert - 1}} +
  \|\mathbf{S}\|_{\mathsf{F}} \frac{e}{\lvert k \rvert - \lvert r \rvert}
  \sqrt{\frac{\lvert k \rvert + \lvert r \rvert - 1}{2}} \,.$$
With $\mathbf{G}_i = \mathbf{V}_i^{\mathsf{H}}\mathbf{G}$, it comes from
$\mathbb{E} \|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\|_2
\le \|\mathbf{S}\|_2 \, \mathbb{E} \|\mathbf{G}_1^{+}\|_{\mathsf{F}} +
\|\mathbf{S}\|_{\mathsf{F}} \, \mathbb{E} \|\mathbf{G}_1^{+}\|_2$ and the moments of
$\mathbf{G}_1^{+}$.
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
  have hY := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁
  have hrk' : Fintype.card r < Fintype.card k := by omega
  refine (integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix_of_indepFun hY.aemeasurable
    (hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₂)
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

/-- **The Gaussian block with factors on both sides**: for a random
$\mathbf{X} \in \mathbb{R}^{n \times k}$ with independent standard Gaussian entries,
$\mathbf{V}_1 \in \mathbb{R}^{n \times r}$ and $\mathbf{V}_2 \in \mathbb{R}^{n \times s}$ with
orthonormal columns and $\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$,
$\lvert r \rvert + 2 \le \lvert k \rvert$, $\mathbf{G}_i = \mathbf{V}_i^{\mathsf{H}}\mathbf{X}$
and any $\mathbf{S} \in \mathbb{R}^{a \times s}$, $\mathbf{T} \in \mathbb{R}^{r \times b}$,
with $r$, $k$ standing for $\lvert r \rvert$, $\lvert k \rvert$ and the constant
`gaussianPinvSpecNormBound` written out, <!-- value gaussianPinvSpecNormBound r k -->
$$\mathbb{E}\|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\mathbf{T}\|_2 \le
\frac{e}{k - r}\sqrt{(k + r - 1)/2}\,\bigl(\|\mathbf{S}\|_2\|\mathbf{T}\|_{\mathsf{F}} +
\|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_2\bigr)\,.$$
No printed source; the two-sided form of [HalkoMartinssonTropp2011, proof of Theorem 10.6]. -/
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

/-- **The second spectral moment of the transposed Gaussian block**: for a random
$\mathbf{X} \in \mathbb{R}^{n \times k}$ with independent standard Gaussian entries
(`HasLaw X (gaussianMatrix n k) μ`), $\mathbf{V}_1 \in \mathbb{R}^{n \times r}$ and
$\mathbf{V}_2 \in \mathbb{R}^{n \times s}$ with orthonormal columns and
$\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$, $\lvert r \rvert + 2 \le \lvert k \rvert$
and any $\mathbf{S} \in \mathbb{R}^{s \times a}$,
with $\mathbf{G}_i = \mathbf{V}_i^{\mathsf{H}}\mathbf{X}$, $r = \lvert r \rvert$ and
$k = \lvert k \rvert$, the sketch-and-solve noise
satisfies <!-- value gaussianPinvSpecNormBound r k -->
$$\mathbb{E}\|\mathbf{G}_1^{\mathsf{H}+}\mathbf{G}_2^{\mathsf{H}}\mathbf{S}\|_2^2 \le
\Bigl(\|\mathbf{S}\|_2\sqrt{\tfrac{r}{k-r-1}} +
\|\mathbf{S}\|_{\mathsf{F}}\,\frac{e}{k - r}\sqrt{(k + r - 1)/2}\Bigr)^2 +
\|\mathbf{S}\|_2^2\Bigl(\frac{e}{k - r}\sqrt{(k + r - 1)/2}\Bigr)^2\,,$$
where $\mathbf{G}_1^{\mathsf{H}+} = (\mathbf{G}_1^{\mathsf{H}})^{+}$ and the constant is
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
