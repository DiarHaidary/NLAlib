/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.Matrix.Structured.Kronecker
public import NLAlib.Probability.Distributions.ChiSquareMoments
public import NLAlib.Probability.Isotropic
public import NLAlib.RandomMatrix.Gaussian.Basic

/-!
# Second moments of random sketches

If the entries of a random matrix $\mathbf{X}$, read as a vector indexed by $m \times n$, are
isotropic, then
$\mathbb{E} \|\mathbf{S}\mathbf{X}\mathbf{T}\|_{\mathsf{F}}^2
= \|\mathbf{S}\|_{\mathsf{F}}^2 \|\mathbf{T}\|_{\mathsf{F}}^2$ for fixed $\mathbf{S}$ and
$\mathbf{T}$ (Halko, Martinsson and Tropp 2011, Proposition 10.1, for a Gaussian $\mathbf{X}$); the
proof writes $\mathbf{S}\mathbf{X}\mathbf{T}$ as $\mathbf{S} \otimes \mathbf{T}^{\mathsf{T}}$
applied to the entries and uses $\mathbb{E} \|\mathbf{A}\mathbf{y}\|^2
= \|\mathbf{A}\|_{\mathsf{F}}^2$ for an isotropic $\mathbf{y}$. The same holds when $\mathbf{S}$ and
$\mathbf{T}$ are random but independent of $\mathbf{X}$:
$\mathbb{E} \|\mathbf{S}\mathbf{X}\mathbf{T}\|_{\mathsf{F}}^2
= \mathbb{E}\bigl[\|\mathbf{S}\|_{\mathsf{F}}^2 \|\mathbf{T}\|_{\mathsf{F}}^2\bigr]$, which is the
conditioning step of the randomized range finder's error bound; the two sides are integrable
together.

The isotropic statements are over $\Bbbk$ and are stated at the root (their subject is
`Function.uncurry X`, so P0's `IsIsotropic` dot notation would not apply); the Gaussian ones are
their corollaries over $\mathbb{R}$.

## Main results

* `NLAlib.integral_frobNorm_mul_mul_sq_of_isIsotropic`.
* `NLAlib.integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_frobNorm_mul_mul_le_of_hasLaw_gaussianMatrix`: the Frobenius mean,
  $\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_{\mathsf{F}} \le
  \|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_{\mathsf{F}}$.
* `NLAlib.integral_frobNorm_pow_four_of_hasLaw_gaussianMatrix`: the fourth moment,
  $\mathbb{E}\|\mathbf{G}\|_{\mathsf{F}}^4 = d^2 + 2d$ with $d = \lvert m \rvert\lvert n \rvert$;
  `NLAlib.integrable_frobNorm_pow_four_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun`,
  `NLAlib.integrable_frobNorm_mul_mul_sq_iff_of_isIsotropic_of_indepFun`.
* `NLAlib.integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {m n a b : Type*} [Fintype m] [Fintype n] [Fintype a] [Fintype b]

section Isotropic

private theorem frobNorm_mul_mul_eq (S : Matrix a m 𝕜) (X : Matrix m n 𝕜) (T : Matrix n b 𝕜) :
    frobNorm (S * X * T) = ‖WithLp.toLp 2 ((S ⊗ₖ Tᵀ) *ᵥ Function.uncurry X)‖ := by
  rw [frobNorm_eq_norm_toLp_uncurry, uncurry_mul_mul]

variable [DecidableEq m] [DecidableEq n] {X : Ω → Matrix m n 𝕜}

/-- The squared Frobenius norm of a sketch with isotropic entries is integrable. -/
theorem integrable_frobNorm_mul_mul_sq_of_isIsotropic
    (hX : IsIsotropic (fun ω => Function.uncurry (X ω)) μ) (S : Matrix a m 𝕜) (T : Matrix n b 𝕜) :
    Integrable (fun ω => frobNorm (S * X ω * T) ^ 2) μ := by
  simp only [frobNorm_mul_mul_eq]
  exact hX.integrable_norm_mulVec_sq _

/-- The second moment of a sketch with isotropic entries: for fixed $\mathbf{S}$ and
$\mathbf{T}$,
$\mathbb{E} \|\mathbf{S}\mathbf{X}\mathbf{T}\|_{\mathsf{F}}^2
= \|\mathbf{S}\|_{\mathsf{F}}^2 \|\mathbf{T}\|_{\mathsf{F}}^2$. -/
theorem integral_frobNorm_mul_mul_sq_of_isIsotropic
    (hX : IsIsotropic (fun ω => Function.uncurry (X ω)) μ) (S : Matrix a m 𝕜) (T : Matrix n b 𝕜) :
    ∫ ω, frobNorm (S * X ω * T) ^ 2 ∂μ = frobNorm S ^ 2 * frobNorm T ^ 2 := by
  simp only [frobNorm_mul_mul_eq]
  rw [hX.integral_norm_mulVec_sq, frobNorm_kronecker, frobNorm_transpose, mul_pow]

variable [IsProbabilityMeasure μ] {ν : Measure (Matrix m n 𝕜)} {α : Type*} [MeasurableSpace α]
  {Y : Ω → α} {S : α → Matrix a m 𝕜} {T : α → Matrix n b 𝕜}

omit [DecidableEq m] [DecidableEq n] [IsProbabilityMeasure μ] in
private theorem measurable_frobNorm_mul_mul_sq (hS : Measurable S) (hT : Measurable T) :
    Measurable fun q : α × Matrix m n 𝕜 => frobNorm (S q.1 * q.2 * T q.1) ^ 2 :=
  (continuous_frobNorm.measurable.comp
    (((hS.comp measurable_fst).matrix_mul measurable_snd).matrix_mul
      (hT.comp measurable_fst))).pow_const 2

omit [DecidableEq m] [DecidableEq n] [IsProbabilityMeasure μ] in
private theorem measurable_frobNorm_sq_mul_frobNorm_sq (hS : Measurable S) (hT : Measurable T) :
    Measurable fun y => frobNorm (S y) ^ 2 * frobNorm (T y) ^ 2 :=
  ((continuous_frobNorm.measurable.comp hS).pow_const 2).mul
    ((continuous_frobNorm.measurable.comp hT).pow_const 2)

private theorem lintegral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun (hX : HasLaw X ν μ)
    (hν : IsIsotropic (fun x : Matrix m n 𝕜 => Function.uncurry x) ν) (hY : AEMeasurable Y μ)
    (hXY : IndepFun Y X μ) (hS : Measurable S) (hT : Measurable T) :
    ∫⁻ ω, ENNReal.ofReal (frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2) ∂μ =
      ∫⁻ ω, ENNReal.ofReal (frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2) ∂μ := by
  refine (hXY.lintegral_ofReal_comp_eq_lintegral_ofReal_integral hY hX
    (F := fun q : α × Matrix m n 𝕜 => frobNorm (S q.1 * q.2 * T q.1) ^ 2)
    (measurable_frobNorm_mul_mul_sq hS hT) (fun _ => sq_nonneg _)
    (ae_of_all _ fun ω => integrable_frobNorm_mul_mul_sq_of_isIsotropic (X := fun x => x) hν
      (S (Y ω)) (T (Y ω)))).trans (lintegral_congr fun ω => ?_)
  simp only [integral_frobNorm_mul_mul_sq_of_isIsotropic (X := fun x => x) hν]

/-- The second moment with independent random factors: if $\mathbf{X}$ has an isotropic law
and is independent of $Y$, and $\mathbf{S}$, $\mathbf{T}$ are measurable, then
$$\mathbb{E} \|\mathbf{S}(Y)\mathbf{X}\mathbf{T}(Y)\|_{\mathsf{F}}^2
= \mathbb{E}\bigl[\|\mathbf{S}(Y)\|_{\mathsf{F}}^2 \|\mathbf{T}(Y)\|_{\mathsf{F}}^2\bigr] \,.$$
A consumer with random factors `S T : Ω → Matrix` takes `Y := fun ω => (S ω, T ω)`. The identity
holds as stated even when the right side is not integrable (both sides are then $0$);
integrability transfers by
`integrable_frobNorm_mul_mul_sq_iff_of_isIsotropic_of_indepFun`. -/
theorem integral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun (hX : HasLaw X ν μ)
    (hν : IsIsotropic (fun x : Matrix m n 𝕜 => Function.uncurry x) ν) (hY : AEMeasurable Y μ)
    (hXY : IndepFun Y X μ) (hS : Measurable S) (hT : Measurable T) :
    ∫ ω, frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2 ∂μ =
      ∫ ω, frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2 ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      ((measurable_frobNorm_mul_mul_sq hS hT).comp_aemeasurable
        (hY.prodMk hX.aemeasurable)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      ((measurable_frobNorm_sq_mul_frobNorm_sq hS hT).comp_aemeasurable hY).aestronglyMeasurable,
    lintegral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun hX hν hY hXY hS hT]

/-- The two sides of `integral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun` are integrable
together. -/
theorem integrable_frobNorm_mul_mul_sq_iff_of_isIsotropic_of_indepFun (hX : HasLaw X ν μ)
    (hν : IsIsotropic (fun x : Matrix m n 𝕜 => Function.uncurry x) ν) (hY : AEMeasurable Y μ)
    (hXY : IndepFun Y X μ) (hS : Measurable S) (hT : Measurable T) :
    Integrable (fun ω => frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2) μ ↔
      Integrable (fun ω => frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2) μ := by
  have hL : AEStronglyMeasurable (fun ω => frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2) μ :=
    ((measurable_frobNorm_mul_mul_sq hS hT).comp_aemeasurable
      (hY.prodMk hX.aemeasurable)).aestronglyMeasurable
  have hR : AEStronglyMeasurable (fun ω => frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2) μ :=
    ((measurable_frobNorm_sq_mul_frobNorm_sq hS hT).comp_aemeasurable hY).aestronglyMeasurable
  rw [Integrable, Integrable, hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _),
    hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    lintegral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun hX hν hY hXY hS hT]
  simp only [hL, hR, true_and]

end Isotropic

section Gaussian

variable {X : Ω → Matrix m n ℝ}

/-- The second moment of a Gaussian sketch (Halko, Martinsson and Tropp 2011,
Proposition 10.1): for fixed $\mathbf{S}$ and $\mathbf{T}$,
$\mathbb{E} \|\mathbf{S}\mathbf{G}\mathbf{T}\|_{\mathsf{F}}^2
= \|\mathbf{S}\|_{\mathsf{F}}^2 \|\mathbf{T}\|_{\mathsf{F}}^2$. -/
theorem integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    ∫ ω, frobNorm (S * X ω * T) ^ 2 ∂μ = frobNorm S ^ 2 * frobNorm T ^ 2 := by
  classical
  exact integral_frobNorm_mul_mul_sq_of_isIsotropic
    (isIsotropic_of_hasLaw_gaussianVector (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX)) S T

private theorem memLp_frobNorm_mul_mul_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    MemLp (fun ω => frobNorm (S * X ω * T)) 2 μ := by
  classical
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hm : AEStronglyMeasurable (fun ω => frobNorm (S * X ω * T)) μ :=
    ((continuous_frobNorm.comp ((continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const)).measurable.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hm).2 (integrable_frobNorm_mul_mul_sq_of_isIsotropic
    (isIsotropic_of_hasLaw_gaussianVector (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX)) S T)

/-- $\|\mathbf{S}\mathbf{G}\mathbf{T}\|_{\mathsf{F}}$ is integrable for a standard Gaussian
matrix $\mathbf{G}$ and fixed $\mathbf{S}$, $\mathbf{T}$. -/
theorem integrable_frobNorm_mul_mul_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    Integrable (fun ω => frobNorm (S * X ω * T)) μ := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  exact (memLp_frobNorm_mul_mul_of_hasLaw_gaussianMatrix hX S T).integrable one_le_two

/-- **The Frobenius mean of a Gaussian sketch**: for a standard Gaussian matrix $\mathbf{G}$ and
fixed $\mathbf{S}$, $\mathbf{T}$,
$\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_{\mathsf{F}} \le \|\mathbf{S}\|_{\mathsf{F}}
\|\mathbf{T}\|_{\mathsf{F}}$, by Jensen from the second moment
`NLAlib.integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix`.
[HalkoMartinssonTropp2011, Proposition 10.1]; there the second moment, here its consequence. -/
theorem integral_frobNorm_mul_mul_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    ∫ ω, frobNorm (S * X ω * T) ∂μ ≤ frobNorm S * frobNorm T := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hvar := variance_nonneg (fun ω => frobNorm (S * X ω * T)) μ
  rw [variance_eq_sub (memLp_frobNorm_mul_mul_of_hasLaw_gaussianMatrix hX S T)] at hvar
  simp only [Pi.pow_apply] at hvar
  rw [integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix hX S T] at hvar
  refine (le_abs_self _).trans (abs_le_of_sq_le_sq' ?_ (by positivity)).2
  rw [mul_pow, sq_abs]
  linarith

private theorem frobNorm_pow_four_eq (A : Matrix m n ℝ) :
    frobNorm A ^ 4 = (‖WithLp.toLp 2 (Function.uncurry A)‖ ^ 2) ^ (2 : ℝ) := by
  rw [frobNorm_eq_norm_toLp_uncurry, Real.rpow_two, ← pow_mul]

private theorem neg_card_prod_div_two_lt_two : -((Fintype.card (m × n) : ℝ) / 2) < 2 := by
  have : (0 : ℝ) ≤ Fintype.card (m × n) := Nat.cast_nonneg _
  linarith

/-- $\|\mathbf{G}\|_{\mathsf{F}}^4$ is integrable for a standard Gaussian matrix
$\mathbf{G}$. -/
theorem integrable_frobNorm_pow_four_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) : Integrable (fun ω => frobNorm (X ω) ^ 4) μ :=
  (integrable_norm_sq_rpow_of_hasLaw_gaussianVector (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX)
    neg_card_prod_div_two_lt_two).congr (ae_of_all _ fun ω => (frobNorm_pow_four_eq (X ω)).symm)

/-- The fourth moment of the Frobenius norm of a Gaussian matrix: for a standard Gaussian
$m \times n$ matrix $\mathbf{G}$ and $d = \lvert m \rvert\lvert n \rvert$,
$\mathbb{E}\|\mathbf{G}\|_{\mathsf{F}}^4 = d^2 + 2d$, the second moment of $\chi^2_d$
(`NLAlib.integral_norm_sq_rpow_of_hasLaw_gaussianVector` at $s = 2$). -/
theorem integral_frobNorm_pow_four_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) :
    ∫ ω, frobNorm (X ω) ^ 4 ∂μ = ((Fintype.card m * Fintype.card n : ℕ) : ℝ) ^ 2 +
      2 * ((Fintype.card m * Fintype.card n : ℕ) : ℝ) := by
  simp only [frobNorm_pow_four_eq]
  rw [integral_norm_sq_rpow_of_hasLaw_gaussianVector (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX)
    neg_card_prod_div_two_lt_two, Fintype.card_prod, show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num]
  set d := ((Fintype.card m * Fintype.card n : ℕ) : ℝ)
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  rcases hd0.eq_or_lt with hd | hd
  · rw [← hd]
    simp
  have hΓ : Real.Gamma (d / 2 + 2) = (d / 2 + 1) * (d / 2) * Real.Gamma (d / 2) := by
    rw [show d / 2 + 2 = (d / 2 + 1) + 1 by ring, Real.Gamma_add_one (by positivity),
      Real.Gamma_add_one (by positivity)]
    ring
  have hG0 : Real.Gamma (d / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [hΓ]
  field_simp
  ring

variable {α : Type*} [MeasurableSpace α] {Y : Ω → α} {S : α → Matrix a m ℝ}
  {T : α → Matrix n b ℝ}

private theorem isIsotropic_uncurry_gaussianMatrix [DecidableEq m] [DecidableEq n] :
    IsIsotropic (fun x : Matrix m n ℝ => Function.uncurry x) (gaussianMatrix m n) :=
  isIsotropic_of_hasLaw_gaussianVector
    (hasLaw_uncurry_of_hasLaw_gaussianMatrix (HasLaw.id (μ := gaussianMatrix m n)))

/-- The second moment of a Gaussian sketch with independent random factors:
$\mathbb{E} \|\mathbf{S}(Y)\mathbf{G}\mathbf{T}(Y)\|_{\mathsf{F}}^2
= \mathbb{E}\bigl[\|\mathbf{S}(Y)\|_{\mathsf{F}}^2 \|\mathbf{T}(Y)\|_{\mathsf{F}}^2\bigr]$ for
$Y$ independent of $\mathbf{G}$. -/
theorem integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun
    (hX : HasLaw X (gaussianMatrix m n) μ) (hY : AEMeasurable Y μ) (hXY : IndepFun Y X μ)
    (hS : Measurable S) (hT : Measurable T) :
    ∫ ω, frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2 ∂μ =
      ∫ ω, frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2 ∂μ := by
  classical
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  exact integral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun hX
    isIsotropic_uncurry_gaussianMatrix hY hXY hS hT

/-- The two sides are integrable together, for a Gaussian sketch. -/
theorem integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun
    (hX : HasLaw X (gaussianMatrix m n) μ) (hY : AEMeasurable Y μ) (hXY : IndepFun Y X μ)
    (hS : Measurable S) (hT : Measurable T) :
    Integrable (fun ω => frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2) μ ↔
      Integrable (fun ω => frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2) μ := by
  classical
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  exact integrable_frobNorm_mul_mul_sq_iff_of_isIsotropic_of_indepFun hX
    isIsotropic_uncurry_gaussianMatrix hY hXY hS hT

end Gaussian

end NLAlib
