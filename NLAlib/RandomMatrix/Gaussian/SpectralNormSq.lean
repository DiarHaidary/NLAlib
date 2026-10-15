/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Probability.Independence.Tonelli
public import NLAlib.Probability.SubGaussian.Basic
public import NLAlib.RandomMatrix.Gaussian.SpectralNorm

/-!
# The second spectral moment of a Gaussian product

For a standard Gaussian $m \times n$ matrix $\mathbf{G}$ and fixed $\mathbf{S}$, $\mathbf{T}$,
$$\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_2^2 \le
(\|\mathbf{S}\|_2\|\mathbf{T}\|_{\mathsf{F}} + \|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_2)^2 +
\|\mathbf{S}\|_2^2\|\mathbf{T}\|_2^2\,:$$
the square of Chevet's first moment
(`NLAlib.integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix`) plus the variance, which
Gaussian concentration (`NLAlib.hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianMatrix`) bounds by
the square of the Lipschitz constant $\|\mathbf{S}\|_2\|\mathbf{T}\|_2$. With random factors
independent of $\mathbf{G}$ the bound holds conditionally, through the iterated integral
`ProbabilityTheory.IndepFun.lintegral_comp_eq_lintegral_lintegral`. Real throughout. A side file
that merges into `NLAlib/RandomMatrix/Gaussian/SpectralNorm.lean`, beside Chevet's inequality
(`docs/design/LowRank-S6.md` §4, L5 to L7).

## Main results

* `NLAlib.integrable_specNorm_mul_mul_sq_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_specNorm_mul_mul_sq_le_of_hasLaw_gaussianMatrix`: the second moment.
* `NLAlib.integral_specNorm_mul_mul_sq_le_of_hasLaw_gaussianMatrix_of_indepFun`: with random
  factors independent of the Gaussian matrix.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n a b : Type*} [Fintype m]
  [Fintype n] [Fintype a] [Fintype b] {X : Ω → Matrix m n ℝ}

/-- $\|\mathbf{S}\mathbf{A}\mathbf{T}\|_2$ is $\|\mathbf{S}\|_2 \|\mathbf{T}\|_2$-Lipschitz in
$\mathbf{A}$ for the Frobenius norm. -/
private theorem abs_specNorm_mul_mul_sub_le' (S : Matrix a m ℝ) (T : Matrix n b ℝ)
    (A B : Matrix m n ℝ) :
    |specNorm (S * A * T) - specNorm (S * B * T)| ≤
      ((⟨specNorm S * specNorm T, by positivity⟩ : ℝ≥0) : ℝ) * frobNorm (A - B) := by
  refine (abs_specNorm_sub_specNorm_le _ _).trans ?_
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  change _ ≤ specNorm S * specNorm T * frobNorm (A - B)
  calc specNorm (S * (A - B) * T) ≤ specNorm S * specNorm (A - B) * specNorm T :=
        (specNorm_mul_le _ _).trans (by gcongr; exact specNorm_mul_le _ _)
    _ ≤ specNorm S * frobNorm (A - B) * specNorm T := by gcongr; exact specNorm_le_frobNorm _
    _ = specNorm S * specNorm T * frobNorm (A - B) := by ring

/-- $\|\mathbf{S}\mathbf{G}\mathbf{T}\|_2$ minus its mean is sub-Gaussian with proxy
$\|\mathbf{S}\|_2^2\|\mathbf{T}\|_2^2$. -/
private theorem hasSubgaussianMGF_specNorm_mul_mul (hX : HasLaw X (gaussianMatrix m n) μ)
    (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    HasSubgaussianMGF (fun ω => specNorm (S * X ω * T) - ∫ ω', specNorm (S * X ω' * T) ∂μ)
      ((⟨specNorm S * specNorm T, by positivity⟩ : ℝ≥0) ^ 2) μ :=
  hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianMatrix hX (f := fun A => specNorm (S * A * T))
    (abs_specNorm_mul_mul_sub_le' S T)

/-- The squared spectral norm of $\mathbf{S}\mathbf{G}\mathbf{T}$ is integrable for a standard
Gaussian $\mathbf{G}$. -/
theorem integrable_specNorm_mul_mul_sq_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    Integrable (fun ω => specNorm (S * X ω * T) ^ 2) μ := by
  have := hX.isProbabilityMeasure
  set c := ∫ ω', specNorm (S * X ω' * T) ∂μ
  have hg : MemLp (fun ω => specNorm (S * X ω * T) - c) 2 μ :=
    (hasSubgaussianMGF_specNorm_mul_mul hX S T).memLp 2
  have hf : MemLp (fun ω => specNorm (S * X ω * T)) 2 μ := by
    convert hg.add (memLp_const c) using 1
    ext ω
    simp only [Pi.add_apply, sub_add_cancel]
  exact hf.integrable_sq

/-- **The second spectral moment of a Gaussian product**: for a standard Gaussian $\mathbf{G}$,
$$\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_2^2 \le
(\|\mathbf{S}\|_2\|\mathbf{T}\|_{\mathsf{F}} + \|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_2)^2 +
\|\mathbf{S}\|_2^2\|\mathbf{T}\|_2^2\,:$$
Chevet's first moment squared plus the variance, which Gaussian concentration bounds by the square
of the Lipschitz constant $\|\mathbf{S}\|_2\|\mathbf{T}\|_2$.
[TroppWebber2023, Lemma B.1]; there without the last term, by Slepian's lemma; here through
Gaussian concentration ([HalkoMartinssonTropp2011, Proposition 10.3]).
Result: chevet-inequality -/
theorem integral_specNorm_mul_mul_sq_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    ∫ ω, specNorm (S * X ω * T) ^ 2 ∂μ ≤
      (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 + (specNorm S * specNorm T) ^ 2 := by
  have := hX.isProbabilityMeasure
  have hg := hasSubgaussianMGF_specNorm_mul_mul hX S T
  set c := ∫ ω', specNorm (S * X ω' * T) ∂μ with hc
  have h0 := hg.integral_eq_zero
  have h2 := hg.integral_sq_le
  have hgi : Integrable (fun ω => specNorm (S * X ω * T) - c) μ := hg.integrable
  have hgi2 : Integrable (fun ω => (specNorm (S * X ω * T) - c) ^ 2) μ := (hg.memLp 2).integrable_sq
  have hc0 : 0 ≤ c := integral_nonneg fun _ => specNorm_nonneg _
  have hc1 : c ≤ specNorm S * frobNorm T + frobNorm S * specNorm T :=
    integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix hX S T
  have key : (fun ω => specNorm (S * X ω * T) ^ 2) =
      fun ω => (specNorm (S * X ω * T) - c) ^ 2 + (2 * c * (specNorm (S * X ω * T) - c) + c ^ 2) :=
    funext fun ω => by ring
  have hint : Integrable (fun ω => 2 * c * (specNorm (S * X ω * T) - c) + c ^ 2) μ :=
    (hgi.const_mul _).add (integrable_const _)
  have hint' : Integrable (fun ω => 2 * c * (specNorm (S * X ω * T) - c)) μ := hgi.const_mul _
  rw [key, integral_add hgi2 hint, integral_add hint' (integrable_const _), integral_const_mul, h0,
    integral_const, probReal_univ, one_smul]
  have h2' : ∫ ω, (specNorm (S * X ω * T) - c) ^ 2 ∂μ ≤ (specNorm S * specNorm T) ^ 2 := by
    exact_mod_cast h2
  nlinarith [mul_le_mul hc1 hc1 hc0 (by positivity)]

section Independent

variable {α : Type*} [MeasurableSpace α] {Y : Ω → α} {S : α → Matrix a m ℝ}
  {T : α → Matrix n b ℝ}

private theorem measurable_specNorm_mul_mul_sq (hS : Measurable S) (hT : Measurable T) :
    Measurable fun q : α × Matrix m n ℝ => specNorm (S q.1 * q.2 * T q.1) ^ 2 :=
  (continuous_specNorm.measurable.comp
    (((hS.comp measurable_fst).matrix_mul measurable_snd).matrix_mul
      (hT.comp measurable_fst))).pow_const 2

private theorem measurable_chevet_sq (hS : Measurable S) (hT : Measurable T) :
    Measurable fun y => (specNorm (S y) * frobNorm (T y) + frobNorm (S y) * specNorm (T y)) ^ 2 +
      (specNorm (S y) * specNorm (T y)) ^ 2 := by
  have h1 := continuous_specNorm.measurable.comp hS
  have h2 := continuous_frobNorm.measurable.comp hT
  have h3 := continuous_frobNorm.measurable.comp hS
  have h4 := continuous_specNorm.measurable.comp hT
  exact (((h1.mul h2).add (h3.mul h4)).pow_const 2).add ((h1.mul h4).pow_const 2)

/-- The second-moment bound under the joint law, as lower integrals. -/
private theorem lintegral_specNorm_mul_mul_sq_le (hY : AEMeasurable Y μ)
    (hX : HasLaw X (gaussianMatrix m n) μ) (hXY : IndepFun Y X μ) (hS : Measurable S)
    (hT : Measurable T) :
    ∫⁻ ω, ENNReal.ofReal (specNorm (S (Y ω) * X ω * T (Y ω)) ^ 2) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal ((specNorm (S (Y ω)) * frobNorm (T (Y ω)) +
        frobNorm (S (Y ω)) * specNorm (T (Y ω))) ^ 2 +
          (specNorm (S (Y ω)) * specNorm (T (Y ω))) ^ 2) ∂μ := by
  have := hX.isProbabilityMeasure
  have hF := ENNReal.measurable_ofReal.comp (measurable_specNorm_mul_mul_sq hS hT)
  have hG := ENNReal.measurable_ofReal.comp (measurable_chevet_sq hS hT)
  have hid : HasLaw (fun x : Matrix m n ℝ => x) (gaussianMatrix m n) (gaussianMatrix m n) :=
    HasLaw.id
  have hinner (y : α) :
      ∫⁻ x, ENNReal.ofReal (specNorm (S y * x * T y) ^ 2) ∂(gaussianMatrix m n) ≤
        ENNReal.ofReal ((specNorm (S y) * frobNorm (T y) + frobNorm (S y) * specNorm (T y)) ^ 2 +
          (specNorm (S y) * specNorm (T y)) ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_specNorm_mul_mul_sq_of_hasLaw_gaussianMatrix hid (S y) (T y))
      (ae_of_all _ fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (integral_specNorm_mul_mul_sq_le_of_hasLaw_gaussianMatrix hid (S y) (T y))
  calc ∫⁻ ω, ENNReal.ofReal (specNorm (S (Y ω) * X ω * T (Y ω)) ^ 2) ∂μ
      = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (specNorm (S y * x * T y) ^ 2) ∂(μ.map X) ∂(μ.map Y) :=
        hXY.lintegral_comp_eq_lintegral_lintegral hY hX.aemeasurable hF
    _ ≤ ∫⁻ y, ENNReal.ofReal ((specNorm (S y) * frobNorm (T y) +
          frobNorm (S y) * specNorm (T y)) ^ 2 + (specNorm (S y) * specNorm (T y)) ^ 2)
          ∂(μ.map Y) := by
        rw [hX.map_eq]
        exact lintegral_mono hinner
    _ = _ := lintegral_map' hG.aemeasurable hY

/-- **The second spectral moment with random factors** independent of the Gaussian matrix:
$$\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_2^2 \le
\mathbb{E}\bigl[(\|\mathbf{S}\|_2\|\mathbf{T}\|_{\mathsf{F}} +
\|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_2)^2 + \|\mathbf{S}\|_2^2\|\mathbf{T}\|_2^2\bigr]$$
when $\mathbf{S}$, $\mathbf{T}$ are measurable functions of a variable $Y$ independent of
$\mathbf{G}$; the conditional form of
`NLAlib.integral_specNorm_mul_mul_sq_le_of_hasLaw_gaussianMatrix`. The integrability hypothesis
`hST` excludes the junk value `0` of a non-integrable right side.
[TroppWebber2023, Lemma B.1]; [HalkoMartinssonTropp2011, proof of Theorem 10.6]; there the
fixed-factor form applied conditionally. -/
theorem integral_specNorm_mul_mul_sq_le_of_hasLaw_gaussianMatrix_of_indepFun
    (hY : AEMeasurable Y μ) (hX : HasLaw X (gaussianMatrix m n) μ) (hXY : IndepFun Y X μ)
    (hS : Measurable S) (hT : Measurable T)
    (hST : Integrable (fun ω => (specNorm (S (Y ω)) * frobNorm (T (Y ω)) +
      frobNorm (S (Y ω)) * specNorm (T (Y ω))) ^ 2 +
        (specNorm (S (Y ω)) * specNorm (T (Y ω))) ^ 2) μ) :
    ∫ ω, specNorm (S (Y ω) * X ω * T (Y ω)) ^ 2 ∂μ ≤
      ∫ ω, ((specNorm (S (Y ω)) * frobNorm (T (Y ω)) +
        frobNorm (S (Y ω)) * specNorm (T (Y ω))) ^ 2 +
          (specNorm (S (Y ω)) * specNorm (T (Y ω))) ^ 2) ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      ((measurable_specNorm_mul_mul_sq hS hT).comp_aemeasurable
        (hY.prodMk hX.aemeasurable)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => by positivity)
      hST.aestronglyMeasurable]
  exact ENNReal.toReal_mono hST.lintegral_lt_top.ne
    (lintegral_specNorm_mul_mul_sq_le hY hX hXY hS hT)

end Independent

end NLAlib
