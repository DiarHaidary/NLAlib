/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import NLAlib.RandomMatrix.Gaussian.InverseMoments.Spectral
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlib.ForMathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Gaussian inverse moments split by the smallest singular value

Hölder combines the lower Gaussian singular-value tail with an arbitrary higher inverse moment.

## Main results

* `NLAlib.integral_specNorm_pinv_sq_le_add_exp_of_hasLaw_gaussianMatrix`.
* [Dimension-ratio bound](https://nla-lib.org/explore/#d/NLAlib.integral_specNorm_pinv_sq_le_div_of_hasLaw_gaussianMatrix_of_fourteen_mul_le).
-/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal
namespace NLAlib
variable {r t : Type*} [Fintype r] [Fintype t]

/-- Hölder combines a higher Gaussian inverse moment with the lower singular-value tail. -/
private theorem gaussian_pinv_bad_moment [Nonempty r]
    {p u : ℝ} (hp : 2 < p)
    (hpt : p ≤ (Fintype.card t : ℝ) - Fintype.card r) (hu : 0 < u) :
    ∫ A in {A : Matrix r t ℝ | singularValues Aᴴ (Fintype.card r - 1) ≤
        √(Fintype.card t : ℝ) - √(Fintype.card r : ℝ) - u},
      specNorm (pinv A) ^ 2 ∂gaussianMatrix r t ≤
        gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card t) ^ 2 *
          Real.exp (-u ^ 2 / 2 * (1 - 2 / p)) := by
  let ν := gaussianMatrix r t
  have hX : HasLaw (fun A : Matrix r t ℝ => A) ν ν := HasLaw.id
  have hp0 : 0 < p := by linarith
  have hrt : Fintype.card r < Fintype.card t := by
    have h : (Fintype.card r : ℝ) < Fintype.card t := by linarith
    exact_mod_cast h
  have hβ := gaussianPinvSpecNormBound_nonneg hrt
  have hmeas : AEStronglyMeasurable (fun A : Matrix r t ℝ => specNorm (pinv A)) ν :=
    (continuous_specNorm.measurable.comp measurable_pinv).aestronglyMeasurable
  have hint := integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix hX hp0 hpt
  have hmem : MemLp (fun A : Matrix r t ℝ => specNorm (pinv A)) (ENNReal.ofReal p) ν := by
    apply (integrable_norm_rpow_iff hmeas
      (by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hp0)
      ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hp0.le,
      Real.norm_of_nonneg (specNorm_nonneg _)] using hint
  have hB := measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix
    (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hX)
    (k := Fintype.card r - 1) (by have := Fintype.card_pos (α := r); omega) hu.le
  have hpow := integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix hX hp0 hpt
  rw [← gaussianPinvSpecNormBound_def] at hpow
  have hhold := setIntegral_sq_le_integral_rpow_mul_measureReal_rpow hp hmem
    (ae_of_all _ fun A => specNorm_nonneg (pinv A))
    {A : Matrix r t ℝ | singularValues Aᴴ (Fintype.card r - 1) ≤
      √(Fintype.card t : ℝ) - √(Fintype.card r : ℝ) - u}
  refine hhold.trans ?_
  have hexp : 0 ≤ 1 - 2 / p := by
    have : 2 / p < 1 := (div_lt_one hp0).mpr hp
    linarith
  have h1 := Real.rpow_le_rpow
    (integral_nonneg fun A => Real.rpow_nonneg (specNorm_nonneg (pinv A)) p) hpow
    (by positivity : 0 ≤ 2 / p)
  have h2 := Real.rpow_le_rpow (measureReal_nonneg) hB hexp
  have h3 := mul_le_mul h1 h2 (Real.rpow_nonneg measureReal_nonneg _) (Real.rpow_nonneg
    (Real.rpow_nonneg hβ p) _)
  refine h3.trans_eq ?_
  rw [← Real.rpow_mul hβ, show p * (2 / p) = 2 by field_simp,
    Real.rpow_two, ← Real.exp_mul]

/-- Split the second inverse moment into a bounded good part and a controlled exceptional part. -/
private theorem gaussian_pinv_split [Nonempty r]
    {p u : ℝ} (hp : 2 < p)
    (hpt : p ≤ (Fintype.card t : ℝ) - Fintype.card r) (hu : 0 < u)
    (hu' : u < √(Fintype.card t : ℝ) - √(Fintype.card r : ℝ)) :
    ∫ A : Matrix r t ℝ, specNorm (pinv A) ^ 2 ∂gaussianMatrix r t ≤
      (√(Fintype.card t : ℝ) - √(Fintype.card r : ℝ) - u)⁻¹ ^ 2 +
        gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card t) ^ 2 *
          Real.exp (-u ^ 2 / 2 * (1 - 2 / p)) := by
  classical
  let ν := gaussianMatrix r t
  have hX : HasLaw (fun A : Matrix r t ℝ => A) ν ν := HasLaw.id
  set c := √(Fintype.card t : ℝ) - √(Fintype.card r : ℝ) - u
  have hc : 0 < c := by dsimp only [c]; linarith
  set B := {A : Matrix r t ℝ | singularValues Aᴴ (Fintype.card r - 1) ≤ c}
  have hB : MeasurableSet B := measurableSet_le
    ((measurable_singularValues _).comp continuous_id.matrix_conjTranspose.measurable)
    measurable_const
  have hrt : Fintype.card r < Fintype.card t := by
    have h : (Fintype.card r : ℝ) < Fintype.card t := by linarith
    exact_mod_cast h
  have hint : Integrable (fun A : Matrix r t ℝ => specNorm (pinv A) ^ 2) ν := by
    have h := integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix hX two_pos
      (by linarith : (2 : ℝ) ≤ (Fintype.card t : ℝ) - Fintype.card r)
    simpa only [Real.rpow_two] using h
  have hgood : ∀ᵐ A ∂ν.restrict Bᶜ, specNorm (pinv A) ^ 2 ≤ c⁻¹ ^ 2 := by
    filter_upwards [ae_restrict_mem hB.compl,
      ae_restrict_of_ae (ae_rank_eq_min_of_hasLaw_gaussianMatrix hX)] with A hA hArank
    have hσ : c < singularValues Aᴴ (Fintype.card r - 1) := not_le.mp hA
    have hk : Fintype.card r - 1 + 1 = A.rank := by
      rw [hArank, min_eq_left hrt.le]
      have := Fintype.card_pos (α := r)
      omega
    rw [specNorm_pinv A hk, ← singularValues_conjTranspose A]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (singularValues_nonneg _ _))
      (inv_le_inv₀ (lt_trans hc hσ) hc |>.mpr hσ.le) 2
  have hg : ∫ A in Bᶜ, specNorm (pinv A) ^ 2 ∂ν ≤ c⁻¹ ^ 2 := by
    have h := integral_mono_ae hint.integrableOn (integrable_const (c⁻¹ ^ 2)) hgood
    rw [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ] at h
    exact h.trans (mul_le_of_le_one_left (sq_nonneg _) measureReal_le_one)
  have hb := gaussian_pinv_bad_moment hp hpt hu (r := r) (t := t)
  have he := integral_add_compl hB hint
  change (∫ A : Matrix r t ℝ, specNorm (pinv A) ^ 2 ∂ν) ≤ _
  change (∫ A in B, specNorm (pinv A) ^ 2 ∂ν) ≤ _ at hb
  dsimp only [c] at hg
  linarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {X : Ω → Matrix r t ℝ}

/-- The second spectral moment of a Gaussian pseudoinverse, split at a smallest-singular-value
threshold: for a standard Gaussian $r\times t$ matrix, $2<p\le t-r$ and
$0<u<\sqrt t-\sqrt r$,
$$\mathbb{E}\|\mathbf{G}^+\|_2^2\le(\sqrt t-\sqrt r-u)^{-2}
+\beta(r,t)^2\exp\bigl(-u^2(1-2/p)/2\bigr)\,,$$
where the existing spectral moment bound is <!-- value gaussianPinvSpecNormBound r t -->
$$\beta(r,t)=\frac{e}{t-r}\sqrt{(t+r-1)/2}\,.$$
No printed source. The Gaussian inputs are [HalkoMartinssonTropp2011, Proposition 10.4] and
[Vershynin2018, Corollary 7.3.3]. -/
theorem integral_specNorm_pinv_sq_le_add_exp_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r t) μ)
    {p u : ℝ} (hp : 2 < p)
    (hpt : p ≤ (Fintype.card t : ℝ) - Fintype.card r)
    (hu : 0 < u)
    (hu' : u < √(Fintype.card t : ℝ) - √(Fintype.card r : ℝ)) :
    ∫ ω, specNorm (pinv (X ω)) ^ 2 ∂μ ≤
      (√(Fintype.card t : ℝ) - √(Fintype.card r : ℝ) - u)⁻¹ ^ 2 +
        gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card t) ^ 2 *
          Real.exp (-u ^ 2 / 2 * (1 - 2 / p)) := by
  rcases isEmpty_or_nonempty r with hr | hr
  · have hz : ∀ A : Matrix r t ℝ, A = 0 := fun A => Subsingleton.elim _ _
    simp only [hz, pinv_zero, specNorm_zero, zero_pow two_ne_zero, integral_zero]
    positivity
  · have hm : AEStronglyMeasurable (fun A : Matrix r t ℝ => specNorm (pinv A) ^ 2)
        (gaussianMatrix r t) :=
      ((continuous_specNorm.measurable.comp measurable_pinv).pow_const 2).aestronglyMeasurable
    exact (hX.integral_comp hm).trans_le (gaussian_pinv_split hp hpt hu hu')
end NLAlib

namespace NLAlib
open MeasureTheory ProbabilityTheory
private theorem gaussian_gap {r t : ℝ} (ht : 2800 ≤ t)
    (hrt : 14 * r ≤ t) : 0.67 * √t ≤ √t - √r - 13 / 4 := by
  have ht0 : 0 ≤ t := by linarith
  have hs : √r ≤ 0.268 * √t := by
    apply Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt ht0]
    nlinarith
  have hu : (13 / 4 : ℝ) ≤ 0.062 * √t := by
    have hh := Real.sq_sqrt ht0
    have hn := Real.sqrt_nonneg t
    nlinarith
  linarith
private theorem gaussian_beta {r t : ℕ} (ht : 2800 ≤ t) (hrt : 14 * r ≤ t) :
    (t : ℝ) * NLAlib.gaussianPinvSpecNormBound r t ^ 2 ≤ 4.6 := by
  have ht' : (2800 : ℝ) ≤ t := by exact_mod_cast ht
  have hr' : 14 * (r : ℝ) ≤ t := by exact_mod_cast hrt
  have hd : (0 : ℝ) < t - r := by linarith
  have hsq : (0 : ℝ) ≤ ((t : ℝ) + r - 1) / 2 := by linarith
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have he2 : Real.exp 1 ^ 2 ≤ 7.3891 := by nlinarith
  rw [NLAlib.gaussianPinvSpecNormBound_def, mul_pow, div_pow, Real.sq_sqrt hsq]
  rw [show (t : ℝ) * (Real.exp 1 ^ 2 / ((t : ℝ) - r) ^ 2 *
      (((t : ℝ) + r - 1) / 2)) =
      Real.exp 1 ^ 2 * ((t : ℝ) * ((t : ℝ) + r - 1)) /
        (2 * ((t : ℝ) - r) ^ 2) by field_simp]
  rw [div_le_iff₀ (by positivity)]
  have h1 : (t : ℝ) * ((t : ℝ) + r - 1) ≤ 15 / 14 * (t : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hr' (by linarith : (0 : ℝ) ≤ t)]
  have h2 : (13 / 14 : ℝ) ^ 2 * (t : ℝ) ^ 2 ≤ ((t : ℝ) - r) ^ 2 := by
    have hh : 13 / 14 * (t : ℝ) ≤ (t : ℝ) - r := by linarith
    nlinarith [sq_nonneg ((t : ℝ) - r - 13 / 14 * t)]
  have h3 := mul_le_mul he2 h1 (mul_nonneg (Nat.cast_nonneg t) (by linarith))
    (by norm_num : (0 : ℝ) ≤ 7.3891)
  nlinarith
private theorem scaled_inverse_moment_le {t g β v : ℝ} (ht : 2800 ≤ t)
    (hgap : 0.67 * √t ≤ g) (hβ : t * β ^ 2 ≤ 4.6)
    (hv : v ≤ g⁻¹ ^ 2 + β ^ 2 * Real.exp (-(1521 / 320 : ℝ))) :
    v ≤ 2.3 / t := by
  have ht0 : 0 < t := by linarith
  have hg0 : 0 < g := lt_of_lt_of_le (mul_pos (by norm_num) (Real.sqrt_pos.mpr ht0)) hgap
  have hgs : (0.67 : ℝ) ^ 2 * t ≤ g ^ 2 := by
    have h := mul_self_le_mul_self (by positivity : 0 ≤ 0.67 * √t) hgap
    simpa only [← sq, mul_pow, Real.sq_sqrt ht0.le] using h
  have hg : t * g⁻¹ ^ 2 ≤ 1 / (0.67 : ℝ) ^ 2 := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (sq_pos_of_pos hg0)]
    nlinarith
  have hexp : Real.exp (-(1521 / 320 : ℝ)) ≤ 0.01 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1521 / 320) 8
    norm_num [Finset.sum_range_succ] at h
    have hh : (100 : ℝ) ≤ Real.exp (1521 / 320) := by linarith
    rw [Real.exp_neg]
    calc
      (Real.exp (1521 / 320))⁻¹ ≤ 1 / 100 := by
        simpa only [one_div] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) hh
      _ = 0.01 := by norm_num
  have hb : t * β ^ 2 * Real.exp (-(1521 / 320 : ℝ)) ≤ 4.6 * 0.01 :=
    mul_le_mul hβ hexp (Real.exp_pos _).le (by norm_num)
  have hvt := mul_le_mul_of_nonneg_right hv ht0.le
  apply (le_div_iff₀ ht0).mpr
  nlinarith
/-- A Gaussian inverse spectral second moment is at most 2.3 divided by the width
when the width is at least 2800 and fourteen times the height. -/
theorem integral_specNorm_pinv_sq_le_div_of_hasLaw_gaussianMatrix_of_fourteen_mul_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {r t : Type*} [Fintype r] [Fintype t] {X : Ω → Matrix r t ℝ}
    (hX : HasLaw X (gaussianMatrix r t) μ)
    (ht : 2800 ≤ Fintype.card t) (hrt : 14 * Fintype.card r ≤ Fintype.card t) :
    ∫ ω, specNorm (pinv (X ω)) ^ 2 ∂μ ≤ 2.3 / Fintype.card t := by
  have ht' : (2800 : ℝ) ≤ Fintype.card t := by exact_mod_cast ht
  have hr' : 14 * (Fintype.card r : ℝ) ≤ Fintype.card t := by exact_mod_cast hrt
  have hgap := gaussian_gap ht' hr'
  have hsqrt : 0 < √(Fintype.card t : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hu : (13 / 4 : ℝ) < √(Fintype.card t : ℝ) - √(Fintype.card r : ℝ) := by
    linarith
  have hp : (20 : ℝ) ≤ (Fintype.card t : ℝ) - Fintype.card r := by linarith
  have hs := integral_specNorm_pinv_sq_le_add_exp_of_hasLaw_gaussianMatrix
    hX (p := 20) (u := 13 / 4) (by norm_num) hp (by norm_num) hu
  norm_num at hs
  rw [← inv_pow] at hs
  exact scaled_inverse_moment_le ht' hgap (gaussian_beta ht hrt) hs
end NLAlib
