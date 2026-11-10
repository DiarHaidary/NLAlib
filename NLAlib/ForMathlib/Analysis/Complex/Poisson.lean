/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The harmonic measure of a vertical strip

The density of strip harmonic measure, its normalization, its boundary limit, and the
corresponding probability measure. Upstream candidates for
`Mathlib.Analysis.Complex.Poisson`.

The proof adapts the original formalization in `tchen-research/NLAlib@77514ce`.

## Main results

* `Real.stripPoissonDensity`: the normalized density on a strip boundary.
-/

@[expose] public section

section

open MeasureTheory Set Filter
open scoped Topology

namespace Real

/-- The Stein–Hirschman boundary density for $0 < r < 1$ [SutterBertaTomamichel2017, Eq. (30)]. -/
noncomputable def stripPoissonDensity (r t : ℝ) : ℝ :=
  sin (π * r) / (2 * r * (cosh (π * t) + cos (π * r)))

/-- The limiting strip density as the interpolation parameter tends to zero. -/
noncomputable def stripPoissonDensityZero (t : ℝ) : ℝ := π / (2 * (cosh (π * t) + 1))

/-- An explicit primitive of the limiting strip density. -/
private noncomputable def hirschmanPrimitiveZero (t : ℝ) : ℝ := (1 + exp (-(π * t)))⁻¹

private theorem stripPoissonDensityZero_pos (t : ℝ) : 0 < stripPoissonDensityZero t := by
  exact div_pos pi_pos (mul_pos (by norm_num) (by linarith [cosh_pos (π * t)]))

/-- The limiting strip density is even. -/
@[simp] theorem stripPoissonDensityZero_neg (t : ℝ) :
    stripPoissonDensityZero (-t) = stripPoissonDensityZero t := by
  simp [stripPoissonDensityZero]

/-- The logistic primitive differentiates to precisely the displayed zero-parameter kernel. -/
private theorem hasDerivAt_hirschmanPrimitiveZero (t : ℝ) :
    HasDerivAt hirschmanPrimitiveZero (stripPoissonDensityZero t) t := by
  have hden : 1 + exp (-(π * t)) ≠ 0 := by positivity
  have h := (((hasDerivAt_id t).const_mul π).neg.exp.const_add 1).inv hden
  change HasDerivAt (fun x : ℝ => (1 + exp (-(π * x)))⁻¹)
    (-(exp (-(π * t)) * -(π * 1)) / (1 + exp (-(π * t))) ^ 2) t at h
  have h' : HasDerivAt (fun x : ℝ => (1 + exp (-(π * x)))⁻¹)
      (π * exp (-(π * t)) / (1 + exp (-(π * t))) ^ 2) t := by
    convert h using 1
    ring
  apply h'.congr_deriv
  dsimp [stripPoissonDensityZero]
  rw [cosh_eq, exp_neg]
  have he := exp_pos (π * t)
  field_simp
  ring

private theorem tendsto_hirschmanPrimitiveZero_atTop :
    Tendsto hirschmanPrimitiveZero atTop (𝓝 1) := by
  have he : Tendsto (fun t : ℝ => exp (-(π * t))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop pi_pos)
  change Tendsto (fun t : ℝ => (1 + exp (-(π * t)))⁻¹) atTop (𝓝 1)
  simpa only [add_zero, inv_one] using
    (tendsto_const_nhds.add he).inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)

private theorem tendsto_hirschmanPrimitiveZero_atBot :
    Tendsto hirschmanPrimitiveZero atBot (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  exact tendsto_const_nhds.add_atTop
    (tendsto_exp_atTop.comp (tendsto_neg_atBot_atTop.comp (tendsto_id.const_mul_atBot pi_pos)))

private theorem integrable_of_even_nonneg_primitive {f F : ℝ → ℝ} {l : ℝ}
    (hf : Function.Even f) (hnonneg : ∀ t, 0 ≤ f t)
    (hF : ∀ t, HasDerivAt F (f t) t) (htop : Tendsto F atTop (𝓝 l)) : Integrable f := by
  have hpos : IntegrableOn f (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hF t) (fun t _ => hnonneg t) htop
  have hci : IntegrableOn f (Ici (0 : ℝ)) := Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have hneg : IntegrableOn f (Iic (0 : ℝ)) := by
    have hci' : IntegrableOn f (Ici (-(0 : ℝ))) := by simpa only [neg_zero] using hci
    have h : IntegrableOn (fun t => f (-t)) (Iic (0 : ℝ)) := hci'.comp_neg_Iic
    have heq : (fun t => f (-t)) = f := funext hf
    rwa [heq] at h
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact integrableOn_union.mpr ⟨hneg, hpos⟩

/-- The limiting strip density is Lebesgue integrable. -/
theorem integrable_stripPoissonDensityZero : Integrable stripPoissonDensityZero :=
  integrable_of_even_nonneg_primitive stripPoissonDensityZero_neg
    (fun t => (stripPoissonDensityZero_pos t).le) hasDerivAt_hirschmanPrimitiveZero
    tendsto_hirschmanPrimitiveZero_atTop

/-- The limiting strip density has integral one. -/
theorem integral_stripPoissonDensityZero : (∫ t, stripPoissonDensityZero t) = 1 := by
  simpa using integral_of_hasDerivAt_of_tendsto hasDerivAt_hirschmanPrimitiveZero
    integrable_stripPoissonDensityZero tendsto_hirschmanPrimitiveZero_atBot
    tendsto_hirschmanPrimitiveZero_atTop

/-- The denominator in the exact interior strip density stays positive. -/
private theorem hirschmanDenominator_pos {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 < cosh (π * t) + cos (π * r) := by
  have hangle : π * r < π := by nlinarith [pi_pos, hr.2]
  have hc := cos_lt_cos_of_nonneg_of_le_pi (mul_pos pi_pos hr.1).le le_rfl hangle
  rw [cos_pi] at hc
  have hch : 1 ≤ cosh (π * t) := by
    nlinarith [cosh_sq (π * t), sq_nonneg (sinh (π * t)), cosh_pos (π * t)]
  linarith

/-- The interior strip density is strictly positive. -/
theorem stripPoissonDensity_pos {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    0 < stripPoissonDensity r t := by
  exact div_pos (sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1) (by nlinarith [pi_pos, hr.2]))
    (mul_pos (mul_pos (by norm_num) hr.1) (hirschmanDenominator_pos hr t))

/-- The strip density is even in the boundary coordinate. -/
@[simp] theorem stripPoissonDensity_neg (r t : ℝ) :
  stripPoissonDensity r (-t) = stripPoissonDensity r t := by
  simp [stripPoissonDensity]

/-- The exact arctangent primitive of the interior strip density. -/
private noncomputable def hirschmanPrimitive (r t : ℝ) : ℝ :=
  arctan ((exp (π * t) + cos (π * r)) / sin (π * r)) / (π * r)

private theorem hasDerivAt_hirschmanPrimitive {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    HasDerivAt (hirschmanPrimitive r) (stripPoissonDensity r t) t := by
  have hs : 0 < sin (π * r) :=
    sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1) (by nlinarith [pi_pos, hr.2])
  have h := (((((hasDerivAt_id t).const_mul π).exp.add_const (cos (π * r))).div_const
    (sin (π * r))).arctan).div_const (π * r)
  change HasDerivAt (hirschmanPrimitive r)
    ((1 / (1 + ((exp (π * t) + cos (π * r)) / sin (π * r)) ^ 2)) *
      (exp (π * t) * (π * 1) / sin (π * r)) / (π * r)) t at h
  apply h.congr_deriv
  unfold stripPoissonDensity
  rw [cosh_eq, exp_neg]
  have he := exp_pos (π * t)
  have hd := hirschmanDenominator_pos hr t
  have hpos : 0 < 1 + ((exp (π * t) + cos (π * r)) / sin (π * r)) ^ 2 := by positivity
  field_simp
  have hp : sin (π * r) ^ 2 + (exp (π * t) + cos (π * r)) ^ 2 =
      exp (π * t) ^ 2 + 1 + exp (π * t) * cos (π * r) * 2 := by
    nlinarith [sin_sq_add_cos_sq (π * r)]
  have hDp : 0 < exp (π * t) ^ 2 + 1 + exp (π * t) * cos (π * r) * 2 := by
    rw [← hp]
    positivity
  rw [hp]
  apply (eq_div_iff (mul_ne_zero (ne_of_gt hr.1) (ne_of_gt hDp))).2
  field_simp [ne_of_gt hr.1]

private theorem tendsto_hirschmanPrimitive_atTop {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Tendsto (hirschmanPrimitive r) atTop (𝓝 ((π / 2) / (π * r))) := by
  have hs : 0 < sin (π * r) :=
    sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1) (by nlinarith [pi_pos, hr.2])
  have hexp : Tendsto (fun t : ℝ => exp (π * t)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop pi_pos)
  have hin : Tendsto (fun t : ℝ => (exp (π * t) + cos (π * r)) / sin (π * r)) atTop atTop := by
    have hadd : Tendsto (fun t : ℝ => exp (π * t) + cos (π * r)) atTop atTop :=
      hexp.atTop_add tendsto_const_nhds
    simpa only [div_eq_mul_inv] using
      hadd.atTop_mul_const (inv_pos.2 hs)
  change Tendsto (fun t : ℝ => arctan ((exp (π * t) + cos (π * r)) / sin (π * r)) / (π * r)) _ _
  exact (((tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hin).div_const (π * r))

private theorem tendsto_hirschmanPrimitive_atBot {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Tendsto (hirschmanPrimitive r) atBot (𝓝 ((π / 2 - π * r) / (π * r))) := by
  have hs : 0 < sin (π * r) :=
    sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1) (by nlinarith [pi_pos, hr.2])
  have hexp : Tendsto (fun t : ℝ => exp (π * t)) atBot (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot pi_pos)
  have hc : arctan (cos (π * r) / sin (π * r)) = π / 2 - π * r := by
    rw [show cos (π * r) / sin (π * r) = tan (π / 2 - π * r) by
      rw [tan_pi_div_two_sub, tan_eq_sin_div_cos, inv_div]]
    apply arctan_tan <;> nlinarith [pi_pos, hr.1, hr.2]
  have hlim := ((continuous_arctan.tendsto _).comp
    ((hexp.add_const (cos (π * r))).div_const (sin (π * r)))).div_const (π * r)
  change Tendsto (fun t : ℝ => arctan ((exp (π * t) + cos (π * r)) / sin (π * r)) / (π * r)) _ _
  simpa only [Function.comp_def, zero_add, hc] using hlim

/-- The explicit interior strip kernel is Lebesgue integrable. -/
theorem integrable_stripPoissonDensity {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Integrable (stripPoissonDensity r) :=
  integrable_of_even_nonneg_primitive (stripPoissonDensity_neg r)
    (fun t => (stripPoissonDensity_pos hr t).le) (hasDerivAt_hirschmanPrimitive hr)
    (tendsto_hirschmanPrimitive_atTop hr)

/-- The interior strip density has integral one. -/
theorem integral_stripPoissonDensity {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    (∫ t, stripPoissonDensity r t) = 1 := by
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_hirschmanPrimitive hr)
    (integrable_stripPoissonDensity hr) (tendsto_hirschmanPrimitive_atBot hr)
    (tendsto_hirschmanPrimitive_atTop hr)]
  field_simp [ne_of_gt hr.1]
  ring

/-- The actual formula has the explicit zero-parameter density as its pointwise limit. -/
private theorem tendsto_stripPoissonDensity_zero (t : ℝ) :
    Tendsto (fun r => stripPoissonDensity r t) (𝓝[>] 0) (𝓝 (stripPoissonDensityZero t)) := by
  have heq : (fun r => stripPoissonDensity r t) =ᶠ[𝓝[>] 0]
      (fun r => π * sinc (π * r) / (2 * (cosh (π * t) + cos (π * r)))) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    rw [sinc_of_ne_zero (mul_ne_zero pi_ne_zero hr0), stripPoissonDensity]
    field_simp [hr0]
  apply Filter.Tendsto.congr' heq.symm
  have hcont : ContinuousAt (fun r : ℝ => π * sinc (π * r) /
      (2 * (cosh (π * t) + cos (π * r)))) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2)
        (by linarith [cosh_pos (π * t)] : 0 < cosh (π * t) + 1))
  simpa only [stripPoissonDensityZero, mul_zero, sinc_zero, cos_zero, mul_one] using
    hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- A common integrable majorant for the zero-parameter limit. The constant
is explicit, so bounded boundary logarithms admit ordinary dominated convergence. -/
private theorem stripPoissonDensity_le_two_mul_zero {r : ℝ} (hr : 0 < r)
    (hrhalf : r ≤ 1 / 2) (t : ℝ) :
    stripPoissonDensity r t ≤ 2 * stripPoissonDensityZero t := by
  have hangle : 0 ≤ π * r := (mul_pos pi_pos hr).le
  have hc : 0 ≤ cos (π * r) := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by
    nlinarith [pi_pos]⟩
  have hch : 1 ≤ cosh (π * t) := by
    nlinarith [cosh_sq (π * t), sq_nonneg (sinh (π * t)), cosh_pos (π * t)]
  have hs : 0 ≤ sin (π * r) := sin_nonneg_of_nonneg_of_le_pi hangle (by
    nlinarith [pi_pos])
  have hb : 0 < 2 * r * cosh (π * t) := mul_pos (mul_pos (by norm_num) hr) (cosh_pos _)
  calc
    stripPoissonDensity r t ≤ sin (π * r) / (2 * r * cosh (π * t)) := by
      exact div_le_div_of_nonneg_left hs hb (by
        have hprod : 0 ≤ (2 * r) * cos (π * r) := mul_nonneg (by positivity) hc
        nlinarith)
    _ ≤ (π * r) / (2 * r * cosh (π * t)) :=
      div_le_div_of_nonneg_right (sin_le hangle) hb.le
    _ = π / (2 * cosh (π * t)) := by field_simp
    _ ≤ 2 * stripPoissonDensityZero t := by
      calc
        _ ≤ π / (cosh (π * t) + 1) := div_le_div_of_nonneg_left pi_pos.le
          (by positivity) (by linarith)
        _ = _ := by unfold stripPoissonDensityZero; field_simp

/-- The explicit strip density is continuous in its integration variable. -/
@[fun_prop] theorem continuous_stripPoissonDensity {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Continuous (stripPoissonDensity r) := by
  unfold stripPoissonDensity
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    exact ne_of_gt (mul_pos (mul_pos (by norm_num) hr.1) (hirschmanDenominator_pos hr t))

/-- Integrals of bounded measurable functions against the strip density converge to the
integral against its limiting density as the interpolation parameter decreases to zero. -/
theorem tendsto_integral_stripPoissonDensity_smul_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : AEStronglyMeasurable f volume) {B : ℝ}
    (hbound : ∀ᵐ t, ‖f t‖ ≤ B) :
    Tendsto (fun r => ∫ t, stripPoissonDensity r t • f t) (𝓝[>] 0)
      (𝓝 (∫ t, stripPoissonDensityZero t • f t)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun t => (2 * B) * stripPoissonDensityZero t)
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with r hr
    exact ((continuous_stripPoissonDensity ⟨hr.1, by linarith [hr.2]⟩).aestronglyMeasurable).smul hf
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with r hr
    filter_upwards [hbound] with t ht
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (stripPoissonDensity_pos ⟨hr.1, by linarith [hr.2]⟩ t)]
    exact (mul_le_mul (stripPoissonDensity_le_two_mul_zero hr.1 hr.2.le t) ht (norm_nonneg _)
      (by positivity [stripPoissonDensityZero_pos t])).trans_eq (by ring)
  · exact integrable_stripPoissonDensityZero.const_mul _
  · exact ae_of_all _ (fun t => (tendsto_stripPoissonDensity_zero t).smul tendsto_const_nhds)

end Real

end

section

open MeasureTheory Set
namespace Real

/-- Harmonic measure on the right boundary of the unit strip, normalized to have mass one
for parameters strictly between zero and one. -/
noncomputable def stripHarmonicMeasure (r : ℝ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (stripPoissonDensity r t))

/-- The explicit density defines a probability measure, with its mass
computed from its antiderivative. -/
theorem isProbabilityMeasure_stripHarmonicMeasure {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    IsProbabilityMeasure (stripHarmonicMeasure r) := by
  constructor
  rw [stripHarmonicMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_stripPoissonDensity hr)
      (ae_of_all _ (fun t => (stripPoissonDensity_pos hr t).le)), integral_stripPoissonDensity hr]
  norm_num

/-- Integrating against normalized strip harmonic measure agrees with the Bochner integral
weighted by its density. -/
theorem integral_stripHarmonicMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (f : ℝ → E) :
    ∫ t, f t ∂stripHarmonicMeasure r = ∫ t, stripPoissonDensity r t • f t := by
  rw [stripHarmonicMeasure, integral_withDensity_eq_integral_toReal_smul
    (continuous_stripPoissonDensity hr).measurable.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (stripPoissonDensity_pos hr _).le]

/-- Every bounded measurable real observable is integrable against the
explicit normalized Stein--Hirschman density. -/
theorem integrable_stripPoissonDensity_mul_of_bounded {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hbound : ∀ t, |f t| ≤ B) :
    Integrable (fun t => stripPoissonDensity r t * f t) := by
  apply ((integrable_stripPoissonDensity hr).const_mul B).mono'
    (((continuous_stripPoissonDensity hr).measurable).mul hf).aestronglyMeasurable
  exact ae_of_all _ fun t => by
    dsimp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (stripPoissonDensity_pos hr t), Real.norm_eq_abs]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (hbound t) (stripPoissonDensity_pos hr t).le

end Real

end
