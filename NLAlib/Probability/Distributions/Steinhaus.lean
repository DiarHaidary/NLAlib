/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Probability.HasLaw

/-!
# Steinhaus variables and vectors

`NLAlib.steinhausMeasure` is the law of a uniform random phase $e^{2\pi i \theta}$, the image of
Mathlib's Haar probability measure on the unit additive circle `AddCircle 1` under
`AddCircle.toCircle`. `NLAlib.steinhausVector n` is the law of a vector of independent phases, an
`abbrev` for the product, as `NLAlib.rademacherVector n` is for signs: the complex analogue of the
Rademacher law (`docs/design/Probability-P2.md` §3.2).

A Steinhaus variable $Z$ has $\lvert Z \rvert = 1$ surely, so $\mathbb{E}\lvert Z \rvert^2 =
\mathbb{E}\lvert Z \rvert^4 = 1$, and $\mathbb{E} Z = \mathbb{E} Z^2 = 0$: rotating the circle by a
quarter turn multiplies $Z$ by $i$ and preserves the law. These are the moment parameters
$s = 0$, $m_4 = 1$ of `NLAlib.integral_norm_quadForm_sub_trace_sq`.

## Main definitions

* `NLAlib.steinhausMeasure`, `NLAlib.steinhausVector n`.

## Main results

* `NLAlib.integral_steinhausMeasure`: the integral as one over the circle.
* `NLAlib.ae_norm_eq_one_of_hasLaw_steinhausMeasure`, `NLAlib.memLp_of_hasLaw_steinhausMeasure`.
* `NLAlib.integral_of_hasLaw_steinhausMeasure`, `NLAlib.integral_sq_of_hasLaw_steinhausMeasure`,
  `NLAlib.integral_norm_sq_of_hasLaw_steinhausMeasure`,
  `NLAlib.integral_norm_pow_four_of_hasLaw_steinhausMeasure`: the moments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory AddCircle Complex
open scoped ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {Z : Ω → ℂ}

private theorem continuous_coe_toCircle :
    Continuous fun θ : AddCircle (1 : ℝ) => ((toCircle θ : Circle) : ℂ) :=
  continuous_subtype_val.comp continuous_toCircle

/-- The **Steinhaus law**: a uniform random phase on the unit circle of $\mathbb{C}$, the image of
the Haar probability measure of `AddCircle 1` under $\theta \mapsto e^{2\pi i \theta}$.
[Epperly2023, Complex-Valued Test Vectors]. -/
noncomputable def steinhausMeasure : Measure ℂ :=
  (haarAddCircle (T := 1)).map fun θ => ((toCircle θ : Circle) : ℂ)

/-- The Steinhaus law is a probability measure. -/
instance isProbabilityMeasure_steinhausMeasure : IsProbabilityMeasure steinhausMeasure :=
  Measure.isProbabilityMeasure_map continuous_coe_toCircle.measurable.aemeasurable

/-- The law of a vector of independent uniform random phases. -/
noncomputable abbrev steinhausVector (n : Type*) [Fintype n] : Measure (n → ℂ) :=
  Measure.pi fun _ : n => steinhausMeasure

/-- An integral against the Steinhaus law is one over the circle:
$\int f \, d\nu = \int f(e^{2\pi i \theta}) \, d\theta$. -/
theorem integral_steinhausMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} (hf : AEStronglyMeasurable f steinhausMeasure) :
    ∫ z, f z ∂steinhausMeasure = ∫ θ, f (toCircle θ : ℂ) ∂(haarAddCircle (T := 1)) :=
  integral_map continuous_coe_toCircle.measurable.aemeasurable hf

/-- A Steinhaus variable has modulus $1$ almost surely. -/
theorem ae_norm_eq_one_of_hasLaw_steinhausMeasure (hZ : HasLaw Z steinhausMeasure μ) :
    ∀ᵐ ω ∂μ, ‖Z ω‖ = 1 := by
  have hS : MeasurableSet {z : ℂ | ‖z‖ = 1} :=
    measurableSet_eq_fun measurable_norm measurable_const
  rw [← ae_map_iff hZ.aemeasurable hS, hZ.map_eq, steinhausMeasure,
    ae_map_iff continuous_coe_toCircle.measurable.aemeasurable hS]
  exact ae_of_all _ fun θ => Circle.norm_coe _

/-- A Steinhaus variable is in every $L^p$. -/
theorem memLp_of_hasLaw_steinhausMeasure (hZ : HasLaw Z steinhausMeasure μ) (p : ℝ≥0∞) :
    MemLp Z p μ := by
  have := hZ.isProbabilityMeasure_iff.2 inferInstance
  exact MemLp.of_bound hZ.aemeasurable.aestronglyMeasurable 1
    ((ae_norm_eq_one_of_hasLaw_steinhausMeasure hZ).mono fun ω h => h.le)

/-- A quarter turn of the circle multiplies the phase by $i$. -/
private theorem coe_toCircle_quarter :
    ((toCircle ((1 / 4 : ℝ) : AddCircle (1 : ℝ)) : Circle) : ℂ) = I := by
  rw [toCircle_apply_mk, Circle.coe_exp]
  convert exp_pi_div_two_mul_I using 2
  push_cast
  ring

/-- $\int e^{2\pi i m \theta} \, d\theta = 0$ when $i^m \ne 1$: the quarter-turn invariance of the
Haar measure. -/
private theorem integral_coe_toCircle_pow {m : ℕ} (hm : I ^ m ≠ 1) :
    ∫ θ, ((toCircle θ : Circle) : ℂ) ^ m ∂(haarAddCircle (T := 1)) = 0 := by
  have h := integral_add_left_eq_self (μ := haarAddCircle (T := 1))
    (fun θ => ((toCircle θ : Circle) : ℂ) ^ m) ((1 / 4 : ℝ) : AddCircle (1 : ℝ))
  simp only [toCircle_add, Circle.coe_mul, mul_pow, coe_toCircle_quarter] at h
  rw [integral_const_mul] at h
  have h0 :
      (I ^ m - 1) * ∫ θ, ((toCircle θ : Circle) : ℂ) ^ m ∂(haarAddCircle (T := 1)) = 0 := by
    rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hm)

/-- A Steinhaus variable has mean zero. -/
theorem integral_of_hasLaw_steinhausMeasure (hZ : HasLaw Z steinhausMeasure μ) :
    ∫ ω, Z ω ∂μ = 0 := by
  rw [hZ.integral_eq, integral_steinhausMeasure (f := fun z => z) aestronglyMeasurable_id]
  simpa only [pow_one] using integral_coe_toCircle_pow (m := 1)
    (by rw [pow_one]; exact fun h => by simpa using congrArg Complex.re h)

/-- A Steinhaus variable has pseudo-variance zero: $\mathbb{E} Z^2 = 0$. -/
theorem integral_sq_of_hasLaw_steinhausMeasure (hZ : HasLaw Z steinhausMeasure μ) :
    ∫ ω, Z ω ^ 2 ∂μ = 0 := by
  have hc := hZ.integral_comp (f := fun z : ℂ => z ^ 2) (by fun_prop)
  simp only [Function.comp_def] at hc
  rw [hc, integral_steinhausMeasure (by fun_prop)]
  exact integral_coe_toCircle_pow (by rw [I_sq]; norm_num)

/-- A Steinhaus variable has second moment $\mathbb{E}\lvert Z \rvert^2 = 1$. -/
theorem integral_norm_sq_of_hasLaw_steinhausMeasure (hZ : HasLaw Z steinhausMeasure μ) :
    ∫ ω, ‖Z ω‖ ^ 2 ∂μ = 1 := by
  have := hZ.isProbabilityMeasure_iff.2 inferInstance
  rw [integral_congr_ae ((ae_norm_eq_one_of_hasLaw_steinhausMeasure hZ).mono
    fun ω (h : ‖Z ω‖ = 1) => show ‖Z ω‖ ^ 2 = (fun _ => (1 : ℝ)) ω by rw [h, one_pow])]
  simp

/-- A Steinhaus variable has fourth moment $\mathbb{E}\lvert Z \rvert^4 = 1$. -/
theorem integral_norm_pow_four_of_hasLaw_steinhausMeasure (hZ : HasLaw Z steinhausMeasure μ) :
    ∫ ω, ‖Z ω‖ ^ 4 ∂μ = 1 := by
  have := hZ.isProbabilityMeasure_iff.2 inferInstance
  rw [integral_congr_ae ((ae_norm_eq_one_of_hasLaw_steinhausMeasure hZ).mono
    fun ω (h : ‖Z ω‖ = 1) => show ‖Z ω‖ ^ 4 = (fun _ => (1 : ℝ)) ω by rw [h, one_pow])]
  simp

end NLAlib
