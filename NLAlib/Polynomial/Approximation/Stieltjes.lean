/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Pow.Real
-- proof only (the representation of `x ^ p`, `p ∈ (0, 1)`):
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
# Stieltjes functions

A function $f$ is a **Stieltjes function** if
$$f(z) = \int_{[0, \infty)} \frac{1}{z + t}\,d\mu(t), \qquad z > 0,$$
for a positive measure $\mu$ on $[0, \infty)$ with $\int (1 + t)^{-1}\,d\mu(t) < \infty$. The
inverse $z^{-1}$ ($\mu = \delta_0$), the shifted inverses $(z + s)^{-1}$ ($\mu = \delta_s$), their
nonnegative combinations and the powers $z^{-\gamma}$, $0 < \gamma < 1$, are Stieltjes. The class
is the one of Lanczos-FA near-optimality
(`Matrix.IsHermitian.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le`).

The class is the paper's: no constant and no linear term are added to the integral.
Constants are reached through the second class of the near-optimality theorems ($f(z)/z = c/z$
is Stieltjes, the atom $c\,\delta_0$); a sum $c + g$ with $g$ Stieltjes is a trivial corollary,
to be added only when a consumer needs it.

Only the values on $(0, \infty)$ are constrained, since only they reach a function of a positive
definite matrix. The measure is a measure on $\mathbb{R}$ that vanishes on $(-\infty, 0)$.
Mathlib's `StieltjesFunction` is a different object (the distribution function of a
Lebesgue–Stieltjes measure); Mathlib's `MeasureTheory.resolventTransform` is the Stieltjes
transform of a measure, and `HasStieltjesMeasure.apply_eq_resolventTransform` is the bridge.

## Main definitions

* `NLAlib.HasStieltjesMeasure f μ`: $f$ is represented by $\mu$.
* `NLAlib.IsStieltjes f`: some measure represents $f$.

## Main results

* `NLAlib.HasStieltjesMeasure.ae_nonneg`, `.integrable_inv_add`: the measure is carried by
  $[0, \infty)$ and each kernel $(z + t)^{-1}$, $z > 0$, is integrable.
* `NLAlib.HasStieltjesMeasure.nonneg`, `.antitoneOn`, `.monotoneOn_id_mul`: $f \ge 0$,
  $f$ is non-increasing and $z f(z)$ is non-decreasing on $(0, \infty)$.
* `NLAlib.HasStieltjesMeasure.mul_le_mul_of_ae_le`: a ratio bound on the kernel
  $\nu(z)/(z + t)$, for $\mu$-almost every $t \ge 0$, passes to $\nu f$.
* `NLAlib.HasStieltjesMeasure.rpow_mul_le`: on $[a, a']$,
  $x^\alpha f(x) \le (a'/a)^{\max(\alpha, 1 - \alpha)}\, y^\alpha f(y)$, from the kernel
  inequality `Real.rpow_mul_add_le`.
* Instances: `NLAlib.hasStieltjesMeasure_inv`, `NLAlib.hasStieltjesMeasure_inv_add`,
  `NLAlib.HasStieltjesMeasure.add`, `NLAlib.HasStieltjesMeasure.smul`,
  `NLAlib.isStieltjes_rpow_neg`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace NLAlib

/-- **A measure representing a Stieltjes function**: $\mu$ is a positive measure on
$[0, \infty)$ (it vanishes on $(-\infty, 0)$) with $\int (1 + t)^{-1}\,d\mu(t) < \infty$, and
$f(z) = \int (z + t)^{-1}\,d\mu(t)$ for every $z > 0$. Values of $f$ at $z \le 0$ are
unconstrained. [ChenPersson2026, (6)]. -/
structure HasStieltjesMeasure (f : ℝ → ℝ) (μ : Measure ℝ) : Prop where
  /-- The measure lives on $[0, \infty)$. -/
  measure_Iio : μ (Set.Iio 0) = 0
  /-- $\int (1 + t)^{-1}\,d\mu(t) < \infty$. -/
  integrable : Integrable (fun t => (1 + t)⁻¹) μ
  /-- The representation on $(0, \infty)$. -/
  eq_integral : ∀ z, 0 < z → f z = ∫ t, (z + t)⁻¹ ∂μ

/-- A **Stieltjes function**: $f(z) = \int_{[0,\infty)} (z + t)^{-1}\,d\mu(t)$ on $(0, \infty)$
for some positive measure $\mu$ with $\int (1 + t)^{-1}\,d\mu(t) < \infty$.
[ChenPersson2026, (6)]. -/
def IsStieltjes (f : ℝ → ℝ) : Prop :=
  ∃ μ : Measure ℝ, HasStieltjesMeasure f μ

variable {f g : ℝ → ℝ} {μ ν : Measure ℝ}

/-- A representing measure is carried by $[0, \infty)$: almost every $t$ is nonnegative. -/
theorem HasStieltjesMeasure.ae_nonneg (hf : HasStieltjesMeasure f μ) : ∀ᵐ t ∂μ, 0 ≤ t := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hf.measure_Iio] with t ht
  exact not_lt.mp ht

/-- The kernel $(z + t)^{-1}$ is integrable for every $z > 0$. -/
theorem HasStieltjesMeasure.integrable_inv_add (hf : HasStieltjesMeasure f μ) {z : ℝ}
    (hz : 0 < z) : Integrable (fun t => (z + t)⁻¹) μ := by
  refine (hf.integrable.const_mul (1 + z⁻¹)).mono'
    ((measurable_const.add measurable_id).inv.aestronglyMeasurable) ?_
  filter_upwards [hf.ae_nonneg] with t ht
  have hzt : 0 < z + t := by linarith
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hzt.le), ← div_eq_mul_inv, le_div_iff₀ (by linarith),
    inv_mul_le_iff₀ hzt]
  have h1 : z * z⁻¹ = 1 := mul_inv_cancel₀ hz.ne'
  have h2 : 0 ≤ t * z⁻¹ := by positivity
  nlinarith

/-- Only the values on $(0, \infty)$ matter. -/
theorem HasStieltjesMeasure.congr (hf : HasStieltjesMeasure f μ)
    (h : ∀ z, 0 < z → f z = g z) : HasStieltjesMeasure g μ :=
  ⟨hf.measure_Iio, hf.integrable, fun z hz => (h z hz).symm.trans (hf.eq_integral z hz)⟩

/-- Bridge to Mathlib's Stieltjes transform: $f(z)$ is the resolvent transform of $\mu$ at
$-z$. -/
theorem HasStieltjesMeasure.apply_eq_resolventTransform (hf : HasStieltjesMeasure f μ) {z : ℝ}
    (hz : 0 < z) : f z = resolventTransform μ (-z) := by
  rw [hf.eq_integral z hz, resolventTransform_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [resolvent, Algebra.algebraMap_self, RingHom.id_apply, sub_neg_eq_add,
    Ring.inverse_eq_inv', add_comm z t]

/-- A Stieltjes function is nonnegative on $(0, \infty)$. -/
theorem HasStieltjesMeasure.nonneg (hf : HasStieltjesMeasure f μ) {z : ℝ} (hz : 0 < z) :
    0 ≤ f z := by
  rw [hf.eq_integral z hz]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hf.ae_nonneg] with t ht
  exact inv_nonneg.mpr (by linarith)

/-- A Stieltjes function with a nonzero measure is positive on $(0, \infty)$. -/
theorem HasStieltjesMeasure.pos (hf : HasStieltjesMeasure f μ) (hμ : μ ≠ 0) {z : ℝ}
    (hz : 0 < z) : 0 < f z := by
  rw [hf.eq_integral z hz]
  have hpos : ∀ᵐ t ∂μ, 0 < (z + t)⁻¹ := by
    filter_upwards [hf.ae_nonneg] with t ht
    exact inv_pos.mpr (by linarith)
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun t ht => ht.le)
    (hf.integrable_inv_add hz)]
  have hsupp : (Function.support fun t : ℝ => (z + t)⁻¹)ᶜ ⊆ {t | ¬ 0 < (z + t)⁻¹} :=
    fun t ht => by
      simp only [Function.mem_support, not_not, Set.mem_compl_iff] at ht
      simp only [Set.mem_ofPred_eq, ht, lt_irrefl, not_false_eq_true]
  have h0 : μ (Function.support fun t : ℝ => (z + t)⁻¹)ᶜ = 0 :=
    measure_mono_null hsupp (ae_iff.mp hpos)
  by_contra hle
  have h1 : μ (Function.support fun t : ℝ => (z + t)⁻¹) = 0 := by
    simpa using hle
  have := measure_union_null h1 h0
  rw [Set.union_compl_self, Measure.measure_univ_eq_zero] at this
  exact hμ this

/-- A Stieltjes function is non-increasing on $(0, \infty)$. -/
theorem HasStieltjesMeasure.antitoneOn (hf : HasStieltjesMeasure f μ) :
    AntitoneOn f (Set.Ioi 0) := by
  intro x hx y hy hxy
  rw [hf.eq_integral x hx, hf.eq_integral y hy]
  refine integral_mono_ae (hf.integrable_inv_add hy) (hf.integrable_inv_add hx) ?_
  filter_upwards [hf.ae_nonneg] with t ht
  have hx' : (0 : ℝ) < x := hx
  exact inv_anti₀ (by linarith) (by linarith)

/-- $z \mapsto z f(z)$ is non-decreasing on $(0, \infty)$ for a Stieltjes function $f$. -/
theorem HasStieltjesMeasure.monotoneOn_id_mul (hf : HasStieltjesMeasure f μ) :
    MonotoneOn (fun z => z * f z) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  simp only
  rw [hf.eq_integral x hx, hf.eq_integral y hy, ← integral_const_mul, ← integral_const_mul]
  refine integral_mono_ae ((hf.integrable_inv_add hx').const_mul x)
    ((hf.integrable_inv_add hy').const_mul y) ?_
  filter_upwards [hf.ae_nonneg] with t ht
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Ratio bounds pass from the kernel to the function: if
$w(x)(y + t) \le R\,w(y)(x + t)$ for $\mu$-almost every $t \ge 0$, that is
$w(x)/(x + t) \le R\,w(y)/(y + t)$ on the support of $\mu$, then
$w(x) f(x) \le R\,w(y) f(y)$. -/
theorem HasStieltjesMeasure.mul_le_mul_of_ae_le (hf : HasStieltjesMeasure f μ)
    {w : ℝ → ℝ} {R x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : ∀ᵐ t ∂μ, 0 ≤ t → w x * (y + t) ≤ R * (w y * (x + t))) :
    w x * f x ≤ R * (w y * f y) := by
  rw [hf.eq_integral x hx, hf.eq_integral y hy, ← integral_const_mul, ← integral_const_mul,
    ← integral_const_mul]
  refine integral_mono_ae ((hf.integrable_inv_add hx).const_mul _)
    (((hf.integrable_inv_add hy).const_mul _).const_mul _) ?_
  filter_upwards [hf.ae_nonneg, h] with t ht hkt
  have hxt : 0 < x + t := by linarith
  have hyt : 0 < y + t := by linarith
  have := hkt ht
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, ← mul_div_assoc, div_le_div_iff₀ hxt hyt]
  linarith

/-- **Weighted Stieltjes functions vary by at most $(a'/a)^{\max(\alpha, 1 - \alpha)}$ on
$[a, a']$**: for a Stieltjes function $f$, $0 < a$, $x, y \in [a, a']$ and real $\alpha$,
$x^\alpha f(x) \le (a'/a)^{\max(\alpha, 1 - \alpha)}\, y^\alpha f(y)$.
[ChenPersson2026, Lemma 6]. -/
theorem HasStieltjesMeasure.rpow_mul_le (hf : HasStieltjesMeasure f μ) {a a' x y : ℝ}
    (ha : 0 < a) (hx : x ∈ Set.Icc a a') (hy : y ∈ Set.Icc a a') (α : ℝ) :
    x ^ α * f x ≤ (a' / a) ^ max α (1 - α) * (y ^ α * f y) :=
  hf.mul_le_mul_of_ae_le (w := fun z => z ^ α) (ha.trans_le hx.1) (ha.trans_le hy.1)
    (Filter.Eventually.of_forall fun _ ht => Real.rpow_mul_add_le ha hx hy ht α)

/-- The **inverse** is a Stieltjes function, with $\mu = \delta_0$. -/
theorem hasStieltjesMeasure_inv : HasStieltjesMeasure (fun z => z⁻¹) (Measure.dirac 0) := by
  refine ⟨?_, ?_, fun z _ => ?_⟩
  · rw [Measure.dirac_apply' _ measurableSet_Iio, Set.indicator_of_notMem (by simp)]
  · exact integrable_dirac (by simp)
  · rw [integral_dirac, add_zero]

/-- A **shifted inverse** $(z + s)^{-1}$, $s \ge 0$, is a Stieltjes function, with
$\mu = \delta_s$. -/
theorem hasStieltjesMeasure_inv_add {s : ℝ} (hs : 0 ≤ s) :
    HasStieltjesMeasure (fun z => (z + s)⁻¹) (Measure.dirac s) := by
  refine ⟨?_, ?_, fun z _ => ?_⟩
  · rw [Measure.dirac_apply' _ measurableSet_Iio, Set.indicator_of_notMem (by simpa using hs)]
  · exact integrable_dirac (by simp)
  · rw [integral_dirac]

/-- Stieltjes functions are closed under addition. -/
theorem HasStieltjesMeasure.add (hf : HasStieltjesMeasure f μ) (hg : HasStieltjesMeasure g ν) :
    HasStieltjesMeasure (fun z => f z + g z) (μ + ν) := by
  refine ⟨?_, hf.integrable.add_measure hg.integrable, fun z hz => ?_⟩
  · rw [Measure.add_apply, hf.measure_Iio, hg.measure_Iio, add_zero]
  · rw [integral_add_measure (hf.integrable_inv_add hz) (hg.integrable_inv_add hz),
      hf.eq_integral z hz, hg.eq_integral z hz]

/-- Stieltjes functions are closed under nonnegative multiples. -/
theorem HasStieltjesMeasure.smul (hf : HasStieltjesMeasure f μ) (c : ℝ≥0) :
    HasStieltjesMeasure (fun z => (c : ℝ) * f z) (c • μ) := by
  refine ⟨?_, hf.integrable.smul_measure_nnreal, fun z hz => ?_⟩
  · rw [Measure.smul_apply, hf.measure_Iio, smul_zero]
  · rw [integral_smul_nnreal_measure, hf.eq_integral z hz, NNReal.smul_def, smul_eq_mul]

/-- The zero function is a Stieltjes function. -/
theorem isStieltjes_zero : IsStieltjes 0 :=
  ⟨0, ⟨rfl, integrable_zero_measure, fun z _ => by simp⟩⟩

/-- **Negative fractional powers are Stieltjes**: $z^{-\gamma}$ for $0 < \gamma < 1$.
The representing measure is Mathlib's measure $\mu$ of
`Real.exists_measure_rpow_eq_integral_rpowIntegrand₀₁` at $p = 1 - \gamma$, restricted to
$(0, \infty)$, with density $t^{p-1}$: that lemma gives
$z^{p} = \int_{(0,\infty)} t^p(t^{-1} - (t + z)^{-1})\,d\mu$, that is
$z^{-\gamma} = \int_{(0,\infty)} (z + t)^{-1}\,t^{p - 1}\,d\mu(t)$. [ChenPersson2026, §1.1]. -/
theorem isStieltjes_rpow_neg {γ : ℝ} (hγ : γ ∈ Set.Ioo 0 1) :
    IsStieltjes fun z => z ^ (-γ) := by
  set p := 1 - γ
  have hp : p ∈ Set.Ioo 0 1 := by
    simp only [p, Set.mem_Ioo]
    constructor <;> linarith [hγ.1, hγ.2]
  obtain ⟨μ, hμ⟩ := Real.exists_measure_rpow_eq_integral_rpowIntegrand₀₁ hp
  set d : ℝ → ℝ≥0 := fun t => Real.toNNReal (t ^ (p - 1))
  have hd : Measurable d := (measurable_id.pow_const _).real_toNNReal
  set ν := (μ.restrict (Set.Ioi 0)).withDensity fun t => (d t : ENNReal)
  -- on $(0, \infty)$ the integrand of Mathlib's representation is $z\,t^{p-1}/(z + t)$
  have hint : ∀ z, 0 ≤ z → ∀ t ∈ Set.Ioi (0 : ℝ),
      Real.rpowIntegrand₀₁ p t z = z * ((d t : ℝ) • (z + t)⁻¹) := by
    intro z hz t ht
    have ht' : (0 : ℝ) < t := ht
    simp only [Real.rpowIntegrand₀₁, d, smul_eq_mul,
      Real.coe_toNNReal _ (Real.rpow_nonneg ht'.le _)]
    rw [Real.rpow_sub_one ht'.ne']
    field_simp
    ring
  have hae : ∀ z, 0 ≤ z → (fun t => Real.rpowIntegrand₀₁ p t z) =ᵐ[μ.restrict (Set.Ioi 0)]
      fun t => z * ((d t : ℝ) • (z + t)⁻¹) := fun z hz =>
    (ae_restrict_mem measurableSet_Ioi).mono fun t ht => hint z hz t ht
  refine ⟨ν, ⟨?_, ?_, fun z hz => ?_⟩⟩
  · rw [withDensity_apply _ measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Set.Iio_inter_Ioi, Set.Ioo_self, Measure.restrict_empty, lintegral_zero_measure]
  · rw [integrable_withDensity_iff_integrable_smul hd]
    have h1 := ((hμ 1 (Set.mem_Ici.mpr zero_le_one)).1).congr (hae 1 zero_le_one)
    refine h1.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, one_mul]
  · obtain ⟨-, hz'⟩ := hμ z (Set.mem_Ici.mpr hz.le)
    rw [integral_congr_ae (hae z hz.le), integral_const_mul] at hz'
    rw [integral_withDensity_eq_integral_smul hd]
    simp only [NNReal.smul_def] at hz' ⊢
    have hγ' : -γ = p - 1 := by simp only [p]; ring
    rw [hγ', Real.rpow_sub_one hz.ne', hz', mul_div_cancel_left₀ _ hz.ne']

end NLAlib
