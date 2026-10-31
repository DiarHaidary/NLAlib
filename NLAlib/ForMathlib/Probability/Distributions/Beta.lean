/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.SubGaussian
public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.ForMathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Beta laws: a ratio of Gammas, and the sub-Gaussian proxy

For independent $X \sim \mathrm{Gamma}(a, r)$ and $Y \sim \mathrm{Gamma}(b, r)$,
$X/(X+Y) \sim \mathrm{Beta}(a, b)$: one substitution $x = ys/(1-s)$ for fixed $y$, Tonelli and
the Gamma integral, with no two-dimensional Jacobian. A $\mathrm{Beta}(\alpha, \beta)$ law is
sub-Gaussian about its mean $\alpha/(\alpha+\beta)$ with variance proxy
$1/(4(\alpha+\beta+1))$ [MarchalArbel2017]; the proof here is a first-order comparison for the
Riccati equation of $(\log\mathrm{mgf})'$ (Kummer's equation after an integration by parts), not
the source's. The primary statements are in Mathlib's measure-level form; the `HasLaw` forms are
corollaries. Upstream candidates for `Mathlib.Probability.Distributions.Beta` (which would then
import `…/Gamma.lean`).


## Main results

* `ProbabilityTheory.map_div_add_prod_gammaMeasure`: Beta as a ratio of Gammas, measure-level.
* `ProbabilityTheory.hasLaw_div_add_of_hasLaw_gammaMeasure`: its `HasLaw` form.
* `ProbabilityTheory.hasSubgaussianMGF_sub_div_betaMeasure`: the Beta sub-Gaussian proxy.
* `ProbabilityTheory.hasSubgaussianMGF_sub_div_of_hasLaw_betaMeasure`: its `HasLaw` form.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Beta as a ratio of Gammas -/

/-- For $y > 0$ the substitution $s \mapsto ys/(1-s)$ maps $(0, 1)$ onto $(0, \infty)$. -/
private theorem image_mul_div_one_sub_Ioo {y : ℝ} (hy : 0 < y) :
    (fun s => y * s / (1 - s)) '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
    exact div_pos (mul_pos hy hs0) (sub_pos.2 hs1)
  · intro hx
    have hxy : 0 < x + y := add_pos hx hy
    refine ⟨x / (x + y), ⟨div_pos hx hxy, (div_lt_one hxy).2 (by linarith)⟩, ?_⟩
    simp only
    rw [one_sub_div hxy.ne', add_sub_cancel_left]
    field_simp

/-- For $y > 0$ the substitution $s \mapsto ys/(1-s)$ is injective on $(0, 1)$. -/
private theorem injOn_mul_div_one_sub (y : ℝ) (hy : 0 < y) :
    InjOn (fun s => y * s / (1 - s)) (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  simp only [mem_Ioo] at ha hb
  have ha1 : (1 - a) ≠ 0 := by linarith [ha.2]
  have hb1 : (1 - b) ≠ 0 := by linarith [hb.2]
  simp only at hab
  rw [div_eq_div_iff ha1 hb1] at hab
  have h2 : y * a = y * b := by linarith [hab]
  exact mul_left_cancel₀ hy.ne' h2

/-- The derivative of the substitution: $s \mapsto ys/(1-s)$ has derivative $y/(1-s)^2$ at every
$s \ne 1$. -/
private theorem hasDerivAt_mul_div_one_sub (y : ℝ) {s : ℝ} (hs : s ≠ 1) :
    HasDerivAt (fun s => y * s / (1 - s)) (y / (1 - s) ^ 2) s := by
  have h1 : (1 - s) ≠ 0 := sub_ne_zero.2 hs.symm
  have hd := HasDerivAt.div (c := fun x => y * x) (d := fun x => 1 - x)
    ((hasDerivAt_id s).const_mul y) ((hasDerivAt_id s).const_sub 1) h1
  refine hd.congr_deriv ?_
  congr 1
  ring

/-- The inner substitution of the Gamma ratio: for measurable $F \ge 0$ and $y > 0$, putting
$x = ys/(1-s)$,
$$\int_0^\infty F\Bigl(\frac{x}{x+y}\Bigr) x^{a-1}e^{-rx}\,dx = \int_0^1 F(s)\,y^a s^{a-1}
(1-s)^{-a-1}e^{-rys/(1-s)}\,ds\,.$$ -/
private theorem lintegral_Ioi_comp_div_add (F : ℝ → ℝ≥0∞) {a r y : ℝ} (hy : 0 < y) :
    ∫⁻ x in Ioi (0 : ℝ), F (x / (x + y)) * ENNReal.ofReal (x ^ (a - 1) * Real.exp (-(r * x))) =
      ∫⁻ s in Ioo (0 : ℝ) 1, F s * ENNReal.ofReal
        (y ^ a * s ^ (a - 1) * (1 - s) ^ (-a - 1) * Real.exp (-(r * y * s / (1 - s)))) := by
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun s => y * s / (1 - s)) (y / (1 - s) ^ 2) (Ioo (0 : ℝ) 1) s :=
    fun s hs => (hasDerivAt_mul_div_one_sub y (ne_of_lt hs.2)).hasDerivWithinAt
  calc
    _ = ∫⁻ x in (fun s => y * s / (1 - s)) '' Ioo (0 : ℝ) 1,
          F (x / (x + y)) * ENNReal.ofReal (x ^ (a - 1) * Real.exp (-(r * x))) := by
          rw [image_mul_div_one_sub_Ioo hy]
    _ = ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal |y / (1 - s) ^ 2| *
          (F ((y * s / (1 - s)) / ((y * s / (1 - s)) + y)) *
            ENNReal.ofReal ((y * s / (1 - s)) ^ (a - 1) * Real.exp (-(r * (y * s / (1 - s)))))) :=
          lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv
            (injOn_mul_div_one_sub y hy) _
    _ = _ := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
          have hs0 : 0 < s := hs.1
          have hs1 : 0 < 1 - s := by linarith [hs.2]
          have h1 : y * s / (1 - s) / (y * s / (1 - s) + y) = s := by
            field_simp
            ring
          have hreal : y / (1 - s) ^ 2 * ((y * s / (1 - s)) ^ (a - 1) *
              Real.exp (-(r * (y * s / (1 - s))))) =
              y ^ a * s ^ (a - 1) * (1 - s) ^ (-a - 1) * Real.exp (-(r * y * s / (1 - s))) := by
            have hv : (1 - s) ^ (-a - 1) = ((1 - s) ^ (a - 1) * (1 - s) ^ 2)⁻¹ := by
              rw [← Real.rpow_natCast, ← Real.rpow_add hs1, ← Real.rpow_neg hs1.le]
              congr 1
              push_cast
              ring
            have hw : (1 - s) ^ (a - 1) ≠ 0 := (Real.rpow_pos_of_pos hs1 _).ne'
            rw [hv, show -(r * (y * s / (1 - s))) = -(r * y * s / (1 - s)) by ring,
              Real.div_rpow (by positivity) hs1.le, Real.mul_rpow hy.le hs0.le,
              Real.rpow_sub_one hy.ne' a]
            field_simp
          rw [h1, abs_of_pos (div_pos hy (pow_pos hs1 2)), ← mul_assoc,
            mul_comm _ (F s), mul_assoc, ← ENNReal.ofReal_mul (div_pos hy (pow_pos hs1 2)).le,
            hreal]

private lemma gammaPDF_eq_mul_ofReal_of_pos {a r x : ℝ} (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    gammaPDF a r x =
      ENNReal.ofReal (r ^ a / Real.Gamma a) *
        ENNReal.ofReal (x ^ (a - 1) * Real.exp (-(r * x))) := by
  have hK : 0 ≤ r ^ a / Real.Gamma a := by positivity
  unfold gammaPDF gammaPDFReal
  rw [if_pos hx.le, mul_assoc, ENNReal.ofReal_mul hK]

private lemma lintegral_eq_lintegral_Ioi_of_eq_zero {g : ℝ → ℝ≥0∞} (hg : ∀ y, y < 0 → g y = 0) :
    ∫⁻ y, g y = ∫⁻ y in Ioi 0, g y := by
  rw [Measure.restrict_congr_set Ioi_ae_eq_Ici, setLIntegral_eq_of_support_subset]
  intro y hy
  by_contra h
  exact hy (hg y (lt_of_not_ge h))

private lemma lintegral_gamma_comp_div_add (F : ℝ → ℝ≥0∞) {a r y : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hy : 0 < y) :
    ∫⁻ x, F (x / (x + y)) * gammaPDF a r x =
      ENNReal.ofReal (r ^ a / Real.Gamma a) * ∫⁻ s in Ioo (0 : ℝ) 1,
        F s * ENNReal.ofReal
          (y ^ a * s ^ (a - 1) * (1 - s) ^ (-a - 1) * Real.exp (-(r * y * s / (1 - s)))) := by
  have hz : ∀ x : ℝ, x < 0 → F (x / (x + y)) * gammaPDF a r x = 0 := fun x hx => by
    rw [gammaPDF_of_neg hx, mul_zero]
  have key : ∀ x ∈ Ioi (0 : ℝ), F (x / (x + y)) * gammaPDF a r x =
      ENNReal.ofReal (r ^ a / Real.Gamma a) *
        (F (x / (x + y)) * ENNReal.ofReal (x ^ (a - 1) * Real.exp (-(r * x)))) := by
    intro x hx
    rw [gammaPDF_eq_mul_ofReal_of_pos ha hr hx]
    ring
  rw [lintegral_eq_lintegral_Ioi_of_eq_zero hz, setLIntegral_congr_fun measurableSet_Ioi key,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioi_comp_div_add F hy]

private lemma integrableOn_rpow_mul_exp_div {a b r s : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun y : ℝ => y ^ (a + b - 1) * Real.exp (-(r / (1 - s) * y))) (Ioi 0) := by
  have h1s : 0 < 1 - s := by linarith [hs.2]
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a + b - 1) (b := r / (1 - s))
    (by linarith) one_pos (div_pos hr h1s)
  simpa only [Real.rpow_one, neg_mul] using this

/-- The Gamma-ratio integral after Tonelli: for measurable $F \ge 0$ and $a, b, r > 0$,
$$\iint F\Bigl(\frac{x}{x+y}\Bigr)\gamma_{a,r}(x)\gamma_{b,r}(y)\,dx\,dy = \int_0^1 F(s)
\frac{r^{a+b}}{\Gamma(a)\Gamma(b)}s^{a-1}(1-s)^{-a-1}\int_0^\infty y^{a+b-1}e^{-ry/(1-s)}\,dy\,
ds\,,$$
$\gamma_{a,r}$ the Gamma density `gammaPDF a r`. -/
private theorem lintegral_lintegral_comp_div_add_gammaPDF {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∫⁻ y, (∫⁻ x, F (x / (x + y)) * gammaPDF a r x) * gammaPDF b r y =
      ∫⁻ s in Ioo (0 : ℝ) 1, F s * ENNReal.ofReal
        (r ^ (a + b) / (Real.Gamma a * Real.Gamma b) * s ^ (a - 1) * (1 - s) ^ (-a - 1) *
          ∫ y in Ioi (0 : ℝ), y ^ (a + b - 1) * Real.exp (-(r / (1 - s) * y))) := by
  have hKc : 0 ≤ r ^ a / Real.Gamma a := by positivity
  have hKd : 0 ≤ r ^ b / Real.Gamma b := by positivity
  have hz : ∀ y : ℝ, y < 0 →
      (∫⁻ x, F (x / (x + y)) * gammaPDF a r x) * gammaPDF b r y = 0 := fun y hy => by
    rw [gammaPDF_of_neg hy, mul_zero]
  have key1 : ∀ y ∈ Ioi (0 : ℝ), (∫⁻ x, F (x / (x + y)) * gammaPDF a r x) * gammaPDF b r y =
      ∫⁻ s in Ioo (0 : ℝ) 1, F s * ENNReal.ofReal (r ^ (a + b) / (Real.Gamma a * Real.Gamma b) *
        s ^ (a - 1) * (1 - s) ^ (-a - 1) * (y ^ (a + b - 1) * Real.exp (-(r / (1 - s) * y)))) := by
    intro y hy
    have hy0 : 0 < y := hy
    rw [gammaPDF_eq_mul_ofReal_of_pos hb hr hy0, lintegral_gamma_comp_div_add F ha hr hy0,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    obtain ⟨hs0, hs1⟩ := hs
    have h1s : 0 < 1 - s := by linarith
    have h1s': 1 - s ≠ 0 := h1s.ne'
    have hA : 0 ≤ y ^ a * s ^ (a - 1) * (1 - s) ^ (-a - 1) * Real.exp (-(r * y * s / (1 - s))) :=
      mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg h1s.le _)) (Real.exp_nonneg _)
    have h2 : y ^ a * y ^ (b - 1) = y ^ (a + b - 1) := by
      rw [← Real.rpow_add hy0]; congr 1; ring
    have h3 : Real.exp (-(r * y * s / (1 - s))) * Real.exp (-(r * y)) =
        Real.exp (-(r / (1 - s) * y)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    have h4 : r ^ a * r ^ b = r ^ (a + b) := (Real.rpow_add hr a b).symm
    have e : r ^ a / Real.Gamma a * (y ^ a * s ^ (a - 1) * (1 - s) ^ (-a - 1) *
        Real.exp (-(r * y * s / (1 - s)))) *
        (r ^ b / Real.Gamma b * (y ^ (b - 1) * Real.exp (-(r * y)))) =
        r ^ (a + b) / (Real.Gamma a * Real.Gamma b) * s ^ (a - 1) * (1 - s) ^ (-a - 1) *
          (y ^ (a + b - 1) * Real.exp (-(r / (1 - s) * y))) := by
      rw [← h2, ← h3, ← h4]
      ring
    rw [← e, ENNReal.ofReal_mul (mul_nonneg hKc hA), ENNReal.ofReal_mul hKc,
      ENNReal.ofReal_mul hKd]
    ring
  have hmeas : AEMeasurable (Function.uncurry fun (y s : ℝ) => F s * ENNReal.ofReal
      (r ^ (a + b) / (Real.Gamma a * Real.Gamma b) * s ^ (a - 1) * (1 - s) ^ (-a - 1) *
        (y ^ (a + b - 1) * Real.exp (-(r / (1 - s) * y)))))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    (Measurable.mul (hF.comp measurable_snd) (Measurable.ennreal_ofReal (by fun_prop))).aemeasurable
  rw [lintegral_eq_lintegral_Ioi_of_eq_zero hz, setLIntegral_congr_fun measurableSet_Ioi key1,
    lintegral_lintegral_swap hmeas]
  refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  obtain ⟨hs0, hs1⟩ := hs
  have h1s : 0 < 1 - s := by linarith
  have hC : 0 ≤ r ^ (a + b) / (Real.Gamma a * Real.Gamma b) * s ^ (a - 1) * (1 - s) ^ (-a - 1) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg h1s.le _)
  have hint : IntegrableOn (fun y : ℝ => r ^ (a + b) / (Real.Gamma a * Real.Gamma b) * s ^ (a - 1) *
      (1 - s) ^ (-a - 1) * (y ^ (a + b - 1) * Real.exp (-(r / (1 - s) * y)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_div ha hb hr ⟨hs0, hs1⟩).const_mul _
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun y : ℝ => r ^ (a + b) /
      (Real.Gamma a * Real.Gamma b) * s ^ (a - 1) * (1 - s) ^ (-a - 1) *
      (y ^ (a + b - 1) * Real.exp (-(r / (1 - s) * y)))) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun y hy =>
      mul_nonneg hC (mul_nonneg (Real.rpow_nonneg (Set.mem_Ioi.mp hy).le _) (Real.exp_nonneg _))
  rw [lintegral_const_mul, ← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul]
  fun_prop

/-- The constant of the Gamma-ratio integral on $(0, 1)$ is the Beta density. -/
private theorem const_mul_integral_eq_beta_density {a b r s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) (hs : s ∈ Ioo (0 : ℝ) 1) :
    r ^ (a + b) / (Real.Gamma a * Real.Gamma b) * s ^ (a - 1) * (1 - s) ^ (-a - 1) *
        ∫ y in Ioi (0 : ℝ), y ^ (a + b - 1) * Real.exp (-(r / (1 - s) * y)) =
      1 / beta a b * s ^ (a - 1) * (1 - s) ^ (b - 1) := by
  obtain ⟨hs0, hs1⟩ := hs
  have h1s : 0 < 1 - s := by linarith
  have hc : 0 < r / (1 - s) := div_pos hr h1s
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hc]
  have hA : (1 / (r / (1 - s))) ^ (a + b) = (1 - s) ^ (a + b) / r ^ (a + b) := by
    rw [one_div_div, Real.div_rpow h1s.le hr.le]
  have hB : (1 - s) ^ (b - 1) = (1 - s) ^ (-a - 1) * (1 - s) ^ (a + b) := by
    rw [← Real.rpow_add h1s]
    congr 1
    ring
  have hG1 := Real.Gamma_pos_of_pos ha
  have hG2 := Real.Gamma_pos_of_pos hb
  have hG3 := Real.Gamma_pos_of_pos (add_pos ha hb)
  have hp : r ^ (a + b) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have hq : (1 - s) ^ (a + b) ≠ 0 := (Real.rpow_pos_of_pos h1s _).ne'
  rw [hA, hB, beta]
  field_simp

/-- The Gamma-ratio integral is the Beta integral: for measurable $F \ge 0$ and $a, b, r > 0$,
$$\iint F\Bigl(\frac{x}{x+y}\Bigr)\gamma_{a,r}(x)\gamma_{b,r}(y)\,dx\,dy = \int F(s)\,
\beta_{a,b}(s)\,ds\,,$$
$\gamma_{a,r}$ the Gamma density `gammaPDF a r` and $\beta_{a,b}$ the Beta density
`betaPDF a b`. -/
private theorem lintegral_lintegral_comp_div_add_gammaPDF_eq_betaPDF {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∫⁻ y, (∫⁻ x, F (x / (x + y)) * gammaPDF a r x) * gammaPDF b r y =
      ∫⁻ s, F s * betaPDF a b s := by
  have hsupp : Function.support (fun s => F s * betaPDF a b s) ⊆ Ioo (0 : ℝ) 1 :=
    Function.support_subset_iff'.2 fun x hx => by
      rcases le_or_gt x 0 with h | h
      · rw [betaPDF_eq_zero_of_nonpos h, mul_zero]
      · rw [betaPDF_eq_zero_of_one_le (not_lt.1 fun h1 => hx ⟨h, h1⟩), mul_zero]
  rw [lintegral_lintegral_comp_div_add_gammaPDF hF ha hb hr,
    ← setLIntegral_eq_of_support_subset hsupp]
  refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  rw [betaPDF_of_pos_lt_one hs.1 hs.2, const_mul_integral_eq_beta_density ha hb hr hs]

/-- **Beta as a ratio of Gammas**: for $a, b, r > 0$, the image of
$\mathrm{Gamma}(a, r) \otimes \mathrm{Gamma}(b, r)$ (shapes $a$, $b$, common rate $r$) under
$$(x, y) \mapsto \frac{x}{x+y}$$
is $\mathrm{Beta}(a, b)$.
No printed source.
Result: gamma-ratio-beta -/
theorem map_div_add_prod_gammaMeasure {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map (fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) =
      betaMeasure a b := by
  ext S hS
  have hf : Measurable (fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) :=
    measurable_fst.div (measurable_fst.add measurable_snd)
  have hT : MeasurableSet ((fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) ⁻¹' S) := hS.preimage hf
  have hF : Measurable (S.indicator (fun _ : ℝ => (1 : ℝ≥0∞))) := measurable_const.indicator hS
  have key := lintegral_lintegral_comp_div_add_gammaPDF_eq_betaPDF hF ha hb hr
  have hga : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  have hgb : Measurable (gammaPDF b r) := (measurable_gammaPDFReal b r).ennreal_ofReal
  rw [Measure.map_apply hf hS, gammaMeasure, gammaMeasure, prod_withDensity hga hgb,
    betaMeasure, withDensity_apply _ hS, withDensity_apply _ hT, ← lintegral_indicator hT,
    lintegral_prod_symm]
  swap
  · exact (((hga.comp measurable_fst).mul (hgb.comp measurable_snd)).indicator hT).aemeasurable
  calc _ = ∫⁻ y, (∫⁻ x, S.indicator (fun _ => (1 : ℝ≥0∞)) (x / (x + y)) * gammaPDF a r x) *
        gammaPDF b r y := by
        refine lintegral_congr fun y => ?_
        rw [← lintegral_mul_const' (gammaPDF b r y) _ (by simp [gammaPDF])]
        refine lintegral_congr fun x => ?_
        by_cases hx : x / (x + y) ∈ S <;> simp [Set.indicator, hx]
    _ = ∫⁻ s, S.indicator (fun _ => (1 : ℝ≥0∞)) s * betaPDF a b s := key
    _ = _ := by
        rw [← lintegral_indicator hS]
        refine lintegral_congr fun s => ?_
        by_cases hs : s ∈ S <;> simp [Set.indicator, hs]

/-- Beta as a ratio of Gammas, `HasLaw` form: for $a, b, r > 0$ and independent
$X \sim \mathrm{Gamma}(a, r)$ and $Y \sim \mathrm{Gamma}(b, r)$ (shapes $a$, $b$, common rate
$r$), $X/(X+Y) \sim \mathrm{Beta}(a, b)$. -/
theorem hasLaw_div_add_of_hasLaw_gammaMeasure {X Y : Ω → ℝ} {a b r : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (hX : HasLaw X (gammaMeasure a r) μ)
    (hY : HasLaw Y (gammaMeasure b r) μ) (hXY : IndepFun X Y μ) :
    HasLaw (fun ω => X ω / (X ω + Y ω)) (betaMeasure a b) μ := by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  have : IsProbabilityMeasure (gammaMeasure b r) := isProbabilityMeasure_gammaMeasure hb hr
  have hpair : HasLaw (fun ω => (X ω, Y ω)) ((gammaMeasure a r).prod (gammaMeasure b r)) μ :=
    ⟨hX.aemeasurable.prodMk hY.aemeasurable, by
      rw [← hX.map_eq, ← hY.map_eq]
      exact (indepFun_iff_map_prod_eq_prod_map_map' hX.aemeasurable hY.aemeasurable
        (by rw [hX.map_eq]; infer_instance) (by rw [hY.map_eq]; infer_instance)).mp hXY⟩
  have hf : HasLaw (fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) (betaMeasure a b)
      ((gammaMeasure a r).prod (gammaMeasure b r)) :=
    ⟨by fun_prop, map_div_add_prod_gammaMeasure ha hb hr⟩
  exact hf.comp hpair

/-! ### The Beta sub-Gaussian proxy -/

/-- The tilted moments of a Beta law,
$\varphi_k(s) = \mathbb{E}\,X^k e^{sX}$ for $X \sim \mathrm{Beta}(\alpha, \beta)$: the
moment-generating integrals of the proxy proof. -/
private noncomputable def betaExpMoment (α β : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  ∫ x, x ^ k * Real.exp (s * x) ∂betaMeasure α β

/-- The derivative of $x^\alpha(1-x)^\beta e^{tx}$ on $(0, 1)$ is
$x^{\alpha-1}(1-x)^{\beta-1}(\alpha - (\alpha+\beta)x + tx(1-x))e^{tx}$. -/
private theorem hasDerivAt_rpow_mul_rpow_mul_exp {α β t x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => x ^ α * (1 - x) ^ β * Real.exp (t * x))
      (x ^ (α - 1) * (1 - x) ^ (β - 1) *
        ((α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x))) x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := (sub_pos.2 hx.2).ne'
  refine (((Real.hasDerivAt_rpow_const (Or.inl hx0)).mul
    (((hasDerivAt_id' x).const_sub 1).rpow_const (Or.inl hx1))).mul
    ((hasDerivAt_id' x).const_mul t).exp).congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [Real.rpow_sub_one hx0, Real.rpow_sub_one hx1]
  field_simp
  ring

/-- The Beta density is nonnegative. -/
private lemma betaPDFReal_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    0 ≤ betaPDFReal α β x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (betaPDFReal_pos hx.1 hx.2 hα hβ).le
  · simp [betaPDFReal, hx]

/-- For $\alpha, \beta > 0$ and real $t$, the derivative
$x^{\alpha-1}(1-x)^{\beta-1}(\alpha - (\alpha+\beta)x + tx(1-x))e^{tx}$ is interval integrable
on $[0, 1]$. -/
private theorem intervalIntegrable_rpow_mul_rpow_mul_exp {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (t : ℝ) :
    IntervalIntegrable (fun x => x ^ (α - 1) * (1 - x) ^ (β - 1) *
      ((α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x))) volume 0 1 := by
  have hint : Integrable (betaPDFReal α β) := by
    refine ⟨(measurable_betaPDFReal α β).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (betaPDFReal_nonneg hα hβ))]
    exact (lintegral_betaPDF_eq_one hα hβ).trans_lt ENNReal.one_lt_top
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖beta α β * ((α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x))‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn (by fun_prop)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  refine (hint.integrableOn.bdd_mul (c := C)
    (f := fun x => beta α β * ((α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x)))
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_).congr ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hC x (Ioo_subset_Icc_self hx)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [betaPDFReal, if_pos (show 0 < x ∧ x < 1 from hx)]
    field_simp [(beta_pos hα hβ).ne']

/-- Integration by parts on $[0, 1]$: for $\alpha, \beta > 0$ and real $t$,
$$\int_0^1 x^{\alpha-1}(1-x)^{\beta-1}(\alpha - (\alpha+\beta)x + tx(1-x))e^{tx}\,dx = 0\,,$$
since $x^\alpha(1-x)^\beta e^{tx}$ vanishes at $0$ and $1$. -/
private theorem intervalIntegral_rpow_mul_rpow_mul_exp_eq_zero {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (t : ℝ) :
    ∫ x in (0 : ℝ)..1, x ^ (α - 1) * (1 - x) ^ (β - 1) *
      ((α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x)) = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ α * (1 - x) ^ β * Real.exp (t * x)) (Icc 0 1) := by
    intro x _
    apply ContinuousAt.continuousWithinAt
    have h1 : ContinuousAt (fun x : ℝ => x ^ α) x :=
      Real.continuousAt_rpow_const x α (Or.inr hα.le)
    have h2 : ContinuousAt (fun x : ℝ => (1 - x) ^ β) x :=
      ContinuousAt.rpow_const (continuousAt_const.sub continuousAt_id) (Or.inr hβ.le)
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
    (fun x hx => hasDerivAt_rpow_mul_rpow_mul_exp hx)
    (intervalIntegrable_rpow_mul_rpow_mul_exp hα hβ t)]
  simp [Real.zero_rpow hα.ne', Real.zero_rpow hβ.ne']

/-- Kummer's equation in integral form: for $X \sim \mathrm{Beta}(\alpha, \beta)$,
$\alpha, \beta > 0$ and real $t$,
$\mathbb{E}[(\alpha - (\alpha+\beta)X + tX(1-X))e^{tX}] = 0$. -/
private theorem integral_sub_mul_add_mul_exp_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (t : ℝ) :
    ∫ x, (α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x) ∂betaMeasure α β = 0 := by
  have hto : ∀ x, (betaPDF α β x).toReal = betaPDFReal α β x := fun x =>
    ENNReal.toReal_ofReal (betaPDFReal_nonneg hα hβ x)
  unfold betaMeasure
  have hmeas : Measurable (betaPDF α β) := (measurable_betaPDFReal α β).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  simp only [hto, smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo (0 : ℝ) 1) ?_]
  · have h2 : ∀ x ∈ Ioo (0 : ℝ) 1, betaPDFReal α β x * ((α - (α + β) * x + t * x * (1 - x)) *
        Real.exp (t * x)) = (1 / beta α β) * (x ^ (α - 1) * (1 - x) ^ (β - 1) *
          ((α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x))) := by
      intro x hx
      rw [betaPDFReal, if_pos (show 0 < x ∧ x < 1 from hx)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioo h2, integral_const_mul,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral_rpow_mul_rpow_mul_exp_eq_zero hα hβ t, mul_zero]
  · intro x hx
    rw [betaPDFReal, if_neg (show ¬(0 < x ∧ x < 1) from hx), zero_mul]

/-- A Beta law lives on $[0, 1]$: for all $\alpha, \beta$, almost every point of
`betaMeasure α β` lies in $[0, 1]$. -/
private theorem ae_mem_Icc_betaMeasure (α β : ℝ) : ∀ᵐ x ∂betaMeasure α β, x ∈ Icc (0 : ℝ) 1 := by
  have hs : MeasurableSet {x : ℝ | x ∉ Icc (0 : ℝ) 1} := measurableSet_Icc.compl
  rw [betaMeasure, ae_iff, withDensity_apply _ hs]
  refine (setLIntegral_congr_fun (g := fun _ => 0) hs fun x hx => ?_).trans (by simp)
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact betaPDF_eq_zero_of_nonpos hx.le
  · exact betaPDF_eq_zero_of_one_le hx.le

/-- A Beta law has every exponential moment: for $\alpha, \beta > 0$ and real $t$,
$x \mapsto e^{tx}$ is integrable for `betaMeasure α β`. -/
private theorem integrable_exp_mul_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    Integrable (fun x => Real.exp (t * x)) (betaMeasure α β) :=
  have := isProbabilityMeasureBeta hα hβ
  integrable_exp_mul_of_mem_Icc (X := id) aemeasurable_id (ae_mem_Icc_betaMeasure α β)

/-- Every real $t$ is interior to the exponential integrability set of a Beta law. -/
private theorem mem_interior_integrableExpSet_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (t : ℝ) : t ∈ interior (integrableExpSet id (betaMeasure α β)) := by
  rw [eq_univ_of_forall (s := integrableExpSet id _) (integrable_exp_mul_betaMeasure hα hβ),
    interior_univ]
  exact mem_univ t

/-- The tilted moments differentiate up: for $\alpha, \beta > 0$, every $k$ and real $t$,
$\varphi_k' (t) = \varphi_{k+1}(t)$, where $\varphi_k(s) = \mathbb{E}\,X^k e^{sX}$ for
$X \sim \mathrm{Beta}(\alpha, \beta)$. -/
private theorem hasDerivAt_betaExpMoment {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) (t : ℝ) :
    HasDerivAt (betaExpMoment α β k) (betaExpMoment α β (k + 1) t) t :=
  have := isProbabilityMeasureBeta hα hβ
  hasDerivAt_integral_pow_mul_exp_real (mem_interior_integrableExpSet_betaMeasure hα hβ t) k

/-- The tilted mass is positive: for $\alpha, \beta > 0$ and real $t$,
$\mathbb{E}\,e^{tX} > 0$ for $X \sim \mathrm{Beta}(\alpha, \beta)$. -/
private theorem betaExpMoment_zero_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    0 < betaExpMoment α β 0 t := by
  have := isProbabilityMeasureBeta hα hβ
  simpa [betaExpMoment] using integral_exp_pos (integrable_exp_mul_betaMeasure hα hβ t)

/-- The Riccati identity: with $\varphi_k(t) = \mathbb{E}\,X^k e^{tX}$ for
$X \sim \mathrm{Beta}(\alpha, \beta)$, $y = \varphi_1/\varphi_0$, $b = \alpha + \beta$,
$\sigma^2 = 1/(4(b+1))$ and $z = y - \alpha/b - \sigma^2 t$ (so $z' = \varphi_2/\varphi_0 - y^2 -
\sigma^2$), for $\alpha, \beta > 0$ and real $t$, $tz' + bz = t(y(1-y) - 1/4)$. -/
private theorem mul_sub_add_mul_sub_eq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    t * (betaExpMoment α β 2 t / betaExpMoment α β 0 t -
        (betaExpMoment α β 1 t / betaExpMoment α β 0 t) ^ 2 - 1 / (4 * (α + β + 1))) +
      (α + β) * (betaExpMoment α β 1 t / betaExpMoment α β 0 t - α / (α + β) -
        t / (4 * (α + β + 1))) =
    t * (betaExpMoment α β 1 t / betaExpMoment α β 0 t *
      (1 - betaExpMoment α β 1 t / betaExpMoment α β 0 t) - 1 / 4) := by
  have hK := integral_sub_mul_add_mul_exp_betaMeasure hα hβ t
  have hpos := betaExpMoment_zero_pos hα hβ t
  have := isProbabilityMeasureBeta hα hβ
  have hi (k : ℕ) : Integrable (fun x : ℝ => x ^ k * Real.exp (t * x)) (betaMeasure α β) :=
    integrable_pow_mul_exp_of_mem_interior_integrableExpSet
      (mem_interior_integrableExpSet_betaMeasure hα hβ t) k
  have hK' : α * betaExpMoment α β 0 t - (α + β) * betaExpMoment α β 1 t +
      t * (betaExpMoment α β 1 t - betaExpMoment α β 2 t) = 0 := by
    simp only [show ∀ x : ℝ, (α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x) =
      α * (x ^ 0 * Real.exp (t * x)) - (α + β) * (x ^ 1 * Real.exp (t * x)) +
        t * (x ^ 1 * Real.exp (t * x) - x ^ 2 * Real.exp (t * x)) from fun x => by ring] at hK
    have i0 : Integrable (fun x : ℝ => α * (x ^ 0 * Real.exp (t * x))) (betaMeasure α β) :=
      (hi 0).const_mul α
    have i1 : Integrable (fun x : ℝ => (α + β) * (x ^ 1 * Real.exp (t * x))) (betaMeasure α β) :=
      (hi 1).const_mul (α + β)
    have i2 : Integrable (fun x : ℝ => t * (x ^ 1 * Real.exp (t * x) - x ^ 2 * Real.exp (t * x)))
        (betaMeasure α β) := ((hi 1).sub (hi 2)).const_mul t
    have i01 : Integrable (fun x : ℝ => α * (x ^ 0 * Real.exp (t * x)) -
        (α + β) * (x ^ 1 * Real.exp (t * x))) (betaMeasure α β) := i0.sub i1
    rw [integral_add i01 i2, integral_sub i0 i1, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_sub (hi 1) (hi 2)] at hK
    exact hK
  have ha : betaExpMoment α β 0 t * (betaExpMoment α β 0 t)⁻¹ = 1 :=
    mul_inv_cancel₀ hpos.ne'
  have hr : α / (α + β) * (α + β) = α := div_mul_cancel₀ α (by positivity)
  have hs : 1 / (4 * (α + β + 1)) * (4 * (α + β + 1)) = 1 :=
    one_div_mul_cancel (by positivity)
  linear_combination (-(betaExpMoment α β 0 t)⁻¹) * hK' +
    α * ha - hr - (t / 4) * hs

/-- The positive half of `mul_le_zero_of_ode_sign`: if $t\,z'(t) + b\,z(t) \le 0$ for $t > 0$,
then $z(t) \le 0$ for $t > 0$ (`antitoneOn_rpow_mul_of_hasDerivAt`, compared with $t = 0$). -/
private theorem nonpos_of_ode_sign {z z' : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hd : ∀ t, HasDerivAt z (z' t) t) (hpos : ∀ t, 0 < t → t * z' t + b * z t ≤ 0) {t : ℝ}
    (ht : 0 < t) : z t ≤ 0 := by
  have hle := antitoneOn_rpow_mul_of_hasDerivAt hb (hd 0).continuousAt.continuousWithinAt
    (fun s _ => hd s) hpos self_mem_Ici ht.le ht.le
  simp only [Real.zero_rpow hb.ne', zero_mul] at hle
  nlinarith [Real.rpow_pos_of_pos ht b]

/-- Sign lemma for a differentiable `z`: if $t\,z'(t) + b\,z(t) \le 0$ for $t > 0$
and $0 \le t\,z'(t) + b\,z(t)$ for $t < 0$, then $t\,z(t) \le 0$ for every $t$. -/
private theorem mul_le_zero_of_ode_sign {z z' : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hd : ∀ t, HasDerivAt z (z' t) t)
    (hpos : ∀ t, 0 < t → t * z' t + b * z t ≤ 0)
    (hneg : ∀ t, t < 0 → 0 ≤ t * z' t + b * z t) (t : ℝ) : t * z t ≤ 0 := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · -- the reflection `s ↦ -z (-s)` satisfies the hypotheses of the positive half
    have h := nonpos_of_ode_sign (z := fun s => -z (-s)) (z' := fun s => z' (-s)) hb
      (fun s => ((hd (-s)).comp s (hasDerivAt_neg s)).neg.congr_deriv (by ring))
      (fun s hs => by nlinarith [hneg (-s) (by linarith)]) (neg_pos.2 ht)
    simp only [neg_neg] at h
    nlinarith
  · simp
  · nlinarith [nonpos_of_ode_sign hb hd hpos ht]

/-- Derivative of the comparison function $z(t) = \varphi_1/\varphi_0 - \alpha/(\alpha+\beta)
- t/(4(\alpha+\beta+1))$ (the Riccati quotient of `mul_sub_div_sub_div_nonpos`). -/
private theorem hasDerivAt_comparison {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    HasDerivAt (fun s => betaExpMoment α β 1 s / betaExpMoment α β 0 s - α / (α + β) -
        s / (4 * (α + β + 1)))
      (betaExpMoment α β 2 t / betaExpMoment α β 0 t -
        (betaExpMoment α β 1 t / betaExpMoment α β 0 t) ^ 2 - 1 / (4 * (α + β + 1))) t := by
  have h0 : HasDerivAt (betaExpMoment α β 0) (betaExpMoment α β 1 t) t :=
    hasDerivAt_betaExpMoment hα hβ 0 t
  have h1 : HasDerivAt (betaExpMoment α β 1) (betaExpMoment α β 2 t) t :=
    hasDerivAt_betaExpMoment hα hβ 1 t
  have hM0 := (betaExpMoment_zero_pos hα hβ t).ne'
  have hd := h1.div h0 hM0
  have hs := ((hd.sub_const (α / (α + β))).sub ((hasDerivAt_id t).div_const (4 * (α + β + 1))))
  refine hs.congr_deriv ?_
  field_simp

/-- The comparison step: with $\varphi_k(t) = \mathbb{E}\,X^k e^{tX}$ for
$X \sim \mathrm{Beta}(\alpha, \beta)$, $\alpha, \beta > 0$, and
$z(t) = \varphi_1(t)/\varphi_0(t) - \alpha/(\alpha+\beta) - t/(4(\alpha+\beta+1))$, every real
$t$ has $t\,z(t) \le 0$. -/
private theorem mul_sub_div_sub_div_nonpos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    t * (betaExpMoment α β 1 t / betaExpMoment α β 0 t - α / (α + β) -
      t / (4 * (α + β + 1))) ≤ 0 := by
  have aux : ∀ y : ℝ, y * (1 - y) - 1 / 4 ≤ 0 := fun y => by nlinarith [sq_nonneg (y - 1 / 2)]
  have hb : 0 < α + β := by linarith
  exact mul_le_zero_of_ode_sign hb
    (z := fun s => betaExpMoment α β 1 s / betaExpMoment α β 0 s - α / (α + β) -
      s / (4 * (α + β + 1)))
    (z' := fun s => betaExpMoment α β 2 s / betaExpMoment α β 0 s -
      (betaExpMoment α β 1 s / betaExpMoment α β 0 s) ^ 2 - 1 / (4 * (α + β + 1)))
    (hasDerivAt_comparison hα hβ)
    (fun s hs => by
      rw [mul_sub_add_mul_sub_eq hα hβ s]
      exact mul_nonpos_of_nonneg_of_nonpos hs.le (aux _))
    (fun s hs => by
      rw [mul_sub_add_mul_sub_eq hα hβ s]
      exact mul_nonneg_of_nonpos_of_nonpos hs.le (aux _)) t

/-- The cumulant bound: for $X \sim \mathrm{Beta}(\alpha, \beta)$, $\alpha, \beta > 0$ and real
$t$, $\log\mathbb{E}\,e^{tX} - \alpha t/(\alpha+\beta) \le t^2/(8(\alpha+\beta+1))$. -/
private theorem log_betaExpMoment_sub_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    Real.log (betaExpMoment α β 0 t) - α / (α + β) * t ≤ t ^ 2 / (8 * (α + β + 1)) := by
  have hpos := betaExpMoment_zero_pos hα hβ
  have hzero : betaExpMoment α β 0 0 = 1 := by
    have := isProbabilityMeasureBeta hα hβ
    simp [betaExpMoment]
  set g : ℝ → ℝ := fun s => Real.log (betaExpMoment α β 0 s) - α / (α + β) * s -
    s ^ 2 / (8 * (α + β + 1)) with hg
  have hg0 : g 0 = 0 := by simp [hg, hzero]
  have hderiv : ∀ s, HasDerivAt g
      (betaExpMoment α β 1 s / betaExpMoment α β 0 s - α / (α + β) - s / (4 * (α + β + 1))) s := by
    intro s
    have hb : α + β ≠ 0 := by positivity
    refine ((((hasDerivAt_betaExpMoment hα hβ 0 s).log (hpos s).ne').sub
      ((hasDerivAt_id s).const_mul _)).sub ((hasDerivAt_pow 2 s).div_const _)).congr_deriv ?_
    field_simp
    ring
  have hcont : Continuous g := continuous_iff_continuousAt.2 fun s => (hderiv s).continuousAt
  have hdiff : Differentiable ℝ g := fun s => (hderiv s).differentiableAt
  suffices g t ≤ 0 by linarith
  rcases le_total 0 t with ht | ht
  · refine hg0 ▸ antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn
      hdiff.differentiableOn (fun s hs => ?_) self_mem_Ici ht ht
    rw [interior_Ici] at hs
    rw [(hderiv s).deriv]
    nlinarith [mul_sub_div_sub_div_nonpos hα hβ s, hs.out]
  · refine hg0 ▸ monotoneOn_of_deriv_nonneg (convex_Iic 0) hcont.continuousOn
      hdiff.differentiableOn (fun s hs => ?_) ht self_mem_Iic ht
    rw [interior_Iic] at hs
    rw [(hderiv s).deriv]
    nlinarith [mul_sub_div_sub_div_nonpos hα hβ s, hs.out]

/-- **Beta laws are sub-Gaussian with proxy $1/(4(\alpha+\beta+1))$**: for
$X \sim \mathrm{Beta}(\alpha, \beta)$ with $\alpha, \beta > 0$, the centred variable
$X - \alpha/(\alpha+\beta)$ satisfies
$$\mathbb{E}\,e^{t(X - \alpha/(\alpha+\beta))} \le \exp\Bigl(\frac{t^2}{8(\alpha+\beta+1)}\Bigr)$$
for every real $t$, the moment generating function bound with variance proxy
$1/(4(\alpha+\beta+1))$. The proxy equals the variance when $\alpha = \beta$ and exceeds it
otherwise; it improves Hoeffding's dimension-free proxy $1/4$ on $[0, 1]$
(`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`).
[MarchalArbel2017, Theorem 1]; the proof here is a comparison for the Riccati equation of
$(\log\mathrm{mgf})'$, not the source's (series comparison when $\alpha = \beta$, a second-order
analysis of Kummer's equation otherwise).
Result: beta-subgaussian -/
theorem hasSubgaussianMGF_sub_div_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    HasSubgaussianMGF (fun x => x - α / (α + β)) ‖1 / (4 * (α + β + 1))‖₊ (betaMeasure α β) := by
  have : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  have hint := integrable_exp_mul_betaMeasure hα hβ
  have hcoe : ((‖1 / (4 * (α + β + 1))‖₊ : ℝ≥0) : ℝ) = 1 / (4 * (α + β + 1)) := by
    rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have he (t x : ℝ) : Real.exp (t * (x - α / (α + β))) =
      Real.exp (-(α / (α + β) * t)) * Real.exp (t * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  refine { integrable_exp_mul := fun t => ?_, mgf_le := fun t => ?_ }
  · simpa only [he] using (hint t).const_mul (Real.exp (-(α / (α + β) * t)))
  · have hmgf : mgf (fun x => x - α / (α + β)) (betaMeasure α β) t
        = Real.exp (-(α / (α + β) * t)) * betaExpMoment α β 0 t := by
      simp only [mgf, betaExpMoment, he, pow_zero, one_mul, integral_const_mul]
    rw [hmgf, hcoe]
    calc Real.exp (-(α / (α + β) * t)) * betaExpMoment α β 0 t
        = Real.exp (Real.log (betaExpMoment α β 0 t) + -(α / (α + β) * t)) := by
          rw [Real.exp_add, Real.exp_log (betaExpMoment_zero_pos hα hβ t)]
          ring
      _ ≤ Real.exp (1 / (4 * (α + β + 1)) * t ^ 2 / 2) := by
          apply Real.exp_le_exp.mpr
          have h8 : 1 / (4 * (α + β + 1)) * t ^ 2 / 2 = t ^ 2 / (8 * (α + β + 1)) := by
            field_simp
            ring
          linarith [log_betaExpMoment_sub_le hα hβ t]

/-- Beta laws are sub-Gaussian, `HasLaw` form: for $X \sim \mathrm{Beta}(\alpha, \beta)$ with
$\alpha, \beta > 0$, $X - \alpha/(\alpha+\beta)$ satisfies the sub-Gaussian moment generating
function bound with variance proxy $1/(4(\alpha+\beta+1))$. -/
theorem hasSubgaussianMGF_sub_div_of_hasLaw_betaMeasure {X : Ω → ℝ} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hX : HasLaw X (betaMeasure α β) μ) :
    HasSubgaussianMGF (fun ω => X ω - α / (α + β)) ‖1 / (4 * (α + β + 1))‖₊ μ := by
  have hmeas : Measurable (fun x : ℝ => x - α / (α + β)) := measurable_id.sub_const _
  have h := hasSubgaussianMGF_sub_div_betaMeasure hα hβ
  rw [← HasSubgaussianMGF.id_map_iff hmeas.aemeasurable] at h
  rw [← HasSubgaussianMGF.id_map_iff (hX.aemeasurable.sub_const _)]
  have hmap : μ.map (fun ω => X ω - α / (α + β)) =
      (μ.map X).map (fun x : ℝ => x - α / (α + β)) :=
    (AEMeasurable.map_map_of_aemeasurable (hmeas.aemeasurable (μ := μ.map X)) hX.aemeasurable).symm
  rw [hmap, hX.map_eq]
  exact h

end ProbabilityTheory
