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
public import NLAlibScaffold.ForMathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Beta laws: a ratio of Gammas, and the sub-Gaussian proxy

Statements for `NLAlib/ForMathlib/Probability/Distributions/Beta.lean` whose proofs are deferred
(`docs/design/Probability-Beta.md`, §§3.2–3.3, β2 and β4). For independent
$X \sim \mathrm{Gamma}(a, r)$ and $Y \sim \mathrm{Gamma}(b, r)$, $X/(X+Y) \sim \mathrm{Beta}(a, b)$:
one substitution $x = ys/(1-s)$ for fixed $y$, Tonelli and the Gamma integral, with no
two-dimensional Jacobian. A $\mathrm{Beta}(\alpha, \beta)$ law is sub-Gaussian about its mean
$\alpha/(\alpha+\beta)$ with variance proxy $1/(4(\alpha+\beta+1))$ [MarchalArbel2017]; the
proof here is a first-order comparison for the Riccati equation of $(\log\mathrm{mgf})'$ (Kummer's
equation after an integration by parts), not the source's. The primary statements are in
Mathlib's measure-level form; the `HasLaw` forms are corollaries. Upstream candidates for
`Mathlib.Probability.Distributions.Beta` (which would then import `…/Gamma.lean`).

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

/-- For $y > 0$ the substitution $s \mapsto ys/(1-s)$ maps $(0, 1)$ onto $(0, \infty)$.
Proof: S, about 10 lines. `Set.ext`; the inverse is $x \mapsto x/(x+y)$; `field_simp`, `div_pos`,
`div_lt_one`. -/
private theorem image_mul_div_one_sub_Ioo {y : ℝ} (hy : 0 < y) :
    (fun s => y * s / (1 - s)) '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
    exact div_pos (mul_pos hy hs0) (sub_pos.2 hs1)
  · intro hx
    have hxy : 0 < x + y := add_pos hx hy
    refine ⟨x / (x + y), ⟨div_pos hx hxy, (div_lt_one hxy).2 (by linarith)⟩, ?_⟩
    have h1 : 1 - x / (x + y) = y / (x + y) := by
      field_simp
      ring
    simp only
    rw [h1]
    field_simp

/-- For $y > 0$ the substitution $s \mapsto ys/(1-s)$ is injective on $(0, 1)$.
Proof: S, about 8 lines. Cross-multiply ($1 - s \ne 0$): `div_eq_div_iff`, then
`mul_left_cancel₀ hy.ne'` and `linarith`. -/
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
$s \ne 1$.
Proof: S, about 8 lines. `HasDerivAt.div` of `(hasDerivAt_id s).const_mul y` by
`(hasDerivAt_id s).const_sub 1` with `sub_ne_zero.2 hs.symm`; `field_simp`, `ring`. -/
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
(1-s)^{-a-1}e^{-rys/(1-s)}\,ds\,.$$
Proof: M, about 40 lines. `lintegral_image_eq_lintegral_abs_deriv_mul` on `Ioo 0 1`, with
`image_mul_div_one_sub_Ioo`, `injOn_mul_div_one_sub` and `hasDerivAt_mul_div_one_sub` (as
`HasDerivWithinAt`); pointwise inside `ENNReal.ofReal`: $x/(x+y) = s$ by `field_simp`,
`Real.mul_rpow`, `Real.div_rpow`, `Real.rpow_neg`, `Real.rpow_add` for
$x^{a-1}\cdot y/(1-s)^2 = y^a s^{a-1}(1-s)^{-a-1}$. -/
private theorem lintegral_Ioi_comp_div_add {F : ℝ → ℝ≥0∞} (hF : Measurable F) {a r y : ℝ}
    (hy : 0 < y) :
    ∫⁻ x in Ioi (0 : ℝ), F (x / (x + y)) * ENNReal.ofReal (x ^ (a - 1) * Real.exp (-(r * x))) =
      ∫⁻ s in Ioo (0 : ℝ) 1, F s * ENNReal.ofReal
        (y ^ a * s ^ (a - 1) * (1 - s) ^ (-a - 1) * Real.exp (-(r * y * s / (1 - s)))) := by
  sorry

/-- The Gamma-ratio integral after Tonelli: for measurable $F \ge 0$ and $a, b, r > 0$,
$$\iint F\Bigl(\frac{x}{x+y}\Bigr)\gamma_{a,r}(x)\gamma_{b,r}(y)\,dx\,dy = \int_0^1 F(s)
\frac{r^{a+b}}{\Gamma(a)\Gamma(b)}s^{a-1}(1-s)^{-a-1}\int_0^\infty y^{a+b-1}e^{-ry/(1-s)}\,dy\,
ds\,,$$
$\gamma_{a,r}$ the Gamma density `gammaPDF a r`.
Proof: M, about 55 lines. Restrict both integrals to `Ioi 0` (`gammaPDF_of_neg`; the point $0$
is null); `lintegral_Ioi_comp_div_add` for each $y > 0$; `lintegral_lintegral_swap`;
`lintegral_const_mul'`; `ofReal_integral_eq_lintegral_ofReal` for the $y$-integral;
`Real.exp_add` for $e^{-rys/(1-s)}e^{-ry} = e^{-ry/(1-s)}$. -/
private theorem lintegral_lintegral_comp_div_add_gammaPDF {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∫⁻ y, (∫⁻ x, F (x / (x + y)) * gammaPDF a r x) * gammaPDF b r y =
      ∫⁻ s in Ioo (0 : ℝ) 1, F s * ENNReal.ofReal
        (r ^ (a + b) / (Real.Gamma a * Real.Gamma b) * s ^ (a - 1) * (1 - s) ^ (-a - 1) *
          ∫ y in Ioi (0 : ℝ), y ^ (a + b - 1) * Real.exp (-(r / (1 - s) * y))) := by
  sorry

/-- The Gamma-ratio integral is the Beta integral: for measurable $F \ge 0$ and $a, b, r > 0$,
$$\iint F\Bigl(\frac{x}{x+y}\Bigr)\gamma_{a,r}(x)\gamma_{b,r}(y)\,dx\,dy = \int F(s)\,
\beta_{a,b}(s)\,ds\,,$$
$\gamma_{a,r}$ the Gamma density `gammaPDF a r` and $\beta_{a,b}$ the Beta density
`betaPDF a b`.
Proof: M, about 40 lines. `lintegral_lintegral_comp_div_add_gammaPDF`; the $y$-integral by
`Real.integral_rpow_mul_exp_neg_mul_Ioi` at rate $r/(1-s)$, which is
$\Gamma(a+b)((1-s)/r)^{a+b}$; the constants $r^{a+b}\Gamma(a+b)r^{-(a+b)}/(\Gamma(a)\Gamma(b))
= 1/B(a,b)$ (`ProbabilityTheory.beta`, `Real.Gamma_pos_of_pos`); `betaPDF_of_pos_lt_one` on
`Ioo 0 1` and `betaPDF_eq_zero_of_nonpos`, `betaPDF_eq_zero_of_one_le` to extend to
$\mathbb{R}$. -/
private theorem lintegral_lintegral_comp_div_add_gammaPDF_eq_betaPDF {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∫⁻ y, (∫⁻ x, F (x / (x + y)) * gammaPDF a r x) * gammaPDF b r y =
      ∫⁻ s, F s * betaPDF a b s := by
  sorry

/-- **Beta as a ratio of Gammas**: for $a, b, r > 0$, the image of
$\mathrm{Gamma}(a, r) \otimes \mathrm{Gamma}(b, r)$ (shapes $a$, $b$, common rate $r$) under
$(x, y) \mapsto x/(x+y)$ is $\mathrm{Beta}(a, b)$.
No printed source.
Proof: M, about 30 lines. `Measure.ext`; `Measure.map_apply` (measurability of
$p \mapsto p.1/(p.1+p.2)$), `Measure.prod_apply` or `lintegral_prod`, `gammaMeasure` and
`lintegral_withDensity_eq_lintegral_mul₀` twice, then
`lintegral_lintegral_comp_div_add_gammaPDF_eq_betaPDF` with $F = \mathbf{1}_S$, and
`betaMeasure`, `withDensity_apply`.
Result: gamma-ratio-beta -/
theorem map_div_add_prod_gammaMeasure {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map (fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) =
      betaMeasure a b := by
  sorry

/-- Beta as a ratio of Gammas, `HasLaw` form: for $a, b, r > 0$ and independent
$X \sim \mathrm{Gamma}(a, r)$ and $Y \sim \mathrm{Gamma}(b, r)$ (shapes $a$, $b$, common rate
$r$), $X/(X+Y) \sim \mathrm{Beta}(a, b)$.
Proof: S, about 8 lines. `indepFun_iff_map_prod_eq_prod_map_map` gives the law of $(X, Y)$ as
`(gammaMeasure a r).prod (gammaMeasure b r)` (`hX.map_eq`, `hY.map_eq`); `HasLaw.comp` with
`map_div_add_prod_gammaMeasure`. -/
theorem hasLaw_div_add_of_hasLaw_gammaMeasure {X Y : Ω → ℝ} {a b r : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (hX : HasLaw X (gammaMeasure a r) μ)
    (hY : HasLaw Y (gammaMeasure b r) μ) (hXY : IndepFun X Y μ) :
    HasLaw (fun ω => X ω / (X ω + Y ω)) (betaMeasure a b) μ := by
  sorry

/-! ### The Beta sub-Gaussian proxy -/

/-- The tilted moments of a Beta law,
$\varphi_k(s) = \mathbb{E}\,X^k e^{sX}$ for $X \sim \mathrm{Beta}(\alpha, \beta)$: the
moment-generating integrals of the proxy proof. -/
private noncomputable def betaExpMoment (α β : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  ∫ x, x ^ k * Real.exp (s * x) ∂betaMeasure α β

/-- The derivative of $x^\alpha(1-x)^\beta e^{tx}$ on $(0, 1)$ is
$x^{\alpha-1}(1-x)^{\beta-1}(\alpha - (\alpha+\beta)x + tx(1-x))e^{tx}$.
Proof: S, about 25 lines. `HasDerivAt.rpow_const` for $x^\alpha$ and $(1-x)^\beta$ (bases
nonzero on `Ioo 0 1`), `HasDerivAt.mul`, `Real.hasDerivAt_exp`, `HasDerivAt.const_sub`;
`Real.rpow_sub_one` to factor out $x^{\alpha-1}(1-x)^{\beta-1}$; `ring`. -/
private theorem hasDerivAt_rpow_mul_rpow_mul_exp {α β t x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => x ^ α * (1 - x) ^ β * Real.exp (t * x))
      (x ^ (α - 1) * (1 - x) ^ (β - 1) *
        ((α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x))) x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hxne : x ≠ 0 := hx0.ne'
  have hx1ne : (1 - x) ≠ 0 := by linarith
  have hxpos : 0 < x := hx0
  have hx1pos : 0 < 1 - x := by linarith
  have h1 : HasDerivAt (fun x : ℝ => x ^ α) (α * x ^ (α - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hxne)
  have h2 := ((hasDerivAt_id' x).const_sub 1).rpow_const (p := β) (Or.inl hx1ne)
  have h3 := ((hasDerivAt_id' x).const_mul t).exp
  have h4 := (h1.mul h2).mul h3
  refine h4.congr_deriv ?_
  have e1 : x ^ α = x ^ (α - 1) * x := by
    rw [← Real.rpow_add_one hxne]; ring_nf
  have e2 : (1 - x) ^ β = (1 - x) ^ (β - 1) * (1 - x) := by
    rw [← Real.rpow_add_one hx1ne]; ring_nf
  simp only [Pi.mul_apply]
  rw [e1, e2]
  ring

/-- For $\alpha, \beta > 0$ and real $t$, the derivative
$x^{\alpha-1}(1-x)^{\beta-1}(\alpha - (\alpha+\beta)x + tx(1-x))e^{tx}$ is interval integrable
on $[0, 1]$.
Proof: M, about 30 lines. A bounded continuous factor on `Icc 0 1` times `betaPDFReal`;
integrability of `betaPDFReal` from `lintegral_betaPDF_eq_one` (a finite lintegral of
`ENNReal.ofReal`, `HasFiniteIntegral`); `IntervalIntegrable.mul_continuousOn`;
`intervalIntegrable_iff_integrableOn_Ioo_of_le`. -/
private theorem intervalIntegrable_rpow_mul_rpow_mul_exp {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (t : ℝ) :
    IntervalIntegrable (fun x => x ^ (α - 1) * (1 - x) ^ (β - 1) *
      ((α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x))) volume 0 1 := by
  have hnn : ∀ x, 0 ≤ betaPDFReal α β x := by
    intro x
    unfold betaPDFReal
    split_ifs with h
    · have : 0 < beta α β := beta_pos hα hβ
      have h1 : 0 ≤ x ^ (α - 1) := Real.rpow_nonneg h.1.le _
      have h2 : 0 ≤ (1 - x) ^ (β - 1) := Real.rpow_nonneg (by linarith [h.2]) _
      positivity
    · exact le_rfl
  have hint : Integrable (betaPDFReal α β) := by
    refine ⟨(measurable_betaPDFReal α β).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)]
    have := lintegral_betaPDF_eq_one hα hβ
    unfold betaPDF at this
    rw [this]
    exact ENNReal.one_lt_top
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖(α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x)‖ ≤ C :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc (by fun_prop)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  refine Integrable.mono' (hint.const_mul (beta α β * C)).integrableOn ?_ ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx' : (0 < x ∧ x < 1) := hx
    have hB : 0 < beta α β := beta_pos hα hβ
    have hB' : beta α β ≠ 0 := hB.ne'
    have hCx : ‖(α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x)‖ ≤ C :=
      hC x (Ioo_subset_Icc_self hx)
    have hP : 0 ≤ x ^ (α - 1) * (1 - x) ^ (β - 1) :=
      mul_nonneg (Real.rpow_nonneg hx'.1.le _) (Real.rpow_nonneg (by linarith [hx'.2]) _)
    have hpdf : betaPDFReal α β x = 1 / beta α β * (x ^ (α - 1) * (1 - x) ^ (β - 1)) := by
      unfold betaPDFReal
      rw [if_pos hx']
      ring
    rw [hpdf, norm_mul, Real.norm_of_nonneg hP,
      show beta α β * C * (1 / beta α β * (x ^ (α - 1) * (1 - x) ^ (β - 1)))
        = C * (x ^ (α - 1) * (1 - x) ^ (β - 1)) by field_simp, mul_comm C]
    exact mul_le_mul_of_nonneg_left hCx hP

/-- Integration by parts on $[0, 1]$: for $\alpha, \beta > 0$ and real $t$,
$$\int_0^1 x^{\alpha-1}(1-x)^{\beta-1}(\alpha - (\alpha+\beta)x + tx(1-x))e^{tx}\,dx = 0\,,$$
since $x^\alpha(1-x)^\beta e^{tx}$ vanishes at $0$ and $1$.
Proof: S, about 15 lines. `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` with
`hasDerivAt_rpow_mul_rpow_mul_exp` on the interior and
`intervalIntegrable_rpow_mul_rpow_mul_exp`; continuity on `Icc 0 1` by
`ContinuousAt.rpow_const` ($0 < \alpha$, $0 < \beta$); endpoint values $0$ by
`Real.zero_rpow`. -/
private theorem intervalIntegral_rpow_mul_rpow_mul_exp_eq_zero {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (t : ℝ) :
    ∫ x in (0 : ℝ)..1, x ^ (α - 1) * (1 - x) ^ (β - 1) *
      ((α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x)) = 0 := by
  sorry

/-- Kummer's equation in integral form: for $X \sim \mathrm{Beta}(\alpha, \beta)$,
$\alpha, \beta > 0$ and real $t$,
$\mathbb{E}[(\alpha - (\alpha+\beta)X + tX(1-X))e^{tX}] = 0$.
Proof: M, about 30 lines. `integral_withDensity_eq_integral_toReal_smul`
(`measurable_betaPDFReal`), `ENNReal.toReal_ofReal` (nonnegativity of `betaPDFReal`),
`setIntegral_eq_integral_of_forall_compl_eq_zero` to restrict to $(0, 1)$,
`intervalIntegral.integral_of_le`, `integral_Ioc_eq_integral_Ioo`, `integral_const_mul` with
the Beta constant, then `intervalIntegral_rpow_mul_rpow_mul_exp_eq_zero`. -/
private theorem integral_sub_mul_add_mul_exp_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (t : ℝ) :
    ∫ x, (α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x) ∂betaMeasure α β = 0 := by
  sorry

/-- A Beta law lives on $[0, 1]$: for all $\alpha, \beta$, almost every point of
`betaMeasure α β` lies in $[0, 1]$.
Proof: S, about 8 lines. `ae_iff`, `betaMeasure`, `withDensity_apply`; `betaPDF_eq_zero_of_nonpos`
and `betaPDF_eq_zero_of_one_le` make the density $0$ off $(0, 1)$ (`setLIntegral_eq_zero`-type
step). -/
private theorem ae_mem_Icc_betaMeasure (α β : ℝ) : ∀ᵐ x ∂betaMeasure α β, x ∈ Icc (0 : ℝ) 1 := by
  have hs : MeasurableSet {x : ℝ | x ∉ Icc (0 : ℝ) 1} := measurableSet_Icc.compl
  rw [betaMeasure, ae_iff, withDensity_apply _ hs]
  refine (setLIntegral_congr_fun (g := fun _ => 0) hs fun x hx => ?_).trans (by simp)
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact betaPDF_eq_zero_of_nonpos hx.le
  · exact betaPDF_eq_zero_of_one_le hx.le

/-- The tilted moments differentiate up: for $\alpha, \beta > 0$, every $k$ and real $t$,
$\varphi_k' (t) = \varphi_{k+1}(t)$, where $\varphi_k(s) = \mathbb{E}\,X^k e^{sX}$ for
$X \sim \mathrm{Beta}(\alpha, \beta)$.
Proof: S, about 12 lines. `haveI := isProbabilityMeasureBeta hα hβ` (a lemma, not an instance);
exponential integrability for every $s$ from boundedness on the support
(`ae_mem_Icc_betaMeasure`, `Integrable.of_bound`), so `interior (integrableExpSet id _) = univ`;
then `hasDerivAt_integral_pow_mul_exp_real`. -/
private theorem hasDerivAt_betaExpMoment {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) (t : ℝ) :
    HasDerivAt (betaExpMoment α β k) (betaExpMoment α β (k + 1) t) t := by
  have := isProbabilityMeasureBeta hα hβ
  have hint : ∀ s : ℝ, Integrable (fun x : ℝ => Real.exp (s * x)) (betaMeasure α β) := by
    intro s
    refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) (Real.exp |s|) ?_
    filter_upwards [ae_mem_Icc_betaMeasure α β] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
    nlinarith [abs_nonneg s, le_abs_self s, hx.1, hx.2, neg_abs_le s]
  have huniv : interior (integrableExpSet id (betaMeasure α β)) = univ := by
    have hall : integrableExpSet id (betaMeasure α β) = univ :=
      Set.eq_univ_of_forall fun s => hint s
    rw [hall, interior_univ]
  have hmem : t ∈ interior (integrableExpSet id (betaMeasure α β)) := by
    rw [huniv]; exact mem_univ t
  exact hasDerivAt_integral_pow_mul_exp_real hmem k

/-- The tilted mass is positive: for $\alpha, \beta > 0$ and real $t$,
$\mathbb{E}\,e^{tX} > 0$ for $X \sim \mathrm{Beta}(\alpha, \beta)$.
Proof: S, about 6 lines. `haveI := isProbabilityMeasureBeta hα hβ`; `pow_zero`, `one_mul`;
`integral_exp_pos` with integrability from `ae_mem_Icc_betaMeasure` (`Integrable.of_bound`). -/
private theorem betaExpMoment_zero_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    0 < betaExpMoment α β 0 t := by
  have := isProbabilityMeasureBeta hα hβ
  have hint : Integrable (fun x => Real.exp (t * x)) (betaMeasure α β) := by
    refine Integrable.of_bound (by fun_prop) (Real.exp |t|) ?_
    filter_upwards [ae_mem_Icc_betaMeasure α β] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    calc t * x ≤ |t * x| := le_abs_self _
      _ = |t| * |x| := abs_mul _ _
      _ ≤ |t| * 1 := by gcongr; rw [abs_of_nonneg hx.1]; exact hx.2
      _ = |t| := mul_one _
  have hpos : 0 < ∫ x, Real.exp (t * x) ∂betaMeasure α β :=
    integral_exp_pos (f := fun x => t * x) hint
  simpa [betaExpMoment, pow_zero, one_mul] using hpos

/-- The Riccati identity: with $\varphi_k(t) = \mathbb{E}\,X^k e^{tX}$ for
$X \sim \mathrm{Beta}(\alpha, \beta)$, $y = \varphi_1/\varphi_0$, $b = \alpha + \beta$,
$\sigma^2 = 1/(4(b+1))$ and $z = y - \alpha/b - \sigma^2 t$ (so $z' = \varphi_2/\varphi_0 - y^2 -
\sigma^2$), for $\alpha, \beta > 0$ and real $t$, $tz' + bz = t(y(1-y) - 1/4)$.
Proof: S, about 20 lines. `integral_sub_mul_add_mul_exp_betaMeasure` split by `integral_add`,
`integral_sub`, `integral_const_mul` into $\alpha\varphi_0 - b\varphi_1 + t(\varphi_1 -
\varphi_2) = 0$ (integrability from `ae_mem_Icc_betaMeasure`); `field_simp` with
`betaExpMoment_zero_pos`; `linear_combination`. -/
private theorem mul_sub_add_mul_sub_eq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    t * (betaExpMoment α β 2 t / betaExpMoment α β 0 t -
        (betaExpMoment α β 1 t / betaExpMoment α β 0 t) ^ 2 - 1 / (4 * (α + β + 1))) +
      (α + β) * (betaExpMoment α β 1 t / betaExpMoment α β 0 t - α / (α + β) -
        t / (4 * (α + β + 1))) =
    t * (betaExpMoment α β 1 t / betaExpMoment α β 0 t *
      (1 - betaExpMoment α β 1 t / betaExpMoment α β 0 t) - 1 / 4) := by
  sorry

/-- The comparison step: with $\varphi_k(t) = \mathbb{E}\,X^k e^{tX}$ for
$X \sim \mathrm{Beta}(\alpha, \beta)$, $\alpha, \beta > 0$, and
$z(t) = \varphi_1(t)/\varphi_0(t) - \alpha/(\alpha+\beta) - t/(4(\alpha+\beta+1))$, every real
$t$ has $t\,z(t) \le 0$.
Proof: M, about 55 lines (Lean risk; split hint: the halves $t > 0$ and $t < 0$ as two private
lemmas, 25 to 35 lines each). `HasDerivAt.div` of `hasDerivAt_betaExpMoment` ($\varphi_0 > 0$,
`betaExpMoment_zero_pos`) gives $z'$; for $t > 0$: `antitoneOn_rpow_mul_of_hasDerivAt` with
$f = z$, $b = \alpha+\beta$, the hypothesis from `mul_sub_add_mul_sub_eq` and
$y(1-y) \le 1/4$ (`nlinarith [sq_nonneg (y - 1/2)]`), evaluation at $0$ (`Real.zero_rpow`,
$z(0) = 0$) and `Real.rpow_pos_of_pos`; for $t < 0$: the same lemma for $f(s) = -z(-s)$
(`HasDerivAt.comp_neg`, `HasDerivAt.neg`); $t = 0$ is trivial. Fallback if the reflection is
hard: prove $t > 0$ only and get $t < 0$ from `(betaMeasure α β).map (fun x => 1 - x) =
betaMeasure β α`. -/
private theorem mul_sub_div_sub_div_nonpos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    t * (betaExpMoment α β 1 t / betaExpMoment α β 0 t - α / (α + β) -
      t / (4 * (α + β + 1))) ≤ 0 := by
  sorry

/-- The cumulant bound: for $X \sim \mathrm{Beta}(\alpha, \beta)$, $\alpha, \beta > 0$ and real
$t$, $\log\mathbb{E}\,e^{tX} - \alpha t/(\alpha+\beta) \le t^2/(8(\alpha+\beta+1))$.
Proof: M, about 45 lines. $g(t) = \log\varphi_0(t) - \alpha t/(\alpha+\beta) -
t^2/(8(\alpha+\beta+1))$ has derivative $z$ (`HasDerivAt.log`, `hasDerivAt_betaExpMoment`,
`betaExpMoment_zero_pos`) and $g(0) = 0$ (`integral_const`, probability, `Real.log_one`);
`antitoneOn_of_deriv_nonpos` on `Ici 0` and `monotoneOn_of_deriv_nonneg` on `Iic 0`, the signs
from `mul_sub_div_sub_div_nonpos`. -/
private theorem log_betaExpMoment_sub_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    Real.log (betaExpMoment α β 0 t) - α / (α + β) * t ≤ t ^ 2 / (8 * (α + β + 1)) := by
  sorry

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
Proof: M, about 30 lines. Exponential integrability from boundedness on the support
(`ae_mem_Icc_betaMeasure`); `mgf` of $X - \mu_0$ is $e^{-\mu_0 t}\varphi_0(t)$
(`integral_const_mul`, `Real.exp_sub`); `Real.exp_log` (`betaExpMoment_zero_pos`),
`log_betaExpMoment_sub_le`, `Real.exp_le_exp`; the proxy as a real is
`by rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (by positivity)]`.
Result: beta-subgaussian -/
theorem hasSubgaussianMGF_sub_div_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    HasSubgaussianMGF (fun x => x - α / (α + β)) ‖1 / (4 * (α + β + 1))‖₊ (betaMeasure α β) := by
  sorry

/-- Beta laws are sub-Gaussian, `HasLaw` form: for $X \sim \mathrm{Beta}(\alpha, \beta)$ with
$\alpha, \beta > 0$, $X - \alpha/(\alpha+\beta)$ satisfies the sub-Gaussian moment generating
function bound with variance proxy $1/(4(\alpha+\beta+1))$.
Proof: S, about 8 lines. `HasSubgaussianMGF.id_map_iff` on both sides, `Measure.map_map`,
`hX.map_eq` (the pattern of `NLAlib.hasSubgaussianMGF_of_hasLaw_gaussianReal`), and
`hasSubgaussianMGF_sub_div_betaMeasure`. -/
theorem hasSubgaussianMGF_sub_div_of_hasLaw_betaMeasure {X : Ω → ℝ} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hX : HasLaw X (betaMeasure α β) μ) :
    HasSubgaussianMGF (fun ω => X ω - α / (α + β)) ‖1 / (4 * (α + β + 1))‖₊ μ := by
  sorry

end ProbabilityTheory
