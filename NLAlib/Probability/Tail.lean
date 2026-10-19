/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Tail probabilities and moments

Tail bounds in NLAlib are failure probabilities in $\mathbb{R}$, with non-strict events:
`μ.real {ω | t ≤ f ω} ≤ bound` (`docs/PORT_PROBABILITY.md` D3). Mathlib's Chernoff bound
`ProbabilityTheory.measure_ge_le_exp_mul_mgf` and Markov's inequality
`MeasureTheory.mul_meas_ge_le_integral_of_nonneg` already have this form; the union bound and the
complement are `MeasureTheory.measureReal_union_le`, `MeasureTheory.measureReal_biUnion_finset_le`
and `MeasureTheory.probReal_compl_eq_one_sub`. This file adds Markov's inequality in quotient
form, Chebyshev's inequality in $\mathbb{R}$, the two-sided tail, Markov's inequality off a
failure event, the passage from a tail bound to integrability and to a bound on the mean,
Chernoff's bound inverted for a sub-gamma moment generating function, and Jensen's inequality for
a power of a sum of random variables.

## Main results

* `NLAlib.measureReal_ge_le_integral_div`: Markov's inequality.
* `NLAlib.measureReal_abs_ge_le_integral_rpow_div`: Markov's inequality for a moment.
* `NLAlib.measureReal_ge_le_variance_div_sq`: Chebyshev's inequality.
* `NLAlib.measureReal_abs_ge_le_add`: a two-sided tail is at most the sum of the one-sided tails.
* `NLAlib.measureReal_le_add_one_div`: Markov's inequality off a failure event, the step of
  every subspace-injection tail.
* `NLAlib.integrable_of_measureReal_ge_le`, `NLAlib.integral_le_of_measureReal_ge_le`: a
  nonnegative random variable with an integrable tail bound is integrable, and its mean is at most
  the integral of the bound.
* `NLAlib.measureReal_ge_le_exp_neg_of_mgf_le`: Chernoff's bound for a sub-gamma upper tail, with
  the exact constant.
* `NLAlib.integrable_rpow_sum`, `NLAlib.integral_rpow_sum_le`: a power $r \ge 1$ of a finite sum of
  nonnegative random variables is integrable, and weighted Jensen bounds its mean.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Markov's inequality** as a failure probability: $\mu\{t \le f\} \le (\int f \, d\mu) / t$ for
$f$ integrable and nonnegative almost everywhere, and $t > 0$. Integrability is needed: otherwise
the Bochner integral $\int f \, d\mu$ is $0$.
Result: markov-inequality -/
theorem measureReal_ge_le_integral_div {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[μ] f) (hf : Integrable f μ)
    {t : ℝ} (ht : 0 < t) : μ.real {ω | t ≤ f ω} ≤ (∫ ω, f ω ∂μ) / t := by
  rw [le_div_iff₀ ht, mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg hf0 hf t

/-- **Markov's inequality for a moment**:
$\mu\{t \le \lvert X\rvert\} \le (\int \lvert X\rvert^p \, d\mu) / t^p$ for real $t, p > 0$. Every
tail derived from a moment bound ends here. Integrability of $\lvert X\rvert^p$ is needed:
otherwise its integral is $0$. -/
theorem measureReal_abs_ge_le_integral_rpow_div {X : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hX : Integrable (fun ω => |X ω| ^ p) μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} ≤ (∫ ω, |X ω| ^ p ∂μ) / t ^ p := by
  have hset : {ω | t ≤ |X ω|} = {ω | t ^ p ≤ |X ω| ^ p} := by
    ext ω
    exact (Real.rpow_le_rpow_iff ht.le (abs_nonneg _) hp).symm
  rw [hset]
  exact measureReal_ge_le_integral_div
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) p) hX
    (Real.rpow_pos_of_pos ht p)

/-- **Chebyshev's inequality** as a failure probability: for a finite measure $\mu$, $X \in L^2$
and $t > 0$, $\mu\{t \le \lvert X - \mathbb{E} X\rvert\} \le \operatorname{Var} X / t^2$, with
$\mathbb{E} X = \int X \, d\mu$.
Result: chebyshev-inequality -/
theorem measureReal_ge_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|} ≤ variance X μ / t ^ 2 := by
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg X μ) (sq_nonneg t))
    (meas_ge_le_variance_div_sq hX ht)

/-- A two-sided tail is at most the sum of the upper and the lower tail:
$\mu\{t \le \lvert X\rvert\} \le \mu\{t \le X\} + \mu\{X \le -t\}$. -/
theorem measureReal_abs_ge_le_add (X : Ω → ℝ) (t : ℝ) :
    μ.real {ω | t ≤ |X ω|} ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | X ω ≤ -t} := by
  have h : {ω | t ≤ |X ω|} = {ω | t ≤ X ω} ∪ {ω | X ω ≤ -t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs, le_neg]
  rw [h]
  exact measureReal_union_le _ _

/-- **Markov's inequality off a failure event**: if $\mu(G^c) \le \delta$, $M \ge 0$ is integrable
with mean $m$ (and vanishes when $m = 0$), and on $G$ the event $E$ forces $t m < M$, then for
$t > 0$
$$\mu(E) \le \delta + \frac{1}{t}\,.$$
The common step of the subspace-injection tails (`NLAlib.Regression.Oblivious`) and
the oblivious low-rank tails. -/
theorem measureReal_le_add_one_div [IsFiniteMeasure μ] {δ t : ℝ} {G E : Set Ω}
    (hG : μ.real Gᶜ ≤ δ) {M : Ω → ℝ} (hM0 : ∀ ω, 0 ≤ M ω) (hM : Integrable M μ) {m : ℝ}
    (hm : ∫ ω, M ω ∂μ = m) (hm0 : m = 0 → ∀ ω, M ω = 0) (ht : 0 < t)
    (hE : ∀ᵐ ω ∂μ, ω ∈ G → ω ∈ E → t * m < M ω) : μ.real E ≤ δ + 1 / t := by
  have hae : ∀ᵐ ω ∂μ, ω ∈ E → ω ∈ Gᶜ ∪ {ω | t * m < M ω} := by
    filter_upwards [hE] with ω hω hωE
    by_cases hωG : ω ∈ G
    · exact Or.inr (hω hωG hωE)
    · exact Or.inl hωG
  have hF : μ.real {ω | t * m < M ω} ≤ 1 / t := by
    rcases eq_or_ne m 0 with h0 | h0
    · have he : {ω | t * m < M ω} = ∅ := by
        ext ω
        simp only [hm0 h0 ω, h0, mul_zero, lt_self_iff_false, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false]
      rw [he, measureReal_empty]
      positivity
    · have hm' : 0 < m := lt_of_le_of_ne (hm ▸ integral_nonneg hM0) (Ne.symm h0)
      calc μ.real {ω | t * m < M ω} ≤ μ.real {ω | t * m ≤ M ω} :=
            measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω => hω.le)
        _ ≤ (∫ ω, M ω ∂μ) / (t * m) :=
            measureReal_ge_le_integral_div (ae_of_all _ hM0) hM (mul_pos ht hm')
        _ = 1 / t := by
            rw [hm]
            field_simp
  calc μ.real E ≤ μ.real (Gᶜ ∪ {ω | t * m < M ω}) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)
    _ ≤ μ.real Gᶜ + μ.real {ω | t * m < M ω} := measureReal_union_le _ _
    _ ≤ δ + 1 / t := add_le_add hG hF

private theorem lintegral_ofReal_le_of_measureReal_ge_le [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} (ha : 0 ≤ a) {F : ℝ → ℝ}
    (hF : IntegrableOn F (Set.Ioi a)) (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤
      μ Set.univ * ENNReal.ofReal a + ENNReal.ofReal (∫ t in Set.Ioi a, F t) := by
  have hF0 : 0 ≤ᵐ[volume.restrict (Set.Ioi a)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact measureReal_nonneg.trans (htail t ht)
  rw [lintegral_eq_lintegral_meas_lt μ hf0 hf, ← Set.Ioc_union_Ioi_eq_Ioi ha,
    lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same,
    ofReal_integral_eq_lintegral_ofReal hF hF0]
  gcongr ?_ + ?_
  · calc ∫⁻ t in Set.Ioc 0 a, μ {x | t < f x} ≤ ∫⁻ _ in Set.Ioc 0 a, μ Set.univ :=
          lintegral_mono fun _ => measure_mono (Set.subset_univ _)
      _ = μ Set.univ * ENNReal.ofReal a := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  · refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    calc μ {x | t < f x} ≤ μ {x | t ≤ f x} := measure_mono fun _ hx => le_of_lt (α := ℝ) hx
      _ = ENNReal.ofReal (μ.real {x | t ≤ f x}) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (F t) := ENNReal.ofReal_le_ofReal (htail t ht)

private theorem integral_le_of_measureReal_ge_le_of_nonneg [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} (ha : 0 ≤ a) {F : ℝ → ℝ}
    (hF : IntegrableOn F (Set.Ioi a)) (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) :
    ∫ ω, f ω ∂μ ≤ a + ∫ t in Set.Ioi a, F t := by
  have hF0 : 0 ≤ ∫ t in Set.Ioi a, F t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht => measureReal_nonneg.trans (htail t ht)
  have hbound := lintegral_ofReal_le_of_measureReal_ge_le hf hf0 ha hF htail
  rw [measure_univ, one_mul, ← ENNReal.ofReal_add ha hF0] at hbound
  rw [integral_eq_lintegral_of_nonneg_ae hf0 hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (add_nonneg ha hF0) hbound

/-- On a finite measure space, a nonnegative random variable $f$ whose tail beyond $a$ is bounded
by a function $F$ integrable on $(a, \infty)$, $\mu\{t \le f\} \le F(t)$ for $t > a$, is
integrable. A bound on the strict tail $\{t < f\}$ follows from one on $\{t \le f\}$ by
monotonicity, so the hypothesis is stated in the non-strict form that tail theorems produce. -/
theorem integrable_of_measureReal_ge_le [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEMeasurable f μ)
    (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} {F : ℝ → ℝ} (hF : IntegrableOn F (Set.Ioi a))
    (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) : Integrable f μ := by
  have hF' : IntegrableOn F (Set.Ioi (max a 0)) :=
    hF.mono_set (Set.Ioi_subset_Ioi (le_max_left a 0))
  have hbound := lintegral_ofReal_le_of_measureReal_ge_le hf hf0 (le_max_right a 0) hF'
    fun t ht => htail t ((le_max_left a 0).trans_lt ht)
  refine ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hf0).2 ?_⟩
  exact hbound.trans_lt (ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top (measure_lt_top μ _) ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)

/-- **The layer-cake bound**: under a probability measure, if $f \ge 0$ almost everywhere and
$\mathbb{P}[t \le f] \le F(t)$ for all $t > a$, with $F$ integrable on $(a, \infty)$, then
$$\mathbb{E} f \le a + \int_a^\infty F(t) \, dt\,.$$
Applied to $f^p$, whose tail at $t$ is the tail of $f$ at $t^{1/p}$, it bounds the moments of $f$.
Integrability of $f$ is `integrable_of_measureReal_ge_le`. -/
theorem integral_le_of_measureReal_ge_le [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} {F : ℝ → ℝ}
    (hF : IntegrableOn F (Set.Ioi a)) (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) :
    ∫ ω, f ω ∂μ ≤ a + ∫ t in Set.Ioi a, F t := by
  rcases le_or_gt 0 a with ha | ha
  · exact integral_le_of_measureReal_ge_le_of_nonneg hf hf0 ha hF htail
  have hF0 : IntegrableOn F (Set.Ioi 0) := hF.mono_set (Set.Ioi_subset_Ioi ha.le)
  have h0 := integral_le_of_measureReal_ge_le_of_nonneg hf hf0 le_rfl hF0
    fun t ht => htail t (ha.trans ht)
  have h1 : -a ≤ ∫ t in Set.Ioc a 0, F t := by
    have hle : ∫ _ in Set.Ioc a 0, (1 : ℝ) ≤ ∫ t in Set.Ioc a 0, F t := by
      refine setIntegral_mono_on (integrableOn_const (by simp))
        (hF.mono_set Set.Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht => ?_
      refine le_trans (le_of_eq ?_) (htail t ht.1)
      rw [measureReal_def, measure_congr (ae_eq_univ.2 ?_), measure_univ, ENNReal.toReal_one]
      exact ae_iff.1 (hf0.mono fun ω hω => ht.2.trans hω)
    simpa [ha.le] using hle
  rw [← Set.Ioc_union_Ioi_eq_Ioi ha.le, setIntegral_union Set.Ioc_disjoint_Ioi_same
    measurableSet_Ioi (hF.mono_set Set.Ioc_subset_Ioi_self) hF0]
  linarith

/-! ### Sub-gamma tails -/

/-- **Chernoff's bound for a sub-gamma upper tail.** If the moment generating function of $X$
satisfies
$$\mathbb{E}\, e^{\theta X} \le \exp \frac{\theta^2 v}{2 (1 - b\theta)}$$
for every $\theta \ge 0$ with $b\theta < 1$ (and $e^{\theta X}$ is integrable there), then for
$t \ge 0$
$$\mu\bigl(X \ge \sqrt{2 v t} + b t\bigr) \le e^{-t}\,.$$
Chernoff's bound at $\theta = s / (1 + b s)$, $s = \sqrt{2t/v}$, where the exponent is exactly
$-t$. No finiteness assumption on $\mu$: integrability at $\theta = 0$ gives it. $v > 0$ is needed:
at $v = b = 0$ the constant $0$ satisfies the hypothesis and the event is everything. The exact
constant, which the $\min(t^2/v, t/b)$ forms of `NLAlib.Probability.SubExponential.Tail` lose; the
step behind every exact-constant Bernstein-type tail (the Hsu–Kakade–Zhang tail
`NLAlib.IsSubgaussianVector.measureReal_norm_mulVec_sq_ge_le`). [BoucheronLugosiMassart2013] (the
sub-gamma tail of their Chapter 2; locator not checked against the book). -/
theorem measureReal_ge_le_exp_neg_of_mgf_le {X : Ω → ℝ} {v b : ℝ} (hv : 0 < v) (hb : 0 ≤ b)
    (hint : ∀ θ : ℝ, 0 ≤ θ → b * θ < 1 → Integrable (fun ω => Real.exp (θ * X ω)) μ)
    (hmgf : ∀ θ : ℝ, 0 ≤ θ → b * θ < 1 →
      mgf X μ θ ≤ Real.exp (θ ^ 2 * v / (2 * (1 - b * θ))))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √(2 * v * t) + b * t ≤ X ω} ≤ Real.exp (-t) := by
  have : IsFiniteMeasure μ := by
    have h0 := hint 0 le_rfl (by simp)
    simp only [zero_mul, Real.exp_zero] at h0
    exact (integrable_const_iff_isFiniteMeasure one_ne_zero).1 h0
  set s := √(2 * t / v) with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 * v = 2 * t := by
    rw [hs_def, Real.sq_sqrt (by positivity)]
    field_simp
  have hsa : s * √(2 * v * t) = 2 * t := by
    rw [hs_def, ← Real.sqrt_mul (by positivity),
      show 2 * t / v * (2 * v * t) = (2 * t) ^ 2 by field_simp, Real.sqrt_sq (by positivity)]
  set D := 1 + b * s with hD
  have hD0 : 0 < D := by positivity
  set θ := s / D with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hbθ : 1 - b * θ = D⁻¹ := by
    rw [hθ, hD]
    field_simp
    ring
  have hbθ1 : b * θ < 1 := by
    have : 0 < D⁻¹ := inv_pos.2 hD0
    linarith
  refine (measure_ge_le_exp_mul_mgf _ hθ0 (hint θ hθ0 hbθ1)).trans ?_
  calc Real.exp (-θ * (√(2 * v * t) + b * t)) * mgf X μ θ
      ≤ Real.exp (-θ * (√(2 * v * t) + b * t)) *
          Real.exp (θ ^ 2 * v / (2 * (1 - b * θ))) := by
        gcongr
        exact hmgf θ hθ0 hbθ1
    _ = Real.exp (-t) := by
        rw [← Real.exp_add, hbθ]
        congr 1
        rw [hθ]
        field_simp
        linear_combination (-2) * hsa + hs2 + 2 * t * hD

/-! ### Moments of a sum -/

/-- For $r \ge 1$ and nonnegative $Y_i$ with each $Y_i^r$ integrable, $(\sum_i Y_i)^r$ is
integrable: it is at most $\lvert\iota\rvert^{r-1}\sum_i Y_i^r$
(`Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg`). -/
theorem integrable_rpow_sum {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ} (hY0 : ∀ i ω, 0 ≤ Y i ω)
    {r : ℝ} (hr : 1 ≤ r) (hm : AEStronglyMeasurable (fun ω => (∑ i, Y i ω) ^ r) μ)
    (hint : ∀ i, Integrable (fun ω => Y i ω ^ r) μ) :
    Integrable (fun ω => (∑ i, Y i ω) ^ r) μ := by
  have hsum : Integrable (fun ω => ∑ i, Y i ω ^ r) μ :=
    integrable_finsetSum Finset.univ (f := fun i ω => Y i ω ^ r) fun i _ => hint i
  refine (hsum.const_mul ((Fintype.card ι : ℝ) ^ (r - 1))).mono' hm (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => hY0 i ω) r)]
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ) (f := fun i => Y i ω)
    hr fun i _ => hY0 i ω
  simpa only [Finset.card_univ] using h

/-- **Weighted Jensen for a sum of nonnegative random variables**: for $r \ge 1$, if
$\mathbb{E}[Y_i^r] \le w_i^r K$ for nonnegative weights $w_i$ summing to one, with $Y_i = 0$
where $w_i = 0$, then $\mathbb{E}[(\sum_i Y_i)^r] \le K$. The sum is integrable by
`NLAlib.integrable_rpow_sum`. -/
theorem integral_rpow_sum_le {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ}
    (hY0 : ∀ i ω, 0 ≤ Y i ω) {r : ℝ} (hr : 1 ≤ r)
    (hm : AEStronglyMeasurable (fun ω => (∑ i, Y i ω) ^ r) μ) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hwY : ∀ i, w i = 0 → ∀ ω, Y i ω = 0)
    (hint : ∀ i, Integrable (fun ω => Y i ω ^ r) μ) {K : ℝ}
    (hK : ∀ i, ∫ ω, Y i ω ^ r ∂μ ≤ w i ^ r * K) :
    ∫ ω, (∑ i, Y i ω) ^ r ∂μ ≤ K := by
  have hpt (ω : Ω) : (∑ i, Y i ω) ^ r ≤ ∑ i, w i * (Y i ω / w i) ^ r := by
    have e : ∑ i, Y i ω = ∑ i, w i * (Y i ω / w i) := Finset.sum_congr rfl fun i _ => by
      rcases eq_or_ne (w i) 0 with h0 | h0
      · rw [h0, hwY i h0 ω, zero_mul]
      · rw [mul_div_cancel₀ _ h0]
    rw [e]
    exact Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ w (fun i => Y i ω / w i)
      (fun i _ => hw0 i) hw1 (fun i _ => div_nonneg (hY0 i ω) (hw0 i)) hr
  have hterm (i : ι) : (fun ω => w i * (Y i ω / w i) ^ r) =
      fun ω => w i / w i ^ r * Y i ω ^ r := by
    funext ω
    rw [Real.div_rpow (hY0 i ω) (hw0 i)]
    ring
  have hti (i : ι) : Integrable (fun ω => w i * (Y i ω / w i) ^ r) μ := by
    rw [hterm]
    exact (hint i).const_mul _
  have hdom : Integrable (fun ω => ∑ i, w i * (Y i ω / w i) ^ r) μ :=
    integrable_finsetSum _ fun i _ => hti i
  refine (integral_mono (integrable_rpow_sum hY0 hr hm hint) hdom hpt).trans ?_
  rw [integral_finsetSum _ fun i _ => hti i]
  calc ∑ i, ∫ ω, w i * (Y i ω / w i) ^ r ∂μ ≤ ∑ i, w i * K :=
        Finset.sum_le_sum fun i _ => ?_
    _ = K := by rw [← Finset.sum_mul, hw1, one_mul]
  rw [hterm, integral_const_mul]
  rcases eq_or_lt_of_le (hw0 i) with h0 | hpos
  · rw [← h0, zero_div, zero_mul, zero_mul]
  · have hwr : 0 < w i ^ r := Real.rpow_pos_of_pos hpos r
    calc w i / w i ^ r * ∫ ω, Y i ω ^ r ∂μ ≤ w i / w i ^ r * (w i ^ r * K) :=
          mul_le_mul_of_nonneg_left (hK i) (div_nonneg hpos.le hwr.le)
      _ = w i * K := by field_simp

end NLAlib
