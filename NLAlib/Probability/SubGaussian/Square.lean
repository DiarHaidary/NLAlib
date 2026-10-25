/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Deriv
public import NLAlib.Probability.SubExponential.Basic
public import NLAlib.Probability.SubGaussian.Moments

/-!
# Squares of sub-Gaussian random variables

The exponential square moment $\mathbb{E} e^{\theta X^2}$ of a sub-Gaussian variable, and the fact
that its centred square $X^2 - \mathbb{E}[X^2]$ is sub-exponential, which is what Bernstein's
inequality and the diagonal part of the Hanson–Wright inequality consume.

The constants of the centred square are written in the statement (`CONTRIBUTING.md` §5.2,
"Numerical bounds"): every pair $(v, b)$ with $2c \le b$ and $16 c^2 b \le (b - 2c) v$, among them
the literature's $(32 c^2, 4 c)$ and the pair $(18 c^2, 18 c)$ that the JL constant uses.

For $k$ independent real $Y_i$, each sub-Gaussian with proxy $1$, with $\mathbb{E}[Y_i^2] = 1$ and
$\mathbb{E}[Y_i^4] \le 3$ (the moments of a standard Gaussian), the relative deviation of
$k^{-1} \sum_i Y_i^2$ from $1$ has the tail $2 e^{-k(\varepsilon^2/4 - \varepsilon^3/6)}$ of
$\chi^2_k$, Dasgupta and Gupta's exponent. The upper half is Chernoff's bound with
$\mathbb{E}[e^{\theta Y^2}] \le (1 - 2\theta)^{-1/2}$ and `Real.log_one_add_le_cubic`; the lower
half is Chernoff's bound with $\mathbb{E}[e^{-\theta Y^2}] \le 1 - \theta + 3\theta^2/2$ at
$\theta = \varepsilon/(2(1 + \varepsilon))$, through `Real.log_one_add_le_cubic_of_nonpos`. A
standard Gaussian and a Rademacher combination $\langle \boldsymbol{\xi}, \mathbf{x} \rangle$ with
$\|\mathbf{x}\| = 1$
($\mathbb{E} \langle \boldsymbol{\xi}, \mathbf{x} \rangle^4 = 3 - 2 \sum_j \mathbf{x}_j^4$)
satisfy the hypotheses; the latter gives the sign-sketch Johnson–Lindenstrauss tail with Gaussian
constants (Achlioptas).

## Main results

* `ProbabilityTheory.HasSubgaussianMGF.integral_exp_mul_sq_le`:
  $\mathbb{E} e^{\theta X^2} \le (1 - 2\theta c)^{-1/2}$.
* `ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral_of_le`: the centred
  square is sub-exponential with variance proxy $v$ and scale $b$ whenever $2c \le b$ and
  $16 c^2 b \le (b - 2c) v$;
  `ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral`, the case
  $(32 c^2, 4 c)$.
* `NLAlib.measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun`: the relative deviation of
  a sum of squares with Gaussian moments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-! ### Gaussian linearisation -/

private lemma lintegral_exp_mul_sq_gaussianReal {a : ℝ} (ha : 2 * a < 1) :
    ∫⁻ g, ENNReal.ofReal (rexp (a * g ^ 2)) ∂(gaussianReal 0 1) =
      ENNReal.ofReal (1 / √(1 - 2 * a)) := by
  have hb : 0 < 1 / 2 - a := by linarith
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul₀ (measurable_gaussianPDF _ _).aemeasurable
      (by fun_prop)]
  have hpt : ∀ x : ℝ, gaussianPDF 0 1 x * ENNReal.ofReal (rexp (a * x ^ 2)) =
      ENNReal.ofReal ((√(2 * π))⁻¹ * rexp (-(1 / 2 - a) * x ^ 2)) := by
    intro x
    rw [gaussianPDF_def, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero, mul_assoc, ← exp_add]
    ring_nf
  simp only [Pi.mul_apply, hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_sq hb).const_mul _)
    (ae_of_all _ fun _ => by positivity), integral_const_mul, integral_gaussian]
  congr 1
  have h1 : π / (1 / 2 - a) = 2 * π / (1 - 2 * a) := by field_simp
  have h2 : 0 < 1 - 2 * a := by linarith
  rw [h1, sqrt_div' _ h2.le]
  have : 0 < √(2 * π) := by positivity
  have : 0 < √(1 - 2 * a) := sqrt_pos.mpr h2
  field_simp

private lemma lintegral_exp_mul_gaussianReal (t : ℝ) :
    ∫⁻ g, ENNReal.ofReal (rexp (t * g)) ∂(gaussianReal 0 1) =
      ENNReal.ofReal (rexp (t ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal t)
    (ae_of_all _ fun _ => (exp_pos _).le)]
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
  simp only [mgf, id, zero_mul, NNReal.coe_one, one_mul, zero_add] at this
  rw [this]

private lemma lintegral_exp_mul_sq_le (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : 2 * θ * c < 1) :
    ∫⁻ ω, ENNReal.ofReal (rexp (θ * X ω ^ 2)) ∂μ ≤ ENNReal.ofReal (1 / √(1 - 2 * θ * c)) := by
  have := h.isFiniteMeasure
  set s := √(2 * θ)
  have hs : s ^ 2 = 2 * θ := sq_sqrt (by linarith)
  have hpt : ∀ x : ℝ, ENNReal.ofReal (rexp (θ * x ^ 2)) =
      ∫⁻ g, ENNReal.ofReal (rexp (s * x * g)) ∂(gaussianReal 0 1) := by
    intro x
    rw [lintegral_exp_mul_gaussianReal, mul_pow, hs]
    ring_nf
  have hX := h.aemeasurable
  have hmeas : AEMeasurable (Function.uncurry fun (ω : Ω) (g : ℝ) =>
      ENNReal.ofReal (rexp (s * X ω * g))) (μ.prod (gaussianReal 0 1)) := by
    have h1 : AEMeasurable (fun p : Ω × ℝ => X p.1) (μ.prod (gaussianReal 0 1)) := hX.comp_fst
    have h2 : AEMeasurable (fun p : Ω × ℝ => p.2) (μ.prod (gaussianReal 0 1)) :=
      measurable_snd.aemeasurable
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (measurable_exp.comp_aemeasurable ((h1.const_mul s).mul h2))
  calc ∫⁻ ω, ENNReal.ofReal (rexp (θ * X ω ^ 2)) ∂μ
      = ∫⁻ ω, ∫⁻ g, ENNReal.ofReal (rexp (s * X ω * g)) ∂(gaussianReal 0 1) ∂μ := by
        simp only [hpt]
    _ = ∫⁻ g, ∫⁻ ω, ENNReal.ofReal (rexp (s * X ω * g)) ∂μ ∂(gaussianReal 0 1) :=
        lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ g, ENNReal.ofReal (rexp ((θ * c) * g ^ 2)) ∂(gaussianReal 0 1) := by
        refine lintegral_mono fun g => ?_
        have hint := h.integrable_exp_mul (s * g)
        have heq : ∫⁻ ω, ENNReal.ofReal (rexp (s * X ω * g)) ∂μ =
            ENNReal.ofReal (mgf X μ (s * g)) := by
          rw [mgf, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (exp_pos _).le)]
          congr 1 with ω
          ring_nf
        rw [heq]
        refine ENNReal.ofReal_le_ofReal ((h.mgf_le (s * g)).trans (exp_le_exp.mpr ?_))
        rw [mul_pow, hs]
        ring_nf
        rfl
    _ = ENNReal.ofReal (1 / √(1 - 2 * θ * c)) := by
        rw [lintegral_exp_mul_sq_gaussianReal (by linarith)]
        ring_nf

/-- $e^{\theta X^2}$ is integrable for a sub-Gaussian $X$ with proxy $c$ when $2 \theta c < 1$ (in
particular for every $\theta \le 0$). -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integrable_exp_mul_sq
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ : 2 * θ * c < 1) :
    Integrable (fun ω => rexp (θ * X ω ^ 2)) μ := by
  have := h.isFiniteMeasure
  have hX := h.aemeasurable
  have hm : AEStronglyMeasurable (fun ω => rexp (θ * X ω ^ 2)) μ :=
    (measurable_exp.comp_aemeasurable ((hX.pow_const 2).const_mul θ)).aestronglyMeasurable
  rcases le_or_gt θ 0 with hθ0 | hθ0
  · refine Integrable.mono' (integrable_const 1) hm (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hθ0 (sq_nonneg _)
  · refine ⟨hm, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (exp_pos _).le)).mpr ?_⟩
    exact (lintegral_exp_mul_sq_le h hθ0.le hθ).trans_lt ENNReal.ofReal_lt_top

/-- $\int e^{\theta X^2} \, d\mu \le (1 - 2\theta c)^{-1/2}$ for a sub-Gaussian $X$ with proxy $c$,
$\theta \ge 0$ and $2\theta c < 1$: the value for a centred Gaussian of variance $c$, by Gaussian
linearisation $e^{\theta x^2} = \mathbb{E}_g\, e^{\sqrt{2\theta}\, g x}$. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integral_exp_mul_sq_le
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ * c < 1) :
    ∫ ω, rexp (θ * X ω ^ 2) ∂μ ≤ 1 / √(1 - 2 * θ * c) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (exp_pos _).le)
    (h.integrable_exp_mul_sq hθ).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (lintegral_exp_mul_sq_le h hθ0 hθ)

/-! ### Moments and the series of $e^{\theta X^2}$ -/

private lemma integral_pow_two_mul_le (h : HasSubgaussianMGF X c μ) (k : ℕ) :
    ∫ ω, X ω ^ (2 * (k + 1)) ∂μ ≤ 2 * (k + 1)! * (2 * c) ^ (k + 1) := by
  have := h.integral_abs_rpow_le (p := 2 * ((k : ℝ) + 1)) (by positivity)
  have hcast : ((2 * (k + 1) : ℕ) : ℝ) = 2 * ((k : ℝ) + 1) := by push_cast; ring
  have hpt : ∀ ω, |X ω| ^ (2 * ((k : ℝ) + 1)) = X ω ^ (2 * (k + 1)) := by
    intro ω
    rw [← hcast, rpow_natCast, pow_abs, abs_of_nonneg (by rw [pow_mul]; positivity)]
  have hhalf : 2 * ((k : ℝ) + 1) / 2 = (k : ℝ) + 1 := by ring
  simp only [hpt, hhalf, Real.Gamma_nat_eq_factorial] at this
  rw [← Nat.cast_succ, rpow_natCast] at this
  refine this.trans_eq ?_
  rw [Nat.factorial_succ]
  push_cast [Nat.succ_eq_add_one]
  ring

private lemma integrable_pow (h : HasSubgaussianMGF X c μ) (n : ℕ) :
    Integrable (fun ω => X ω ^ n) μ :=
  integrable_pow_of_integrable_exp_mul one_ne_zero (h.integrable_exp_mul 1)
    (h.integrable_exp_mul (-1)) n

private lemma integral_exp_mul_sq_sub_le (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : 2 * θ * c < 1) :
    ∫ ω, (rexp (θ * X ω ^ 2) - 1 - θ * X ω ^ 2) ∂μ ≤
      2 * (2 * θ * c) ^ 2 / (1 - 2 * θ * c) := by
  have := h.isFiniteMeasure
  set u := 2 * θ * c with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : 0 < 1 - u := by linarith
  set g : ℕ → Ω → ℝ := fun n ω => (θ * X ω ^ 2) ^ (n + 2) / (n + 2)! with hg
  have hg0 : ∀ n ω, 0 ≤ g n ω := fun n ω => by positivity
  have hsum : ∀ ω, HasSum (fun n => g n ω) (rexp (θ * X ω ^ 2) - 1 - θ * X ω ^ 2) := by
    intro ω
    have := NormedSpace.expSeries_div_hasSum_exp (θ * X ω ^ 2)
    rw [← exp_eq_exp_ℝ, ← hasSum_nat_add_iff' 2] at this
    simpa [Finset.sum_range_succ, sub_sub] using this
  have hgeq : ∀ n, g n = fun ω => θ ^ (n + 2) / (n + 2)! * X ω ^ (2 * (n + 2)) := by
    intro n
    ext ω
    simp only [hg]
    rw [mul_pow, ← pow_mul]
    ring
  have hint : ∀ n, Integrable (g n) μ := fun n => by
    rw [hgeq]
    exact (integrable_pow h _).const_mul _
  have hle : ∀ n, ∫ ω, g n ω ∂μ ≤ 2 * u ^ (n + 2) := by
    intro n
    rw [hgeq, integral_const_mul]
    calc θ ^ (n + 2) / (n + 2)! * ∫ ω, X ω ^ (2 * (n + 2)) ∂μ
        ≤ θ ^ (n + 2) / (n + 2)! * (2 * (n + 2)! * (2 * c) ^ (n + 2)) := by
          gcongr
          exact integral_pow_two_mul_le h (n + 1)
      _ = 2 * u ^ (n + 2) := by
          rw [hu]
          field_simp
          ring
  have hgeom : (fun n : ℕ => 2 * u ^ (n + 2)) = fun n => 2 * u ^ 2 * u ^ n := by
    ext n
    ring
  have hsumm : Summable fun n : ℕ => 2 * u ^ (n + 2) := by
    rw [hgeom]
    exact (summable_geometric_of_lt_one hu0 (by linarith)).mul_left _
  have hφ0 : 0 ≤ᵐ[μ] fun ω => rexp (θ * X ω ^ 2) - 1 - θ * X ω ^ 2 :=
    ae_of_all _ fun ω => (hsum ω).nonneg (hg0 · ω)
  have hφm : AEStronglyMeasurable (fun ω => rexp (θ * X ω ^ 2) - 1 - θ * X ω ^ 2) μ :=
    (((h.integrable_exp_mul_sq hθ).sub (integrable_const 1)).sub
      ((integrable_pow h 2).const_mul θ)).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hφ0 hφm]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc ∫⁻ ω, ENNReal.ofReal (rexp (θ * X ω ^ 2) - 1 - θ * X ω ^ 2) ∂μ
      = ∫⁻ ω, ∑' n, ENNReal.ofReal (g n ω) ∂μ := by
        congr with ω
        rw [← (hsum ω).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (hg0 · ω) (hsum ω).summable]
    _ = ∑' n, ∫⁻ ω, ENNReal.ofReal (g n ω) ∂μ :=
        lintegral_tsum fun n => (hint n).aemeasurable.ennreal_ofReal
    _ ≤ ∑' n, ENNReal.ofReal (2 * u ^ (n + 2)) := ENNReal.tsum_le_tsum fun n => by
        rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all _ (hg0 n))]
        exact ENNReal.ofReal_le_ofReal (hle n)
    _ = ENNReal.ofReal (∑' n, 2 * u ^ (n + 2)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm).symm
    _ = ENNReal.ofReal (2 * u ^ 2 / (1 - u)) := by
        rw [hgeom, tsum_mul_left, tsum_geometric_of_lt_one hu0 (by linarith), div_eq_mul_inv]

/-- $e^{-t} \le 1 - t + t^2/2$ for $t \ge 0$: the difference has derivative
$t - 1 + e^{-t} \ge 0$ and vanishes at $0$. -/
private lemma exp_neg_le_one_sub_add_sq_div_two {t : ℝ} (ht : 0 ≤ t) :
    rexp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  let g : ℝ → ℝ := fun s => 1 - s + s ^ 2 / 2 - rexp (-s)
  have hg : ∀ s, HasDerivAt g (-1 + s + rexp (-s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => 1 - s + s ^ 2 / 2) (-1 + s) s := by
      have := ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id' s)).add
        ((hasDerivAt_pow 2 s).div_const 2)
      exact this.congr_deriv (by norm_num)
    have h2 : HasDerivAt (fun s : ℝ => rexp (-s)) (-rexp (-s)) s :=
      (hasDerivAt_neg s).exp.congr_deriv (by ring)
    exact (h1.sub h2).congr_deriv (by ring)
  have hmono := monotone_of_hasDerivAt_nonneg hg fun s => by
    have := add_one_le_exp (-s)
    simp only [Pi.zero_apply]
    linarith
  have := hmono ht
  simp only [g, neg_zero, exp_zero] at this
  linarith

/-! ### The centred square -/

/-- For $bx < 1$, $16 c^2 \le v(1 - 2cx)$ when $2c \le b$ and $16 c^2 b \le (b - 2c) v$: the
margin of the window $b\lvert l\rvert < 1$. -/
private lemma sixteen_mul_sq_le_mul_one_sub {v b : ℝ} (hc : 0 ≤ (c : ℝ)) (hv0 : 0 ≤ v)
    (hb : 2 * c ≤ b) (hv : 16 * (c : ℝ) ^ 2 * b ≤ (b - 2 * c) * v) {x : ℝ} (hx : b * x < 1) :
    16 * (c : ℝ) ^ 2 ≤ v * (1 - 2 * c * x) := by
  rcases eq_or_lt_of_le hc with h0 | h0
  · rw [← h0]
    nlinarith
  have hb0 : 0 < b := by linarith
  have h1 : 0 ≤ 2 * c * (1 - b * x) := by nlinarith
  have h2 : (b - 2 * c) * v ≤ b * (v * (1 - 2 * c * x)) := by nlinarith [mul_nonneg hv0 h1]
  by_contra! hlt
  nlinarith [mul_lt_mul_of_pos_left hlt hb0]

private lemma mgf_sq_sub_integral_le [IsProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ)
    {v b : ℝ} (hv0 : 0 ≤ v) (hb : 2 * c ≤ b) (hv : 16 * (c : ℝ) ^ 2 * b ≤ (b - 2 * c) * v)
    {l : ℝ} (hl : b * |l| < 1) :
    mgf (fun ω => X ω ^ 2 - ∫ ω', X ω' ^ 2 ∂μ) μ l ≤ rexp (v * l ^ 2 / 2) := by
  set m := ∫ ω', X ω' ^ 2 ∂μ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun _ => sq_nonneg _
  have hc : (0 : ℝ) ≤ c := c.coe_nonneg
  have hl2 : 2 * l * c < 1 := by
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self l) hc, mul_nonneg hc (abs_nonneg l),
      mul_le_mul_of_nonneg_right hb (abs_nonneg l)]
  have hexp := h.integrable_exp_mul_sq hl2
  have hsq := integrable_pow h 2
  have hmgf : mgf (fun ω => X ω ^ 2 - m) μ l = rexp (-l * m) * ∫ ω, rexp (l * X ω ^ 2) ∂μ := by
    rw [mgf, ← integral_const_mul]
    congr 1 with ω
    rw [← exp_add]
    ring_nf
  have hv16 : 16 * (c : ℝ) ^ 2 ≤ v := by
    simpa using sixteen_mul_sq_le_mul_one_sub hc hv0 hb hv (x := 0) (by simp)
  rw [hmgf]
  rcases le_or_gt 0 l with hl0 | hl0
  · rw [abs_of_nonneg hl0] at hl
    set T := ∫ ω, (rexp (l * X ω ^ 2) - 1 - l * X ω ^ 2) ∂μ with hT
    have hI : ∫ ω, rexp (l * X ω ^ 2) ∂μ = T + 1 + l * m := by
      rw [hT, integral_sub (f := fun ω => rexp (l * X ω ^ 2) - 1)
        (hexp.sub (integrable_const 1)) (hsq.const_mul l),
        integral_sub hexp (integrable_const 1), integral_const_mul]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
      ring
    have hw := sixteen_mul_sq_le_mul_one_sub hc hv0 hb hv hl
    have htail : T ≤ v * l ^ 2 / 2 := by
      refine (integral_exp_mul_sq_sub_le h hl0 hl2).trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left hw (sq_nonneg l)]
    have hT0 : 0 ≤ T := integral_nonneg fun ω => by
      change (0 : ℝ) ≤ _
      linarith [add_one_le_exp (l * X ω ^ 2)]
    have hE : rexp (-l * m) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
    have hE' : rexp (-l * m) * (1 + l * m) ≤ 1 := by
      calc rexp (-l * m) * (1 + l * m) ≤ rexp (-l * m) * rexp (l * m) := by
            gcongr
            linarith [add_one_le_exp (l * m)]
        _ = 1 := by rw [← exp_add]; simp
    have hET : rexp (-l * m) * T ≤ T := mul_le_of_le_one_left hT0 hE
    rw [hI]
    calc rexp (-l * m) * (T + 1 + l * m) = rexp (-l * m) * (1 + l * m) + rexp (-l * m) * T := by
          ring
      _ ≤ 1 + v * l ^ 2 / 2 := by linarith
      _ ≤ rexp (v * l ^ 2 / 2) := by linarith [add_one_le_exp (v * l ^ 2 / 2)]
  · have hX4 := integrable_pow h 4
    have hM4 := integral_pow_two_mul_le h 1
    norm_num [Nat.factorial] at hM4
    have hpt : ∀ ω, rexp (l * X ω ^ 2) ≤ 1 + l * X ω ^ 2 + l ^ 2 / 2 * X ω ^ 4 := by
      intro ω
      have := exp_neg_le_one_sub_add_sq_div_two
        (mul_nonneg (neg_nonneg.mpr hl0.le) (sq_nonneg (X ω)))
      calc rexp (l * X ω ^ 2) = rexp (-(-l * X ω ^ 2)) := by ring_nf
        _ ≤ 1 - -l * X ω ^ 2 + (-l * X ω ^ 2) ^ 2 / 2 := this
        _ = 1 + l * X ω ^ 2 + l ^ 2 / 2 * X ω ^ 4 := by ring
    have hI : ∫ ω, rexp (l * X ω ^ 2) ∂μ ≤ 1 + l * m + l ^ 2 / 2 * ∫ ω, X ω ^ 4 ∂μ := by
      refine (integral_mono hexp (g := fun ω => 1 + l * X ω ^ 2 + l ^ 2 / 2 * X ω ^ 4)
        (((integrable_const 1).add (hsq.const_mul l)).add (hX4.const_mul (l ^ 2 / 2))) hpt).trans_eq
        ?_
      rw [integral_add (f := fun ω => 1 + l * X ω ^ 2)
        ((integrable_const 1).add (hsq.const_mul l)) (hX4.const_mul (l ^ 2 / 2)),
        integral_add (integrable_const 1) (hsq.const_mul l), integral_const_mul,
        integral_const_mul]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
      rfl
    calc rexp (-l * m) * ∫ ω, rexp (l * X ω ^ 2) ∂μ
        ≤ rexp (-l * m) * (1 + l * m + l ^ 2 / 2 * ∫ ω, X ω ^ 4 ∂μ) := by gcongr
      _ ≤ rexp (-l * m) * rexp (l * m + l ^ 2 / 2 * ∫ ω, X ω ^ 4 ∂μ) := by
          gcongr
          linarith [add_one_le_exp (l * m + l ^ 2 / 2 * ∫ ω, X ω ^ 4 ∂μ)]
      _ = rexp (l ^ 2 / 2 * ∫ ω, X ω ^ 4 ∂μ) := by rw [← exp_add]; ring_nf
      _ ≤ rexp (v * l ^ 2 / 2) := by
          gcongr
          nlinarith [sq_nonneg l, mul_le_mul_of_nonneg_left hv16 (sq_nonneg l)]

/-- The centred square of a sub-Gaussian variable is sub-exponential, every window: if $X$
has proxy $c$ under a probability measure, $2c \le b$ and $16 c^2 b \le (b - 2c) v$, then
$X^2 - \mathbb{E}[X^2]$ is sub-exponential with variance proxy $v$ and scale $b$: on the window
$b\lvert\theta\rvert < 1$ the series of $e^{\theta X^2}$ against
$\mathbb{E}[X^{2k}] \le 2\, k!\, (2c)^k$ is at most $8 c^2\theta^2/(1 - 2c\theta)$ for
$\theta \ge 0$, and $e^{-x} \le 1 - x + x^2/2$ with $\mathbb{E}[X^4] \le 16 c^2$ covers
$\theta < 0$. The pairs on the boundary are $v = 16 c^2 b/(b - 2c)$: $(32 c^2, 4 c)$ is Honorio
and Jaakkola's (`ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral`), and
$(18 c^2, 18 c)$ balances the two regimes of Bernstein's inequality (it gives the sub-Gaussian
JL constant `NLAlib.subgaussianJLConstant`, <!-- value subgaussianJLConstant -->$1/36$). No
printed source. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral_of_le
    [IsProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ) {v b : ℝ≥0} (hb : 2 * c ≤ b)
    (hv : 16 * (c : ℝ) ^ 2 * b ≤ ((b : ℝ) - 2 * c) * v) :
    HasSubexponentialMGF (fun ω => X ω ^ 2 - ∫ ω', X ω' ^ 2 ∂μ) v b μ := by
  have hc : (0 : ℝ) ≤ c := c.coe_nonneg
  have hb' : 2 * (c : ℝ) ≤ b := by exact_mod_cast hb
  refine ⟨fun l hl => ?_, fun l hl => mgf_sq_sub_integral_le h v.2 hb' hv hl⟩
  have hl2 : 2 * l * c < 1 := by
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self l) hc, mul_nonneg hc (abs_nonneg l),
      mul_le_mul_of_nonneg_right hb' (abs_nonneg l)]
  refine ((h.integrable_exp_mul_sq hl2).const_mul
    (rexp (-l * ∫ ω', X ω' ^ 2 ∂μ))).congr (ae_of_all _ fun ω => ?_)
  simp only
  rw [← exp_add]
  ring_nf

/-- The centred square of a sub-Gaussian variable is sub-exponential: if $X$ has proxy $c$ under a
probability measure, then $X^2 - \mathbb{E}[X^2]$ has variance proxy $32 c^2$ and scale $4 c$, the
constants of Honorio and Jaakkola (2014): the window $b = 4c$ of
`ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral_of_le`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral
    [IsProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ) :
    HasSubexponentialMGF (fun ω => X ω ^ 2 - ∫ ω', X ω' ^ 2 ∂μ) (32 * c ^ 2) (4 * c) μ := by
  refine h.hasSubexponentialMGF_sq_sub_integral_of_le ?_ ?_
  · exact mul_le_mul_of_nonneg_right (by norm_num) c.2
  · push_cast
    nlinarith [pow_nonneg c.coe_nonneg 3]

/-! ### Sums of squares with Gaussian moments -/

section SumSq

variable {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ} {ε : ℝ}

/-- The arithmetic of the lower tail: for $\varepsilon \ge 0$, at
$\theta = \varepsilon/(2(1 + \varepsilon))$ and $u = -\theta + 3\theta^2/2$,
$$\theta (1 - \varepsilon) + u - u^2/2 + u^3/3 \le -(\varepsilon^2/4 - \varepsilon^3/6) \,;$$
the difference is $\varepsilon^3$ times a rational function with positive coefficients. -/
private theorem lower_exponent_le (hε : 0 ≤ ε) :
    ε / (2 * (1 + ε)) * (1 - ε) + ((-(ε / (2 * (1 + ε))) + 3 * (ε / (2 * (1 + ε))) ^ 2 / 2) -
      (-(ε / (2 * (1 + ε))) + 3 * (ε / (2 * (1 + ε))) ^ 2 / 2) ^ 2 / 2 +
      (-(ε / (2 * (1 + ε))) + 3 * (ε / (2 * (1 + ε))) ^ 2 / 2) ^ 3 / 3) ≤
      -(ε ^ 2 / 4 - ε ^ 3 / 6) := by
  have hε1 : 0 < 1 + ε := by linarith
  have e : -(ε ^ 2 / 4 - ε ^ 3 / 6) - (ε / (2 * (1 + ε)) * (1 - ε) +
      ((-(ε / (2 * (1 + ε))) + 3 * (ε / (2 * (1 + ε))) ^ 2 / 2) -
      (-(ε / (2 * (1 + ε))) + 3 * (ε / (2 * (1 + ε))) ^ 2 / 2) ^ 2 / 2 +
      (-(ε / (2 * (1 + ε))) + 3 * (ε / (2 * (1 + ε))) ^ 2 / 2) ^ 3 / 3)) =
      ε ^ 3 * (256 * ε ^ 6 + 1152 * ε ^ 5 + 2304 * ε ^ 4 + 2637 * ε ^ 3 + 1668 * ε ^ 2 +
        444 * ε + 32) / (1536 * (1 + ε) ^ 6) := by
    field_simp
    ring
  have : 0 ≤ ε ^ 3 * (256 * ε ^ 6 + 1152 * ε ^ 5 + 2304 * ε ^ 4 + 2637 * ε ^ 3 +
      1668 * ε ^ 2 + 444 * ε + 32) / (1536 * (1 + ε) ^ 6) := by positivity
  linarith

/-- The moment generating function of $\sum_i Y_i^2$ is the product of those of the $Y_i^2$, for
independent sub-Gaussian $Y_i$. -/
private theorem mgf_sum_sq (hind : iIndepFun Y μ) (hsub : ∀ i, HasSubgaussianMGF (Y i) 1 μ)
    (t : ℝ) : mgf (fun ω => ∑ i, Y i ω ^ 2) μ t = ∏ i, mgf (fun ω => Y i ω ^ 2) μ t := by
  have hW : iIndepFun (fun i ω => Y i ω ^ 2) μ :=
    hind.comp (fun _ y => y ^ 2) fun _ => by fun_prop
  rw [← hW.mgf_sum₀ (fun i => (hsub i).aemeasurable.pow_const 2) Finset.univ]
  congr 1
  ext ω
  rw [Finset.sum_apply]

/-- $e^{\theta \sum_i Y_i^2}$ is integrable for independent $Y_i$, each sub-Gaussian with proxy
$1$, when $2\theta < 1$ (where each $e^{\theta Y_i^2}$ is). -/
private theorem integrable_exp_mul_sum_sq (hind : iIndepFun Y μ)
    (hsub : ∀ i, HasSubgaussianMGF (Y i) 1 μ) {θ : ℝ} (hθ : 2 * θ < 1) :
    Integrable (fun ω => Real.exp (θ * ∑ i, Y i ω ^ 2)) μ := by
  have := hind.isProbabilityMeasure
  refine Integrable.of_integral_ne_zero ?_
  have h := mgf_sum_sq hind hsub θ
  rw [mgf] at h
  rw [h]
  refine (Finset.prod_pos fun i _ => mgf_pos ?_).ne'
  exact (hsub i).integrable_exp_mul_sq (by rw [NNReal.coe_one, mul_one]; exact hθ)

/-- **Upper Chernoff tail**: for $\varepsilon \ge 0$,
$\mathbb{P}\bigl[(1 + \varepsilon) k \le \sum_i Y_i^2\bigr]
\le e^{-k(\varepsilon^2/4 - \varepsilon^3/6)}$, $k = \lvert \iota \rvert$, at
$\theta = \varepsilon/(2(1 + \varepsilon))$ with
$\mathbb{E}[e^{\theta Y_i^2}] \le (1 - 2\theta)^{-1/2}$. -/
private theorem measureReal_mul_card_le_sum_sq_le (hind : iIndepFun Y μ)
    (hsub : ∀ i, HasSubgaussianMGF (Y i) 1 μ) (hε : 0 ≤ ε) :
    μ.real {ω | (1 + ε) * Fintype.card ι ≤ ∑ i, Y i ω ^ 2} ≤
      Real.exp (-(Fintype.card ι * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
  have := hind.isProbabilityMeasure
  set N : ℝ := (Fintype.card ι : ℝ) with hN_def
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hε1 : 0 < 1 + ε := by linarith
  set θ : ℝ := ε / (2 * (1 + ε)) with hθ_def
  have hθ0 : 0 ≤ θ := by positivity
  have hθ2 : 1 - 2 * θ = 1 / (1 + ε) := by rw [hθ_def]; field_simp; ring
  have hθ1 : 2 * θ < 1 := by
    have : 0 < 1 / (1 + ε) := by positivity
    linarith
  have hθε : θ * (1 + ε) = ε / 2 := by rw [hθ_def]; field_simp
  have hmgf : ∀ i, mgf (fun ω => Y i ω ^ 2) μ θ ≤ √(1 + ε) := by
    intro i
    have h := (hsub i).integral_exp_mul_sq_le hθ0 (by rw [NNReal.coe_one, mul_one]; exact hθ1)
    rw [NNReal.coe_one, mul_one, hθ2, one_div, one_div, Real.sqrt_inv, inv_inv] at h
    exact h
  have hsqrt : √(1 + ε) = Real.exp (Real.log (1 + ε) / 2) := by
    rw [← Real.log_sqrt hε1.le, Real.exp_log (Real.sqrt_pos.2 hε1)]
  refine (measure_ge_le_exp_mul_mgf (X := fun ω => ∑ i, Y i ω ^ 2) ((1 + ε) * N) hθ0
    (integrable_exp_mul_sum_sq hind hsub hθ1)).trans ?_
  rw [mgf_sum_sq hind hsub]
  calc Real.exp (-θ * ((1 + ε) * N)) * ∏ i, mgf (fun ω => Y i ω ^ 2) μ θ
    _ ≤ Real.exp (-θ * ((1 + ε) * N)) * ∏ _i : ι, √(1 + ε) := by
      gcongr with i
      · exact fun i _ => mgf_nonneg
      · exact hmgf i
    _ = Real.exp (-θ * ((1 + ε) * N) + N * (Real.log (1 + ε) / 2)) := by
      rw [Finset.prod_const, Finset.card_univ, hsqrt, ← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := by
      rw [Real.exp_le_exp]
      have hL := mul_le_mul_of_nonneg_left (Real.log_one_add_le_cubic (u := ε) (by linarith)) hN0
      have e : -θ * ((1 + ε) * N) = -(ε / 2) * N := by rw [← hθε]; ring
      rw [e]
      nlinarith

/-- **Lower Chernoff tail**: for $\varepsilon \ge 0$,
$\mathbb{P}\bigl[\sum_i Y_i^2 \le (1 - \varepsilon) k\bigr]
\le e^{-k(\varepsilon^2/4 - \varepsilon^3/6)}$, $k = \lvert \iota \rvert$, at
$\theta = \varepsilon/(2(1 + \varepsilon))$ with
$\mathbb{E}[e^{-\theta Y_i^2}] \le 1 - \theta + 3\theta^2/2$ (the fourth moment) and
`Real.log_one_add_le_cubic_of_nonpos`. -/
private theorem measureReal_sum_sq_le_mul_card_le (hind : iIndepFun Y μ)
    (hsub : ∀ i, HasSubgaussianMGF (Y i) 1 μ) (h2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = 1)
    (h4 : ∀ i, ∫ ω, Y i ω ^ 4 ∂μ ≤ 3) (hε : 0 ≤ ε) :
    μ.real {ω | ∑ i, Y i ω ^ 2 ≤ (1 - ε) * Fintype.card ι} ≤
      Real.exp (-(Fintype.card ι * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
  have := hind.isProbabilityMeasure
  set N : ℝ := (Fintype.card ι : ℝ) with hN_def
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hε1 : 0 < 1 + ε := by linarith
  set θ : ℝ := ε / (2 * (1 + ε)) with hθ_def
  have hθ0 : 0 ≤ θ := by positivity
  have hθ2 : 1 - 2 * θ = 1 / (1 + ε) := by rw [hθ_def]; field_simp; ring
  have hθ1 : 2 * θ < 1 := by
    have : 0 < 1 / (1 + ε) := by positivity
    linarith
  set u : ℝ := -θ + 3 * θ ^ 2 / 2 with hu_def
  have hu1 : -1 < u := by nlinarith
  have hu0 : u ≤ 0 := by nlinarith
  have hq : 0 < 1 + u := by linarith
  have hmgf : ∀ i, mgf (fun ω => Y i ω ^ 2) μ (-θ) ≤ 1 + u := by
    intro i
    have hpow := integrable_pow (hsub i)
    have hexp : Integrable (fun ω => Real.exp (-θ * Y i ω ^ 2)) μ :=
      (hsub i).integrable_exp_mul_sq (by rw [NNReal.coe_one, mul_one]; linarith)
    have hpoly : Integrable (fun ω => 1 - θ * Y i ω ^ 2 + θ ^ 2 / 2 * Y i ω ^ 4) μ :=
      ((integrable_const 1).sub ((hpow 2).const_mul θ)).add ((hpow 4).const_mul _)
    calc mgf (fun ω => Y i ω ^ 2) μ (-θ)
      _ = ∫ ω, Real.exp (-θ * Y i ω ^ 2) ∂μ := rfl
      _ ≤ ∫ ω, (1 - θ * Y i ω ^ 2 + θ ^ 2 / 2 * Y i ω ^ 4) ∂μ := by
        refine integral_mono hexp hpoly fun ω => ?_
        have := exp_neg_le_one_sub_add_sq_div_two (t := θ * Y i ω ^ 2) (by positivity)
        rw [neg_mul]
        calc _ ≤ _ := this
          _ = _ := by ring
      _ = 1 - θ + θ ^ 2 / 2 * ∫ ω, Y i ω ^ 4 ∂μ := by
        rw [integral_add (f := fun ω => 1 - θ * Y i ω ^ 2) (g := fun ω => θ ^ 2 / 2 * Y i ω ^ 4)
            ((integrable_const 1).sub ((hpow 2).const_mul θ)) ((hpow 4).const_mul _),
          integral_sub (f := fun _ => (1 : ℝ)) (g := fun ω => θ * Y i ω ^ 2) (integrable_const 1)
            ((hpow 2).const_mul θ), integral_const_mul,
          integral_const_mul, h2 i, integral_const, probReal_univ, smul_eq_mul, mul_one,
          mul_one]
      _ ≤ 1 + u := by
        rw [hu_def]
        nlinarith [h4 i, sq_nonneg θ]
  refine (measure_le_le_exp_mul_mgf (X := fun ω => ∑ i, Y i ω ^ 2) ((1 - ε) * N)
    (neg_nonpos.2 hθ0) (integrable_exp_mul_sum_sq hind hsub (by linarith))).trans ?_
  rw [mgf_sum_sq hind hsub]
  calc Real.exp (-(-θ) * ((1 - ε) * N)) * ∏ i, mgf (fun ω => Y i ω ^ 2) μ (-θ)
    _ ≤ Real.exp (-(-θ) * ((1 - ε) * N)) * ∏ _i : ι, (1 + u) := by
      gcongr with i
      · exact fun i _ => mgf_nonneg
      · exact hmgf i
    _ = Real.exp (N * (θ * (1 - ε) + Real.log (1 + u))) := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_log hq, ← Real.exp_nat_mul,
        ← Real.exp_add, ← hN_def, Real.log_exp]
      ring_nf
    _ ≤ _ := by
      rw [Real.exp_le_exp]
      have hlog := Real.log_one_add_le_cubic_of_nonpos hu1 hu0
      have hK := lower_exponent_le hε
      rw [← hθ_def, ← hu_def] at hK
      have : θ * (1 - ε) + Real.log (1 + u) ≤ -(ε ^ 2 / 4 - ε ^ 3 / 6) := by linarith
      nlinarith

/-- Dasgupta–Gupta tail for sums of squares: for independent real $Y_i$, $i \in \iota$, each
sub-Gaussian with proxy $1$, with $\mathbb{E}[Y_i^2] = 1$ and $\mathbb{E}[Y_i^4] \le 3$, and
$\varepsilon \ge 0$,
$$\mathbb{P}\Bigl[\varepsilon \le \Bigl\lvert \frac{1}{k} \sum_i Y_i^2 - 1 \Bigr\rvert\Bigr]
\le 2 e^{-k(\varepsilon^2/4 - \varepsilon^3/6)} \,, \qquad k = \lvert \iota \rvert \,.$$
The exponent of Dasgupta and Gupta (2003) for $\chi^2_k$, cited by name only
(`docs/PORT_SKETCHING.md` §7.2); here for any variables with the Gaussian's proxy and its second
and fourth moments. The lower half covers $\varepsilon = 1$, where $\sum_i Y_i^2 = 0$ may have
positive probability (up to $2^{-k}$ for Rademacher combinations). The bound is at least $2$ for
$\varepsilon \ge 3/2$ and for empty $\iota$. -/
theorem measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun (hind : iIndepFun Y μ)
    (hsub : ∀ i, HasSubgaussianMGF (Y i) 1 μ) (h2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ = 1)
    (h4 : ∀ i, ∫ ω, Y i ω ^ 4 ∂μ ≤ 3) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |(∑ i, Y i ω ^ 2) / Fintype.card ι - 1|} ≤
      2 * Real.exp (-(Fintype.card ι * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
  have := hind.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hN | hN
  · rw [hN, Nat.cast_zero, zero_mul, neg_zero, Real.exp_zero]
    exact measureReal_le_one.trans (by norm_num)
  have hN' : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 hN
  have hsubset : {ω | ε ≤ |(∑ i, Y i ω ^ 2) / Fintype.card ι - 1|} ⊆
      {ω | (1 + ε) * Fintype.card ι ≤ ∑ i, Y i ω ^ 2} ∪
        {ω | ∑ i, Y i ω ^ 2 ≤ (1 - ε) * Fintype.card ι} := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
    rcases le_abs'.1 hω with h | h
    · right
      rw [← div_le_iff₀ hN']
      linarith
    · left
      rw [← le_div_iff₀ hN']
      linarith
  calc _ ≤ _ := measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add (measureReal_mul_card_le_sum_sq_le hind hsub hε)
      (measureReal_sum_sq_le_mul_card_le hind hsub h2 h4 hε)
    _ = _ := by ring

end SumSq

end NLAlib
