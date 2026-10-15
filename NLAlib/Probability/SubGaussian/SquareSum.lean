/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Deriv
public import NLAlib.Probability.SubGaussian.Square

/-!
# Sums of squares of sub-Gaussian variables with Gaussian moments

For $k$ independent real $Y_i$, each sub-Gaussian with proxy $1$, with $\mathbb{E}[Y_i^2] = 1$ and
$\mathbb{E}[Y_i^4] \le 3$ (the moments of a standard Gaussian), the relative deviation of
$k^{-1} \sum_i Y_i^2$ from $1$ has the tail $2 e^{-k(\varepsilon^2/4 - \varepsilon^3/6)}$ of
$\chi^2_k$, Dasgupta and Gupta's exponent. The upper half is Chernoff's bound with
$\mathbb{E}[e^{\theta Y^2}] \le (1 - 2\theta)^{-1/2}$ (`HasSubgaussianMGF.integral_exp_mul_sq_le`)
and the arithmetic of the $\chi^2$ tail; the lower half is Chernoff's bound with
$\mathbb{E}[e^{-\theta Y^2}] \le 1 - \theta + 3\theta^2/2$ at
$\theta = \varepsilon/(2(1 + \varepsilon))$, through `Real.log_one_add_le_cubic_of_nonpos`. A
standard Gaussian and a Rademacher combination $\langle \boldsymbol{\xi}, \mathbf{x} \rangle$ with
$\|\mathbf{x}\| = 1$
($\mathbb{E} \langle \boldsymbol{\xi}, \mathbf{x} \rangle^4 = 3 - 2 \sum_j \mathbf{x}_j^4$)
satisfy the hypotheses; the latter gives the sign-sketch Johnson–Lindenstrauss tail with Gaussian
constants (Achlioptas).

This file is Sketching stage S3's (`docs/design/Sketching-S3.md` §8, item 2). At the round's
wrap-up it merges into `NLAlib/Probability/SubGaussian/Square.lean`, and the $\chi^2$ relative
deviation `NLAlib.measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector`, which
it dominates (same bound, weaker hypotheses), can be reproved from it and keep its name
(CONTRIBUTING §5.2, rule 6).

## Main results

* `NLAlib.measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ι : Type*} [Fintype ι]
  {Y : ι → Ω → ℝ} {ε : ℝ}

/-- $\log(1 + \varepsilon) \le \varepsilon - \varepsilon^2/2 + \varepsilon^3/3$ for
$\varepsilon \ge 0$: the difference has derivative $\varepsilon^3/(1 + \varepsilon) \ge 0$ and
vanishes at $0$. A copy of the private lemma of
`NLAlib/Probability/Distributions/ChiSquareTails.lean`, until the wrap-up. -/
private theorem log_one_add_le_cubic {ε : ℝ} (hε : 0 ≤ ε) :
    Real.log (1 + ε) ≤ ε - ε ^ 2 / 2 + ε ^ 3 / 3 := by
  let f : ℝ → ℝ := fun t => t - t ^ 2 / 2 + t ^ 3 / 3 - Real.log (1 + t)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt f (1 - t + t ^ 2 - 1 / (1 + t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := (hasDerivAt_id t).const_add 1
    have hlog := h1.log (by linarith)
    have hp : HasDerivAt (fun t : ℝ => t - t ^ 2 / 2 + t ^ 3 / 3) (1 - t + t ^ 2) t := by
      have := (((hasDerivAt_id' t).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 3 t).div_const 3))
      exact this.congr_deriv (by norm_num)
    exact hp.sub hlog
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hderiv t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 < t := ht
      rw [(hderiv t ht0.le).deriv]
      have : 1 - t + t ^ 2 - 1 / (1 + t) = t ^ 3 / (1 + t) := by field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hε) hε
  simp only [f, add_zero, Real.log_one] at this
  norm_num at this
  linarith

/-- $e^{-t} \le 1 - t + t^2/2$ for $t \ge 0$: the difference has derivative
$t - 1 + e^{-t} \ge 0$ and vanishes at $0$. -/
private theorem exp_neg_le_one_sub_add_sq_div_two {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  let g : ℝ → ℝ := fun s => 1 - s + s ^ 2 / 2 - Real.exp (-s)
  have hg : ∀ s, HasDerivAt g (-1 + s + Real.exp (-s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => 1 - s + s ^ 2 / 2) (-1 + s) s := by
      have := ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id' s)).add
        ((hasDerivAt_pow 2 s).div_const 2)
      exact this.congr_deriv (by norm_num)
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-s)) s :=
      (hasDerivAt_neg s).exp.congr_deriv (by ring)
    exact (h1.sub h2).congr_deriv (by ring)
  have hmono := monotone_of_hasDerivAt_nonneg hg fun s => by
    have := Real.add_one_le_exp (-s)
    simp only [Pi.zero_apply]
    linarith
  have := hmono ht
  simp only [g, neg_zero, Real.exp_zero] at this
  linarith

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
$\mathbb{P}\bigl((1 + \varepsilon) k \le \sum_i Y_i^2\bigr)
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
      have hL := mul_le_mul_of_nonneg_left (log_one_add_le_cubic hε) hN0
      have e : -θ * ((1 + ε) * N) = -(ε / 2) * N := by rw [← hθε]; ring
      rw [e]
      nlinarith

/-- **Lower Chernoff tail**: for $\varepsilon \ge 0$,
$\mathbb{P}\bigl(\sum_i Y_i^2 \le (1 - \varepsilon) k\bigr)
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
    have hpow : ∀ n : ℕ, Integrable (fun ω => Y i ω ^ n) μ := fun n =>
      integrable_pow_of_integrable_exp_mul one_ne_zero ((hsub i).integrable_exp_mul 1)
        ((hsub i).integrable_exp_mul (-1)) n
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

/-- **Dasgupta–Gupta tail for sums of squares**: for independent real $Y_i$, $i \in \iota$, each
sub-Gaussian with proxy $1$, with $\mathbb{E}[Y_i^2] = 1$ and $\mathbb{E}[Y_i^4] \le 3$, and
$\varepsilon \ge 0$,
$$\mathbb{P}\Bigl(\varepsilon \le \Bigl\lvert \frac{1}{k} \sum_i Y_i^2 - 1 \Bigr\rvert\Bigr)
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

end NLAlib
