/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.MatrixConcentration.Chernoff

/-!
# The matrix Chernoff inequalities for sums of independent matrices

For independent random positive semidefinite matrices
$\mathbf{0} \preceq \mathbf{X}_k \preceq L\mathbf{I}$ of size $d = \lvert n\rvert$, with
$\mu_{\max}$ and $\mu_{\min}$ the largest and smallest eigenvalues of
$\sum_k \mathbb{E}\mathbf{X}_k$, the largest eigenvalue of the sum exceeds
$(1 + \delta) \mu_{\max}$, and the smallest falls below $(1 - \delta) \mu_{\min}$, with the
Chernoff probabilities (Tropp 2015, Theorem 5.1.1), and the means satisfy
$\mathbb{E} \lambda_{\max} \le (e - 1) \mu_{\max} + L \log d$ and
$\mathbb{E} \lambda_{\min} \ge (1 - e^{-1}) \mu_{\min} - L \log d$. When the summands have mean
sum the identity, the sum is within $\varepsilon$ of the identity in spectral norm outside
probability $2 d\, e^{-\varepsilon^2 / (3L)}$, the form row-sampling arguments use.

## Main results

* `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_chernoff`,
  `NLAlib.measureReal_eigenvalue_sum_le_le_chernoff`: the source forms.
* `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp`,
  `NLAlib.measureReal_eigenvalue_sum_le_le_card_mul_exp`: the simplified forms.
* `NLAlib.integral_eigenvalue_zero_sum_le_chernoff`, `NLAlib.le_integral_eigenvalue_sum_chernoff`.
* `NLAlib.measureReal_specNorm_sum_sub_one_ge_le`: the two-sided form around the identity.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι] {X : ι → Ω → Matrix n n 𝕜}
  {L : ℝ}

/-- The hypotheses of the trace-form Chernoff tails for $\mathbf{Y} = \sum_k \mathbf{X}_k$ and
$\mathbf{V} = \sum_k \mathbb{E}\mathbf{X}_k$. -/
private theorem chernoff_sum_hyps (hind : iIndepFun X μ) (hXm : ∀ k, AEMeasurable (X k) μ)
    (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) :
    (∀ᵐ ω ∂μ, (∑ k, X k ω).IsHermitian) ∧ (∑ k, ∫ ω, X k ω ∂μ).PosSemidef ∧
      (∀ θ : ℝ, Integrable (fun ω => RCLike.re (exp (θ • ∑ k, X k ω)).trace) μ) ∧
      ∀ θ : ℝ, ∫ ω, RCLike.re (exp (θ • ∑ k, X k ω)).trace ∂μ ≤
        RCLike.re (exp (((Real.exp (θ * L) - 1) / L) • ∑ k, ∫ ω, X k ω ∂μ)).trace := by
  have := hind.isProbabilityMeasure
  have h := fun k => hasMatrixMGFBound_of_posSemidef_of_le (hXm k) hL (hpsd k) (hle k)
  refine ⟨?_, Matrix.posSemidef_sum _ fun k _ => Matrix.posSemidef_integral (hpsd k),
    fun θ => HasMatrixMGFBound.integrable_re_trace_exp_sum hind h (Set.mem_univ θ),
    fun θ => HasMatrixMGFBound.integral_re_trace_exp_sum_le hind h (Set.mem_univ θ)⟩
  filter_upwards [ae_all_iff.2 fun k => hpsd k] with ω hω
  exact isSelfAdjoint_sum _ fun k _ => (hω k).isHermitian

/-- **Matrix Chernoff, upper tail**: for finitely many independent, almost everywhere measurable
random $n \times n$ matrices $\mathbf{X}_k$ over $\Bbbk$, $n$ nonempty, with
$\mathbf{0} \preceq \mathbf{X}_k \preceq L\mathbf{I}$ almost surely, $L > 0$,
$\mu_{\max} = \lambda_0(\sum_k \mathbb{E}\mathbf{X}_k)$ and $\delta \ge 0$,
$$\mathbb{P}\Bigl[\lambda_0\Bigl(\sum_k \mathbf{X}_k\Bigr) \ge (1 + \delta) \mu_{\max}\Bigr]
\le \lvert n\rvert \Bigl(\frac{e^\delta}{(1 + \delta)^{1+\delta}}\Bigr)^{\mu_{\max} / L}\,.$$
[Tropp2015, Theorem 5.1.1]. -/
theorem measureReal_eigenvalue_zero_sum_ge_le_chernoff [Nonempty n] (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {δ : ℝ} (hδ : 0 ≤ δ) :
    μ.real {ω | (1 + δ) * eigenvalue (∑ k, ∫ ω', X k ω' ∂μ) 0 ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Fintype.card n * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^
        (eigenvalue (∑ k, ∫ ω, X k ω ∂μ) 0 / L) := by
  obtain ⟨hY, hV, hint, htr⟩ := chernoff_sum_hyps hind hXm hL hpsd hle
  have := hind.isProbabilityMeasure
  exact measureReal_eigenvalue_zero_ge_le_chernoff_of_integral_le hY hV hL (fun θ _ => hint θ)
    (fun θ _ => htr θ) hδ

/-- **Matrix Chernoff, lower tail**: for finitely many independent, almost everywhere
measurable random $n \times n$ matrices $\mathbf{X}_k$ over $\Bbbk$ with
$\mathbf{0} \preceq \mathbf{X}_k \preceq L\mathbf{I}$ almost surely, $L > 0$,
$\mu_{\min} = \lambda_j(\sum_k \mathbb{E}\mathbf{X}_k)$ the smallest eigenvalue
($j + 1 = \lvert n\rvert$) and $0 \le \delta < 1$,
$$\mathbb{P}\Bigl[\lambda_j\Bigl(\sum_k \mathbf{X}_k\Bigr) \le (1 - \delta) \mu_{\min}\Bigr]
\le \lvert n\rvert \Bigl(\frac{e^{-\delta}}{(1 - \delta)^{1-\delta}}\Bigr)^{\mu_{\min} / L}\,.$$
[Tropp2015, Theorem 5.1.1]. -/
theorem measureReal_eigenvalue_sum_le_le_chernoff (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {j : ℕ} (hj : j + 1 = Fintype.card n)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    μ.real {ω | eigenvalue (∑ k, X k ω) j ≤ (1 - δ) * eigenvalue (∑ k, ∫ ω', X k ω' ∂μ) j} ≤
      Fintype.card n * (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^
        (eigenvalue (∑ k, ∫ ω, X k ω ∂μ) j / L) := by
  obtain ⟨hY, hV, hint, htr⟩ := chernoff_sum_hyps hind hXm hL hpsd hle
  have := hind.isProbabilityMeasure
  exact measureReal_eigenvalue_le_le_chernoff_of_integral_le hY hV hL hj (fun θ _ => hint θ)
    (fun θ _ => htr θ) hδ0 hδ1

/-- Matrix Chernoff, upper tail, simplified: for finitely many independent, almost everywhere
measurable random $n \times n$ matrices $\mathbf{X}_k$ over $\Bbbk$, $n$ nonempty, with
$\mathbf{0} \preceq \mathbf{X}_k \preceq L\mathbf{I}$ almost surely, $L > 0$, and
$0 \le \delta \le 1$,
$\mathbb{P}[\lambda_0(\sum_k \mathbf{X}_k) \ge (1 + \delta) \mu_{\max}]
\le \lvert n\rvert\, e^{-\delta^2 \mu_{\max} / (3L)}$, with
$\mu_{\max} = \lambda_0(\sum_k \mathbb{E}\mathbf{X}_k)$. -/
theorem measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp [Nonempty n] (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | (1 + δ) * eigenvalue (∑ k, ∫ ω', X k ω' ∂μ) 0 ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Fintype.card n * Real.exp (-δ ^ 2 * eigenvalue (∑ k, ∫ ω, X k ω ∂μ) 0 / (3 * L)) := by
  obtain ⟨hY, hV, hint, htr⟩ := chernoff_sum_hyps hind hXm hL hpsd hle
  have := hind.isProbabilityMeasure
  exact measureReal_eigenvalue_zero_ge_le_card_mul_exp_of_integral_le hY hV hL
    (fun θ _ => hint θ) (fun θ _ => htr θ) hδ0 hδ1

/-- Matrix Chernoff, lower tail, simplified: for finitely many independent, almost everywhere
measurable random $n \times n$ matrices $\mathbf{X}_k$ over $\Bbbk$ with
$\mathbf{0} \preceq \mathbf{X}_k \preceq L\mathbf{I}$ almost surely, $L > 0$,
$0 \le \delta < 1$ and $j + 1 = \lvert n\rvert$,
$\mathbb{P}[\lambda_j(\sum_k \mathbf{X}_k) \le (1 - \delta) \mu_{\min}]
\le \lvert n\rvert\, e^{-\delta^2 \mu_{\min} / (2L)}$, with
$\mu_{\min} = \lambda_j(\sum_k \mathbb{E}\mathbf{X}_k)$. -/
theorem measureReal_eigenvalue_sum_le_le_card_mul_exp (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {j : ℕ} (hj : j + 1 = Fintype.card n)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    μ.real {ω | eigenvalue (∑ k, X k ω) j ≤ (1 - δ) * eigenvalue (∑ k, ∫ ω', X k ω' ∂μ) j} ≤
      Fintype.card n * Real.exp (-δ ^ 2 * eigenvalue (∑ k, ∫ ω, X k ω ∂μ) j / (2 * L)) := by
  obtain ⟨hY, hV, hint, htr⟩ := chernoff_sum_hyps hind hXm hL hpsd hle
  have := hind.isProbabilityMeasure
  exact measureReal_eigenvalue_le_le_card_mul_exp_of_integral_le hY hV hL hj
    (fun θ _ => hint θ) (fun θ _ => htr θ) hδ0 hδ1

/-- Matrix Chernoff for the mean of the largest eigenvalue: for finitely many independent,
almost everywhere measurable random $n \times n$ matrices $\mathbf{X}_k$ over $\Bbbk$, $n$
nonempty, with $\mathbf{0} \preceq \mathbf{X}_k \preceq L\mathbf{I}$ almost surely and $L > 0$,
$$\mathbb{E}\, \lambda_0\Bigl(\sum_k \mathbf{X}_k\Bigr)
\le (e - 1) \mu_{\max} + L \log \lvert n\rvert$$
with $\mu_{\max} = \lambda_0(\sum_k \mathbb{E}\mathbf{X}_k)$.
[Tropp2015, Theorem 5.1.1]. -/
theorem integral_eigenvalue_zero_sum_le_chernoff [Nonempty n] (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) :
    ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ ≤
      (Real.exp 1 - 1) * eigenvalue (∑ k, ∫ ω, X k ω ∂μ) 0 + L * Real.log (Fintype.card n) := by
  have := hind.isProbabilityMeasure
  obtain ⟨-, hV, -, -⟩ := chernoff_sum_hyps hind hXm hL hpsd hle
  have h := fun k => hasMatrixMGFBound_of_posSemidef_of_le (hXm k) hL (hpsd k) (hle k)
  have hXi := fun k => integrable_of_posSemidef_of_le (hXm k) (hpsd k) (hle k)
  have hmean := HasMatrixMGFBound.integral_eigenvalue_zero_sum_le hind h hXi
    (Set.mem_univ L⁻¹) (inv_pos.mpr hL)
  have hθL : L⁻¹ * L = 1 := inv_mul_cancel₀ hL.ne'
  simp only [hθL, inv_inv] at hmean
  set c := (Real.exp 1 - 1) / L with hcdef
  have hc : 0 ≤ c := div_nonneg (by linarith [Real.add_one_le_exp 1]) hL.le
  have hcV : (c • ∑ k, ∫ ω, X k ω ∂μ).IsHermitian := (IsSelfAdjoint.all c).smul hV.isHermitian
  have htrd := hcV.re_trace_exp_le_card_mul_exp
  rw [eigenvalue_real_smul _ hc] at htrd
  have hd : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have hlog := Real.log_le_log hcV.re_trace_exp_pos htrd
  rw [Real.log_mul hd.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  refine hmean.trans ?_
  calc L * Real.log (RCLike.re (exp (c • ∑ k, ∫ ω, X k ω ∂μ)).trace)
      ≤ L * (Real.log (Fintype.card n) + c * eigenvalue (∑ k, ∫ ω, X k ω ∂μ) 0) :=
        mul_le_mul_of_nonneg_left hlog hL.le
    _ = (Real.exp 1 - 1) * eigenvalue (∑ k, ∫ ω, X k ω ∂μ) 0 + L * Real.log (Fintype.card n) := by
        rw [hcdef]
        field_simp
        ring

/-- Matrix Chernoff for the mean of the smallest eigenvalue: for finitely many independent,
almost everywhere measurable random $n \times n$ matrices $\mathbf{X}_k$ over $\Bbbk$ with
$\mathbf{0} \preceq \mathbf{X}_k \preceq L\mathbf{I}$ almost surely, $L > 0$ and
$j + 1 = \lvert n\rvert$,
$$\mathbb{E}\, \lambda_j\Bigl(\sum_k \mathbf{X}_k\Bigr)
\ge (1 - e^{-1}) \mu_{\min} - L \log \lvert n\rvert$$
with $\mu_{\min} = \lambda_j(\sum_k \mathbb{E}\mathbf{X}_k)$.
[Tropp2015, Theorem 5.1.1]. The summands are bounded, so the sum is integrable and the integral
is not a junk value. -/
theorem le_integral_eigenvalue_sum_chernoff (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {j : ℕ} (hj : j + 1 = Fintype.card n) :
    (1 - Real.exp (-1)) * eigenvalue (∑ k, ∫ ω, X k ω ∂μ) j - L * Real.log (Fintype.card n) ≤
      ∫ ω, eigenvalue (∑ k, X k ω) j ∂μ := by
  have := hind.isProbabilityMeasure
  obtain ⟨hY, hV, hint, htr⟩ := chernoff_sum_hyps hind hXm hL hpsd hle
  have hXi := fun k => integrable_of_posSemidef_of_le (hXm k) (hpsd k) (hle k)
  have hθ : -L⁻¹ < 0 := neg_neg_of_pos (inv_pos.mpr hL)
  have hlow := le_integral_eigenvalue hY (integrable_finsetSum _ fun k _ => hXi k) hj hθ
    (hint (-L⁻¹))
  have hθL : -L⁻¹ * L = -1 := by rw [neg_mul, inv_mul_cancel₀ hL.ne']
  have htr' := htr (-L⁻¹)
  rw [hθL] at htr'
  rw [inv_neg, inv_inv] at hlow
  set V := ∑ k, ∫ ω, X k ω ∂μ with hVdef
  set c := (Real.exp (-1) - 1) / L with hcdef
  have hc : c ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by linarith [Real.exp_le_one_iff.mpr (show (-1 : ℝ) ≤ 0 by norm_num)]) hL.le
  have hcV : (c • V).IsHermitian := (IsSelfAdjoint.all c).smul hV.isHermitian
  have htrd := hcV.re_trace_exp_le_card_mul_exp
  have heig : eigenvalue (c • V) 0 = c * eigenvalue V j := by
    rw [show c • V = -((-c) • V) by rw [neg_smul, neg_neg],
      eigenvalue_neg _ (show 0 + j + 1 = Fintype.card n by omega),
      eigenvalue_real_smul _ (neg_nonneg.mpr hc), neg_mul, neg_neg]
  rw [heig] at htrd
  have hd : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr (by omega)
  have hpos : 0 < ∫ ω, RCLike.re (exp (-L⁻¹ • ∑ k, X k ω)).trace ∂μ := by
    have : Nonempty n := Fintype.card_pos_iff.mp (by omega)
    exact integral_pos_of_ae_pos (hint _) (hY.mono fun ω hω =>
      (show (-L⁻¹ • ∑ k, X k ω).IsHermitian from (IsSelfAdjoint.all _).smul hω).re_trace_exp_pos)
  have hlog := Real.log_le_log hpos (htr'.trans htrd)
  rw [Real.log_mul hd.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  refine le_trans ?_ hlow
  calc (1 - Real.exp (-1)) * eigenvalue V j - L * Real.log (Fintype.card n)
      = -L * (Real.log (Fintype.card n) + c * eigenvalue V j) := by
        rw [hcdef]
        field_simp
        ring
    _ ≤ -L * Real.log (∫ ω, RCLike.re (exp (-L⁻¹ • ∑ k, X k ω)).trace ∂μ) :=
        mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hL.le)

/-- Spectral approximation of the identity by a sum of bounded positive semidefinite
matrices: for finitely many independent, almost everywhere measurable random $n \times n$
matrices $\mathbf{X}_k$ over $\Bbbk$, $n$ nonempty, with
$\mathbf{0} \preceq \mathbf{X}_k \preceq L\mathbf{I}$ almost surely, $L > 0$ and
$\sum_k \mathbb{E}\mathbf{X}_k = \mathbf{I}$, for $0 \le \varepsilon < 1$
$$\mathbb{P}\Bigl[\Bigl\|\sum_k \mathbf{X}_k - \mathbf{I}\Bigr\|_2 \ge \varepsilon\Bigr]
\le 2 \lvert n\rvert\, e^{-\varepsilon^2 / (3L)}\,,$$
the form row-sampling and subspace-embedding arguments use. -/
theorem measureReal_specNorm_sum_sub_one_ge_le [Nonempty n] (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜))
    (hmean : ∑ k, ∫ ω, X k ω ∂μ = 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    μ.real {ω | ε ≤ specNorm (∑ k, X k ω - 1)} ≤
      2 * Fintype.card n * Real.exp (-ε ^ 2 / (3 * L)) := by
  have := hind.isProbabilityMeasure
  obtain ⟨hY, -, -, -⟩ := chernoff_sum_hyps hind hXm hL hpsd hle
  obtain ⟨j, hj⟩ : ∃ j, j + 1 = Fintype.card n :=
    ⟨Fintype.card n - 1, Nat.sub_add_cancel Fintype.card_pos⟩
  have hU := measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp hind hXm hL hpsd hle hε0 hε1.le
  have hD := measureReal_eigenvalue_sum_le_le_card_mul_exp hind hXm hL hpsd hle hj hε0 hε1
  rw [hmean, eigenvalue_one Fintype.card_pos] at hU
  rw [hmean, eigenvalue_one (by omega)] at hD
  simp only [mul_one] at hU hD
  have hsub : ∀ᵐ ω ∂μ, ε ≤ specNorm (∑ k, X k ω - 1) →
      1 + ε ≤ eigenvalue (∑ k, X k ω) 0 ∨ eigenvalue (∑ k, X k ω) j ≤ 1 - ε := by
    filter_upwards [hY] with ω hA hω
    set A := ∑ k, X k ω
    have hA1 : (A - 1).IsHermitian := hA.sub Matrix.isHermitian_one
    have hshift : A - 1 = A + (-1 : ℝ) • (1 : Matrix n n 𝕜) := by
      rw [neg_one_smul, sub_eq_add_neg]
    have e0 : eigenvalue (A - 1) 0 = eigenvalue A 0 + -1 := by
      rw [hshift, hA.eigenvalue_add_smul_one (-1) Fintype.card_pos]
    have ej : eigenvalue (A - 1) j = eigenvalue A j + -1 := by
      rw [hshift, hA.eigenvalue_add_smul_one (-1) (by omega)]
    have hmono : eigenvalue A j ≤ eigenvalue A 0 :=
      hA.eigenvalue_le_eigenvalue (Nat.zero_le j) (by omega)
    rw [hA1.specNorm_eq_max hj, e0, ej, le_max_iff, le_abs, le_abs] at hω
    rcases hω with (h | h) | (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have h23 : -ε ^ 2 / (2 * L) ≤ -ε ^ 2 / (3 * L) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg ε) (by positivity) (by linarith)
  calc μ.real {ω | ε ≤ specNorm (∑ k, X k ω - 1)}
      ≤ μ.real ({ω | 1 + ε ≤ eigenvalue (∑ k, X k ω) 0} ∪
          {ω | eigenvalue (∑ k, X k ω) j ≤ 1 - ε}) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ μ.real {ω | 1 + ε ≤ eigenvalue (∑ k, X k ω) 0} +
          μ.real {ω | eigenvalue (∑ k, X k ω) j ≤ 1 - ε} := measureReal_union_le _ _
    _ ≤ Fintype.card n * Real.exp (-ε ^ 2 / (3 * L)) +
          Fintype.card n * Real.exp (-ε ^ 2 / (2 * L)) := add_le_add hU hD
    _ ≤ 2 * Fintype.card n * Real.exp (-ε ^ 2 / (3 * L)) := by
        have := Real.exp_le_exp.mpr h23
        have hd : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
        nlinarith

end NLAlib
