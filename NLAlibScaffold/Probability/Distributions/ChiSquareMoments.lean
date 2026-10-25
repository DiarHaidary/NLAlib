/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.ChiSquareMoments

/-!
# Moments of a difference of two independent chi-square variables (stage S10)

For independent standard Gaussian vectors $\mathbf{g}, \mathbf{h}$ of dimension
$d = \lvert n \rvert$,
the symmetric variable $X = \|\mathbf{g}\|^2 - \|\mathbf{h}\|^2$ has $\mathbb{E} X^2 = 4d$ and
$\mathbb{E} X^4 = 48 d^2 + 96 d$. These are the two moments the Paley–Zygmund step of the
early-truncation lower bound needs (`docs/design/LowRank-EstimatorLowerBounds.md`, §3.1). They
join `NLAlib/Probability/Distributions/ChiSquareMoments.lean`; their proofs are deferred.

## Main results

* `NLAlib.integral_norm_sq_sub_norm_sq_sq_of_hasLaw_gaussianVector`: $\mathbb{E}X^2 = 4d$.
* `NLAlib.integral_norm_sq_sub_norm_sq_pow_four_of_hasLaw_gaussianVector`:
  $\mathbb{E}X^4 = 48d^2 + 96d$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {g h : Ω → n → ℝ}

private lemma integral_norm_sq_moments_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hd : 0 < Fintype.card n) :
    ∫ ω, ‖WithLp.toLp 2 (g ω)‖ ^ 2 ∂μ = Fintype.card n ∧
      ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ 2 ∂μ = Fintype.card n * (Fintype.card n + 2) := by
  have hdpos : (0 : ℝ) < Fintype.card n := by exact_mod_cast hd
  have hG : Real.Gamma ((Fintype.card n : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have h1 : Real.Gamma ((Fintype.card n : ℝ) / 2 + 1) =
      (Fintype.card n : ℝ) / 2 * Real.Gamma ((Fintype.card n : ℝ) / 2) :=
    Real.Gamma_add_one (by positivity)
  have h2 : Real.Gamma ((Fintype.card n : ℝ) / 2 + 2) =
      ((Fintype.card n : ℝ) / 2 + 1) * Real.Gamma ((Fintype.card n : ℝ) / 2 + 1) := by
    rw [show (Fintype.card n : ℝ) / 2 + 2 = ((Fintype.card n : ℝ) / 2 + 1) + 1 by ring]
    exact Real.Gamma_add_one (by positivity)
  constructor
  · have := integral_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := 1) (by linarith)
    simp only [Real.rpow_one] at this
    rw [this, h1]
    field_simp
  · have := integral_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := 2) (by linarith)
    simp only [Real.rpow_two] at this
    rw [this, h2, h1]
    field_simp

/-- **The variance of a difference of two independent $\chi^2_d$ variables**: for independent
standard Gaussian vectors $\mathbf{g}, \mathbf{h}$ of dimension $d = \lvert n \rvert$,
$$\mathbb{E}\bigl(\|\mathbf{g}\|^2 - \|\mathbf{h}\|^2\bigr)^2 = 4d\,.$$
Proof: S, about 20 lines. Expand the square; $\mathbb{E}\|\mathbf{g}\|^4 = d(d+2)$ and
$\mathbb{E}\|\mathbf{g}\|^2 = d$ from `integral_norm_sq_rpow_of_hasLaw_gaussianVector` at $s = 2, 1$
(`Real.Gamma_add_one`, `Real.rpow_natCast`), the cross term
$\mathbb{E}\|\mathbf{g}\|^2\|\mathbf{h}\|^2 = d^2$ by independence
(`IndepFun.integral_mul_eq_mul_integral`
after `IndepFun.comp` with the measurable map $x \mapsto \|x\|^2$); integrability from
`integrable_norm_sq_rpow_of_hasLaw_gaussianVector`. Then $2d(d+2) - 2d^2 = 4d$. -/
theorem integral_norm_sq_sub_norm_sq_sq_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hh : HasLaw h (gaussianVector n) μ)
    (hgh : IndepFun g h μ) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2 - ‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2 ∂μ =
      4 * Fintype.card n := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hd0 | hd
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hd0
    simp [Subsingleton.elim (WithLp.toLp 2 (g _)) 0, Subsingleton.elim (WithLp.toLp 2 (h _)) 0]
  have hdpos : (0 : ℝ) < Fintype.card n := by exact_mod_cast hd
  obtain ⟨hU1, hU2⟩ := integral_norm_sq_moments_of_hasLaw_gaussianVector hg hd
  obtain ⟨hV1, hV2⟩ := integral_norm_sq_moments_of_hasLaw_gaussianVector hh hd
  have hmeas : Measurable fun x : n → ℝ => ‖WithLp.toLp 2 x‖ ^ 2 := by fun_prop
  have hind : IndepFun (fun ω => ‖WithLp.toLp 2 (g ω)‖ ^ 2)
      (fun ω => ‖WithLp.toLp 2 (h ω)‖ ^ 2) μ :=
    hgh.comp hmeas hmeas
  have hiU : Integrable (fun ω => ‖WithLp.toLp 2 (g ω)‖ ^ 2) μ := by
    have := integrable_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := 1) (by linarith)
    simpa only [Real.rpow_one] using this
  have hiV : Integrable (fun ω => ‖WithLp.toLp 2 (h ω)‖ ^ 2) μ := by
    have := integrable_norm_sq_rpow_of_hasLaw_gaussianVector hh (s := 1) (by linarith)
    simpa only [Real.rpow_one] using this
  have hiU2 : Integrable (fun ω => (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ 2) μ := by
    have := integrable_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := 2) (by linarith)
    simpa only [Real.rpow_two] using this
  have hiV2 : Integrable (fun ω => (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2) μ := by
    have := integrable_norm_sq_rpow_of_hasLaw_gaussianVector hh (s := 2) (by linarith)
    simpa only [Real.rpow_two] using this
  have hiUV : Integrable (fun ω => ‖WithLp.toLp 2 (g ω)‖ ^ 2 * ‖WithLp.toLp 2 (h ω)‖ ^ 2) μ :=
    hind.integrable_mul hiU hiV
  have hUV : ∫ ω, ‖WithLp.toLp 2 (g ω)‖ ^ 2 * ‖WithLp.toLp 2 (h ω)‖ ^ 2 ∂μ =
      Fintype.card n * Fintype.card n := by
    have h := hind.integral_mul_eq_mul_integral
      (hmeas.comp_aemeasurable hg.aemeasurable).aestronglyMeasurable
      (hmeas.comp_aemeasurable hh.aemeasurable).aestronglyMeasurable
    simp only [Pi.mul_apply] at h
    rw [h, hU1, hV1]
  have e : ∀ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2 - ‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2 =
      ((‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ 2 + (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2) -
        2 * (‖WithLp.toLp 2 (g ω)‖ ^ 2 * ‖WithLp.toLp 2 (h ω)‖ ^ 2) := fun ω => by ring
  have hI : Integrable (fun ω => (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ 2 +
      (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2) μ := hiU2.add hiV2
  have hJ : Integrable (fun ω => 2 * (‖WithLp.toLp 2 (g ω)‖ ^ 2 * ‖WithLp.toLp 2 (h ω)‖ ^ 2)) μ :=
    hiUV.const_mul 2
  simp only [e]
  rw [integral_sub hI hJ, integral_add hiU2 hiV2, integral_const_mul, hUV, hU2, hV2]
  ring

/-- Moments of $\|\mathbf{g}\|^2$ (helper): $\mathbb{E}(\|\mathbf{g}\|^2)^k
= \prod_{i<k}(d+2i)$ for $d = \lvert n \rvert > 0$. -/
private theorem integral_norm_sq_pow_eq_prod (hg : HasLaw g (gaussianVector n) μ)
    (hn : 0 < Fintype.card n) (k : ℕ) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ k ∂μ =
      ∏ i ∈ Finset.range k, ((Fintype.card n : ℝ) + 2 * i) := by
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast hn
  have hs : -((Fintype.card n : ℝ) / 2) < (k : ℝ) := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have h := integral_norm_sq_rpow_of_hasLaw_gaussianVector hg hs
  simp only [Real.rpow_natCast] at h
  have hpos : ∀ m : ℕ, (0 : ℝ) < (Fintype.card n : ℝ) / 2 + m := fun m => by
    have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    linarith
  have hG : ∀ m : ℕ, Real.Gamma ((Fintype.card n : ℝ) / 2 + m) =
      Real.Gamma ((Fintype.card n : ℝ) / 2) *
        ∏ i ∈ Finset.range m, ((Fintype.card n : ℝ) / 2 + i) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.cast_succ, show (Fintype.card n : ℝ) / 2 + (m + 1) =
          ((Fintype.card n : ℝ) / 2 + m) + 1 by ring,
        Real.Gamma_add_one (hpos m).ne', ih, Finset.prod_range_succ]
      ring
  have hΓ : Real.Gamma ((Fintype.card n : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hp : ∏ i ∈ Finset.range k, ((Fintype.card n : ℝ) + 2 * i) =
      2 ^ k * ∏ i ∈ Finset.range k, ((Fintype.card n : ℝ) / 2 + i) := by
    rw [show (2 : ℝ) ^ k = ∏ _i ∈ Finset.range k, (2 : ℝ) by simp, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [h, hG k, hp]
  field_simp

/-- Expansion of $\mathbb{E}(A - B)^4$ for integrable powers and factorised mixed terms
(helper). -/
private theorem integral_sub_pow_four_eq {A B : Ω → ℝ}
    (hA : ∀ k : ℕ, Integrable (fun ω => A ω ^ k) μ)
    (hB : ∀ k : ℕ, Integrable (fun ω => B ω ^ k) μ)
    (hAB : ∀ a b : ℕ, Integrable (fun ω => A ω ^ a * B ω ^ b) μ)
    (hI : ∀ a b : ℕ, ∫ ω, A ω ^ a * B ω ^ b ∂μ = (∫ ω, A ω ^ a ∂μ) * ∫ ω, B ω ^ b ∂μ) :
    ∫ ω, (A ω - B ω) ^ 4 ∂μ = ∫ ω, A ω ^ 4 ∂μ + ∫ ω, B ω ^ 4 ∂μ
      - 4 * ((∫ ω, A ω ^ 3 ∂μ) * ∫ ω, B ω ^ 1 ∂μ)
      - 4 * ((∫ ω, A ω ^ 1 ∂μ) * ∫ ω, B ω ^ 3 ∂μ)
      + 6 * ((∫ ω, A ω ^ 2 ∂μ) * ∫ ω, B ω ^ 2 ∂μ) := by
  have e : ∀ ω, (A ω - B ω) ^ 4 = A ω ^ 4 + B ω ^ 4 - 4 * (A ω ^ 3 * B ω ^ 1)
      - 4 * (A ω ^ 1 * B ω ^ 3) + 6 * (A ω ^ 2 * B ω ^ 2) := fun ω => by ring
  simp only [e]
  have i1 : Integrable (fun ω => A ω ^ 4 + B ω ^ 4) μ := (hA 4).add (hB 4)
  have i2 : Integrable (fun ω => A ω ^ 4 + B ω ^ 4 - 4 * (A ω ^ 3 * B ω ^ 1)) μ :=
    i1.sub ((hAB 3 1).const_mul 4)
  have i3 : Integrable (fun ω => A ω ^ 4 + B ω ^ 4 - 4 * (A ω ^ 3 * B ω ^ 1)
      - 4 * (A ω ^ 1 * B ω ^ 3)) μ := i2.sub ((hAB 1 3).const_mul 4)
  have i4 : Integrable (fun ω => 6 * (A ω ^ 2 * B ω ^ 2)) μ := (hAB 2 2).const_mul 6
  rw [integral_add i3 i4, integral_sub i2 ((hAB 1 3).const_mul 4),
    integral_sub i1 ((hAB 3 1).const_mul 4), integral_add (hA 4) (hB 4),
    integral_const_mul, integral_const_mul, integral_const_mul, hI 3 1, hI 1 3, hI 2 2]

/-- **The fourth moment of a difference of two independent $\chi^2_d$ variables**: for
independent standard Gaussian vectors $\mathbf{g}, \mathbf{h}$ of dimension
$d = \lvert n \rvert$,
$$\mathbb{E}\bigl(\|\mathbf{g}\|^2 - \|\mathbf{h}\|^2\bigr)^4 = 48 d^2 + 96 d\,.$$
Proof: S, about 30 lines. With $U = \|\mathbf{g}\|^2$, $V = \|\mathbf{h}\|^2$ independent and
$\mathbb{E} U^j = d(d+2)\cdots(d+2j-2)$ (`integral_norm_sq_rpow_of_hasLaw_gaussianVector` at
$s = j$, `Real.Gamma_add_one` four times),
$\mathbb{E}(U - V)^4 = 2\mathbb{E}U^4 - 8\,\mathbb{E}U^3\,\mathbb{E}U + 6(\mathbb{E}U^2)^2$
(binomial expansion, `IndepFun.integral_mul_eq_mul_integral` on each mixed term), and
$2d(d+2)(d+4)(d+6) - 8d^2(d+2)(d+4) + 6d^2(d+2)^2 = 48d(d+2)$ (`ring`). -/
theorem integral_norm_sq_sub_norm_sq_pow_four_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hh : HasLaw h (gaussianVector n) μ)
    (hgh : IndepFun g h μ) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2 - ‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 4 ∂μ =
      48 * (Fintype.card n : ℝ) ^ 2 + 96 * Fintype.card n := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hd0 | hd
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hd0
    have hz : ∀ x : n → ℝ, ‖WithLp.toLp 2 x‖ = 0 := fun x => by
      rw [show x = 0 from funext fun i => isEmptyElim i]
      simp
    simp [hz]
  have hpow (k : ℕ) : ∀ {m : Ω → n → ℝ}, HasLaw m (gaussianVector n) μ →
      Integrable (fun ω => (‖WithLp.toLp 2 (m ω)‖ ^ 2) ^ k) μ := by
    intro m hm
    have hs : -((Fintype.card n : ℝ) / 2) < (k : ℝ) := by
      have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      have : (0 : ℝ) < Fintype.card n := by exact_mod_cast hd
      linarith
    simpa only [Real.rpow_natCast] using integrable_norm_sq_rpow_of_hasLaw_gaussianVector hm hs
  have hmixI : ∀ a b : ℕ,
      ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ a * (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ b ∂μ =
        (∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ a ∂μ) * ∫ ω, (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ b ∂μ := by
    intro a b
    have hf : Measurable fun x : n → ℝ => (‖WithLp.toLp 2 x‖ ^ 2) ^ a := by fun_prop
    have hk : Measurable fun x : n → ℝ => (‖WithLp.toLp 2 x‖ ^ 2) ^ b := by fun_prop
    exact (hgh.comp hf hk).integral_mul_eq_mul_integral
      (hf.comp_aemeasurable hg.aemeasurable).aestronglyMeasurable
      (hk.comp_aemeasurable hh.aemeasurable).aestronglyMeasurable
  have hmix : ∀ a b : ℕ, Integrable (fun ω => (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ a *
      (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ b) μ := by
    intro a b
    have hf : Measurable fun x : n → ℝ => (‖WithLp.toLp 2 x‖ ^ 2) ^ a := by fun_prop
    have hk : Measurable fun x : n → ℝ => (‖WithLp.toLp 2 x‖ ^ 2) ^ b := by fun_prop
    exact (hgh.comp hf hk).integrable_mul (hpow a hg) (hpow b hh)
  rw [integral_sub_pow_four_eq (A := fun ω => ‖WithLp.toLp 2 (g ω)‖ ^ 2)
      (B := fun ω => ‖WithLp.toLp 2 (h ω)‖ ^ 2) (hpow · hg) (hpow · hh) hmix hmixI]
  simp only [integral_norm_sq_pow_eq_prod hg hd, integral_norm_sq_pow_eq_prod hh hd,
    Finset.prod_range_succ, Finset.prod_range_zero]
  push_cast
  ring

end NLAlib
