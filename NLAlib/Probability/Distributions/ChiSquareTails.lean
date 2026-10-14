/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.ChiSquare

/-!
# Chernoff tails of `χ²_n`

For a standard Gaussian vector `X` in `ℝⁿ`, Chernoff's bound with the exact Laplace transform of
`‖X‖² ~ χ²_n` at `θ = (1 - 1/β)/2` gives `P(‖X‖² ≥ β n)` and `P(‖X‖² ≤ β n)` at most
`exp ((n/2)(1 - β + log β))`, on either side of `β = 1`; the relative deviation
`P(ε ≤ |‖X‖²/n - 1|) ≤ 2 exp (-n (ε²/4 - ε³/6))` follows, with the polynomial exponent of
Dasgupta and Gupta (2003). The weighted Laplace transform `E exp (∑ θᵢ Xᵢ²)` is the input of the
projection tails of a uniform unit vector (`NLAlib/RandomMatrix/Haar/Sphere.lean`).

The lower tail dominates both lower bounds of `NLAlib/Probability/Distributions/ChiSquare.lean`
(Laurent–Massart and the small ball; CONTRIBUTING §5.2 rule 6). This file is a skeleton of
Sketching stage S2 (`docs/design/Sketching-S2.md` §3.1, §8): at the wrap-up it merges into
`ChiSquare.lean`, where both older bounds are reproved from the new tail and keep their names.

## Main results

* `NLAlib.integral_exp_sum_mul_sq_of_hasLaw_gaussianVector`:
  `E exp (∑ θᵢ Xᵢ²) = ∏ (1 - 2θᵢ)^{-1/2}`.
* `NLAlib.measureReal_mul_card_le_norm_sq_le_of_hasLaw_gaussianVector`: the upper tail, `β ≥ 1`.
* `NLAlib.measureReal_norm_sq_le_mul_card_le_of_hasLaw_gaussianVector`: the lower tail,
  `0 < β ≤ 1`.
* `NLAlib.measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector`: the relative
  deviation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {X : Ω → n → ℝ} {ε β : ℝ}

private theorem integral_exp_mul_sq_gaussianReal' {θ : ℝ} (hθ : 2 * θ < 1) :
    ∫ y, Real.exp (θ * y ^ 2) ∂(gaussianReal 0 1) = (1 - 2 * θ) ^ (-(1 / 2 : ℝ)) := by
  have hu : 0 < 1 - 2 * θ := by linarith
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal_def, smul_eq_mul, NNReal.coe_one, sub_zero, mul_one]
  have h (x : ℝ) : (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (θ * x ^ 2)
      = (√(2 * Real.pi))⁻¹ * Real.exp (-((1 - 2 * θ) / 2) * x ^ 2) := by
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  simp only [h]
  rw [integral_const_mul, integral_gaussian,
    show Real.pi / ((1 - 2 * θ) / 2) = (2 * Real.pi) / (1 - 2 * θ) by field_simp,
    Real.sqrt_div (by positivity), Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  have : √(2 * Real.pi) ≠ 0 := by positivity
  field_simp

/-- `log (1 + ε) ≤ ε - ε²/2 + ε³/3` for `ε ≥ 0`: the difference has derivative
`ε³/(1 + ε) ≥ 0` and vanishes at `0`. -/
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

private theorem log_one_sub_le' {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Real.log (1 - u) ≤ -u - u ^ 2 / 2 := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := u) (by rwa [abs_of_nonneg hu0])
  have := sum_le_hasSum (Finset.range 2) (fun n _ => by positivity) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
  norm_num at this
  linarith

/-- Chernoff's bound at `θ`, with the exact Laplace transform: both tails at once. -/
private theorem measureReal_chernoff (hX : HasLaw X (gaussianVector n) μ) (c : ℝ) {θ : ℝ}
    (hθ : 2 * θ < 1) (hθ0 : 0 ≤ θ) :
    μ.real {ω | c ≤ ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤
      Real.exp (-θ * c) * (1 - 2 * θ) ^ (-(Fintype.card n / 2 : ℝ)) := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 inferInstance
  have hlap := integral_exp_mul_norm_sq_of_hasLaw_gaussianVector hX hθ
  have hint : Integrable (fun ω => Real.exp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2)) μ :=
    Integrable.of_integral_ne_zero (by rw [hlap]; exact (Real.rpow_pos_of_pos (by linarith) _).ne')
  have h := measure_ge_le_exp_mul_mgf (X := fun ω => ‖WithLp.toLp 2 (X ω)‖ ^ 2) c hθ0 hint
  rwa [mgf, hlap] at h

private theorem measureReal_chernoff_le (hX : HasLaw X (gaussianVector n) μ) (c : ℝ) {s : ℝ}
    (hs : 0 ≤ s) :
    μ.real {ω | ‖WithLp.toLp 2 (X ω)‖ ^ 2 ≤ c} ≤
      Real.exp (s * c) * (1 + 2 * s) ^ (-(Fintype.card n / 2 : ℝ)) := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 inferInstance
  have hlap := integral_exp_mul_norm_sq_of_hasLaw_gaussianVector hX (θ := -s) (by linarith)
  rw [show 1 - 2 * -s = 1 + 2 * s by ring] at hlap
  have hint : Integrable (fun ω => Real.exp (-s * ‖WithLp.toLp 2 (X ω)‖ ^ 2)) μ :=
    Integrable.of_integral_ne_zero (by rw [hlap]; exact (Real.rpow_pos_of_pos (by linarith) _).ne')
  have h := measure_le_le_exp_mul_mgf (X := fun ω => ‖WithLp.toLp 2 (X ω)‖ ^ 2) c
    (neg_nonpos.2 hs) hint
  rwa [mgf, hlap, neg_neg] at h

/-- `exp (a) * (β⁻¹)^{-N/2} = exp (a + (N/2) log β)`. -/
private theorem exp_mul_inv_rpow (a N : ℝ) (hβ : 0 < β) :
    Real.exp a * (β⁻¹) ^ (-(N / 2 : ℝ)) = Real.exp (a + N / 2 * Real.log β) := by
  rw [Real.inv_rpow hβ.le, ← Real.rpow_neg hβ.le, neg_neg, Real.rpow_def_of_pos hβ,
    ← Real.exp_add]
  ring_nf

/-- **The weighted Laplace transform of a Gaussian vector**: `E exp (∑ θᵢ Xᵢ²) = ∏ (1 - 2θᵢ)^{-1/2}`
for weights with `θᵢ < 1/2`, by independence of the coordinates. The equal-weight case is
`NLAlib.integral_exp_mul_norm_sq_of_hasLaw_gaussianVector`; two weights give the projection tails
of a uniform unit vector. -/
theorem integral_exp_sum_mul_sq_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    {θ : n → ℝ} (hθ : ∀ i, 2 * θ i < 1) :
    ∫ ω, Real.exp (∑ i, θ i * X ω i ^ 2) ∂μ = ∏ i, (1 - 2 * θ i) ^ (-(1 / 2 : ℝ)) := by
  refine (hX.integral_comp (f := fun x : n → ℝ => Real.exp (∑ i, θ i * x i ^ 2))
    (Continuous.aestronglyMeasurable (by fun_prop))).trans ?_
  simp only [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i y => Real.exp (θ i * y ^ 2))]
  exact Finset.prod_congr rfl fun i _ => integral_exp_mul_sq_gaussianReal' (hθ i)

/-- **Upper Chernoff tail of `χ²_n`**: `P(β n ≤ ‖X‖²) ≤ exp ((n/2)(1 - β + log β))` for
`β ≥ 1`, Chernoff's bound with the exact Laplace transform at `θ = (1 - 1/β)/2`. At every
threshold it is at least as good as Laurent and Massart's upper tail, which stays in the library
as the sub-Gaussian-vector bound `NLAlib.IsSubgaussianVector.measure_norm_sq_ge_le` at proxy `1`
(rule 6: that theorem is about every sub-Gaussian vector and keeps its form). The exponent of
Dasgupta and Gupta (2003), there for the projection of a uniform unit vector.
Result: chi-square-upper-tail -/
theorem measureReal_mul_card_le_norm_sq_le_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ) (hβ : 1 ≤ β) :
    μ.real {ω | β * Fintype.card n ≤ ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤
      Real.exp (Fintype.card n / 2 * (1 - β + Real.log β)) := by
  have hβ0 : 0 < β := by linarith
  have hθ : 2 * ((1 - β⁻¹) / 2) < 1 := by
    have := inv_pos.2 hβ0; linarith
  have hθ0 : 0 ≤ (1 - β⁻¹) / 2 := by
    have := inv_le_one_of_one_le₀ hβ; linarith
  refine (measureReal_chernoff hX _ hθ hθ0).trans (le_of_eq ?_)
  rw [show 1 - 2 * ((1 - β⁻¹) / 2) = β⁻¹ by ring, exp_mul_inv_rpow _ _ hβ0]
  congr 1
  field_simp
  ring

/-- **Lower Chernoff tail of `χ²_n`**: `P(‖X‖² ≤ β n) ≤ exp ((n/2)(1 - β + log β))` for
`0 < β ≤ 1`, Chernoff's bound with the exact Laplace transform at `θ = (1 - 1/β)/2`. It dominates
(CONTRIBUTING §5.2 rule 6) both lower bounds of `ChiSquare.lean`: Laurent and Massart's
`NLAlib.measureReal_norm_sq_le_of_hasLaw_gaussianVector` (at `β = 1 - 2√(t/n)`, with
`log (1 - u) ≤ -u - u²/2`) and the small ball
`NLAlib.measureReal_norm_sq_le_le_rpow_of_hasLaw_gaussianVector` (at `β = u/n`, the same Chernoff
parameter `s = (n/u - 1)/2`, after dropping the factor `e^{-u/2} ≤ 1`). At the merge into
`ChiSquare.lean` both become corollaries of this tail and keep their names; the private
`measureReal_norm_sq_le_le_exp_mul_rpow` there is this bound before optimisation. The exponent of
Dasgupta and Gupta (2003), there for the projection of a uniform unit vector.
Result: chi-square-lower-tail -/
theorem measureReal_norm_sq_le_mul_card_le_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ) (hβ0 : 0 < β) (hβ : β ≤ 1) :
    μ.real {ω | ‖WithLp.toLp 2 (X ω)‖ ^ 2 ≤ β * Fintype.card n} ≤
      Real.exp (Fintype.card n / 2 * (1 - β + Real.log β)) := by
  have hs : 0 ≤ (β⁻¹ - 1) / 2 := by
    have := one_le_inv_iff₀.2 ⟨hβ0, hβ⟩; linarith
  refine (measureReal_chernoff_le hX _ hs).trans (le_of_eq ?_)
  rw [show 1 + 2 * ((β⁻¹ - 1) / 2) = β⁻¹ by ring, exp_mul_inv_rpow _ _ hβ0]
  congr 1
  field_simp

/-- **Relative deviation of `χ²_n`**: `P(ε ≤ |‖X‖²/n - 1|) ≤ 2 exp (-n (ε²/4 - ε³/6))` for
`ε ≥ 0`, from the two Chernoff tails with `log (1 + ε) ≤ ε - ε²/2 + ε³/3` and
`log (1 - ε) ≤ -ε - ε²/2`; for `ε ≥ 1` the lower event is `{‖X‖² ≤ 0}`, null for nonempty `n`.
The bound is at least `2` for `ε ≥ 3/2` and for empty `n`. The exponent of Dasgupta and Gupta
(2003); [Woodruff2014, Lemma 18] has Laurent and Massart's `ε² n / 16` in its place. -/
theorem measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |‖WithLp.toLp 2 (X ω)‖ ^ 2 / Fintype.card n - 1|} ≤
      2 * Real.exp (-(Fintype.card n * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 inferInstance
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hN | hN
  · rw [hN, Nat.cast_zero, zero_mul, neg_zero, Real.exp_zero]
    exact measureReal_le_one.trans (by norm_num)
  set N : ℝ := (Fintype.card n : ℝ) with hN_def
  replace hN : 0 < N := Nat.cast_pos.2 hN
  have hsub : {ω | ε ≤ |‖WithLp.toLp 2 (X ω)‖ ^ 2 / N - 1|} ⊆
      {ω | (1 + ε) * N ≤ ‖WithLp.toLp 2 (X ω)‖ ^ 2} ∪
        {ω | ‖WithLp.toLp 2 (X ω)‖ ^ 2 ≤ (1 - ε) * N} := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
    rcases le_abs'.1 hω with h | h
    · right
      rw [← div_le_iff₀ hN]
      linarith
    · left
      rw [← le_div_iff₀ hN]
      linarith
  have hup : μ.real {ω | (1 + ε) * N ≤ ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤
      Real.exp (-(N * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
    refine (measureReal_mul_card_le_norm_sq_le_of_hasLaw_gaussianVector hX
      (by linarith)).trans (Real.exp_le_exp.2 ?_)
    have := log_one_add_le_cubic hε
    nlinarith
  have hlo : μ.real {ω | ‖WithLp.toLp 2 (X ω)‖ ^ 2 ≤ (1 - ε) * N} ≤
      Real.exp (-(N * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
    rcases lt_or_ge ε 1 with hε1 | hε1
    · refine (measureReal_norm_sq_le_mul_card_le_of_hasLaw_gaussianVector hX
        (by linarith) (by linarith)).trans (Real.exp_le_exp.2 ?_)
      have := log_one_sub_le' hε hε1
      have : 0 ≤ N * ε ^ 3 := by positivity
      nlinarith
    · refine (measureReal_mono (s₂ := {ω | ‖WithLp.toLp 2 (X ω)‖ ^ 2 ≤ 0})
        (fun ω hω => ?_) (measure_ne_top _ _)).trans
        ((measureReal_norm_sq_le_le_rpow_of_hasLaw_gaussianVector hX le_rfl).trans ?_)
      · simp only [Set.mem_ofPred_eq] at hω ⊢
        exact hω.trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) hN.le)
      · rw [mul_zero, zero_div, Real.zero_rpow (by positivity)]
        positivity
  calc _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add hup hlo
    _ = _ := by ring

end NLAlib
