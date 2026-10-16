/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Approximation.ChebyshevCoefficients
public import Mathlib.Analysis.Polynomial.Fourier
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic.Ring

/-!
# Chebyshev series and the Fourier dictionary

The even cosine pullback identifies the canonical full Chebyshev coefficients with Fourier
coefficients. Continuity and absolute coefficient summability then give pointwise reconstruction,
including the endpoints. No holomorphic extension or ellipse is required.

## Main results

* `NLAlib.fourierCoeff_cosinePullback_eq_chebyshevCoeff`: canonical Fourier representation.
* `NLAlib.hasSum_chebyshevCoeff_mul_eval_T`: reconstruction from summable coefficients.
-/

@[expose] public section

open MeasureTheory Polynomial Polynomial.Chebyshev Complex

namespace NLAlib

attribute [local instance] Polynomial.instTwoPiPos

private lemma re_fourier_coe (k : ℕ) (θ : ℝ) :
    (fourier (k : ℤ) (θ : AddCircle (2 * Real.pi))).re = Real.cos ((k : ℝ) * θ) := by
  rw [fourier_coe_apply]
  push_cast
  have heq : 2 * (Real.pi : ℂ) * I * (k : ℂ) * (θ : ℂ) / (2 * Real.pi) =
      (((k : ℝ) * θ : ℝ) : ℂ) * I := by
    push_cast
    field_simp
  rw [heq, Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

private lemma fourier_apply_neg (k : ℤ) (θ : AddCircle (2 * Real.pi)) :
    fourier k (-θ) = fourier (-k) θ := by
  simp only [fourier_apply, smul_neg, neg_smul]

private lemma pullback_even (f : ℝ → ℂ) (θ : AddCircle (2 * Real.pi)) :
    f ((fourier 1 (-θ)).re) = f ((fourier 1 θ).re) := by
  rw [fourier_apply_neg, fourier_neg]
  rfl

private lemma pullback_coeff_neg (f : ℝ → ℂ) (k : ℤ) :
    fourierCoeff (fun θ : AddCircle (2 * Real.pi) => f ((fourier 1 θ).re)) (-k) =
      fourierCoeff (fun θ : AddCircle (2 * Real.pi) => f ((fourier 1 θ).re)) k := by
  rw [fourierCoeff, fourierCoeff]
  have h := MeasureTheory.integral_neg_eq_self
    (fun θ : AddCircle (2 * Real.pi) => fourier (-k) θ • f ((fourier 1 θ).re))
    AddCircle.haarAddCircle
  simpa only [fourier_apply_neg, neg_neg, fourier_neg, Complex.conj_re, Complex.conj_conj] using h

private lemma cosine_full_period {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) (k : ℕ) :
    (∫ θ in 0..2 * Real.pi, f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : ℂ)) =
      2 * ∫ θ in 0..Real.pi, f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : ℂ) := by
  let g : ℝ → ℂ := fun θ => f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : ℂ)
  have hfc : Continuous (fun θ => f (Real.cos θ)) :=
    hf.comp_continuous Real.continuous_cos (fun θ => ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
  have hg : Continuous g := hfc.mul (by fun_prop)
  have hreflect := intervalIntegral.integral_comp_sub_left (f := g)
    (a := Real.pi) (b := 2 * Real.pi) (2 * Real.pi)
  have hsym : ∀ θ, g (2 * Real.pi - θ) = g θ := by
    intro θ
    have hcos : Real.cos ((k : ℝ) * (2 * Real.pi - θ)) = Real.cos ((k : ℝ) * θ) := by
      rw [mul_sub, Real.cos_nat_mul_two_pi_sub]
    simp only [g, Real.cos_two_pi_sub, hcos]
  simp_rw [hsym] at hreflect
  have heq : (∫ θ in Real.pi..2 * Real.pi, g θ) = ∫ θ in 0..Real.pi, g θ := by
    simpa only [sub_self, show 2 * Real.pi - Real.pi = Real.pi by ring] using hreflect
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable 0 Real.pi) (hg.intervalIntegrable Real.pi (2 * Real.pi))
  change (∫ θ in 0..2 * Real.pi, g θ) = 2 * ∫ θ in 0..Real.pi, g θ
  rw [← hadd, heq]
  ring

private lemma pullback_coeff_nat {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) (k : ℕ) :
    fourierCoeff (fun θ : AddCircle (2 * Real.pi) => f ((fourier 1 θ).re)) (k : ℤ) =
      chebyshevCoeff f k / (if k = 0 then 1 else 2) := by
  let g : AddCircle (2 * Real.pi) → ℂ := fun θ => f ((fourier 1 θ).re)
  have hgc : Continuous g := hf.comp_continuous (by fun_prop) (fun θ => by
    have hn : ‖fourier (1 : ℤ) θ‖ = 1 := Circle.norm_coe _
    exact ⟨by linarith [Complex.abs_re_le_norm (fourier 1 θ), neg_abs_le (fourier 1 θ).re],
      (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans_eq hn)⟩)
  have heven := pullback_coeff_neg f (k : ℤ)
  have hcont (n : ℤ) : Continuous (fun θ : ℝ =>
      fourier n (θ : AddCircle (2 * Real.pi)) * g θ) :=
    ((fourier n).continuous.comp (AddCircle.continuous_mk' _)).mul
      (hgc.comp (AddCircle.continuous_mk' _))
  have hadd := intervalIntegral.integral_add (μ := volume)
    ((hcont (-(k : ℤ))).intervalIntegrable 0 (2 * Real.pi))
    ((hcont (k : ℤ)).intervalIntegrable 0 (2 * Real.pi))
  have hpair : ∀ θ : ℝ,
      fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) * g θ +
        fourier (k : ℤ) (θ : AddCircle (2 * Real.pi)) * g θ =
          2 * (f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : ℂ)) := by
    intro θ
    rw [← add_mul, fourier_neg, add_comm ((starRingEnd ℂ) _) _, Complex.add_conj, re_fourier_coe]
    simp only [g]
    rw [show (fourier (1 : ℤ) (θ : AddCircle (2 * Real.pi))).re = Real.cos θ by
      simpa only [Nat.cast_one, one_mul] using re_fourier_coe 1 θ]
    push_cast
    ring
  have heq : 2 * fourierCoeff g (k : ℤ) =
      ((2 / Real.pi : ℝ) : ℂ) *
        ∫ θ in 0..Real.pi, f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : ℂ) := by
    calc
      2 * fourierCoeff g (k : ℤ) = fourierCoeff g (k : ℤ) + fourierCoeff g (-(k : ℤ)) := by
        rw [heven]; ring
      _ = _ := by
        rw [fourierCoeff_eq_intervalIntegral _ _ 0, fourierCoeff_eq_intervalIntegral _ _ 0]
        simp only [zero_add, smul_eq_mul, Complex.real_smul, neg_neg]
        rw [← mul_add, ← hadd]
        simp_rw [hpair]
        rw [intervalIntegral.integral_const_mul, cosine_full_period hf]
        simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
          Complex.ofReal_one]
        field_simp
  have hn : chebyshevCoeff f k / (if k = 0 then 1 else 2) =
      (1 / (Real.pi : ℂ)) *
        ∫ θ in 0..Real.pi, f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : ℂ) := by
    have hc : (((if k = 0 then 1 else 2) / Real.pi : ℝ) : ℂ) =
        (if k = 0 then 1 else 2) / (Real.pi : ℂ) := by
      split_ifs <;> push_cast <;> rfl
    unfold chebyshevCoeff
    change ((((if k = 0 then 1 else 2) / Real.pi : ℝ) : ℂ) *
      (∫ θ in 0..Real.pi, f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : ℂ))) /
      (if k = 0 then 1 else 2) = _
    calc
      _ = ((if k = 0 then 1 else 2) / (Real.pi : ℂ)) *
          (∫ θ in 0..Real.pi, f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : ℂ)) /
          (if k = 0 then 1 else 2) := congrArg (fun z : ℂ => z * _ / _) hc
      _ = _ := by split_ifs <;> ring
  change fourierCoeff g (k : ℤ) = _
  rw [hn]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at heq
  linear_combination heq / 2

/-- The Fourier coefficient of the even cosine pullback is the canonical full Chebyshev
coefficient, divided by two away from frequency zero. Negative frequencies use the same index
modulus. [Trefethen2019, Theorem 3.1], expressed through Mathlib's Fourier coefficients. -/
theorem fourierCoeff_cosinePullback_eq_chebyshevCoeff
    {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) (k : ℤ) :
    fourierCoeff (fun θ : AddCircle (2 * Real.pi) => f ((fourier 1 θ).re)) k =
      chebyshevCoeff f k.natAbs / (if k = 0 then 1 else 2) := by
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · simpa only [Int.natAbs_natCast, Nat.cast_eq_zero] using pullback_coeff_nat hf n
  · rw [pullback_coeff_neg]
    simpa only [Int.natAbs_neg, Int.natAbs_natCast, neg_eq_zero, Nat.cast_eq_zero] using
      pullback_coeff_nat hf n

private lemma continuous_pullback {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) :
    Continuous (fun θ : AddCircle (2 * Real.pi) => f ((fourier 1 θ).re)) := by
  apply hf.comp_continuous (by fun_prop)
  intro θ
  have hn : ‖fourier (1 : ℤ) θ‖ = 1 := Circle.norm_coe _
  exact ⟨by linarith [Complex.abs_re_le_norm (fourier 1 θ), neg_abs_le (fourier 1 θ).re],
    (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans_eq hn)⟩

private lemma summable_pullback_coeff {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hs : Summable (fun k : ℕ => ‖chebyshevCoeff f k‖)) :
    Summable (fourierCoeff (fun θ : AddCircle (2 * Real.pi) => f ((fourier 1 θ).re))) := by
  have hn : Summable (fun k : ℕ =>
      ‖fourierCoeff (fun θ : AddCircle (2 * Real.pi) => f ((fourier 1 θ).re)) (k : ℤ)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
    intro k
    rw [fourierCoeff_cosinePullback_eq_chebyshevCoeff hf]
    simp only [Int.natAbs_natCast, Nat.cast_eq_zero]
    split_ifs <;> simp only [div_one, norm_div, Complex.norm_two]
    · exact le_refl _
    · exact div_le_self (norm_nonneg _) (by norm_num)
  have hp := hn.of_norm
  have hm : Summable (fun k : ℕ =>
      fourierCoeff (fun θ : AddCircle (2 * Real.pi) => f ((fourier 1 θ).re))
        (-((k : ℤ) + 1))) := by
    simp_rw [pullback_coeff_neg]
    exact_mod_cast (summable_nat_add_iff 1).mpr hp
  exact Summable.of_nat_of_neg_add_one hp hm

private lemma pair_term {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) {k : ℕ} (hk : 0 < k) (θ : ℝ) :
    fourierCoeff (fun t : AddCircle (2 * Real.pi) => f ((fourier 1 t).re)) (k : ℤ) *
        fourier (k : ℤ) (θ : AddCircle (2 * Real.pi)) +
      fourierCoeff (fun t : AddCircle (2 * Real.pi) => f ((fourier 1 t).re)) (-(k : ℤ)) *
        fourier (-(k : ℤ)) (θ : AddCircle (2 * Real.pi)) =
      chebyshevCoeff f k * (T ℂ (k : ℤ)).eval (Real.cos θ : ℂ) := by
  rw [pullback_coeff_neg, pullback_coeff_nat hf, if_neg hk.ne', ← mul_add,
    fourier_neg, Complex.add_conj, re_fourier_coe]
  have hT : (T ℂ (k : ℤ)).eval (Real.cos θ : ℂ) =
      (Real.cos ((k : ℝ) * θ) : ℂ) := by
    have h := eval_map_apply (p := T ℝ (k : ℤ)) (f := algebraMap ℝ ℂ) (Real.cos θ)
    rw [map_T, T_real_cos, Int.cast_natCast] at h
    exact h
  rw [hT]
  push_cast
  ring

private lemma complex_reconstruction_cos {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hs : Summable (fun k : ℕ => ‖chebyshevCoeff f k‖)) (θ : ℝ) :
    HasSum (fun k : ℕ => chebyshevCoeff f k * (T ℂ (k : ℤ)).eval (Real.cos θ : ℂ))
      (f (Real.cos θ)) := by
  let g : C(AddCircle (2 * Real.pi), ℂ) := ⟨_, continuous_pullback hf⟩
  let u : ℤ → ℂ := fun k => fourierCoeff g k * fourier k (θ : AddCircle (2 * Real.pi))
  have hu : HasSum u (f (Real.cos θ)) := by
    have h := has_pointwise_sum_fourier_series_of_summable
      (f := g) (summable_pullback_coeff hf hs) (θ : AddCircle (2 * Real.pi))
    change HasSum u (f ((fourier 1 (θ : AddCircle (2 * Real.pi))).re)) at h
    rw [show (fourier (1 : ℤ) (θ : AddCircle (2 * Real.pi))).re = Real.cos θ by
      simpa only [Nat.cast_one, one_mul] using re_fourier_coe 1 θ] at h
    exact h
  have hp := hu.summable.comp_injective Nat.cast_injective
  have hn : Summable (fun k : ℕ => u (-((k + 1 : ℕ) : ℤ))) :=
    hu.summable.comp_injective (show Function.Injective (fun k : ℕ => -((k + 1 : ℕ) : ℤ)) by
      intro a b hab
      exact Nat.add_right_cancel (Int.natCast_inj.mp (neg_injective hab)))
  have hps := (summable_nat_add_iff 1).mpr hp
  have hsum : (∑' k : ℕ, u (k : ℤ)) + (∑' k : ℕ, u (-((k + 1 : ℕ) : ℤ))) =
      f (Real.cos θ) := by
    rw [← hu.tsum_eq]
    exact (tsum_of_nat_of_neg_add_one hp hn).symm
  have hsplit := hp.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  have hpair := hps.hasSum.add hn.hasSum
  have hterm : ∀ k : ℕ, u ((k + 1 : ℕ) : ℤ) + u (-((k + 1 : ℕ) : ℤ)) =
      chebyshevCoeff f (k + 1) * (T ℂ ((k + 1 : ℕ) : ℤ)).eval (Real.cos θ : ℂ) := by
    intro k
    exact pair_term hf (Nat.succ_pos k) θ
  change HasSum (fun k : ℕ => u ((k + 1 : ℕ) : ℤ) + u (-((k + 1 : ℕ) : ℤ))) _ at hpair
  simp_rw [hterm] at hpair
  have hfull := hpair.zero_add (f := fun k : ℕ =>
    chebyshevCoeff f k * (T ℂ (k : ℤ)).eval (Real.cos θ : ℂ))
  have hzero : chebyshevCoeff f 0 * (T ℂ (0 : ℤ)).eval (Real.cos θ : ℂ) = u 0 := by
    change chebyshevCoeff f 0 * (T ℂ (0 : ℤ)).eval (Real.cos θ : ℂ) =
      fourierCoeff (fun t : AddCircle (2 * Real.pi) => f ((fourier 1 t).re)) 0 *
        fourier 0 (θ : AddCircle (2 * Real.pi))
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, pullback_coeff_nat hf]
    simp only [Nat.cast_zero, T_zero, eval_one, mul_one, ↓reduceIte, div_one, fourier_zero]
  simp only [Function.comp_apply, Nat.cast_zero] at hfull hsplit
  rw [hzero, ← add_assoc, hsplit, hsum] at hfull
  exact hfull

/-- A continuous function on $[-1,1]$ with absolutely summable full Chebyshev coefficients
is reconstructed by its Chebyshev series at every point, including the endpoints.
The Fourier convergence criterion underlying [Trefethen2019, Theorem 3.1] is expressed here
through Mathlib's summable Fourier-series theorem, and generalized to RCLike values. -/
theorem hasSum_chebyshevCoeff_mul_eval_T
    {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜}
    (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1))
    (hs : Summable (fun k : ℕ => ‖chebyshevCoeff f k‖)) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => chebyshevCoeff f k *
      (Polynomial.Chebyshev.T 𝕜 (k : ℤ)).eval (x : 𝕜)) (f x) := by
  let L : 𝕜 →ₗᵢ[ℝ] ℂ :=
    { RCLike.toComplex.toAlgHom.toLinearMap with norm_map' := RCLike.norm_toComplex }
  have hfc : ContinuousOn (fun t => RCLike.toComplex (f t)) (Set.Icc (-1 : ℝ) 1) :=
    RCLike.continuous_toComplex.comp_continuousOn hf
  have hsc : Summable (fun k : ℕ =>
      ‖chebyshevCoeff (fun t => RCLike.toComplex (f t)) k‖) := by
    simpa only [← toComplex_chebyshevCoeff, RCLike.norm_toComplex] using hs
  have hc := complex_reconstruction_cos hfc hsc (Real.arccos x)
  rw [Real.cos_arccos hx.1 hx.2] at hc
  have hT (k : ℕ) : RCLike.toComplex ((T 𝕜 (k : ℤ)).eval (x : 𝕜)) =
      (T ℂ (k : ℤ)).eval (x : ℂ) := by
    have h := eval_map_apply (p := T 𝕜 (k : ℤ))
      (f := RCLike.toComplex.toRingHom) (x : 𝕜)
    rw [map_T] at h
    change (T ℂ (k : ℤ)).eval (RCLike.toComplex (x : 𝕜)) =
      RCLike.toComplex ((T 𝕜 (k : ℤ)).eval (x : 𝕜)) at h
    rw [RCLike.toComplex_ofReal] at h
    exact h.symm
  have hm : HasSum (fun k : ℕ => L (chebyshevCoeff f k *
      (T 𝕜 (k : ℤ)).eval (x : 𝕜))) (L (f x)) := by
    change HasSum (fun k : ℕ => RCLike.toComplex (chebyshevCoeff f k *
      (T 𝕜 (k : ℤ)).eval (x : 𝕜))) (RCLike.toComplex (f x))
    simp_rw [map_mul, toComplex_chebyshevCoeff, hT]
    exact hc
  apply L.isometry.tendsto_nhds_iff.mpr
  change Filter.Tendsto (fun s : Finset ℕ =>
    L (∑ k ∈ s, chebyshevCoeff f k * (T 𝕜 (k : ℤ)).eval (x : 𝕜))) _ _
  change Filter.Tendsto (fun s : Finset ℕ =>
    ∑ k ∈ s, L (chebyshevCoeff f k * (T 𝕜 (k : ℤ)).eval (x : 𝕜))) _ _ at hm
  convert hm using 1
  funext s
  exact map_sum L.toLinearMap _ _

end NLAlib
