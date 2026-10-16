/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Jackson damping and its positive periodic kernel

Sine autocorrelations give the Jackson damping coefficients. The full kernel has constant
coefficient one and integral $2\pi$, matching the library's unhalved Chebyshev constant term.
[ChenTrogdonUbaru2022, Appendix C, Lemmas 44–45], specifically the first arXiv version.

## Main results

* `jacksonDamping_eq_closed_form`: the classical closed form of the damping factors.
* `jacksonDamping_nonneg`, `jacksonDamping_le_one`: damping factors lie in $[0,1]$.
* `integral_jacksonKernel`, `integral_cos_mul_jacksonKernel`: mass and first cosine moment.
* `jacksonKernel_eq_norm_sq`, `jacksonKernel_nonneg`: autocorrelation identity and positivity.
-/

@[expose] public section

open Finset Real

namespace NLAlib

/-- Zero-padded Jackson damping from the normalized finite sine-vector autocorrelation.
For indices $k\le N$ this is the classical Jackson factor; for $k>N$ it is zero. The
normalization includes $N=0$. [ChenTrogdonUbaru2022, Appendix C, Lemma 45]. -/
noncomputable def jacksonDamping (N k : ℕ) : ℝ :=
  if k ≤ N then
    (2 / (N + 2 : ℝ)) * ∑ j ∈ Finset.range (N + 1 - k),
      Real.sin (((j + 1 : ℕ) : ℝ) * (Real.pi / (N + 2))) *
      Real.sin (((j + k + 1 : ℕ) : ℝ) * (Real.pi / (N + 2)))
  else 0

/-- The full Jackson kernel $K_N(\theta)=1+2\sum_{k=1}^N\rho_k\cos(k\theta)$.
It is twice the kernel with constant term $1/2$ used in [ChenTrogdonUbaru2022, Appendix C].
This convention normalizes integration by $1/(2\pi)$ and keeps the constant coefficient full. -/
noncomputable def jacksonKernel (N : ℕ) (θ : ℝ) : ℝ :=
  1 + 2 * ∑ k ∈ Finset.range N,
    jacksonDamping N (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ)

private lemma phase_mul (N : ℕ) : (N + 2 : ℝ) * (Real.pi / (N + 2)) = Real.pi := by
  field_simp

private lemma phase_sin_pos (N : ℕ) : 0 < Real.sin (Real.pi / (N + 2)) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · apply div_lt_self Real.pi_pos
    have := Nat.cast_nonneg (α := ℝ) N
    linarith

private lemma cosine_sum {N k : ℕ} (hk : k ≤ N) :
    Real.sin (Real.pi / (N + 2)) *
      (∑ j ∈ range (N + 1 - k),
        Real.cos (((2 * j + k + 2 : ℕ) : ℝ) * (Real.pi / (N + 2)))) =
      -Real.sin (((k + 1 : ℕ) : ℝ) * (Real.pi / (N + 2))) := by
  let a := Real.pi / (N + 2)
  have hm : ((N + 1 - k : ℕ) : ℝ) + k + 1 = N + 2 := by
    have h : N + 1 - k + k = N + 1 := Nat.sub_add_cancel (by omega)
    exact_mod_cast (by omega : N + 1 - k + k + 1 = N + 2)
  have h := Real.sin_mul_sum_cos (N + 1 - k) (2 * a) (((k : ℝ) + 2) * a)
  have hp : (N + 2 : ℝ) * a = Real.pi := phase_mul N
  have harg : ((N + 1 - k : ℕ) : ℝ) * (2 * a) / 2 = Real.pi - (k + 1) * a := by
    calc
      _ = (((N + 1 - k : ℕ) : ℝ) + k + 1) * a - (k + 1) * a := by ring
      _ = _ := by rw [hm, hp]
  have harg' : (((N + 1 - k : ℕ) : ℝ) - 1) * (2 * a) / 2 + ((k : ℝ) + 2) * a =
      Real.pi := by
    calc
      _ = (((N + 1 - k : ℕ) : ℝ) + k + 1) * a := by ring
      _ = _ := by rw [hm, hp]
  rw [show 2 * a / 2 = a by ring, harg, harg', Real.cos_pi, Real.sin_pi_sub, mul_neg_one] at h
  convert h using 1
  · congr 1
    apply sum_congr rfl
    intro j hj
    congr 1
    push_cast
    ring
  · dsimp [a]
    push_cast
    rfl

private lemma sine_correlation {N k : ℕ} (hk : k ≤ N) :
    2 * (∑ j ∈ range (N + 1 - k),
      Real.sin (((j + 1 : ℕ) : ℝ) * (Real.pi / (N + 2))) *
      Real.sin (((j + k + 1 : ℕ) : ℝ) * (Real.pi / (N + 2)))) =
      ((N : ℝ) - k + 2) * Real.cos ((k : ℝ) * (Real.pi / (N + 2))) +
        Real.sin ((k : ℝ) * (Real.pi / (N + 2))) *
          (Real.cos (Real.pi / (N + 2)) / Real.sin (Real.pi / (N + 2))) := by
  let a := Real.pi / (N + 2)
  have hs := cosine_sum hk
  have hm : ((N + 1 - k : ℕ) : ℝ) = (N : ℝ) + 1 - k := by
    rw [Nat.cast_sub (by omega : k ≤ N + 1)]
    push_cast
    rfl
  have hprod : ∀ j : ℕ,
      2 * (Real.sin (((j + 1 : ℕ) : ℝ) * a) * Real.sin (((j + k + 1 : ℕ) : ℝ) * a)) =
        Real.cos ((k : ℝ) * a) - Real.cos (((2 * j + k + 2 : ℕ) : ℝ) * a) := by
    intro j
    have h₁ := Real.cos_sub (((j + 1 : ℕ) : ℝ) * a) (((j + k + 1 : ℕ) : ℝ) * a)
    have h₂ := Real.cos_add (((j + 1 : ℕ) : ℝ) * a) (((j + k + 1 : ℕ) : ℝ) * a)
    have he₁ : (((j + 1 : ℕ) : ℝ) * a) - (((j + k + 1 : ℕ) : ℝ) * a) = -(k * a) := by
      push_cast
      ring
    have he₂ : (((j + 1 : ℕ) : ℝ) * a) + (((j + k + 1 : ℕ) : ℝ) * a) =
        ((2 * j + k + 2 : ℕ) : ℝ) * a := by push_cast; ring
    rw [he₁, Real.cos_neg] at h₁
    rw [he₂] at h₂
    linarith
  rw [Finset.mul_sum]
  dsimp only [a] at hprod
  simp_rw [hprod]
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, hm]
  have ha : Real.sin a ≠ 0 := (phase_sin_pos N).ne'
  have hsa : Real.sin a * (∑ j ∈ range (N + 1 - k),
      Real.cos (((2 * j + k + 2 : ℕ) : ℝ) * a)) = -Real.sin ((k + 1) * a) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hs
  have hsum : (∑ j ∈ range (N + 1 - k),
      Real.cos (((2 * j + k + 2 : ℕ) : ℝ) * a)) =
      -Real.sin ((k + 1) * a) / Real.sin a :=
    (eq_div_iff ha).mpr (by nlinarith [hsa])
  have hsin : Real.sin ((k + 1) * a) =
      Real.sin (k * a) * Real.cos a + Real.cos (k * a) * Real.sin a := by
    rw [add_mul, one_mul, Real.sin_add]
  dsimp only [a] at hsum hsin
  rw [hsum, hsin]
  field_simp [(phase_sin_pos N).ne']
  ring

/-- Beyond the degree cutoff, the damping coefficient is zero by its total definition. -/
theorem jacksonDamping_of_lt {N k : ℕ} (hNk : N < k) : jacksonDamping N k = 0 := by
  exact if_neg (not_le.mpr hNk)

/-- The sine-autocorrelation definition agrees with the standard trigonometric Jackson formula
at every index within the cutoff. [ChenTrogdonUbaru2022, Appendix C, Lemma 45]. -/
theorem jacksonDamping_eq_closed_form {N k : ℕ} (hk : k ≤ N) :
    jacksonDamping N k =
      (((N : ℝ) - k + 2) * Real.cos ((k : ℝ) * (Real.pi / (N + 2))) +
        Real.sin ((k : ℝ) * (Real.pi / (N + 2))) *
          (Real.cos (Real.pi / (N + 2)) / Real.sin (Real.pi / (N + 2)))) / (N + 2) := by
  rw [jacksonDamping, if_pos hk, div_mul_eq_mul_div, sine_correlation hk]

/-- Jackson damping preserves the full constant coefficient, including degree zero. -/
theorem jacksonDamping_zero (N : ℕ) : jacksonDamping N 0 = 1 := by
  rw [jacksonDamping_eq_closed_form (Nat.zero_le N)]
  simp only [Nat.cast_zero, sub_zero, zero_mul, Real.cos_zero, mul_one, Real.sin_zero,
    zero_mul, add_zero]
  exact div_self (by positivity)

/-- Every zero-padded damping coefficient is nonnegative. -/
theorem jacksonDamping_nonneg (N k : ℕ) : 0 ≤ jacksonDamping N k := by
  unfold jacksonDamping
  split_ifs with hk
  · apply mul_nonneg (by positivity)
    apply sum_nonneg
    intro j hj
    have hjk : j + k + 1 ≤ N + 1 := by have := mem_range.mp hj; omega
    have hj' : j + 1 ≤ N + 1 := by omega
    have hsin (i : ℕ) (hi : i ≤ N + 1) : 0 ≤ Real.sin ((i : ℝ) * (Real.pi / (N + 2))) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · positivity
      · calc
          _ ≤ (N + 2 : ℝ) * (Real.pi / (N + 2)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : i ≤ N + 2)) (by positivity)
          _ = Real.pi := phase_mul N
    exact mul_nonneg (hsin _ hj') (hsin _ hjk)
  · exact le_rfl

/-- The first damping coefficient is the cosine of the Jackson phase, including $N=0$. -/
theorem jacksonDamping_one (N : ℕ) :
    jacksonDamping N 1 = Real.cos (Real.pi / (N + 2)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [jacksonDamping_of_lt (by omega : 0 < 1)]
    norm_num
  · rw [jacksonDamping_eq_closed_form hN]
    have hs : Real.sin (Real.pi / (N + 2)) ≠ 0 := (phase_sin_pos N).ne'
    push_cast
    field_simp
    ring

private lemma sine_energy (N : ℕ) :
    (∑ j ∈ range (N + 1), Real.sin (((j + 1 : ℕ) : ℝ) *
      (Real.pi / (N + 2))) ^ 2) = (N + 2 : ℝ) / 2 := by
  have h := jacksonDamping_zero N
  simp only [jacksonDamping, Nat.zero_le, ↓reduceIte, Nat.sub_zero, add_zero] at h
  have hN : (N + 2 : ℝ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq hN] at h
  simpa only [pow_two] using (show (∑ j ∈ range (N + 1),
    Real.sin (((j + 1 : ℕ) : ℝ) * (Real.pi / (N + 2))) *
      Real.sin (((j + 1 : ℕ) : ℝ) * (Real.pi / (N + 2)))) = (N + 2 : ℝ) / 2 by linarith)

private lemma sum_shift_le (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (k m : ℕ) :
    (∑ j ∈ range m, f (j + k)) ≤ ∑ j ∈ range (k + m), f j := by
  have h := Finset.sum_range_add f k m
  have hp : 0 ≤ ∑ j ∈ range k, f j := sum_nonneg (fun j _ => hf j)
  have he : (∑ j ∈ range (k + m), f j) =
      (∑ j ∈ range k, f j) + ∑ j ∈ range m, f (j + k) := by
    simpa only [add_comm] using h
  linarith

/-- Every zero-padded damping coefficient is at most one. This follows from the finite sine
energy and the correlation inequality; no sign or degree assumption is omitted. -/
theorem jacksonDamping_le_one (N k : ℕ) : jacksonDamping N k ≤ 1 := by
  unfold jacksonDamping
  split_ifs with hk
  · let a (j : ℕ) := Real.sin (((j + 1 : ℕ) : ℝ) * (Real.pi / (N + 2)))
    have hleft : (∑ j ∈ range (N + 1 - k), a j ^ 2) ≤ (N + 2 : ℝ) / 2 := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega : N + 1 - k ≤ N + 1))
        (fun j _ _ => sq_nonneg (a j))).trans_eq ?_
      exact sine_energy N
    have hright : (∑ j ∈ range (N + 1 - k), a (j + k) ^ 2) ≤ (N + 2 : ℝ) / 2 := by
      have h := sum_shift_le (fun j => a j ^ 2) (fun j => sq_nonneg _) k (N + 1 - k)
      rw [show k + (N + 1 - k) = N + 1 by omega] at h
      exact h.trans_eq (sine_energy N)
    have hprod : 2 * (∑ j ∈ range (N + 1 - k), a j * a (j + k)) ≤
        (N + 2 : ℝ) := by
      have hsum := Finset.sum_le_sum (s := range (N + 1 - k))
        (f := fun j => 2 * (a j * a (j + k)))
        (g := fun j => a j ^ 2 + a (j + k) ^ 2)
        (fun j _ => by nlinarith [sq_nonneg (a j - a (j + k))])
      rw [← Finset.mul_sum, sum_add_distrib] at hsum
      linarith
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]
    exact hprod
  · norm_num

/-- The Jackson kernel is $2\pi$-periodic. -/
theorem jacksonKernel_periodic (N : ℕ) :
    Function.Periodic (jacksonKernel N) (2 * Real.pi) := by
  intro θ
  unfold jacksonKernel
  congr 2
  apply sum_congr rfl
  intro k hk
  rw [mul_add, Real.cos_add_nat_mul_two_pi]

private lemma integral_cos_frequency {k : ℕ} (hk : 0 < k) :
    (∫ θ in (-Real.pi)..Real.pi, Real.cos ((k : ℝ) * θ)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left _ (Nat.cast_ne_zero.mpr hk.ne'), integral_cos]
  simp only [mul_neg, Real.sin_neg, Real.sin_nat_mul_pi, neg_zero, sub_zero, smul_zero]

private lemma integral_cos_product {k : ℕ} (hk : 0 < k) :
    (∫ θ in (-Real.pi)..Real.pi, Real.cos θ * Real.cos ((k : ℝ) * θ)) =
      if k = 1 then Real.pi else 0 := by
  rcases eq_or_ne k 1 with rfl | hk1
  · simp only [Nat.cast_one, one_mul, ↓reduceIte, ← pow_two]
    rw [integral_cos_sq]
    simp only [Real.sin_pi, Real.cos_pi, Real.cos_neg, Real.sin_neg, neg_zero,
      mul_zero, sub_zero, sub_neg_eq_add]
    ring
  · have hm : 0 < k - 1 := by omega
    have hp : ∀ θ : ℝ, 2 * (Real.cos θ * Real.cos ((k : ℝ) * θ)) =
        Real.cos (((k + 1 : ℕ) : ℝ) * θ) + Real.cos (((k - 1 : ℕ) : ℝ) * θ) := by
      intro θ
      have ha := Real.cos_add ((k : ℝ) * θ) θ
      have hb := Real.cos_sub ((k : ℝ) * θ) θ
      have hplus : ((k + 1 : ℕ) : ℝ) * θ = (k : ℝ) * θ + θ := by push_cast; ring
      have hminus : ((k - 1 : ℕ) : ℝ) * θ = (k : ℝ) * θ - θ := by
        rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
        ring
      rw [hplus, hminus]
      nlinarith [ha, hb]
    have he : 2 * (∫ θ in (-Real.pi)..Real.pi, Real.cos θ * Real.cos ((k : ℝ) * θ)) = 0 := by
      rw [← intervalIntegral.integral_const_mul]
      simp_rw [hp]
      rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
        integral_cos_frequency (Nat.succ_pos k), integral_cos_frequency hm, add_zero]
    rw [if_neg hk1]
    linarith

/-- The full kernel has integral $2\pi$, so division by $2\pi$ gives unit mass. -/
theorem integral_jacksonKernel (N : ℕ) :
    (∫ θ in (-Real.pi)..Real.pi, jacksonKernel N θ) = 2 * Real.pi := by
  unfold jacksonKernel
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum
      (fun k _ => by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const_mul, integral_cos_frequency (Nat.succ_pos _),
    mul_zero, sum_const_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one,
    sub_neg_eq_add, add_zero]
  ring

/-- The first cosine moment of the full Jackson kernel is $2\pi\cos(\pi/(N+2))$.
This is the moment controlling its approximation error, including degree zero. -/
theorem integral_cos_mul_jacksonKernel (N : ℕ) :
    (∫ θ in (-Real.pi)..Real.pi, Real.cos θ * jacksonKernel N θ) =
      2 * Real.pi * Real.cos (Real.pi / (N + 2)) := by
  have he : ∀ θ : ℝ, Real.cos θ * jacksonKernel N θ = Real.cos θ +
      2 * ∑ k ∈ range N,
        jacksonDamping N (k + 1) * (Real.cos θ * Real.cos (((k + 1 : ℕ) : ℝ) * θ)) := by
    intro θ
    simp only [jacksonKernel, mul_add, Finset.mul_sum, mul_comm]
    ring_nf
  simp_rw [he]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum
      (fun k _ => by apply Continuous.intervalIntegrable; fun_prop)]
  have hz : (∫ θ in (-Real.pi)..Real.pi, Real.cos θ) = 0 := by
    simpa only [Nat.cast_one, one_mul] using integral_cos_frequency (k := 1) (by omega)
  rw [hz, zero_add]
  simp only [intervalIntegral.integral_const_mul, integral_cos_product (Nat.succ_pos _)]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [range_zero, sum_empty, mul_zero, Nat.cast_zero, zero_add, Real.cos_pi_div_two]
  · rw [Finset.sum_eq_single 0]
    · simp only [zero_add, ↓reduceIte]
      rw [jacksonDamping_one]
      ring
    · intro k hk hk0
      rw [if_neg (by omega : k + 1 ≠ 1), mul_zero]
    · intro h
      exact (h (mem_range.mpr hN)).elim

private lemma triangle_by_lag (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range i, F j i) =
      ∑ k ∈ range N, ∑ j ∈ range (N - k), F j (j + k + 1) := by
  have h := Finset.sum_range_diag_flip N (fun k j => F j (j + k + 1))
  rw [Finset.sum_range_succ']
  simp only [range_zero, sum_empty, add_zero]
  calc
    _ = ∑ i ∈ range N, ∑ j ∈ range (i + 1), F (i - j) (i + 1) := by
      apply sum_congr rfl
      intro i hi
      simpa only [Nat.add_sub_cancel] using
        (Finset.sum_range_reflect (fun j => F j (i + 1)) (i + 1)).symm
    _ = _ := by
      convert h using 1
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      have hj' : j ≤ i := Nat.le_of_lt_succ (mem_range.mp hj)
      rw [Nat.sub_add_cancel hj']

private lemma norm_add_square (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * (starRingEnd ℂ) w).re := by
  simpa only [Complex.sq_norm] using Complex.normSq_add z w

private lemma norm_sum_square (z : ℕ → ℂ) (n : ℕ) :
    ‖∑ i ∈ range n, z i‖ ^ 2 = (∑ i ∈ range n, ‖z i‖ ^ 2) +
      2 * ∑ i ∈ range n, ∑ j ∈ range i, (z j * (starRingEnd ℂ) (z i)).re := by
  induction n with
  | zero => simp only [range_zero, sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, add_zero]
  | succ n ih =>
    rw [sum_range_succ, norm_add_square, ih, sum_range_succ, sum_range_succ]
    simp only [sum_mul, Complex.re_sum]
    ring

private lemma phase_product (a b x y : ℝ) :
    (((a : ℂ) * Complex.exp ((x : ℂ) * Complex.I)) *
      (starRingEnd ℂ) ((b : ℂ) * Complex.exp ((y : ℂ) * Complex.I))).re =
      a * b * Real.cos (y - x) := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.conj_re,
    Complex.conj_im, zero_mul, sub_zero, Real.cos_sub]
  ring

/-- The full Jackson kernel is a normalized squared modulus of a finite sine Fourier sum.
This is the positivity identity in [ChenTrogdonUbaru2022, Appendix C, Lemma 45], with the
kernel multiplied by two to give full constant coefficient one. -/
theorem jacksonKernel_eq_norm_sq (N : ℕ) (θ : ℝ) :
    jacksonKernel N θ = (2 / (N + 2 : ℝ)) *
      ‖∑ j ∈ Finset.range (N + 1),
        (Real.sin (((j + 1 : ℕ) : ℝ) * (Real.pi / (N + 2))) : ℂ) *
          Complex.exp ((((j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
  let a (j : ℕ) := Real.sin (((j + 1 : ℕ) : ℝ) * (Real.pi / (N + 2)))
  have hn (j : ℕ) : ‖(a j : ℂ) * Complex.exp ((((j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      a j ^ 2 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  have hp (i j : ℕ) :
      (((a j : ℂ) * Complex.exp ((((j : ℝ) * θ : ℝ) : ℂ) * Complex.I)) *
        (starRingEnd ℂ) ((a i : ℂ) * Complex.exp ((((i : ℝ) * θ : ℝ) : ℂ) * Complex.I))).re =
      a j * a i * Real.cos (((i : ℝ) - j) * θ) := by
    rw [phase_product, ← sub_mul]
  rw [norm_sum_square]
  dsimp only [a] at hn hp
  simp_rw [hn, hp]
  rw [triangle_by_lag]
  have hd (k : ℕ) (hk : k ∈ range N) :
      (2 / (N + 2 : ℝ)) *
        (∑ j ∈ range (N - k), a j * a (j + k + 1)) = jacksonDamping N (k + 1) := by
    rw [jacksonDamping, if_pos (by have := mem_range.mp hk; omega)]
    rw [show N + 1 - (k + 1) = N - k by omega]
    congr 1
  have he : (∑ j ∈ range (N + 1), a j ^ 2) = (N + 2 : ℝ) / 2 := sine_energy N
  rw [he, mul_add]
  have hconst : (2 / (N + 2 : ℝ)) * ((N + 2 : ℝ) / 2) = 1 := by field_simp
  rw [hconst]
  unfold jacksonKernel
  congr 1
  rw [mul_left_comm (2 / (N + 2 : ℝ)) 2]
  congr 1
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro k hk
  have hang (j : ℕ) : (((j + k + 1 : ℕ) : ℝ) - j) * θ = ((k + 1 : ℕ) : ℝ) * θ := by
    push_cast
    ring
  simp_rw [hang]
  dsimp only [a] at hd
  rw [← Finset.sum_mul, ← mul_assoc, hd k hk]

/-- The Jackson kernel is nonnegative for every degree and angle. -/
theorem jacksonKernel_nonneg (N : ℕ) (θ : ℝ) : 0 ≤ jacksonKernel N θ := by
  rw [jacksonKernel_eq_norm_sq]
  positivity

end NLAlib
