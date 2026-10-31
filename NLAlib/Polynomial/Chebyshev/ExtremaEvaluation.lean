/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Chebyshev.Residual
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Evaluation off an interval from the Chebyshev extrema

A real polynomial of degree at most $q$ is controlled at zero by its values at the $q+1$
Chebyshev extrema of a positive interval $[a, a']$. The constant is the squared Chebyshev value
$T_q\bigl((a'+a)/(a'-a)\bigr)^2$, which stays below four once $a'/a \ge 4(q+1)^2$.

## Main results

* `NLAlib.eval_zero_sq_le_eval_T_real_sq_mul_sum_eval_chebyshevExtremum_sq`: the extrapolation
  bound from the signed dual weights.
* `NLAlib.eval_T_real_le_two`: the Chebyshev value is at most two on a long interval.
-/

@[expose] public section

open Polynomial Polynomial.Chebyshev

namespace NLAlib

/-- Chebyshev extrapolation to zero: for $0 < a < a'$ and every real $p$ with
$\deg p \le q$,
$$p(0)^2 \le T_q\Bigl(\frac{a'+a}{a'-a}\Bigr)^2 \sum_{k=0}^q p(\xi_k)^2 \,,$$
with $\xi_k$ the Chebyshev extrema of $[a, a']$ (`chebyshevExtremum`). The proof writes $p(0)$
with the signed dual weights and applies Cauchy–Schwarz. -/
theorem eval_zero_sq_le_eval_T_real_sq_mul_sum_eval_chebyshevExtremum_sq {a a' : ℝ}
    (ha : 0 < a) (haa : a < a') {q : ℕ} {p : ℝ[X]} (hp : p.degree ≤ q) :
    p.eval 0 ^ 2 ≤ (T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)) ^ 2 *
      ∑ k : Fin (q + 1), p.eval (chebyshevExtremum a a' q k) ^ 2 := by
  set ω := chebyshevWeight a a' q
  set u := fun k : Fin (q + 1) => |p.eval (chebyshevExtremum a a' q k)|
  have hω : ∀ k, 0 < ω k := chebyshevWeight_pos ha haa q
  have hW : ∑ k, ω k = (T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)) := sum_chebyshevWeight ha haa q
  have h0 : |p.eval 0| ≤ ∑ k, ω k * u k := by
    have h := sum_neg_one_pow_mul_chebyshevWeight_mul_eval (𝕜 := ℝ) ha haa hp
    simp only [RCLike.ofReal_real_eq_id, id] at h
    rw [← h]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun k _ => ?_)
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (hω k)]
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun k => ω k * u k) (f := ω) (g := fun k => ω k * u k ^ 2)
    (fun k _ => (hω k).le) (fun k _ => mul_nonneg (hω k).le (sq_nonneg _))
    (fun k _ => by ring_nf; rfl)
  have hg : ∑ k, ω k * u k ^ 2 ≤ (∑ k, ω k) * ∑ k, u k ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact Finset.single_le_sum (fun j _ => (hω j).le) (Finset.mem_univ k)
  have hu : ∑ k, u k ^ 2 = ∑ k : Fin (q + 1), p.eval (chebyshevExtremum a a' q k) ^ 2 :=
    Finset.sum_congr rfl fun k _ => sq_abs _
  have hS : 0 ≤ ∑ k, ω k := Finset.sum_nonneg fun k _ => (hω k).le
  have hsq : p.eval 0 ^ 2 ≤ (∑ k, ω k * u k) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  rw [← hW, ← hu]
  calc p.eval 0 ^ 2 ≤ (∑ k, ω k * u k) ^ 2 := hsq
    _ ≤ (∑ k, ω k) * ∑ k, ω k * u k ^ 2 := hCS
    _ ≤ (∑ k, ω k) * ((∑ k, ω k) * ∑ k, u k ^ 2) := mul_le_mul_of_nonneg_left hg hS
    _ = (∑ k, ω k) ^ 2 * ∑ k, u k ^ 2 := by ring

/-- The Chebyshev value on a long interval is at most two: for $a > 0$ and
$a' \ge 4(q+1)^2a$,
$$T_q\Bigl(\frac{a'+a}{a'-a}\Bigr) \le 2 \,.$$
With $\rho = (\sqrt{a'/a}-1)/(\sqrt{a'/a}+1)$ and $x = \rho^q$, the value is $(1+x^2)/(2x)$, and
$x \ge e^{-2q/(\sqrt{a'/a}-1)} \ge e^{-1} > 1/3$. -/
theorem eval_T_real_le_two {a a' : ℝ} (ha : 0 < a) (q : ℕ)
    (h : (2 * ((q : ℝ) + 1)) ^ 2 * a ≤ a') :
    (T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)) ≤ 2 := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h4 : 4 * a ≤ (2 * ((q : ℝ) + 1)) ^ 2 * a :=
    mul_le_mul_of_nonneg_right (by nlinarith) ha.le
  have haa : a < a' := by linarith
  have hT := inv_eval_T_real_eq_two_mul_pow_div q ha haa
  set s := Real.sqrt (a' / a) with hs_def
  have hs : 2 * ((q : ℝ) + 1) ≤ s := by
    rw [hs_def]
    refine Real.le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ ha]
    exact h
  have hs1 : 0 < s - 1 := by linarith
  set ρ := (s - 1) / (s + 1) with hρ_def
  have hρ0 : 0 < ρ := div_pos hs1 (by linarith)
  have hρ1 : ρ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hρexp : Real.exp (-(2 / (s - 1))) ≤ ρ := by
    have h2 : (s + 1) / (s - 1) = 2 / (s - 1) + 1 := by
      field_simp
      ring
    have h3 : (s + 1) / (s - 1) ≤ Real.exp (2 / (s - 1)) := by
      rw [h2]
      exact Real.add_one_le_exp _
    rw [Real.exp_neg, hρ_def, show (s - 1) / (s + 1) = ((s + 1) / (s - 1))⁻¹ by rw [inv_div]]
    exact inv_anti₀ (div_pos (by linarith) hs1) h3
  set x := ρ ^ q with hx_def
  have hx0 : 0 < x := pow_pos hρ0 q
  have hx1 : x ≤ 1 := pow_le_one₀ hρ0.le hρ1
  have hxexp : Real.exp (-1) ≤ x := by
    have hle : -1 ≤ -(2 / (s - 1)) * q := by
      have : 2 / (s - 1) * q ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_one hs1]
        linarith
      linarith
    calc Real.exp (-1) ≤ Real.exp (-(2 / (s - 1)) * q) := Real.exp_le_exp.mpr hle
      _ = Real.exp (-(2 / (s - 1))) ^ q := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ x := pow_le_pow_left₀ (Real.exp_nonneg _) hρexp q
  have hthird : 1 / 3 ≤ x := by
    refine le_trans ?_ hxexp
    rw [Real.exp_neg, one_div]
    refine inv_anti₀ (Real.exp_pos 1) ?_
    linarith [Real.exp_one_lt_d9]
  have hx2 : x ^ 2 = ρ ^ (2 * q) := by rw [hx_def, ← pow_mul, mul_comm]
  rw [← hx2] at hT
  have hTpos : 0 < (T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)) := by
    have := inv_pos.mp (hT ▸ (by positivity : (0 : ℝ) < 2 * x / (1 + x ^ 2)))
    exact this
  have hval : (T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)) = (1 + x ^ 2) / (2 * x) := by
    rw [← inv_inv ((T ℝ (q : ℤ)).eval ((a' + a) / (a' - a))), hT, inv_div]
  rw [hval, div_le_iff₀ (by positivity)]
  nlinarith

end NLAlib
