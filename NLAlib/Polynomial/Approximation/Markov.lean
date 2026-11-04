/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Polynomial derivative and Lipschitz bounds

A polynomial bounded on an interval has derivative and Lipschitz bounds quadratic in its
degree. Mathlib's Chebyshev endpoint extremal theorem supplies the endpoint estimate;
restriction to a half-length subinterval gives a factor two relaxation of Markov's inequality.

## Main results

* `NLAlib.abs_derivative_eval_le_of_forall_abs_eval_le`: an interval derivative estimate.
* `NLAlib.abs_eval_sub_eval_le_of_forall_abs_eval_le`: the corresponding Lipschitz estimate.
-/

@[expose] public section

open Polynomial Set

namespace NLAlib

/-- Degree factor in the interval derivative and Lipschitz estimates,
currently <!-- value polynomialDerivativeFactor n -->
$$4n^2\,.$$
The resulting estimate is a factor two relaxation of Markov's inequality, derived from
Mathlib's Chebyshev endpoint extremal theorem. No printed source for this relaxation. -/
irreducible_def polynomialDerivativeFactor (n : ℕ) : ℝ := 4 * (n : ℝ) ^ 2

/-- The polynomial derivative degree factor is nonnegative for every degree. -/
theorem polynomialDerivativeFactor_nonneg (n : ℕ) : 0 ≤ polynomialDerivativeFactor n := by
  rw [polynomialDerivativeFactor_def]
  positivity

/-- The derivative degree factor is monotone in the allowed degree. -/
theorem polynomialDerivativeFactor_mono : Monotone polynomialDerivativeFactor := by
  intro m n h
  rw [polynomialDerivativeFactor_def, polynomialDerivativeFactor_def]
  gcongr

/-- The derivative degree factor is at most
the value <!-- value polynomialDerivativeFactor n -->$4n^2$. -/
theorem polynomialDerivativeFactor_le (n : ℕ) :
    polynomialDerivativeFactor n ≤ 4 * (n : ℝ) ^ 2 := by
  rw [polynomialDerivativeFactor_def]

private theorem abs_derivative_eval_one_le {p : ℝ[X]} {n : ℕ}
    (hp : p.degree ≤ n) (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    |p.derivative.eval 1| ≤ (n : ℝ) ^ 2 := by
  have hu := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (k := 1) (x := 1) le_rfl hp hbound
  have hl := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (k := 1) (x := 1) (P := -p) le_rfl (by simpa using hp)
      (by simpa only [eval_neg, abs_neg] using hbound)
  simp only [Function.iterate_one, Polynomial.Chebyshev.derivative_T_eval_one,
    Int.cast_natCast, derivative_neg, eval_neg] at hu hl
  exact abs_le.mpr ⟨by linarith, hu⟩

private theorem abs_derivative_eval_one_le_mul {p : ℝ[X]} {n : ℕ} {M : ℝ}
    (hp : p.degree ≤ n) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    |p.derivative.eval 1| ≤ (n : ℝ) ^ 2 * M := by
  rcases hM.eq_or_lt with hM | hM
  · have hp0 : p = 0 := p.eq_zero_of_infinite_isRoot <|
      (Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono fun x hx => by
        exact abs_nonpos_iff.mp (hM ▸ hbound x hx)
    simp [hp0, ← hM]
  · have hq := abs_derivative_eval_one_le
      ((degree_smul_le M⁻¹ p).trans hp) (fun x hx => show
        |(M⁻¹ • p).eval x| ≤ 1 by
          simpa only [eval_smul, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hM,
            inv_mul_le_iff₀ hM, mul_one] using hbound x hx)
    simp only [derivative_smul, eval_smul, smul_eq_mul, abs_mul, abs_inv,
      abs_of_pos hM] at hq
    exact (inv_mul_le_iff₀ hM).mp hq |>.trans_eq (mul_comm M _)

private theorem abs_mul_derivative_affine_le {p : ℝ[X]} {n : ℕ} {s c M : ℝ}
    (hp : p.degree ≤ n) (hM : 0 ≤ M)
    (hbound : ∀ t ∈ Icc (-1 : ℝ) 1, |p.eval (s * t + c)| ≤ M) :
    |s| * |p.derivative.eval (s + c)| ≤ (n : ℝ) ^ 2 * M := by
  let q := p.comp (C s * X + C c)
  have hdeg : q.degree ≤ n := by
    apply degree_le_of_natDegree_le
    exact natDegree_comp_le.trans <|
      (Nat.mul_le_mul (natDegree_le_of_degree_le hp)
        (show (C s * X + C c).natDegree ≤ 1 by compute_degree!)).trans_eq (mul_one n)
  have hb : ∀ t ∈ Icc (-1 : ℝ) 1, |q.eval t| ≤ M := by
    simpa only [q, eval_comp, eval_add, eval_mul, eval_C, eval_X] using hbound
  have h := abs_derivative_eval_one_le_mul hdeg hM hb
  simpa [q, derivative_comp, abs_mul] using h

/-- Interval derivative bound for a bounded polynomial: if $a<b$, $M\ge0$ and a real
polynomial $p$ of degree at most $n$ satisfies $\lvert p(x)\rvert\le M$ on $[a,b]$, then
the bound is <!-- value polynomialDerivativeFactor n -->
$$\lvert p'(x)\rvert\le \frac{4n^2M}{b-a},\qquad x\in[a,b].$$
A factor two relaxation of Markov's inequality, obtained from Mathlib's Chebyshev endpoint
extremal theorem. No printed source for this relaxation. -/
theorem abs_derivative_eval_le_of_forall_abs_eval_le {p : ℝ[X]} {n : ℕ} {a b M x : ℝ}
    (hp : p.degree ≤ n) (hab : a < b) (hM : 0 ≤ M)
    (hbound : ∀ t ∈ Icc a b, |p.eval t| ≤ M) (hx : x ∈ Icc a b) :
    |p.derivative.eval x| ≤ polynomialDerivativeFactor n * M / (b - a) := by
  rw [le_div_iff₀ (sub_pos.mpr hab)]
  rw [polynomialDerivativeFactor_def]
  by_cases hm : (a + b) / 2 ≤ x
  · have hs : 0 ≤ (x - a) / 2 := by linarith [hx.1]
    have h := abs_mul_derivative_affine_le (s := (x - a) / 2)
      (c := (x + a) / 2) hp hM (fun t ht => hbound _ ⟨by nlinarith [ht.1],
        by nlinarith [ht.2, hx.2]⟩)
    rw [abs_of_nonneg hs, show (x - a) / 2 + (x + a) / 2 = x by ring] at h
    nlinarith [abs_nonneg (p.derivative.eval x)]
  · have hs : (x - b) / 2 ≤ 0 := by linarith [hx.2]
    have h := abs_mul_derivative_affine_le (s := (x - b) / 2)
      (c := (x + b) / 2) hp hM (fun t ht => hbound _ ⟨by nlinarith [ht.2, hx.1],
        by nlinarith [ht.1]⟩)
    rw [abs_of_nonpos hs, show (x - b) / 2 + (x + b) / 2 = x by ring] at h
    nlinarith [abs_nonneg (p.derivative.eval x)]

/-- Polynomial Lipschitz estimate on an interval: if $a<b$, $M\ge0$ and $p$ has degree
at most $n$ and absolute value at most $M$ on $[a,b]$, then for $x,y\in[a,b]$,
the bound is <!-- value polynomialDerivativeFactor n -->
$$\lvert p(x)-p(y)\rvert\le\frac{4n^2M}{b-a}\lvert x-y\rvert.$$
The mean value consequence of a factor two relaxation of Markov's inequality.
No printed source for this relaxation. -/
theorem abs_eval_sub_eval_le_of_forall_abs_eval_le {p : ℝ[X]} {n : ℕ} {a b M x y : ℝ}
    (hp : p.degree ≤ n) (hab : a < b) (hM : 0 ≤ M)
    (hbound : ∀ t ∈ Icc a b, |p.eval t| ≤ M) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |p.eval x - p.eval y| ≤ polynomialDerivativeFactor n * M / (b - a) * |x - y| := by
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => p.differentiableAt) (fun t ht => show ‖deriv p.eval t‖ ≤ _ by
      simpa only [Polynomial.deriv, Real.norm_eq_abs] using
        abs_derivative_eval_le_of_forall_abs_eval_le hp hab hM hbound ht) hy hx
  simpa only [Real.norm_eq_abs] using h

end NLAlib
