/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Chebyshev growth outside the unit interval

Radical formulas and lower bounds for Mathlib's first-kind Chebyshev polynomials.
These are upstream candidates in `Polynomial.Chebyshev`.

## Main results

* `Polynomial.Chebyshev.eval_T_real_eq_of_one_le`: the radical closed form.
* `Polynomial.Chebyshev.pow_div_two_le_eval_T_real`: exponential lower growth.
* `Polynomial.Chebyshev.sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real`:
  the square-root condition-ratio lower bound.
-/

@[expose] public section

namespace Polynomial.Chebyshev

open Real

/-- For $x\ge1$, the radical closed form is
$$T_q(x)=\frac{(x+\sqrt{x^2-1})^q+(x-\sqrt{x^2-1})^q}{2}.$$
[Saad2003, §6.11.1, Eq. (6.111)], with the reciprocal term rewritten algebraically.

Result: chebyshev-growth
-/
theorem eval_T_real_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) (q : ℕ) :
    (T ℝ (q : ℤ)).eval x =
      ((x + Real.sqrt (x ^ 2 - 1)) ^ q + (x - Real.sqrt (x ^ 2 - 1)) ^ q) / 2 := by
  have hs : 0 < x + √(x ^ 2 - 1) := by positivity
  have h := T_real_cosh (arcosh x) (q : ℤ)
  rw [cosh_arcosh hx] at h
  rw [h, arcosh, ← add_sqrt_self_sq_sub_one_inv hx, Int.cast_natCast, ← Real.log_pow,
    cosh_log (pow_pos hs q), inv_pow]

/-- For $x\ge1$, the Chebyshev polynomial satisfies
$$(x+\sqrt{x^2-1})^q/2\le T_q(x).$$
[Saad2003, proof of Theorem 6.29, Eqs. (6.124)–(6.128)].
-/
theorem pow_div_two_le_eval_T_real {x : ℝ} (hx : 1 ≤ x) (q : ℕ) :
    (x + Real.sqrt (x ^ 2 - 1)) ^ q / 2 ≤ (T ℝ (q : ℤ)).eval x := by
  rw [eval_T_real_eq_of_one_le hx]
  have hs : 0 ≤ x - √(x ^ 2 - 1) := by
    rw [← add_sqrt_self_sq_sub_one_inv hx]
    positivity
  have := pow_nonneg hs q
  linarith

/-- For $0<a<b$, the condition-ratio form of Chebyshev growth is
$$\frac12\left(\frac{\sqrt b+\sqrt a}{\sqrt b-\sqrt a}\right)^q
\le T_q\left(\frac{b+a}{b-a}\right).$$
[Saad2003, proof of Theorem 6.29, Eqs. (6.124)–(6.128)].
-/
theorem sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (q : ℕ) :
    ((Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a)) ^ q / 2 ≤
      (T ℝ (q : ℤ)).eval ((b + a) / (b - a)) := by
  have key : ∀ s t : ℝ, 0 < s → s < t →
      (t ^ 2 + s ^ 2) / (t ^ 2 - s ^ 2) +
        √(((t ^ 2 + s ^ 2) / (t ^ 2 - s ^ 2)) ^ 2 - 1) = (t + s) / (t - s) := by
    intro s t hs hst
    have hd : 0 < t ^ 2 - s ^ 2 := by nlinarith
    have hts : 0 < t - s := by linarith
    have hsq : ((t ^ 2 + s ^ 2) / (t ^ 2 - s ^ 2)) ^ 2 - 1 =
        (2 * t * s / (t ^ 2 - s ^ 2)) ^ 2 := by
      field_simp
      ring
    have ht : 0 < t := by linarith
    rw [hsq, Real.sqrt_sq (div_nonneg (by positivity) hd.le)]
    field_simp
    ring
  have h := key (√a) (√b) (Real.sqrt_pos.2 ha) (Real.sqrt_lt_sqrt ha.le hab)
  rw [Real.sq_sqrt ha.le, Real.sq_sqrt (by linarith)] at h
  rw [← h]
  exact pow_div_two_le_eval_T_real (by rw [le_div_iff₀ (by linarith)]; linarith) q

end Polynomial.Chebyshev
