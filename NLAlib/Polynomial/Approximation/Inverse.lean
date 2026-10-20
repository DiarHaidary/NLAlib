/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Chebyshev.Residual
public import NLAlib.ForMathlib.Algebra.Polynomial.Div

/-!
# Polynomial approximation of the inverse function

A normalized Chebyshev residual gives a polynomial approximation of the inverse on a positive
interval, with geometric decay in its allowed degree. No matrix or Krylov assumptions are needed.

## Main results

* `NLAlib.exists_degree_lt_isUniformApproxOn_inv`: inverse approximation including degree zero.
-/

@[expose] public section

open Polynomial Real

namespace NLAlib

/-- **Polynomial approximation of the inverse.** For $0<a<b$, there is a polynomial of degree
less than $q$ such that
$$\left\lvert p(x)-x^{-1}\right\rvert\le\frac2a
\left(\frac{\sqrt b-\sqrt a}{\sqrt b+\sqrt a}\right)^q\quad(x\in[a,b]).$$
This is a scalar inverse-approximation corollary of [Saad2003, Theorem 6.25 and proof of
Theorem 6.29], obtained by factoring $1-r_q=Xp$. The `WithBot` degree includes $q=0$:
the zero polynomial has degree $\bot<0$, and error at most $1/a\le2/a$.

Result: inverse-polynomial-approx
-/
theorem exists_degree_lt_isUniformApproxOn_inv {a b : ℝ} (q : ℕ)
    (ha : 0 < a) (hab : a < b) :
    ∃ p : ℝ[X], p.degree < (q : WithBot ℕ) ∧
      Metric.IsUniformApproxOn p.eval (fun x => x⁻¹) (Set.Icc a b)
        ((2 / a) * ((Real.sqrt b - Real.sqrt a) / (Real.sqrt b + Real.sqrt a)) ^ q) := by
  obtain ⟨s, hs, hrs⟩ := exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one
    (degree_chebyshevResidual_le a b q) (eval_chebyshevResidual_zero q ha hab)
  refine ⟨s, hs, fun x hx => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
  have hev : 1 - (chebyshevResidual a b q).eval x = x * s.eval x := by
    rw [← eval_one (x := x), ← eval_sub, hrs, eval_mul, eval_X]
  have hval : s.eval x - x⁻¹ = -((chebyshevResidual a b q).eval x / x) := by
    rw [← one_div]
    field_simp
    linarith
  rw [Real.dist_eq, hval, abs_neg, abs_div, abs_of_pos hxpos]
  have hbound := (isUniformApproxOn_chebyshevResidual_two_mul_pow q ha hab).apply hx
  change |(chebyshevResidual a b q).eval x - 0| ≤ _ at hbound
  rw [sub_zero] at hbound
  calc
    |(chebyshevResidual a b q).eval x| / x ≤ |(chebyshevResidual a b q).eval x| / a :=
      div_le_div_of_nonneg_left (abs_nonneg _) ha hx.1
    _ ≤ (2 * ((√b - √a) / (√b + √a)) ^ q) / a :=
      div_le_div_of_nonneg_right hbound ha.le
    _ = (2 / a) * ((√b - √a) / (√b + √a)) ^ q := by ring

end NLAlib
