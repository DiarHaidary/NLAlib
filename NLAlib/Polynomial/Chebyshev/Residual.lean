/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Growth
public import NLAlib.ForMathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Normalized Chebyshev residuals

The shifted Chebyshev polynomial normalized at zero, with uniform bounds on a positive interval.
Degree and error remain separate, so the same metric approximation interface serves other functions.

## Main results

* `NLAlib.chebyshevResidual`: the normalized residual polynomial.
* `NLAlib.degree_chebyshevResidual_le`: unconditional degree bound.
* `NLAlib.eval_chebyshevResidual_zero`: normalization on a positive nondegenerate interval.
* `NLAlib.isUniformApproxOn_chebyshevResidual`: the reciprocal-Chebyshev error bound.
* `NLAlib.isUniformApproxOn_chebyshevResidual_two_mul_pow`: geometric decay.
-/

@[expose] public section

open Polynomial Polynomial.Chebyshev

namespace NLAlib

/-- The normalized residual is
$$r_q(x)=\frac{T_q((b+a-2x)/(b-a))}{T_q((b+a)/(b-a))}.$$
For $0<a<b$ it equals one at zero and is small on $[a,b]$.
[Saad2003, Theorem 6.25 and following corollary]. The definition is total: division by zero
uses Lean's zero inverse. If the normalizing denominator vanishes, the polynomial is zero;
when $a=b$, both affine coefficients are zero, so the result is the constant
$T_q(0)^{-1}T_q(0)$. No normalization is asserted outside $0<a<b$.
-/
noncomputable def chebyshevResidual (a b : ℝ) (q : ℕ) : ℝ[X] :=
  Polynomial.C (((Polynomial.Chebyshev.T ℝ (q : ℤ)).eval ((b + a) / (b - a)))⁻¹) *
    (Polynomial.Chebyshev.T ℝ (q : ℤ)).comp
      (Polynomial.C ((b + a) / (b - a)) - Polynomial.C (2 / (b - a)) * Polynomial.X)

/-- Evaluation of the normalized residual by the scalar Chebyshev quotient. -/
theorem eval_chebyshevResidual (a b : ℝ) (q : ℕ) (x : ℝ) :
    (chebyshevResidual a b q).eval x =
      (T ℝ (q : ℤ)).eval ((b + a) / (b - a) - 2 / (b - a) * x) /
        (T ℝ (q : ℤ)).eval ((b + a) / (b - a)) := by
  simp only [chebyshevResidual, eval_mul, eval_C, eval_comp, eval_sub, eval_X]
  simp only [div_eq_mul_inv]
  exact mul_comm _ _

/-- The normalized residual has degree at most $q$, including degenerate parameters. -/
theorem degree_chebyshevResidual_le (a b : ℝ) (q : ℕ) :
    (chebyshevResidual a b q).degree ≤ (q : WithBot ℕ) := by
  unfold chebyshevResidual
  refine ((congrArg degree (C_mul' _ _)).trans_le (degree_smul_le _ _)).trans
    (degree_le_natDegree.trans ?_)
  have hd : (C ((b + a) / (b - a)) - C (2 / (b - a)) * X : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans (max_le (by simp only [natDegree_C, zero_le]) ?_)
    exact (natDegree_C_mul_le _ _).trans (by simp only [natDegree_X, le_refl])
  have h : ((T ℝ (q : ℤ)).comp
      (C ((b + a) / (b - a)) - C (2 / (b - a)) * X)).natDegree ≤ q := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_T, Int.natAbs_natCast]
    exact (Nat.mul_le_mul_left q hd).trans_eq (mul_one q)
  exact_mod_cast h

/-- For $0<a<b$, the residual equals one at zero.
[Saad2003, Theorem 6.25 and following corollary]. -/
theorem eval_chebyshevResidual_zero {a b : ℝ} (q : ℕ) (ha : 0 < a) (hab : a < b) :
    (chebyshevResidual a b q).eval 0 = 1 := by
  have hT := one_le_eval_T_real (q : ℤ) (show 1 ≤ (b + a) / (b - a) by
    rw [le_div_iff₀ (by linarith)]
    linarith)
  rw [eval_chebyshevResidual, mul_zero, sub_zero, div_self (by linarith)]

/-- On $[a,b]$, where $0<a<b$, the residual satisfies
$$|r_q(x)|\le T_q((b+a)/(b-a))^{-1}.$$
[Saad2003, Theorem 6.25 and following corollary].

Result: chebyshev-residual
-/
theorem isUniformApproxOn_chebyshevResidual {a b : ℝ} (q : ℕ)
    (ha : 0 < a) (hab : a < b) :
    Metric.IsUniformApproxOn (chebyshevResidual a b q).eval (fun _ => 0) (Set.Icc a b)
      (((T ℝ (q : ℤ)).eval ((b + a) / (b - a)))⁻¹) := by
  intro x hx
  have hba : 0 < b - a := by linarith
  have hT := one_le_eval_T_real (q : ℤ) (show 1 ≤ (b + a) / (b - a) by
    rw [le_div_iff₀ hba]
    linarith)
  have hy : |(b + a) / (b - a) - 2 / (b - a) * x| ≤ 1 := by
    have he : (b + a) / (b - a) - 2 / (b - a) * x = (b + a - 2 * x) / (b - a) := by
      field_simp
    rw [he, abs_le, le_div_iff₀ hba, div_le_iff₀ hba]
    constructor <;> linarith [hx.1, hx.2]
  change |(chebyshevResidual a b q).eval x - 0| ≤ _
  rw [sub_zero, eval_chebyshevResidual, abs_div,
    abs_of_pos (show 0 < (T ℝ (q : ℤ)).eval ((b + a) / (b - a)) by linarith),
    ← one_div]
  exact div_le_div_of_nonneg_right (abs_eval_T_real_le_one _ hy) (by linarith)

/-- For $0<a<b$, the uniform residual bound has geometric form
$$|r_q(x)|\le2\left(\frac{\sqrt b-\sqrt a}{\sqrt b+\sqrt a}\right)^q
\quad(x\in[a,b]).$$
At $q=0$ this remains valid with residual one and upper bound two.
[Saad2003, proof of Theorem 6.29, Eq. (6.128)], stated as a scalar residual estimate.

Result: chebyshev-residual
-/
theorem isUniformApproxOn_chebyshevResidual_two_mul_pow {a b : ℝ} (q : ℕ)
    (ha : 0 < a) (hab : a < b) :
    Metric.IsUniformApproxOn (chebyshevResidual a b q).eval (fun _ => 0) (Set.Icc a b)
      (2 * ((Real.sqrt b - Real.sqrt a) / (Real.sqrt b + Real.sqrt a)) ^ q) := by
  apply (isUniformApproxOn_chebyshevResidual q ha hab).mono_error
  have hlow := sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real ha hab q
  have hsa := Real.sqrt_pos.2 ha
  have hsb : √a < √b := Real.sqrt_lt_sqrt ha.le hab
  have hρ : 0 < ((√b + √a) / (√b - √a)) ^ q := by
    apply pow_pos
    apply div_pos <;> linarith
  have hT : 0 < (T ℝ (q : ℤ)).eval ((b + a) / (b - a)) := by
    linarith [div_pos hρ two_pos]
  have hinv : (√b - √a) / (√b + √a) = ((√b + √a) / (√b - √a))⁻¹ := by
    rw [inv_div]
  rw [hinv, inv_pow, ← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hT hρ]
  linarith

end NLAlib
