/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp

/-!
# Chebyshev coefficients

Canonical full Chebyshev coefficients for real-input, real- or complex-valued functions.
The constant coefficient uses $1/\pi$ and positive coefficients use $2/\pi$, so the expansion
has no half-constant term. Cosine Bochner integrals are primary; later contour representations
are equalities, not additional coefficient objects.

## Main results

* `NLAlib.chebyshevCoeff`: the canonical coefficient.
* `NLAlib.chebyshevCoeff_add`: additivity under interval integrability.
* `NLAlib.chebyshevCoeff_const_mul`: scalar linearity.
* `NLAlib.chebyshevCoeff_eval_T`: coefficient identification on the Chebyshev basis.
-/

@[expose] public section

open MeasureTheory Polynomial Polynomial.Chebyshev

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The full coefficient is
$$a_k=\frac{2-\mathbf{1}_{k=0}}{\pi}\int_0^\pi f(\cos\theta)\cos(k\theta)\,d\theta.$$
[Trefethen2019, Theorem 3.1, Eqs. (3.11)–(3.12)], after cosine substitution, generalized to
RCLike values. Each weighted integrand has its own Bochner integrability condition; its integral
is zero when nonintegrable. Nonintegrability of the unweighted pullback does not force every
coefficient to vanish. No reconstruction is asserted for arbitrary functions. -/
noncomputable def chebyshevCoeff (f : ℝ → 𝕜) (k : ℕ) : 𝕜 :=
  (((if k = 0 then 1 else 2) / Real.pi : ℝ) : 𝕜) *
    ∫ θ in 0..Real.pi, f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : 𝕜)

/-- Every coefficient of the zero function vanishes. -/
theorem chebyshevCoeff_zero (k : ℕ) :
    chebyshevCoeff (fun _ : ℝ => (0 : 𝕜)) k = 0 := by
  simp only [chebyshevCoeff, zero_mul, intervalIntegral.integral_zero, mul_zero]

/-- Coefficients are additive when the cosine pullbacks are interval-integrable. -/
theorem chebyshevCoeff_add {f g : ℝ → 𝕜}
    (hf : IntervalIntegrable (fun θ => f (Real.cos θ)) volume 0 Real.pi)
    (hg : IntervalIntegrable (fun θ => g (Real.cos θ)) volume 0 Real.pi) (k : ℕ) :
    chebyshevCoeff (fun x => f x + g x) k = chebyshevCoeff f k + chebyshevCoeff g k := by
  have hc : ContinuousOn (fun θ : ℝ => (Real.cos ((k : ℝ) * θ) : 𝕜))
      (Set.uIcc 0 Real.pi) := by fun_prop
  simp only [chebyshevCoeff, add_mul]
  rw [intervalIntegral.integral_add (hf.mul_continuousOn hc) (hg.mul_continuousOn hc), mul_add]

/-- Coefficients commute with multiplication by a scalar, without integrability assumptions. -/
theorem chebyshevCoeff_const_mul (c : 𝕜) (f : ℝ → 𝕜) (k : ℕ) :
    chebyshevCoeff (fun x => c * f x) k = c * chebyshevCoeff f k := by
  simp only [chebyshevCoeff, mul_assoc, intervalIntegral.integral_const_mul]
  rw [← mul_assoc, mul_comm _ c, mul_assoc]

private lemma eval_T_ofReal (j : ℕ) (x : ℝ) :
    (T 𝕜 (j : ℤ)).eval (x : 𝕜) = algebraMap ℝ 𝕜 ((T ℝ (j : ℤ)).eval x) := by
  rw [← map_T (algebraMap ℝ 𝕜), eval_map_apply]

private lemma integral_cos_mul_cos (j k : ℕ) :
    (∫ θ in 0..Real.pi, Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)) =
      if j = k then (if k = 0 then Real.pi else Real.pi / 2) else 0 := by
  have h := integral_measureT_eq_integral_cos
    (f := fun x => (T ℝ (j : ℤ)).eval x * (T ℝ (k : ℤ)).eval x)
  simp only [T_real_cos, Int.cast_natCast] at h
  rw [← h]
  split_ifs with hjk hk
  · subst j
    subst k
    exact integral_eval_T_real_mul_self_measureT_zero
  · subst j
    exact integral_T_real_mul_self_measureT_of_ne_zero hk
  · exact integral_eval_T_real_mul_eval_T_real_measureT_of_ne hjk

/-- The coefficient of $T_j$ at index $k$ is one for $j=k$ and zero otherwise.
[Trefethen2019, Exercise 3.7]; [GolubMeurant2010, §2.5.1]. The generic scalar form follows by
transporting Mathlib's real orthogonality through the real-to-RCLike integral map. -/
theorem chebyshevCoeff_eval_T (j k : ℕ) :
    chebyshevCoeff (fun x : ℝ => (Polynomial.Chebyshev.T 𝕜 (j : ℤ)).eval (x : 𝕜)) k =
      if j = k then 1 else 0 := by
  unfold chebyshevCoeff
  simp_rw [eval_T_ofReal, T_real_cos, Int.cast_natCast, ← RCLike.ofReal_mul]
  rw [RCLike.intervalIntegral_ofReal, integral_cos_mul_cos]
  split_ifs <;> simp [Real.pi_ne_zero]

end NLAlib
