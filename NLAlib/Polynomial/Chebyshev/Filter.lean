/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import NLAlib.ForMathlib.Analysis.Convex.SupportingLine
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import NLAlib.ForMathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Growth

/-!
# Chebyshev filters with supporting lines

The squared Chebyshev filter of randomized block Krylov iteration,
$\varphi_j(y) = y\,T_j(2y - 1)^2 = y\,T_{2j}(\sqrt{y})^2$, is not convex on $[0, \infty)$, but it
has a supporting line on $[0, \infty)$ at every point $x \ge 1$: on $[0, 1]$ its derivative is at
most $\varphi_j'(1)$, and on $[1, \infty)$ it is convex. This is what lets Jensen's inequality pass
through the filter in the gapless bound for randomized block Krylov iteration
(`HasSupportingLineOn.le_integral_comp`).

## Main results

* `NLAlib.hasSupportingLineOn_mul_eval_T_sq`: the supporting lines of $y\,T_j(2y - 1)^2$.
-/

@[expose] public section

open Polynomial Polynomial.Chebyshev

namespace NLAlib

-- Stage B2b

/-- **Supporting lines of the squared Chebyshev filter**: for every $j$ and every $x \ge 1$, the
function $\varphi(y) = y\,T_j(2y - 1)^2$ has a supporting line on $[0, \infty)$ at $x$. Since
$T_j(2y - 1) = T_{2j}(\sqrt{y})$, this is the filter $y\,T_{2j}(\sqrt{y})^2$ of the source.
[TroppWebber2023, Lemma 9.3], part 5; there for $x\,T_{2j}(x^{1/2})^2$ (the $x^{1/4}$ variant of the
source is not needed). -/
theorem hasSupportingLineOn_mul_eval_T_sq (j : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    HasSupportingLineOn (fun y => y * ((T ℝ (j : ℤ)).eval (2 * y - 1)) ^ 2) (Set.Ici 0) x := by
  -- Write $g(t) = T_j(2t - 1)$ and $d(t) = T_j'(2t - 1)$, so $\varphi' = g^2 + 4tgd$.
  set g : ℝ → ℝ := fun t => (T ℝ (j : ℤ)).eval (2 * t - 1) with hg
  set d : ℝ → ℝ := fun t => (derivative (T ℝ (j : ℤ))).eval (2 * t - 1) with hd
  set φ : ℝ → ℝ := fun y => y * ((T ℝ (j : ℤ)).eval (2 * y - 1)) ^ 2
  set φ' : ℝ → ℝ := fun t => g t ^ 2 + 4 * (t * g t * d t) with hφ'
  have hderiv (t : ℝ) : HasDerivAt φ (φ' t) t := by
    have h₁ : HasDerivAt (fun t : ℝ => 2 * t - 1) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
    have h₂ := (Polynomial.hasDerivAt (T ℝ (j : ℤ)) (2 * t - 1)).comp t h₁
    refine ((hasDerivAt_id' t).mul (h₂.pow 2)).congr_deriv ?_
    simp only [hφ', hg, hd, Function.comp_apply, Pi.pow_apply]
    push_cast
    ring
  -- On $[1, \infty)$, $g \ge 1$ and $d \ge 0$ are non-decreasing, hence so is $\varphi'$.
  have hmono : MonotoneOn φ' (Set.Ici 1) := by
    intro s hs t ht hst
    have hs' : (1 : ℝ) ≤ 2 * s - 1 := by simp only [Set.mem_Ici] at hs; linarith
    have ht' : (1 : ℝ) ≤ 2 * t - 1 := by simp only [Set.mem_Ici] at ht; linarith
    have hst' : 2 * s - 1 ≤ 2 * t - 1 := by linarith
    have hg₁ : 1 ≤ g s := one_le_eval_T_real _ hs'
    have hgst : g s ≤ g t := monotoneOn_eval_T_real j hs' ht' hst'
    have hd₀ : 0 ≤ d s := by
      simpa using eval_iterate_derivative_T_real_nonneg (x := 2 * s - 1) j 1 hs'
    have hdst : d s ≤ d t := by
      simpa using monotoneOn_eval_iterate_derivative_T_real j 1 hs' ht' hst'
    have hs₀ : (0 : ℝ) ≤ s := by simp only [Set.mem_Ici] at hs; linarith
    have ht₀ : (0 : ℝ) ≤ t := by linarith
    have hgt₀ : 0 ≤ g t := by linarith
    simp only [hφ']
    gcongr
  -- On $[0, 1]$, $|g| \le 1$ and $|d| \le T_j'(1) = j^2$, so $\varphi' \le 1 + 4j^2 = \varphi'(1)$.
  have hle₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ' t ≤ φ' 1 := by
    rintro t ⟨ht₀, ht₁⟩
    have habs : |2 * t - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have hgt : |g t| ≤ 1 := abs_eval_T_real_le_one _ habs
    have hdt : |d t| ≤ (j : ℝ) ^ 2 := by
      have := abs_iterate_derivative_T_real_le (j : ℤ) 1 habs
      simpa [derivative_T_eval_one] using this
    have hg1 : g 1 = 1 := by norm_num [hg, T_eval_one]
    have hd1 : d 1 = (j : ℝ) ^ 2 := by norm_num [hd, derivative_T_eval_one]
    have hsq : g t ^ 2 ≤ 1 := by
      rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hgt
    have hprod : t * g t * d t ≤ (j : ℝ) ^ 2 := by
      calc t * g t * d t ≤ |t * g t * d t| := le_abs_self _
        _ = t * (|g t| * |d t|) := by rw [abs_mul, abs_mul, abs_of_nonneg ht₀, mul_assoc]
        _ ≤ 1 * (1 * (j : ℝ) ^ 2) := by gcongr
        _ = (j : ℝ) ^ 2 := by ring
    simp only [hφ', hg1, hd1]
    linarith
  -- Hence $\varphi' \le \varphi'(x)$ on $[0, x]$ and $\varphi' \ge \varphi'(x)$ on
  -- $[x, \infty)$, so $\varphi(y) - \varphi'(x)\,y$ is minimised at $y = x$.
  have hx₁ : x ∈ Set.Ici (1 : ℝ) := hx
  refine ⟨φ' x, fun y hy => ?_⟩
  have hd' (t : ℝ) : HasDerivAt (fun t => φ t - φ' x * t) (φ' t - φ' x) t := by
    have := (hderiv t).sub ((hasDerivAt_id' t).const_mul (φ' x))
    rwa [mul_one] at this
  have hcont : Continuous fun t => φ t - φ' x * t :=
    continuous_iff_continuousAt.2 fun t => (hd' t).continuousAt
  suffices φ x - φ' x * x ≤ φ y - φ' x * y by linarith
  rcases le_total y x with hyx | hxy
  · have hanti : AntitoneOn (fun t => φ t - φ' x * t) (Set.Icc 0 x) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 x) hcont.continuousOn
        (fun t _ => (hd' t).hasDerivWithinAt) fun t ht => ?_
      rw [interior_Icc] at ht
      rcases le_total t 1 with ht₁ | ht₁
      · have := hle₁ t ⟨ht.1.le, ht₁⟩
        have := hmono (Set.mem_Ici.2 le_rfl) hx₁ hx
        linarith
      · have := hmono (Set.mem_Ici.2 ht₁) hx₁ ht.2.le
        linarith
    exact hanti ⟨hy, hyx⟩ ⟨by linarith, le_rfl⟩ hyx
  · have hmon : MonotoneOn (fun t => φ t - φ' x * t) (Set.Ici x) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici x) hcont.continuousOn
        (fun t _ => (hd' t).hasDerivWithinAt) fun t ht => ?_
      rw [interior_Ici] at ht
      have := hmono hx₁ (Set.mem_Ici.2 (hx.trans ht.le)) (Set.mem_Ioi.1 ht).le
      linarith
    exact hmon (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hxy) hxy

end NLAlib
