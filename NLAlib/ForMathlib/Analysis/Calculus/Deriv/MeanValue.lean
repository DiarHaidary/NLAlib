/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# An integrating-factor comparison

If $t f'(t) + b f(t) \le 0$ on $(0, \infty)$ with $b > 0$, the integrating factor $t^b$ makes
$t^b f(t)$ antitone on $[0, \infty)$. Grönwall's inequality
(`norm_le_gronwallBound_of_norm_deriv_right_le`) does not cover this case, because the coefficient
$b/t$ is singular at $0$. Upstream candidate for `Mathlib.Analysis.Calculus.Deriv.MeanValue`.

Design: stage Probability-Beta (`docs/design/Probability-Beta.md` §3.3, β4e).

## Main results

* `antitoneOn_rpow_mul_of_hasDerivAt`: the integrating-factor comparison.
-/

@[expose] public section

open Set

/-- Integrating factor: if $f$ is differentiable on $(0, \infty)$ with derivative $f'$,
continuous from the right at $0$, $b > 0$, and $t f'(t) + b f(t) \le 0$ for every $t > 0$, then
$t \mapsto t^b f(t)$ is antitone on $[0, \infty)$. -/
theorem antitoneOn_rpow_mul_of_hasDerivAt {f f' : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hc : ContinuousWithinAt f (Ici 0) 0) (hf : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (h : ∀ t ∈ Ioi (0 : ℝ), t * f' t + b * f t ≤ 0) :
    AntitoneOn (fun t => t ^ b * f t) (Ici 0) := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ b * f t) (Ici 0) := by
    intro t ht
    rcases eq_or_lt_of_le (mem_Ici.mp ht) with rfl | hpos
    · exact (Real.continuousAt_rpow_const 0 b (Or.inr hb.le)).continuousWithinAt.mul hc
    · exact (Real.continuousAt_rpow_const t b (Or.inl hpos.ne')).continuousWithinAt.mul
        (hf t hpos).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ interior (Ici (0 : ℝ)),
      HasDerivAt (fun t : ℝ => t ^ b * f t) (t ^ (b - 1) * (t * f' t + b * f t)) t := by
    intro t ht
    rw [interior_Ici] at ht
    have ht0 : t ≠ 0 := ht.out.ne'
    refine ((Real.hasDerivAt_rpow_const (Or.inl ht0)).mul (hf t ht)).congr_deriv ?_
    rw [Real.rpow_sub_one ht0]
    field_simp
    ring
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont
    (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt) fun t ht => ?_
  rw [(hderiv t ht).deriv]
  rw [interior_Ici] at ht
  exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg ht.out.le _) (h t ht)
