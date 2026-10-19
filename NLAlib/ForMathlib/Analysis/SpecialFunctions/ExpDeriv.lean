/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Bernstein's bound for the exponential

For $x \le L$ and $0 < \theta$ with $L\theta < 3$,
$e^{\theta x} \le 1 + \theta x + (\theta^2/2)/(1 - L\theta/3)\, x^2$: the scalar inequality
behind Bernstein's inequality, scalar and matrix. It follows from
$u^2/2 - (1 - u/3)(e^u - 1 - u) \ge 0$ for every real $u$, proved by the sign of derivatives.
Upstream candidate for `Mathlib.Analysis.SpecialFunctions.ExpDeriv`.

## Main results

* `Real.exp_mul_le_bernstein`.
-/

@[expose] public section

namespace Real

/-- The derivative of $u + (e^u - 1 - u)/3 - (1 - u/3)(e^u - 1)$. -/
private theorem hasDerivAt_bernsteinAux' (u : ℝ) :
    HasDerivAt (fun u => u + (exp u - 1 - u) / 3 - (1 - u / 3) * (exp u - 1))
      ((1 - exp u * (1 - u)) / 3) u := by
  have h1 := (((hasDerivAt_exp u).sub_const 1).sub (hasDerivAt_id' u)).div_const 3
  have h2 := ((hasDerivAt_id' u).div_const 3).const_sub 1
  have h3 := h2.mul ((hasDerivAt_exp u).sub_const 1)
  refine (((hasDerivAt_id' u).add h1).sub h3).congr_deriv ?_
  ring

/-- The derivative of $u^2/2 - (1 - u/3)(e^u - 1 - u)$. -/
private theorem hasDerivAt_bernsteinAux (u : ℝ) :
    HasDerivAt (fun u => u ^ 2 / 2 - (1 - u / 3) * (exp u - 1 - u))
      (u + (exp u - 1 - u) / 3 - (1 - u / 3) * (exp u - 1)) u := by
  have h1 := ((hasDerivAt_exp u).sub_const 1).sub (hasDerivAt_id' u)
  have h2 := ((hasDerivAt_id' u).div_const 3).const_sub 1
  refine (((hasDerivAt_pow 2 u).div_const 2).sub (h2.mul h1)).congr_deriv ?_
  simp only [Pi.sub_apply]
  push_cast
  ring

/-- $u^2/2 - (1 - u/3)(e^u - 1 - u) \ge 0$ for every real $u$: its derivative is monotone and
vanishes at $0$, where the function vanishes. -/
private theorem bernsteinAux_nonneg (u : ℝ) :
    0 ≤ u ^ 2 / 2 - (1 - u / 3) * (exp u - 1 - u) := by
  set g : ℝ → ℝ := fun u => u ^ 2 / 2 - (1 - u / 3) * (exp u - 1 - u) with hg
  set h : ℝ → ℝ := fun u => u + (exp u - 1 - u) / 3 - (1 - u / 3) * (exp u - 1)
    with hh
  have hmono : Monotone h := by
    refine monotone_of_deriv_nonneg (fun u => (hasDerivAt_bernsteinAux' u).differentiableAt)
      fun u => ?_
    rw [(hasDerivAt_bernsteinAux' u).deriv]
    have h1 := add_one_le_exp (-u)
    have h2 : exp u * exp (-u) = 1 := by
      rw [← exp_add, add_neg_cancel, exp_zero]
    have h3 := exp_pos u
    refine div_nonneg ?_ (by norm_num)
    nlinarith
  have hd : Differentiable ℝ g := fun u => (hasDerivAt_bernsteinAux u).differentiableAt
  have hg0 : g 0 = 0 := by simp only [hg]; norm_num
  have hh0 : h 0 = 0 := by simp only [hh]; norm_num
  change 0 ≤ g u
  rcases le_total u 0 with hu | hu
  · have hanti : AntitoneOn g (Set.Iic 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Iic 0) hd.continuous.continuousOn
        hd.differentiableOn fun x hx => ?_
      rw [interior_Iic] at hx
      rw [(hasDerivAt_bernsteinAux x).deriv]
      exact (hmono (le_of_lt (Set.mem_Iio.mp hx))).trans_eq hh0
    have := hanti (Set.mem_Iic.mpr hu) (Set.mem_Iic.mpr le_rfl) hu
    linarith
  · have hmon : MonotoneOn g (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hd.continuous.continuousOn
        hd.differentiableOn fun x hx => ?_
      rw [interior_Ici] at hx
      rw [(hasDerivAt_bernsteinAux x).deriv]
      exact hh0.symm.trans_le (hmono (le_of_lt (Set.mem_Ioi.mp hx)))
    have := hmon (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
    linarith

/-- The one-sided Bernstein bound for the exponential: for $x \le L$ and $0 < \theta$ with
$L\theta < 3$,
$$e^{\theta x} \le 1 + \theta x + \frac{\theta^2/2}{1 - L\theta/3}\, x^2\,.$$
[Tropp2015, Lemma 6.6.2]. -/
theorem exp_mul_le_bernstein {L θ x : ℝ} (hθ : 0 < θ) (hθL : L * θ < 3) (hx : x ≤ L) :
    exp (θ * x) ≤ 1 + θ * x + θ ^ 2 / 2 / (1 - L * θ / 3) * x ^ 2 := by
  have hux : θ * x ≤ L * θ := by nlinarith
  have hpos : 0 < 1 - L * θ / 3 := by linarith
  have hpos' : 0 < 1 - θ * x / 3 := by linarith
  have hg := bernsteinAux_nonneg (θ * x)
  have h1 : exp (θ * x) - 1 - θ * x ≤ (θ * x) ^ 2 / 2 / (1 - θ * x / 3) := by
    rw [le_div_iff₀ hpos']
    nlinarith
  have h2 : (θ * x) ^ 2 / 2 / (1 - θ * x / 3) ≤ (θ * x) ^ 2 / 2 / (1 - L * θ / 3) :=
    div_le_div_of_nonneg_left (by positivity) hpos (by linarith)
  have h3 : θ ^ 2 / 2 / (1 - L * θ / 3) * x ^ 2 = (θ * x) ^ 2 / 2 / (1 - L * θ / 3) := by ring
  linarith

end Real
