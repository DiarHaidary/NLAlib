/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# An elementary lower bound for the Gamma function

$\Gamma(x + 1) \ge x^x e^{-x}$ for real $x \ge 0$, the crude half of Stirling's formula, by
restricting Euler's integral to $[x, \infty)$. Mathlib has Stirling's formula for factorials only
(`Stirling.le_factorial_stirling`); this is the real-argument bound that the small-ball tails of
the $\chi^2$ law need at half-integers. Upstream candidate for
`Mathlib.Analysis.SpecialFunctions.Gamma.Basic`.

## Main results

* `Real.rpow_mul_exp_neg_le_Gamma_add_one`: $x^x e^{-x} \le \Gamma(x + 1)$.
-/

@[expose] public section

open MeasureTheory Set

namespace Real

/-- **Elementary lower bound for $\Gamma$**: $x^x e^{-x} \le \Gamma(x + 1)$ for $x \ge 0$,
equivalently $(x/e)^x \le \Gamma(x + 1)$. Euler's integral restricted to $[x, \infty)$, where
$t^x \ge x^x$. -/
theorem rpow_mul_exp_neg_le_Gamma_add_one {x : ℝ} (hx : 0 ≤ x) :
    x ^ x * exp (-x) ≤ Gamma (x + 1) := by
  have hs : 0 < x + 1 := by linarith
  rw [Gamma_eq_integral hs, add_sub_cancel_right]
  have hint : IntegrableOn (fun t => exp (-t) * t ^ x) (Ioi 0) :=
    (GammaIntegral_convergent hs).congr_fun (fun t _ => by rw [add_sub_cancel_right])
      measurableSet_Ioi
  have hsub : Ioi x ⊆ Ioi 0 := fun t (ht : x < t) => lt_of_le_of_lt hx ht
  calc x ^ x * exp (-x) = ∫ t in Ioi x, x ^ x * exp (-t) := by
        rw [integral_const_mul, integral_exp_neg_Ioi]
    _ ≤ ∫ t in Ioi x, exp (-t) * t ^ x := by
        refine setIntegral_mono_on ?_ (hint.mono_set hsub) measurableSet_Ioi
          fun t (ht : x < t) => ?_
        · exact (integrableOn_exp_neg_Ioi x).const_mul _
        · rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (rpow_le_rpow hx ht.le hx) (exp_pos _).le
    _ ≤ ∫ t in Ioi 0, exp (-t) * t ^ x :=
        setIntegral_mono_set hint ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) =>
          mul_nonneg (exp_pos _).le (rpow_nonneg ht.le _)) hsub.eventuallyLE

end Real
