/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Elementary bounds for the Gamma function

$\Gamma(x + 1) \ge x^x e^{-x}$ for real $x \ge 0$, the crude half of Stirling's formula, by
restricting Euler's integral to $[x, \infty)$. Mathlib has Stirling's formula for factorials only
(`Stirling.le_factorial_stirling`); this is the real-argument bound that the small-ball tails of
the $\chi^2$ law need at half-integers. In the other direction, $\Gamma(x) \le x^{x-1}$ for
$x \ge 1$: $\Gamma \le 1$ on $[1, 2]$ by convexity (`Real.convexOn_Gamma`), then
$\Gamma(x + 1) = x\Gamma(x)$; the readable form of the sub-exponential moment bound
(`NLAlib.subexponentialMomentBound_le`) inverts through it. Upstream candidates for
`Mathlib.Analysis.SpecialFunctions.Gamma.Basic` and, for the upper bound, which uses convexity,
`Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup`.

## Main results

* `Real.rpow_mul_exp_neg_le_Gamma_add_one`: $x^x e^{-x} \le \Gamma(x + 1)$.
* `Real.Gamma_le_rpow_sub_one`: $\Gamma(x) \le x^{x-1}$ for $x \ge 1$.
-/

@[expose] public section

open MeasureTheory Set

namespace Real

/-- Elementary lower bound for $\Gamma$: $x^x e^{-x} \le \Gamma(x + 1)$ for $x \ge 0$,
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

/-- $\Gamma \le 1$ on $[1, 2]$: $\Gamma$ is convex on $(0, \infty)$ and
$\Gamma(1) = \Gamma(2) = 1$. -/
private theorem Gamma_le_one_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) : Gamma x ≤ 1 := by
  have h := convexOn_Gamma.le_max_of_mem_Icc (x := 1) (y := 2) (z := x)
    (by norm_num : (1 : ℝ) ∈ Ioi 0) (by norm_num : (2 : ℝ) ∈ Ioi 0) hx
  rwa [Gamma_one, Gamma_two, max_self] at h

/-- For $x \ge 1$, $\Gamma(x) \le x^{x-1}$: $\Gamma \le 1$ on $[1, 2]$ by convexity and
$\Gamma(1) = \Gamma(2) = 1$, then $\Gamma(x + 1) = x\Gamma(x)$. The crude upper half of
Stirling's formula at real arguments; it loses a factor of about $e^{x}/\sqrt{2\pi x}$. -/
theorem Gamma_le_rpow_sub_one {x : ℝ} (hx : 1 ≤ x) : Gamma x ≤ x ^ (x - 1) := by
  have key : ∀ n : ℕ, ∀ y : ℝ, 1 ≤ y → y ≤ n + 2 → Gamma y ≤ y ^ (y - 1) := by
    intro n
    induction n with
    | zero =>
      intro y hy1 hy2
      exact (Gamma_le_one_of_mem_Icc ⟨hy1, by simpa using hy2⟩).trans
        (one_le_rpow hy1 (by linarith))
    | succ n ih =>
      intro y hy1 hy2
      rcases le_or_gt y (n + 2) with hyn | hyn
      · exact ih y hy1 hyn
      have hy0 : 0 < y - 1 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hIH := ih (y - 1) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
        (by push_cast at hy2; linarith)
      calc Gamma y = Gamma (y - 1 + 1) := by rw [sub_add_cancel]
        _ = (y - 1) * Gamma (y - 1) := Gamma_add_one hy0.ne'
        _ ≤ (y - 1) * (y - 1) ^ (y - 1 - 1) := by gcongr
        _ = (y - 1) ^ (y - 1) := by
          rw [mul_comm, ← rpow_add_one hy0.ne', sub_add_cancel]
        _ ≤ y ^ (y - 1) := rpow_le_rpow hy0.le (by linarith) hy0.le
  exact key ⌈x⌉₊ x hx (by have := Nat.le_ceil x; linarith)

end Real
