/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.Complex.ExponentialBounds

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
* `Real.Gamma_add_half_le_mul_sqrt`: the half-step consequence of log-convexity.
* `Real.Gamma_le_rpow_sub_one`: $\Gamma(x) \le x^{x-1}$ for $x \ge 1$.
* `Real.sqrt_pi_div_rpow_mul_Gamma_lt_rpow`: the half-integer inverse chi-square endpoint.
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

/-- For $x > 0$, $\Gamma(x + 1/2) \le \Gamma(x)\sqrt{x}$, by log-convexity at $x$
and $x+1$ and the Gamma recurrence. This is a consequence of Mathlib's
`Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma`.
Port of `NLAlib.Gamma_add_half_le_mul_sqrt`. -/
theorem Gamma_add_half_le_mul_sqrt {x : ℝ} (hx : 0 < x) :
    Gamma (x + 1 / 2) ≤ Gamma x * sqrt x := by
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx (by linarith : 0 < x + 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hG : 0 < Gamma x := Gamma_pos_of_pos hx
  rw [show 1 / 2 * x + 1 / 2 * (x + 1) = x + 1 / 2 by ring, Gamma_add_one hx.ne',
    ← Real.mul_rpow hG.le (by positivity), ← Real.sqrt_eq_rpow,
    show Gamma x * (x * Gamma x) = Gamma x ^ 2 * x by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hG.le] at h
  exact h

/-- The elementary exponential estimate in the inverse chi-square endpoint. -/
private theorem exp_one_pow_mul_three_lt {n : ℕ} (hn : 5 ≤ n) :
    exp 1 ^ n * 3 < 2 * 3 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have he : exp 1 < 11 / 4 := lt_trans exp_one_lt_d9 (by norm_num)
  have he0 : 0 < exp 1 := exp_pos 1
  have he3 : exp 1 ≤ 3 := by linarith
  have h5 : exp 1 ^ 5 * 3 < 2 * 3 ^ 5 := by
    have := pow_lt_pow_left₀ he he0.le (by norm_num : (5 : ℕ) ≠ 0)
    have : (11 / 4 : ℝ) ^ 5 * 3 < 2 * 3 ^ 5 := by norm_num
    nlinarith
  have hm : exp 1 ^ m ≤ 3 ^ m := pow_le_pow_left₀ he0.le he3 m
  rw [pow_add, pow_add]
  have : 0 < exp 1 ^ 5 := by positivity
  have : (0 : ℝ) < 3 ^ m := by positivity
  nlinarith

/-- Duplication and factorial Stirling give a lower bound for the squared half-integer Gamma. -/
private theorem mul_pi_mul_div_exp_pow_le_Gamma_sq {n : ℕ} (hn : 0 < n) :
    4 * π * ((n : ℝ) ^ n / exp 1 ^ n) ≤ n * 2 ^ n * Gamma ((n : ℝ) / 2) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set x : ℝ := (n : ℝ) / 2 with hx
  have hx0 : 0 < x := by positivity
  set G := Gamma x with hGdef
  have hG : 0 < G := Gamma_pos_of_pos hx0
  set s := √x with hs
  have hs0 : 0 < s := sqrt_pos.mpr hx0
  set sp := √π with hsp
  have hspsq : sp ^ 2 = π := sq_sqrt pi_pos.le
  have hhalf : Gamma (x + 1 / 2) ≤ G * s := Gamma_add_half_le_mul_sqrt hx0
  have hdup : G * Gamma (x + 1 / 2) = Gamma n * 2 ^ (1 - (n : ℝ)) * sp := by
    rw [hGdef, Gamma_mul_Gamma_add_half, hx, show 2 * ((n : ℝ) / 2) = n by ring]
  have hfac : (n : ℝ) * Gamma n = (n.factorial : ℝ) := by
    rw [← Gamma_add_one hn0.ne', Gamma_nat_eq_factorial]
  have hstir := Stirling.le_factorial_stirling n
  have hsqrt : √(2 * π * n) = 2 * sp * s := by
    rw [show 2 * π * (n : ℝ) = 2 ^ 2 * π * x by rw [hx]; ring, sqrt_mul (by positivity),
      sqrt_mul (by positivity), sqrt_sq (by norm_num)]
  have htwo : (2 : ℝ) ^ (1 - (n : ℝ)) * 2 ^ n = 2 := by
    rw [← rpow_natCast, ← rpow_add (by norm_num)]
    norm_num
  have hdivpow : ((n : ℝ) / exp 1) ^ n = (n : ℝ) ^ n / exp 1 ^ n := div_pow _ _ _
  have hprod : G * Gamma (x + 1 / 2) ≤ G ^ 2 * s := by
    have := mul_le_mul_of_nonneg_left hhalf hG.le
    nlinarith
  have hscaled : (n.factorial : ℝ) * sp * 2 ≤ n * 2 ^ n * G ^ 2 * s := by
    have hbound : Gamma n * (2 : ℝ) ^ (1 - (n : ℝ)) * sp ≤ G ^ 2 * s := hdup ▸ hprod
    have hpos : (0 : ℝ) ≤ n * 2 ^ n := by positivity
    have := mul_le_mul_of_nonneg_left hbound hpos
    calc (n.factorial : ℝ) * sp * 2
        = (n * Gamma n) * ((2 : ℝ) ^ (1 - (n : ℝ)) * 2 ^ n) * sp := by rw [hfac, htwo]; ring
      _ = n * 2 ^ n * (Gamma n * (2 : ℝ) ^ (1 - (n : ℝ)) * sp) := by ring
      _ ≤ n * 2 ^ n * (G ^ 2 * s) := this
      _ = n * 2 ^ n * G ^ 2 * s := by ring
  have hfacLower : 2 * sp * s * ((n : ℝ) ^ n / exp 1 ^ n) ≤ n.factorial := by
    rw [← hsqrt, ← hdivpow]
    exact hstir
  have hcancel : 4 * π * ((n : ℝ) ^ n / exp 1 ^ n) * s ≤ n * 2 ^ n * G ^ 2 * s := by
    calc 4 * π * ((n : ℝ) ^ n / exp 1 ^ n) * s
        = (2 * sp * s * ((n : ℝ) ^ n / exp 1 ^ n)) * sp * 2 := by rw [← hspsq]; ring
      _ ≤ (n.factorial : ℝ) * sp * 2 := by gcongr
      _ ≤ _ := hscaled
  exact le_of_mul_le_mul_right hcancel hs0

/-- The strict polynomial inequality obtained after bounding the exponential factor. -/
private theorem mul_pi_pow_lt_mul_Gamma_sq {n : ℕ} (hn : 5 ≤ n) :
    6 * π * (n : ℝ) ^ n < n * 6 ^ n * Gamma ((n : ℝ) / 2) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hgamma := mul_pi_mul_div_exp_pow_le_Gamma_sq (show 0 < n by omega)
  have hexp := exp_one_pow_mul_three_lt hn
  have hen : 0 < exp 1 ^ n := by positivity
  have hfirst : 6 * π * (n : ℝ) ^ n < 4 * π * ((n : ℝ) ^ n / exp 1 ^ n) * 3 ^ n := by
    rw [show 4 * π * ((n : ℝ) ^ n / exp 1 ^ n) * 3 ^ n =
      (π * (n : ℝ) ^ n) * (2 * (2 * 3 ^ n)) / exp 1 ^ n by ring, lt_div_iff₀ hen]
    have hpn : 0 < π * (n : ℝ) ^ n := by positivity
    nlinarith
  calc 6 * π * (n : ℝ) ^ n < 4 * π * ((n : ℝ) ^ n / exp 1 ^ n) * 3 ^ n := hfirst
    _ ≤ n * 2 ^ n * Gamma ((n : ℝ) / 2) ^ 2 * 3 ^ n := by gcongr
    _ = n * 6 ^ n * Gamma ((n : ℝ) / 2) ^ 2 := by
      rw [show (6 : ℝ) ^ n = 2 ^ n * 3 ^ n by rw [← mul_pow]; norm_num]
      ring

/-- The half-integer Gamma estimate underlying the inverse chi-square moment bound:
$\sqrt{\pi}/(2^q\Gamma(d/2)) < (3/d)^q$ for $q=(d-1)/2$ and $d\ge5$.
The proof uses duplication, log-convexity, and factorial Stirling.
Port of the private `sqrt_pi_div_lt_rpow` in the backend's `Probability/ChiSquare/ChiSquare.lean`;
the resulting moment inequality is [HalkoMartinssonTropp2011, Lemma A.10]. -/
theorem sqrt_pi_div_rpow_mul_Gamma_lt_rpow {d : ℕ} (hd : 5 ≤ d) :
    sqrt π / (2 ^ (((d : ℝ) - 1) / 2) * Gamma ((d : ℝ) / 2)) <
      (3 / (d : ℝ)) ^ (((d : ℝ) - 1) / 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set q : ℝ := ((d : ℝ) - 1) / 2 with hq
  set G := Gamma ((d : ℝ) / 2) with hGdef
  have hG : 0 < G := Gamma_pos_of_pos (by positivity)
  set sp := √π with hsp
  have hspsq : sp ^ 2 = π := sq_sqrt pi_pos.le
  have key := mul_pi_pow_lt_mul_Gamma_sq hd
  have h2q : 2 * q = (d : ℝ) - 1 := by rw [hq]; ring
  have hsq : ∀ a : ℝ, 0 < a → (a ^ q) ^ 2 = a ^ d / a := by
    intro a ha
    rw [← rpow_natCast (a ^ q) 2, ← rpow_mul ha.le,
      show q * ((2 : ℕ) : ℝ) = 2 * q by push_cast; ring,
      h2q, rpow_sub_one ha.ne', rpow_natCast a d]
  have hA : sp * (d : ℝ) ^ q < (6 : ℝ) ^ q * G := by
    apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
    rw [mul_pow, mul_pow, hspsq, hsq _ hd0, hsq 6 (by norm_num)]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have : π * ((d : ℝ) ^ d * (d : ℝ)⁻¹) = (6 * π * (d : ℝ) ^ d) * (6 * (d : ℝ))⁻¹ := by
      field_simp
    rw [this, show (6 : ℝ) ^ d * 6⁻¹ * G ^ 2 = (d * 6 ^ d * G ^ 2) * (6 * (d : ℝ))⁻¹ by
      field_simp]
    exact mul_lt_mul_of_pos_right key (by positivity)
  rw [div_lt_iff₀ (by positivity), div_rpow (by norm_num) hd0.le]
  rw [show (3 : ℝ) ^ q / (d : ℝ) ^ q * (2 ^ q * G) =
    ((2 : ℝ) ^ q * 3 ^ q) * G / (d : ℝ) ^ q by ring,
    ← mul_rpow (by norm_num) (by norm_num), lt_div_iff₀ (by positivity)]
  norm_num
  linarith

end Real
