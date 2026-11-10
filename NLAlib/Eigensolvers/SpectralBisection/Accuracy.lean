/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Global

/-!
# Hermitian diagonalization in linear precision, at fixed parameters

[Shah2024, Theorem 4.2] for randomized spectral bisection (`NLAlib.eigh`) with every parameter
of the algorithm chosen: the depth counter $\ell = \lceil\log_2(1/\varepsilon)\rceil + 5$
(`NLAlib.bisectionDepth`), the accuracy $\beta$ of the sign function and deflation an explicit
function of $\varepsilon$, $\theta$ and $n$, and the black-box constants of a correctly rounded
machine ($\mu_{\mathrm{MM}}(d) = \mu_{\mathrm{QR}}(d) = 2d$, $c_{\mathrm N} = \sqrt2$, the constants
of `NLAlib.binaryFloatMachine`). The precision, floor and range conditions are then each one
explicit inequality in $\log_2(1/\varepsilon)$, $\log_2(1/\theta)$ and $\log_2 n$. The general
statements are in `NLAlib/Eigensolvers/SpectralBisection/Global.lean`.

With $\Lambda = \log_2(1/\varepsilon) + \log_2(1/\theta) + \log_2 n$, the hypotheses imply
those of
[Theorem 4.2](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw):
the window for $\beta$ lies below its $\hat\beta$, the step count $N_*$ is at most $4\Lambda$,
and the sign-function condition needs $\log_2(1/\varepsilon) + \tfrac32\log_2(1/\theta) +
\tfrac72\log_2 n + \tfrac72\log_2\Lambda + 24.07$ bits, the stopping and deflation conditions
$\log_2(1/\varepsilon) + \tfrac12\log_2(1/\theta) + \tfrac72\log_2 n + \tfrac52\log_2\Lambda +
29.4$.

Rounding these up to one inequality in $\Lambda$ costs a few bits against the
[general bit count](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw).

## Main results

* [Theorem 4.2 at fixed parameters](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_bisectionDepth_le_of_logb_le_of_hasLaw_eighSampleLaw).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- $\log_2 x \le x/4 + 1$ for $x \ge 8$. -/
private theorem logb_two_le_div_four_add_one {x : ℝ} (hx : 8 ≤ x) :
    Real.logb 2 x ≤ x / 4 + 1 := by
  have hy : 1 ≤ x / 8 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have h8 : Real.logb 2 x = 3 + Real.logb 2 (x / 8) := by
    rw [Real.logb_div (by linarith) (by norm_num),
      show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
    push_cast; ring
  have hl : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog : Real.log (x / 8) ≤ x / 8 - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hb : Real.logb 2 (x / 8) ≤ 2 * (x / 8 - 1) := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
    nlinarith [mul_nonneg (sub_nonneg.2 hy) (sub_nonneg.2 hl.le)]
  rw [h8]; linarith

/-- $\log_2\sqrt x = \tfrac12\log_2 x$ for $x > 0$. -/
private theorem logb_two_sqrt {x : ℝ} (hx : 0 < x) : Real.logb 2 √x = Real.logb 2 x / 2 := by
  rw [Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hx]; ring

/-- Exponentiating the precision condition of the theorem. -/
private theorem mul_le_of_logb_le {e θ n Λ u : ℝ} (he : 0 < e) (hθ : 0 < θ) (hn : 0 < n)
    (hΛ : 0 < Λ) (hu : 0 < u)
    (h : Real.logb 2 e⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ + 7 / 2 * Real.logb 2 n +
      4 * Real.logb 2 Λ + 24 ≤ Real.logb 2 u⁻¹) :
    u * (2 ^ 24 * (n ^ 3 * √n) * Λ ^ 4) ≤ e * (θ * √θ) := by
  have hK : 2 ^ 24 * (n ^ 3 * √n) * Λ ^ 4 / (e * (θ * √θ)) ≤ u⁻¹ := by
    rw [← Real.logb_le_logb one_lt_two (by positivity) (by positivity), Real.logb_div
      (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul he.ne' (by positivity), Real.logb_mul hθ.ne' (by positivity),
      Real.logb_pow, Real.logb_pow, Real.logb_pow, logb_two_sqrt hθ, logb_two_sqrt hn,
      Real.logb_self_eq_one one_lt_two]
    simp only [Real.logb_inv] at h ⊢
    push_cast
    linarith
  rw [div_le_iff₀ (by positivity)] at hK
  calc u * (2 ^ 24 * (n ^ 3 * √n) * Λ ^ 4) ≤ u * (u⁻¹ * (e * (θ * √θ))) :=
        mul_le_mul_of_nonneg_left hK hu.le
    _ = e * (θ * √θ) := by rw [← mul_assoc, mul_inv_cancel₀ hu.ne', one_mul]

/-- The parameters: $\log_2(1/\varepsilon) \ge 15$, $\log_2(1/\theta) \ge 0$, $\log_2 n \ge 0$ and
$\log_2(1/\varepsilon) + 5 \le \ell \le \log_2(1/\varepsilon) + 6$ for
$\ell = \lceil\log_2(1/\varepsilon)\rceil + 5$. -/
private theorem fifteen_le_logb_and {n : ℕ} {e θ : ℝ} (hn : 1 ≤ n) (he : 0 < e)
    (he₁ : e ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) :
    15 ≤ Real.logb 2 e⁻¹ ∧ 0 ≤ Real.logb 2 θ⁻¹ ∧ 0 ≤ Real.logb 2 n ∧
      Real.logb 2 e⁻¹ + 5 ≤ bisectionDepth e ∧ (bisectionDepth e : ℝ) ≤ Real.logb 2 e⁻¹ + 6 := by
  have hL : 15 ≤ Real.logb 2 e⁻¹ := by
    have h2 : (2 : ℝ) ^ (15 : ℕ) ≤ e⁻¹ := by
      rw [le_inv_comm₀ (by positivity) he, ← inv_pow]; exact he₁
    have := Real.logb_le_logb_of_le one_lt_two (by positivity) h2
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this
    exact_mod_cast this
  refine ⟨hL, Real.logb_nonneg one_lt_two ((one_le_inv₀ hθ).mpr hθ₁),
    Real.logb_nonneg one_lt_two (by exact_mod_cast hn), ?_, ?_⟩ <;> unfold bisectionDepth <;>
    push_cast
  · linarith [Nat.le_ceil (Real.logb 2 e⁻¹)]
  · linarith [Nat.ceil_lt_add_one (show 0 ≤ Real.logb 2 e⁻¹ by linarith)]

/-- The logarithm in $\hat T$: $\log(96nm/\theta) \le \tfrac75\Lambda$ and $\ge 0$ for
$m = \min(n, \ell + 1)$, $\Lambda = L + \log_2(1/\theta) + \log_2 n$, $L \ge 15$. -/
private theorem log_le_and_nonneg {n ℓ : ℕ} {θ L : ℝ} (hn : 1 ≤ n) (hθ : 0 < θ) (hθ₁ : θ ≤ 1)
    (hL : 15 ≤ L) :
    Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ) ≤
        7 / 5 * (L + Real.logb 2 θ⁻¹ + Real.logb 2 n) ∧
      0 ≤ Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm1 : 1 ≤ min (n : ℝ) (ℓ + 1) := le_min hn1 (by linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)])
  have hmn : min (n : ℝ) (ℓ + 1) ≤ n := min_le_left _ _
  have hpos : 0 < 96 * (n : ℝ) * min (n : ℝ) (ℓ + 1) := by positivity
  refine ⟨?_, Real.log_nonneg ?_⟩
  · have hx : 96 * (n : ℝ) * min (n : ℝ) (ℓ + 1) / θ ≤ 2 ^ 7 * (n : ℝ) ^ 2 * θ⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (inv_nonneg.2 hθ.le)
    have h1 := Real.log_le_log (div_pos hpos hθ) hx
    rw [Real.log_mul (by positivity) (inv_pos.2 hθ).ne', Real.log_mul (by norm_num)
      (by positivity), Real.log_pow, Real.log_pow] at h1
    have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    have hk : Real.log n = Real.logb 2 n * Real.log 2 := by rw [Real.logb, div_mul_cancel₀ _ hl]
    have ht : Real.log θ⁻¹ = Real.logb 2 θ⁻¹ * Real.log 2 := by
      rw [Real.logb, div_mul_cancel₀ _ hl]
    have hk0 : 0 ≤ Real.logb 2 n := Real.logb_nonneg one_lt_two hn1
    have ht0 : 0 ≤ Real.logb 2 θ⁻¹ := Real.logb_nonneg one_lt_two ((one_le_inv₀ hθ).mpr hθ₁)
    have hl2 : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
    have a1 := mul_le_mul_of_nonneg_left hl2 hk0
    have a2 := mul_le_mul_of_nonneg_left hl2 ht0
    rw [hk, ht] at h1
    push_cast at h1
    nlinarith
  · rw [le_div_iff₀ hθ, one_mul]; nlinarith

/-- $D = \sqrt{nm\min(n, e)} \le 2n$ for $m = \min(n, \ell + 1)$. -/
private theorem sqrt_le_two_mul {n ℓ : ℕ} (hn : 1 ≤ n) :
    √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) ≤ 2 * n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [show 2 * (n : ℝ) = √((2 * n) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  have h1 : min (n : ℝ) (ℓ + 1) ≤ n := min_le_left _ _
  have h2 : min (n : ℝ) (Real.exp 1) ≤ 3 :=
    (min_le_right _ _).trans (by linarith [Real.exp_one_lt_d9])
  have h0 : 0 ≤ min (n : ℝ) (ℓ + 1) := le_min (by positivity) (by positivity)
  have h0' : 0 ≤ min (n : ℝ) (Real.exp 1) := le_min (by positivity) (Real.exp_pos 1).le
  calc (n : ℝ) * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1) ≤ n * n * 3 := by gcongr
    _ ≤ (2 * n) ^ 2 := by nlinarith

/-- $\hat T = 2\sqrt2\sqrt n + \sqrt g \le 2\sqrt{n\Lambda}$ for $0 \le g \le \tfrac75\Lambda$,
$\Lambda \ge 15$. -/
private theorem two_mul_sqrt_two_mul_sqrt_add_sqrt_le {n Λ g : ℝ} (hn : 1 ≤ n) (hΛ : 15 ≤ Λ)
    (hg0 : 0 ≤ g) (hg : g ≤ 7 / 5 * Λ) : 2 * √2 * √n + √g ≤ 2 * √(n * Λ) := by
  have h4 : √(4 * (n * Λ)) = 2 * √(n * Λ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← h4]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  have ha : (2 * √2 * √n) ^ 2 = 8 * n := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by linarith)]; ring
  have eg := Real.sq_sqrt hg0
  nlinarith [sq_nonneg (2 * √2 * √n - √g),
    mul_nonneg (sub_nonneg.2 hn) (show (0 : ℝ) ≤ 4 * Λ - 16 by linarith)]

/-- The accuracy window of the theorem lies below the bound $\hat\beta$ of the general theorem. -/
private theorem div_le_div_of_le_two_mul {n ℓ : ℕ} {e θ Λ D T : ℝ} (hn : 1 ≤ n) (he : 0 < e)
    (hθ : 0 < θ) (hΛ : 15 ≤ Λ) (hℓ : 20 ≤ ℓ) (hℓΛ : (ℓ : ℝ) ≤ 7 / 5 * Λ) (hD0 : 0 < D)
    (hD : D ≤ 2 * n) (hT0 : 0 < T) (hT : T ≤ 2 * √(n * Λ)) :
    e * √θ / (1024 * (n * Λ) * √(n * Λ)) ≤
      ((ℓ : ℝ) - 1) ^ 2 * e * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) * D * T) := by
  have hℓ1 : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have a1 : (ℓ : ℝ) ^ 2 ≤ 10 / 9 * ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
  have a2 : 2 * (ℓ : ℝ) - 1 ≤ 14 / 5 * Λ := by linarith
  have hX : 52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) * D * T ≤
      ((ℓ : ℝ) - 1) ^ 2 * (1024 * (n * Λ) * √(n * Λ)) := by
    calc 52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) * D * T ≤
          52 * (10 / 9 * ((ℓ : ℝ) - 1) ^ 2) * (14 / 5 * Λ) * (2 * n) * (2 * √(n * Λ)) := by
          gcongr
          linarith
      _ = 29120 / 45 * ((ℓ : ℝ) - 1) ^ 2 * (n * Λ * √(n * Λ)) := by ring
      _ ≤ 1024 * ((ℓ : ℝ) - 1) ^ 2 * (n * Λ * √(n * Λ)) := by gcongr; norm_num
      _ = _ := by ring
  rw [div_le_div_iff₀ (by positivity)
    (mul_pos (mul_pos (mul_pos (by positivity) (by linarith)) hD0) hT0)]
  calc e * √θ * (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) * D * T) ≤
        e * √θ * (((ℓ : ℝ) - 1) ^ 2 * (1024 * (n * Λ) * √(n * Λ))) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = _ := by ring

/-- The sign-function condition of the general theorem. -/
private theorem mul_le_mul_of_le_div {n ℓ : ℕ} {e θ Λ u β : ℝ} (hn : 1 ≤ n) (hθ : 0 < θ)
    (hΛ : 15 ≤ Λ) (hu : 0 ≤ u) (hℓℓ : (ℓ : ℝ) * (ℓ + 1) ≤ 21 / 10 * Λ ^ 2)
    (hβ : e * √θ / (2048 * (n * Λ) * √(n * Λ)) ≤ β)
    (key : u * (2 ^ 24 * (n ^ 3 * √(n : ℝ)) * Λ ^ 4) ≤ e * (θ * √θ)) :
    146 * n * ℓ * (ℓ + 1) * (4 * (2 * n) + 10 + 10 * √(n : ℝ)) * u ≤ θ * β := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : √(n : ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hν : 4 * (2 * (n : ℝ)) + 10 + 10 * √(n : ℝ) ≤ 28 * n := by linarith
  have hr : 3 ≤ √Λ := by
    rw [show (3 : ℝ) = √(3 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hrr : √Λ * √Λ = Λ := Real.mul_self_sqrt (by linarith)
  have hsq : √((n : ℝ) * Λ) = √(n : ℝ) * √Λ := Real.sqrt_mul (by positivity) _
  have h1 : 146 * n * ℓ * (ℓ + 1) * (4 * (2 * n) + 10 + 10 * √(n : ℝ)) * u ≤
      146 * n * (21 / 10 * Λ ^ 2) * (28 * n) * u := by
    calc _ = 146 * n * ((ℓ : ℝ) * (ℓ + 1)) * (4 * (2 * n) + 10 + 10 * √(n : ℝ)) * u := by ring
      _ ≤ _ := by gcongr
  have hΛr : 87908352 / 5 * √Λ ≤ 2 ^ 24 * Λ := by
    nlinarith [mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg Λ)]
  have h2 : 146 * n * (21 / 10 * Λ ^ 2) * (28 * n) * u ≤
      θ * (e * √θ / (2048 * (n * Λ) * √(n * Λ))) := by
    rw [mul_div_assoc', le_div_iff₀ (by positivity), hsq]
    calc 146 * n * (21 / 10 * Λ ^ 2) * (28 * n) * u * (2048 * (n * Λ) * (√(n : ℝ) * √Λ))
        = u * ((n : ℝ) ^ 3 * √(n : ℝ)) * Λ ^ 3 * (87908352 / 5 * √Λ) := by ring
      _ ≤ u * ((n : ℝ) ^ 3 * √(n : ℝ)) * Λ ^ 3 * (2 ^ 24 * Λ) :=
        mul_le_mul_of_nonneg_left hΛr (by positivity)
      _ = u * (2 ^ 24 * (n ^ 3 * √(n : ℝ)) * Λ ^ 4) := by ring
      _ ≤ e * (θ * √θ) := key
      _ = θ * (e * √θ) := by ring
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left hβ hθ.le))

/-- The step count of the sign iterations is at most $4\Lambda$. -/
private theorem newtonSchulzSteps_le {n ℓ : ℕ} {e θ Λ β : ℝ} (hn : 1 ≤ n) (he : 0 < e)
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hL : 15 ≤ Real.logb 2 e⁻¹) (ht : 0 ≤ Real.logb 2 θ⁻¹)
    (hk : 0 ≤ Real.logb 2 n) (hΛ : Λ = Real.logb 2 e⁻¹ + Real.logb 2 θ⁻¹ + Real.logb 2 n)
    (hℓ : 20 ≤ ℓ) (hℓℓ : (ℓ : ℝ) * (ℓ + 1) ≤ 21 / 10 * Λ ^ 2) (hβ₁ : β ≤ 1)
    (hβ : e * √θ / (2048 * (n * Λ) * √(n * Λ)) ≤ β) :
    newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (β / (16 * n)) ≤ 4 * Λ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hℓ1 : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hΛ15 : 15 ≤ Λ := by linarith
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hq : 0 < 12 * (n : ℝ) * ℓ * (ℓ + 1) := by positivity
  have hx0 : 0 < θ / (12 * n * ℓ * (ℓ + 1)) := div_pos hθ hq
  have hmin : min |θ / (12 * n * ℓ * (ℓ + 1))| (1 / 2) = θ / (12 * n * ℓ * (ℓ + 1)) := by
    rw [abs_of_pos hx0]
    have h20 : (20 : ℝ) ≤ ℓ * (ℓ + 1) := by nlinarith
    exact min_eq_left (by
      rw [div_le_iff₀ hq]; nlinarith [mul_le_mul hn1 h20 (by norm_num) (by positivity)])
  have hlΛ := logb_two_le_div_four_add_one (show 8 ≤ Λ by linarith)
  have h1 : Real.logb 2 (θ / (12 * n * ℓ * (ℓ + 1)))⁻¹ ≤
      5 + Real.logb 2 n + 2 * Real.logb 2 Λ + Real.logb 2 θ⁻¹ := by
    have hle : (θ / (12 * n * ℓ * (ℓ + 1)))⁻¹ ≤ 2 ^ 5 * n * Λ ^ 2 * θ⁻¹ := by
      rw [inv_div, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hθ.le)
      nlinarith [mul_le_mul_of_nonneg_left hℓℓ (show (0 : ℝ) ≤ n by positivity),
        show (0 : ℝ) ≤ n * Λ ^ 2 by positivity]
    calc _ ≤ Real.logb 2 (2 ^ 5 * n * Λ ^ 2 * θ⁻¹) :=
          Real.logb_le_logb_of_le one_lt_two (inv_pos.2 hx0) hle
      _ = _ := by
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
          (by positivity), Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
          Real.logb_pow, Real.logb_self_eq_one one_lt_two]
        push_cast; ring
  have hy : (β / (16 * n))⁻¹ ≤ 2 ^ 15 * n ^ 2 * Λ * √(n * Λ) * e⁻¹ * √θ⁻¹ := by
    rw [inv_div, div_le_iff₀ hβ0, Real.sqrt_inv]
    calc 16 * (n : ℝ) = 2 ^ 15 * n ^ 2 * Λ * √(n * Λ) * e⁻¹ * (√θ)⁻¹ *
          (e * √θ / (2048 * (n * Λ) * √(n * Λ))) := by
          field_simp
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hβ (by positivity)
  have hy1 : 1 < (β / (16 * n))⁻¹ := by
    rw [inv_div, one_lt_div hβ0]; linarith
  have h2 : Real.logb 2 (β / (16 * n))⁻¹ ≤ 4 * Λ := by
    have := Real.logb_le_logb_of_le one_lt_two (by linarith) hy
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
      (by positivity), Real.logb_mul (by positivity) (by positivity), Real.logb_mul
      (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
      Real.logb_pow, Real.logb_pow, logb_two_sqrt (by positivity), logb_two_sqrt (by positivity),
      Real.logb_mul (by positivity) (by positivity), Real.logb_self_eq_one one_lt_two] at this
    push_cast at this
    linarith
  have h3 : Real.logb 2 (Real.logb 2 (β / (16 * n))⁻¹) ≤ 2 + Real.logb 2 Λ := by
    calc _ ≤ Real.logb 2 (4 * Λ) :=
          Real.logb_le_logb_of_le one_lt_two (Real.logb_pos one_lt_two hy1) h2
      _ = _ := by
        rw [Real.logb_mul (by norm_num) (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.logb_pow, Real.logb_self_eq_one one_lt_two]
        push_cast; ring
  unfold newtonSchulzSteps
  rw [hmin]
  linarith

/-- The stopping and deflation conditions of the general theorem. -/
private theorem mul_le_and_mul_le {n : ℕ} {e θ Λ u β Nst : ℝ} (hn : 1 ≤ n) (he : 0 < e)
    (hθ₁ : θ ≤ 1) (hΛ : 15 ≤ Λ) (hu : 0 ≤ u) (hN : Nst ≤ 4 * Λ)
    (hβ : e * √θ / (2048 * (n * Λ) * √(n * Λ)) ≤ β)
    (key : u * (2 ^ 24 * (n ^ 3 * √(n : ℝ)) * Λ ^ 4) ≤ e * (θ * √θ)) :
    2048 * (n + Nst + 1) * (4 * (2 * n) + 10 + 10 * √(n : ℝ)) * u ≤ β ∧
      16 * (4 * (2 * n) + 4 * √(n : ℝ) * (√2 + 1) + 2 * (2 * n) + 1) * u ≤ β := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : √(n : ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hs2 : √(2 : ℝ) ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hr : 3 ≤ √Λ := by
    rw [show (3 : ℝ) = √(3 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hrr : √Λ * √Λ = Λ := Real.mul_self_sqrt (by linarith)
  have hsq : √((n : ℝ) * Λ) = √(n : ℝ) * √Λ := Real.sqrt_mul (by positivity) _
  have hnΛ : 15 ≤ (n : ℝ) * Λ := by nlinarith
  have hP : 344064 * (n : ℝ) ^ 2 * Λ * u ≤ β := by
    refine le_trans ?_ hβ
    rw [le_div_iff₀ (by positivity), hsq]
    have hΛr : 42 * Λ ^ 2 * √Λ ≤ Λ ^ 4 := by
      have : 45 * √Λ ≤ Λ * Λ := by nlinarith [mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg Λ)]
      nlinarith [Real.sqrt_nonneg Λ, sq_nonneg Λ]
    have hθs : θ * √θ ≤ √θ := mul_le_of_le_one_left (Real.sqrt_nonneg θ) hθ₁
    calc 344064 * (n : ℝ) ^ 2 * Λ * u * (2048 * (n * Λ) * (√(n : ℝ) * √Λ))
        = 2 ^ 24 * (u * ((n : ℝ) ^ 3 * √(n : ℝ))) * (42 * Λ ^ 2 * √Λ) := by ring
      _ ≤ 2 ^ 24 * (u * ((n : ℝ) ^ 3 * √(n : ℝ))) * Λ ^ 4 :=
        mul_le_mul_of_nonneg_left hΛr (by positivity)
      _ = u * (2 ^ 24 * (n ^ 3 * √(n : ℝ)) * Λ ^ 4) := by ring
      _ ≤ e * (θ * √θ) := key
      _ ≤ e * √θ := mul_le_mul_of_nonneg_left hθs he.le
  constructor
  · refine le_trans ?_ hP
    have hν : 4 * (2 * (n : ℝ)) + 10 + 10 * √(n : ℝ) ≤ 28 * n := by linarith
    have hm : (n : ℝ) + Nst + 1 ≤ 5 * (n * Λ) := by nlinarith
    calc 2048 * (n + Nst + 1) * (4 * (2 * n) + 10 + 10 * √(n : ℝ)) * u
        ≤ 2048 * (5 * (n * Λ)) * (4 * (2 * n) + 10 + 10 * √(n : ℝ)) * u := by gcongr
      _ ≤ 2048 * (5 * (n * Λ)) * (28 * n) * u := by gcongr
      _ ≤ 344064 * (n : ℝ) ^ 2 * Λ * u := by nlinarith [mul_nonneg (mul_nonneg
          (show (0 : ℝ) ≤ n ^ 2 by positivity) (show (0 : ℝ) ≤ Λ by linarith)) hu]
  · refine le_trans ?_ hP
    have h1 : 4 * (2 * (n : ℝ)) + 4 * √(n : ℝ) * (√2 + 1) + 2 * (2 * n) + 1 ≤ 23 * n := by
      nlinarith [mul_le_mul hsn (show √2 + 1 ≤ 5 / 2 by linarith) (by positivity)
        (by positivity)]
    have h2 : 16 * (23 * (n : ℝ)) ≤ 344064 * n ^ 2 * Λ := by nlinarith
    calc 16 * (4 * (2 * n) + 4 * √(n : ℝ) * (√2 + 1) + 2 * (2 * n) + 1) * u
        ≤ 16 * (23 * (n : ℝ)) * u := by gcongr
      _ ≤ 344064 * (n : ℝ) ^ 2 * Λ * u := mul_le_mul_of_nonneg_right h2 hu

/-- The floor condition of the general theorem. -/
private theorem mul_le_min_of_mul_le {n ℓ : ℕ} {e θ R τ : ℝ} (hn : 1 ≤ n) (he : 0 < e)
    (he₁ : e ≤ 1) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hτ₀ : 0 ≤ τ) (hR : 0 < R)
    (hτ : 300 * n ^ 3 * τ ≤ e * θ * min R 1) :
    τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (e * min R 1) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : √(n : ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hm0 : 0 < min R 1 := lt_min hR one_pos
  have hm1 : min R 1 ≤ 1 := min_le_right _ _
  have hmn : min (n : ℝ) (ℓ + 1) ≤ n := min_le_left _ _
  have hmp : 1 ≤ min (n : ℝ) (ℓ + 1) := le_min hn1 (by linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)])
  have h0 : τ * (100 * n * √(n : ℝ)) ≤ 100 * n ^ 2 * τ := by
    calc τ * (100 * n * √(n : ℝ)) = (100 * n * τ) * √(n : ℝ) := by ring
      _ ≤ (100 * n * τ) * n := mul_le_mul_of_nonneg_left hsn (by positivity)
      _ = 100 * n ^ 2 * τ := by ring
  have hn23 : (n : ℝ) ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have hn2 : 100 * (n : ℝ) ^ 2 * τ ≤ 100 * n ^ 3 * τ := by
    nlinarith [mul_nonneg hτ₀ (sub_nonneg.2 hn23)]
  have hn3 : 0 ≤ (n : ℝ) ^ 3 * τ := by positivity
  have heθ : e * θ * min R 1 ≤ θ := by
    calc e * θ * min R 1 ≤ 1 * θ * 1 := by gcongr
      _ = θ := by ring
  refine le_min ?_ ?_
  · have h1 : 100 * (n : ℝ) ^ 2 * τ ≤ θ / (3 * n) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    refine h0.trans (h1.trans ((le_abs_self _).trans (Real.abs_le_sqrt ?_)))
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have a : θ ^ 2 ≤ θ := by nlinarith
    have b : 8 * (n : ℝ) * min (n : ℝ) (ℓ + 1) ≤ 8 * n ^ 2 := by nlinarith
    nlinarith [mul_le_mul a b (by positivity) hθ.le]
  · calc τ * (100 * n * √(n : ℝ)) ≤ 300 * n ^ 3 * τ := by nlinarith
      _ ≤ e * θ * min R 1 := hτ
      _ ≤ e * 1 * min R 1 := by gcongr
      _ = e * min R 1 := by ring

/-- The range condition of the general theorem. -/
private theorem le_of_mul_add_le {n ℓ : ℕ} {θ R Λ Ω : ℝ} (hn : 1 ≤ n) (hR : 0 < R)
    (hΛ : 15 ≤ Λ) (hℓΛ : (ℓ : ℝ) ≤ 7 / 5 * Λ)
    (hg : Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ) ≤ 7 / 5 * Λ)
    (hΩ : 64 * (R + n + Λ) ≤ Ω) :
    16 * (2 * R + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : √(n : ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hs2 : √(2 : ℝ) ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hg' : √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)) ≤ Λ :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have h2 : 2 * √2 * √(n : ℝ) ≤ 3 * n := by
    nlinarith [mul_le_mul hs2 hsn (Real.sqrt_nonneg _) (by norm_num)]
  linarith

-- The declaration name and a docstring line exceed 100 characters.
set_option linter.style.longLine false in
/-- **Hermitian diagonalization in linear precision, at fixed parameters** (Theorem 4.2 with
every parameter chosen). Let the machine meet `NLAlib.FloatMachine.IsAccurate` with unit roundoff
$u$, floor $\tau \ge 0$ and range $\Omega$ at the constants of correctly rounded black boxes,
$\mu_{\mathrm{MM}}(d) = \mu_{\mathrm{QR}}(d) = 2d$ and $c_{\mathrm N} = \sqrt2$ (those of
`NLAlib.binaryFloatMachine`), with samplers of measurable fibres and countable ranges. Let the
stored $n \times n$ input $\mathbf{A}$, $n \ge 1$, have Hermitian decoding with
$\|\mathbf{A}\|_2 \le R_0$ for a stored $R_0 > 0$, let $0 < \varepsilon \le 2^{-15}$,
$0 < \theta \le 1$ and
$$\Lambda = \log_2\frac1\varepsilon + \log_2\frac1\theta + \log_2 n \,.$$
Run `NLAlib.eigh` with the depth counter $\ell = \lceil\log_2(1/\varepsilon)\rceil + 5$
(`NLAlib.bisectionDepth`), a sign step limit of at least $4\Lambda$ and a stored accuracy
$$\frac{\varepsilon\sqrt\theta}{2048\,(n\Lambda)^{3/2}} \le \beta \le
\frac{\varepsilon\sqrt\theta}{1024\,(n\Lambda)^{3/2}}$$
(the upper end rounded down to a power of two, say), on node samples that are independent, each
with law `NLAlib.eighSampleLaw` $n$. If the precision is
$$\log_2\frac1u \ge \log_2\frac1\varepsilon + \frac32\log_2\frac1\theta + \frac72\log_2 n +
4\log_2\Lambda + 24 \,,$$
the floor is small, $300n^3\tau \le \varepsilon\theta\min(R_0, 1)$, and the range large,
$64(R_0 + n + \Lambda) \le \Omega$, then
$$\mathbb{P}\bigl[\mathsf{eigh}(\mathbf{A}, \varepsilon) \text{ is not an approximate
diagonalization with residual } 2\varepsilon R_0 \text{ and } \mathbf{U} \text{ within }
\varepsilon/3 \text{ of unitary}\bigr] \le \theta \,,$$
$\mathsf{eigh}$ the decoded output of `NLAlib.eigh`. At these constants the precision is 54.6,
67.4, 92.4 and 123.1 bits at $(n, \varepsilon, \theta) = (1, 2^{-15}, 1)$, $(10, 2^{-15}, 1)$,
$(1000, 2^{-15}, 1)$, $(1000, 2^{-40}, 1/2)$. It is at least 54.6 bits, the value at
$(1, 2^{-15}, 1)$, so binary64 ($p = 53$) never meets it, while the general bit count
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw`
asks for 49.3 there at the same constants; binary128 ($p = 113$) meets it at $1 \le n \le 1024$,
$\varepsilon = 2^{-15}$, $\theta = 1/2$, $R_0 = 1$ with at most 94.3 bits (the third example in
`NLAlib/Eigensolvers/SpectralBisection/Instance.lean`). The hypotheses are satisfiable for every
$n$, $\varepsilon$, $\theta$, $R_0$: the last example there meets them at every $n \ge 1$,
$0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$, $R_0 > 0$ in a binary format chosen for
the parameters.
[Shah2024, Theorem 4.2], there $\log_2(1/\varepsilon) +
\log_2\max(n^{1.5}\mu_{\mathrm{QR}}, n^2c_{\mathrm N}, n^{4.5}\mu_{\mathrm{MM}}) +
2\log_2\log_2(1/\varepsilon) + 1.5\log_2(1/\theta) + \log_2\log_2(n\log_2(1/\varepsilon)/\theta)
+ 23$ bits for $R_0 = \|\mathbf{A}\|_2$, node-dependent accuracies and unspecified floor and
range conditions; at the same constants, $\mu_{\mathrm{MM}}(n) = \mu_{\mathrm{QR}}(n) = 2n$ and
$c_{\mathrm N} = \sqrt2$, that is 48.8, 67.9, 105.4 and 135.0 bits at the four points.
Result: spectral-bisection-diagonalization-simple -/
theorem
    FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_bisectionDepth_le_of_logb_le_of_hasLaw_eighSampleLaw
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω : ℝ}
    (hM : M.IsAccurate dec u τ Ω (fun d => 2 * (d : ℝ)) (fun d => 2 * (d : ℝ)) √2)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {Λ : ℝ}
    (hΛ : Λ = Real.logb 2 (dec ε)⁻¹ + Real.logb 2 θ⁻¹ + Real.logb 2 n)
    (hβ : dec ε * √θ / (2048 * (n * Λ) * √(n * Λ)) ≤ dec β)
    (hβ' : dec β ≤ dec ε * √θ / (1024 * (n * Λ) * √(n * Λ)))
    (hbits : Real.logb 2 (dec ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ + 7 / 2 * Real.logb 2 n +
      4 * Real.logb 2 Λ + 24 ≤ Real.logb 2 u⁻¹)
    {signFuel : ℕ} (hfuel : 4 * Λ ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : 300 * n ^ 3 * τ ≤ dec ε * θ * min (dec R₀) 1) (hΩ : 64 * (dec R₀ + n + Λ) ≤ Ω)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {ζ : List Bool → Ω' → EighSample ℝ ℂ n} (hind : iIndepFun ζ μ)
    (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel (bisectionDepth (dec ε)) A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel (bisectionDepth (dec ε)) A R₀ ε β fun a => ζ a ω).2 i))
      (2 * dec ε * dec R₀) (dec ε / 3)} ≤ θ := by
  obtain ⟨hL, ht, hk, hℓlo, hℓhi⟩ := fifteen_le_logb_and hn hε hε₁ hθ hθ₁
  set ℓ := bisectionDepth (dec ε) with hℓdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hℓ20 : 20 ≤ ℓ := by exact_mod_cast (show (20 : ℝ) ≤ ℓ by linarith)
  have hΛ15 : 15 ≤ Λ := by linarith
  have hℓΛ : (ℓ : ℝ) ≤ 7 / 5 * Λ := by linarith
  have hℓℓ : (ℓ : ℝ) * (ℓ + 1) ≤ 21 / 10 * Λ ^ 2 := by
    nlinarith [mul_le_mul hℓΛ (show (ℓ : ℝ) + 1 ≤ 3 / 2 * Λ by linarith) (by positivity)
      (by positivity)]
  obtain ⟨hg, hg0⟩ := log_le_and_nonneg (ℓ := ℓ) hn hθ hθ₁ hL
  rw [← hΛ] at hg
  have hu0 : 0 ≤ u := by
    have h := hM.ofNat 1 (by norm_num; nlinarith)
    have h1 : 0 < max |((1 : ℕ) : ℝ)| τ := lt_max_of_lt_left (by norm_num)
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) h1
    linarith [abs_nonneg (((1 : ℕ) : ℝ) - dec (M.ofNat 1))]
  have hu : 0 < u := by
    refine lt_of_le_of_ne hu0 fun h => ?_
    rw [← h, inv_zero, Real.logb_zero] at hbits
    linarith [Real.logb_nonneg one_lt_two (show 1 ≤ Λ by linarith)]
  have key := mul_le_of_logb_le hε hθ (by positivity) (by positivity) hu hbits
  have hb0 : 0 < dec ε * √θ / (2048 * (n * Λ) * √(n * Λ)) := by positivity
  have hβle := hβ'.trans (div_le_div_of_le_two_mul hn hε hθ hΛ15 hℓ20 hℓΛ (by positivity)
    (sqrt_le_two_mul (ℓ := ℓ) hn) (by positivity)
    (two_mul_sqrt_two_mul_sqrt_add_sqrt_le hn1 hΛ15 hg0 hg))
  have hβ1 : dec β ≤ 1 := by
    refine hβ'.trans ((div_le_one (by positivity)).mpr ?_)
    have h1 : 1 ≤ √((n : ℝ) * Λ) := Real.one_le_sqrt.mpr (by nlinarith)
    have h2 : dec ε * √θ ≤ 1 :=
      mul_le_one₀ (by linarith [show (2 : ℝ)⁻¹ ^ 15 ≤ 1 by norm_num]) (Real.sqrt_nonneg θ)
        (Real.sqrt_le_one.mpr hθ₁)
    have h3 : 1 ≤ (n : ℝ) * Λ * √((n : ℝ) * Λ) := one_le_mul_of_one_le_of_one_le (by nlinarith) h1
    linarith
  have hN := newtonSchulzSteps_le (ℓ := ℓ) hn hε hθ hθ₁ hL ht hk hΛ hℓ20 hℓℓ hβ1 hβ
  obtain ⟨hstop, hdefl⟩ := mul_le_and_mul_le hn hε hθ₁ hΛ15 hu0 hN hβ key
  exact hM.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw hunifm hunifc
    hnormalm hnormalc (Nat.mono_cast.const_mul (by norm_num)) (Nat.mono_cast.const_mul
    (by norm_num)) (by norm_num) (by norm_num) (by positivity) hn hA hR₀ hR₀pos hε hε₁ hθ hθ₁
    le_rfl (hb0.trans_le hβ) hβle rfl (mul_le_mul_of_le_div hn hθ hΛ15 hu0 hℓℓ hβ key) hstop
    hdefl (hN.trans hfuel) hτ₀ (mul_le_min_of_mul_le hn hε (hε₁.trans (by norm_num)) hθ hθ₁
    hτ₀ hR₀pos hτ) (le_of_mul_add_le hn hR₀pos hΛ15 hℓΛ hg hΩ) hind hlaw

end NLAlib
