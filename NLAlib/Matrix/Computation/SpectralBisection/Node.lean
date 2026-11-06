/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisection.Child

/-!
# Local guarantee of a node of spectral bisection

A node of the machine
algorithm `NLAlib.eighAux` with a good sample whose children return approximate
diagonalizations returns one itself, with residual $\varepsilon(R + R_0)$ and singular values
within $\varepsilon/3$ of $1$ ([Shah2024, Lemma 4.1]); leaves are treated directly.

## Main results

* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_leaf`: the leaves.
* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`:
  Lemma 4.1.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- The stored half window $\lvert\mathrm{fl}(R/\mathrm{fl}(2))\rvert \le R/2 + 2uR + u\tau$. -/
private theorem FloatMachine.IsAccurate.abs_dec_div_ofNat_two_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R : F} (hu : 0 ≤ u) (hu1 : u ≤ 1 / 1000)
    (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1 / 4) (hR : 0 ≤ dec R) (hRΩ : dec R ≤ Ω) (hΩ : 2 ≤ Ω) :
    |dec (M.div R (M.ofNat 2))| ≤ dec R / 2 + 2 * u * dec R + u * τ := by
  have h2 := abs_le.mp (abs_sub_le_of_isRoundingOf (hM.ofNat 2) (by norm_num; linarith) hu hτ₀)
  push_cast at h2
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
  have huτ := mul_le_mul_of_nonneg_left hτ hu
  have ht1 : 2 - 3 * u ≤ dec (M.ofNat 2) := by linarith
  have ht0 : 0 < dec (M.ofNat 2) := by linarith
  have hRt : dec R / dec (M.ofNat 2) ≤ dec R / 2 + u * dec R := by
    rw [div_le_iff₀ ht0]
    have := mul_le_mul_of_nonneg_right ht1 (by positivity : 0 ≤ dec R / 2 + u * dec R)
    nlinarith [mul_nonneg (mul_nonneg hu hu) hR]
  have hRt0 : 0 ≤ dec R / dec (M.ofNat 2) := div_nonneg hR ht0.le
  have hd := abs_sub_le_of_isRoundingOf (hM.div R (M.ofNat 2) ht0.ne')
    (by rw [abs_of_nonneg hRt0]; nlinarith) hu hτ₀
  rw [abs_of_nonneg hRt0, abs_sub_comm] at hd
  have h3 := abs_sub_abs_le_abs_sub (dec (M.div R (M.ofNat 2))) (dec R / dec (M.ofNat 2))
  rw [abs_of_nonneg hRt0] at h3
  nlinarith [mul_le_mul_of_nonneg_left hRt hu, mul_nonneg (mul_nonneg hu hu) hR]

/-- The child's tolerance $e'$ and window $r'$, the half window $s$ and the terms
$\kappa = e'/3$, $\rho = e'(r' + R_0)$ of the budget of a node, against $w = 1/\ell$. -/
private theorem node_budget_params {ε w R R₀ u τ e' r' κ ρ s : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8)
    (hw0 : 0 < w) (hw20 : w ≤ 1 / 20) (hR : 0 ≤ R) (hR₀ : 0 ≤ R₀) (hu : 0 ≤ u)
    (hu' : u * 1000000 ≤ ε * w) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1 / 4) (hτR : τ * 4 ≤ ε * R₀)
    (he'₁ : (1 - w) * (1 - 9 * u) * ε - u * τ ≤ e') (he'₂ : e' ≤ (1 - w) * ε + 7 * u * ε + u * τ)
    (hr'₀ : 0 ≤ r') (hr' : r' ≤ (1 / 2 + 2 * w) * (1 + 22 * u) * R + u * τ) (hκ : κ = e' / 3)
    (hs : s = R / 2 + 2 * u * R + u * τ) (hρ : ρ = e' * (r' + R₀)) :
    0 ≤ e' ∧ e' ≤ ε * (1 - w + 2 * w / 1000000) ∧ 0 ≤ κ ∧ κ ≤ 1 / 24 ∧ 0 ≤ ρ ∧ 0 ≤ s ∧
      ρ ≤ ε * (1 - w + 2 * w / 1000000) * ((1 / 2 + 2 * w + 2 * w / 1000000) * R +
        ε * w * R₀ / 10000000 + R₀) ∧
      s * (2 * κ + κ ^ 2) ≤ ((1 / 2 + w / 1000000) * R + ε * w * R₀ / 10000000) *
        (49 / 72 * (ε * (1 - w + 2 * w / 1000000))) ∧
      r' + ρ ≤ 6751 / 10000 * R + 1251 / 10000 * R₀ ∧ s ≤ 5001 / 10000 * R + R₀ / 10000 ∧
      u * R * 1000000 ≤ ε * w * R := by
  have hεw1 : ε * w ≤ 1 / 160 := by linarith [mul_le_mul hε₁ hw20 hw0.le (by norm_num)]
  have huτ : u * τ ≤ u / 4 := by linarith [mul_le_mul_of_nonneg_left hτ hu]
  have hεwR0 : 0 ≤ ε * w * R₀ := by positivity
  have hεwR : 0 ≤ ε * w * R := by positivity
  have hwR0 : 0 ≤ w * R := by positivity
  have huR0 : 0 ≤ u * R := by positivity
  have huτ0 : 0 ≤ u * τ := by positivity
  have huτR : u * τ * 10000000 ≤ ε * w * R₀ := by
    have h1 : u * τ * 4 ≤ u * (ε * R₀) := by linarith [mul_le_mul_of_nonneg_left hτR hu]
    have h2 := mul_le_mul_of_nonneg_right hu' (by positivity : 0 ≤ ε * R₀)
    have h3 := mul_le_mul_of_nonneg_left hε₁ (by positivity : 0 ≤ ε * w * R₀)
    linarith
  have huR : u * R * 1000000 ≤ ε * w * R := by linarith [mul_le_mul_of_nonneg_right hu' hR]
  have hεwR8 : ε * w * R ≤ w * R / 8 := by
    linarith [mul_le_mul_of_nonneg_right hε₁ (mul_nonneg hw0.le hR)]
  have hwuR : w * (u * R) ≤ u * R / 20 := by
    linarith [mul_le_mul_of_nonneg_right hw20 (mul_nonneg hu hR)]
  have hwR : w * R ≤ R / 20 := by linarith [mul_le_mul_of_nonneg_right hw20 hR]
  have hεwR₀ : ε * w * R₀ ≤ R₀ / 160 := by linarith [mul_le_mul_of_nonneg_right hεw1 hR₀]
  set E := ε * (1 - w + 2 * w / 1000000) with hE
  have hE' : e' ≤ E := by
    rw [hE]; linarith [mul_le_mul_of_nonneg_left hε₁ (by linarith : 0 ≤ 7 * u)]
  have he'0 : 0 ≤ e' := by
    have h1 : (1 / 2 : ℝ) ≤ (1 - w) * (1 - 9 * u) := by linarith [mul_nonneg hw0.le hu]
    linarith [mul_le_mul_of_nonneg_right h1 hε.le]
  have hE1 : E ≤ ε := by
    rw [hE]; linarith [mul_le_mul_of_nonneg_left (by linarith : 1 - w + 2 * w / 1000000 ≤ 1) hε.le]
  have hκ0 : 0 ≤ κ := by rw [hκ]; linarith
  have hκ1 : κ ≤ 1 / 24 := by rw [hκ]; linarith
  set Rr := (1 / 2 + 2 * w + 2 * w / 1000000) * R + ε * w * R₀ / 10000000 with hRr
  have hr'R : r' ≤ Rr := by rw [hRr]; linarith
  set Sb := (1 / 2 + w / 1000000) * R + ε * w * R₀ / 10000000 with hSb
  have hsS : s ≤ Sb := by rw [hs, hSb]; linarith
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hRR : 0 ≤ Rr + R₀ := by linarith [hr'₀.trans hr'R]
  have hρE : ρ ≤ E * (Rr + R₀) := by
    rw [hρ]; exact mul_le_mul hE' (by linarith) (by positivity) (he'0.trans hE')
  have hκ2 : 2 * κ + κ ^ 2 ≤ 49 / 72 * E := by
    linarith [mul_le_mul_of_nonneg_left hκ1 hκ0, sq κ]
  have hrρ : r' + ρ ≤ 6751 / 10000 * R + 1251 / 10000 * R₀ := by
    have h1 : E * (Rr + R₀) ≤ ε * (Rr + R₀) := mul_le_mul_of_nonneg_right hE1 hRR
    have h2 := mul_le_mul_of_nonneg_right hε₁ hRR
    have hRr6 : Rr ≤ 6000001 / 10000000 * R + R₀ / 1000000000 := by rw [hRr]; linarith
    linarith
  exact ⟨he'0, hE', hκ0, hκ1, by rw [hρ]; positivity, hs0, hρE,
    mul_le_mul hsS hκ2 (by positivity) (hs0.trans hsS), hrρ, by linarith, huR⟩

/-- The deflation, product and eigenvalue errors of the budget of a node, against $w = 1/\ell$. -/
private theorem node_budget_errors {ε w R R₀ u v τ η κ ρ s γ ξ Dn θ : ℝ} (hε : 0 < ε)
    (hε₁ : ε ≤ 1 / 8) (hw0 : 0 < w) (hw20 : w ≤ 1 / 20) (hR : 0 ≤ R) (hR₀ : 0 ≤ R₀)
    (hu : 0 ≤ u) (hu' : u * 1000000 ≤ ε * w) (hv : 0 ≤ v) (hv' : v * 100000 ≤ ε * w)
    (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1 / 4) (hτR : τ * 4 ≤ ε * R₀) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 24)
    (hs0 : 0 ≤ s) (hsb : s ≤ 5001 / 10000 * R + R₀ / 10000) (hρ0 : 0 ≤ ρ)
    (hρb : ρ ≤ 6751 / 10000 * R + 1251 / 10000 * R₀) (hη : η = (1 - w) * ε * w / 5)
    (hγ : γ = (2 + 2 * η) * R * η) (hξ : ξ = η * (1 + κ) + v * ((1 + η) * (1 + κ) + τ))
    (hDn : Dn = ρ / (1 - κ) ^ 2) (hθ : θ = u * (Dn + s + τ)) :
    0 ≤ η ∧ γ ≤ 4005 / 10000 * (ε * w * R) ∧ 0 ≤ ξ ∧ ξ ≤ 2084 / 10000 * (ε * w) ∧ 0 ≤ Dn ∧
      Dn ≤ 7352 / 10000 * R + 1363 / 10000 * R₀ ∧ 0 ≤ θ ∧
      (1 + κ) ^ 2 * θ ≤ ε * w * (R + R₀) / 100000 ∧
      ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ) ≤
        4345 / 10000 * (ε * w) * (12355 / 10000 * R + 1366 / 10000 * R₀) := by
  have hεw1 : ε * w ≤ 1 / 160 := by linarith [mul_le_mul hε₁ hw20 hw0.le (by norm_num)]
  have hεww : 0 ≤ ε * w * w := by positivity
  have hη0 : 0 ≤ η := by
    rw [hη]; exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) hε.le) hw0.le) (by norm_num)
  have hηw : η ≤ ε * w / 5 := by rw [hη]; linarith
  have hη1 : η ≤ 1 / 800 := by linarith
  have hγ' : γ ≤ 4005 / 10000 * (ε * w * R) := by
    rw [hγ]
    have h1 := mul_le_mul_of_nonneg_left hηw hR
    have h2 := mul_le_mul_of_nonneg_left hη1 (mul_nonneg hR hη0)
    linarith
  have hξ0 : 0 ≤ ξ := by rw [hξ]; positivity
  have hξ' : ξ ≤ 2084 / 10000 * (ε * w) := by
    rw [hξ]
    have h1 : η * (1 + κ) ≤ ε * w / 5 * (25 / 24) :=
      mul_le_mul hηw (by linarith) (by linarith) (by positivity)
    have h2 : (1 + η) * (1 + κ) ≤ (1 + 1 / 800) * (25 / 24) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    have h3 := mul_le_mul_of_nonneg_left (by linarith : (1 + η) * (1 + κ) + τ ≤ 1.31) hv
    linarith
  have hκd : (23 / 24 : ℝ) ^ 2 ≤ (1 - κ) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hDn0 : 0 ≤ Dn := by rw [hDn]; exact div_nonneg hρ0 (sq_nonneg _)
  have hDn' : Dn ≤ 7352 / 10000 * R + 1363 / 10000 * R₀ := by
    rw [hDn, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hκd)]
    have := mul_le_mul_of_nonneg_left hκd (by positivity : 0 ≤ 7352 / 10000 * R + 1363 / 10000 * R₀)
    linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact mul_nonneg hu (by linarith)
  have hεwR0 : 0 ≤ ε * w * R₀ := by positivity
  have hεwR : 0 ≤ ε * w * R := by positivity
  have hτR₀ : τ ≤ R₀ / 32 := by linarith [mul_le_mul_of_nonneg_right hε₁ hR₀]
  have hθ' : θ * 1000000 ≤ ε * w * (124 / 100 * R + 17 / 100 * R₀) := by
    rw [hθ]
    have h1 : Dn + s + τ ≤ 124 / 100 * R + 17 / 100 * R₀ := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hu
    have h3 := mul_le_mul_of_nonneg_right hu'
      (by positivity : (0 : ℝ) ≤ 124 / 100 * R + 17 / 100 * R₀)
    linarith
  have hθ1 : θ ≤ R / 10000 + R₀ / 10000 := by
    linarith [mul_le_mul_of_nonneg_right hεw1 hR, mul_le_mul_of_nonneg_right hεw1 hR₀]
  have hκ3 : (1 + κ) ^ 2 ≤ 625 / 576 := by
    have := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + κ) (by linarith : 1 + κ ≤ 25 / 24) 2
    norm_num at this ⊢; linarith
  have hT2 : ξ * (2 * (1 + κ) + ξ) ≤ 4345 / 10000 * (ε * w) := by
    have := mul_le_mul hξ' (by linarith : 2 * (1 + κ) + ξ ≤ 2.0848) (by linarith) (by positivity)
    linarith
  refine ⟨hη0, hγ', hξ0, hξ', hDn0, hDn', hθ0, by linarith [mul_le_mul_of_nonneg_right hκ3 hθ0],
    mul_le_mul hT2 (by linarith) (by linarith) (by positivity)⟩

/-- The residual and singular-value budget of a node (pure real arithmetic). -/
private theorem node_budget {ε x R R₀ u v τ e' r' η κ s ρ γ ξ Dn θ ε₀ : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8) (hx : 20 ≤ x) (hR : 0 ≤ R) (hR₀ : 0 ≤ R₀)
    (hu : 0 ≤ u) (hux : x * u * 1000000 ≤ ε) (hv : 0 ≤ v) (hvx : x * v * 100000 ≤ ε)
    (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1 / 4) (hτR : τ * 4 ≤ ε * R₀)
    (he'₁ : (1 - 1 / x) * (1 - 9 * u) * ε - u * τ ≤ e')
    (he'₂ : e' ≤ (1 - 1 / x) * ε + 7 * u * ε + u * τ)
    (hr'₀ : 0 ≤ r') (hr' : r' ≤ (1 / 2 + 2 / x) * (1 + 22 * u) * R + u * τ)
    (hη : η = (1 - 1 / x) * ε / (5 * x)) (hκ : κ = e' / 3) (hs : s = R / 2 + 2 * u * R + u * τ)
    (hρ : ρ = e' * (r' + R₀)) (hγ : γ = (2 + 2 * η) * R * η)
    (hξ : ξ = η * (1 + κ) + v * ((1 + η) * (1 + κ) + τ)) (hDn : Dn = (r' + ρ) / (1 - κ) ^ 2)
    (hθ : θ = u * (Dn + s + τ)) (hε₀ : ε₀ = u * (R + s + τ)) :
    0 ≤ κ ∧ κ < 1 ∧ 0 ≤ ξ ∧ 0 ≤ θ ∧ 0 ≤ ρ ∧ 0 ≤ Dn ∧ 0 ≤ s ∧ Dn + s ≤ 2 * R + R₀ ∧
    κ + √2 * ξ ≤ ε / 3 ∧
    γ + ρ + s * (2 * κ + κ ^ 2) +
        2 * ((1 + κ) ^ 2 * θ + ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ)) ≤ ε * (R + R₀) ∧
    ε₀ + ρ + s * (2 * κ + κ ^ 2) + (1 + κ) ^ 2 * θ ≤ ε * (R + R₀) := by
  -- the depth parameter $w = 1/x$
  obtain ⟨w, hw_def⟩ : ∃ w, w = 1 / x := ⟨_, rfl⟩
  have hx0 : 0 < x := by linarith
  have hwx : w * x = 1 := by rw [hw_def]; field_simp
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw20 : w ≤ 1 / 20 := by rw [hw_def, div_le_div_iff₀ hx0 (by norm_num)]; linarith
  rw [← hw_def] at he'₁ he'₂
  rw [show 2 / x = 2 * w by rw [hw_def]; ring] at hr'
  have hu' : u * 1000000 ≤ ε * w := by
    have := mul_le_mul_of_nonneg_left hux hw0.le
    rw [show w * (x * u * 1000000) = (w * x) * u * 1000000 by ring, hwx] at this; linarith
  have hv' : v * 100000 ≤ ε * w := by
    have := mul_le_mul_of_nonneg_left hvx hw0.le
    rw [show w * (x * v * 100000) = (w * x) * v * 100000 by ring, hwx] at this; linarith
  obtain ⟨he'0, hE', hκ0, hκ1, hρ0, hs0, hρE, hsκ, hrρ, hsb, huR⟩ := node_budget_params hε hε₁
    hw0 hw20 hR hR₀ hu hu' hτ₀ hτ hτR he'₁ he'₂ hr'₀ hr' hκ hs hρ
  obtain ⟨hη0, hγ', hξ0, hξ', hDn0, hDn', hθ0, hT1, hT3⟩ := node_budget_errors hε hε₁ hw0 hw20
    hR hR₀ hu hu' hv hv' hτ₀ hτ hτR hκ0 hκ1 hs0 hsb (by linarith) hrρ
    (by rw [hη, hw_def]; field_simp) hγ hξ hDn hθ
  have hsq2 : √2 ≤ 1.4143 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hεR : 0 ≤ ε * R := by positivity
  have hεR₀ : 0 ≤ ε * R₀ := by positivity
  have hεw : 0 ≤ ε * w := by positivity
  have hww : 0 ≤ w * w := by positivity
  have hεww : 0 ≤ ε * w * w := by positivity
  have hεw8 : ε * w ≤ w / 8 := by linarith [mul_le_mul_of_nonneg_right hε₁ hw0.le]
  have hεwR0 : 0 ≤ ε * w * R₀ := by positivity
  have hεwR : 0 ≤ ε * w * R := by positivity
  have hτR₀ : τ ≤ R₀ / 32 := by linarith [mul_le_mul_of_nonneg_right hε₁ hR₀]
  refine ⟨hκ0, by linarith, hξ0, hθ0, hρ0, hDn0, hs0, by linarith, ?_, ?_, ?_⟩
  · linarith [mul_le_mul hsq2 hξ' hξ0 (by norm_num)]
  · -- the residual of a split
    have h1 := mul_le_mul_of_nonneg_left (show (1 - w + 2 * w / 1000000) *
        (1 / 2 + 2 * w + 2 * w / 1000000) + 49 / 72 * (1 - w + 2 * w / 1000000) *
        (1 / 2 + w / 1000000) + (4005 / 10000 + 2 / 100000 + 2 * (4345 / 10000) *
        (12355 / 10000)) * w ≤ 1 by linarith) hεR
    have h2 := mul_le_mul_of_nonneg_left (show (1 - w + 2 * w / 1000000) *
        (ε * w / 10000000 + 1) + 49 / 72 * (1 - w + 2 * w / 1000000) *
        (ε * w / 10000000) + (2 / 100000 + 2 * (4345 / 10000) * (1366 / 10000)) * w ≤ 1 by
        linarith) hεR₀
    linarith
  · -- the residual of a shift
    have hε₀' : ε₀ ≤ ε * w * (R + R₀) / 100000 := by
      rw [hε₀]
      have h2 := mul_le_mul_of_nonneg_left (by linarith : R + s + τ ≤ 2 * R + R₀) hu
      have h3 := mul_le_mul_of_nonneg_right hu' (by positivity : (0 : ℝ) ≤ 2 * R + R₀)
      linarith
    have h1 := mul_le_mul_of_nonneg_left (show (1 - w + 2 * w / 1000000) *
        (1 / 2 + 2 * w + 2 * w / 1000000) + 49 / 72 * (1 - w + 2 * w / 1000000) *
        (1 / 2 + w / 1000000) + (2 / 100000) * w ≤ 1 by linarith) hεR
    have h2 := mul_le_mul_of_nonneg_left (show (1 - w + 2 * w / 1000000) *
        (ε * w / 10000000 + 1) + 49 / 72 * (1 - w + 2 * w / 1000000) *
        (ε * w / 10000000) + (2 / 100000) * w ≤ 1 by linarith) hεR₀
    linarith

open scoped ComplexOrder in
/-- Reindexing the columns of an approximate diagonalization. -/
private theorem isApproxDiagonalization_submatrix {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {A : Matrix m m ℂ} {U : Matrix m n ℂ} {d : n → ℝ} (e : m ≃ n)
    {η κ : ℝ} (h1 : specNorm (A - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) ≤ η)
    (h2 : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ Uᴴ * U)
    (h3 : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ)) :
    IsApproxDiagonalization A (U.submatrix id e) (fun i => d (e i)) η κ := by
  have hD : Matrix.diagonal (fun i => ((d (e i) : ℝ) : ℂ)) =
      (Matrix.diagonal (fun i => (d i : ℂ))).submatrix e e := by
    rw [Matrix.submatrix_diagonal_equiv]; rfl
  have hG : (U.submatrix id e)ᴴ * U.submatrix id e = (Uᴴ * U).submatrix e e := by
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
  have hsub : ∀ c : ℝ, (c • (1 : Matrix n n ℂ)).submatrix e e = c • (1 : Matrix m m ℂ) := by
    intro c; ext i j; simp [Matrix.one_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [hD, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    simpa using h1
  · have := (Matrix.le_iff.mp h2).submatrix e
    rw [hG, ← hsub, Matrix.le_iff]
    convert this using 1
    rfl
  · have := (Matrix.le_iff.mp h3).submatrix e
    rw [hG, ← hsub, Matrix.le_iff]
    convert this using 1
    rfl

/-- Sandwich bound. -/
private theorem specNorm_mul_mul_conjTranspose_le_sq_mul {m n : Type*} [Fintype m] [Fintype n]
    {U : Matrix m n ℂ} {M : Matrix n n ℂ} {b : ℝ} (hU : specNorm U ≤ b) :
    specNorm (U * M * Uᴴ) ≤ b ^ 2 * specNorm M := by
  have hb : 0 ≤ b := (specNorm_nonneg U).trans hU
  calc specNorm (U * M * Uᴴ) ≤ specNorm U * specNorm M * specNorm Uᴴ :=
        (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _)
          (specNorm_nonneg _))
    _ ≤ b * specNorm M * b := by
        rw [specNorm_conjTranspose]
        gcongr
    _ = b ^ 2 * specNorm M := by ring

/-- Diagonal shift identity. -/
private theorem diagonal_add_smul_one_sub_diagonal {n : Type*} [DecidableEq n] (d e : n → ℝ)
    (σ : ℝ) :
    Matrix.diagonal (fun i => (d i : ℂ)) + σ • (1 : Matrix n n ℂ) -
        Matrix.diagonal (fun i => (e i : ℂ)) =
      Matrix.diagonal (fun i => ((d i + σ - e i : ℝ) : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

/-- Generic Loewner perturbation of a Gram matrix. -/
private theorem smul_one_le_and_le_smul_one_add {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq k]
    {G X : Matrix m k ℂ} {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hac : 0 ≤ a - c)
    (h₁ : a ^ 2 • (1 : Matrix k k ℂ) ≤ Gᴴ * G) (h₂ : Gᴴ * G ≤ b ^ 2 • (1 : Matrix k k ℂ))
    (hX : specNorm X ≤ c) :
    (a - c) ^ 2 • (1 : Matrix k k ℂ) ≤ (G + X)ᴴ * (G + X) ∧
      (G + X)ᴴ * (G + X) ≤ (b + c) ^ 2 • (1 : Matrix k k ℂ) := by
  have ha : 0 ≤ a := by linarith
  constructor
  · rw [smul_one_le_conjTranspose_mul_self_iff]
    rw [smul_one_le_conjTranspose_mul_self_iff] at h₁
    intro x
    have hG : a * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (G *ᵥ x)‖ := by
      have := h₁ x
      rw [← mul_pow] at this
      exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 this
    have hXx := (specNorm_le_iff hc).1 hX x
    have e : WithLp.toLp 2 (G *ᵥ x) =
        WithLp.toLp 2 ((G + X) *ᵥ x) - WithLp.toLp 2 (X *ᵥ x) := by
      rw [Matrix.add_mulVec, WithLp.toLp_add]; abel
    have ht := norm_sub_le (WithLp.toLp 2 ((G + X) *ᵥ x)) (WithLp.toLp 2 (X *ᵥ x))
    rw [← e] at ht
    have hl : (a - c) * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 ((G + X) *ᵥ x)‖ := by nlinarith
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hl 2
  · have hG : specNorm G ≤ b :=
      (sq_le_sq₀ (specNorm_nonneg _) hb).1
        ((specNorm_sq_le_iff_conjTranspose_mul_self_le (by positivity)).2 h₂)
    rw [← specNorm_sq_le_iff_conjTranspose_mul_self_le (by positivity)]
    exact pow_le_pow_left₀ (specNorm_nonneg _)
      ((specNorm_add_le _ _).trans (add_le_add hG hX)) 2

/-- (B') A Loewner upper bound on the Gram matrix bounds the spectral norm. -/
private theorem specNorm_le_of_conjTranspose_mul_self_le {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] {U : Matrix m n ℂ} {κ : ℝ} (hκ : 0 ≤ κ)
    (h : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ)) : specNorm U ≤ 1 + κ := by
  have h' := (specNorm_sq_le_iff_conjTranspose_mul_self_le (by positivity)).2 h
  exact (sq_le_sq₀ (specNorm_nonneg _) (by positivity)).1 h'

/-- (B) Near-unitary square matrix: `‖1 - U Uᴴ‖ ≤ 2κ + κ²`. -/
private theorem specNorm_one_sub_mul_conjTranspose_le {n : Type*} [Fintype n]
    [DecidableEq n] {U : Matrix n n ℂ} {κ : ℝ} (hκ : 0 ≤ κ)
    (h₁ : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ Uᴴ * U)
    (h₂ : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ)) :
    specNorm (1 - U * Uᴴ) ≤ 2 * κ + κ ^ 2 := by
  have hn : specNorm U ≤ 1 + κ := specNorm_le_of_conjTranspose_mul_self_le hκ h₂
  have h1 : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ U * Uᴴ :=
    smul_one_le_mul_conjTranspose_self_of_smul_one_le h₁
  have h2 : U * Uᴴ ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ) := by
    have := conjTranspose_mul_self_le_specNorm_sq_smul_one Uᴴ
    rw [Matrix.conjTranspose_conjTranspose, specNorm_conjTranspose] at this
    refine this.trans (smul_one_le_smul_one ?_)
    exact pow_le_pow_left₀ (specNorm_nonneg _) hn 2
  have hH : (1 - U * Uᴴ).IsHermitian := by
    refine Matrix.IsHermitian.sub (Matrix.isHermitian_one) ?_
    simpa using Matrix.isHermitian_mul_conjTranspose_self U
  refine hH.specNorm_le_of_le_smul_one (by positivity) ?_ ?_
  · rw [Matrix.le_iff] at h2 ⊢
    convert h2 using 1
    rw [show (1 + κ) ^ 2 = 1 + (2 * κ + κ ^ 2) by ring]
    simp only [add_smul, one_smul]
    abel
  · have h3 : (1 - (2 * κ + κ ^ 2)) • (1 : Matrix n n ℂ) ≤ U * Uᴴ :=
      (smul_one_le_smul_one (by nlinarith)).trans h1
    rw [Matrix.le_iff] at h3 ⊢
    convert h3 using 1
    rw [sub_smul, one_smul]
    abel

/-- (A) The diagonal of an approximate diagonalization is bounded by the norm. -/
private theorem abs_le_specNorm_mul_diagonal_mul_div {n : Type*} [Fintype n]
    [DecidableEq n] {U : Matrix n n ℂ} {d : n → ℝ} {κ : ℝ} (hκ1 : κ < 1)
    (hU : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ Uᴴ * U) (i : n) :
    |d i| ≤ specNorm (U * Matrix.diagonal (fun j => (d j : ℂ)) * Uᴴ) / (1 - κ) ^ 2 := by
  set D := Matrix.diagonal (fun j => (d j : ℂ)) with hD
  have hc : 0 ≤ 1 - κ := by linarith
  have h1 := mul_specNorm_le_of_sq_smul_one_le hc hU (D * Uᴴ)
  have h2 := mul_specNorm_le_of_sq_smul_one_le hc hU Dᴴ
  have e : specNorm (D * Uᴴ) = specNorm (U * Dᴴ) := by
    rw [← specNorm_conjTranspose (D * Uᴴ), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  rw [specNorm_conjTranspose] at h2
  have h3 : |d i| ≤ specNorm D := by
    have := norm_apply_le_specNorm D i i
    simpa [hD] using this
  rw [le_div_iff₀ (by positivity), Matrix.mul_assoc]
  rw [e] at h1
  nlinarith [mul_le_mul_of_nonneg_left h3 hc, mul_le_mul_of_nonneg_left h2 hc]

/-- (S) The residual of a shift node. -/
private theorem specNorm_sub_mul_diagonal_mul_conjTranspose_le {n : Type*} [Fintype n]
    [DecidableEq n] {A A' U : Matrix n n ℂ} {d e : n → ℝ} {σ s κ ρ θ ε₀ : ℝ}
    (hσ : |σ| ≤ s) (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (hU₁ : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ Uᴴ * U)
    (hU₂ : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ))
    (hA' : specNorm ((A - σ • (1 : Matrix n n ℂ)) - A') ≤ ε₀)
    (hF : specNorm (A' - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) ≤ ρ)
    (he : ∀ i, |e i - (d i + σ)| ≤ θ) :
    specNorm (A - U * Matrix.diagonal (fun i => (e i : ℂ)) * Uᴴ) ≤
      ε₀ + ρ + s * (2 * κ + κ ^ 2) + (1 + κ) ^ 2 * θ := by
  have hn : specNorm U ≤ 1 + κ := specNorm_le_of_conjTranspose_mul_self_le hκ hU₂
  have hB := specNorm_one_sub_mul_conjTranspose_le hκ hU₁ hU₂
  set D := Matrix.diagonal (fun i => (d i : ℂ))
  set E := Matrix.diagonal (fun i => (e i : ℂ))
  have key : A - U * E * Uᴴ = ((A - σ • (1 : Matrix n n ℂ)) - A') + (A' - U * D * Uᴴ) +
      σ • (1 - U * Uᴴ) + U * (D + σ • (1 : Matrix n n ℂ) - E) * Uᴴ := by
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, smul_sub]
    abel
  have hT : specNorm (U * (D + σ • (1 : Matrix n n ℂ) - E) * Uᴴ) ≤ (1 + κ) ^ 2 * θ := by
    refine (specNorm_mul_mul_conjTranspose_le_sq_mul hn).trans ?_
    gcongr
    rw [diagonal_add_smul_one_sub_diagonal]
    refine specNorm_diagonal_le hθ fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact he i
  have hσ' : specNorm (σ • (1 - U * Uᴴ)) ≤ s * (2 * κ + κ ^ 2) := by
    rw [specNorm_real_smul]
    exact mul_le_mul hσ hB (specNorm_nonneg _) ((abs_nonneg σ).trans hσ)
  rw [key]
  refine (specNorm_add_le _ _).trans ?_
  refine add_le_add ?_ hT
  refine (specNorm_add_le _ _).trans ?_
  refine add_le_add ?_ hσ'
  exact (specNorm_add_le _ _).trans (add_le_add hA' hF)

/-- Perturbation of a congruence. -/
private theorem specNorm_mul_mul_conjTranspose_sub_le {m p : Type*} [Fintype m] [Fintype p]
    {G V : Matrix m p ℂ} {D' E : Matrix p p ℂ} {b ξ θ M : ℝ}
    (hG : specNorm G ≤ b) (hV : specNorm (V - G) ≤ ξ) (hDE : specNorm (D' - E) ≤ θ)
    (hE : specNorm E ≤ M) :
    specNorm (G * D' * Gᴴ - V * E * Vᴴ) ≤ b ^ 2 * θ + ξ * (2 * b + ξ) * M := by
  have hb : 0 ≤ b := (specNorm_nonneg _).trans hG
  have hξ : 0 ≤ ξ := (specNorm_nonneg _).trans hV
  have hM : 0 ≤ M := (specNorm_nonneg _).trans hE
  have key : G * D' * Gᴴ - V * E * Vᴴ =
      G * (D' - E) * Gᴴ - ((V - G) * E * Gᴴ + V * E * (V - G)ᴴ) := by
    simp only [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hVn : specNorm V ≤ b + ξ := by
    have : V = G + (V - G) := by abel
    rw [this]; exact (specNorm_add_le _ _).trans (add_le_add hG hV)
  have h1 := specNorm_mul_mul_conjTranspose_le_sq_mul (M := D' - E) hG
  have h2 : specNorm ((V - G) * E * Gᴴ) ≤ ξ * M * b := by
    calc specNorm ((V - G) * E * Gᴴ) ≤ specNorm (V - G) * specNorm E * specNorm Gᴴ :=
          (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _)
            (specNorm_nonneg _))
      _ ≤ ξ * M * b := by
          rw [specNorm_conjTranspose]
          gcongr
  have h3 : specNorm (V * E * (V - G)ᴴ) ≤ (b + ξ) * M * ξ := by
    calc specNorm (V * E * (V - G)ᴴ) ≤ specNorm V * specNorm E * specNorm (V - G)ᴴ :=
          (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _)
            (specNorm_nonneg _))
      _ ≤ (b + ξ) * M * ξ := by
          rw [specNorm_conjTranspose]
          gcongr
  rw [key]
  refine (specNorm_sub_le _ _).trans ?_
  have := (specNorm_add_le ((V - G) * E * Gᴴ) (V * E * (V - G)ᴴ))
  have h1' : b ^ 2 * specNorm (D' - E) ≤ b ^ 2 * θ := by gcongr
  nlinarith

/-- One block of the assembled residual: replacing $\mathbf{Z}\mathbf{U}$ by $\mathbf{V}$ and
the shifted eigenvalues $d_i + \sigma$ by $e_i$. -/
private theorem specNorm_mul_diagonal_mul_conjTranspose_sub_le {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq p] {Z : Matrix m p ℂ} {U : Matrix p p ℂ} {V : Matrix m p ℂ}
    {d e : p → ℝ} {σ s κ ξ θ Dn : ℝ} (hZ : HasOrthonormalCols Z) (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (hσ : |σ| ≤ s) (hDn : 0 ≤ Dn) (hU₂ : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix p p ℂ))
    (hV : specNorm (V - Z * U) ≤ ξ) (hd : ∀ i, |d i| ≤ Dn) (he : ∀ i, |e i - (d i + σ)| ≤ θ) :
    specNorm ((Z * U) * Matrix.diagonal (fun i => ((d i + σ : ℝ) : ℂ)) * (Z * U)ᴴ -
      V * Matrix.diagonal (fun i => (e i : ℂ)) * Vᴴ) ≤
        (1 + κ) ^ 2 * θ + ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ) := by
  have hs : 0 ≤ s := (abs_nonneg _).trans hσ
  refine specNorm_mul_mul_conjTranspose_sub_le ?_ hV ?_ ?_
  · rw [hZ.specNorm_mul_left]; exact specNorm_le_of_conjTranspose_mul_self_le hκ hU₂
  · have : Matrix.diagonal (fun i => ((d i + σ : ℝ) : ℂ)) - Matrix.diagonal (fun i => (e i : ℂ)) =
        Matrix.diagonal (fun i => ((d i + σ - e i : ℝ) : ℂ)) := by
      ext i j; by_cases h : i = j
      · subst h; simp
      · simp [Matrix.diagonal_apply_ne _ h]
    rw [this]
    refine specNorm_diagonal_le hθ fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]; exact he i
  · refine specNorm_diagonal_le (by positivity) fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 := he i; have h2 := hd i
    rw [abs_le] at h1 h2 hσ ⊢; constructor <;> linarith

/-- The residual of an assembled split: the blocks of $\mathbf{A}$ in the frames
$\mathbf{Z}_\pm$ against the children's diagonalizations, through the computed bases
$\mathbf{V}_\pm$. -/
private theorem specNorm_sub_fromCols_mul_diagonal_le {m p q : Type*} [Fintype m]
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {A : Matrix m m ℂ} {Zp : Matrix m p ℂ} {Zm : Matrix m q ℂ}
    (hZp : HasOrthonormalCols Zp) (hZm : HasOrthonormalCols Zm) (hZpm : Zpᴴ * Zm = 0)
    (hA : A = Zp * (Zpᴴ * A * Zp) * Zpᴴ + Zm * (Zmᴴ * A * Zm) * Zmᴴ)
    {Ap Up : Matrix p p ℂ} {Am Um : Matrix q q ℂ} {Vp : Matrix m p ℂ} {Vm : Matrix m q ℂ}
    {dp ep : p → ℝ} {dm em : q → ℝ} {σp σm s γ ρ κ ξ θ Dn : ℝ}
    (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) (hσp : |σp| ≤ s) (hσm : |σm| ≤ s) (hDn : 0 ≤ Dn)
    (hCp : specNorm (Ap - (Zpᴴ * A * Zp - σp • (1 : Matrix p p ℂ))) ≤ γ)
    (hCm : specNorm (Am - (Zmᴴ * A * Zm - σm • (1 : Matrix q q ℂ))) ≤ γ)
    (hFp : specNorm (Ap - Up * Matrix.diagonal (fun i => (dp i : ℂ)) * Upᴴ) ≤ ρ)
    (hFm : specNorm (Am - Um * Matrix.diagonal (fun i => (dm i : ℂ)) * Umᴴ) ≤ ρ)
    (hUp₁ : (1 - κ) ^ 2 • (1 : Matrix p p ℂ) ≤ Upᴴ * Up)
    (hUp₂ : Upᴴ * Up ≤ (1 + κ) ^ 2 • (1 : Matrix p p ℂ))
    (hUm₁ : (1 - κ) ^ 2 • (1 : Matrix q q ℂ) ≤ Umᴴ * Um)
    (hUm₂ : Umᴴ * Um ≤ (1 + κ) ^ 2 • (1 : Matrix q q ℂ))
    (hVp : specNorm (Vp - Zp * Up) ≤ ξ) (hVm : specNorm (Vm - Zm * Um) ≤ ξ)
    (hdp : ∀ i, |dp i| ≤ Dn) (hdm : ∀ i, |dm i| ≤ Dn)
    (hep : ∀ i, |ep i - (dp i + σp)| ≤ θ) (hem : ∀ i, |em i - (dm i + σm)| ≤ θ) :
    specNorm (A - Matrix.fromCols Vp Vm *
        Matrix.diagonal (fun i => ((Sum.elim ep em i : ℝ) : ℂ)) * (Matrix.fromCols Vp Vm)ᴴ) ≤
      γ + ρ + s * (2 * κ + κ ^ 2) +
        2 * ((1 + κ) ^ 2 * θ + ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ)) := by
  have hs : 0 ≤ s := (abs_nonneg _).trans hσp
  set Dp' := Matrix.diagonal (fun i => ((dp i + σp : ℝ) : ℂ))
  set Dm' := Matrix.diagonal (fun i => ((dm i + σm : ℝ) : ℂ))
  set Ep := Matrix.diagonal (fun i => (ep i : ℂ))
  set Em := Matrix.diagonal (fun i => (em i : ℂ))
  set Yp := Zpᴴ * A * Zp - Up * Dp' * Upᴴ
  set Ym := Zmᴴ * A * Zm - Um * Dm' * Umᴴ
  -- the blocks
  have hYp : specNorm Yp ≤ γ + ρ + s * (2 * κ + κ ^ 2) := by
    have := specNorm_sub_mul_diagonal_mul_conjTranspose_le (A := Zpᴴ * A * Zp)
      (e := fun i => dp i + σp)
      (θ := 0) (ε₀ := γ) hσp hκ le_rfl hUp₁ hUp₂ (by
        have h := specNorm_neg (Ap - (Zpᴴ * A * Zp - σp • (1 : Matrix _ _ ℂ)))
        rw [neg_sub] at h; rw [h]; exact hCp) hFp
      (fun i => by simp)
    exact (le_of_eq rfl).trans (this.trans (le_of_eq (by ring)))
  have hYm : specNorm Ym ≤ γ + ρ + s * (2 * κ + κ ^ 2) := by
    have := specNorm_sub_mul_diagonal_mul_conjTranspose_le (A := Zmᴴ * A * Zm)
      (e := fun i => dm i + σm)
      (θ := 0) (ε₀ := γ) hσm hκ le_rfl hUm₁ hUm₂ (by
        have h := specNorm_neg (Am - (Zmᴴ * A * Zm - σm • (1 : Matrix _ _ ℂ)))
        rw [neg_sub] at h; rw [h]; exact hCm) hFm
      (fun i => by simp)
    exact (le_of_eq rfl).trans (this.trans (le_of_eq (by ring)))
  set Z := Matrix.fromCols Zp Zm
  have hZ : HasOrthonormalCols Z := hasOrthonormalCols_fromCols_iff.mpr ⟨hZp, hZm, hZpm⟩
  have hblk : Zp * Yp * Zpᴴ + Zm * Ym * Zmᴴ = Z * Matrix.fromBlocks Yp 0 0 Ym * Zᴴ := by
    simp only [Z, Matrix.fromCols_mul_fromBlocks,
      Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows, Matrix.mul_zero, add_zero, zero_add]
  have hB : specNorm (Zp * Yp * Zpᴴ + Zm * Ym * Zmᴴ) ≤ γ + ρ + s * (2 * κ + κ ^ 2) := by
    rw [hblk, hZ.specNorm_mul_conjTranspose_right, hZ.specNorm_mul_left,
      specNorm_fromBlocks_zero₁₂_zero₂₁]
    exact max_le hYp hYm
  -- the T terms
  have hTp := specNorm_mul_diagonal_mul_conjTranspose_sub_le hZp hκ hθ hσp hDn hUp₂ hVp hdp hep
  have hTm := specNorm_mul_diagonal_mul_conjTranspose_sub_le hZm hκ hθ hσm hDn hUm₂ hVm hdm hem
  -- the decomposition
  have hE : Matrix.diagonal (fun i => ((Sum.elim ep em i : ℝ) : ℂ)) =
      Matrix.fromBlocks Ep 0 0 Em := by
    rw [Matrix.fromBlocks_diagonal]; congr 1; ext (i | i) <;> rfl
  have hCp' : Zpᴴ * A * Zp = Yp + Up * Dp' * Upᴴ := by simp [Yp]
  have hCm' : Zmᴴ * A * Zm = Ym + Um * Dm' * Umᴴ := by simp [Ym]
  have key : A - Matrix.fromCols Vp Vm *
        Matrix.diagonal (fun i => ((Sum.elim ep em i : ℝ) : ℂ)) * (Matrix.fromCols Vp Vm)ᴴ =
      (Zp * Yp * Zpᴴ + Zm * Ym * Zmᴴ) +
        ((Zp * Up) * Dp' * (Zp * Up)ᴴ - Vp * Ep * Vpᴴ) +
        ((Zm * Um) * Dm' * (Zm * Um)ᴴ - Vm * Em * Vmᴴ) := by
    rw [hE, Matrix.fromCols_mul_fromBlocks, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows]
    nth_rewrite 1 [hA]
    rw [hCp', hCm']
    simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.conjTranspose_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [key]
  have h1 := specNorm_add_le (Zp * Yp * Zpᴴ + Zm * Ym * Zmᴴ)
    ((Zp * Up) * Dp' * (Zp * Up)ᴴ - Vp * Ep * Vpᴴ)
  refine (specNorm_add_le _ _).trans ?_
  linarith

/-- (D) The singular values of the assembled basis, before reindexing. -/
private theorem smul_one_le_and_le_smul_one_fromCols {m p q : Type*} [Fintype m]
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {Zp : Matrix m p ℂ} {Zm : Matrix m q ℂ}
    (hZp : HasOrthonormalCols Zp) (hZm : HasOrthonormalCols Zm) (hZpm : Zpᴴ * Zm = 0)
    {Up : Matrix p p ℂ} {Um : Matrix q q ℂ} {Vp : Matrix m p ℂ} {Vm : Matrix m q ℂ}
    {κ ξ : ℝ} (hκ : 0 ≤ κ) (hξ : 0 ≤ ξ) (hκξ : κ + √2 * ξ ≤ 1)
    (hUp₁ : (1 - κ) ^ 2 • (1 : Matrix p p ℂ) ≤ Upᴴ * Up)
    (hUp₂ : Upᴴ * Up ≤ (1 + κ) ^ 2 • (1 : Matrix p p ℂ))
    (hUm₁ : (1 - κ) ^ 2 • (1 : Matrix q q ℂ) ≤ Umᴴ * Um)
    (hUm₂ : Umᴴ * Um ≤ (1 + κ) ^ 2 • (1 : Matrix q q ℂ))
    (hVp : specNorm (Vp - Zp * Up) ≤ ξ) (hVm : specNorm (Vm - Zm * Um) ≤ ξ) :
    (1 - (κ + √2 * ξ)) ^ 2 • (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ) ≤
        (Matrix.fromCols Vp Vm)ᴴ * Matrix.fromCols Vp Vm ∧
      (Matrix.fromCols Vp Vm)ᴴ * Matrix.fromCols Vp Vm ≤
        (1 + (κ + √2 * ξ)) ^ 2 • (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ) := by
  set Z := Matrix.fromCols Zp Zm
  have hZ : HasOrthonormalCols Z := hasOrthonormalCols_fromCols_iff.mpr ⟨hZp, hZm, hZpm⟩
  set B : Matrix (p ⊕ q) (p ⊕ q) ℂ := Matrix.fromBlocks Up 0 0 Um
  set G := Z * B
  set X := Matrix.fromCols (Vp - Zp * Up) (Vm - Zm * Um)
  have hGX : Matrix.fromCols Vp Vm = G + X := by
    simp only [G, X, Z, B, Matrix.fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, zero_add]
    ext i (j | j) <;> simp
  have hGG : Gᴴ * G = Matrix.fromBlocks (Upᴴ * Up) 0 0 (Umᴴ * Um) := by
    simp only [G, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Zᴴ, show Zᴴ * Z = 1 from hZ, Matrix.one_mul]
    simp only [B, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hblk : ∀ (r : ℝ), r • (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ) =
      Matrix.fromBlocks (r • (1 : Matrix p p ℂ)) 0 0 (r • (1 : Matrix q q ℂ)) := by
    intro r
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero, smul_zero]
  have h₁ : (1 - κ) ^ 2 • (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ) ≤ Gᴴ * G := by
    rw [hGG, hblk, Matrix.le_iff]
    rw [Matrix.le_iff] at hUp₁ hUm₁
    have := Matrix.PosSemidef.fromBlocks_zero₁₂_zero₂₁ hUp₁ hUm₁
    convert this using 1
    simp [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  have h₂ : Gᴴ * G ≤ (1 + κ) ^ 2 • (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ) := by
    rw [hGG, hblk, Matrix.le_iff]
    rw [Matrix.le_iff] at hUp₂ hUm₂
    have := Matrix.PosSemidef.fromBlocks_zero₁₂_zero₂₁ hUp₂ hUm₂
    convert this using 1
    simp [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  have hX : specNorm X ≤ √2 * ξ := by
    have h := specNorm_fromCols_sq_le (Vp - Zp * Up) (Vm - Zm * Um)
    have h' : specNorm X ^ 2 ≤ (√2 * ξ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      nlinarith [specNorm_nonneg (Vp - Zp * Up), specNorm_nonneg (Vm - Zm * Um)]
    exact (sq_le_sq₀ (specNorm_nonneg _) (by positivity)).1 h'
  have := smul_one_le_and_le_smul_one_add (a := 1 - κ) (b := 1 + κ) (by linarith) (by positivity)
    (by linarith) h₁ h₂ hX
  rw [hGX]
  convert this using 3 <;> ring


/-- A rounding of a bounded number. -/
private theorem abs_sub_le_of_isRoundingOf_of_abs_le {u τ Ω a z c : ℝ} (h : IsRoundingOf u τ Ω a z)
    (ha : |a| ≤ c) (hc : c ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) : |z - a| ≤ u * (c + τ) := by
  rw [abs_sub_comm]
  exact (abs_sub_le_of_isRoundingOf h (ha.trans hc) hu hτ).trans
    (mul_le_mul_of_nonneg_left (by linarith) hu)

/-- The eigenvalues of a child's approximate diagonalization are bounded. -/
private theorem abs_le_of_isApproxDiagonalization {n : Type*} [Fintype n] [DecidableEq n]
    {A U : Matrix n n ℂ} {d : n → ℝ} {ρ κ r : ℝ} (h : IsApproxDiagonalization A U d ρ κ)
    (hA : specNorm A ≤ r) (hκ1 : κ < 1) (i : n) :
    |d i| ≤ (r + ρ) / (1 - κ) ^ 2 := by
  refine (abs_le_specNorm_mul_diagonal_mul_div hκ1 h.smul_one_le i).trans ?_
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  have e : U * Matrix.diagonal (fun j => (d j : ℂ)) * Uᴴ =
      A - (A - U * Matrix.diagonal (fun j => (d j : ℂ)) * Uᴴ) := by abel
  rw [e]
  exact (specNorm_sub_le _ _).trans (add_le_add hA h.specNorm_sub_le)

/-- The computed product `mm(Q, U)` against the ideal frame. -/
private theorem FloatMachine.IsAccurate.specNorm_decodeMatrix_mm_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k r : ℕ}
    (hr : r ≤ k) {Q : Matrix (Fin k) (Fin r) (F × F)} {X : Matrix (Fin r) (Fin r) (F × F)}
    {Z : Matrix (Fin k) (Fin r) ℂ} {η κ : ℝ} (hZ : HasOrthonormalCols Z)
    (hQ : specNorm (Z - decodeMatrix dec Q) ≤ η) (hX : specNorm (decodeMatrix dec X) ≤ 1 + κ)
    (hκ : 0 ≤ κ) (hΩ : (1 + η) * (1 + κ) ≤ Ω) (hμ : 0 ≤ μM k) (hu : 0 ≤ u) (hτ : 0 ≤ τ) :
    specNorm (decodeMatrix dec (M.mm Q X) - Z * decodeMatrix dec X) ≤
      η * (1 + κ) + μM k * u * ((1 + η) * (1 + κ) + τ) := by
  have hQn : specNorm (decodeMatrix dec Q) ≤ 1 + η := by
    have e : decodeMatrix dec Q = Z - (Z - decodeMatrix dec Q) := by abel
    rw [e]
    exact (specNorm_sub_le _ _).trans (add_le_add hZ.specNorm_le_one hQ)
  have hη : 0 ≤ η := (specNorm_nonneg _).trans hQ
  have hprod : specNorm (decodeMatrix dec Q) * specNorm (decodeMatrix dec X) ≤
      (1 + η) * (1 + κ) :=
    mul_le_mul hQn hX (specNorm_nonneg _) (by linarith)
  have hmm := hM.isMatMulErr.specNorm_mul_sub_le Q X (hprod.trans hΩ)
  have hk : max k (max r r) = k := by omega
  rw [hk] at hmm
  change specNorm (decodeMatrix dec Q * decodeMatrix dec X - decodeMatrix dec (M.mm Q X)) ≤
    μM k * u * max (specNorm (decodeMatrix dec Q) * specNorm (decodeMatrix dec X)) τ at hmm
  have e : decodeMatrix dec (M.mm Q X) - Z * decodeMatrix dec X =
      -(decodeMatrix dec Q * decodeMatrix dec X - decodeMatrix dec (M.mm Q X)) -
        (Z - decodeMatrix dec Q) * decodeMatrix dec X := by
    rw [Matrix.sub_mul]; abel
  rw [e]
  refine (specNorm_sub_le _ _).trans ?_
  rw [specNorm_neg]
  have h1 := (specNorm_mul_le (Z - decodeMatrix dec Q) (decodeMatrix dec X)).trans
    (mul_le_mul hQ hX (specNorm_nonneg _) hη)
  have h2 : μM k * u * max (specNorm (decodeMatrix dec Q) * specNorm (decodeMatrix dec X)) τ ≤
      μM k * u * ((1 + η) * (1 + κ) + τ) :=
    mul_le_mul_of_nonneg_left (max_le (by linarith) (by
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + η) (by linarith : (0 : ℝ) ≤ 1 + κ)
      linarith)) (mul_nonneg hμ hu)
  linarith
/-- A leaf of `NLAlib.eighAux` is an approximate diagonalization: for a stored $\mathbf{A}$
with Hermitian decoding, $0 \le \kappa \le 1$ and a recursion budget $f + 1$, if the node has size
at most one (and $\eta \ge 0$) or the machine's leaf test $R \le \mathrm{fl}(\varepsilon R_0)$
holds (and $\|\mathbf{A}\|_2 \le \eta$), the output of `NLAlib.eighAux` is an approximate
diagonalization of $\mathbf{A}$ with residual $\eta$ and singular values within $\kappa$ of $1$. -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_leaf {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel f k ℓ : ℕ} {R₀ β R ε : F}
    {A : Matrix (Fin k) (Fin k) (F × F)} {s : List Bool → EighSample ℝ ℂ N} {η κ : ℝ}
    (hA : (decodeMatrix dec A).IsHermitian) (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1)
    (hleaf : (k ≤ 1 ∧ 0 ≤ η) ∨
      (M.le R (M.mul ε R₀) = true ∧ specNorm (decodeMatrix dec A) ≤ η)) :
    IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eighAux M N signFuel R₀ β (f + 1) A R ε ℓ s).1)
      (fun i => dec ((eighAux M N signFuel R₀ β (f + 1) A R ε ℓ s).2 i)) η κ := by
  have h1 : (1 - κ) ^ 2 • (1 : Matrix (Fin k) (Fin k) ℂ) ≤ 1ᴴ * 1 := by
    rw [Matrix.conjTranspose_one, Matrix.one_mul]
    simpa using smul_one_le_smul_one (n := Fin k) (𝕜 := ℂ) (show (1 - κ) ^ 2 ≤ 1 by nlinarith)
  have h2 : (1 : Matrix (Fin k) (Fin k) ℂ)ᴴ * 1 ≤ (1 + κ) ^ 2 • 1 := by
    rw [Matrix.conjTranspose_one, Matrix.one_mul]
    simpa using smul_one_le_smul_one (n := Fin k) (𝕜 := ℂ) (show 1 ≤ (1 + κ) ^ 2 by nlinarith)
  by_cases hk : k ≤ 1
  · have hη : 0 ≤ η := by
      rcases hleaf with h | h
      · exact h.2
      · exact (specNorm_nonneg _).trans h.2
    simp only [eighAux, eighStep, if_pos hk, hM.decodeMatrix_identityMat]
    refine ⟨?_, h1, h2⟩
    have : Subsingleton (Fin k) := Fin.subsingleton_iff_le_one.mpr hk
    have hd : decodeMatrix dec A = Matrix.diagonal fun i => (dec (A i i).1 : ℂ) := by
      ext i j
      obtain rfl := Subsingleton.elim i j
      have h := congrArg Complex.im (hA.apply i i)
      simp only [decodeMatrix, decodeComplex, Matrix.map_apply, Complex.star_def,
        Complex.conj_im] at h
      apply Complex.ext <;> simp [decodeMatrix, decodeComplex]
      linarith
    simpa [hd] using hη
  · have ht := hleaf.resolve_left fun h => hk h.1
    simp only [eighAux, eighStep, if_neg hk, ht.1, if_true, hM.decodeMatrix_identityMat,
      hM.dec_zero]
    refine ⟨?_, h1, h2⟩
    simpa using ht.2


/-- The one-child outcomes of `NLAlib.eighStep`. -/
private theorem eq_hermShift_and_of_eighStep_eq_shift {F Su Sg : Type*} [Inhabited Sg]
    {M : FloatMachine F Su Sg}
    {N signFuel : ℕ} {R₀ β : F} {k : ℕ} {A : Matrix (Fin k) (Fin k) (F × F)} {R ε : F} {ℓ : ℕ}
    {smp : EighSample Su Sg N} {b : Bool} {A' : Matrix (Fin k) (Fin k) (F × F)} {σ : F}
    (h : eighStep M N signFuel R₀ β A R ε ℓ smp = .shift b A' σ) :
    A' = M.hermShift A σ ∧
      (σ = M.div R (M.ofNat 2) ∨ σ = M.neg (M.div R (M.ofNat 2))) := by
  unfold eighStep at h
  dsimp only at h
  split_ifs at h <;> simp only [EighStep.shift.injEq] at h
  · obtain ⟨-, rfl, rfl⟩ := h; exact ⟨rfl, Or.inl rfl⟩
  · obtain ⟨-, rfl, rfl⟩ := h; exact ⟨rfl, Or.inr rfl⟩

/-- `NLAlib.eighStep` is not a leaf at an internal node. -/
private theorem eighStep_ne_leaf {F Su Sg : Type*} [Inhabited Sg] {M : FloatMachine F Su Sg}
    {N signFuel : ℕ} {R₀ β : F} {k : ℕ} {A : Matrix (Fin k) (Fin k) (F × F)} {R ε : F} {ℓ : ℕ}
    {smp : EighSample Su Sg N} (hk : ¬ k ≤ 1) (hint : M.le R (M.mul ε R₀) = false)
    (U : Matrix (Fin k) (Fin k) (F × F)) (d : Fin k → F) :
    eighStep M N signFuel R₀ β A R ε ℓ smp ≠ .leaf U d := by
  unfold eighStep
  rw [if_neg hk, if_neg (by simp [hint])]
  dsimp only
  split_ifs <;> simp

/-- Weakening the residual and the singular-value window of an approximate diagonalization. -/
private theorem isApproxDiagonalization_of_le {n : Type*} [Fintype n] [DecidableEq n]
    {A U : Matrix n n ℂ} {d : n → ℝ} {η η' κ κ' : ℝ} (h : IsApproxDiagonalization A U d η κ)
    (hη : η ≤ η') (hκ0 : 0 ≤ κ) (hκ : κ ≤ κ') (hκ1 : κ' ≤ 1) :
    IsApproxDiagonalization A U d η' κ' :=
  ⟨h.specNorm_sub_le.trans hη, (smul_one_le_smul_one (by nlinarith)).trans h.smul_one_le,
    h.le_smul_one.trans (smul_one_le_smul_one (by nlinarith))⟩

/-- At a node whose leaf test $R \le \mathrm{fl}(e R_0)$ holds, $R \le e(R + R_0)$ (for
$1000u \le e \le 1/8$ and $4\tau \le eR_0$). -/
private theorem FloatMachine.IsAccurate.le_mul_add_of_le_eq_true {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R e R₀ : F} (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (he : 0 < dec e) (he₁ : dec e ≤ 1 / 8) (hR₀ : 0 < dec R₀) (hR : 0 ≤ dec R)
    (hue : u * 1000 ≤ dec e) (hτ : τ * 4 ≤ dec e * dec R₀) (hΩ : dec R₀ ≤ Ω)
    (ht : M.le R (M.mul e R₀) = true) : dec R ≤ dec e * (dec R + dec R₀) := by
  have hle := (hM.le_iff _ _).mp ht
  have hεR₀ : dec e * dec R₀ ≤ dec R₀ / 8 := by linarith [mul_le_mul_of_nonneg_right he₁ hR₀.le]
  obtain ⟨-, hm⟩ := le_and_le_of_isRoundingOf (hM.mul e R₀) (by positivity) (by linarith) hu hτ₀
  have h1 : u * (dec e * dec R₀ + τ) ≤ dec e * dec e * dec R₀ := by
    have h4 := mul_le_mul_of_nonneg_right (by linarith : u ≤ dec e / 1000)
      (by positivity : 0 ≤ dec e * dec R₀ + τ)
    have h5 := mul_le_mul_of_nonneg_left (by linarith : dec e * dec R₀ + τ ≤
      5 / 4 * (dec e * dec R₀)) (by positivity : 0 ≤ dec e / 1000)
    have h6 : 0 ≤ dec e * dec e * dec R₀ := by positivity
    linarith
  have heR0 := mul_nonneg he.le hR
  rcases le_or_gt (dec R) (dec e * dec R₀) with h | h
  · linarith
  · linarith [mul_le_mul_of_nonneg_left h.le he.le]

/-- **A shift node**: the child's approximate diagonalization of the stored
$\mathrm{fl}(\mathbf{A} - \sigma\mathbf{I})$ (residual $\rho$, window $\kappa < 1$, norm at most
$r'$), with its eigenvalues shifted back by the stored $\sigma$, $\lvert\sigma\rvert \le s$, is one
of $\mathbf{A}$ ($\|\mathbf{A}\|_2 \le R$) with residual
$u(R + s + \tau) + \rho + s(2\kappa + \kappa^2) + (1 + \kappa)^2\theta$,
$\theta = u(D + s + \tau)$, $D = (r' + \rho)/(1 - \kappa)^2$. -/
private theorem FloatMachine.IsAccurate.isApproxDiagonalization_add_of_hermShift {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k : ℕ} {A U : Matrix (Fin k) (Fin k) (F × F)}
    {d : Fin k → F} {σ : F} {R s r' ρ κ : ℝ} (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hA : (decodeMatrix dec A).IsHermitian) (hR : specNorm (decodeMatrix dec A) ≤ R)
    (hσ : |dec σ| ≤ s) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hc : IsApproxDiagonalization (decodeMatrix dec (M.hermShift A σ)) (decodeMatrix dec U)
      (fun i => dec (d i)) ρ κ)
    (hA'R : specNorm (decodeMatrix dec (M.hermShift A σ)) ≤ r') (hΩ1 : R + s + τ ≤ Ω)
    (hΩ2 : (r' + ρ) / (1 - κ) ^ 2 + s + τ ≤ Ω) :
    IsApproxDiagonalization (decodeMatrix dec A) (decodeMatrix dec U)
      (fun i => dec (M.add (d i) σ)) (u * (R + s + τ) + ρ + s * (2 * κ + κ ^ 2) +
        (1 + κ) ^ 2 * (u * ((r' + ρ) / (1 - κ) ^ 2 + s + τ))) κ := by
  have hρ0 := (specNorm_nonneg _).trans hc.specNorm_sub_le
  have hr0 := (specNorm_nonneg _).trans hA'R
  have hs0 := (abs_nonneg _).trans hσ
  have hR0 := (specNorm_nonneg _).trans hR
  have hn : specNorm (decodeMatrix dec A - dec σ • (1 : Matrix (Fin k) (Fin k) ℂ)) ≤ R + s := by
    refine (specNorm_sub_le _ _).trans (add_le_add hR ?_)
    rw [specNorm_real_smul]
    exact (mul_le_mul_of_nonneg_left specNorm_one_le (abs_nonneg _)).trans (by linarith)
  have hA'err := (hM.specNorm_sub_decodeMatrix_hermShift_le hu hA σ (by linarith)).trans
    (mul_le_mul_of_nonneg_left (max_le (c := R + s + τ) (by linarith) (by linarith)) hu)
  have hd := abs_le_of_isApproxDiagonalization hc hA'R hκ1
  have hθ0 : 0 ≤ u * ((r' + ρ) / (1 - κ) ^ 2 + s + τ) := mul_nonneg hu (by positivity)
  refine ⟨specNorm_sub_mul_diagonal_mul_conjTranspose_le hσ hκ0 hθ0 hc.smul_one_le
    hc.le_smul_one hA'err hc.specNorm_sub_le fun i =>
    abs_sub_le_of_isRoundingOf_of_abs_le (hM.add _ _)
      ((abs_add_le _ _).trans (add_le_add (hd i) hσ)) (by linarith) hu hτ₀, hc.smul_one_le,
    hc.le_smul_one⟩

/-- The rotated frames $\mathbf{Z}_\pm = \mathbf{V}_\pm\mathbf{W}_\pm$ of the two spectral
projectors $\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} - c\mathbf{I}))$ are mutually
orthogonal and block-diagonalize $\mathbf{A}$. -/
private theorem conjTranspose_mul_eq_zero_and_eq_add_of_mul_conjTranspose_eq {k p q : ℕ}
    {A : Matrix (Fin k) (Fin k) ℂ} {c : ℝ} {Vp : Matrix (Fin k) (Fin p) ℂ}
    {Vm : Matrix (Fin k) (Fin q) ℂ} {Wp : Matrix (Fin p) (Fin p) ℂ}
    {Wm : Matrix (Fin q) (Fin q) ℂ} (hWp : HasOrthonormalCols Wp) (hWm : HasOrthonormalCols Wm)
    (hZp : HasOrthonormalCols (Vp * Wp)) (hZm : HasOrthonormalCols (Vm * Wm))
    (hVpP : Vp * Vpᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))))
    (hVmP : Vm * Vmᴴ = (2⁻¹ : ℝ) • (1 - cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)))) :
    (Vp * Wp)ᴴ * (Vm * Wm) = 0 ∧ A = (Vp * Wp) * ((Vp * Wp)ᴴ * A * (Vp * Wp)) * (Vp * Wp)ᴴ +
      (Vm * Wm) * ((Vm * Wm)ᴴ * A * (Vm * Wm)) * (Vm * Wm)ᴴ := by
  set Zp := Vp * Wp with hZpdef
  set Zm := Vm * Wm with hZmdef
  have hPp : Zp * Zpᴴ = Vp * Vpᴴ := by
    rw [hZpdef, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wp,
      mul_eq_one_comm.mp hWp, Matrix.one_mul]
  have hPm : Zm * Zmᴴ = Vm * Vmᴴ := by
    rw [hZmdef, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wm,
      mul_eq_one_comm.mp hWm, Matrix.one_mul]
  set S := cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))
  have hPQ : Zp * Zpᴴ + Zm * Zmᴴ = 1 := by
    rw [hPp, hPm, hVpP, hVmP, ← smul_add, add_add_sub_cancel, ← two_smul ℝ, smul_smul]
    norm_num
  have hZpm : Zpᴴ * Zm = 0 := by
    have h : Zpᴴ * Zm = Zpᴴ * Zm + Zpᴴ * Zm := by
      calc Zpᴴ * Zm = Zpᴴ * (Zp * Zpᴴ + Zm * Zmᴴ) * Zm := by rw [hPQ, Matrix.mul_one]
        _ = (Zpᴴ * Zp) * (Zpᴴ * Zm) + (Zpᴴ * Zm) * (Zmᴴ * Zm) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = _ := by rw [hZp, hZm, Matrix.one_mul, Matrix.mul_one]
    simpa using h
  have hZmp : Zmᴴ * Zp = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose Zp, ← Matrix.conjTranspose_mul, hZpm,
      Matrix.conjTranspose_zero]
  have hcomm : Commute S A := Commute.cfc_real
    ((Commute.refl A).sub_left ((Commute.one_left A).smul_left _)) Real.sign
  have hPc : Commute (Zp * Zpᴴ) A := by
    rw [hPp, hVpP]; exact ((Commute.one_left A).add_left hcomm).smul_left _
  have hQc : Commute (Zm * Zmᴴ) A := by
    rw [show Zm * Zmᴴ = 1 - Zp * Zpᴴ by rw [← hPQ]; abel]
    exact (Commute.one_left A).sub_left hPc
  refine ⟨hZpm, ?_⟩
  have h1 : Zp * Zpᴴ * A * (Zm * Zmᴴ) = 0 := by
    rw [hPc.eq, Matrix.mul_assoc, Matrix.mul_assoc Zp, ← Matrix.mul_assoc Zpᴴ, hZpm,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
  have h2 : Zm * Zmᴴ * A * (Zp * Zpᴴ) = 0 := by
    rw [hQc.eq, Matrix.mul_assoc, Matrix.mul_assoc Zm, ← Matrix.mul_assoc Zmᴴ, hZmp,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
  calc A = (Zp * Zpᴴ + Zm * Zmᴴ) * A * (Zp * Zpᴴ + Zm * Zmᴴ) := by
        rw [hPQ, Matrix.one_mul, Matrix.mul_one]
    _ = Zp * Zpᴴ * A * (Zp * Zpᴴ) + Zm * Zmᴴ * A * (Zm * Zmᴴ) +
        (Zp * Zpᴴ * A * (Zm * Zmᴴ) + Zm * Zmᴴ * A * (Zp * Zpᴴ)) := by
      simp only [Matrix.mul_add, Matrix.add_mul]; abel
    _ = _ := by rw [h1, h2, add_zero, add_zero]; simp only [Matrix.mul_assoc]

/-- **A split node**: the children's approximate diagonalizations (residual $\rho$, window
$\kappa < 1$, norms at most $r'$), through the computed bases $\mathrm{mm}(\mathbf{Q}_\pm,
\mathbf{U}_\pm)$ (with $\mathbf{Q}_\pm$ within $\eta$ of orthonormal, mutually orthogonal frames
$\mathbf{Z}_\pm$ that block-diagonalize $\mathbf{A}$) and the stored shift $\pm\sigma$, assemble
into one of $\mathbf{A}$. -/
private theorem FloatMachine.IsAccurate.isApproxDiagonalization_submatrix_fromCols_mm {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k kp : ℕ} (hkp : kp ≤ k)
    {A : Matrix (Fin k) (Fin k) (F × F)} {Qp : Matrix (Fin k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)} {Ap Up : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am Um : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)} {dp : Fin kp → F}
    {dm : Fin (k - kp) → F} {σ : F} {c : ℝ} {Vp : Matrix (Fin k) (Fin kp) ℂ}
    {Vm : Matrix (Fin k) (Fin (k - kp)) ℂ} {Wp : Matrix (Fin kp) (Fin kp) ℂ}
    {Wm : Matrix (Fin (k - kp)) (Fin (k - kp)) ℂ} {η γ s ρ κ r' ξ Dn θ : ℝ} (hμM : 0 ≤ μM k)
    (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) (hVp : HasOrthonormalCols Vp) (hVm : HasOrthonormalCols Vm)
    (hWp : HasOrthonormalCols Wp) (hWm : HasOrthonormalCols Wm)
    (hVpP : Vp * Vpᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (decodeMatrix dec A -
      c • (1 : Matrix (Fin k) (Fin k) ℂ))))
    (hVmP : Vm * Vmᴴ = (2⁻¹ : ℝ) • (1 - cfc Real.sign (decodeMatrix dec A -
      c • (1 : Matrix (Fin k) (Fin k) ℂ))))
    (hQp : specNorm (Vp * Wp - decodeMatrix dec Qp) ≤ η)
    (hQm : specNorm (Vm * Wm - decodeMatrix dec Qm) ≤ η)
    (hAp : specNorm (decodeMatrix dec Ap - (Wpᴴ * (Vpᴴ * decodeMatrix dec A * Vp) * Wp -
      dec σ • (1 : Matrix (Fin kp) (Fin kp) ℂ))) ≤ γ)
    (hAm : specNorm (decodeMatrix dec Am - (Wmᴴ * (Vmᴴ * decodeMatrix dec A * Vm) * Wm +
      dec σ • (1 : Matrix (Fin (k - kp)) (Fin (k - kp)) ℂ))) ≤ γ)
    (hcp : IsApproxDiagonalization (decodeMatrix dec Ap) (decodeMatrix dec Up)
      (fun i => dec (dp i)) ρ κ)
    (hcm : IsApproxDiagonalization (decodeMatrix dec Am) (decodeMatrix dec Um)
      (fun i => dec (dm i)) ρ κ)
    (hApR : specNorm (decodeMatrix dec Ap) ≤ r') (hAmR : specNorm (decodeMatrix dec Am) ≤ r')
    (hσ : |dec σ| ≤ s) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκξ : κ + √2 * ξ ≤ 1) (hη1 : η ≤ 1)
    (hΩ4 : 4 ≤ Ω) (hΩd : Dn + s + τ ≤ Ω)
    (hξ : ξ = η * (1 + κ) + μM k * u * ((1 + η) * (1 + κ) + τ)) (hDn : Dn = (r' + ρ) / (1 - κ) ^ 2)
    (hθ : θ = u * (Dn + s + τ)) :
    IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec ((Matrix.fromCols (M.mm Qp Up) (M.mm Qm Um)).submatrix id
        ((finCongr (Nat.add_sub_of_le hkp).symm).trans finSumFinEquiv.symm)))
      (fun i => dec (Sum.elim (fun j => M.add (dp j) σ) (fun j => M.sub (dm j) σ)
        (((finCongr (Nat.add_sub_of_le hkp).symm).trans finSumFinEquiv.symm) i)))
      (γ + ρ + s * (2 * κ + κ ^ 2) + 2 * ((1 + κ) ^ 2 * θ + ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ)))
      (κ + √2 * ξ) := by
  have hη0 : 0 ≤ η := (specNorm_nonneg _).trans hQp
  have hξ0' : 0 ≤ ξ := by rw [hξ]; positivity
  have hZp := hVp.mul hWp
  have hZm := hVm.mul hWm
  obtain ⟨hZpm, hAdec⟩ := conjTranspose_mul_eq_zero_and_eq_add_of_mul_conjTranspose_eq hWp hWm
    hZp hZm hVpP hVmP
  have hCp : specNorm (decodeMatrix dec Ap - ((Vp * Wp)ᴴ * decodeMatrix dec A * (Vp * Wp) -
      dec σ • (1 : Matrix (Fin kp) (Fin kp) ℂ))) ≤ γ := by
    convert hAp using 4; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hCm : specNorm (decodeMatrix dec Am - ((Vm * Wm)ᴴ * decodeMatrix dec A * (Vm * Wm) -
      (-dec σ) • (1 : Matrix (Fin (k - kp)) (Fin (k - kp)) ℂ))) ≤ γ := by
    rw [neg_smul, sub_neg_eq_add]
    convert hAm using 4; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hκ1' : κ ≤ 1 := by linarith [mul_nonneg (Real.sqrt_nonneg 2) hξ0']
  have hΩq : (1 + η) * (1 + κ) ≤ Ω := by
    linarith [mul_le_mul (by linarith : 1 + η ≤ 2) (by linarith : 1 + κ ≤ 2) (by linarith)
      (by norm_num : (0 : ℝ) ≤ 2)]
  have hρ0 := (specNorm_nonneg _).trans hcp.specNorm_sub_le
  have hr0 := (specNorm_nonneg _).trans hApR
  have hξ0 : 0 ≤ ξ := by rw [hξ]; positivity
  have hDn0 : 0 ≤ Dn := by rw [hDn]; exact div_nonneg (by linarith) (sq_nonneg _)
  have hθ0 : 0 ≤ θ := by rw [hθ]; have := (abs_nonneg _).trans hσ; positivity
  have hVoutp := hM.specNorm_decodeMatrix_mm_sub_le hkp hZp hQp
    (specNorm_le_of_conjTranspose_mul_self_le hκ0 hcp.le_smul_one) hκ0 hΩq hμM hu hτ₀ (X := Up)
  have hVoutm := hM.specNorm_decodeMatrix_mm_sub_le (Nat.sub_le _ _) hZm hQm
    (specNorm_le_of_conjTranspose_mul_self_le hκ0 hcm.le_smul_one) hκ0 hΩq hμM hu hτ₀ (X := Um)
  rw [← hξ] at hVoutp hVoutm
  have hdp := abs_le_of_isApproxDiagonalization hcp hApR hκ1
  have hdm := abs_le_of_isApproxDiagonalization hcm hAmR hκ1
  rw [← hDn] at hdp hdm
  have hep := fun i => abs_sub_le_of_isRoundingOf_of_abs_le (hM.add (dp i) σ)
    ((abs_add_le _ _).trans (add_le_add (hdp i) hσ)) (by linarith) hu hτ₀
  have hem := fun i => abs_sub_le_of_isRoundingOf_of_abs_le (hM.sub (dm i) σ)
    ((abs_sub _ _).trans (add_le_add (hdm i) hσ)) (by linarith) hu hτ₀
  rw [← hθ] at hep hem
  have hres := specNorm_sub_fromCols_mul_diagonal_le hZp hZm hZpm hAdec hκ0 hθ0 hσ
    (by rwa [abs_neg]) hDn0 hCp hCm hcp.specNorm_sub_le hcm.specNorm_sub_le hcp.smul_one_le
    hcp.le_smul_one hcm.smul_one_le hcm.le_smul_one hVoutp hVoutm hdp hdm hep
    (fun i => by rw [← sub_eq_add_neg]; exact hem i)
  obtain ⟨hlo, hhi⟩ := smul_one_le_and_le_smul_one_fromCols hZp hZm hZpm hκ0 hξ0 hκξ
    hcp.smul_one_le hcp.le_smul_one hcm.smul_one_le hcm.le_smul_one hVoutp hVoutm
  have key := isApproxDiagonalization_submatrix
    ((finCongr (Nat.add_sub_of_le hkp).symm).trans finSumFinEquiv.symm) hres hlo hhi
  convert key using 2
  · simp only [decodeMatrix, ← Matrix.submatrix_map, Matrix.fromCols_map]
  · rename_i i
    generalize ((finCongr (Nat.add_sub_of_le hkp).symm).trans finSumFinEquiv.symm) i = j
    cases j <;> rfl

/-- **Local guarantee of a node of spectral bisection** (Lemma 4.1): let the machine meet
`NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ with $u \ge 0$ and constants
$\mu_{\mathrm{MM}}(k), \mu_{\mathrm{QR}}(k), c_{\mathrm N} \ge 0$. Let the node $y$ have a stored
matrix with Hermitian decoding $\mathbf{A}$ of size $k$, $\|\mathbf{A}\|_2 \le R$, $\ell \ge 20$,
$0 < \varepsilon \le 1/8$ (decoded stored values), let $R_0 > 0$, $0 < \rho \le 1$,
$0 < w \le R$, the stored accuracy $\beta$ with $0 < \beta \le$ `NLAlib.bisectionSignTol` $k$
$\varepsilon$ $\rho$ $\ell$, and $N_y = N(w/(8R), \beta/(16k))$ (`NLAlib.newtonSchulzSteps`).
Suppose
$$640\,k^{3/2}(8 + \mu_{\mathrm{MM}}(k))(N_y + 1)\,u \le \frac{w}{4R}\,\beta \,, \qquad
(4\mu_{\mathrm{QR}}(k) + 4\sqrt k(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(k) + 1)\,u \le \beta
\,,$$
the sign step limit is at least $N_y$, $0 \le \tau$,
$4k^{3/2}\tau \le \min(\sqrt{\rho/2}, \varepsilon R_0)$ and
$16(R_0 + R + k + \ell + \sqrt{\log(4/\rho)}) \le \Omega$; that, when $k \ge 2$ and the
machine's leaf test $R \le \mathrm{fl}(\varepsilon R_0)$ fails, the
node's sample satisfies `NLAlib.IsEighGoodSample` with $w$, $x = \sqrt{\rho/2}/k$ and
$t = \sqrt2(2\sqrt k + \sqrt{2\log(4/\rho)})$; and that every child $y'$ of the node returns an
approximate diagonalization of its matrix with residual $\varepsilon'(R' + R_0)$ and singular
values within $\varepsilon'/3$ of $1$ (its own tolerance and window). Then the node returns an
approximate diagonalization (`NLAlib.IsApproxDiagonalization`) of $\mathbf{A}$ with residual
$\varepsilon(R + R_0)$ and singular values within $\varepsilon/3$ of $1$. [Shah2024, Lemma 4.1],
there with the probabilities of the events folded in, $R_0$-free bounds on the children's
$\|\mathbf{D}_\pm\|_2$ (the $R_0$ part is absorbed by the slack $\varepsilon R_0/\ell$), and
Events I–III as conditions. -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hμQ : 0 ≤ μQ y.k) (hcN : 0 ≤ cN) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hudefl : (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    {f : ℕ} {s : List Bool → EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w (√(ρ / 2) / y.k)
        (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y (s []))
    (hchild : ∀ (b : Bool) (y' : EighNode F), eighChild M N signFuel R₀ β y (s []) b = some y' →
      IsApproxDiagonalization (decodeMatrix dec y'.A)
        (decodeMatrix dec (eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).1)
        (fun i => dec ((eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).2 i))
        (dec y'.ε * (dec y'.R + dec R₀)) (dec y'.ε / 3)) :
    IsApproxDiagonalization (decodeMatrix dec y.A)
      (decodeMatrix dec (eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).1)
      (fun i => dec ((eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).2 i))
      (dec y.ε * (dec y.R + dec R₀)) (dec y.ε / 3) := by
  have hR0 : 0 ≤ dec y.R := (specNorm_nonneg _).trans hR
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hℓ
  obtain ⟨hk1, -, -, hkτ, -, -, hux, hvx, h4τ⟩ := mul_le_of_le_bisectionSignTol hℓ hε hε₁ hρ₁ hw
    hwR hβ hβtol hμM hu husign hτ₀ hτ
  have hk1' : (1 : ℝ) ≤ y.k := by exact_mod_cast hk1
  have hτ4 : τ ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_right hk1' hτ₀]
  have hlu : 20 * u ≤ y.ℓ * u := mul_le_mul_of_nonneg_right hℓ' hu
  have hΩ' : 16 * (dec R₀ + dec y.R + y.k + y.ℓ) ≤ Ω := by
    have := Real.sqrt_nonneg (Real.log (4 / ρ)); linarith
  have hk0 : (0 : ℝ) ≤ y.k := Nat.cast_nonneg _
  obtain ⟨hp1, hp2, hp3⟩ := hM.dec_eighNextParams_le (R := y.R) (ε := y.ε) (m := y.ℓ) hu
    (by linarith) hτ₀ (by linarith) hℓ (by linarith) hR0 (by linarith) hε.le (by linarith)
  have hhalf := hM.abs_dec_div_ofNat_two_le (R := y.R) hu (by linarith) hτ₀ hτ4 hR0 (by linarith)
    (by linarith)
  have budget := fun hr'₀ => node_budget (x := (y.ℓ : ℝ)) (R := dec y.R) (R₀ := dec R₀)
    (v := μM y.k * u) (e' := dec (eighNextParams M y.R y.ε y.ℓ).2)
    (r' := dec (eighNextParams M y.R y.ε y.ℓ).1) hε hε₁ hℓ' hR0 hR₀.le hu hux
    (mul_nonneg hμM hu) hvx hτ₀ hτ4 (by linarith) hp2 hp3 hr'₀ hp1 rfl rfl rfl rfl rfl rfl rfl rfl
    rfl
  have huR := mul_le_mul_of_nonneg_right (by linarith : u ≤ 1) hR0
  have huτ := mul_le_mul_of_nonneg_right (by linarith : u ≤ 1) hτ₀
  by_cases hk : y.k ≤ 1
  · exact hM.isApproxDiagonalization_eighAux_succ_of_leaf hA (by positivity) (by linarith)
      (Or.inl ⟨hk, by positivity⟩)
  by_cases ht : M.le y.R (M.mul y.ε R₀) = true
  · exact hM.isApproxDiagonalization_eighAux_succ_of_leaf hA (by positivity) (by linarith)
      (Or.inr ⟨ht, hR.trans (hM.le_mul_add_of_le_eq_true hu hτ₀ hε hε₁ hR₀ hR0 (by linarith)
        (by linarith) (by linarith) ht)⟩)
  have hint : M.le y.R (M.mul y.ε R₀) = false := by simpa using ht
  have hinv := fun {b : Bool} {y' : EighNode F} (h : eighChild M N signFuel R₀ β y (s []) b =
    some y') => hM.isHermitian_and_specNorm_le_of_eighChild_eq_some hμM hμQ hcN hu hA hR hℓ hε hε₁
      hR₀ hρ hρ₁ hw hwR hβ hβtol husign hudefl hfuel hτ₀ hτ hΩ hgood h
  rcases hst : eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s []) with
    ⟨U, d⟩ | ⟨b, A', σ⟩ | ⟨kp, hkp, Qp, Qm, Ap, Am, σ⟩
  · exact absurd hst (eighStep_ne_leaf hk hint U d)
  · obtain ⟨rfl, hσ⟩ := eq_hermShift_and_of_eighStep_eq_shift hst
    have hy' : eighChild M N signFuel R₀ β y (s []) b = some ⟨y.k, M.hermShift y.A σ,
        (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩ := by
      simp [eighChild, hst]
    have hc := hchild b _ hy'
    obtain ⟨-, hA'R⟩ := hinv hy'
    dsimp only at hc hA'R
    simp only [eighAux, hst]
    obtain ⟨hκ0, hκ1, hξ0, -, -, -, -, hDs, hsing, -, hshift⟩ :=
      budget ((specNorm_nonneg _).trans hA'R)
    have hσabs : |dec σ| ≤ dec y.R / 2 + 2 * u * dec y.R + u * τ := by
      rcases hσ with rfl | rfl
      · exact hhalf
      · rw [hM.dec_neg, abs_neg]; exact hhalf
    exact isApproxDiagonalization_of_le (hM.isApproxDiagonalization_add_of_hermShift hu hτ₀ hA hR
      hσabs hκ0 hκ1 hc hA'R (by linarith) (by linarith)) hshift hκ0
      (by linarith [mul_nonneg (Real.sqrt_nonneg 2) hξ0]) (by linarith)
  · obtain ⟨hσR, ⟨Vp, hVp, hVpP, -, Wp, hWp, hQp, hAp⟩, ⟨Vm, hVm, hVmP, -, Wm, hWm, hQm, hAm⟩⟩ :=
      hM.exists_hasOrthonormalCols_specNorm_sub_le_of_eighStep_eq_split hμM hμQ hcN hu hA hR hℓ
        hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol husign hudefl hfuel hτ₀ hτ hΩ hgood hst
    have hyp : eighChild M N signFuel R₀ β y (s []) true = some ⟨kp, Ap,
        (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩ := by
      simp [eighChild, hst]
    have hym : eighChild M N signFuel R₀ β y (s []) false = some ⟨y.k - kp, Am,
        (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩ := by
      simp [eighChild, hst]
    obtain ⟨-, hApR⟩ := hinv hyp
    obtain ⟨-, hAmR⟩ := hinv hym
    have hcp := hchild true _ hyp
    have hcm := hchild false _ hym
    dsimp only at hcp hcm hApR hAmR
    simp only [eighAux, hst]
    obtain ⟨hκ0, hκ1, hξ0, -, -, -, -, hDs, hsing, hsplit, -⟩ :=
      budget ((specNorm_nonneg _).trans hApR)
    have hsξ := mul_nonneg (Real.sqrt_nonneg 2) hξ0
    have hσabs : |dec σ| ≤ dec y.R / 2 + 2 * u * dec y.R + u * τ := by
      rw [abs_le] at hσR ⊢
      constructor <;> linarith [mul_nonneg hu hR0, mul_nonneg hu hτ₀]
    have hη1 : (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ≤ 1 := div_le_one_of_le₀
      ((mul_le_of_le_one_left hε.le (sub_le_self _ (by positivity))).trans (by linarith))
      (by positivity)
    have key := hM.isApproxDiagonalization_submatrix_fromCols_mm hkp hμM hu hτ₀ hVp hVm hWp hWm
      hVpP hVmP hQp hQm hAp hAm hcp hcm hApR hAmR hσabs hκ0 hκ1 (by linarith) hη1 (by linarith)
      (by linarith) rfl rfl rfl
    exact isApproxDiagonalization_of_le key hsplit (by linarith) (by linarith) (by linarith)

end NLAlib
