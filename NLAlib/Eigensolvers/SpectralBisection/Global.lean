/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection
public import NLAlib.Probability.AdaptiveUnionBound
public import NLAlib.Computation.BinaryFloat

/-!
# Hermitian diagonalization in linear precision

The main theorem ([Shah2024, Theorem 4.2]):
randomized spectral bisection (`NLAlib.eigh`) on a floating-point machine with black-box
multiplication and QR returns, with
probability at least $1 - \theta$, an approximate diagonalization with residual
$2\varepsilon R_0$ and $\mathbf{U}$ within $\varepsilon/3$ of unitary, using
$\log_2(1/\varepsilon) + O(\log n + \log\log(1/\varepsilon)) + \tfrac32\log_2(1/\theta)$ bits of
precision. The samples of the nodes are independent, each with the law `NLAlib.eighSampleLaw`;
the node bounds and the measurability of the nodes are in
`NLAlib/Eigensolvers/SpectralBisection.lean`, and the union bound over the adaptively grown
tree is `NLAlib.measureReal_exists_mem_le_of_forall_measure_le_lintegral`.

## Main results

* [Theorem 4.2](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw).
* [Its bit count](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw).
* [The bounded format](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le_of_hasLaw_eighSampleLaw),, with $\log_2\log_2(n/(\varepsilon\theta)) + O(1)$ exponent bits.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ENNReal

namespace NLAlib

/-- The Newton–Schulz step count is nonnegative for $x > 0$ and $0 < e \le 1/2$. -/
private theorem newtonSchulzSteps_nonneg_of_pos {x e : ℝ} (hx : 0 < x) (he : 0 < e)
    (he₁ : e ≤ 1 / 2) : 0 ≤ newtonSchulzSteps x e := by
  rw [newtonSchulzSteps]
  have h₁ : 0 ≤ Real.logb 2 (min |x| (1 / 2))⁻¹ :=
    Real.logb_nonneg one_lt_two ((one_le_inv₀ (by positivity)).mpr
      ((min_le_right _ _).trans (by norm_num)))
  have h₂ : 1 ≤ Real.logb 2 e⁻¹ := by
    have h2 : (2 : ℝ) ≤ e⁻¹ := by rw [le_inv_comm₀ two_pos he]; linarith
    simpa only [Real.logb_self_eq_one one_lt_two] using
      Real.logb_le_logb_of_le one_lt_two two_pos h2
  linarith [Real.logb_nonneg one_lt_two h₂]

/-- The precomputed accuracy of Theorem 4.2 is positive only for $n, \ell > 0$, and it is then
at most $1$. -/
private theorem pos_and_le_one_of_le_div {n ℓ : ℕ} {e θ b : ℝ} (he₁ : e ≤ 2⁻¹ ^ 15)
    (hθ₁ : θ ≤ 1) (hb : 0 < b)
    (hble : b ≤ e * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) :
    0 < n ∧ 0 < ℓ ∧ b ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, mul_zero, zero_mul, div_zero] at hble
    exact absurd hble hb.not_ge
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ0
  · simp only [Nat.cast_zero, mul_zero, zero_mul, div_zero] at hble
    exact absurd hble hb.not_ge
  refine ⟨hn, hℓ0, hble.trans ((div_le_one (by positivity)).mpr ?_)⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ0
  have hsn : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hS2 : 2 ≤ 2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)) := by
    have := Real.sqrt_nonneg (2 * Real.log (16 * n / θ)); linarith
  have h4 : 1 ≤ (ℓ : ℝ) * n * √(n : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hl1 hn1) hsn
  have hc1 : 1 ≤ 2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))) := by
    nlinarith [mul_le_mul h4 hS2 (by norm_num) (by positivity)]
  exact (mul_le_one₀ (he₁.trans (by norm_num)) (Real.sqrt_nonneg θ)
    (Real.sqrt_le_one.mpr hθ₁)).trans hc1

/-- The global hypotheses of Theorem 4.2 give $u \ge 0$, $n \ge 1$, $\ell \ge 20$, $N_* \ge 0$,
$\beta \le 1$ and the contract bounds used at every node. -/
private theorem FloatMachine.IsAccurate.nonneg_and_one_le_and_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hμM : Monotone μM) (hμM₀ : 0 ≤ μM 0) {n : ℕ} {R₀ ε β : F} {θ : ℝ} (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω) :
    0 ≤ u ∧ 1 ≤ n ∧ 20 ≤ ℓ ∧ 0 ≤ Nst ∧ dec β ≤ 1 ∧ 100 * (ℓ : ℝ) ^ 2 * u ≤ 1 ∧
      100 * τ ≤ dec ε * min (dec R₀) 1 ∧ 16 * (dec R₀ + ℓ) ≤ Ω := by
  obtain ⟨hn, hℓ0, hb1⟩ := pos_and_le_one_of_le_div hε₁ hθ₁ hβ hβle
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hμMn : 0 ≤ μM n := hμM₀.trans (hμM (Nat.zero_le n))
  have hNst : 0 ≤ Nst := hN ▸ newtonSchulzSteps_nonneg_of_pos (by positivity) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; linarith)
  have hlog := Real.sqrt_nonneg (Real.log (16 * n / θ))
  have hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω := by linarith
  have hu : 0 ≤ u := by
    have h := hM.ofNat 1 (by norm_num; linarith)
    have h1 : 0 < max |((1 : ℕ) : ℝ)| τ := lt_max_of_lt_left (by norm_num)
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) h1
    linarith [abs_nonneg (((1 : ℕ) : ℝ) - dec (M.ofNat 1))]
  have hθβ : θ * dec β ≤ 1 := mul_le_one₀ hθ₁ hβ.le hb1
  have hl20 : 20 ≤ ℓ := by
    have h15 : (15 : ℝ) ≤ Real.logb 2 (dec ε)⁻¹ := by
      have h2 : (2 : ℝ) ^ (15 : ℕ) ≤ (dec ε)⁻¹ := by
        rw [le_inv_comm₀ (by positivity) hε, ← inv_pow]; exact hε₁
      have := Real.logb_le_logb_of_le one_lt_two (by positivity) h2
      rwa [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this
    have : 15 ≤ ⌈Real.logb 2 (dec ε)⁻¹⌉₊ := by
      have := h15.trans (Nat.le_ceil _); exact_mod_cast this
    unfold bisectionDepth at hℓ; omega
  refine ⟨hu, hn, hl20, hNst, hb1, ?_, ?_, hΩ16⟩
  · have h1 : (1 : ℝ) ≤ n * √(n : ℝ) := one_le_mul_of_one_le_of_one_le hn1 hsn
    have h2 : 8 ≤ (8 + μM n) * (Nst + 1) := by linarith [mul_nonneg hμMn hNst]
    have h3 : 640 * 8 ≤ 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) := by
      linarith [mul_le_mul h1 h2 (by norm_num) (by positivity)]
    have h4 : 32 * (ℓ : ℝ) ^ 2 ≤ 16 * n * (n + 1) * ℓ * (ℓ + 1) := by
      have h41 : (2 : ℝ) ≤ n * (n + 1) := by nlinarith
      have h42 : (ℓ : ℝ) ^ 2 ≤ ℓ * (ℓ + 1) := by nlinarith
      linarith [mul_le_mul h42 h41 (by norm_num) (by positivity)]
    have h5 := mul_le_mul h3 h4 (by positivity) (by positivity)
    have h6 := mul_le_mul_of_nonneg_right h5 hu
    linarith [mul_nonneg (sq_nonneg (ℓ : ℝ)) hu]
  · have h1 : (1 : ℝ) ≤ n * √(n : ℝ) := one_le_mul_of_one_le_of_one_le hn1 hsn
    have : 100 * τ ≤ τ * (100 * n * √(n : ℝ)) := by
      linarith [mul_le_mul_of_nonneg_left h1 hτ₀]
    exact this.trans (hτ.trans (min_le_right _ _))

/-- The precomputed accuracy is below the sign tolerance of every node. -/
private theorem le_bisectionSignTol_of_le_div {n k L ℓ : ℕ} {e ey b θ : ℝ} (hk : 1 ≤ k)
    (hkn : k ≤ n) (hL : ℓ ≤ L) (hL₂ : L ≤ 2 * ℓ) (hl20 : 20 ≤ ℓ) (he : 0 < e) (hey : e / 3 ≤ ey)
    (hθ : 0 < θ) (hb : b ≤ e * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) :
    b ≤ bisectionSignTol k ey (θ / (4 * n)) L := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn1 : (1 : ℝ) ≤ n := hk1.trans hkn'
  have hl20' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hl20
  have hL1 : (ℓ : ℝ) ≤ L := by exact_mod_cast hL
  have hL2 : (L : ℝ) ≤ 2 * ℓ := by exact_mod_cast hL₂
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsρ : √(θ / (4 * n)) * (2 * √(n : ℝ)) = √θ := by
    rw [show (2 : ℝ) * √n = √(4 * n) by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul (by positivity),
      div_mul_cancel₀ _ (by positivity)]
  have h4ρ : 4 / (θ / (4 * n)) = 16 * n / θ := by field_simp; ring
  have hlog := Real.sqrt_nonneg (2 * Real.log (16 * n / θ))
  have hSk : 2 * √(k : ℝ) + √(2 * Real.log (4 / (θ / (4 * n)))) ≤
      2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)) := by
    rw [h4ρ]; gcongr
  have hβ' : b * (2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))) ≤
      e * √θ := by rwa [le_div_iff₀ (by positivity)] at hb
  have hA : 19 / 20 * (e / 3) / (10 * ℓ) ≤ (1 - 1 / (L : ℝ)) * ey / (5 * L) := by
    have h1 : 1 / (L : ℝ) ≤ 1 / 20 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    apply div_le_div₀ (by nlinarith) (mul_le_mul (by linarith) hey (by positivity) (by linarith))
      (by linarith) (by linarith)
  rcases le_or_gt b 0 with hb0 | hb0
  · exact hb0.trans (by
      rw [bisectionSignTol]
      exact div_nonneg (mul_nonneg ((by positivity : (0 : ℝ) ≤ 19 / 20 * (e / 3) / (10 * ℓ)).trans
        hA) (Real.sqrt_nonneg _)) (by positivity))
  rw [bisectionSignTol, le_div_iff₀ (by positivity)]
  calc b * (36 * k * (2 * √(k : ℝ) + √(2 * Real.log (4 / (θ / (4 * n))))))
      ≤ b * (36 * n * (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))) := by gcongr
    _ ≤ 19 / 20 * (e / 3) / (10 * ℓ) * √(θ / (4 * n)) := by
        refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 10 * ℓ * (2 * √(n : ℝ)))
        rw [show 19 / 20 * (e / 3) / (10 * ℓ) * √(θ / (4 * n)) * (10 * ℓ * (2 * √(n : ℝ))) =
          19 / 20 * (e / 3) * (√(θ / (4 * n)) * (2 * √(n : ℝ))) by field_simp, hsρ]
        nlinarith [mul_nonneg he.le (Real.sqrt_nonneg θ)]
    _ ≤ (1 - 1 / (L : ℝ)) * ey / (5 * L) * √(θ / (4 * n)) :=
        mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg _)

/-- A node whose leaf test fails has a positive stored norm bound. -/
private theorem FloatMachine.IsAccurate.pos_of_le_mul_eq_false
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : u ≤ 1 / 100)
    {R e R₀ ε : F} (hint : M.le R (M.mul e R₀) = false) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1) (he : dec ε / 3 ≤ dec e) (he₁ : dec e ≤ dec ε)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1) (hR₀Ω : dec R₀ ≤ Ω) : 0 < dec R := by
  have h1 : ¬ dec R ≤ dec (M.mul e R₀) := fun h => by simp [(hM.le_iff _ _).2 h] at hint
  have ha : 0 < dec e * dec R₀ := mul_pos (by linarith) hR₀pos
  have hτa : τ ≤ dec e * dec R₀ := by
    linarith [mul_le_mul_of_nonneg_left (min_le_left (dec R₀) 1) hε.le,
      mul_le_mul_of_nonneg_right he hR₀pos.le]
  have h2 := hM.mul e R₀ (by
    rw [abs_of_pos ha]
    linarith [mul_le_mul_of_nonneg_right (he₁.trans hε₁) hR₀pos.le])
  rw [abs_of_pos ha, max_eq_left hτa] at h2
  have h3 := (abs_le.mp h2).2
  linarith [mul_le_mul_of_nonneg_right hu ha.le, lt_of_not_ge h1]

/-- The global hypotheses of Theorem 4.2 give the hypotheses of the node lemmas at every internal
node within the depth and accuracy ranges. -/
private theorem FloatMachine.IsAccurate.pos_and_le_of_eighNode
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {R₀ ε β : F} {θ : ℝ} (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hl20 : 20 ≤ ℓ) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hβ : 0 < dec β) (hb1 : dec β ≤ 1)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1) (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω)
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω)
    {y : EighNode F} (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false) (hkn : y.k ≤ n)
    (hℓy : ℓ ≤ y.ℓ) (hℓy₂ : y.ℓ ≤ 2 * ℓ) (hεy : dec ε / 3 ≤ dec y.ε) (hεy₁ : dec y.ε ≤ dec ε)
    (hRy : dec y.R ≤ dec R₀) {w : ℝ}
    (hw : w = θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1))) :
    0 < dec y.R ∧ 0 ≤ μM y.k ∧ 0 ≤ μQ y.k ∧ 20 ≤ y.ℓ ∧ 0 < dec y.ε ∧ dec y.ε ≤ 1 / 8 ∧
      0 < θ / (4 * n) ∧ θ / (4 * n) ≤ 1 ∧ 0 < w ∧ w ≤ dec y.R ∧
      dec β ≤ bisectionSignTol y.k (dec y.ε) (θ / (4 * n)) y.ℓ ∧
      640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
        (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
          w / (4 * dec y.R) * dec β ∧
      (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β ∧
      newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel ∧
      τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(θ / (4 * n) / 2)) (dec y.ε * dec R₀) ∧
      16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / (θ / (4 * n))))) ≤ Ω := by
  have hk2 : (2 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hkn' : (y.k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl20' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hl20
  have hL1 : (ℓ : ℝ) ≤ y.ℓ := by exact_mod_cast hℓy
  have hL2 : (y.ℓ : ℝ) ≤ 2 * ℓ := by exact_mod_cast hℓy₂
  have hεy0 : 0 < dec y.ε := by linarith
  have hk0 : 0 < y.k := by omega
  have hL0 : 0 < y.ℓ := by omega
  have hn0 : 0 < n := by omega
  have hl0 : 0 < ℓ := by omega
  have hu100 : u ≤ 1 / 100 := by
    have : (1 : ℝ) ≤ (ℓ : ℝ) ^ 2 := one_le_pow₀ (by linarith)
    linarith [mul_le_mul_of_nonneg_right this hu]
  have hRpos : 0 < dec y.R := hM.pos_of_le_mul_eq_false hu100 hint hR₀pos hε
    (hε₁.trans (by norm_num)) hεy hεy₁ hτ100 (by linarith)
  have hD : 0 < (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1) : ℝ) := by positivity
  have hD1 : θ ≤ (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1) : ℝ) := by
    have h1 : (1 : ℝ) ≤ 2 * y.k * y.ℓ := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have h2 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1
      (by linarith : (1 : ℝ) ≤ n + 1)) (by linarith : (1 : ℝ) ≤ ℓ + 1)
    linarith
  have hkL : (y.k : ℝ) * y.ℓ ≤ n * (2 * ℓ) := mul_le_mul hkn' hL2 (by positivity) (by positivity)
  have hw8 : w / (8 * dec y.R) = θ / (16 * y.k * y.ℓ * (n + 1) * (ℓ + 1)) := by
    rw [hw]; field_simp; ring
  have hw4 : w / (4 * dec y.R) = θ / (8 * y.k * y.ℓ * (n + 1) * (ℓ + 1)) := by
    rw [hw]; field_simp; ring
  have hNy : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ Nst := by
    rw [hw8, hN]
    refine (newtonSchulzSteps_le_of_le_abs (a := θ / (32 * n * (n + 1) * ℓ * (ℓ + 1)))
      (by positivity) ?_).trans (newtonSchulzSteps_le_of_le (by positivity) ?_ ?_)
    · rw [abs_of_pos (by positivity)]
      apply div_le_div_of_nonneg_left hθ.le (by positivity)
      linarith [mul_le_mul_of_nonneg_right hkL (by positivity : (0 : ℝ) ≤ 16 * (n + 1) * (ℓ + 1))]
    · exact div_le_div_of_nonneg_left hβ.le (by positivity) (by linarith)
    · rw [div_le_iff₀ (by positivity)]; linarith
  have hNy0 : 0 ≤ newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) :=
    newtonSchulzSteps_nonneg_of_pos (by rw [hw8]; positivity) (by positivity)
      (by rw [div_le_iff₀ (by positivity)]; linarith)
  have hsk : √(y.k : ℝ) ≤ √n := Real.sqrt_le_sqrt hkn'
  have h4ρ : 4 / (θ / (4 * n)) = 16 * n / θ := by field_simp; ring
  refine ⟨hRpos, hμM₀.trans (hμM (Nat.zero_le _)), hμQ₀.trans (hμQ (Nat.zero_le _)), by omega,
    hεy0, by linarith [hε₁.trans (by norm_num : (2⁻¹ : ℝ) ^ 15 ≤ 1 / 8)], by positivity,
    by rw [div_le_one (by positivity)]; linarith, by rw [hw]; positivity, ?_,
    le_bisectionSignTol_of_le_div (by omega) hkn hℓy hℓy₂ hl20 hε hεy hθ hβle, ?_, ?_,
    hNy.trans hfuel, ?_, ?_⟩
  · rw [hw, div_le_iff₀ hD]; linarith [mul_le_mul_of_nonneg_left hD1 hRpos.le]
  · have hA : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) ≤ 640 * n * √(n : ℝ) * (8 + μM n) := by
      have := hμM hkn
      have := hμM₀.trans (hμM (Nat.zero_le y.k))
      gcongr
    calc 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
          (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u
        ≤ 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * u :=
          mul_le_mul_of_nonneg_right (mul_le_mul hA (by linarith) (by linarith)
            (by have := hμM₀.trans (hμM (Nat.zero_le n)); positivity)) hu
      _ ≤ θ * dec β / (16 * n * (n + 1) * ℓ * (ℓ + 1)) := by
          rw [le_div_iff₀ (by positivity)]; linarith
      _ ≤ w / (4 * dec y.R) * dec β := by
          rw [hw4, div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          linarith [mul_le_mul_of_nonneg_right hkL
            (by positivity : (0 : ℝ) ≤ 8 * (n + 1) * (ℓ + 1))]
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ hu) hudefl
    linarith [hμQ hkn, hμM hkn, mul_le_mul_of_nonneg_right hsk (by linarith : (0 : ℝ) ≤ cN + 1)]
  · have hX : τ * (4 * y.k * √(y.k : ℝ)) ≤ τ * (4 * n * √(n : ℝ)) := by gcongr
    have hX1 : τ * (4 * n * √(n : ℝ)) * 25 = τ * (100 * n * √(n : ℝ)) := by ring
    have hX0 : 0 ≤ τ * (4 * n * √(n : ℝ)) := by positivity
    rw [show θ / (4 * n) / 2 = θ / (8 * n) by ring]
    refine le_min (hX.trans (by linarith [hτ.trans (min_le_left _ _)])) ?_
    have hτ' := hτ.trans (min_le_right _ _)
    linarith [mul_le_mul_of_nonneg_left (min_le_left (dec R₀) 1) hε.le,
      mul_le_mul_of_nonneg_right hεy hR₀pos.le, mul_pos hεy0 hR₀pos]
  · rw [h4ρ]; linarith

/-- Good samples at the internal nodes with Hermitian, norm-bounded matrices are good samples at
all internal nodes: the invariant propagates down the tree. -/
private theorem FloatMachine.IsAccurate.isEighGoodSample_of_forall_isHermitian_imp
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian) {R₀ ε β : F} {θ : ℝ}
    (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hl20 : 20 ≤ ℓ) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1)
    (hβ : 0 < dec β) (hb1 : dec β ≤ 1)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1) (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω)
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω)
    {s : List Bool → EighSample ℝ ℂ n}
    (hS : ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → 2 ≤ y.k →
        M.le y.R (M.mul y.ε R₀) = false → (decodeMatrix dec y.A).IsHermitian →
        specNorm (decodeMatrix dec y.A) ≤ dec y.R →
        IsEighGoodSample dec (θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)))
          (√(θ / (4 * n) / 2) / y.k)
          (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / (θ / (4 * n)))))) y (s a)) :
    ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → 2 ≤ y.k →
        M.le y.R (M.mul y.ε R₀) = false →
        IsEighGoodSample dec (θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)))
          (√(θ / (8 * n)) / y.k) (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (16 * n / θ)))) y
          (s a) := by
  have hinv : ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y →
        (decodeMatrix dec y.A).IsHermitian ∧ specNorm (decodeMatrix dec y.A) ≤ dec y.R := by
    intro a
    induction a using List.reverseRecOn with
    | nil =>
      intro y hy
      simp only [eighNodeAt, Option.some.injEq] at hy
      subst hy
      exact ⟨hA, hR₀⟩
    | append_singleton a b ih =>
      intro y hy
      rw [eighNodeAt_append_singleton] at hy
      obtain ⟨z, hz, hzy⟩ := Option.bind_eq_some_iff.1 hy
      obtain ⟨hH, hNz⟩ := ih z hz
      obtain ⟨hk, hint⟩ := two_le_k_and_le_eq_false_of_eighChild_eq_some hzy
      obtain ⟨hlen, hkn, hLz, hεz, hεz₁, hRz⟩ :=
        hM.eighNodeAt_eq_some_params hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ100 hΩ16 A s hz
      obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
        hM.pos_and_le_of_eighNode hu hμM hμQ hμM₀ hμQ₀ hcN hn hR₀pos hε hε₁ hθ hθ₁ hl20 hu₁ hβ
          hb1 hβle hN husign hudefl hfuel hτ₀ hτ hτ100 hΩ16 hΩ hk hint hkn (by omega)
          (by omega) hεz hεz₁ hRz rfl
      exact hM.isHermitian_and_specNorm_le_of_eighChild_eq_some h1 h2 hcN hu hH hNz h3 h4 h5
        hR₀pos h6 h7 h8 h9 hβ h10 h11 h12 h13 hτ₀ h14 h15 (fun _ _ => hS a z hz hk hint hH hNz)
        hzy
  intro a y hy hk hint
  obtain ⟨hH, hNy⟩ := hinv a y hy
  have h := hS a y hy hk hint hH hNy
  rwa [show θ / (4 * n) / 2 = θ / (8 * n) by ring,
    show 4 / (θ / (4 * n)) = 16 * n / θ by field_simp; ring] at h

/-- The bad events of an internal node have probability at most its charge
$\theta/(2(n + 1)(\ell + 1)) + (\theta/(2n))\,\mathbb{P}[\text{split}]$. -/
private theorem FloatMachine.IsAccurate.eighSampleLaw_not_isEighGoodSample_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {R₀ ε β : F} {θ : ℝ} (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hl20 : 20 ≤ ℓ) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hβ : 0 < dec β) (hb1 : dec β ≤ 1)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1) (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω)
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω)
    {y : EighNode F} (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false) (hkn : y.k ≤ n)
    (hℓy : ℓ ≤ y.ℓ) (hℓy₂ : y.ℓ ≤ 2 * ℓ) (hεy : dec ε / 3 ≤ dec y.ε) (hεy₁ : dec y.ε ≤ dec ε)
    (hRy : dec y.R ≤ dec R₀) (hH : (decodeMatrix dec y.A).IsHermitian)
    (hNy : specNorm (decodeMatrix dec y.A) ≤ dec y.R) :
    eighSampleLaw n {z | ¬ IsEighGoodSample dec (θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)))
      (√(θ / (4 * n) / 2) / y.k) (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / (θ / (4 * n))))))
      y z} ≤ ENNReal.ofReal (θ / (2 * (n + 1) * (ℓ + 1))) + ENNReal.ofReal (2 * (θ / (4 * n))) *
        eighSampleLaw n {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit} := by
  obtain ⟨hRpos, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    hM.pos_and_le_of_eighNode hu hμM hμQ hμM₀ hμQ₀ hcN hn hR₀pos hε hε₁ hθ hθ₁ hl20 hu₁ hβ
      hb1 hβle hN husign hudefl hfuel hτ₀ hτ hτ100 hΩ16 hΩ hk hint hkn hℓy hℓy₂ hεy hεy₁ hRy rfl
  refine (hM.measure_not_isEighGoodSample_le h1 h2 hcN hu hH hNy hk hkn h3 h4 h5 hR₀pos hint
    h6 h7 h8 h9 hβ h10 h11 h12 h13 hτ₀ h14 h15).trans
    (add_le_add (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) le_rfl)
  have : (y.k : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ y.k := by exact_mod_cast hk
    linarith
  have : (y.ℓ : ℝ) ≠ 0 := by
    have : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast h3
    linarith
  field_simp

/-- The charges along every run of the tree sum to at most $\theta$. -/
private theorem FloatMachine.IsAccurate.tsum_eighNodeAt_charge_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n : ℕ} (hn : 1 ≤ n)
    {signFuel : ℕ} {R₀ ε β : F} {θ : ℝ} (hθ : 0 < θ) (hR₀pos : 0 < dec R₀) (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 2⁻¹ ^ 15) {ℓ : ℕ} (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u)
    (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω) (A : Matrix (Fin n) (Fin n) (F × F))
    (V : EighNode F → Prop) [DecidablePred V] (s : List Bool → EighSample ℝ ℂ n) :
    ∑' a, (eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s).elim 0 (fun y => if V y then
      ENNReal.ofReal (θ / (2 * (n + 1) * (ℓ + 1))) + ENNReal.ofReal (2 * (θ / (4 * n))) *
        {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit}.indicator 1 (s a)
      else 0) ≤ ENNReal.ofReal θ := by
  set C₁ : ℝ≥0∞ := ENNReal.ofReal (θ / (2 * (n + 1) * (ℓ + 1)))
  set C₂ : ℝ≥0∞ := ENNReal.ofReal (2 * (θ / (4 * n)))
  set Spl : EighNode F → Set (EighSample ℝ ℂ n) := fun y =>
    {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit}
  have hle : ∀ a, ((eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s).elim 0 fun y =>
      if V y then C₁ + C₂ * (Spl y).indicator 1 (s a) else 0) ≤
      {a | eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s ≠ none}.indicator
        (fun _ => C₁) a +
      {a | ∃ y, eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y ∧
        (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit}.indicator
        (fun _ => C₂) a := by
    intro a
    rcases hX : eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s with _ | y
    · exact zero_le
    simp only [Option.elim_some]
    split_ifs with hV
    · have hmem : a ∈ {a | eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s ≠ none} := by
        simp [hX]
      rw [Set.indicator_of_mem hmem]
      gcongr
      by_cases hsp : s a ∈ Spl y
      · have hmem2 : a ∈ {a | ∃ y, eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y ∧
            (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit} := ⟨y, hX, hsp⟩
        rw [Set.indicator_of_mem hsp, Set.indicator_of_mem hmem2]
        simp
      · rw [Set.indicator_of_notMem hsp]
        simp
    · exact zero_le
  refine (ENNReal.tsum_le_tsum hle).trans ?_
  rw [ENNReal.tsum_add, ← tsum_subtype, ← tsum_subtype, ENNReal.tsum_set_const,
    ENNReal.tsum_set_const]
  have e1 := hM.encard_eighNodeAt_ne_none_le (N := n) (signFuel := signFuel) (β := β) hε hε₁
    hR₀pos hℓ hu hu₁ hτ₀ hτ100 hΩ16 A s
  have e2 := encard_eighNodeAt_isSplit_le M (signFuel := signFuel) (R₀ := R₀) (β := β)
    ⟨n, A, R₀, ε, ℓ⟩ s
  calc _ ≤ (((n + 1) * (ℓ + 1) : ℕ) : ℝ≥0∞) * C₁ + (n : ℝ≥0∞) * C₂ := by
        gcongr
        · exact_mod_cast e1
        · exact_mod_cast e2
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast n,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                                 linarith
        push_cast
        field_simp
        ring

/-- The sample law is a probability measure. -/
private theorem isProbabilityMeasure_eighSampleLaw (N : ℕ) :
    IsProbabilityMeasure (eighSampleLaw N) := by
  unfold eighSampleLaw
  have : IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite (by simp [Real.volume_Icc])
      (by simp [Real.volume_Icc])
  infer_instance

/-- Theorem 4.2 for measurable samples. -/
private theorem FloatMachine.IsAccurate.measureReal_eigh_le_of_measurable
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n}
    (hζ : ∀ a, Measurable (ζ a)) (hind : iIndepFun ζ μ)
    (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  classical
  obtain ⟨hu, hn, hl20, hNst, hb1, hu₁, hτ100, hΩ16⟩ := hM.nonneg_and_one_le_and_mul_le hμM hμM₀
    hR₀pos hε hε₁ hθ hθ₁ hℓ hβ hβle hN husign hτ₀ hτ hΩ
  have := isProbabilityMeasure_eighSampleLaw n
  have : IsProbabilityMeasure μ := (hlaw []).isProbabilityMeasure_iff.2 this
  let V : EighNode F → Prop := fun y => 2 ≤ y.k ∧ M.le y.R (M.mul y.ε R₀) = false ∧
    (decodeMatrix dec y.A).IsHermitian ∧ specNorm (decodeMatrix dec y.A) ≤ dec y.R ∧ y.k ≤ n ∧
    ℓ ≤ y.ℓ ∧ y.ℓ ≤ 2 * ℓ ∧ dec ε / 3 ≤ dec y.ε ∧ dec y.ε ≤ dec ε ∧ dec y.R ≤ dec R₀
  let G : EighNode F → EighSample ℝ ℂ n → Prop := fun y z =>
    IsEighGoodSample dec (θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)))
      (√(θ / (4 * n) / 2) / y.k) (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / (θ / (4 * n)))))) y z
  let Spl : EighNode F → Set (EighSample ℝ ℂ n) := fun y =>
    {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit}
  let C₁ : ℝ≥0∞ := ENNReal.ofReal (θ / (2 * (n + 1) * (ℓ + 1)))
  let C₂ : ℝ≥0∞ := ENNReal.ofReal (2 * (θ / (4 * n)))
  let X : List Bool → Ω' → Option (EighNode F) := fun a ω =>
    eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ fun b => ζ b ω
  have hsub : {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ⊆ {ω | ∃ a, ζ a ω ∈ {z | ∃ y, X a ω = some y ∧ V y ∧ ¬ G y z}} := by
    intro ω hω
    by_contra hne
    apply hω
    refine hM.isApproxDiagonalization_eigh_of_forall_isEighGoodSample hu hμM hμQ hμM₀ hμQ₀ hcN hA
      hR₀ hR₀pos hε hε₁ hθ hθ₁ hℓ hβ hβle hN husign hudefl hfuel hτ₀ hτ hΩ ?_
    refine hM.isEighGoodSample_of_forall_isHermitian_imp hu hμM hμQ hμM₀ hμQ₀ hcN hn hA hR₀
      hR₀pos hε hε₁ hθ hθ₁ hℓ hl20 hu₁ hβ hb1 hβle hN husign hudefl hfuel hτ₀ hτ hτ100 hΩ16 hΩ ?_
    intro a y hy hk hint hH hNy
    obtain ⟨hlen, hkn, hLy, hεy, hεy₁, hRy⟩ :=
      hM.eighNodeAt_eq_some_params hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ100 hΩ16 A _ hy
    by_contra hbad
    exact hne ⟨a, y, hy, ⟨hk, hint, hH, hNy, hkn, by omega, by omega, hεy, hεy₁, hRy⟩, hbad⟩
  refine (measureReal_mono hsub).trans ?_
  refine measureReal_exists_mem_le_of_forall_measure_le_lintegral hlaw (X := X)
    (fun a => (countable_range_eighNodeAt hunifc hnormalc n signFuel R₀ β a _).mono
      (by rintro _ ⟨ω, rfl⟩; exact ⟨_, rfl⟩))
    (fun a y => measurableSet_eighNodeAt_eq hunifm hunifc hnormalm hnormalc hζ a _ y)
    (fun a y => indepFun_eighNodeAt_eq hunifm hunifc hnormalm hnormalc hζ hind a _ y)
    (S := fun _ oy => {z | ∃ y, oy = some y ∧ V y ∧ ¬ G y z})
    (q := fun _ oy z => oy.elim 0 fun y => if V y then C₁ + C₂ * (Spl y).indicator 1 z else 0)
    ?_ ?_ hθ.le ?_
  · intro a oy
    rcases oy with _ | y
    · simp only [Option.elim_none]
      exact measurable_const
    · simp only [Option.elim_some]
      split_ifs
      · exact measurable_const.add (((measurable_const : Measurable fun _ :
          EighSample ℝ ℂ n => (1 : ℝ≥0∞)).indicator
          (measurableSet_setOf_eighStep_isSplit hunifm hunifc n signFuel R₀ β y.A y.R y.ε
            y.ℓ)).const_mul _)
      · exact measurable_const
  · intro a oy
    rcases oy with _ | y
    · simp
    by_cases hV : V y
    · have hS : {z | ∃ y', some y = some y' ∧ V y' ∧ ¬ G y' z} = {z | ¬ G y z} := by
        ext z
        simp only [Set.mem_ofPred_eq, Option.some.injEq]
        exact ⟨fun ⟨_, h, _, hg⟩ => h ▸ hg, fun hg => ⟨y, rfl, hV, hg⟩⟩
      have hs := measurableSet_setOf_eighStep_isSplit hunifm hunifc n signFuel R₀ β y.A y.R y.ε
        y.ℓ
      rw [hS]
      simp only [Option.elim_some, if_pos hV]
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_const_mul _ (measurable_one.indicator hs), lintegral_indicator_one hs]
      obtain ⟨hk, hint, hH, hNy, hkn, hLy, hLy₂, hεy, hεy₁, hRy⟩ := hV
      exact hM.eighSampleLaw_not_isEighGoodSample_le hu hμM hμQ hμM₀ hμQ₀ hcN hn hR₀pos hε hε₁
        hθ hθ₁ hl20 hu₁ hβ hb1 hβle hN husign hudefl hfuel hτ₀ hτ hτ100 hΩ16 hΩ hk hint hkn hLy
        hLy₂ hεy hεy₁ hRy hH hNy
    · have hS : {z | ∃ y', some y = some y' ∧ V y' ∧ ¬ G y' z} = ∅ := by
        ext z
        simp only [Set.mem_ofPred_eq, Option.some.injEq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, rfl, hV', -⟩
        exact hV hV'
      rw [hS, measure_empty]
      exact zero_le
  · exact fun ω => hM.tsum_eighNodeAt_charge_le hn hθ hR₀pos hε hε₁ hℓ hu hu₁ hτ₀ hτ100 hΩ16 A V
      (fun b => ζ b ω)

-- The declaration name and a docstring line exceed 100 characters.
set_option linter.style.longLine false in
/-- **Hermitian diagonalization in linear precision** (Theorem 4.2): let the machine meet
`NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ (constants $\mu_{\mathrm{MM}}$,
$\mu_{\mathrm{QR}}$, $c_{\mathrm N}$), with $\mu_{\mathrm{MM}}, \mu_{\mathrm{QR}}$ monotone
and nonnegative, $c_{\mathrm N} \ge 0$, and the samplers with measurable fibres and countable
ranges. Let the stored $\mathbf{A}$ have Hermitian decoding with $\|\mathbf{A}\|_2 \le R_0$, for
stored $R_0 > 0$, $\varepsilon$, $\beta$ (decoded values) with $0 < \varepsilon \le 2^{-15}$, $0 <
\theta \le 1$, a depth counter $\ell \ge$ `NLAlib.bisectionDepth` $\varepsilon$, and the
precomputed accuracy $$0 < \beta \le \frac{\varepsilon\sqrt\theta}{2880\,\ell\, n^{3/2}\bigl(2\sqrt
n + \sqrt{2\log(16n/\theta)}\bigr)} \,, \qquad
N_* = N\Bigl(\frac{\theta}{32n(n+1)\ell(\ell+1)}, \frac{\beta}{16n}\Bigr) \,.$$
If $640\,n^{3/2}(8 + \mu_{\mathrm{MM}}(n))(N_* + 1)\cdot16n(n+1)\ell(\ell+1)\,u \le
\theta\beta$, $(4\mu_{\mathrm{QR}}(n) + 4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1)u
\le \beta$, the sign step limit is at least $N_*$, $0 \le \tau$,
$100n^{3/2}\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon\min(R_0, 1))$,
$16(2R_0 + n + 2\ell + \sqrt{\log(16n/\theta)}) \le \Omega$, and the node samples $\zeta_a$ are
independent, each of law `NLAlib.eighSampleLaw` $n$, then
$$\mathbb{P}\bigl[\mathsf{eigh}(\mathbf{A}, \varepsilon, \theta) \text{ is not an approximate
diagonalization with residual } 2\varepsilon R_0 \text{ and } \mathbf{U} \text{ within }
\varepsilon/3 \text{ of unitary}\bigr] \le \theta \,,$$
$\mathsf{eigh}$ the decoded output of `NLAlib.eigh`. [Shah2024, Theorem 4.2], there with
$R_0 = \|\mathbf{A}\|_2$, node-dependent accuracies, the bit count of
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw`
with other constants, and an
operation count (not formalized). -/
theorem
    FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n}
    (hind : iIndepFun ζ μ) (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  have hae : ∀ᵐ ω ∂μ, ∀ a, ζ a ω = (hlaw a).aemeasurable.mk (ζ a) ω :=
    ae_all_iff.2 fun a => (hlaw a).aemeasurable.ae_eq_mk
  refine le_of_eq_of_le (measureReal_congr (Filter.eventuallyEq_set.2 ?_))
    (hM.measureReal_eigh_le_of_measurable hunifm hunifc hnormalm hnormalc hμM hμQ hμM₀ hμQ₀ hcN
      hA hR₀ hR₀pos hε hε₁ hθ hθ₁ hℓ hβ hβle hN husign hudefl hfuel hτ₀ hτ hΩ
      (fun a => (hlaw a).aemeasurable.measurable_mk)
      ((iIndepFun_congr fun a => (hlaw a).aemeasurable.ae_eq_mk).1 hind)
      fun a => (hlaw a).congr (hlaw a).aemeasurable.ae_eq_mk.symm)
  filter_upwards [hae] with ω hω
  have h2 : (fun a => ζ a ω) = fun a => (hlaw a).aemeasurable.mk (ζ a) ω := funext hω
  simp only [h2]

/-- Exponentiating the bit-count condition. -/
private theorem mul_le_mul_mul_sqrt_of_logb_le {e θ P N L S u : ℝ} (he : 0 < e) (hθ : 0 < θ)
    (hP : 0 < P) (hN : 0 < N) (hL : 0 < L) (hS : 0 < S) (hu : 0 < u)
    (h : Real.logb 2 e⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ + Real.logb 2 P + Real.logb 2 N +
      3 * Real.logb 2 L + Real.logb 2 S + 26 ≤ Real.logb 2 u⁻¹) :
    u * (2 ^ 26 * P * N * L ^ 3 * S) ≤ e * (θ * √θ) := by
  have hsθ : 0 < √θ := Real.sqrt_pos.mpr hθ
  have hK : 2 ^ 26 * P * N * L ^ 3 * S / (e * (θ * √θ)) ≤ u⁻¹ := by
    rw [← Real.logb_le_logb one_lt_two (by positivity) (by positivity), Real.logb_div
      (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
      (by positivity), Real.logb_mul (by positivity) (by positivity), Real.logb_mul he.ne'
      (by positivity), Real.logb_mul hθ.ne' hsθ.ne', Real.logb_pow,
      Real.logb_pow, Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hθ,
      Real.logb_self_eq_one one_lt_two]
    rw [Real.logb_inv, Real.logb_inv] at h
    push_cast
    linarith
  rw [div_le_iff₀ (by positivity)] at hK
  calc u * (2 ^ 26 * P * N * L ^ 3 * S) ≤ u * (u⁻¹ * (e * (θ * √θ))) :=
        mul_le_mul_of_nonneg_left hK hu.le
    _ = e * (θ * √θ) := by rw [← mul_assoc, mul_inv_cancel₀ hu.ne', one_mul]

/-- The exponentiated bit count gives both precision conditions of Theorem 4.2. -/
private theorem mul_le_mul_and_mul_le_of_mul_le_mul_sqrt {n l sn m D S N b e θ u : ℝ} (hn : 1 ≤ n)
    (hl : 1 ≤ l) (hsn : sn * sn = n) (hsn0 : 0 ≤ sn) (hm : 0 ≤ m) (hD : 0 ≤ D) (hS : 0 < S)
    (hN : 0 ≤ N) (he : 0 ≤ e) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hu : 0 ≤ u)
    (key : u * (2 ^ 26 * (n ^ 4 * (n + 1) * (8 + m) + n * sn * D) * (N + 1) * (l + 1) ^ 3 * S) ≤
      e * (θ * √θ))
    (hβ : e * √θ ≤ 2 * (2880 * l * n * sn * S) * b) :
    640 * n * sn * (8 + m) * (N + 1) * (16 * n * (n + 1) * l * (l + 1)) * u ≤ θ * b ∧
      D * u ≤ b := by
  have hsθ : 0 < √θ := Real.sqrt_pos.mpr hθ
  have hsn1 : 1 ≤ sn := by nlinarith
  have hc0 : 0 < 2 * (2880 * l * n * sn * S) := by positivity
  have hA : 0 ≤ n ^ 4 * (n + 1) * (8 + m) := by positivity
  have hB : 0 ≤ n * sn * D := by positivity
  have hl3 : l ^ 2 * (l + 1) ≤ (l + 1) ^ 3 := by nlinarith
  have hl3' : l ≤ (l + 1) ^ 3 := by nlinarith
  constructor
  · refine le_of_mul_le_mul_right ?_ hc0
    calc 640 * n * sn * (8 + m) * (N + 1) * (16 * n * (n + 1) * l * (l + 1)) * u *
          (2 * (2880 * l * n * sn * S))
        = 58982400 * (n ^ 4 * (n + 1) * (8 + m)) * (N + 1) * (l ^ 2 * (l + 1)) * S * u := by
          rw [← hsn]; ring
      _ ≤ 2 ^ 26 * (n ^ 4 * (n + 1) * (8 + m) + n * sn * D) * (N + 1) * (l + 1) ^ 3 * S * u := by
          gcongr ?_ * ?_ * _ * ?_ * _ * _
          · norm_num
          · linarith
      _ ≤ e * (θ * √θ) := by linarith
      _ ≤ θ * b * (2 * (2880 * l * n * sn * S)) := by
          have := mul_le_mul_of_nonneg_left hβ hθ.le
          linarith
  · refine le_of_mul_le_mul_right ?_ hc0
    calc D * u * (2 * (2880 * l * n * sn * S)) = 5760 * (n * sn * D) * 1 * l * S * u := by ring
      _ ≤ 2 ^ 26 * (n ^ 4 * (n + 1) * (8 + m) + n * sn * D) * (N + 1) * (l + 1) ^ 3 * S * u := by
          gcongr ?_ * ?_ * ?_ * ?_ * _ * _
          · norm_num
          · linarith
          · linarith
      _ ≤ e * (θ * √θ) := by linarith
      _ ≤ e * √θ := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hsθ.le hθ₁) he
      _ ≤ b * (2 * (2880 * l * n * sn * S)) := by linarith

-- The declaration name and a docstring line exceed 100 characters.
set_option linter.style.longLine false in
/-- **The bit count of Hermitian diagonalization** (Theorem 4.2, in bits): let the machine meet
`NLAlib.FloatMachine.IsAccurate` with $u > 0$, monotone $\mu_{\mathrm{MM}}, \mu_{\mathrm{QR}} \ge
0$,
$c_{\mathrm N} \ge 0$ and samplers with measurable fibres and countable ranges; let the stored
$n \times n$ input $\mathbf{A}$ be Hermitian with $\|\mathbf{A}\|_2 \le R_0$, $R_0 > 0$,
$0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$ and $\ell \ge$ `NLAlib.bisectionDepth`
$\varepsilon$;
let the accuracy be within a factor $2$ of its bound, $\beta_*/2 \le \beta \le \beta_*$ with
$\beta_* = \varepsilon\sqrt\theta/(2880\ell n^{3/2}(2\sqrt n + \sqrt{2\log(16n/\theta)}))$, let
$N_* =$ `NLAlib.newtonSchulzSteps` $(\theta/(32n(n+1)\ell(\ell+1)))\,(\beta/(16n))$ be at most the
step limit, the floor $0 \le \tau$ with $100n^{3/2}\tau \le \min(\sqrt{\theta/(8n)},
\varepsilon\min(R_0,
1))$, the range $16(2R_0 + n + 2\ell + \sqrt{\log(16n/\theta)}) \le \Omega$, the ideal samples of
the nodes independent with law `NLAlib.eighSampleLaw` $n$, and
$$\begin{aligned}\log_2\frac1u \ge{}& \log_2\frac1\varepsilon + \frac32\log_2\frac1\theta +
\log_2\Bigl(n^4(n + 1)(8 + \mu_{\mathrm{MM}}(n)) + n^{3/2}\bigl(4\mu_{\mathrm{QR}}(n) +
4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1\bigr)\Bigr) \\
&+ \log_2(N_* + 1) + 3\log_2(\ell + 1) +
\log_2\bigl(2\sqrt n + \sqrt{2\log(16n/\theta)}\bigr) + 26 \,,\end{aligned}$$
the probability that `NLAlib.eigh` is not an approximate diagonalization with residual
$2\varepsilon R_0$ and singular values within $\varepsilon/3$ of $1$ is at most $\theta$. Since
$\ell = O(\log(1/\varepsilon))$ and
$N_* = O(\log(n\ell/\theta) + \log\log(n/(\varepsilon\theta)))$, this is
$\log_2(1/\varepsilon) + O(\log n + \log\log(1/\varepsilon)) + \tfrac32\log_2(1/\theta)$ bits.
[Shah2024, Theorem 4.2], there $\log_2(1/\varepsilon) + \log_2\max(n^{1.5}\mu_{\mathrm{QR}},
n^{1.5}\sqrt n c_{\mathrm N}, n^{4.5}\mu_{\mathrm{MM}}) + 2\log_2\log_2(1/\varepsilon) +
1.5\log_2(1/\theta) + \log_2\log_2(n\log_2(1/\varepsilon)/\theta) + 23$; the exponent of $n$ and
the third power of $\ell$ (from the corrected shift-avoidance probability) differ. -/
theorem
    FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))))
    (hβge : dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))) / 2 ≤ dec β)
    {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (hu : 0 < u)
    (hbits : Real.logb 2 (dec ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
      Real.logb 2 (n ^ 4 * (n + 1) * (8 + μM n) +
        n * √(n : ℝ) * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1)) +
      Real.logb 2 (Nst + 1) + 3 * Real.logb 2 (ℓ + 1) +
      Real.logb 2 (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))) + 26 ≤ Real.logb 2 u⁻¹)
    {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n}
    (hind : iIndepFun ζ μ) (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  obtain ⟨hn, hℓ0, hb1⟩ := pos_and_le_one_of_le_div hε₁ hθ₁ hβ hβle
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ0
  have hμMn : 0 ≤ μM n := hμM₀.trans (hμM (Nat.zero_le n))
  have hμQn : 0 ≤ μQ n := hμQ₀.trans (hμQ (Nat.zero_le n))
  have hS2 : 2 ≤ 2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)) := by
    linarith [Real.one_le_sqrt.mpr hn1, Real.sqrt_nonneg (2 * Real.log (16 * n / θ))]
  have hNst : 0 ≤ Nst := hN ▸ newtonSchulzSteps_nonneg_of_pos (by positivity) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; linarith)
  have hβ' : dec ε * √θ ≤ 2 * (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))) * dec β := by
    rw [div_div, div_le_iff₀ (by positivity)] at hβge; linarith
  obtain ⟨h₁, h₂⟩ := mul_le_mul_and_mul_le_of_mul_le_mul_sqrt hn1 hl1
    (Real.mul_self_sqrt (by positivity)) (Real.sqrt_nonneg _) hμMn (by positivity) (by linarith)
    hNst hε.le hθ hθ₁ hu.le
    (mul_le_mul_mul_sqrt_of_logb_le hε hθ (by positivity) (by linarith) (by positivity)
      (by linarith) hu hbits) hβ'
  exact hM.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw
    hunifm hunifc hnormalm hnormalc hμM hμQ hμM₀ hμQ₀ hcN hA hR₀ hR₀pos hε hε₁ hθ hθ₁ hℓ hβ hβle hN
    h₁ h₂ hfuel hτ₀ hτ hΩ hind hlaw

/-- The exponent-bit condition bounds $L$ by $2^{2^{E-1} - 2}$. -/
private theorem le_zpow_of_logb_logb_add_two_le {L : ℝ} {E : ℕ} (hE : 2 ≤ E) (hL : 1 ≤ L)
    (h : Real.logb 2 (Real.logb 2 L + 2) + 1 ≤ E) : L ≤ (2 : ℝ) ^ ((2 : ℤ) ^ (E - 1) - 2) := by
  have h0 : 0 ≤ Real.logb 2 L := Real.logb_nonneg one_lt_two hL
  have h1 : Real.logb 2 L + 2 ≤ (2 : ℝ) ^ (E - 1) := by
    have : Real.logb 2 (Real.logb 2 L + 2) ≤ ((E - 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ E)]; linarith
    rwa [Real.logb_le_iff_le_rpow one_lt_two (by linarith), Real.rpow_natCast] at this
  have h2 : Real.logb 2 L ≤ (((2 : ℤ) ^ (E - 1) - 2 : ℤ) : ℝ) := by push_cast; linarith
  rwa [Real.logb_le_iff_le_rpow one_lt_two (by linarith), Real.rpow_intCast] at h2

/-- The floor and range hypotheses of Theorem 4.2 from the bounded-format bounds. -/
private theorem mul_le_min_and_le_of_mul_le {n ℓ e θ R τ Ω : ℝ} (hn : 0 ≤ n) (hℓ : 0 ≤ ℓ)
    (he : 0 < e) (he₁ : e ≤ 1) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hR : 1 / 2 ≤ R) (hR₁ : R ≤ 1)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (1536 * (n + ℓ + 2) ^ 2) ≤ e * θ)
    (hΩ : 3072 * (n + ℓ + 2) ^ 2 ≤ Ω * (e * θ)) :
    τ * (100 * n * √n) ≤ min (√(θ / (8 * n))) (e * min R 1) ∧
      16 * (2 * R + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω := by
  have hm : 2 ≤ n + ℓ + 2 := by linarith
  have hm2 : 0 < 1536 * (n + ℓ + 2) ^ 2 := by positivity
  have hs : √n ^ 2 = n := Real.sq_sqrt hn
  have hsn : √n ≤ n + ℓ + 2 := by nlinarith [Real.sqrt_nonneg n]
  have hnsn : n * √n ≤ (n + ℓ + 2) ^ 2 := by
    rw [sq]; exact mul_le_mul (by linarith) hsn (Real.sqrt_nonneg n) (by linarith)
  have heθ : e * θ ≤ θ := mul_le_of_le_one_left hθ.le he₁
  have hX0 : 0 ≤ τ * (100 * n * √n) := by positivity
  have hX : τ * (100 * n * √n) * (1536 * (n + ℓ + 2) ^ 2) ≤ 100 * n * √n * (e * θ) := by
    have := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ 100 * n * √n)
    linarith
  refine ⟨le_min ?_ ?_, ?_⟩
  · rcases hn.eq_or_lt with rfl | hn0
    · simp
    rw [← Real.sqrt_sq hX0]
    refine Real.sqrt_le_sqrt ?_
    rw [le_div_iff₀ (by positivity)]
    refine le_of_mul_le_mul_right ?_ (pow_pos hm2 2)
    have h1 := pow_le_pow_left₀ (by positivity) hX 2
    have h2 : (100 * n * √n * (e * θ)) ^ 2 = 10000 * n ^ 3 * (e * θ) ^ 2 := by
      linear_combination (10000 * n ^ 2 * (e * θ) ^ 2) * hs
    have h3 : n ^ 4 ≤ (n + ℓ + 2) ^ 4 := pow_le_pow_left₀ hn (by linarith) 4
    have h4 : (e * θ) ^ 2 ≤ θ := by nlinarith [mul_pos he hθ]
    have h5 := mul_le_mul h3 h4 (by positivity) (by positivity)
    nlinarith
  · have h1 : 1 / 2 ≤ min R 1 := le_min hR (by norm_num)
    refine le_trans ?_ (mul_le_mul_of_nonneg_left h1 he.le)
    refine le_of_mul_le_mul_right ?_ hm2
    have := mul_le_mul_of_nonneg_left hnsn (by positivity : (0 : ℝ) ≤ 100 * (e * θ))
    have := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right he.le hθ₁)
      (sq_nonneg (n + ℓ + 2))
    linarith [mul_nonneg he.le (sq_nonneg (n + ℓ + 2))]
  · have hy : 0 ≤ 16 * n / θ := by positivity
    have h1 : √(Real.log (16 * n / θ)) ≤ 16 * n / θ + 1 :=
      (Real.sqrt_le_sqrt (Real.log_le_self hy)).trans
        (by nlinarith [Real.sq_sqrt hy, Real.sqrt_nonneg (16 * n / θ)])
    have h2 : (16 * n / θ) * θ = 16 * n := div_mul_cancel₀ _ hθ.ne'
    refine le_of_mul_le_mul_right ?_ (mul_pos he hθ)
    calc 16 * (2 * R + n + 2 * ℓ + √(Real.log (16 * n / θ))) * (e * θ)
        ≤ 16 * (2 + n + 2 * ℓ + (16 * n / θ + 1)) * (e * θ) := by gcongr; linarith
      _ = 16 * (3 + n + 2 * ℓ) * (e * θ) + 256 * n * e := by linear_combination 16 * e * h2
      _ ≤ 16 * (3 + n + 2 * ℓ) + 256 * n := by
          have := mul_le_mul_of_nonneg_left (mul_le_one₀ he₁ hθ.le hθ₁)
            (by positivity : (0 : ℝ) ≤ 16 * (3 + n + 2 * ℓ))
          have := mul_le_mul_of_nonneg_left he₁ (by positivity : (0 : ℝ) ≤ 256 * n)
          linarith
      _ ≤ 3072 * (n + ℓ + 2) ^ 2 := by nlinarith
      _ ≤ Ω * (e * θ) := hΩ

-- The declaration name and a docstring line exceed 100 characters.
set_option linter.style.longLine false in
/-- **Hermitian diagonalization in a bounded binary format: $\log_2\log_2(n/(\varepsilon\theta)) +
O(1)$ exponent bits suffice** (Theorem 4.2 for a finite exponent range): let the machine meet
`NLAlib.FloatMachine.IsAccurate` with $u = 2^{-p}$, floor $2^{e_{\min} + p - 1}$ (the smallest
normal number) and range the largest finite number of a binary format with $E \ge 2$ exponent
bits, precision $p$ and smallest exponent $e_{\min}$ (as
`NLAlib.exists_floatMachine_isAccurate_binaryFloatRound` provides), with the other hypotheses of
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw`,
the input scaled so that $1/2 \le R_0 \le 1$ (an exact power-of-two scaling), the precision
condition
there with $\log_2(1/u) = p$, the ideal samples of the nodes independent, each with law
`NLAlib.eighSampleLaw` $n$, and
$$\log_2\Bigl(\log_2\frac{1536\,(n + \ell + 2)^2}{\varepsilon\theta} + 2\Bigr) + 1 \le E \,.$$
Then the failure probability is at most $\theta$. With $\ell = O(\log(1/\varepsilon))$ this is
$\log_2\log_2(n/(\varepsilon\theta)) + O(1)$ exponent bits, the claim of [Shah2024, Section 1.2]
("$\lg\lg(n/\varepsilon) + O(1)$ bits to store the exponent"), with the $\theta$ it omits. -/
theorem
    FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le_of_hasLaw_eighSampleLaw
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} (fmt : Float.Model.Format)
    (hE : 2 ≤ fmt.exponentBits) {cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) fmt.maxFinite μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀)
    (hR₀half : 1 / 2 ≤ dec R₀) (hR₀one : dec R₀ ≤ 1) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15)
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ} (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))))
    (hβge : dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))) / 2 ≤ dec β)
    {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (hbits : Real.logb 2 (dec ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
      Real.logb 2 (n ^ 4 * (n + 1) * (8 + μM n) +
        n * √(n : ℝ) * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1)) +
      Real.logb 2 (Nst + 1) + 3 * Real.logb 2 (ℓ + 1) +
      Real.logb 2 (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))) + 26 ≤ fmt.mantissaBits)
    (hexp : Real.logb 2 (Real.logb 2 (1536 * (n + ℓ + 2) ^ 2 / (dec ε * θ)) + 2) + 1 ≤
      fmt.exponentBits)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n} (hind : iIndepFun ζ μ)
    (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  have hτeq : fmt.minExponent + (fmt.mantissaBits : ℤ) - 1 =
      -((2 : ℤ) ^ (fmt.exponentBits - 1) - 2) := by
    simp only [Float.Model.Format.minExponent]; ring
  have hB : fmt.maxExponentBound = (2 : ℤ) ^ (fmt.exponentBits - 1) - fmt.mantissaBits := by
    have h1 : 1 ≤ 2 ^ (fmt.exponentBits - 1) := Nat.one_le_two_pow
    have h2 : (2 : ℤ) ^ fmt.exponentBits = 2 * 2 ^ (fmt.exponentBits - 1) := by
      rw [← pow_succ']; congr 1; omega
    simp only [Float.Model.Format.maxExponentBound, Float.Model.Format.exponentBias,
      Float.Model.Format.mantissaBits]
    rw [Nat.cast_sub h1]
    push_cast
    rw [h2]
    ring
  have hp : 1 ≤ fmt.mantissaBits := by simp only [Float.Model.Format.mantissaBits]; omega
  have hmax : 2 * (2 : ℝ) ^ ((2 : ℤ) ^ (fmt.exponentBits - 1) - 2) ≤ fmt.maxFinite := by
    rw [Float.Model.Format.maxFinite, hB]
    have h2p : (2 : ℝ) ≤ 2 ^ fmt.mantissaBits := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp
    have : 2 * (2 : ℝ) ^ ((2 : ℤ) ^ (fmt.exponentBits - 1) - 2) =
        (2 ^ fmt.mantissaBits / 2) * 2 ^ ((2 : ℤ) ^ (fmt.exponentBits - 1) - fmt.mantissaBits) := by
      rw [← zpow_natCast, div_eq_mul_inv, ← zpow_neg_one, ← zpow_add₀ two_ne_zero,
        ← zpow_add₀ two_ne_zero, mul_comm (2 : ℝ), ← zpow_add_one₀ two_ne_zero]
      congr 1; ring
    rw [this]
    gcongr
    linarith
  set m : ℝ := (n : ℝ) + ℓ + 2 with hm_def
  have hm : 2 ≤ m := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); have := (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)
    linarith
  have he₁ : dec ε ≤ 1 := hε₁.trans (by norm_num)
  have hL1 : 1 ≤ 1536 * m ^ 2 / (dec ε * θ) := by
    rw [le_div_iff₀ (by positivity), one_mul]
    nlinarith [mul_le_one₀ he₁ hθ.le hθ₁]
  have hL := le_zpow_of_logb_logb_add_two_le hE hL1 (by simpa only [m] using hexp)
  have hτ : (2 : ℝ) ^ (fmt.minExponent + (fmt.mantissaBits : ℤ) - 1) *
      (1536 * m ^ 2) ≤ dec ε * θ := by
    rw [hτeq, zpow_neg, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hL
    linarith
  have hΩ : 3072 * m ^ 2 ≤ fmt.maxFinite * (dec ε * θ) := by
    rw [div_le_iff₀ (by positivity)] at hL
    nlinarith [mul_le_mul_of_nonneg_right hmax (by positivity : 0 ≤ dec ε * θ)]
  obtain ⟨h₁, h₂⟩ := mul_le_min_and_le_of_mul_le (Nat.cast_nonneg n) (Nat.cast_nonneg ℓ) hε he₁
    hθ hθ₁ hR₀half hR₀one (by positivity) hτ hΩ
  refine hM.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw
    hunifm hunifc hnormalm hnormalc hμM hμQ hμM₀ hμQ₀ hcN hA hR₀ (by linarith) hε hε₁ hθ hθ₁ hℓ hβ
    hβle hβge hN
    (by positivity) ?_ hfuel (by positivity) h₁ h₂ hind hlaw
  rwa [inv_pow, inv_inv, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

end NLAlib
