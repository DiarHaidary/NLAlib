/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Matrix.Computation.SpectralBisection.Node
public import NLAlibScaffold.Matrix.Computation.SpectralBisection.Tree

/-!
# Global deterministic guarantee of spectral bisection (scaffold)

Statements for `NLAlib/Matrix/Computation/SpectralBisection/Global.lean` (stage HDIAG, wave W4,
design note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.8): if every internal node
of the recursion tree of `NLAlib.eigh` has a good sample, the output is an approximate
diagonalization with residual $2\varepsilon R_0$ and singular values of $\mathbf{U}$ in
$[1 - \varepsilon/3, 1 + \varepsilon/3]$ ([Shah2024, Theorem 4.2], deterministic part). The
probability is in `NLAlibScaffold/Eigensolvers/SpectralBisection.lean`.

## Main results

* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample`: the
  global deterministic guarantee.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- The Newton–Schulz step count of an internal node is at most the global $N_*$. -/
private lemma newtonSchulzSteps_node_le {n k ℓ ℓy : ℕ} {Ry β θ : ℝ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hℓ : 1 ≤ ℓ) (hℓy : 1 ≤ ℓy) (hℓy₂ : ℓy ≤ 2 * ℓ) (hRy : 0 < Ry) (hθ : 0 < θ) (hβ : 0 < β)
    (hβ₁ : β ≤ 1) :
    newtonSchulzSteps (θ * Ry / (2 * k * ℓy * (n + 1) * (ℓ + 1)) / (8 * Ry)) (β / (16 * k)) ≤
      newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (β / (16 * n)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓy' : (1 : ℝ) ≤ ℓy := by exact_mod_cast hℓy
  have hℓy₂' : (ℓy : ℝ) ≤ 2 * ℓ := by exact_mod_cast hℓy₂
  have hn' : (0 : ℝ) < n := by linarith
  have he : θ * Ry / (2 * k * ℓy * (n + 1) * (ℓ + 1)) / (8 * Ry) =
      θ / (16 * k * ℓy * (n + 1) * (ℓ + 1)) := by
    field_simp
    ring
  rw [he]
  refine (newtonSchulzSteps_le_of_le_abs (by positivity) ?_).trans
    (newtonSchulzSteps_le_of_le (by positivity) ?_ ?_)
  · rw [abs_of_pos (by positivity)]
    gcongr θ / ?_
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul hkn' hℓy₂' (by positivity) (by positivity))
      (by positivity : (0 : ℝ) ≤ 16 * (n + 1) * (ℓ + 1))
    nlinarith [h2]
  · gcongr
  · rw [div_le_iff₀ (by positivity)]
    linarith

/-- The global accuracy is below the deflation accuracy bound of every internal node. -/
private lemma le_bisectionSignTol_node {n k ℓ ℓy : ℕ} {ε εy β θ : ℝ} (hk : 0 < k) (hkn : k ≤ n)
    (hℓ : 20 ≤ ℓ) (hℓy : ℓ ≤ ℓy) (hℓy₂ : ℓy ≤ 2 * ℓ) (hεy : ε / 3 ≤ εy) (hε : 0 < ε)
    (hθ : 0 < θ) (hβle : β ≤ ε * √θ / (2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) +
      √(2 * Real.log (16 * n / θ))))) :
    β ≤ bisectionSignTol k εy (θ / (4 * n)) ℓy := by
  have hn : 0 < n := hk.trans_le hkn
  have hℓ0 : 0 < ℓ := by omega
  have hℓy0 : 0 < ℓy := by omega
  have hℓy' : (20 : ℝ) ≤ ℓy := by exact_mod_cast hℓ.trans hℓy
  have hℓy₂' : (ℓy : ℝ) ≤ 2 * ℓ := by exact_mod_cast hℓy₂
  have h4 : 4 / (θ / (4 * n)) = 16 * n / θ := by field_simp; ring
  have hsq : √θ = 2 * √(θ / (4 * n)) * √(n : ℝ) := by
    rw [mul_assoc, ← Real.sqrt_mul (by positivity), show θ / (4 * n) * n = θ / 2 ^ 2 by
      field_simp; ring, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by norm_num)]
    ring
  unfold bisectionSignTol
  rw [h4]
  set L := 2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)) with hL
  have hL0 : 0 < L := by positivity
  calc β ≤ ε * √θ / (2880 * ℓ * n * √(n : ℝ) * L) := hβle
    _ = ε / 1440 * √(θ / (4 * n)) / (ℓ * n * L) := by rw [hsq]; field_simp; ring
    _ ≤ 19 * ε / 21600 * √(θ / (4 * n)) / (ℓ * n * L) := by
      gcongr ?_ * _ / _
      linarith
    _ = 19 / 20 * (ε / 3) / (5 * (2 * ℓ)) * √(θ / (4 * n)) / (36 * n * L) := by
      field_simp; ring
    _ ≤ _ := by
      have h20 : 1 / (ℓy : ℝ) ≤ 1 / 20 := by gcongr
      set c := 1 - 1 / (ℓy : ℝ) with hc
      have hc0 : 0 < c := by linarith
      have hεy0 : 0 < εy := by linarith
      gcongr
      · linarith
      · rw [hL]
        gcongr

/-- The global sign-step roundoff condition gives the node's. -/
private lemma husign_node {n k ℓ ℓy : ℕ} {Ry β θ u Nst Ny : ℝ} {μ : ℕ → ℝ} (hμ : Monotone μ)
    (hμ₀ : 0 ≤ μ 0) (hk : 0 < k) (hkn : k ≤ n) (hℓ : 0 < ℓ) (hℓy : 0 < ℓy)
    (hℓy₂ : ℓy ≤ 2 * ℓ) (hRy : 0 < Ry) (hθ : 0 < θ) (hβ : 0 ≤ β) (hu : 0 ≤ u)
    (hNy : Ny ≤ Nst)
    (husign : 640 * n * √(n : ℝ) * (8 + μ n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * β) :
    640 * k * √(k : ℝ) * (8 + μ k) * (Ny + 1) * u ≤
      θ * Ry / (2 * k * ℓy * (n + 1) * (ℓ + 1)) / (4 * Ry) * β := by
  have hμk : 0 ≤ μ k := hμ₀.trans (hμ (Nat.zero_le k))
  have hμkn : μ k ≤ μ n := hμ hkn
  have hn : 0 < n := hk.trans_le hkn
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hℓy₂' : (ℓy : ℝ) ≤ 2 * ℓ := by exact_mod_cast hℓy₂
  have hA : 0 ≤ 640 * k * √(k : ℝ) * (8 + μ k) := by positivity
  rcases le_or_gt (Ny + 1) 0 with h | h
  · calc 640 * k * √(k : ℝ) * (8 + μ k) * (Ny + 1) * u ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hA h) hu
      _ ≤ _ := by positivity
  have hD : 0 < (16 * n * (n + 1) * ℓ * (ℓ + 1) : ℝ) := by positivity
  have he : θ * Ry / (2 * k * ℓy * (n + 1) * (ℓ + 1)) / (4 * Ry) =
      θ / (8 * k * ℓy * (n + 1) * (ℓ + 1)) := by
    field_simp
    ring
  rw [he]
  calc 640 * k * √(k : ℝ) * (8 + μ k) * (Ny + 1) * u ≤
        640 * n * √(n : ℝ) * (8 + μ n) * (Nst + 1) * u := by
        have : 0 ≤ μ n := hμk.trans hμkn
        gcongr
    _ ≤ θ * β / (16 * n * (n + 1) * ℓ * (ℓ + 1)) := by
        rw [le_div_iff₀ hD]
        linarith
    _ = θ / (16 * n * (n + 1) * ℓ * (ℓ + 1)) * β := by ring
    _ ≤ θ / (8 * k * ℓy * (n + 1) * (ℓ + 1)) * β := by
        gcongr θ / ?_ * _
        have h2 := mul_le_mul_of_nonneg_left (mul_le_mul hkn' hℓy₂' (by positivity)
          (by positivity)) (by positivity : (0 : ℝ) ≤ 8 * (n + 1) * (ℓ + 1))
        nlinarith [h2]

/-- The global numeric consequences of the hypotheses of `NLAlib.eigh`'s guarantee: the depth
counter is at least $20$, and the conditions of
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params` hold. -/
private lemma eigh_global_bounds {u τ Ω : ℝ} {μM : ℕ → ℝ} (hu : 0 ≤ u) (hμM : Monotone μM)
    (hμM₀ : 0 ≤ μM 0) {n : ℕ} (hn : 0 < n) {R₀ ε β θ : ℝ} (hR₀pos : 0 < R₀) (hε : 0 < ε)
    (hε₁ : ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ} (hℓ : bisectionDepth ε ≤ ℓ)
    (hβ : 0 < β) (hβle : β ≤ ε * √θ / (2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) +
      √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * β) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (ε * min R₀ 1))
    (hΩ : 16 * (2 * R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω) :
    20 ≤ ℓ ∧ 100 * ℓ ^ 2 * u ≤ 1 ∧ 100 * τ ≤ ε * min R₀ 1 ∧ 16 * (R₀ + ℓ) ≤ Ω := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn'
  have hℓ20 : 20 ≤ ℓ := by
    refine le_trans ?_ hℓ
    have h15 : (2 : ℝ) ^ 15 ≤ ε⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hε, ← inv_pow]
      exact hε₁
    have h14 : ((14 : ℕ) : ℝ) < Real.logb 2 ε⁻¹ := by
      rw [Real.lt_logb_iff_rpow_lt one_lt_two (by positivity)]
      norm_num
      linarith
    have := Nat.lt_ceil.mpr h14
    unfold bisectionDepth
    omega
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ20
  have hβ₁ : β ≤ ε := by
    have hL : 1 ≤ 2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)) := by
      linarith [Real.sqrt_nonneg (2 * Real.log (16 * n / θ))]
    have hden := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (show (1 : ℝ) ≤ 2880 * ℓ by linarith) hn') hs1) hL
    refine hβle.trans ((div_le_self (by positivity) hden).trans ?_)
    exact mul_le_of_le_one_right hε.le (Real.sqrt_le_one.mpr hθ₁)
  have hε1 : ε ≤ 1 := hε₁.trans (by norm_num)
  have hNst : 0 ≤ Nst := by
    rw [hN]
    refine newtonSchulzSteps_nonneg (by positivity) ?_ (by positivity) ?_
    · have hD : (1 : ℝ) ≤ n * (n + 1) * ℓ * (ℓ + 1) :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hn' (by linarith)) (by linarith)) (by linarith)
      rw [div_le_iff₀ (by positivity)]
      linarith
    · rw [div_le_iff₀ (by positivity)]
      linarith
  have hu₁ : 100 * ℓ ^ 2 * u ≤ 1 := by
    have hμn : 0 ≤ μM n := hμM₀.trans (hμM (Nat.zero_le n))
    have hP : 4 ≤ 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) := by
      calc (4 : ℝ) ≤ 640 * 1 * 1 * 8 * 1 := by norm_num
        _ ≤ _ := by gcongr <;> linarith
    have hQ : 32 * (ℓ : ℝ) ^ 2 ≤ 16 * n * (n + 1) * ℓ * (ℓ + 1) := by
      calc 32 * (ℓ : ℝ) ^ 2 = 16 * 1 * (1 + 1) * ℓ * ℓ := by ring
        _ ≤ _ := by gcongr; linarith
    have hPQ := mul_le_mul hP hQ (by positivity) (by linarith)
    have hθβ : θ * β ≤ 1 := mul_le_one₀ hθ₁ hβ.le (hβ₁.trans hε1)
    have h0 : 0 ≤ (ℓ : ℝ) ^ 2 * u := by positivity
    linarith [mul_le_mul_of_nonneg_right hPQ hu]
  have hτ' : 100 * τ ≤ ε * min R₀ 1 := by
    have : 100 * τ ≤ τ * (100 * n * √(n : ℝ)) := by
      have h1 : (1 : ℝ) ≤ n * √(n : ℝ) := one_le_mul_of_one_le_of_one_le hn' hs1
      linarith [mul_le_mul_of_nonneg_left h1 hτ₀]
    exact this.trans (hτ.trans (min_le_right _ _))
  have hΩ' : 16 * (R₀ + ℓ) ≤ Ω := by
    linarith [Real.sqrt_nonneg (Real.log (16 * n / θ))]
  exact ⟨hℓ20, hu₁, hτ', hΩ'⟩

/-- An internal node of the tree of `NLAlib.eigh` (size at least $2$, positive window) with
the parameters of `NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params` meets the
hypotheses of the local guarantee, and so returns an approximate diagonalization once its
children (with the child invariant) do. -/
private lemma isApproxDiagonalization_eighAux_succ_of_node {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hμM : Monotone μM) (hμQ : Monotone μQ)
    (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN) {n : ℕ} {R₀ ε β : F} {θ : ℝ}
    (hR₀pos : 0 < dec R₀) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ)
    (hθ₁ : θ ≤ 1) {ℓ : ℕ} (hℓ : 20 ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) +
      √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω) {y : EighNode F}
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hkn : y.k ≤ n) (hℓy : ℓ ≤ y.ℓ) (hℓy₂ : y.ℓ ≤ 2 * ℓ) (hεy : dec ε / 3 ≤ dec y.ε)
    (hεy' : dec y.ε ≤ dec ε) (hRy : dec y.R ≤ dec R₀) (hk : 2 ≤ y.k) (hRpos : 0 < dec y.R)
    {f : ℕ} {s : List Bool → EighSample ℝ ℂ n}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false →
      IsEighGoodSample dec (θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)))
        (√(θ / (8 * n)) / y.k) (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (16 * n / θ)))) y (s []))
    (hchild : ∀ (b : Bool) (y' : EighNode F), eighChild M n signFuel R₀ β y (s []) b = some y' →
      (decodeMatrix dec y'.A).IsHermitian → specNorm (decodeMatrix dec y'.A) ≤ dec y'.R →
      IsApproxDiagonalization (decodeMatrix dec y'.A)
        (decodeMatrix dec (eighAux M n signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).1)
        (fun i => dec ((eighAux M n signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).2 i))
        (dec y'.ε * (dec y'.R + dec R₀)) (dec y'.ε / 3)) :
    IsApproxDiagonalization (decodeMatrix dec y.A)
      (decodeMatrix dec (eighAux M n signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).1)
      (fun i => dec ((eighAux M n signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).2 i))
      (dec y.ε * (dec y.R + dec R₀)) (dec y.ε / 3) := by
  have hn : 0 < n := by omega
  have hk0 : 0 < y.k := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk0
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓy' : (ℓ : ℝ) ≤ y.ℓ := by exact_mod_cast hℓy
  have hℓy₂' : (y.ℓ : ℝ) ≤ 2 * ℓ := by exact_mod_cast hℓy₂
  have hkn' : (y.k : ℝ) ≤ n := by exact_mod_cast hkn
  have hρ2 : θ / (4 * n) / 2 = θ / (8 * n) := by field_simp; ring
  have hρ4 : 4 / (θ / (4 * n)) = 16 * n / θ := by field_simp; ring
  have hε1 : dec ε ≤ 1 := hε₁.trans (by norm_num)
  have hβ₁ : dec β ≤ 1 := by
    have hs1 : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn'
    have hL : 1 ≤ 2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)) := by
      linarith [Real.sqrt_nonneg (2 * Real.log (16 * n / θ))]
    have hden := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (show (1 : ℝ) ≤ 2880 * ℓ by linarith) hn') hs1) hL
    have hεθ : dec ε * √θ ≤ 1 := by
      nlinarith [Real.sqrt_le_one.mpr hθ₁, Real.sqrt_nonneg θ]
    exact hβle.trans ((div_le_self (by positivity) hden).trans hεθ)
  have hNy := newtonSchulzSteps_node_le hk0 hkn (by omega) (by omega) hℓy₂ hRpos hθ hβ hβ₁
  have hμMk : 0 ≤ μM y.k := hμM₀.trans (hμM (Nat.zero_le _))
  have hμQk : 0 ≤ μQ y.k := hμQ₀.trans (hμQ (Nat.zero_le _))
  have hτy : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(θ / (4 * n) / 2)) (dec y.ε * dec R₀) := by
    rw [hρ2]
    have h0 : τ * (4 * y.k * √(y.k : ℝ)) * 25 ≤ τ * (100 * n * √(n : ℝ)) := by
      calc _ = τ * (100 * y.k * √(y.k : ℝ)) := by ring
        _ ≤ _ := by gcongr
    have h1 := hτ.trans (min_le_left _ _)
    have h2 := hτ.trans (min_le_right _ _)
    have h3 : dec ε * min (dec R₀) 1 ≤ dec ε * dec R₀ := by gcongr; exact min_le_left _ _
    have h4 : 0 ≤ τ * (4 * y.k * √(y.k : ℝ)) := by positivity
    have h5 := mul_le_mul_of_nonneg_right hεy hR₀pos.le
    have h6 : 0 ≤ dec ε * dec R₀ := by positivity
    exact le_min (by linarith) (by linarith)
  have hD1 : (1 : ℝ) ≤ 2 * y.k * y.ℓ * (n + 1) * (ℓ + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) (by linarith)) (by linarith)
  have hw : 0 < θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)) := by positivity
  have hwR : θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)) ≤ dec y.R := by
    rw [div_le_iff₀ (by positivity)]
    exact (mul_le_mul_of_nonneg_right hθ₁ hRpos.le).trans
      ((mul_le_mul_of_nonneg_right hD1 hRpos.le).trans_eq (mul_comm _ _))
  have hβtol := le_bisectionSignTol_node hk0 hkn hℓ hℓy hℓy₂ hεy hε hθ hβle
  have husign' := husign_node hμM hμM₀ hk0 hkn (by omega) (by omega) hℓy₂ hRpos hθ hβ.le hu
    (hNy.trans_eq hN.symm) husign
  have hudefl' : (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β := by
    refine le_trans ?_ hudefl
    have := hμQ hkn
    have := hμM hkn
    gcongr
  have hΩy : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / (θ / (4 * n))))) ≤ Ω := by
    rw [hρ4]
    linarith
  have hg : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false →
      IsEighGoodSample dec (θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)))
        (√(θ / (4 * n) / 2) / y.k)
        (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / (θ / (4 * n)))))) y (s []) := by
    rw [hρ2, hρ4]
    exact hgood
  have hρ1 : θ / (4 * n) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hεy18 : dec y.ε ≤ 1 / 8 := hεy'.trans (hε₁.trans (by norm_num))
  have hfuel' := (hNy.trans_eq hN.symm).trans hfuel
  refine hM.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample hμMk hμQk hcN hu hA hR
    (by omega) (by linarith) hεy18 hR₀pos (by positivity) hρ1 hw hwR hβ hβtol husign' hudefl'
    hfuel' hτ₀ hτy hΩy hg ?_
  intro b y' hy'
  obtain ⟨hA', hR'⟩ := hM.isHermitian_and_specNorm_le_of_eighChild_eq_some hμMk hμQk hcN hu hA
    hR (by omega) (by linarith) hεy18 hR₀pos (by positivity) hρ1 hw hwR hβ hβtol husign'
    hudefl' hfuel' hτ₀ hτy hΩy hg hy'
  exact hchild b y' hy' hA' hR'

/-- The child of the node at the path $a$ is the node at the path $a + [b]$. -/
private lemma eighNodeAt_append_singleton_eq_some {F Su Sg : Type*} [Inhabited Sg]
    {M : FloatMachine F Su Sg} {N signFuel : ℕ} {R₀ β : F} {b : Bool} {y y' : EighNode F} :
    ∀ (a : List Bool) (x : EighNode F) (s : List Bool → EighSample Su Sg N),
      eighNodeAt M N signFuel R₀ β a x s = some y →
      eighChild M N signFuel R₀ β y (s a) b = some y' →
      eighNodeAt M N signFuel R₀ β (a ++ [b]) x s = some y'
  | [], x, s, h, h' => by
    obtain rfl : x = y := Option.some_injective _ h
    simpa [eighNodeAt] using h'
  | b' :: a, x, s, h, h' => by
    simp only [eighNodeAt, Option.bind_eq_some_iff] at h
    obtain ⟨z, hz, hza⟩ := h
    simp only [List.cons_append, eighNodeAt, hz, Option.bind_some]
    exact eighNodeAt_append_singleton_eq_some a z _ hza h'

/-- **Global deterministic guarantee of spectral bisection**: let the machine meet
`NLAlib.FloatMachine.IsAccurate` with $u \ge 0$ and
$\mu_{\mathrm{MM}}$, $\mu_{\mathrm{QR}}$ monotone and nonnegative and $c_{\mathrm N} \ge 0$; let
the stored $\mathbf{A}$ have Hermitian decoding with $\|\mathbf{A}\|_2 \le R_0$, for stored
$R_0 > 0$, $\varepsilon$ and $\beta$ (decoded values) with $0 < \varepsilon \le 2^{-15}$,
$0 < \theta \le 1$, a depth counter $\ell \ge$ `NLAlib.bisectionDepth` $\varepsilon$, and an
accuracy (a precomputed threshold)
$$0 < \beta \le \frac{\varepsilon\sqrt\theta}{2880\,\ell\, n^{3/2}\bigl(2\sqrt n +
\sqrt{2\log(16n/\theta)}\bigr)} \,, \qquad
N_* = N\Bigl(\frac{\theta}{32n(n+1)\ell(\ell+1)}, \frac{\beta}{16n}\Bigr) \,.$$
Suppose $640\,n^{3/2}(8 + \mu_{\mathrm{MM}}(n))(N_* + 1)\cdot16n(n+1)\ell(\ell+1)\,u \le
\theta\beta$, $(4\mu_{\mathrm{QR}}(n) + 4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1)u
\le \beta$, the sign step limit is at least $N_*$, $0 \le \tau$,
$100n^{3/2}\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon\min(R_0, 1))$ and
$16(2R_0 + n + 2\ell + \sqrt{\log(16n/\theta)}) \le \Omega$ (each node has $R_y \le R_0$
and $\ell_y \le 2\ell$). If every internal node $y$ (size at
least $2$, and the machine's test $R_y \le \mathrm{fl}(\varepsilon_y R_0)$ fails) of the tree of
`NLAlib.eighNodeAt` has a good sample (`NLAlib.IsEighGoodSample` with $w_y = \theta
R_y/(2k_y\ell_y(n+1)(\ell+1))$, $x_y = \sqrt{\theta/(8n)}/k_y$, $t_y = \sqrt2(2\sqrt{k_y} +
\sqrt{2\log(16n/\theta)})$), then the decoded output of $\mathsf{eigh}(\mathbf{A}, \varepsilon)$
(`NLAlib.eigh`) is an approximate diagonalization of $\mathbf{A}$ with residual $2\varepsilon R_0$
and singular values within $\varepsilon/3$ of $1$. [Shah2024, Theorem 4.2], deterministic part.
Proof: induct on the fuel with the node-level hypotheses as a predicate over paths (the
children's trees are `eighNodeAt a y' (fun a' => s (b :: a'))` definitionally, so no snoc lemma
is needed); the depth is at most $\ell$
(`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`), so the budget $\ell + 1$ of
`NLAlib.eigh` is never exhausted. Treat leaves directly ($k \le 1$ exact; $R \le \varepsilon_y R_0$
residual $\le \varepsilon_y R_0$; the local lemma's $0 < w$ fails at a leaf with $R_y = 0$). At an
internal node apply
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`, its
matrix hypotheses coming from the parent through
`NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some` (at the root from
`hA`, `hR₀`), and its parameter hypotheses from the depth $j$: $k_y \le n$, $\ell \le \ell_y \le
2\ell$, $\varepsilon_y \ge \varepsilon/3$, $R_y \le R_0$, hence `NLAlib.bisectionSignTol` at $y$ is
at least $\beta$
(`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params`), $w_y/(4R_y) \ge
\theta/(16n(n+1)\ell(\ell+1))$ and $N_y \le N_*$ (`NLAlib.newtonSchulzSteps_le_of_le_abs`,
`NLAlib.newtonSchulzSteps_le_of_le`, monotone $\mu$), all up to the factors $(1 \pm u)^{4j}$ of the
machine-computed parameters: `husign` forces $u \le 10^{-11}\varepsilon$ and `hτ` bounds the floor
absolutely, so the floor error $u\tau$ in each $\varepsilon_j$ is negligible; the node floor
condition ($4k^{3/2}\tau \le \min(\sqrt{\rho/2}, \varepsilon_yR_0)$) and the depth lemmas'
($100\tau \le \varepsilon\min(R_0, 1)$) follow from `hτ` since $\varepsilon_y \ge \varepsilon/3$.
At the root $R = R_0$ gives residual $2\varepsilon R_0$. H, about 200 lines. -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hμM : Monotone μM) (hμQ : Monotone μQ)
    (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian) {R₀ ε β : F}
    {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) +
      √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω)
    {s : List Bool → EighSample ℝ ℂ n}
    (hgood : ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → 2 ≤ y.k →
        M.le y.R (M.mul y.ε R₀) = false →
        IsEighGoodSample dec (θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)))
          (√(θ / (8 * n)) / y.k) (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (16 * n / θ)))) y
          (s a)) :
    IsApproxDiagonalization (decodeMatrix dec A) (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β s).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β s).2 i)) (2 * dec ε * dec R₀) (dec ε / 3) := by
  have hκ₁ : dec ε / 3 ≤ 1 := by linarith [hε₁.trans (show (2⁻¹ : ℝ) ^ 15 ≤ 1 by norm_num)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hM.isApproxDiagonalization_eighAux_succ_of_leaf hA (by positivity) hκ₁
      (Or.inl ⟨Nat.zero_le 1, by positivity⟩)
  obtain ⟨hℓ20, hu₁, hτ', hΩ'⟩ := eigh_global_bounds hu hμM hμM₀ hn hR₀pos hε hε₁ hθ hθ₁ hℓ hβ
    hβle hN husign hτ₀ hτ hΩ
  have hε1 : dec ε ≤ 1 := hε₁.trans (by norm_num)
  have key : ∀ (f : ℕ) (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → ℓ + 1 ≤ f + a.length →
      (decodeMatrix dec y.A).IsHermitian → specNorm (decodeMatrix dec y.A) ≤ dec y.R →
      IsApproxDiagonalization (decodeMatrix dec y.A)
        (decodeMatrix dec (eighAux M n signFuel R₀ β f y.A y.R y.ε y.ℓ fun a' => s (a ++ a')).1)
        (fun i => dec ((eighAux M n signFuel R₀ β f y.A y.R y.ε y.ℓ
          fun a' => s (a ++ a')).2 i))
        (dec y.ε * (dec y.R + dec R₀)) (dec y.ε / 3) := by
    intro f
    induction f with
    | zero =>
      intro a y hy hfa _ _
      have := (hM.eighNodeAt_eq_some_params hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ' hΩ' A s hy).1
      omega
    | succ f ih =>
      intro a y hy hfa hyA hyR
      obtain ⟨hal, hkn, hℓy, hεy, hεy', hRy⟩ :=
        hM.eighNodeAt_eq_some_params hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ' hΩ' A s hy
      have hRy0 : 0 ≤ dec y.R := (specNorm_nonneg _).trans hyR
      have hεy0 : 0 < dec y.ε := by linarith
      by_cases hleaf : y.k ≤ 1 ∨ dec y.R ≤ 0
      · refine hM.isApproxDiagonalization_eighAux_succ_of_leaf hyA (by positivity)
          (by linarith) ?_
        rcases hleaf with hk | hR0
        · exact Or.inl ⟨hk, by positivity⟩
        refine Or.inr ⟨?_, hyR.trans (hR0.trans (by positivity))⟩
        rw [hM.le_iff]
        have hp : 0 < dec y.ε * dec R₀ := by positivity
        have hεR : dec y.ε * dec R₀ ≤ dec R₀ := by
          simpa using mul_le_mul_of_nonneg_right (hεy'.trans hε1) hR₀pos.le
        have hmul := hM.mul y.ε R₀ (by
          rw [abs_of_pos hp]
          linarith [Real.sqrt_nonneg (Real.log (16 * n / θ))])
        have hτR : τ ≤ dec y.ε * dec R₀ := by
          have h1 : dec ε * min (dec R₀) 1 ≤ dec ε * dec R₀ := by gcongr; exact min_le_left _ _
          have h5 := mul_le_mul_of_nonneg_right hεy hR₀pos.le
          have h6 : 0 ≤ dec ε * dec R₀ := by positivity
          linarith
        rw [abs_of_pos hp, max_eq_left hτR] at hmul
        have hu1 : u ≤ 1 := by
          have h4 : (400 : ℝ) ≤ ℓ ^ 2 := by
            have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ20
            nlinarith
          linarith [mul_le_mul_of_nonneg_right h4 hu]
        linarith [(abs_le.mp hmul).2, mul_le_mul_of_nonneg_right hu1 hp.le]
      simp only [not_or, not_le] at hleaf
      refine isApproxDiagonalization_eighAux_succ_of_node hM hu hμM hμQ hμM₀ hμQ₀ hcN hR₀pos hε
        hε₁ hθ hθ₁ hℓ20 hβ hβle hN husign hudefl hfuel hτ₀ hτ hΩ hyA hyR hkn (by omega)
        (by omega) hεy hεy' hRy hleaf.1 hleaf.2 ?_ ?_
      · simp only [List.append_nil]
        exact hgood a y hy
      intro b y' hy' hA' hR'
      simp only [List.append_nil] at hy'
      have h := ih (a ++ [b]) y' (eighNodeAt_append_singleton_eq_some a _ s hy hy')
        (by simp only [List.length_append, List.length_singleton]; omega) hA' hR'
      have hs : (fun a'' => s (a ++ [b] ++ a'')) = fun a'' => s (a ++ b :: a'') := by
        funext a''
        simp
      rw [hs] at h
      exact h
  rw [show 2 * dec ε * dec R₀ = dec ε * (dec R₀ + dec R₀) by ring]
  exact key (ℓ + 1) [] _ rfl (by simp) hA hR₀

end NLAlib
