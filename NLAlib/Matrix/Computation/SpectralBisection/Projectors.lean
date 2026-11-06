/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisection
public import NLAlib.Matrix.Computation.NewtonSchulzSign

/-!
# Spectral projectors and rank recovery at a node of spectral bisection

On Event I (the
ideal shift $c' = (R/\ell)v$ is at distance at least $w$ from every eigenvalue), the stored
spectral projectors of one node of `NLAlib.eighStep` are within $\beta$ of the true ones, and the
rounded rank estimate is the inertia $i_+(\mathbf{A} - c'\mathbf{I})$, so the node splits exactly
when the true projectors are both nontrivial ([Shah2024, proof of Lemma 4.1]). The file also
holds the scalar consequences of the node hypotheses used by the whole analysis
(`NLAlib.mul_le_of_le_bisectionSignTol`) and two facts on roundings.

## Main results

* `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le`: the computed
  projectors.
* `NLAlib.FloatMachine.IsAccurate.min_toNat_eighProjector_eq_inertiaPos`: the rank estimate.
* `NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub`: rank recovery.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- A rounding $z$ of $a$ (`NLAlib.IsRoundingOf` with $u, \tau \ge 0$ and $\lvert a\rvert \le
\Omega$) has $\lvert a - z\rvert \le u(\lvert a\rvert + \tau)$. -/
theorem abs_sub_le_of_isRoundingOf {u τ Ω a z : ℝ} (h : IsRoundingOf u τ Ω a z)
    (ha : |a| ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) : |a - z| ≤ u * (|a| + τ) :=
  (h ha).trans (mul_le_mul_of_nonneg_left (max_le_add_of_nonneg (abs_nonneg a) hτ) hu)

/-- A rounding $z$ of $0 \le a \le \Omega$ (`NLAlib.IsRoundingOf` with $u, \tau \ge 0$) has
$a - u(a + \tau) \le z \le a + u(a + \tau)$. -/
theorem le_and_le_of_isRoundingOf {u τ Ω a z : ℝ} (h : IsRoundingOf u τ Ω a z) (ha0 : 0 ≤ a)
    (ha : a ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) : a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) := by
  have h1 := abs_sub_le_of_isRoundingOf h (by rwa [abs_of_nonneg ha0]) hu hτ
  rw [abs_of_nonneg ha0] at h1
  constructor <;> linarith [(abs_le.mp h1).1, (abs_le.mp h1).2]

/-- The Newton–Schulz step count `NLAlib.newtonSchulzSteps` $s$ $\varepsilon$ is nonnegative for
$0 < s \le 1/2$ and $0 < \varepsilon \le 1/2$. -/
theorem newtonSchulzSteps_nonneg {s ε : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1 / 2) (hε : 0 < ε)
    (hε₁ : ε ≤ 1 / 2) : 0 ≤ newtonSchulzSteps s ε := by
  have h₁ : 0 ≤ Real.logb 2 (min |s| (1 / 2))⁻¹ := by
    rw [abs_of_pos hs, min_eq_left hs₁]
    exact Real.logb_nonneg one_lt_two (one_le_inv₀ hs |>.mpr (by linarith))
  have h₂ : 0 ≤ Real.logb 2 (Real.logb 2 ε⁻¹) := by
    refine Real.logb_nonneg one_lt_two ?_
    rw [← Real.logb_self_eq_one one_lt_two]
    exact Real.logb_le_logb_of_le one_lt_two two_pos ((le_inv_comm₀ two_pos hε).mpr (by linarith))
  unfold newtonSchulzSteps
  linarith

/-- If the machine's leaf test $R \le \mathrm{fl}(e R_0)$ fails, then
$eR_0 - u(eR_0 + \tau) < R$ (for $e, R_0 \ge 0$ and $eR_0 \le \Omega$). -/
theorem FloatMachine.IsAccurate.mul_sub_lt_of_le_eq_false {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    {R e R₀ : F} (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) (he : 0 ≤ dec e) (hR₀ : 0 ≤ dec R₀)
    (hΩ : dec e * dec R₀ ≤ Ω) (hint : M.le R (M.mul e R₀) = false) :
    dec e * dec R₀ - u * (dec e * dec R₀ + τ) < dec R := by
  have hlt : dec (M.mul e R₀) < dec R :=
    not_le.mp fun h => by simp [(hM.le_iff _ _).mpr h] at hint
  linarith [(le_and_le_of_isRoundingOf (hM.mul e R₀) (mul_nonneg he hR₀) hΩ hu hτ₀).1]

/-- The accuracy bound `NLAlib.bisectionSignTol` gives $\beta k^{3/2} \le 1/57600$ and
$\beta\ell \le \varepsilon/360$. -/
private theorem mul_le_of_le_bisectionSignTol_aux {β ε ρ : ℝ} {k ℓ : ℕ} (hk : 1 ≤ k)
    (hℓ : 20 ≤ ℓ) (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8) (hρ₁ : ρ ≤ 1) (hβ : 0 < β)
    (hβtol : β ≤ bisectionSignTol k ε ρ ℓ) :
    β * (k * √(k : ℝ)) ≤ 1 / 57600 ∧ β * ℓ ≤ ε / 360 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hkk : (1 : ℝ) ≤ k * √(k : ℝ) :=
    one_le_mul_of_one_le_of_one_le hk1 (Real.one_le_sqrt.mpr hk1)
  have hℓi : 0 < 1 / (ℓ : ℝ) := by positivity
  have hℓi1 : 1 / (ℓ : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  set η := (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) with hη
  have hη0 : 0 ≤ η := div_nonneg (mul_nonneg (by linarith) hε.le) (by positivity)
  have hηℓ : η * ℓ = (1 - 1 / (ℓ : ℝ)) * ε / 5 := by rw [hη]; field_simp
  have hηℓ' : η * ℓ ≤ ε / 5 := by rw [hηℓ]; nlinarith [mul_pos hℓi hε]
  have hη1 : η ≤ 1 / 800 := by nlinarith [mul_le_mul_of_nonneg_left hℓ' hη0]
  have hD : 72 * (k * √(k : ℝ)) ≤ 36 * k * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ))) := by
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k) (Real.sqrt_nonneg (2 * Real.log (4 / ρ)))]
  have hβD : β * (36 * k * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ)))) ≤ η := by
    have h := hβtol
    rw [bisectionSignTol, ← hη, le_div_iff₀ (by linarith)] at h
    exact h.trans (mul_le_of_le_one_right hη0 (Real.sqrt_le_one.mpr hρ₁))
  have h72 : 72 * β * (k * √(k : ℝ)) ≤ η := by linarith [mul_le_mul_of_nonneg_left hD hβ.le]
  have hβη : 72 * β ≤ η := by linarith [mul_le_mul_of_nonneg_left hkk hβ.le]
  refine ⟨by linarith, ?_⟩
  linarith [mul_le_mul_of_nonneg_right hβη (by linarith : (0 : ℝ) ≤ ℓ)]

/-- The scalar budget of a node: under the accuracy bound $0 < \beta \le$
`NLAlib.bisectionSignTol` $k$ $\varepsilon$ $\rho$ $\ell$ (with $\ell \ge 20$,
$0 < \varepsilon \le 1/8$, $\rho \le 1$), the sign-step roundoff condition
$640k^{3/2}(8 + \mu)(N(w/(8R), \beta/(16k)) + 1)u \le (w/(4R))\beta$ (with $0 < w \le R$,
$\mu, u \ge 0$) and the floor condition $4k^{3/2}\tau \le \min(\sqrt{\rho/2}, X)$ (with
$\tau \ge 0$), the node is nonempty and $k\beta \le 1/57600$, $k^2u \le 10^{-5}$,
$k\tau \le 1/4$, $k^{3/2}uR \le w\beta/20480$, $k^{3/2}u \le \beta/20480$,
$10^6\ell u \le \varepsilon$, $10^5\ell\mu u \le \varepsilon$ and $4\tau \le X$. -/
theorem mul_le_of_le_bisectionSignTol {u τ ρ w R ε β μ X : ℝ} {k ℓ : ℕ} (hℓ : 20 ≤ ℓ)
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ R) (hβ : 0 < β)
    (hβtol : β ≤ bisectionSignTol k ε ρ ℓ) (hμ : 0 ≤ μ) (hu : 0 ≤ u)
    (husign : 640 * k * √(k : ℝ) * (8 + μ) *
      (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) * u ≤ w / (4 * R) * β)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * k * √(k : ℝ)) ≤ min (√(ρ / 2)) X) :
    1 ≤ k ∧ (k : ℝ) * β ≤ 1 / 57600 ∧ (k : ℝ) ^ 2 * u ≤ 1 / 100000 ∧ (k : ℝ) * τ ≤ 1 / 4 ∧
      k * √(k : ℝ) * u * R ≤ w * β / 20480 ∧ k * √(k : ℝ) * u ≤ β / 20480 ∧
      (ℓ : ℝ) * u * 1000000 ≤ ε ∧ (ℓ : ℝ) * (μ * u) * 100000 ≤ ε ∧ 4 * τ ≤ X := by
  have hk : 1 ≤ k := Nat.pos_of_ne_zero fun h => by
    simp only [h, bisectionSignTol, Nat.cast_zero, mul_zero, zero_mul, div_zero] at hβtol
    linarith
  obtain ⟨hβk, hβℓ⟩ := mul_le_of_le_bisectionSignTol_aux hk hℓ hε hε₁ hρ₁ hβ hβtol
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq1 : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hkk : (k : ℝ) ≤ k * √(k : ℝ) := le_mul_of_one_le_right (by linarith) hsq1
  have hR0 : 0 < R := hw.trans_le hwR
  have hℓ0 : (0 : ℝ) ≤ ℓ := by positivity
  have hkk1 : (1 : ℝ) ≤ k * √(k : ℝ) := hk1.trans hkk
  have hβ1 : β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_left hkk1 hβ.le]
  have hNs := newtonSchulzSteps_nonneg (s := w / (8 * R)) (ε := β / (16 * k))
    (by positivity) (by rw [div_le_iff₀ (by positivity)]; linarith) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; linarith)
  have hw4 : w / (4 * R) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hKu : 0 ≤ k * √(k : ℝ) * u := by positivity
  have h0 : 0 ≤ 640 * (8 + μ) * (k * √(k : ℝ) * u) := by positivity
  have hmain : 640 * (8 + μ) * (k * √(k : ℝ) * u) ≤ w / (4 * R) * β :=
    le_trans (by linarith [mul_nonneg h0 hNs]) husign
  have hwβ := mul_le_mul_of_nonneg_right hw4 hβ.le
  have hku : k * √(k : ℝ) * u ≤ β / 20480 := by linarith [mul_nonneg hμ hKu]
  have hμu : μ * u * 2560 ≤ β := by linarith [mul_nonneg (mul_nonneg hμ hu) (by linarith :
    (0 : ℝ) ≤ k * √(k : ℝ) - 1), mul_nonneg hμ hKu]
  have hkuR : k * √(k : ℝ) * u * R ≤ w * β / 20480 := by
    have h := mul_le_mul_of_nonneg_right hmain hR0.le
    rw [show w / (4 * R) * β * R = w * β / 4 by field_simp] at h
    linarith [mul_nonneg (mul_nonneg hμ hKu) hR0.le]
  have hu1 : u ≤ β / 20480 := by linarith [mul_le_mul_of_nonneg_right hkk1 hu]
  have hk2u : (k : ℝ) ^ 2 * u ≤ 1 / 100000 := by
    have e : (k : ℝ) ^ 2 * u = (k * √(k : ℝ) * u) * √(k : ℝ) := by
      rw [pow_two]; nth_rewrite 1 [← Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) k)]; ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_right hku (Real.sqrt_nonneg (k : ℝ))
    have h2 : β * √(k : ℝ) ≤ β * (k * √(k : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hk1) hβ.le
    linarith
  have hsρ : √(ρ / 2) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  refine ⟨hk, by linarith [mul_le_mul_of_nonneg_left hkk hβ.le], hk2u, ?_, hkuR, hku, ?_, ?_, ?_⟩
  · linarith [hτ.trans (min_le_left _ _), mul_le_mul_of_nonneg_right hkk hτ₀]
  · linarith [mul_le_mul_of_nonneg_left hu1 hℓ0]
  · linarith [mul_le_mul_of_nonneg_left (by linarith : μ * u ≤ β / 2560) hℓ0]
  · linarith [hτ.trans (min_le_right _ _), mul_le_mul_of_nonneg_right hkk1 hτ₀]

/-- The stored $\mathrm{fl}(2)$ is within $3u$ of $2$ (for $u \ge 0$, $0 \le \tau \le 1/4$ and
$2 \le \Omega$). -/
private theorem FloatMachine.IsAccurate.abs_dec_ofNat_two_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 4)
    (hΩ : 2 ≤ Ω) : 2 - 3 * u ≤ dec (M.ofNat 2) ∧ dec (M.ofNat 2) ≤ 2 + 3 * u := by
  have h := le_and_le_of_isRoundingOf (hM.ofNat 2) (by norm_num) (by push_cast; linarith) hu hτ₀
  push_cast at h
  have := mul_le_mul_of_nonneg_left hτ1 hu
  constructor <;> linarith [h.1, h.2]

/-- The stored $\mathrm{fl}(Z/\mathrm{fl}(2))$ of a Hermitian $\mathbf{Z}$ within $\delta \le 1$ of
$\mathbf{Y}$, $\|\mathbf{Y}\|_2 \le 2$, is within $\delta/2 + u(2\sqrt k + 4)$ of
$\mathbf{Y}/2$. -/
private theorem FloatMachine.IsAccurate.specNorm_decodeMatrix_hermScale_two_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 1000)
    (hτ₀ : 0 ≤ τ) {k : ℕ} (hk1 : (1 : ℝ) ≤ k) (hkτ : (k : ℝ) * τ ≤ 1 / 4) (hΩ : 4 ≤ Ω)
    {Z : Matrix (Fin k) (Fin k) (F × F)} (hZ : (decodeMatrix dec Z).IsHermitian)
    {Y : Matrix (Fin k) (Fin k) ℂ} (hY : specNorm Y ≤ 2) {δ : ℝ}
    (hδ : specNorm (decodeMatrix dec Z - Y) ≤ δ) (hδ1 : δ ≤ 1) :
    specNorm (decodeMatrix dec (M.hermScale Z (M.ofNat 2)) - (2⁻¹ : ℝ) • Y) ≤
      δ / 2 + u * (2 * √(k : ℝ) + 4) := by
  have hτ1 : τ ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_right hk1 hτ₀]
  obtain ⟨ht1, ht2⟩ := hM.abs_dec_ofNat_two_sub_le hu hτ₀ hτ1 (by linarith)
  have hs := hM.specNorm_sub_decodeMatrix_hermScale_le hu hτ₀ hZ (c := M.ofNat 2)
  set t := dec (M.ofNat 2)
  have ht0 : 0 < t := by linarith
  set Zd := decodeMatrix dec Z
  have hZn : specNorm Zd ≤ 3 := by
    have := specNorm_add_le (Zd - Y) Y
    rw [sub_add_cancel] at this
    linarith
  have hZs : specNorm (t⁻¹ • Zd) ≤ 2 := by
    rw [specNorm_real_smul, abs_of_pos (inv_pos.mpr ht0), inv_mul_le_iff₀ ht0]
    linarith
  have hs' : specNorm (t⁻¹ • Zd - decodeMatrix dec (M.hermScale Z (M.ofNat 2))) ≤
      u * (2 * √(k : ℝ) + 1 / 2) := by
    refine (hs ht0.ne' (by rw [abs_of_pos ht0, div_le_iff₀ ht0]; nlinarith)).trans ?_
    have := mul_le_mul_of_nonneg_left hZs (Real.sqrt_nonneg (k : ℝ))
    nlinarith
  have hinv : |t⁻¹ - 2⁻¹| ≤ u := by
    rw [inv_sub_inv ht0.ne' two_ne_zero, abs_div, abs_of_pos (mul_pos ht0 two_pos),
      div_le_iff₀ (mul_pos ht0 two_pos), abs_le]
    constructor <;> nlinarith
  have hmid : specNorm (t⁻¹ • Zd - (2⁻¹ : ℝ) • Y) ≤ 3 * u + δ / 2 := by
    rw [show t⁻¹ • Zd - (2⁻¹ : ℝ) • Y = (t⁻¹ - 2⁻¹) • Zd + (2⁻¹ : ℝ) • (Zd - Y) by module]
    refine (specNorm_add_le _ _).trans ?_
    rw [specNorm_real_smul, specNorm_real_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    have := mul_le_mul hinv hZn (specNorm_nonneg _) hu
    linarith
  rw [show decodeMatrix dec (M.hermScale Z (M.ofNat 2)) - (2⁻¹ : ℝ) • Y = (t⁻¹ • Zd -
    (2⁻¹ : ℝ) • Y) - (t⁻¹ • Zd - decodeMatrix dec (M.hermScale Z (M.ofNat 2))) by abel]
  exact (specNorm_sub_le _ _).trans (by linarith)

/-- The stored scale $b = \mathrm{fl}(\mathrm{fl}(2)R)$ is within $7uR$ of $2R$ (for
$u \le 1/1000$, $0 \le \tau \le \min(1/4, R/2)$ and $3R + 2 \le \Omega$). -/
private theorem FloatMachine.IsAccurate.dec_mul_ofNat_two_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R : F} (hu : 0 ≤ u) (hu1 : u ≤ 1 / 1000)
    (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 4) (hτR : τ ≤ dec R / 2) (hΩ : 3 * dec R + 2 ≤ Ω) :
    2 * dec R - 7 * u * dec R ≤ dec (M.mul (M.ofNat 2) R) ∧
      dec (M.mul (M.ofNat 2) R) ≤ 2 * dec R + 7 * u * dec R := by
  obtain ⟨ht1, ht2⟩ := hM.abs_dec_ofNat_two_sub_le hu hτ₀ hτ1 (by linarith)
  have hR0 : 0 ≤ dec R := by linarith
  have htR0 : 0 ≤ dec (M.ofNat 2) * dec R := mul_nonneg (by linarith) hR0
  have htR : dec (M.ofNat 2) * dec R ≤ 3 * dec R := mul_le_mul_of_nonneg_right (by linarith) hR0
  obtain ⟨hb1, hb2⟩ := le_and_le_of_isRoundingOf (hM.mul (M.ofNat 2) R) htR0 (by linarith) hu hτ₀
  have e1 := mul_le_mul_of_nonneg_left htR hu
  have e2 := mul_le_mul_of_nonneg_left hτR hu
  have e3 := mul_le_mul_of_nonneg_right ht1 hR0
  have e4 := mul_le_mul_of_nonneg_right ht2 hR0
  have e5 := mul_nonneg hu hR0
  constructor <;> linarith

/-- The stored shift $c = \mathrm{unif}(\mathrm{fl}(R/\mathrm{fl}(\ell)), v)$ of a seed
$v \in [-1, 1]$ is within $2uR$ of the ideal shift $c' = (R/\ell)v$, with $\lvert c\rvert \le
R/10$ and $\lvert c'\rvert \le R/20$ (for $R > 0$, $\ell \ge 20$, $u\ell \le 1/1000$,
$0 \le \tau \le \min(1, R/2)$ and $16(R + \ell) \le \Omega$). -/
private theorem FloatMachine.IsAccurate.abs_dec_unif_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R : F} {ℓ : ℕ} {v : ℝ} (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ1 : τ ≤ 1) (hR0 : 0 < dec R) (hℓ : (20 : ℝ) ≤ ℓ) (huℓ : u * ℓ ≤ 1 / 1000)
    (hτR : τ ≤ dec R / 2) (hΩ : 16 * (dec R + ℓ) ≤ Ω) (hv : v ∈ Set.Icc (-1 : ℝ) 1) :
    |dec (M.unif (M.div R (M.ofNat ℓ)) v) - dec R / ℓ * v| ≤ 2 * u * dec R ∧
      |dec (M.unif (M.div R (M.ofNat ℓ)) v)| ≤ dec R / 10 ∧ |dec R / ℓ * v| ≤ dec R / 20 := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  -- the rounded `ℓ`
  have hLr := (hM.ofNat ℓ) (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; linarith)
  rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) ℓ), max_eq_left (by linarith : τ ≤ (ℓ : ℝ))] at hLr
  have hLr' := abs_le.mp hLr
  have hL1 : 19 ≤ dec (M.ofNat ℓ) := by linarith
  have hL0 : 0 < dec (M.ofNat ℓ) := by linarith
  have hq10 : dec R / dec (M.ofNat ℓ) ≤ dec R / 19 :=
    div_le_div_of_nonneg_left hR0.le (by norm_num) hL1
  have hq0 : 0 ≤ dec R / dec (M.ofNat ℓ) := div_nonneg hR0.le hL0.le
  have hsr := abs_sub_le_of_isRoundingOf (hM.div R (M.ofNat ℓ) hL0.ne')
    (by rw [abs_of_nonneg hq0]; linarith) hu hτ₀
  rw [abs_of_nonneg hq0] at hsr
  set L := dec (M.ofNat ℓ)
  set q := dec R / L with hq
  set s := dec (M.div R (M.ofNat ℓ)) with hs
  clear_value s q L
  have hqd : |q - dec R / ℓ| ≤ u * q := by
    have hqL : q * L = dec R := by rw [hq]; exact div_mul_cancel₀ _ hL0.ne'
    rw [show q - dec R / ℓ = q * (ℓ - L) / ℓ by rw [← hqL]; field_simp, abs_div, abs_mul,
      abs_of_nonneg hq0, abs_of_pos hℓ0, div_le_iff₀ hℓ0]
    nlinarith [mul_le_mul_of_nonneg_left hLr hq0]
  have hsbd : |s - dec R / ℓ| ≤ u * dec R * (7 / 10) := by
    have e1 := abs_sub_le s q (dec R / ℓ)
    rw [abs_sub_comm s q] at e1
    have e2 := mul_le_mul_of_nonneg_left hq10 hu
    have e3 := mul_le_mul_of_nonneg_left hτR hu
    linarith [mul_nonneg hu hR0.le]
  have hRℓ : u * dec R ≤ dec R / ℓ := by
    rw [le_div_iff₀ hℓ0]
    linarith [mul_le_mul_of_nonneg_left huℓ hR0.le]
  have hRℓ2 : dec R / ℓ ≤ dec R / 20 := div_le_div_of_nonneg_left hR0.le (by norm_num) hℓ
  have hsbd' := abs_le.mp hsbd
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ dec R / 10 := by linarith
  obtain ⟨hc1, hc2⟩ := hM.isUnifSampler (M.div R (M.ofNat ℓ)) v (by rw [← hs]; exact hs0) hv
  rw [← hs] at hc1 hc2
  have hv' : |v| ≤ 1 := abs_le.mpr ⟨hv.1, hv.2⟩
  refine ⟨?_, hc1.trans hs1, ?_⟩
  · have e1 := abs_le.mp (hc2.trans (mul_le_mul_of_nonneg_left
      (max_le_add_of_nonneg hs0 hτ₀) hu))
    have e2 : |(s - dec R / ℓ) * v| ≤ |s - dec R / ℓ| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hv'
    have e3 := abs_le.mp (e2.trans hsbd)
    have e4 := mul_le_mul_of_nonneg_left hs1 hu
    have e5 := mul_le_mul_of_nonneg_left hτR hu
    have e6 := mul_nonneg hu hR0.le
    rw [abs_le]
    constructor <;> linarith
  · rw [abs_mul, abs_of_nonneg (div_nonneg hR0.le hℓ0.le)]
    exact (mul_le_of_le_one_right (div_nonneg hR0.le hℓ0.le) hv').trans hRℓ2

/-- If $z$ is in the spectrum of $\mathbf{X} - c\mathbf{I}$, then $z + c$ is in that of
$\mathbf{X}$. -/
private theorem add_mem_spectrum_of_mem_spectrum_sub_smul_one {k : ℕ}
    {X : Matrix (Fin k) (Fin k) ℂ} {c z : ℝ}
    (hz : z ∈ spectrum ℝ (X - c • (1 : Matrix (Fin k) (Fin k) ℂ))) : z + c ∈ spectrum ℝ X := by
  rw [spectrum.mem_iff] at hz ⊢
  rwa [show algebraMap ℝ (Matrix (Fin k) (Fin k) ℂ) (z + c) - X =
    algebraMap ℝ _ z - (X - c • (1 : Matrix (Fin k) (Fin k) ℂ)) by
      simp only [Algebra.algebraMap_eq_smul_one, add_smul]; abel]

/-- The stored shifted matrix $\mathbf{X} = \mathrm{fl}(\mathbf{A} - c\mathbf{I})$ of a node, for a
stored shift $c$ within $2uR$ of $c'$, is Hermitian, within $4uR$ of $\mathbf{A} - c'\mathbf{I}$
and of norm at most $(21/20)R + 4uR$; on Event I its eigenvalues have modulus at least
$w - 4uR$. -/
private theorem FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_eighShift_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k : ℕ} {A : Matrix (Fin k) (Fin k) (F × F)}
    {R c : F} {c' w : ℝ} (hu : 0 ≤ u)
    (hA : (decodeMatrix dec A).IsHermitian) (hR : specNorm (decodeMatrix dec A) ≤ dec R)
    (hτR : τ ≤ dec R / 2) (hΩ : 2 * dec R ≤ Ω) (hcc : |dec c - c'| ≤ 2 * u * dec R)
    (hcR : |dec c| ≤ dec R / 10) (hcpR : |c'| ≤ dec R / 20)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec A), w ≤ |e - c'|) :
    (decodeMatrix dec (M.hermShift A c)).IsHermitian ∧
      specNorm ((decodeMatrix dec A - c' • (1 : Matrix (Fin k) (Fin k) ℂ)) -
        decodeMatrix dec (M.hermShift A c)) ≤ 4 * u * dec R ∧
      specNorm (decodeMatrix dec (M.hermShift A c)) ≤ 21 / 20 * dec R + 4 * u * dec R ∧
      (∀ z ∈ spectrum ℝ (decodeMatrix dec A - c' • (1 : Matrix (Fin k) (Fin k) ℂ)), w ≤ |z|) ∧
      ∀ x ∈ spectrum ℝ (decodeMatrix dec (M.hermShift A c)), w - 4 * u * dec R ≤ |x| := by
  set Ad := decodeMatrix dec A
  set I := (1 : Matrix (Fin k) (Fin k) ℂ)
  have hI1 : specNorm I ≤ 1 := specNorm_one_le
  have hR0 : 0 ≤ dec R := (specNorm_nonneg _).trans hR
  have hsm : ∀ {a b : ℝ}, |a| ≤ b → specNorm (Ad - a • I) ≤ dec R + b := fun h => by
    refine (specNorm_sub_le _ _).trans (add_le_add hR ?_)
    rw [specNorm_real_smul]
    exact (mul_le_mul_of_nonneg_left hI1 (abs_nonneg _)).trans (by linarith)
  have hAc := hsm hcR
  have hsh := (hM.specNorm_sub_decodeMatrix_hermShift_le hu hA c (hAc.trans (by linarith))).trans
    (mul_le_mul_of_nonneg_left (max_le hAc (by linarith)) hu)
  set Xd := decodeMatrix dec (M.hermShift A c)
  have he : specNorm ((Ad - c' • I) - Xd) ≤ 4 * u * dec R := by
    rw [show (Ad - c' • I) - Xd = ((Ad - dec c • I) - Xd) + (dec c - c') • I by
      rw [sub_smul]; abel]
    refine (specNorm_add_le _ _).trans ?_
    rw [specNorm_real_smul]
    nlinarith [mul_le_mul hcc hI1 (specNorm_nonneg _) (by positivity)]
  have hXh : Xd.IsHermitian := hM.isHermitian_decodeMatrix_hermFrom _ _
  have hB : (Ad - c' • I).IsHermitian := hA.sub (isHermitian_real_smul_one c')
  have hspecA : ∀ z ∈ spectrum ℝ (Ad - c' • I), w ≤ |z| := fun z hz => by
    simpa using hI _ (add_mem_spectrum_of_mem_spectrum_sub_smul_one hz)
  refine ⟨hXh, he, ?_, hspecA, fun x hx => ?_⟩
  · have := specNorm_sub_le (Ad - c' • I) ((Ad - c' • I) - Xd)
    rw [sub_sub_cancel] at this
    linarith [hsm hcpR]
  · rw [hXh.spectrum_eq_image_eigenvalue] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have h1 := hspecA _ (hB.eigenvalue_mem_spectrum hj)
    have h2 := hB.abs_eigenvalue_sub_le hXh j
    have := abs_sub_abs_le_abs_sub (eigenvalue (Ad - c' • I) j) (eigenvalue Xd j)
    linarith

/-- The Newton–Schulz sign of the stored shifted matrix of a node is within
$\beta + \beta/2000$ of $\operatorname{sign}(\mathbf{A} - c'\mathbf{I})$ on Event I, when the
leaf test fails. -/
private theorem FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_eighSign_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    (hint : M.le y.R (M.mul y.ε R₀) = false)
    {smp : EighSample ℝ ℂ N} (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    specNorm (cfc Real.sign (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) -
      decodeMatrix dec (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
        (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1)))) ≤
      dec β + dec β / 2000 := by
  obtain ⟨hk, hkβ, -, hkτ, hkuR, hku, hℓu, -, h4τ⟩ :=
    mul_le_of_le_bisectionSignTol hℓ hε hε₁ hρ₁ hw hwR hβ hβtol hμM hu husign hτ₀ hτ
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hkk : (1 : ℝ) ≤ y.k * √(y.k : ℝ) :=
    one_le_mul_of_one_le_of_one_le hk1 (Real.one_le_sqrt.mpr hk1)
  have hR0 : 0 < dec y.R := hw.trans_le hwR
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hℓ
  have hβ1 : dec β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  have huR : u * dec y.R ≤ w * dec β / 20480 := by
    linarith [mul_le_mul_of_nonneg_right hkk (mul_nonneg hu hR0.le)]
  have hu1 : u ≤ 1 / 1000000 := by linarith [mul_le_mul_of_nonneg_right hkk hu]
  have hτ1 : τ ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_right hk1 hτ₀]
  have hsqL := Real.sqrt_nonneg (Real.log (4 / ρ))
  have hε8 := mul_le_mul_of_nonneg_right hε₁ hR₀.le
  have hτR : τ ≤ dec y.R / 2 := by
    have := hM.mul_sub_lt_of_le_eq_false hu hτ₀ hε.le hR₀.le (by linarith) hint
    linarith [mul_le_mul_of_nonneg_right hu1 (mul_pos hε hR₀).le,
      mul_le_mul_of_nonneg_right hu1 hτ₀]
  obtain ⟨hcc, hcR, hcpR⟩ := hM.abs_dec_unif_sub_le (R := y.R) (ℓ := y.ℓ) hu hτ₀ (by linarith)
    hR0 hℓ' (by linarith) hτR (by linarith) hv
  obtain ⟨hb1, hb2⟩ := hM.dec_mul_ofNat_two_le (R := y.R) hu (by linarith) hτ₀ hτ1 hτR
    (by linarith)
  obtain ⟨hXh, he, hXn, hspecA, hspecX⟩ := hM.specNorm_sub_decodeMatrix_hermShift_eighShift_le hu
    hA hR hτR (by linarith) hcc hcR hcpR hI
  set b := dec (M.mul (M.ofNat 2) y.R)
  set Ad := decodeMatrix dec y.A
  set I := (1 : Matrix (Fin y.k) (Fin y.k) ℂ)
  set cp := dec y.R / y.ℓ * smp.1
  set X := M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1)
  set a := w / 2 + 2 * u * w with ha
  have huw : u * w ≤ u * dec y.R := mul_le_mul_of_nonneg_left hwR hu
  have hwβ : w * dec β ≤ w * (1 / 57600) := mul_le_mul_of_nonneg_left hβ1 hw.le
  have huwR : 0 ≤ u * w * dec y.R := by positivity
  have hb0 : 0 < b := by linarith [mul_le_mul_of_nonneg_right hu1 hR0.le]
  have hwb := mul_le_mul_of_nonneg_left hb2 hw.le
  have hN : newtonSchulzSteps (a / (2 * b)) (dec β / (16 * y.k)) ≤
      newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) := by
    refine newtonSchulzSteps_le_of_le_abs (by positivity) ?_
    rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity), ha]
    linarith
  have hab : w / (4 * dec y.R) ≤ a / b := by
    rw [div_le_div_iff₀ (by positivity) hb0, ha]
    linarith
  have hC : 0 ≤ 640 * (y.k : ℝ) * √(y.k : ℝ) * (8 + μM y.k) := by positivity
  have huSN : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (a / (2 * b)) (dec β / (16 * y.k)) + 1) * u ≤ a / b * dec β :=
    calc _ ≤ 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
          (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC) hu
      _ ≤ w / (4 * dec y.R) * dec β := husign
      _ ≤ a / b * dec β := mul_le_mul_of_nonneg_right hab hβ.le
  have hSN := hM.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le hμM hu hτ₀
    (by linarith) (by linarith) hXh (by positivity) (fun x hx => by linarith [hspecX x hx])
    (by linarith [mul_le_mul_of_nonneg_right hu1 hR0.le]) hβ (by linarith) huSN (N := signFuel)
    (hN.trans hfuel)
  have hAcp : (Ad - cp • I).IsHermitian := hA.sub (isHermitian_real_smul_one cp)
  have hmove := hAcp.specNorm_cfc_sign_sub_cfc_sign_le hXh hw hspecA
  have hmove' : 2 * specNorm ((Ad - cp • I) - decodeMatrix dec X) / w ≤ dec β / 2000 := by
    rw [div_le_iff₀ hw]
    linarith
  have := specNorm_add_le (cfc Real.sign (Ad - cp • I) - cfc Real.sign (decodeMatrix dec X))
    (cfc Real.sign (decodeMatrix dec X) - decodeMatrix dec (newtonSchulzSign M β
      (M.mul (M.ofNat 2) y.R) signFuel X))
  rw [sub_add_sub_cancel] at this
  linarith

/-- The sign of a shifted Hermitian matrix has norm at most $1$. -/
private theorem specNorm_cfc_sign_sub_smul_one_le {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (c : ℝ) :
    specNorm (cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) ≤ 1 :=
  (hA.sub (isHermitian_real_smul_one c)).specNorm_cfc_le zero_le_one fun x _ => by
    rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num

/-- **The computed spectral projectors are accurate on Event I**: under the node hypotheses of
`NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub` (without the size
condition), including that the node is not a leaf ($\mathrm{fl}(R) > \mathrm{fl}(\varepsilon R_0)$,
`hint`; without it the window $R$ can lie far below $u\tau$ and the bound fails), for a seed
$v \in [-1, 1]$ whose ideal shift $c' = (R/\ell)v$ is at distance at least $w$ from every
eigenvalue of $\mathbf{A}$, the stored projectors of `NLAlib.eighStep`, $\mathbf{P}_+ =
(\mathbf{B} + \mathbf{I})/2$ and $\mathbf{P}_- = -(\mathbf{B} - \mathbf{I})/2$ with $\mathbf{B}$
the Newton–Schulz sign of the stored shifted matrix, are within $\beta$ of
$\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} - c'\mathbf{I}))$. [Shah2024, proof of
Lemma 4.1], (4.4)–(4.9). -/
theorem FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    (hint : M.le y.R (M.mul y.ε R₀) = false)
    {smp : EighSample ℝ ℂ N} (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    specNorm (decodeMatrix dec (M.hermScale (M.hermShift
        (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
          (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) (M.neg M.one)) (M.ofNat 2)) -
      (2⁻¹ : ℝ) • (1 + cfc Real.sign (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)))) ≤ dec β ∧
    specNorm (decodeMatrix dec (M.hermScale (M.negMat (M.hermShift
        (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
          (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) M.one)) (M.ofNat 2)) -
      (2⁻¹ : ℝ) • (1 - cfc Real.sign (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)))) ≤ dec β := by
  have _ := hρ
  obtain ⟨hk, hkβ, -, hkτ, -, hku3, -, -, -⟩ :=
    mul_le_of_le_bisectionSignTol hℓ hε hε₁ hρ₁ hw hwR hβ hβtol hμM hu husign hτ₀ hτ
  have hSB := hM.specNorm_cfc_sign_sub_decodeMatrix_eighSign_le hμM hu hA hR hℓ hε hε₁ hR₀ hρ₁ hw
    hwR hβ hβtol husign hfuel hτ₀ hτ hΩ hint hv hI
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hksq : √(y.k : ℝ) ≤ y.k * √(y.k : ℝ) := le_mul_of_one_le_left (by positivity) hk1
  have huk : u * √(y.k : ℝ) ≤ dec β / 20480 := by
    linarith [mul_le_mul_of_nonneg_left hksq hu]
  have huβ : u ≤ dec β / 20480 := by
    linarith [mul_le_mul_of_nonneg_left (Real.one_le_sqrt.mpr hk1) hu]
  have hβ1 : dec β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  have hτ1 : τ ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_right hk1 hτ₀]
  have hΩ4 : 4 ≤ Ω := by
    have := Real.sqrt_nonneg (Real.log (4 / ρ))
    have : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hℓ
    linarith [hw.trans_le hwR]
  have hBh := hM.isHermitian_decodeMatrix_newtonSchulzSign β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))
  set B := newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))
  set S := cfc Real.sign (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))
  set Bd := decodeMatrix dec B
  have hS : specNorm S ≤ 1 := specNorm_cfc_sign_sub_smul_one_le hA _
  have hBn : specNorm Bd ≤ 2 := by
    have := specNorm_sub_le S (S - Bd)
    rw [sub_sub_cancel] at this
    linarith
  have hBS : specNorm (Bd - S) ≤ dec β + dec β / 2000 := by rw [specNorm_sub_comm]; exact hSB
  have hI1 : specNorm (1 : Matrix (Fin y.k) (Fin y.k) ℂ) ≤ 1 := specNorm_one_le
  have hfin : (dec β + dec β / 2000 + 3 * u) / 2 + u * (2 * √(y.k : ℝ) + 4) ≤ dec β := by
    linarith
  have hsc : ∀ {Z : Matrix (Fin y.k) (Fin y.k) (F × F)} {Y : Matrix (Fin y.k) (Fin y.k) ℂ},
      (decodeMatrix dec Z).IsHermitian → specNorm Y ≤ 2 →
      specNorm (decodeMatrix dec Z - Y) ≤ dec β + dec β / 2000 + 3 * u →
      specNorm (decodeMatrix dec (M.hermScale Z (M.ofNat 2)) - (2⁻¹ : ℝ) • Y) ≤ dec β :=
    fun hZ hY hZY => (hM.specNorm_decodeMatrix_hermScale_two_sub_le hu (by linarith) hτ₀ hk1 hkτ
      hΩ4 hZ hY hZY (by linarith)).trans hfin
  have hshift : ∀ s : F, |dec s| = 1 → specNorm ((Bd - dec s • 1) -
      decodeMatrix dec (M.hermShift B s)) ≤ 3 * u := fun s hs => by
    have hBs : specNorm (Bd - dec s • 1) ≤ 3 := by
      refine (specNorm_sub_le _ _).trans ?_
      rw [specNorm_real_smul, hs, one_mul]
      linarith
    exact (hM.specNorm_sub_decodeMatrix_hermShift_le hu hBh s (by linarith)).trans
      (by linarith [mul_le_mul_of_nonneg_left (max_le hBs (by linarith : τ ≤ 3)) hu])
  have hW : ∀ s : F, (decodeMatrix dec (M.hermShift B s)).IsHermitian := fun s =>
    hM.isHermitian_decodeMatrix_hermFrom _ _
  constructor
  · have hsh := hshift (M.neg M.one) (by rw [hM.dec_neg, hM.dec_one]; norm_num)
    rw [hM.dec_neg, hM.dec_one, neg_one_smul, sub_neg_eq_add] at hsh
    refine hsc (hW _) ((specNorm_add_le _ _).trans (by linarith)) ?_
    rw [show decodeMatrix dec (M.hermShift B (M.neg M.one)) - (1 + S) =
      (Bd - S) - ((Bd + 1) - decodeMatrix dec (M.hermShift B (M.neg M.one))) by abel]
    exact (specNorm_sub_le _ _).trans (by linarith)
  · have hsh := hshift M.one (by rw [hM.dec_one]; norm_num)
    rw [hM.dec_one, one_smul] at hsh
    refine hsc (by rw [hM.decodeMatrix_negMat]; exact (hW _).neg)
      ((specNorm_sub_le _ _).trans (by linarith)) ?_
    rw [hM.decodeMatrix_negMat, show -decodeMatrix dec (M.hermShift B M.one) - (1 - S) =
      ((Bd - 1) - decodeMatrix dec (M.hermShift B M.one)) - (Bd - S) by abel]
    exact (specNorm_sub_le _ _).trans (by linarith)

/-- The rounded trace $\mathrm{fl}(t + \mathrm{fl}(1/2))$ of a stored $\mathbf{X}$ whose diagonal
sum is within $1/57600$ of $r \le k$ (with $\sum_i \lvert x_{ii}\rvert \le 2k$) has floor $r$. -/
private theorem FloatMachine.IsAccurate.toNat_add_traceRe_div_eq {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) {k : ℕ}
    (hk1 : (1 : ℝ) ≤ k) (hk2u : (k : ℝ) ^ 2 * u ≤ 1 / 100000) (hkτ : (k : ℝ) * τ ≤ 1 / 4)
    (hΩ : 16 * k ≤ Ω) (X : Matrix (Fin k) (Fin k) (F × F)) {r : ℕ} (hrk : (r : ℝ) ≤ k)
    (hdiag : |∑ i, dec (X i i).1 - r| ≤ 1 / 57600) (hsabs : ∑ i, |dec (X i i).1| ≤ 2 * k) :
    M.toNat (M.add (M.traceRe X) (M.div M.one (M.ofNat 2))) = r := by
  have hkk : (k : ℝ) ≤ k ^ 2 := by nlinarith
  have hku : (k : ℝ) * u ≤ 1 / 100000 := by linarith [mul_le_mul_of_nonneg_right hkk hu]
  have hu1 : u ≤ 1 / 100000 := by linarith [mul_le_mul_of_nonneg_right hk1 hu]
  have hτ1 : τ ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_right hk1 hτ₀]
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  -- the rounded trace
  have htrace := abs_le.mp (hM.abs_sum_sub_traceRe_le hu hτ₀ (by linarith) X (by linarith))
  have htr2 := mul_le_mul_of_nonneg_left (by linarith : ∑ i, |dec (X i i).1| + k * τ ≤ 3 * k)
    (by positivity : (0 : ℝ) ≤ 2 * k * u)
  have hdiag' := abs_le.mp hdiag
  -- the rounded half
  obtain ⟨h2a, h2b⟩ := hM.abs_dec_ofNat_two_sub_le hu hτ₀ hτ1 (by linarith)
  have hd2 : 1.9 ≤ dec (M.ofNat 2) := by linarith
  have hd20 : 0 < dec (M.ofNat 2) := by linarith
  have hh2 : 1 / dec (M.ofNat 2) ≤ 1 := by rw [div_le_one hd20]; linarith
  have hh := abs_le.mp (abs_sub_le_of_isRoundingOf (hM.div M.one (M.ofNat 2) hd20.ne')
    (by rw [hM.dec_one, abs_of_pos (div_pos one_pos hd20)]; linarith) hu hτ₀)
  rw [hM.dec_one, abs_of_pos (div_pos one_pos hd20)] at hh
  have hh1 : |1 / dec (M.ofNat 2) - 1 / 2| ≤ u := by
    rw [div_sub_div _ _ hd20.ne' (by norm_num), abs_div, abs_of_pos (mul_pos hd20 two_pos),
      div_le_iff₀ (mul_pos hd20 two_pos), abs_le]
    have := mul_le_mul_of_nonneg_left hd2 hu
    constructor <;> linarith
  have hh1' := abs_le.mp hh1
  have := mul_le_mul_of_nonneg_left hh2 hu
  have hdh : |dec (M.div M.one (M.ofNat 2)) - 1 / 2| ≤ 3 * u := by
    rw [abs_le]; constructor <;> linarith
  have hdh' := abs_le.mp hdh
  -- their rounded sum
  have hzabs : |dec (M.traceRe X) + dec (M.div M.one (M.ofNat 2))| ≤ k + 1 := by
    rw [abs_le]; constructor <;> linarith
  have hz := abs_le.mp (abs_sub_le_of_isRoundingOf (hM.add (M.traceRe X)
    (M.div M.one (M.ofNat 2))) (by linarith) hu hτ₀)
  have hzu := mul_le_mul_of_nonneg_left hzabs hu
  rw [hM.toNat_eq, Nat.floor_eq_iff (by linarith)]
  constructor <;> linarith

/-- **The rounded rank estimate is the inertia on Event I**: let the machine meet
`NLAlib.FloatMachine.IsAccurate` with $u \ge 0$ and
$\mu_{\mathrm{MM}}(k) \ge 0$, and let the node $(k, \mathbf{A}, R, \varepsilon, \ell)$ have
$\mathbf{A}$
Hermitian with $\|\mathbf{A}\|_2 \le R$, $k \ge 2$, $\ell \ge 20$, $0 < \varepsilon \le 1/8$, $R_0 >
0$
and the machine's leaf test $R \le \mathrm{fl}(\varepsilon R_0)$ failing. Let $0 < \rho \le 1$,
$0 < w \le R$, $0 < \beta \le$ `NLAlib.bisectionSignTol` $k\,\varepsilon\,\rho\,\ell$, the sign
precision
$640k^{3/2}(8 + \mu_{\mathrm{MM}}(k))(N_w + 1)u \le (w/(4R))\beta$ with
$N_w =$ `NLAlib.newtonSchulzSteps` $(w/(8R))\,(\beta/(16k))$ at most the step limit, the floor
$0 \le \tau$ with $4k^{3/2}\tau \le \min(\sqrt{\rho/2}, \varepsilon R_0)$ and the range
$16(R_0 + R + k + \ell + \sqrt{\log(4/\rho)}) \le \Omega$. On Event I for a seed $v \in [-1, 1]$
(every eigenvalue $e$ of
$\mathbf{A}$ has $\lvert e - (R/\ell)v\rvert \ge w$), the rank estimate
$k_+ = \min(k, \lfloor\mathrm{fl}(\operatorname{tr}\mathbf{P}_+ + \mathrm{fl}(1/2))\rfloor)$ of
the node's step (`NLAlib.eighStep`) is the inertia $i_+(\mathbf{A} - c'\mathbf{I})$ of the ideal
shift $c' = (R/\ell)v$. [Shah2024, proof of Lemma 4.1], "the estimates $k_\pm$ are the exact
ranks". -/
theorem FloatMachine.IsAccurate.min_toNat_eighProjector_eq_inertiaPos
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false) {smp : EighSample ℝ ℂ N}
    (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    min y.k (M.toNat (M.add (M.traceRe (M.hermScale (M.hermShift
        (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
          (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) (M.neg M.one)) (M.ofNat 2)))
        (M.div M.one (M.ofNat 2)))) =
      inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) := by
  set r := inertiaPos (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) with hr
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast (by omega : 1 ≤ y.k)
  obtain ⟨-, hkβ, hk2u, hkτ, -⟩ :=
    mul_le_of_le_bisectionSignTol hℓ hε hε₁ hρ₁ hw hwR hβ hβtol hμM hu husign hτ₀ hτ
  have hβ1 : dec β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  -- the computed projector is near the ideal one, whose trace is the inertia
  obtain ⟨hP, -⟩ := hM.specNorm_sub_decodeMatrix_eighProjectors_le (N := N)
    (signFuel := signFuel) (R₀ := R₀) hμM hu hA hR hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol
    husign hfuel hτ₀ hτ hΩ hint hv hI
  set Pp := M.hermScale (M.hermShift (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) (M.neg M.one)) (M.ofNat 2)
  set S := cfc Real.sign (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))
  have hPid : specNorm ((2⁻¹ : ℝ) • (1 + S)) ≤ 1 := by
    rw [specNorm_real_smul, abs_of_pos (by norm_num)]
    linarith [(specNorm_add_le 1 S).trans (add_le_add specNorm_one_le
      (specNorm_cfc_sign_sub_smul_one_le hA _))]
  have htr := hA.re_trace_smul_one_add_cfc_sign (c := dec y.R / y.ℓ * smp.1) fun x hx h => by
    have := hI x hx
    rw [h, sub_self, abs_zero] at this
    linarith
  rw [← hr] at htr
  have hentry : ∀ i, |dec (Pp i i).1 - RCLike.re (((2⁻¹ : ℝ) • (1 + S)) i i)| ≤ dec β := by
    intro i
    have h := (RCLike.abs_re_le_norm _).trans
      ((norm_apply_le_specNorm (decodeMatrix dec Pp - (2⁻¹ : ℝ) • (1 + S)) i i).trans hP)
    simpa [decodeMatrix, decodeComplex] using h
  have hentry' : ∀ i, |dec (Pp i i).1| ≤ 1 + dec β := by
    intro i
    have h1 := (RCLike.abs_re_le_norm _).trans
      ((norm_apply_le_specNorm ((2⁻¹ : ℝ) • (1 + S)) i i).trans hPid)
    have h2 := abs_sub_abs_le_abs_sub (dec (Pp i i).1) (RCLike.re (((2⁻¹ : ℝ) • (1 + S)) i i))
    linarith [hentry i]
  have hdiag : |∑ i, dec (Pp i i).1 - r| ≤ y.k * dec β := by
    rw [← htr, Matrix.trace, map_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hentry i
  have hsabs : ∑ i, |dec (Pp i i).1| ≤ y.k * (1 + dec β) := by
    rw [mul_add, mul_one]
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hentry' i
  have hrk : (r : ℝ) ≤ y.k := by
    have : r ≤ y.k := by
      rw [hr, inertiaPos]
      exact (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hk2 := mul_le_mul_of_nonneg_left (by linarith : 1 + dec β ≤ 2) (Nat.cast_nonneg (α := ℝ) y.k)
  rw [hM.toNat_add_traceRe_div_eq hu hτ₀ hk1 hk2u hkτ
    (by linarith [Real.sqrt_nonneg (Real.log (4 / ρ))]) Pp hrk (hdiag.trans (by linarith))
    (hsabs.trans (by linarith))]
  exact min_eq_right (by exact_mod_cast hrk)

/-- **Rank recovery on Event I**: under the node hypotheses of
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`
(contracts, precision, step limit, floor and range), for an internal node ($k \ge 2$, $R >
\varepsilon R_0$) and a seed $v \in [-1, 1]$ whose ideal shift $c' = (R/\ell)v$ is at distance at
least $w$ from every eigenvalue (Event I), the node's step splits exactly when $0 < i_+(\mathbf{A}
- c'\mathbf{I}) < k$; moreover then $k_+ = i_+(\mathbf{A} - c'\mathbf{I})$. [Shah2024, proof of
Lemma 4.1], "the estimates $k_\pm$ are the exact ranks". -/
theorem FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false) {smp : EighSample ℝ ℂ N}
    (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ smp).IsSplit ↔
      0 < inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) ∧
      inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) < y.k := by
  have hkp := hM.min_toNat_eighProjector_eq_inertiaPos (N := N) (signFuel := signFuel)
    (R₀ := R₀) hμM hu hA hR hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol husign hfuel hτ₀ hτ hΩ hk hint
    hv hI
  set r := inertiaPos (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) with hr
  have hrk : r ≤ y.k := by
    rw [hr, inertiaPos]
    exact (Finset.card_filter_le _ _).trans (by simp)
  unfold eighStep
  rw [if_neg (by omega), if_neg (by simp [hint])]
  dsimp only
  clear_value r
  split_ifs with h1 h2
  · rw [hkp] at h1
    exact iff_of_false id (by rw [h1]; exact fun h => h.2.false)
  · rw [hkp] at h2
    exact iff_of_false id (by rw [h2]; exact fun h => h.1.false)
  · rw [hkp] at h1 h2
    exact iff_of_true trivial ⟨Nat.pos_of_ne_zero h2, lt_of_le_of_ne hrk h1⟩

end NLAlib
