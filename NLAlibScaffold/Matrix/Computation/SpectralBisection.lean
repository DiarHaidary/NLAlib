/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisection.Global
public import NLAlibScaffold.Matrix.Computation.Deflation
public import NLAlib.Matrix.Computation.NewtonSchulzSign.Accuracy

/-!
# Spectral bisection with sharper precision budgets (scaffold, stage HDIAG-BOUNDS)

Statements for `NLAlib/Matrix/Computation/SpectralBisection/` (design note
`docs/design/Eigensolvers-HermitianDiagonalization-Bounds.md`, items I2, I3, I7–I10). The node
lemmas of [Shah2024, Lemma 4.1] are restated generically in the parameters $(w, x, t)$ of the good
event (shift distance, smallest singular value and norm thresholds of the Gaussian blocks), with
their precision hypotheses bundled in `NLAlib.FloatMachine.IsEighNodeBudget`: the probabilistic
choice of $(x, t)$ moves to the probability files, and the deflation tolerance becomes the single
condition $2t\beta/x \le \eta$. The global theorem EB5' uses a size-weighted union bound (each
node charged in proportion to its size, item I3), the sharp tolerance at the deepest node (EB2a',
item I2), and the sign theorem SN4' and deflation theorem DF2'.

## Main definitions

* `NLAlib.FloatMachine.IsEighNodeBudget`: the precision hypotheses of one node.

## Main results

* `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget`
  (EB1c'), `NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_isEighNodeBudget` (EB1b'),
  `NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_isEighNodeBudget`
  (EB1d'), `NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_isEighNodeBudget`
  (EB1a'), `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighNodeBudget`
  (EB1').
* `NLAlib.FloatMachine.IsAccurate.mul_le_dec_ε_of_eighNodeAt_eq_some` (EB2a'),
  `NLAlib.sum_k_eighNodeAt_ofFn_le` (EB3').
* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample'` (EB5').
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- `M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y`: the **precision budget of the
node $y$** of spectral bisection for a good event with shift distance $w$, smallest singular value
threshold $x$ and norm threshold $t$: the node's matrix is Hermitian with norm at most its window
$R$, its depth counter is at least $20$, $0 < \varepsilon \le 1/8$, $0 < w \le R$, $0 < x \le 1$,
$t \ge 2\sqrt2\sqrt k$, and, with $\nu = 4\mu_{\mathrm{MM}}(k) + 10 + 10\sqrt k$ and
$N_0 = N(w/(5R), \beta/(16k))$: the deflation tolerance $2t\beta/x \le
(1 - 1/\ell)\varepsilon/(5\ell)$, the sign condition $32\nu u \le (1 - 2^{-7})\,w\beta/(2R)$, the
stopping condition $2048(k + N_0 + 1)\nu u \le \beta$, the deflation rounding condition
$16(4\mu_{\mathrm{QR}}(k) + 4\sqrt k(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(k) + 1)u \le \beta$,
$k\beta \le 1/57600$, at least $N_0$ sign steps, and the floor and range conditions
$4k^{3/2}\tau \le \min(x, \varepsilon R_0)$, $16(R_0 + R + k + \ell + t) \le \Omega$. The
hypotheses of [Shah2024, Lemma 4.1] with the constants of SN4' and DF2'. -/
structure FloatMachine.IsEighNodeBudget {F : Type*} (M : FloatMachine F ℝ ℂ) (dec : F → ℝ)
    (u τ Ω : ℝ) (μM μQ : ℕ → ℝ) (cN : ℝ) (R₀ β : F) (signFuel : ℕ) (w x t : ℝ)
    (y : EighNode F) : Prop where
  /-- The product constant is nonnegative. -/
  nonneg_μM : 0 ≤ μM y.k
  /-- The QR constant is nonnegative. -/
  nonneg_μQ : 0 ≤ μQ y.k
  /-- The sampler constant is nonnegative. -/
  nonneg_cN : 0 ≤ cN
  /-- The unit roundoff is nonnegative. -/
  nonneg_u : 0 ≤ u
  /-- The node's matrix is Hermitian. -/
  isHermitian : (decodeMatrix dec y.A).IsHermitian
  /-- The node's matrix lies in its window. -/
  specNorm_le : specNorm (decodeMatrix dec y.A) ≤ dec y.R
  /-- The depth counter is at least $20$. -/
  twenty_le : 20 ≤ y.ℓ
  /-- The tolerance is positive. -/
  pos_ε : 0 < dec y.ε
  /-- The tolerance is at most $1/8$. -/
  ε_le : dec y.ε ≤ 1 / 8
  /-- The root scale is positive. -/
  pos_R₀ : 0 < dec R₀
  /-- The shift distance is positive. -/
  pos_w : 0 < w
  /-- The shift distance is at most the window. -/
  w_le : w ≤ dec y.R
  /-- The singular value threshold is positive. -/
  pos_x : 0 < x
  /-- The singular value threshold is at most $1$. -/
  x_le : x ≤ 1
  /-- The norm threshold is at least $2\sqrt2\sqrt k$. -/
  le_t : 2 * √2 * √(y.k : ℝ) ≤ t
  /-- The accuracy is positive. -/
  pos_β : 0 < dec β
  /-- The deflation tolerance. -/
  defl_tol : 2 * t / x * dec β ≤ (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)
  /-- The sign condition. -/
  sign_tol : 32 * (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u ≤
    (1 - 2⁻¹ ^ 7) * w / (2 * dec y.R) * dec β
  /-- The stopping condition. -/
  stop_tol : 2048 * (y.k + newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) + 1) *
    (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u ≤ dec β
  /-- The deflation rounding condition. -/
  defl_u : 16 * (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β
  /-- The accuracy is small against the size. -/
  mul_β_le : (y.k : ℝ) * dec β ≤ 1 / 57600
  /-- Enough sign steps. -/
  fuel : newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel
  /-- The floor is nonnegative. -/
  nonneg_τ : 0 ≤ τ
  /-- The floor condition. -/
  τ_le : τ * (4 * y.k * √(y.k : ℝ)) ≤ min x (dec y.ε * dec R₀)
  /-- The range condition. -/
  Ω_le : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + t) ≤ Ω

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
  {N signFuel : ℕ} {R₀ β : F} {w x t : ℝ} {y : EighNode F}

/-- The stored $\mathrm{fl}(2)$ is within $3u$ of $2$ (for $u \ge 0$, $0 \le \tau \le 1/4$ and
$2 \le \Omega$). -/
private theorem FloatMachine.IsAccurate.abs_dec_ofNat_two_sub_le_eb1c {F : Type*}
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
  obtain ⟨ht1, ht2⟩ := hM.abs_dec_ofNat_two_sub_le_eb1c hu hτ₀ hτ1 (by linarith)
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
  obtain ⟨ht1, ht2⟩ := hM.abs_dec_ofNat_two_sub_le_eb1c hu hτ₀ hτ1 (by linarith)
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

/-- The sign of a shifted Hermitian matrix has norm at most $1$. -/
private theorem specNorm_cfc_sign_sub_smul_one_le_eb1c {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (c : ℝ) :
    specNorm (cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) ≤ 1 :=
  (hA.sub (isHermitian_real_smul_one c)).specNorm_cfc_le zero_le_one fun x _ => by
    rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num


/-- The scalar smallness facts of a node budget of positive size: $\beta \le 1/57600$,
$20480u(1 + \sqrt k) \le \beta$, $4k\tau \le 1$, $80\ell\beta \le 1$ and $640uR \le w\beta$. -/
private theorem FloatMachine.IsEighNodeBudget.le_of_one_le
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk : 1 ≤ y.k) :
    dec β ≤ 1 / 57600 ∧ 20480 * u + 20480 * (u * √(y.k : ℝ)) ≤ dec β ∧
      4 * (y.k * τ) ≤ 1 ∧ 80 * (y.ℓ * dec β) ≤ 1 ∧ 640 * (u * dec y.R) ≤ w * dec β := by
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hsq1 : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hu := hB.nonneg_u
  have hβ := hB.pos_β
  have hR0 : 0 < dec y.R := hB.pos_w.trans_le hB.w_le
  set ν := 4 * μM y.k + 10 + 10 * √(y.k : ℝ) with hν
  have hν10 : 10 + 10 * √(y.k : ℝ) ≤ ν := by linarith [hB.nonneg_μM]
  have hνu : 0 ≤ ν * u := mul_nonneg (by linarith) hu
  have hstop : 2048 * (ν * u) ≤ dec β := by
    have h := hB.stop_tol
    have hN : (1 : ℝ) ≤ y.k + newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) + 1 := by
      have hw5 : w / (5 * dec y.R) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith [hB.w_le]
      have hβk : dec β / (16 * y.k) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [hB.mul_β_le]
      linarith [newtonSchulzSteps_nonneg (by have := hB.pos_w; positivity) hw5
        (by positivity) hβk]
    nlinarith [mul_le_mul_of_nonneg_right hN hνu]
  have hsign : 32 * (ν * u) ≤ w / (2 * dec y.R) * dec β := by
    have h := hB.sign_tol
    have : 0 ≤ w / (2 * dec y.R) * dec β := by have := hB.pos_w; positivity
    rw [show (1 - 2⁻¹ ^ 7) * w / (2 * dec y.R) * dec β =
      (1 - 2⁻¹ ^ 7) * (w / (2 * dec y.R) * dec β) by ring] at h
    nlinarith
  have hνu' := mul_le_mul_of_nonneg_right hν10 hu
  have hxk : τ * (4 * y.k * √(y.k : ℝ)) ≤ 1 := hB.τ_le.trans ((min_le_left _ _).trans hB.x_le)
  have hkτ := mul_le_mul_of_nonneg_left hsq1 (mul_nonneg (by positivity : (0 : ℝ) ≤ y.k)
    hB.nonneg_τ)
  refine ⟨by nlinarith [hB.mul_β_le], by nlinarith, by nlinarith, ?_, ?_⟩
  · have hℓ : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
    have ht : 1 ≤ t := by
      have : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
      nlinarith [hB.le_t]
    have h2 : 2 * dec β ≤ 2 * t / x * dec β := by
      gcongr
      rw [le_div_iff₀ hB.pos_x]; nlinarith [hB.x_le]
    have h3 : (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ≤ 1 / (40 * y.ℓ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ 1 / (y.ℓ : ℝ) := by positivity
      nlinarith [hB.ε_le, hB.pos_ε, mul_nonneg this hB.pos_ε.le]
    have h4 := (h2.trans hB.defl_tol).trans h3
    rw [le_div_iff₀ (by positivity)] at h4
    nlinarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hsign
    nlinarith [mul_le_mul_of_nonneg_right hνu' hR0.le,
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg (y.k : ℝ)) hu) hR0.le]

/-- The Newton–Schulz sign of the stored shifted matrix of a node with budget is within
$\beta + \beta/64$ of $\operatorname{sign}(\mathbf{A} - c'\mathbf{I})$ on Event I, when the leaf
test fails. -/
private theorem FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_eighSign_le_of_budget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk : 1 ≤ y.k)
    (hint : M.le y.R (M.mul y.ε R₀) = false)
    {smp : EighSample ℝ ℂ N} (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    specNorm (cfc Real.sign (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) -
      decodeMatrix dec (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
        (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1)))) ≤
      dec β + dec β / 64 := by
  obtain ⟨hβ1, hu20, hkτ, hℓβ, huR⟩ := hB.le_of_one_le hk
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hw := hB.pos_w
  have hβ := hB.pos_β
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hR0 : 0 < dec y.R := hw.trans_le hB.w_le
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
  have hR₀ := hB.pos_R₀
  have hΩ := hB.Ω_le
  have ht0 : 0 ≤ t := le_trans (by positivity) hB.le_t
  have hsk := mul_nonneg hu (Real.sqrt_nonneg (y.k : ℝ))
  have hu1 : u ≤ 1 / 1000000 := by linarith
  have hτ1 : τ ≤ 1 / 4 := by nlinarith
  have hkk : (1 : ℝ) ≤ y.k * √(y.k : ℝ) :=
    one_le_mul_of_one_le_of_one_le hk1 (Real.one_le_sqrt.mpr hk1)
  have h4τ : 4 * τ ≤ dec y.ε * dec R₀ := by
    nlinarith [hB.τ_le.trans (min_le_right _ _), mul_le_mul_of_nonneg_right hkk hτ₀]
  have hε8 := mul_le_mul_of_nonneg_right hB.ε_le hR₀.le
  have hτR : τ ≤ dec y.R / 2 := by
    have := hM.mul_sub_lt_of_le_eq_false hu hτ₀ hB.pos_ε.le hR₀.le (by linarith) hint
    nlinarith [mul_le_mul_of_nonneg_right hu1 (mul_pos hB.pos_ε hR₀).le,
      mul_le_mul_of_nonneg_right hu1 hτ₀]
  obtain ⟨hcc, hcR, hcpR⟩ := hM.abs_dec_unif_sub_le (R := y.R) (ℓ := y.ℓ) hu hτ₀ (by linarith)
    hR0 hℓ' (by nlinarith) hτR (by linarith) hv
  obtain ⟨hb1, hb2⟩ := hM.dec_mul_ofNat_two_le (R := y.R) hu (by linarith) hτ₀ hτ1 hτR
    (by linarith)
  obtain ⟨hXh, he, hXn, hspecA, hspecX⟩ := hM.specNorm_sub_decodeMatrix_hermShift_eighShift_le hu
    hB.isHermitian hB.specNorm_le hτR (by linarith) hcc hcR hcpR hI
  set b := dec (M.mul (M.ofNat 2) y.R)
  set X := M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1)
  set a := w - 4 * u * dec y.R with ha
  have hwβ : w * dec β ≤ w * (1 / 57600) := mul_le_mul_of_nonneg_left hβ1 hw.le
  have huR1 : u * dec y.R ≤ w / 36864000 := by linarith
  have huRR := mul_le_mul_of_nonneg_right huR1 hR0.le
  have huwR := mul_le_mul_of_nonneg_right hu1 (mul_pos hw hR0).le
  have hb0 : 0 < b := by nlinarith [mul_le_mul_of_nonneg_right hu1 hR0.le]
  have hwb := mul_le_mul_of_nonneg_left hb2 hw.le
  have ha0 : 0 < a := by rw [ha]; linarith
  have hab : (1 - 2⁻¹ ^ 7) * w / (2 * dec y.R) ≤ a / b := by
    rw [div_le_div_iff₀ (by positivity) hb0, ha]
    nlinarith
  have hN : newtonSchulzSteps (a / (2 * b)) (dec β / (16 * y.k)) ≤
      newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) := by
    refine newtonSchulzSteps_le_of_le_abs (by positivity) ?_
    rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity), ha]
    linarith [mul_pos hw hR0]
  have hνu : 0 ≤ (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u :=
    mul_nonneg (by linarith [hB.nonneg_μM, Real.sqrt_nonneg (y.k : ℝ)]) hu
  have hstop : 640 * (y.k + newtonSchulzSteps (a / (2 * b)) (dec β / (16 * y.k)) + 1) *
      (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u ≤ dec β := by
    refine le_trans ?_ hB.stop_tol
    have h : 640 * (y.k + newtonSchulzSteps (a / (2 * b)) (dec β / (16 * y.k)) + 1) ≤
        2048 * (y.k + newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) + 1) := by
      have hw5 : w / (5 * dec y.R) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith [hB.w_le]
      have hβk : dec β / (16 * y.k) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith [newtonSchulzSteps_nonneg (by positivity) hw5 (by positivity) hβk]
    have := mul_le_mul_of_nonneg_right h hνu
    linarith
  have hSN := hM.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le_of_mul_le hB.nonneg_μM hu
    hτ₀ (by linarith) (by linarith) hXh ha0 hspecX (b := M.mul (M.ofNat 2) y.R)
    (by linarith [mul_le_mul_of_nonneg_right hu1 hR0.le]) hβ (by linarith)
    (hB.sign_tol.trans (mul_le_mul_of_nonneg_right hab hβ.le)) hstop (N := signFuel)
    (by exact_mod_cast hN.trans hB.fuel)
  have hAcp := hB.isHermitian.sub (isHermitian_real_smul_one (dec y.R / y.ℓ * smp.1))
  have hmove := hAcp.specNorm_cfc_sign_sub_cfc_sign_le hXh hw hspecA
  have hmove' : 2 * specNorm ((decodeMatrix dec y.A - (dec y.R / y.ℓ * smp.1) •
      (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) - decodeMatrix dec X) / w ≤ dec β / 64 := by
    rw [div_le_iff₀ hw]
    linarith
  have := specNorm_add_le (cfc Real.sign (decodeMatrix dec y.A - (dec y.R / y.ℓ * smp.1) •
      (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) - cfc Real.sign (decodeMatrix dec X))
    (cfc Real.sign (decodeMatrix dec X) - decodeMatrix dec (newtonSchulzSign M β
      (M.mul (M.ofNat 2) y.R) signFuel X))
  rw [sub_add_sub_cancel] at this
  linarith

/-- **Computed spectral projectors under a node budget** (EB1'c): at an internal node with
budget `NLAlib.FloatMachine.IsEighNodeBudget` and Event I (seed in $[-1, 1]$, every eigenvalue at
distance at least $w$ from the ideal shift), the stored $\mathbf{P}_\pm$ are within $\beta$ of
$\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} - c'\mathbf{I}))$. [Shah2024, proof of
Lemma 4.1].
Proof: Smallness facts: re-derive the conjuncts of `NLAlib.mul_le_of_le_bisectionSignTol` from the
budget ($k\beta \le 1/57600$ is `mul_β_le`; $k^2u$, $k^{3/2}u \le \beta/20480$ and $u \le
\beta/147456$ from `stop_tol`; $k\tau \le 1/4$ from `τ_le`; $10^6\ell u$, $10^5\ell\mu u \le
\varepsilon$ from `defl_tol` and `stop_tol`); the conjunct $k^{3/2}uR \le w\beta/20480$ is gone
(not derivable) and is replaced by the $\beta/64$ shift budget below. EB1c's proof with SN4'
(`NLAlib.FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le_of_mul_le`)
at modulus $a = w - 4uR \ge (1 - 2^{-8})w$ and scale $b = \mathrm{fl}(2R) \le 2R(1 + 7u)$, so
$a/b \ge (1 - 2^{-7})w/(2R)$ (the field `sign_tol`) and $a/(2b) \ge w/(5R)$ (NS11 for the
step count and `stop_tol`); the shift error $4uR$ moves the sign by at most $8uR/w \le \beta/64$
(`Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le`), the rounded halving by at most
$u(\sqrt k + 2k\tau) \le \beta/64$. M, about 150 lines. -/
theorem FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
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
  rcases Nat.eq_zero_or_pos y.k with hk0 | hk
  · have : IsEmpty (Fin y.k) := by rw [hk0]; infer_instance
    simp only [Subsingleton.elim _ (0 : Matrix (Fin y.k) (Fin y.k) ℂ), specNorm_zero]
    exact ⟨hB.pos_β.le, hB.pos_β.le⟩
  obtain ⟨hβ1, hu20, hkτ, -, -⟩ := hB.le_of_one_le hk
  have hSB := hM.specNorm_cfc_sign_sub_decodeMatrix_eighSign_le_of_budget hB hk hint hv hI
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hβ := hB.pos_β
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hsk := mul_nonneg hu (Real.sqrt_nonneg (y.k : ℝ))
  have hΩ4 : 4 ≤ Ω := by
    have : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
    linarith [hB.Ω_le, hB.pos_R₀, hB.pos_w.trans_le hB.w_le,
      le_trans (by positivity) hB.le_t]
  have hBh := hM.isHermitian_decodeMatrix_newtonSchulzSign β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))
  set B := newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))
  set S := cfc Real.sign (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))
  set Bd := decodeMatrix dec B
  have hS : specNorm S ≤ 1 := specNorm_cfc_sign_sub_smul_one_le_eb1c hB.isHermitian _
  have hBn : specNorm Bd ≤ 2 := by
    have := specNorm_sub_le S (S - Bd)
    rw [sub_sub_cancel] at this
    linarith
  have hBS : specNorm (Bd - S) ≤ dec β + dec β / 64 := by rw [specNorm_sub_comm]; exact hSB
  have hI1 : specNorm (1 : Matrix (Fin y.k) (Fin y.k) ℂ) ≤ 1 := specNorm_one_le
  have hsc : ∀ {Z : Matrix (Fin y.k) (Fin y.k) (F × F)} {Y : Matrix (Fin y.k) (Fin y.k) ℂ},
      (decodeMatrix dec Z).IsHermitian → specNorm Y ≤ 2 →
      specNorm (decodeMatrix dec Z - Y) ≤ dec β + dec β / 64 + 3 * u →
      specNorm (decodeMatrix dec (M.hermScale Z (M.ofNat 2)) - (2⁻¹ : ℝ) • Y) ≤ dec β :=
    fun hZ hY hZY => (hM.specNorm_decodeMatrix_hermScale_two_sub_le hu (by linarith) hτ₀ hk1
      (by linarith) hΩ4 hZ hY hZY (by linarith)).trans (by linarith)
  have hshift : ∀ s : F, |dec s| = 1 → specNorm ((Bd - dec s • 1) -
      decodeMatrix dec (M.hermShift B s)) ≤ 3 * u := fun s hs => by
    have hBs : specNorm (Bd - dec s • 1) ≤ 3 := by
      refine (specNorm_sub_le _ _).trans ?_
      rw [specNorm_real_smul, hs, one_mul]
      linarith
    have hτ3 : τ ≤ 3 := by nlinarith
    exact (hM.specNorm_sub_decodeMatrix_hermShift_le hu hBh s (by linarith)).trans
      (by linarith [mul_le_mul_of_nonneg_left (max_le hBs hτ3) hu])
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

/-- The smallness facts of a node budget used for the rounded trace: $k^2u \le 10^{-5}$,
$k\tau \le 1/4$ and $16k \le \Omega$. -/
private theorem FloatMachine.IsEighNodeBudget.sq_mul_le
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk1 : (1 : ℝ) ≤ y.k) :
    (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 ∧ (y.k : ℝ) * τ ≤ 1 / 4 ∧ 16 * (y.k : ℝ) ≤ Ω := by
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hβ := hB.pos_β
  have hkβ := hB.mul_β_le
  have hβ1 : dec β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  have hsk : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr hk1
  -- smallness of `k u` and `k τ`
  have hku : (y.k : ℝ) * u ≤ dec β / 20480 := by
    have hN : (y.k : ℝ) ≤
        y.k + newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) + 1 := by
      have hR := hB.pos_w.trans_le hB.w_le
      linarith [newtonSchulzSteps_nonneg (s := w / (5 * dec y.R)) (ε := dec β / (16 * y.k))
        (by have := hB.pos_w; positivity)
        (by rw [div_le_iff₀ (by positivity)]; linarith [hB.w_le]) (by positivity)
        (by rw [div_le_iff₀ (by positivity)]; linarith)]
    have hν : (10 : ℝ) ≤ 4 * μM y.k + 10 + 10 * √(y.k : ℝ) := by
      linarith [hB.nonneg_μM, Real.sqrt_nonneg (y.k : ℝ)]
    have := mul_le_mul hN hν (by norm_num) (by linarith)
    have := mul_le_mul_of_nonneg_right this hu
    linarith [hB.stop_tol]
  have hk2u : (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 := by
    have := mul_le_mul_of_nonneg_left hku (by linarith : (0 : ℝ) ≤ y.k)
    nlinarith
  have hkτ : (y.k : ℝ) * τ ≤ 1 / 4 := by
    have h1 := hB.τ_le.trans ((min_le_left _ _).trans hB.x_le)
    have := mul_le_mul_of_nonneg_left hsk (by positivity : (0 : ℝ) ≤ y.k * τ)
    nlinarith
  have hΩ : 16 * (y.k : ℝ) ≤ Ω := by
    have := hB.Ω_le
    have : (0 : ℝ) ≤ y.ℓ := by positivity
    linarith [hB.pos_R₀, hB.pos_w.trans_le hB.w_le, hB.le_t, 
      (by positivity : (0 : ℝ) ≤ 2 * √2 * √(y.k : ℝ))]
  exact ⟨hk2u, hkτ, hΩ⟩

/-- **Rank recovery under a node budget** (EB1b'): at an internal node of size $k \ge 2$ with
budget and Event I, the step splits iff $0 < i_+(\mathbf{A} - c'\mathbf{I}) < k$. [Shah2024,
proof of Lemma 4.1].
Proof: EB1b's proof with EB1c' in place of EB1c: the rounded trace of $\mathbf{P}_+$ is within
$k\beta + 2ku(k + k\tau) < 1/2$ of the inertia (`mul_β_le`, `stop_tol`). M, about 80 lines. -/
theorem FloatMachine.IsAccurate.eighStep_isSplit_iff_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false) {smp : EighSample ℝ ℂ N}
    (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ smp).IsSplit ↔
      0 < inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) ∧
      inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) < y.k := by
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast (by omega : 1 ≤ y.k)
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hβ := hB.pos_β
  have hkβ := hB.mul_β_le
  have hβ1 : dec β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  obtain ⟨hk2u, hkτ, hΩ⟩ := hB.sq_mul_le hk1
  -- the computed projector is near the ideal one, whose trace is the inertia
  obtain ⟨hP, -⟩ := hM.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget hB hint
    (smp := smp) hv hI
  set r := inertiaPos (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) with hr
  set Pp := M.hermScale (M.hermShift (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) (M.neg M.one)) (M.ofNat 2)
  set S := cfc Real.sign (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))
  have hA := hB.isHermitian
  have hPid : specNorm ((2⁻¹ : ℝ) • (1 + S)) ≤ 1 := by
    rw [specNorm_real_smul, abs_of_pos (by norm_num)]
    linarith [(specNorm_add_le 1 S).trans (add_le_add specNorm_one_le
      ((hA.sub (isHermitian_real_smul_one _)).specNorm_cfc_le zero_le_one fun x _ => by
        rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num))]
  have htr := hA.re_trace_smul_one_add_cfc_sign (c := dec y.R / y.ℓ * smp.1) fun x hx h => by
    have := hI x hx
    rw [h, sub_self, abs_zero] at this
    linarith [hB.pos_w]
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
  have hrk : r ≤ y.k := by
    rw [hr, inertiaPos]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hk2 := mul_le_mul_of_nonneg_left (by linarith : 1 + dec β ≤ 2) (Nat.cast_nonneg (α := ℝ) y.k)
  have hkp : min y.k (M.toNat (M.add (M.traceRe Pp) (M.div M.one (M.ofNat 2)))) = r := by
    rw [hM.toNat_add_traceRe_div_eq hu hτ₀ hk1 hk2u hkτ hΩ Pp (by exact_mod_cast hrk)
      (hdiag.trans (by linarith)) (hsabs.trans (by linarith))]
    exact min_eq_right hrk
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

/-- A Hermitian eigenvalue is bounded by the spectral norm. -/
private theorem abs_le_of_mem_spectrum_of_specNorm_le {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) {R x : ℝ} (hR : specNorm X ≤ R) (hx : x ∈ spectrum ℝ X) : |x| ≤ R := by
  rw [hX.spectrum_eq_image_eigenvalue] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact (hX.abs_eigenvalue_le_specNorm j).trans hR

/-- The frame of the positive spectral projector, with a prescribed column count. -/
private theorem exists_frame_pos {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) {R c : ℝ} (hR : specNorm A ≤ R) (hc : ∀ x ∈ spectrum ℝ A, x ≠ c)
    {r : ℕ} (hr : inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) = r) :
    ∃ V : Matrix (Fin k) (Fin r) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) ∧
      spectrum ℝ (Vᴴ * A * V) ⊆ Set.Icc c R := by
  subst hr
  obtain ⟨V, hV, hVV, -, hsp⟩ := hA.exists_hasOrthonormalCols_mul_conjTranspose_eq hc
  refine ⟨V, hV, hVV, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hsp hx
  exact ⟨le_of_lt h2, (le_abs_self x).trans (abs_le_of_mem_spectrum_of_specNorm_le hA hR h1)⟩

/-- The frame of the negative spectral projector, with the complementary column count. -/
private theorem exists_frame_neg {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) {R c : ℝ} (hR : specNorm A ≤ R) (hc : ∀ x ∈ spectrum ℝ A, x ≠ c)
    {m : ℕ} (hm : inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) = m) (hmk : m ≤ k) :
    ∃ V : Matrix (Fin k) (Fin (k - m)) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 - cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) ∧
      spectrum ℝ (Vᴴ * A * V) ⊆ Set.Icc (-R) c := by
  set X := A - c • (1 : Matrix (Fin k) (Fin k) ℂ) with hXdef
  have hX : X.IsHermitian := hA.sub (isHermitian_real_smul_one c)
  have hc' : ∀ x ∈ spectrum ℝ (-A), x ≠ -c := by
    intro x hx hxc
    rw [← spectrum.neg_eq] at hx
    exact hc (-x) (Set.mem_neg.mp hx) (by rw [hxc, neg_neg])
  have heq : -A - (-c) • (1 : Matrix (Fin k) (Fin k) ℂ) = -X := by
    rw [hXdef, neg_smul]; abel
  have hunit : IsUnit X := by
    have hcn : c ∉ spectrum ℝ A := fun h => hc c h rfl
    rw [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one] at hcn
    rw [show X = -(c • (1 : Matrix (Fin k) (Fin k) ℂ) - A) by rw [hXdef]; abel]
    exact hcn.neg
  have hrank : X.rank = k := by rw [Matrix.rank_of_isUnit X hunit, Fintype.card_fin]
  have hrk : inertiaPos (-A - (-c) • (1 : Matrix (Fin k) (Fin k) ℂ)) = k - m := by
    rw [heq, ← inertiaNeg_eq_inertiaPos_neg]
    have := hX.inertiaPos_add_inertiaNeg
    omega
  have key := hA.neg.exists_hasOrthonormalCols_mul_conjTranspose_eq hc'
  rw [hrk] at key
  obtain ⟨V, hV, hVV, -, hsp⟩ := key
  refine ⟨V, hV, ?_, fun x hx => ?_⟩
  · rw [hVV, heq]
    have hs : cfc Real.sign (-X) = -cfc Real.sign X := by
      rw [← cfc_comp_neg Real.sign X ((X.finite_real_spectrum.image _).continuousOn _)
        hX.isSelfAdjoint]
      rw [show (fun x : ℝ => Real.sign (-x)) = fun x => -Real.sign x from
        funext fun x => Real.sign_neg, cfc_neg]
    rw [hs, ← sub_eq_add_neg]
  · have hx' : -x ∈ spectrum ℝ (Vᴴ * -A * V) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, ← spectrum.neg_eq]
      exact Set.neg_mem_neg.mpr hx
    obtain ⟨h1, h2⟩ := hsp hx'
    rw [← spectrum.neg_eq] at h1
    have := abs_le_of_mem_spectrum_of_specNorm_le hA hR (by simpa using h1)
    rw [Set.mem_Ioi] at h2
    exact ⟨(neg_abs_le x).trans' (by linarith), by linarith⟩

/-- A square matrix whose action is bounded below by `x` is a unit with inverse of norm `≤ 1/x`. -/
private lemma isUnit_and_specNorm_inv_le {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ}
    {x : ℝ} (hx : 0 < x)
    (h : ∀ z : Fin r → ℂ, x * ‖WithLp.toLp 2 z‖ ≤ ‖WithLp.toLp 2 (M *ᵥ z)‖) :
    IsUnit M ∧ specNorm M⁻¹ ≤ 1 / x := by
  have hinj : Function.Injective M.mulVec := by
    intro a b hab
    have h0 : x * ‖WithLp.toLp 2 (a - b)‖ ≤ 0 := by
      have := h (a - b)
      rw [Matrix.mulVec_sub, hab, sub_self] at this
      simpa using this
    have hn : ‖WithLp.toLp 2 (a - b)‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (WithLp.toLp 2 (a - b))]) (norm_nonneg _)
    simpa [sub_eq_zero] using hn
  have hU : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  refine ⟨hU, (specNorm_le_iff (by positivity)).2 fun y => ?_⟩
  have h1 := h (M⁻¹ *ᵥ y)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hU),
    Matrix.one_mulVec] at h1
  rw [one_div_mul_eq_div, le_div_iff₀ hx]
  linarith [mul_comm x ‖WithLp.toLp 2 (M⁻¹ *ᵥ y)‖]

/-- The product contract through `decodeMatrix`. -/
private theorem FloatMachine.IsAccurate.specNorm_mul_sub_decodeMatrix_mm_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (F × F))
    (B : Matrix (Fin m) (Fin n) (F × F))
    (h : specNorm (decodeMatrix dec A) * specNorm (decodeMatrix dec B) ≤ Ω) :
    specNorm (decodeMatrix dec A * decodeMatrix dec B - decodeMatrix dec (M.mm A B)) ≤
      μM (max l (max m n)) * u *
        max (specNorm (decodeMatrix dec A) * specNorm (decodeMatrix dec B)) τ :=
  hM.isMatMulErr.specNorm_mul_sub_le A B h

/-- Replacing the frame $\mathbf{Z}$ ($\|\mathbf{Z}\|_2 \le 1$) of a compression by a matrix
within $e$ of it costs at most $Re(2 + e)$, for $\|\mathbf{A}\|_2 \le R$. -/
private theorem specNorm_conjTranspose_mul_mul_sub_le {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m m ℂ} {Z Q : Matrix m n ℂ} {R e : ℝ} (hA : specNorm A ≤ R)
    (hZ : specNorm Z ≤ 1) (he : specNorm (Z - Q) ≤ e) :
    specNorm (Zᴴ * A * Z - Qᴴ * A * Q) ≤ R * (e * (2 + e)) := by
  have hR0 : 0 ≤ R := (specNorm_nonneg _).trans hA
  have he0 : 0 ≤ e := (specNorm_nonneg _).trans he
  have hQ : specNorm Q ≤ 1 + e := by
    rw [show Q = Z - (Z - Q) by abel]; exact (specNorm_sub_le _ _).trans (add_le_add hZ he)
  have hZA : specNorm (Zᴴ * A) ≤ R :=
    (specNorm_mul_le _ _).trans ((mul_le_mul (by rw [specNorm_conjTranspose]; exact hZ) hA
      (specNorm_nonneg _) zero_le_one).trans (one_mul R).le)
  rw [show Zᴴ * A * Z - Qᴴ * A * Q = Zᴴ * A * (Z - Q) + (Z - Q)ᴴ * A * Q by
    rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]; abel]
  refine (specNorm_add_le _ _).trans ?_
  have h1 : specNorm (Zᴴ * A * (Z - Q)) ≤ R * e :=
    (specNorm_mul_le _ _).trans (mul_le_mul hZA he (specNorm_nonneg _) hR0)
  have h2 : specNorm ((Z - Q)ᴴ * A * Q) ≤ R * e * (1 + e) := by
    refine (specNorm_mul_le _ _).trans (mul_le_mul ?_ hQ (specNorm_nonneg _) (mul_nonneg hR0 he0))
    refine (specNorm_mul_le _ _).trans ?_
    rw [specNorm_conjTranspose, mul_comm R]
    exact mul_le_mul he hA (specNorm_nonneg _) he0
  linarith [show R * e + R * e * (1 + e) = R * (e * (2 + e)) by ring]

/-- The two stored products of a compression, against the exact compression by `V W`. -/
private theorem FloatMachine.IsAccurate.specNorm_compress_sub_decodeMatrix_mm_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k r : ℕ} (hk1 : 1 ≤ k) (hrk : r ≤ k) {β e R : ℝ}
    (hu0 : 0 ≤ u) (hμ0 : 0 ≤ μM k) (hμ : μM k * u ≤ β / 2)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 115200) (he0 : 0 ≤ e) (he1 : e ≤ 1 / 500)
    (hR0 : 0 < R) (hτ0 : 0 ≤ τ) (hkτ : 3 * k * τ ≤ R) (hΩ : 4 * R ≤ Ω)
    {As : Matrix (Fin k) (Fin k) (F × F)} (hAR : specNorm (decodeMatrix dec As) ≤ R)
    {Q : Matrix (Fin k) (Fin r) (F × F)} {V : Matrix (Fin k) (Fin r) ℂ}
    {W : Matrix (Fin r) (Fin r) ℂ} (hV : HasOrthonormalCols V) (hW : HasOrthonormalCols W)
    (he : specNorm (V * W - decodeMatrix dec Q) ≤ e) :
    specNorm ((V * W)ᴴ * decodeMatrix dec As * (V * W) -
      decodeMatrix dec (M.mm (M.mm (M.conjTransposeMat Q) As) Q)) ≤
        R * (e * (2 + e)) + 136 / 100 * β * R := by
  set A := decodeMatrix dec As with hAdef
  set Qb := decodeMatrix dec Q with hQbdef
  have heR' : (1 + e) * R ≤ 1002 / 1000 * R := mul_le_mul_of_nonneg_right (by linarith) hR0.le
  have hτR : τ ≤ R / 3 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith [mul_le_mul_of_nonneg_right this hτ0]
  have hβR := mul_le_mul_of_nonneg_right hβ1 hR0.le
  have hβR0 := mul_nonneg hβ0 hR0.le
  have hA0 := specNorm_nonneg A
  have hμu0 : 0 ≤ μM k * u := mul_nonneg hμ0 hu0
  have hQ : specNorm Qb ≤ 1 + e := by
    rw [show Qb = V * W - (V * W - Qb) by abel]
    exact (specNorm_sub_le _ _).trans (by linarith [(hV.mul hW).specNorm_le_one])
  have hQ0 := specNorm_nonneg Qb
  -- the first product
  have hQH : decodeMatrix dec (M.conjTransposeMat Q) = Qbᴴ := hM.decodeMatrix_conjTransposeMat Q
  have hQA : specNorm Qbᴴ * specNorm A ≤ (1 + e) * R := by
    rw [specNorm_conjTranspose]; exact mul_le_mul hQ hAR hA0 (by linarith)
  have hm1 := hM.specNorm_mul_sub_decodeMatrix_mm_le (M.conjTransposeMat Q) As
    (by rw [hQH]; linarith)
  rw [hQH, ← hAdef, show max r (max k k) = k by omega] at hm1
  set C1 := decodeMatrix dec (M.mm (M.conjTransposeMat Q) As) with hC1def
  have hd1 : specNorm (Qbᴴ * A - C1) ≤ β / 2 * (134 / 100 * R) :=
    hm1.trans ((mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hμu0).trans
      (mul_le_mul_of_nonneg_right hμ (by linarith)))
  have hC1 : specNorm C1 ≤ 1003 / 1000 * R := by
    rw [show C1 = Qbᴴ * A - (Qbᴴ * A - C1) by abel]
    refine (specNorm_sub_le _ _).trans ?_
    linarith [(specNorm_mul_le Qbᴴ A).trans hQA]
  -- the second product
  have hC1Q : specNorm C1 * specNorm Qb ≤ 1006 / 1000 * R := by
    have := mul_le_mul hC1 hQ hQ0 (by linarith)
    have h2 : 1003 / 1000 * R * (1 + e) ≤ 1003 / 1000 * R * (1002 / 1000) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hm2 := hM.specNorm_mul_sub_decodeMatrix_mm_le (M.mm (M.conjTransposeMat Q) As) Q
    (by rw [← hC1def]; linarith)
  rw [← hC1def, ← hQbdef, show max r (max k r) = k by omega] at hm2
  set C2 := decodeMatrix dec (M.mm (M.mm (M.conjTransposeMat Q) As) Q)
  have hd2 : specNorm (C1 * Qb - C2) ≤ β / 2 * (134 / 100 * R) :=
    hm2.trans ((mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hμu0).trans
      (mul_le_mul_of_nonneg_right hμ (by linarith)))
  -- the exact compression
  have hHQ := specNorm_conjTranspose_mul_mul_sub_le hAR (hV.mul hW).specNorm_le_one he
  rw [show (V * W)ᴴ * A * (V * W) - C2 = ((V * W)ᴴ * A * (V * W) - Qbᴴ * A * Qb) +
    (Qbᴴ * A - C1) * Qb + (C1 * Qb - C2) by rw [Matrix.sub_mul]; abel]
  have h3 := specNorm_add_le ((V * W)ᴴ * A * (V * W) - Qbᴴ * A * Qb + (Qbᴴ * A - C1) * Qb)
    (C1 * Qb - C2)
  have h4 := specNorm_add_le ((V * W)ᴴ * A * (V * W) - Qbᴴ * A * Qb) ((Qbᴴ * A - C1) * Qb)
  have h1 := (specNorm_mul_le (Qbᴴ * A - C1) Qb).trans (mul_le_mul hd1 hQ hQ0 (by positivity))
  have : β / 2 * (134 / 100 * R) * (1 + e) ≤ β / 2 * (134 / 100 * R) * (1 + 1 / 500) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- The Hermitian average $d^{-1}(\mathbf{C} + \mathbf{C}^{\mathsf{H}})$, for
$\lvert d - 2\rvert \le 3u$ ($u \le 1/1000$), of a $\mathbf{C}$ within $\delta \le R/100$ of a
Hermitian $\mathbf{H}$ with $\|\mathbf{H}\|_2 \le R$, is within $\delta + 3uR/100 + 3uR$ of
$\mathbf{H}$. -/
private theorem specNorm_sub_inv_smul_add_conjTranspose_le {n : Type*} [Fintype n]
    {H C : Matrix n n ℂ} {R δ u d : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 1000) (hHh : Hᴴ = H)
    (hH : specNorm H ≤ R) (hHC : specNorm (H - C) ≤ δ) (hδ : δ ≤ R / 100)
    (hd : |d - 2| ≤ 3 * u) :
    specNorm (H - d⁻¹ • (C + Cᴴ)) ≤ δ + 3 * u * (R / 100) + 3 * u * R := by
  obtain ⟨hda, hdb⟩ := abs_le.mp hd
  have hd1 : 1 ≤ d := by linarith
  have ha : d⁻¹ * d = 1 := inv_mul_cancel₀ (by linarith)
  have ha0 : 0 < d⁻¹ := inv_pos.mpr (by linarith)
  have ha1 : d⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd1
  have h2a : 2 * d⁻¹ ≤ 1 + 3 * u := by
    linarith [mul_le_mul_of_nonneg_left (by linarith : 2 - 3 * u ≤ d) ha0.le,
      mul_le_mul_of_nonneg_right ha1 (by linarith : 0 ≤ 3 * u)]
  have h1a : |1 - 2 * d⁻¹| ≤ 3 * u := by
    rw [show 1 - 2 * d⁻¹ = d⁻¹ * (d - 2) by rw [mul_sub, ha]; ring, abs_mul, abs_of_pos ha0]
    linarith [mul_le_mul_of_nonneg_left hd ha0.le,
      mul_le_mul_of_nonneg_right ha1 (by linarith : 0 ≤ 3 * u)]
  rw [show H - d⁻¹ • (C + Cᴴ) = d⁻¹ • ((H - C) + (H - C)ᴴ) + (1 - 2 * d⁻¹) • H by
    rw [Matrix.conjTranspose_sub, hHh]; module]
  refine (specNorm_add_le _ _).trans ?_
  rw [specNorm_real_smul, specNorm_real_smul, abs_of_pos ha0]
  have hHC0 := specNorm_nonneg (H - C)
  have h1 : specNorm ((H - C) + (H - C)ᴴ) ≤ 2 * specNorm (H - C) := by
    have := specNorm_add_le (H - C) (H - C)ᴴ
    rw [specNorm_conjTranspose] at this; linarith
  have h2 := mul_le_mul_of_nonneg_left h1 ha0.le
  have h3 := mul_le_mul_of_nonneg_right h2a hHC0
  have h4 := mul_le_mul h1a hH (specNorm_nonneg _) (by linarith)
  have h5 := mul_le_mul_of_nonneg_left (hHC.trans hδ) (by linarith : 0 ≤ 3 * u)
  linarith

/-- The stored Hermitian average and shift of a matrix near a Hermitian `H`. -/
private theorem FloatMachine.IsAccurate.specNorm_decodeMatrix_hermShift_hermAvg_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {r : ℕ} {β R δ : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hβ1 : β ≤ 1 / 115200) (hR0 : 0 < R)
    (hτ0 : 0 ≤ τ) (hτR : τ ≤ R / 3) (hrτ : (r : ℝ) * τ ≤ R / 3) (hsr : √(r : ℝ) * u ≤ β / 4)
    (hΩ : 4 * R ≤ Ω) {H : Matrix (Fin r) (Fin r) ℂ} (hHh : Hᴴ = H) (hH : specNorm H ≤ R)
    {X : Matrix (Fin r) (Fin r) (F × F)} (hHC2 : specNorm (H - decodeMatrix dec X) ≤ δ)
    (hδ : δ ≤ R / 100) {two s : F} (htwo : |dec two - 2| ≤ 3 * u) (hs : |dec s| ≤ R) :
    specNorm (decodeMatrix dec (M.hermShift (M.hermAvg X two) s) -
      (H - dec s • (1 : Matrix (Fin r) (Fin r) ℂ))) ≤
        δ + 3 * u * (R / 100) + 3 * u * R + (3 * (β / 4) * (102 / 100 * R) + 2 * (u * R)) +
          u * (21 / 10 * R + R / 3) := by
  have hβR : β * R ≤ R / 115200 := by nlinarith [mul_le_mul_of_nonneg_right hβ1 hR0.le]
  set C2 := decodeMatrix dec X with hC2def
  set d := dec two with hddef
  have hd1 : 1 ≤ d := by linarith [(abs_le.mp htwo).1]
  set Hs := d⁻¹ • (C2 + C2ᴴ) with hHsdef
  have hHHs := specNorm_sub_inv_smul_add_conjTranspose_le hu0 (by linarith) hHh hH hHC2 hδ htwo
  rw [← hHsdef] at hHHs
  have huR : u * R ≤ β * R := mul_le_mul_of_nonneg_right hu1 hR0.le
  have hHs : specNorm Hs ≤ 102 / 100 * R := by
    rw [show Hs = H - (H - Hs) by abel]
    refine (specNorm_sub_le _ _).trans ?_
    linarith
  have hC2 : specNorm C2 ≤ 101 / 100 * R := by
    rw [show C2 = H - (H - C2) by abel]
    exact (specNorm_sub_le _ _).trans (by linarith)
  have hAvg := hM.specNorm_sub_decodeMatrix_hermAvg_le hu0 (by linarith) hτ0 X (c := two)
    (by rw [← hddef, abs_of_pos (by linarith)]; exact hd1) (by rw [← hC2def]; linarith)
  rw [← hC2def, ← hddef, ← hHsdef] at hAvg
  set Y := decodeMatrix dec (M.hermAvg X two) with hYdef
  have hHsY : specNorm (Hs - Y) ≤ 3 * (β / 4) * (102 / 100 * R) + 2 * (u * R) := by
    refine hAvg.trans ?_
    rw [show 3 * u * (√(r : ℝ) * specNorm Hs + 2 * r * τ) =
      3 * (√(r : ℝ) * u) * specNorm Hs + 6 * u * (r * τ) by ring]
    have h1 : 3 * (√(r : ℝ) * u) * specNorm Hs ≤ 3 * (β / 4) * (102 / 100 * R) :=
      mul_le_mul (by linarith) hHs (specNorm_nonneg _) (by linarith)
    linarith [mul_le_mul_of_nonneg_left hrτ (by linarith : 0 ≤ 6 * u)]
  -- the shift
  set I := (1 : Matrix (Fin r) (Fin r) ℂ)
  have hs1 : specNorm (dec s • I) ≤ R := by
    rw [specNorm_real_smul]
    exact (mul_le_mul hs specNorm_one_le (specNorm_nonneg _) hR0.le).trans (mul_one R).le
  have hYs : specNorm (Y - dec s • I) ≤ 21 / 10 * R := by
    rw [show Y - dec s • I = Hs - (Hs - Y) - dec s • I by abel]
    refine (specNorm_sub_le _ _).trans ?_
    linarith [specNorm_sub_le Hs (Hs - Y)]
  have hYh : Y.IsHermitian := hM.isHermitian_decodeMatrix_hermFrom _ _
  have hSh := (hM.specNorm_sub_decodeMatrix_hermShift_le hu0 hYh s (by linarith)).trans
    (mul_le_mul_of_nonneg_left (max_le (c := 21 / 10 * R + R / 3) (by linarith) (by linarith)) hu0)
  rw [← hYdef] at hSh
  rw [show decodeMatrix dec (M.hermShift (M.hermAvg X two) s) - (H - dec s • I) =
    -((H - Hs) + (Hs - Y)) - ((Y - dec s • I) - decodeMatrix dec (M.hermShift (M.hermAvg X two) s))
      by abel]
  refine (specNorm_sub_le _ _).trans ?_
  rw [specNorm_neg]
  linarith [specNorm_add_le (H - Hs) (Hs - Y)]

/-- The stored compression of a deflated basis near `V W`. -/
private theorem FloatMachine.IsAccurate.specNorm_decodeMatrix_compress_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k r : ℕ} (hk1 : 1 ≤ k) (hrk : r ≤ k) {β η R : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ β / 1000) (hμ0 : 0 ≤ μM k) (hμ : μM k * u ≤ β / 2)
    (hsk : √(k : ℝ) * u ≤ β / 4) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 115200) (hβη : β ≤ η / 8)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 800)
    (hR0 : 0 < R) (hτ0 : 0 ≤ τ) (hkτ : 3 * k * τ ≤ R) (hΩ : 4 * R ≤ Ω)
    {As : Matrix (Fin k) (Fin k) (F × F)} (hAh : (decodeMatrix dec As).IsHermitian)
    (hAR : specNorm (decodeMatrix dec As) ≤ R)
    {Q : Matrix (Fin k) (Fin r) (F × F)} {V : Matrix (Fin k) (Fin r) ℂ}
    {W : Matrix (Fin r) (Fin r) ℂ} (hV : HasOrthonormalCols V) (hW : HasOrthonormalCols W)
    (he : specNorm (V * W - decodeMatrix dec Q) ≤ 17 / 20 * η)
    {two s : F} (htwo : |dec two - 2| ≤ 3 * u) (hs : |dec s| ≤ R) :
    specNorm (decodeMatrix dec
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) As) Q) two) s) -
      (Wᴴ * (Vᴴ * decodeMatrix dec As * V) * W - dec s • (1 : Matrix (Fin r) (Fin r) ℂ))) ≤
        (2 + 2 * η) * R * η := by
  have hP1 := hM.specNorm_compress_sub_decodeMatrix_mm_le hk1 hrk hu0 hμ0 hμ hβ0 hβ1
    (by positivity) (by linarith) hR0 hτ0 hkτ hΩ hAR hV hW he
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hrk' : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hsr : √(r : ℝ) * u ≤ β / 4 := by
    linarith [mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hrk') hu0]
  have hHh : ((V * W)ᴴ * decodeMatrix dec As * (V * W))ᴴ =
      (V * W)ᴴ * decodeMatrix dec As * (V * W) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hAh.eq,
      Matrix.mul_assoc]
  have hZ1 : specNorm (V * W) ≤ 1 := (hV.mul hW).specNorm_le_one
  have hH : specNorm ((V * W)ᴴ * decodeMatrix dec As * (V * W)) ≤ R :=
    (specNorm_mul_le _ _).trans ((mul_le_mul ((specNorm_mul_le _ _).trans
      ((mul_le_mul (by rw [specNorm_conjTranspose]; exact hZ1) hAR (specNorm_nonneg _)
        zero_le_one).trans (one_mul R).le)) hZ1 (specNorm_nonneg _) hR0.le).trans (mul_one R).le)
  have h4 : R * η * η ≤ R * η * (1 / 800) := mul_le_mul_of_nonneg_left hη1 (by positivity)
  have h5 : R * η ≤ R * (1 / 800) := mul_le_mul_of_nonneg_left hη1 hR0.le
  have hP2 := hM.specNorm_decodeMatrix_hermShift_hermAvg_sub_le hu0 (by linarith) hβ1 hR0 hτ0
    (by linarith [mul_le_mul_of_nonneg_right hk1' hτ0])
    (by linarith [mul_le_mul_of_nonneg_right hrk' hτ0]) hsr hΩ hHh hH hP1
    (by nlinarith [mul_le_mul_of_nonneg_right hβ1 hR0.le]) htwo hs
  rw [show Wᴴ * (Vᴴ * decodeMatrix dec As * V) * W = (V * W)ᴴ * decodeMatrix dec As * (V * W) by
    rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]]
  refine hP2.trans ?_
  have h3 : β * R ≤ η / 8 * R := mul_le_mul_of_nonneg_right hβη hR0.le
  have h6 : 0 ≤ R * η * η := by positivity
  have huR : u * R ≤ β / 1000 * R := mul_le_mul_of_nonneg_right hu1 hR0.le
  have huR0 : 0 ≤ u * R := mul_nonneg hu0 hR0.le
  nlinarith

/-- A split of `NLAlib.eighStep` happens at an internal node whose leaf test fails. -/
private theorem two_le_and_le_eq_false_of_eighStep_eq_split {F Su Sg : Type*} [Inhabited Sg]
    {M : FloatMachine F Su Sg} {N signFuel : ℕ} {R₀ β : F} {k : ℕ}
    {A : Matrix (Fin k) (Fin k) (F × F)} {R ε : F} {ℓ : ℕ} {smp : EighSample Su Sg N} {kp : ℕ}
    {hkp : kp ≤ k} {Qp : Matrix (Fin k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)} {σ : F}
    (h : eighStep M N signFuel R₀ β A R ε ℓ smp = .split kp hkp Qp Qm Ap Am σ) :
    2 ≤ k ∧ M.le R (M.mul ε R₀) = false := by
  unfold eighStep at h
  by_cases hk : k ≤ 1
  · rw [if_pos hk] at h; cases h
  cases hle : M.le R (M.mul ε R₀)
  · exact ⟨by omega, rfl⟩
  · rw [if_neg hk, if_pos hle] at h; cases h

/-- The stored $\mathrm{fl}(2)$ is within $3u$ of $2$ (for $u \ge 0$, $0 \le \tau \le 1/4$ and
$2 \le \Omega$). -/
private theorem FloatMachine.IsAccurate.abs_dec_ofNat_two_sub_le_eb1d {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 4)
    (hΩ : 2 ≤ Ω) : 2 - 3 * u ≤ dec (M.ofNat 2) ∧ dec (M.ofNat 2) ≤ 2 + 3 * u := by
  have h := le_and_le_of_isRoundingOf (hM.ofNat 2) (by norm_num) (by push_cast; linarith) hu hτ₀
  push_cast at h
  have := mul_le_mul_of_nonneg_left hτ1 hu
  constructor <;> linarith [h.1, h.2]

/-- The sign of a shifted Hermitian matrix has norm at most $1$. -/
private theorem specNorm_cfc_sign_sub_smul_one_le {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (c : ℝ) :
    specNorm (cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) ≤ 1 :=
  (hA.sub (isHermitian_real_smul_one c)).specNorm_cfc_le zero_le_one fun x _ => by
    rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num

/-- The rounded trace $\mathrm{fl}(t + \mathrm{fl}(1/2))$ of a stored $\mathbf{X}$ whose diagonal
sum is within $1/57600$ of $r \le k$ (with $\sum_i \lvert x_{ii}\rvert \le 2k$) has floor $r$. -/
private theorem FloatMachine.IsAccurate.toNat_add_traceRe_div_eq_eb1d {F : Type*}
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
  obtain ⟨h2a, h2b⟩ := hM.abs_dec_ofNat_two_sub_le_eb1d hu hτ₀ hτ1 (by linarith)
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


/-- The rounded rank estimate of a stored projector within $\beta$ of the ideal spectral
projector $\tfrac12(\mathbf{I} + \operatorname{sign}(\mathbf{A} - c\mathbf{I}))$ is the
inertia, for $k\beta \le 1/57600$. -/
private theorem FloatMachine.IsAccurate.min_toNat_eq_inertiaPos_of_specNorm_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) {k : ℕ}
    (hk1 : (1 : ℝ) ≤ k) (hk2u : (k : ℝ) ^ 2 * u ≤ 1 / 100000) (hkτ : (k : ℝ) * τ ≤ 1 / 4)
    (hΩ : 16 * k ≤ Ω) {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian) {c : ℝ}
    (hc : ∀ x ∈ spectrum ℝ A, x ≠ c) {β : ℝ} (hβ0 : 0 ≤ β) (hkβ : k * β ≤ 1 / 57600)
    {Pp : Matrix (Fin k) (Fin k) (F × F)}
    (hP : specNorm (decodeMatrix dec Pp -
      (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)))) ≤ β) :
    min k (M.toNat (M.add (M.traceRe Pp) (M.div M.one (M.ofNat 2)))) =
      inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
  set r := inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) with hr
  have hβ1 : β ≤ 1 / 57600 := by nlinarith
  set S := cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))
  have hPid : specNorm ((2⁻¹ : ℝ) • (1 + S)) ≤ 1 := by
    rw [specNorm_real_smul, abs_of_pos (by norm_num)]
    linarith [(specNorm_add_le 1 S).trans (add_le_add specNorm_one_le
      (specNorm_cfc_sign_sub_smul_one_le hA _))]
  have htr := hA.re_trace_smul_one_add_cfc_sign (c := c) fun x hx h => hc x hx h
  rw [← hr] at htr
  have hentry : ∀ i, |dec (Pp i i).1 - RCLike.re (((2⁻¹ : ℝ) • (1 + S)) i i)| ≤ β := by
    intro i
    have h := (RCLike.abs_re_le_norm _).trans
      ((norm_apply_le_specNorm (decodeMatrix dec Pp - (2⁻¹ : ℝ) • (1 + S)) i i).trans hP)
    simpa [decodeMatrix, decodeComplex] using h
  have hentry' : ∀ i, |dec (Pp i i).1| ≤ 1 + β := by
    intro i
    have h1 := (RCLike.abs_re_le_norm _).trans
      ((norm_apply_le_specNorm ((2⁻¹ : ℝ) • (1 + S)) i i).trans hPid)
    have h2 := abs_sub_abs_le_abs_sub (dec (Pp i i).1) (RCLike.re (((2⁻¹ : ℝ) • (1 + S)) i i))
    linarith [hentry i]
  have hdiag : |∑ i, dec (Pp i i).1 - r| ≤ k * β := by
    rw [← htr, Matrix.trace, map_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hentry i
  have hsabs : ∑ i, |dec (Pp i i).1| ≤ k * (1 + β) := by
    rw [mul_add, mul_one]
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hentry' i
  have hrk : (r : ℝ) ≤ k := by
    have : r ≤ k := by
      rw [hr, inertiaPos]
      exact (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hk2 := mul_le_mul_of_nonneg_left (by linarith : 1 + β ≤ 2) (Nat.cast_nonneg (α := ℝ) k)
  rw [hM.toNat_add_traceRe_div_eq_eb1d hu hτ₀ hk1 hk2u hkτ hΩ Pp hrk (hdiag.trans hkβ)
    (hsabs.trans (by linarith))]
  exact min_eq_right (by exact_mod_cast hrk)

/-- Deflation of a true spectral projector `V Vᴴ` through a stored approximation, on Event II:
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le`
with $\mathbf{S} = \mathbf{I}_r$, for $2t\beta/x \le \eta \le 1/800$. -/
private theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_deflate_le_of_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β t x η : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hr0 : 0 < r) (hr : r ≤ n)
    (hμM : 0 ≤ μM n) (hu₀ : 0 ≤ u)
    {V : Matrix (Fin n) (Fin r) ℂ} (hV : HasOrthonormalCols V) {P : Matrix (Fin n) (Fin n) (F × F)}
    (hP : specNorm (V * Vᴴ - decodeMatrix dec P) ≤ β) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 115200)
    {G : Matrix (Fin n) (Fin n) ℂ} (hGt : specNorm G < t) (hx : 0 < x)
    (hσ : x < singularValues (Vᴴ * G.submatrix id (Fin.castLE hr)) (r - 1))
    (htx : 2 * t / x * β ≤ η) (hη : η ≤ 1 / 800)
    (hu : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β) (hτ0 : 0 ≤ τ)
    (hτ : τ * √(n : ℝ) ≤ x) (hΩ : 16 * t ≤ Ω) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (V * W - decodeMatrix dec (deflate M r P G)) ≤ 17 / 20 * η := by
  set B := Vᴴ * G.submatrix id (Fin.castLE hr)
  obtain ⟨hGu, hinv⟩ := isUnit_and_specNorm_inv_le hx fun z =>
    (mul_le_mul_of_nonneg_right hσ.le (norm_nonneg _)).trans
      (singularValues_last_mul_norm_le B (k := r - 1) (by rw [Fintype.card_fin]; omega) z)
  have hVn : specNorm Vᴴ ≤ 1 := by rw [specNorm_conjTranspose]; exact hV.specNorm_le_one
  have hMG : specNorm B ≤ specNorm G :=
    (specNorm_mul_le _ _).trans ((mul_le_mul hVn (specNorm_submatrix_le G Function.injective_id
      (Fin.castLE_injective hr)) (specNorm_nonneg _) zero_le_one).trans (one_mul _).le)
  have hxG : x ≤ specNorm G := hσ.le.trans ((singularValues_le_specNorm _ _).trans hMG)
  have hn1 : (1 : ℝ) ≤ √(n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ n))
  have : Nonempty (Fin r) := ⟨⟨0, hr0⟩⟩
  have hS1 : specNorm (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := specNorm_one
  have hG0 := specNorm_nonneg G
  have ht0 : 0 < t := lt_of_le_of_lt hG0 hGt
  have hη0 : 0 ≤ η := le_trans (by positivity) htx
  have htxβ : t / x * β ≤ η / 2 := by
    have : 2 * t / x * β = 2 * (t / x * β) := by ring
    linarith
  have hmval : (1 + 2 * β + specNorm (1 : Matrix (Fin r) (Fin r) ℂ) / 8) *
      specNorm (1 : Matrix (Fin r) (Fin r) ℂ)⁻¹ * specNorm G * specNorm B⁻¹ ≤
        (9 / 8 + 2 * β) * (t / x) := by
    rw [inv_one, hS1, mul_one]
    calc (1 + 2 * β + 1 / 8) * specNorm G * specNorm B⁻¹ ≤ (1 + 2 * β + 1 / 8) * t * (1 / x) := by
          gcongr
      _ = (9 / 8 + 2 * β) * (t / x) := by ring
  have hmβ : (9 / 8 + 2 * β) * (t / x) * β ≤ (9 / 8 + 2 * β) * (η / 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left htxβ (by linarith)
  have hmβ' := (mul_le_mul_of_nonneg_right hmval hβ0).trans hmβ
  have hu' : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β := hu
  obtain ⟨W, hW, hWb⟩ := hM.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le hμM
    hu₀ hr hV hV isUnit_one (by rw [Matrix.mul_one]) hP hGu rfl (hmβ'.trans (by nlinarith)) hu'
    (by rw [hS1, one_mul]; nlinarith) (hτ.trans hxG) (by rw [hS1]; nlinarith) (by linarith)
  refine ⟨W, hW, hWb.trans ?_⟩
  change 3 / 2 * ((1 + 2 * β + specNorm (1 : Matrix (Fin r) (Fin r) ℂ) / 8) *
    specNorm (1 : Matrix (Fin r) (Fin r) ℂ)⁻¹ * specNorm G * specNorm B⁻¹) * β ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hβ1 hη0]

/-- One side of a split under a node budget: the frame `V` of a true spectral projector, through
the deflation of the stored projector (Event II) and the compression of the node's matrix. -/
private theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_deflate_compress_le_of_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k r : ℕ} (hk1 : 1 ≤ k) (hr0 : 0 < r) (hrk : r ≤ k)
    {β η R t x : ℝ} (hμM : 0 ≤ μM k) (hu : 0 ≤ u) (huβ : u ≤ β / 1000) (hμ : μM k * u ≤ β / 2)
    (hsk : √(k : ℝ) * u ≤ β / 4) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 115200) (hβη : β ≤ η / 8)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 800) (hR0 : 0 < R) (hτ₀ : 0 ≤ τ) (hkτ : 3 * k * τ ≤ R)
    (hΩ : 4 * R ≤ Ω) (hx : 0 < x) (htx : 2 * t / x * β ≤ η)
    (hdefl : 16 * (4 * μQ k + 4 * √(k : ℝ) * cN + 2 * μM k) * u ≤ β) (hτx : τ * √(k : ℝ) ≤ x)
    (hΩt : 16 * t ≤ Ω) {As : Matrix (Fin k) (Fin k) (F × F)}
    (hAh : (decodeMatrix dec As).IsHermitian) (hAR : specNorm (decodeMatrix dec As) ≤ R)
    {two : F} (htwo : |dec two - 2| ≤ 3 * u) {V : Matrix (Fin k) (Fin r) ℂ}
    (hV : HasOrthonormalCols V) {P : Matrix (Fin k) (Fin k) (F × F)}
    (hP : specNorm (V * Vᴴ - decodeMatrix dec P) ≤ β) {G : Matrix (Fin k) (Fin k) ℂ}
    (hGt : specNorm G < t)
    (hσ : x < singularValues (Vᴴ * G.submatrix id (Fin.castLE hrk)) (r - 1))
    {s : F} (hs : |dec s| ≤ R) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (V * W - decodeMatrix dec (deflate M r P G)) ≤ η ∧
      specNorm (decodeMatrix dec (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat
        (deflate M r P G)) As) (deflate M r P G)) two) s) -
        (Wᴴ * (Vᴴ * decodeMatrix dec As * V) * W - dec s • (1 : Matrix (Fin r) (Fin r) ℂ))) ≤
          (2 + 2 * η) * R * η := by
  obtain ⟨W, hW, hWb⟩ := hM.exists_hasOrthonormalCols_specNorm_sub_deflate_le_of_mul_le hr0 hrk
    hμM hu hV hP hβ0 hβ1 hGt hx hσ htx hη1 hdefl hτ₀ hτx hΩt
  exact ⟨W, hW, hWb.trans (by linarith), hM.specNorm_decodeMatrix_compress_sub_le hk1 hrk hu huβ
    hμM hμ hsk hβ0 hβ1 hβη hη0 hη1 hR0 hτ₀ hkτ hΩ hAh hAR hV hW hWb htwo hs⟩

/-- The roundoff budget of a node from the stopping condition of
`NLAlib.FloatMachine.IsEighNodeBudget`. -/
private theorem FloatMachine.IsEighNodeBudget.le_of_stop_tol
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk2 : 2 ≤ y.k) :
    u ≤ dec β / 1000 ∧ μM y.k * u ≤ dec β / 2 ∧ √(y.k : ℝ) * u ≤ dec β / 4 ∧
      dec β ≤ 1 / 115200 ∧ (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 := by
  have hk2' : (2 : ℝ) ≤ y.k := by exact_mod_cast hk2
  have hsqk : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hsk2 : √(y.k : ℝ) * √(y.k : ℝ) = y.k := Real.mul_self_sqrt (by linarith)
  have hsqk' : √(y.k : ℝ) ≤ y.k := by nlinarith
  have hR0 : 0 < dec y.R := hB.pos_w.trans_le hB.w_le
  have hu := hB.nonneg_u
  have hμM := hB.nonneg_μM
  have hβ := hB.pos_β
  -- the stopping condition
  set ν := 4 * μM y.k + 10 + 10 * √(y.k : ℝ) with hν
  have hνu : 0 ≤ ν * u := mul_nonneg (by positivity) hu
  have hkβ := hB.mul_β_le
  have hβ1 : dec β ≤ 1 / 115200 := by nlinarith
  have hN := newtonSchulzSteps_nonneg (s := w / (5 * dec y.R)) (ε := dec β / (16 * y.k))
    (div_pos hB.pos_w (by positivity))
    (by rw [div_le_iff₀ (by positivity)]; linarith [hB.w_le]) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; linarith)
  have hstop : 2048 * (y.k + newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) + 1) *
      ν * u ≤ dec β := hB.stop_tol
  have hX : (y.k + 1) * (ν * u) ≤
      (y.k + newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) + 1) * (ν * u) :=
    mul_le_mul_of_nonneg_right (by linarith) hνu
  have hkνu : 2048 * (y.k * (ν * u)) ≤ dec β := by linarith
  have hνu3 : 2048 * 3 * (ν * u) ≤ dec β := by
    linarith [mul_le_mul_of_nonneg_right (by linarith : (3 : ℝ) ≤ y.k + 1) hνu]
  have hνe : ν * u = 4 * (μM y.k * u) + 10 * u + 10 * (√(y.k : ℝ) * u) := by rw [hν]; ring
  have hμu := mul_nonneg hμM hu
  have hsu := mul_le_mul_of_nonneg_right hsqk hu
  have hu1β : u ≤ dec β / 1000 := by linarith
  have hμ : μM y.k * u ≤ dec β / 2 := by linarith
  have hsk : √(y.k : ℝ) * u ≤ dec β / 4 := by linarith
  have hkνe : y.k * (ν * u) = 4 * (y.k * (μM y.k * u)) + 10 * (y.k * u) +
      10 * (y.k * √(y.k : ℝ) * u) := by rw [hν]; ring
  have hk3u : y.k * √(y.k : ℝ) * u ≤ dec β / 20480 := by
    have : 0 ≤ (y.k : ℝ) * (μM y.k * u) := by positivity
    have : 0 ≤ (y.k : ℝ) * u := by positivity
    linarith
  have hk2u : (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 := by
    have h1 : (y.k : ℝ) ^ 2 * u = √(y.k : ℝ) * (y.k * √(y.k : ℝ) * u) := by
      rw [show √(y.k : ℝ) * (y.k * √(y.k : ℝ) * u) = y.k * (√(y.k : ℝ) * √(y.k : ℝ)) * u by ring,
        hsk2]
      ring
    have h2 := mul_le_mul_of_nonneg_right hsqk' (by positivity : 0 ≤ y.k * √(y.k : ℝ) * u)
    have h3 := mul_le_mul_of_nonneg_left hk3u (by positivity : (0 : ℝ) ≤ y.k)
    linarith
  exact ⟨hu1β, hμ, hsk, hβ1, hk2u⟩

/-- The scalar budget of a split node under `NLAlib.FloatMachine.IsEighNodeBudget`. -/
private theorem FloatMachine.IsEighNodeBudget.split_numerics
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk2 : 2 ≤ y.k)
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hint : M.le y.R (M.mul y.ε R₀) = false) :
    u ≤ 1 / 1000 ∧ τ ≤ 1 / 8 ∧ 6 * τ ≤ dec y.R ∧ 3 * y.k * τ ≤ dec y.R ∧ 2 ≤ Ω ∧
      4 * dec y.R ≤ Ω ∧ μM y.k * u ≤ dec β / 2 ∧ √(y.k : ℝ) * u ≤ dec β / 4 ∧
      u ≤ dec β / 1000 ∧ dec β ≤ 1 / 115200 ∧
      dec β ≤ (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) / 8 ∧
      0 < (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ∧
      (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ≤ 1 / 800 ∧
      (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 ∧ (y.k : ℝ) * τ ≤ 1 / 4 ∧ 16 * (y.k : ℝ) ≤ Ω ∧
      τ * √(y.k : ℝ) ≤ x ∧
      16 * (4 * μQ y.k + 4 * √(y.k : ℝ) * cN + 2 * μM y.k) * u ≤ dec β ∧ 16 * t ≤ Ω := by
  have hk2' : (2 : ℝ) ≤ y.k := by exact_mod_cast hk2
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
  have hsqk : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hR0 : 0 < dec y.R := hB.pos_w.trans_le hB.w_le
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hβ := hB.pos_β
  obtain ⟨hu1β, hμ, hsk, hβ1, hk2u⟩ := hB.le_of_stop_tol hk2
  -- the norm threshold
  have ht4 : 4 ≤ t := by
    have h2 : √2 * √(y.k : ℝ) = √(2 * y.k) := (Real.sqrt_mul (by norm_num) _).symm
    have h4 : (2 : ℝ) ≤ √(2 * y.k) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
    have := hB.le_t
    rw [mul_assoc, h2] at this
    linarith
  have hΩ := hB.Ω_le
  have hR₀ := hB.pos_R₀
  have hRlt := hM.mul_sub_lt_of_le_eq_false hu hτ₀ hB.pos_ε.le hR₀.le
    (by linarith [mul_le_mul_of_nonneg_right hB.ε_le hR₀.le]) hint
  -- the floor and the range
  have hτ := hB.τ_le
  have hτx : τ * (4 * y.k * √(y.k : ℝ)) ≤ x := hτ.trans (min_le_left _ _)
  have hτε : τ * (4 * y.k * √(y.k : ℝ)) ≤ dec y.ε * dec R₀ := hτ.trans (min_le_right _ _)
  have hkτ4 : 4 * y.k * τ ≤ τ * (4 * y.k * √(y.k : ℝ)) := by
    linarith [mul_le_mul_of_nonneg_left hsqk (by positivity : (0 : ℝ) ≤ 4 * y.k * τ)]
  have hτk : τ * √(y.k : ℝ) ≤ τ * (4 * y.k * √(y.k : ℝ)) := by
    linarith [mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 4 * y.k)
      (mul_nonneg hτ₀ (Real.sqrt_nonneg (y.k : ℝ)))]
  have hx1 := hB.x_le
  have hkτ : (y.k : ℝ) * τ ≤ 1 / 4 := by linarith
  have h2τ := mul_le_mul_of_nonneg_right hk2' hτ₀
  have hτ1 : τ ≤ 1 / 8 := by linarith
  have hu1 : u ≤ 1 / 1000 := by linarith
  have hkτR : 3 * y.k * τ ≤ dec y.R := by
    linarith [mul_le_mul_of_nonneg_left (hkτ4.trans hτε) (by linarith : (0 : ℝ) ≤ 1 - u),
      mul_le_mul_of_nonneg_right hu1 hτ₀,
      mul_le_mul_of_nonneg_right hu1 (by positivity : (0 : ℝ) ≤ y.k * τ)]
  -- the tolerance
  have hε := hB.pos_ε
  have hε₁ := hB.ε_le
  set η := (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) with hηdef
  have hℓinv : 1 / (y.ℓ : ℝ) ≤ 1 / 20 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hℓinv0 : 0 < 1 / (y.ℓ : ℝ) := by positivity
  have hη0 : 0 < η := div_pos (mul_pos (by linarith) hε) (by linarith)
  have hη1 : η ≤ 1 / 800 := by
    rw [hηdef, div_le_iff₀ (by linarith)]
    linarith [mul_nonneg hℓinv0.le hε.le]
  have hx := hB.pos_x
  have htx : t ≤ t / x := by
    rw [le_div_iff₀ hx]; exact mul_le_of_le_one_right (by linarith) hx1
  have hβη : dec β ≤ η / 8 := by
    have h := hB.defl_tol
    have : 2 * 4 * dec β ≤ 2 * t / x * dec β := by
      rw [mul_div_assoc]; gcongr; linarith
    linarith
  have hdefl := hB.defl_u
  have hcN := hB.nonneg_cN
  refine ⟨hu1, hτ1, by linarith, hkτR, by linarith, by linarith, hμ, hsk, hu1β, hβ1, hβη, hη0,
    hη1, hk2u, hkτ, by linarith, by linarith, ?_, by linarith⟩
  linarith [mul_nonneg (Real.sqrt_nonneg (y.k : ℝ)) hu]

/-- **A split node under a node budget** (EB1d'): with budget and a good sample
(`NLAlib.IsEighGoodSample` with parameters $(w, x, t)$), a split gives frames $\mathbf{V}_\pm$,
unitaries $\mathbf{W}_\pm$ with $\|\mathbf{V}_\pm\mathbf{W}_\pm - \mathbf{Q}_\pm\|_2 \le \eta =
(1 - 1/\ell)\varepsilon/(5\ell)$ and children within $(2 + 2\eta)R\eta$ of the shifted
compressions, as EB1d. [Shah2024, proof of Lemma 4.1].
Proof: EB1d's proof with EB1c', EB1b' and DF2'
(`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le`)
for $\mathbf{A} = \mathbf{V}\mathbf{V}^{\mathsf H}$, $\mathbf{S} = \mathbf{I}$: on Event II
$\|\mathbf{G}\|_2 < t$ and $\sigma_{\min}(\mathbf{V}^{\mathsf H}\mathbf{G}_1) > x$, so
$m \le (1 + 2\beta + 1/8)t/x$ and $\tfrac32 m\beta \le 2t\beta/x \le \eta$ (`defl_tol`). L, about
250 lines (EB1d's assembly reused). -/
theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    {smp : EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w x t y smp)
    {kp : ℕ} {hkp : kp ≤ y.k} {Qp : Matrix (Fin y.k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin y.k) (Fin (y.k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) (F × F)} {σ : F}
    (hsplit : eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ smp = .split kp hkp Qp Qm Ap Am σ) :
    |dec σ - dec y.R / 2| ≤ 3 * u * (dec y.R / 2) ∧
    (∃ V : Matrix (Fin y.k) (Fin kp) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (decodeMatrix dec y.A -
          (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))) ∧
      spectrum ℝ (Vᴴ * decodeMatrix dec y.A * V) ⊆ Set.Icc (dec y.R / y.ℓ * smp.1) (dec y.R) ∧
      ∃ W : Matrix (Fin kp) (Fin kp) ℂ, HasOrthonormalCols W ∧
        specNorm (V * W - decodeMatrix dec Qp) ≤ ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)) ∧
        specNorm (decodeMatrix dec Ap - (Wᴴ * (Vᴴ * decodeMatrix dec y.A * V) * W -
          dec σ • (1 : Matrix (Fin kp) (Fin kp) ℂ))) ≤
            (2 + 2 * ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) * dec y.R *
              ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) ∧
    (∃ V : Matrix (Fin y.k) (Fin (y.k - kp)) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 - cfc Real.sign (decodeMatrix dec y.A -
          (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))) ∧
      spectrum ℝ (Vᴴ * decodeMatrix dec y.A * V) ⊆ Set.Icc (-dec y.R) (dec y.R / y.ℓ * smp.1) ∧
      ∃ W : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) ℂ, HasOrthonormalCols W ∧
        specNorm (V * W - decodeMatrix dec Qm) ≤ ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)) ∧
        specNorm (decodeMatrix dec Am - (Wᴴ * (Vᴴ * decodeMatrix dec y.A * V) * W +
          dec σ • (1 : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) ℂ))) ≤
            (2 + 2 * ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) * dec y.R *
              ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) := by
  obtain ⟨hk2, hint⟩ := two_le_and_le_eq_false_of_eighStep_eq_split hsplit
  obtain ⟨⟨hv, hI⟩, hII⟩ := hgood hk2 hint
  have hR0 : 0 < dec y.R := hB.pos_w.trans_le hB.w_le
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast (by omega : 1 ≤ y.k)
  obtain ⟨hu1, hτ1, hτR6, hkτR, hΩ2, hΩ4, hμ, hsk, huβ, hβ1, hβη, hη0, hη1, hk2u, hkτ, hΩk,
    hτx, hdefl, hΩt⟩ := hB.split_numerics hk2 hM hint
  -- the shift
  have hσ := hM.abs_dec_div_ofNat_two_sub_le hu (by linarith) hτ₀ hτ1 hτR6 hΩ2 (by linarith)
  have hhalf : |dec (M.div y.R (M.ofNat 2))| ≤ dec y.R := by
    have h1 := abs_sub_abs_le_abs_sub (dec (M.div y.R (M.ofNat 2))) (dec y.R / 2)
    rw [abs_of_pos (by linarith : 0 < dec y.R / 2)] at h1
    linarith [mul_le_mul_of_nonneg_right hu1 hR0.le]
  have htwo : |dec (M.ofNat 2) - 2| ≤ 3 * u := by
    have h := abs_sub_le_of_isRoundingOf (hM.ofNat 2) (by push_cast; rw [abs_two]; exact hΩ2) hu
      hτ₀
    push_cast at h
    rw [abs_two, abs_sub_comm] at h
    linarith [mul_le_mul_of_nonneg_left (by linarith : τ ≤ 1) hu]
  -- Event I: the ideal shift is not an eigenvalue
  have hc : ∀ x ∈ spectrum ℝ (decodeMatrix dec y.A), x ≠ dec y.R / y.ℓ * smp.1 :=
    fun x hx hxc => by have := hI x hx; rw [hxc, sub_self, abs_zero] at this; linarith [hB.pos_w]
  obtain ⟨hPp, hPm⟩ :=
    hM.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget hB hint hv hI
  have hkpr := hM.min_toNat_eq_inertiaPos_of_specNorm_sub_le hu hτ₀ hk1 hk2u hkτ hΩk
    hB.isHermitian hc hB.pos_β.le hB.mul_β_le hPp
  -- unfold the step
  unfold eighStep at hsplit
  rw [if_neg (by omega), if_neg (by simp [hint])] at hsplit
  dsimp only at hsplit
  split_ifs at hsplit with h1 h2
  cases hsplit
  refine ⟨hσ, ?_, ?_⟩
  · -- the positive side
    obtain ⟨V, hV, hVV, hsp⟩ := exists_frame_pos hB.isHermitian hB.specNorm_le hc hkpr.symm
    have hr0 := Nat.pos_of_ne_zero h2
    have hrk := lt_of_le_of_ne (min_le_left _ _) h1
    obtain ⟨hGt, hσG⟩ := hII true _ V hr0 hrk hV (by rw [if_pos rfl, one_smul]; exact hVV)
    rw [specNorm_sub_comm, ← hVV] at hPp
    exact ⟨V, hV, hVV, hsp, hM.exists_hasOrthonormalCols_deflate_compress_le_of_mul_le (by omega)
      hr0 hrk.le hB.nonneg_μM hu huβ hμ hsk hB.pos_β.le hβ1 hβη hη0 hη1 hR0 hτ₀ hkτR hΩ4
      hB.pos_x hB.defl_tol hdefl hτx hΩt hB.isHermitian hB.specNorm_le htwo hV hPp hGt
      (hσG hrk.le) hhalf⟩
  · -- the negative side
    obtain ⟨V, hV, hVV, hsp⟩ := exists_frame_neg hB.isHermitian hB.specNorm_le hc hkpr.symm
      (min_le_left _ _)
    have hr0 := Nat.sub_pos_of_lt (lt_of_le_of_ne (min_le_left _ _) h1)
    have hrk : y.k - _ < y.k := Nat.sub_lt (by omega) (Nat.pos_of_ne_zero h2)
    obtain ⟨hGt, hσG⟩ := hII false _ V hr0 hrk hV
      (by rw [if_neg (by simp), neg_one_smul, ← sub_eq_add_neg]; exact hVV)
    rw [specNorm_sub_comm, ← hVV] at hPm
    obtain ⟨W, hW, hWb, hC⟩ := hM.exists_hasOrthonormalCols_deflate_compress_le_of_mul_le
      (by omega) hr0 hrk.le hB.nonneg_μM hu huβ hμ hsk hB.pos_β.le hβ1 hβη hη0 hη1 hR0 hτ₀
      hkτR hΩ4 hB.pos_x hB.defl_tol hdefl hτx hΩt hB.isHermitian hB.specNorm_le htwo hV hPm hGt
      (hσG hrk.le) (s := M.neg (M.div y.R (M.ofNat 2))) (by rw [hM.dec_neg, abs_neg]; exact hhalf)
    rw [hM.dec_neg, neg_smul, sub_neg_eq_add] at hC
    exact ⟨V, hV, hVV, hsp, W, hW, hWb, hC⟩

/-- The real arithmetic of the lower bound on the next window. -/
private theorem le_of_isRoundingOf_eighNextParams_fst_of_le {u τ Ω m t L a1 a2 c p r : ℝ}
    (hu : 0 ≤ u) (hum : u * m ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 8) (hm : 20 ≤ m)
    (hrτ : 7 * τ ≤ r) (hΩ : 2 * r + 2 * m + 4 ≤ Ω)
    (ht : IsRoundingOf u τ Ω 2 t) (hL : IsRoundingOf u τ Ω m L)
    (ha1 : t ≠ 0 → IsRoundingOf u τ Ω (1 / t) a1) (ha2 : L ≠ 0 → IsRoundingOf u τ Ω (t / L) a2)
    (hc : IsRoundingOf u τ Ω (a1 + a2) c) (hp : IsRoundingOf u τ Ω (c * r) p) :
    (1 / 2 + 2 / m) * r - 4 * u * r ≤ p := by
  have rnd : ∀ {a z : ℝ}, IsRoundingOf u τ Ω a z → 0 ≤ a → a ≤ Ω →
      a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) :=
    fun h ha0 ha => le_and_le_of_isRoundingOf h ha0 ha hu hτ₀
  have hm0 : 0 < m := by linarith
  obtain ⟨w, hw_def⟩ : ∃ w, w = 1 / m := ⟨_, rfl⟩
  have hwm : w * m = 1 := by rw [hw_def]; field_simp
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw20 : w ≤ 1 / 20 := by rw [hw_def, div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have hu20 := mul_le_mul_of_nonneg_left hm hu
  have hu1 : u ≤ 1 / 20000 := by linarith
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  have huu := mul_nonneg hu hu
  have hr0 : 0 ≤ r := by linarith
  -- the stored `2` and `ℓ`
  obtain ⟨ht1, ht2⟩ := rnd ht (by norm_num) (by linarith)
  obtain ⟨hL1, hL2⟩ := rnd hL hm0.le (by linarith)
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  have ht2' : t ≤ 2 + 2.125 * u := by linarith
  -- `fl(1/fl(2))`
  have hit1 : 1 / 2 - 0.6 * u ≤ 1 / t := by
    rw [le_div_iff₀ ht0]
    have := mul_le_mul_of_nonneg_left ht2' (by linarith : (0 : ℝ) ≤ 1 / 2 - 0.6 * u)
    linarith
  have hit2 : 1 / t ≤ 0.51 := by rw [div_le_iff₀ ht0]; linarith
  obtain ⟨hA1, -⟩ := rnd (ha1 ht0.ne') (by positivity) (by linarith)
  have := mul_le_mul_of_nonneg_left hit2 hu
  -- `fl(fl(2)/fl(ℓ))`
  have hq1 : 2 * w - 5 * u * w ≤ t / L := by
    rw [le_div_iff₀ hL0]
    have h0 : 0 ≤ w * (2 - 5 * u) := mul_nonneg hw0.le (by linarith)
    have := mul_le_mul_of_nonneg_left hL2 h0
    have e : w * (2 - 5 * u) * (m + u * (m + τ)) =
        (2 - 5 * u) * (1 + u) + w * (2 - 5 * u) * (u * τ) := by
      linear_combination (2 - 5 * u) * (1 + u) * hwm
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτ1 hu) h0
    have := mul_le_mul_of_nonneg_right hw20 (by linarith : (0 : ℝ) ≤ 2 - 5 * u)
    have := mul_nonneg hw0.le hu
    nlinarith
  have hq2 : t / L ≤ 0.11 := by rw [div_le_iff₀ hL0]; linarith
  obtain ⟨hA2, -⟩ := rnd (ha2 hL0.ne') (by positivity) (by linarith)
  have := mul_le_mul_of_nonneg_left hq2 hu
  have := mul_le_mul_of_nonneg_left hw20 hu
  -- `fl(a1 + a2)`
  have ha1u : a1 ≤ 0.52 := by
    obtain ⟨-, h⟩ := rnd (ha1 ht0.ne') (by positivity) (by linarith); linarith
  have ha2u : a2 ≤ 0.12 := by
    obtain ⟨-, h⟩ := rnd (ha2 hL0.ne') (by positivity) (by linarith); linarith
  obtain ⟨hC, hC'⟩ := rnd hc (by linarith) (by linarith)
  have := mul_le_mul_of_nonneg_left (by linarith : a1 + a2 ≤ 0.65) hu
  have hC1 : 1 / 2 + 2 * w - 2.55 * u ≤ c := by linarith
  have hC2 : c ≤ 0.66 := by linarith
  -- `fl(c r)`
  have hcr0 : 0 ≤ c * r := mul_nonneg (by linarith) hr0
  have hcr1 : c * r ≤ 0.66 * r := mul_le_mul_of_nonneg_right hC2 hr0
  obtain ⟨hP, -⟩ := rnd hp hcr0 (by linarith)
  have := mul_le_mul_of_nonneg_right hC1 hr0
  have := mul_le_mul_of_nonneg_left hcr1 hu
  have := mul_le_mul_of_nonneg_left hrτ hu
  have := mul_nonneg hu hr0
  have e2 : 2 / m = 2 * w := by rw [hw_def]; ring
  rw [e2]
  linarith

/-- The stored next window is at least $(1/2 + 2/\ell)R - 4uR$. -/
private theorem FloatMachine.IsAccurate.le_dec_eighNextParams_fst {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (R e : F) {ℓ : ℕ} (hu : 0 ≤ u)
    (huℓ : u * ℓ ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 8) (hℓ : 20 ≤ ℓ)
    (hRτ : 7 * τ ≤ dec R) (hΩ : 2 * dec R + 2 * ℓ + 4 ≤ Ω) :
    (1 / 2 + 2 / (ℓ : ℝ)) * dec R - 4 * u * dec R ≤ dec (eighNextParams M R e ℓ).1 := by
  have h2 := hM.ofNat 2
  push_cast at h2
  exact le_of_isRoundingOf_eighNextParams_fst_of_le hu huℓ hτ₀ hτ1 (by exact_mod_cast hℓ) hRτ hΩ
    h2 (hM.ofNat ℓ) (fun h => hM.dec_one ▸ hM.div _ _ h) (fun h => hM.div _ _ h) (hM.add _ _)
    (hM.mul _ _)

/-- A Hermitian matrix between $a\mathbf{I}$ and $b\mathbf{I}$ is within $m$ of $c\mathbf{I}$ when
$b - c \le m$ and $c - a \le m$. -/
private theorem specNorm_sub_smul_one_le_of_le_of_le {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) {a b c m : ℝ} (h₁ : a • (1 : Matrix n n ℂ) ≤ X)
    (h₂ : X ≤ b • (1 : Matrix n n ℂ)) (hb : b - c ≤ m) (ha : c - a ≤ m) (hm : 0 ≤ m) :
    specNorm (X - c • (1 : Matrix n n ℂ)) ≤ m := by
  refine (hX.sub (isHermitian_real_smul_one c)).specNorm_le_of_le_smul_one hm ?_ ?_
  · have h := (smul_one_le_smul_one (n := n) (𝕜 := ℂ) (by linarith : c - m ≤ a)).trans h₁
    rw [sub_smul] at h
    rw [le_sub_iff_add_le]
    simpa [neg_add_eq_sub] using h
  · have h := h₂.trans (smul_one_le_smul_one (n := n) (𝕜 := ℂ) (by linarith : b ≤ m + c))
    rwa [add_smul, ← sub_le_iff_le_add] at h

/-- A Hermitian matrix with spectrum in $[a, b]$ lies between $a\mathbf{I}$ and $b\mathbf{I}$. -/
private theorem smul_one_le_and_le_smul_one_of_spectrum_subset {n : Type*} [Fintype n]
    [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) {a b : ℝ}
    (h : spectrum ℝ X ⊆ Set.Icc a b) :
    a • (1 : Matrix n n ℂ) ≤ X ∧ X ≤ b • (1 : Matrix n n ℂ) := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
    exact ⟨le_of_eq (Subsingleton.elim _ _), le_of_eq (Subsingleton.elim _ _)⟩
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n := ⟨Fintype.card n - 1, by omega⟩
    exact ⟨(smul_one_le_smul_one (h (hX.eigenvalue_mem_spectrum (by omega : k < _))).1).trans
      (hX.eigenvalue_last_smul_one_le hk), hX.le_eigenvalue_zero_smul_one.trans
        (smul_one_le_smul_one (h (hX.eigenvalue_mem_spectrum h0)).2)⟩

open scoped ComplexOrder in
/-- All eigenvalues above $c$: $c\mathbf{I} \preceq \mathbf{X}$ when $i_+(\mathbf{X} -
c\mathbf{I})$ is the size. -/
private theorem smul_one_le_of_inertiaPos_eq_card {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) {c : ℝ}
    (h : inertiaPos (X - c • (1 : Matrix n n ℂ)) = Fintype.card n) :
    c • (1 : Matrix n n ℂ) ≤ X :=
  Matrix.le_iff.mpr ((hX.sub (isHermitian_real_smul_one _)).posDef_iff_inertiaPos_eq_card.mpr
    h).posSemidef

/-- No eigenvalue above $c$: $\mathbf{X} \preceq c\mathbf{I}$ when $i_+(\mathbf{X} - c\mathbf{I})
= 0$. -/
private theorem le_smul_one_of_inertiaPos_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) {c : ℝ} (hn : 0 < Fintype.card n)
    (h : inertiaPos (X - c • (1 : Matrix n n ℂ)) = 0) :
    X ≤ c • (1 : Matrix n n ℂ) := by
  have hB : (X - c • (1 : Matrix n n ℂ)).IsHermitian := hX.sub (isHermitian_real_smul_one _)
  have hpos : ¬ 0 < inertiaPos (X - c • (1 : Matrix n n ℂ)) := by rw [h]; exact lt_irrefl 0
  rw [hB.lt_inertiaPos_iff] at hpos
  have h0 := hB.le_eigenvalue_zero_smul_one.trans (smul_one_le_smul_one (n := n) (𝕜 := ℂ)
    (le_of_not_gt fun hc => hpos ⟨hn, hc⟩))
  rw [zero_smul] at h0
  exact sub_nonpos.mp h0

/-- The deflation accuracy $\eta = (1 - 1/\ell)\varepsilon/(5\ell)$ has
$0 \le \eta\ell \le 1/40$. -/
private theorem eta_mul_le {ε : ℝ} {ℓ : ℕ} (hℓ : 20 ≤ ℓ) (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8) :
    0 ≤ (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) ∧ (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) * ℓ ≤ 1 / 40 := by
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have h1 : 1 / (ℓ : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h0 : 0 ≤ 1 / (ℓ : ℝ) := by positivity
  refine ⟨div_nonneg (mul_nonneg (by linarith) hε.le) (by positivity), ?_⟩
  rw [show (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) * ℓ = (1 - 1 / (ℓ : ℝ)) * ε / 5 by field_simp]
  linarith [mul_le_mul_of_nonneg_right (by linarith : 1 - 1 / (ℓ : ℝ) ≤ 1) hε.le]

/-- A shift child: the stored $\mathrm{fl}(\mathbf{A} - s\mathbf{I})$, for
$\|\mathbf{A} - s\mathbf{I}\|_2 \le m \le \Omega$ and $m + u(m + \tau) \le r$, is Hermitian with
norm at most $r$. -/
private theorem FloatMachine.IsAccurate.isHermitian_and_specNorm_decodeMatrix_hermShift_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k : ℕ} {A : Matrix (Fin k) (Fin k) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian) (hu : 0 ≤ u) {s : F} {m r : ℝ} (hτ₀ : 0 ≤ τ)
    (hs : specNorm (decodeMatrix dec A - dec s • (1 : Matrix (Fin k) (Fin k) ℂ)) ≤ m)
    (hΩ : m ≤ Ω) (hr : m + u * (m + τ) ≤ r) :
    (decodeMatrix dec (M.hermShift A s)).IsHermitian ∧
      specNorm (decodeMatrix dec (M.hermShift A s)) ≤ r := by
  refine ⟨hM.isHermitian_decodeMatrix_hermFrom _ _, ?_⟩
  have hS := (hM.specNorm_sub_decodeMatrix_hermShift_le hu hA s (hs.trans hΩ)).trans
    (mul_le_mul_of_nonneg_left (max_le_add_of_nonneg (specNorm_nonneg _) hτ₀) hu)
  have htri := specNorm_sub_le (decodeMatrix dec A - dec s • (1 : Matrix (Fin k) (Fin k) ℂ))
    ((decodeMatrix dec A - dec s • (1 : Matrix (Fin k) (Fin k) ℂ)) -
      decodeMatrix dec (M.hermShift A s))
  rw [sub_sub_cancel] at htri
  nlinarith [mul_le_mul_of_nonneg_left hs hu]

/-- A split child: a matrix within $\gamma$ of the shifted compression
$\mathbf{W}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}}\mathbf{X}\mathbf{V}\mathbf{W} - c\mathbf{I}$
($\mathbf{W}$ unitary), when the compression $\mathbf{V}^{\mathsf{H}}\mathbf{X}\mathbf{V}$ has
spectrum in $[a, b]$ with $b - c, c - a \le m$, has norm at most $m + \gamma$. -/
private theorem specNorm_le_of_spectrum_subset_of_specNorm_sub_le {k r : ℕ}
    {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian) {V : Matrix (Fin k) (Fin r) ℂ}
    {W : Matrix (Fin r) (Fin r) ℂ} (hW : HasOrthonormalCols W) {a b c m γ : ℝ}
    (hspec : spectrum ℝ (Vᴴ * X * V) ⊆ Set.Icc a b) (hb : b - c ≤ m) (ha : c - a ≤ m)
    (hm : 0 ≤ m) {Y : Matrix (Fin r) (Fin r) ℂ}
    (hY : specNorm (Y - (Wᴴ * (Vᴴ * X * V) * W - c • (1 : Matrix (Fin r) (Fin r) ℂ))) ≤ γ) :
    specNorm Y ≤ m + γ := by
  have hC : (Vᴴ * X * V).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul V hX
  obtain ⟨hlo, hhi⟩ := smul_one_le_and_le_smul_one_of_spectrum_subset hC hspec
  have hWC : specNorm (Wᴴ * (Vᴴ * X * V) * W - c • (1 : Matrix (Fin r) (Fin r) ℂ)) ≤ m := by
    rw [show Wᴴ * (Vᴴ * X * V) * W - c • (1 : Matrix (Fin r) (Fin r) ℂ) =
        Wᴴ * (Vᴴ * X * V - c • (1 : Matrix (Fin r) (Fin r) ℂ)) * W by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        show Wᴴ * W = 1 from hW]]
    exact (hW.specNorm_conjTranspose_mul_mul_le _).trans
      (specNorm_sub_smul_one_le_of_le_of_le hC hlo hhi hb ha hm)
  have h := specNorm_add_le (Wᴴ * (Vᴴ * X * V) * W - c • (1 : Matrix (Fin r) (Fin r) ℂ))
    (Y - (Wᴴ * (Vᴴ * X * V) * W - c • (1 : Matrix (Fin r) (Fin r) ℂ)))
  rw [add_sub_cancel] at h
  linarith


/-- The scalar facts of a node budget: $k^2u \le 10^{-5}$, $k\tau \le 1/4$, $u\ell \le 10^{-5}$
and $t \ge 2$, for $k \ge 1$. -/
private theorem FloatMachine.IsEighNodeBudget.scalars
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk : 1 ≤ y.k) :
    (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 ∧ (y.k : ℝ) * τ ≤ 1 / 4 ∧ u * y.ℓ ≤ 1 / 100000 ∧
      2 ≤ t := by
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hsk : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hs2 : 1 ≤ √(2 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have ht : 2 ≤ t := by nlinarith [hB.le_t]
  have hu := hB.nonneg_u
  have hβ := hB.pos_β
  -- `2048 k ⋅ 20 u ≤ β` from the stopping condition
  have hku : 40960 * (y.k * u) ≤ dec β := by
    have hR := hB.pos_w.trans_le hB.w_le
    have hN := newtonSchulzSteps_nonneg (s := w / (5 * dec y.R)) (ε := dec β / (16 * y.k))
      (by have := hB.pos_w; positivity)
      (by rw [div_le_iff₀ (by positivity)]; linarith [hB.w_le]) (by positivity)
      (by rw [div_le_iff₀ (by positivity)]; nlinarith [hB.mul_β_le])
    have hS : (y.k : ℝ) ≤ y.k + newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) + 1 :=
      by linarith
    have hν : (20 : ℝ) ≤ 4 * μM y.k + 10 + 10 * √(y.k : ℝ) := by linarith [hB.nonneg_μM]
    have := mul_le_mul (mul_le_mul_of_nonneg_left hS (by norm_num : (0 : ℝ) ≤ 2048)) hν
      (by norm_num) (by positivity)
    nlinarith [hB.stop_tol]
  have hkβ := hB.mul_β_le
  refine ⟨by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y.k) hu], ?_, ?_, ht⟩
  · have := hB.τ_le.trans ((min_le_left _ _).trans hB.x_le)
    nlinarith [mul_le_mul_of_nonneg_left hsk (mul_nonneg (by linarith : (0 : ℝ) ≤ y.k) hB.nonneg_τ)]
  · have hℓ : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
    have h4 : 4 ≤ 2 * t / x := by rw [le_div_iff₀ hB.pos_x]; nlinarith [hB.x_le, hB.pos_x]
    have hη : (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) * y.ℓ ≤ 1 / 40 := by
      rw [show (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) * y.ℓ =
        (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / 5 by field_simp]
      have : 0 ≤ 1 / (y.ℓ : ℝ) := by positivity
      nlinarith [hB.ε_le, hB.pos_ε]
    have h1 := mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_right h4 hβ.le)
      hB.defl_tol) (by linarith : (0 : ℝ) ≤ y.ℓ)
    nlinarith [mul_le_mul_of_nonneg_right hk1 (mul_nonneg hu (by linarith : (0 : ℝ) ≤ y.ℓ))]

/-- The scalar budget of a child under a node budget: with $D = R/\ell$, the stored half window
$h = \mathrm{fl}(R/\mathrm{fl}(2))$ and $m = R/2 + D + 1.5uR$, $\lvert h - R/2\rvert \le 1.5uR$
and the next window $R'$ is at least $m + u(m + \tau)$ and $m + (2 + 2\eta)R\eta$, and
$m \le \Omega$, when $k \ge 2$ and the leaf test fails. -/
private theorem FloatMachine.IsAccurate.child_numerics_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk : 2 ≤ y.k)
    (hint : M.le y.R (M.mul y.ε R₀) = false) :
    |dec (M.div y.R (M.ofNat 2)) - dec y.R / 2| ≤ 3 * u * (dec y.R / 2) ∧
      dec y.R / 2 + dec y.R / y.ℓ + 1.5 * (u * dec y.R) + u * (dec y.R / 2 + dec y.R / y.ℓ +
        1.5 * (u * dec y.R) + τ) ≤ dec (eighNextParams M y.R y.ε y.ℓ).1 ∧
      dec y.R / 2 + dec y.R / y.ℓ + 1.5 * (u * dec y.R) +
        (2 + 2 * ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) * dec y.R *
          ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)) ≤ dec (eighNextParams M y.R y.ε y.ℓ).1 ∧
      dec y.R / 2 + dec y.R / y.ℓ + 1.5 * (u * dec y.R) ≤ Ω := by
  have hℓ := hB.twenty_le
  have hε := hB.pos_ε
  have hε₁ := hB.ε_le
  have hR₀ := hB.pos_R₀
  have hw := hB.pos_w
  have hwR := hB.w_le
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hτ := hB.τ_le
  have hΩ := hB.Ω_le
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hℓ
  obtain ⟨-, hkτ, huℓ, ht2⟩ := hB.scalars (by omega)
  obtain ⟨hη0, hηℓ⟩ := eta_mul_le hℓ hε hε₁
  have hk2 : (2 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hu1 : u ≤ 1 / 1000 := by linarith [mul_le_mul_of_nonneg_left hℓ' hu]
  have hτ1 : τ ≤ 1 / 8 := by linarith [mul_le_mul_of_nonneg_right hk2 hτ₀]
  have hR0 : 0 < dec y.R := hw.trans_le hwR
  have hRτ : 7 * τ ≤ dec y.R := by
    have h2 := mul_le_mul hk2 (Real.one_le_sqrt.mpr (by linarith : (1 : ℝ) ≤ y.k)) zero_le_one
      (by linarith)
    have := hM.mul_sub_lt_of_le_eq_false hu hτ₀ hε.le hR₀.le
      (by linarith [mul_le_mul_of_nonneg_right hε₁ hR₀.le]) hint
    linarith [hτ.trans (min_le_right _ _), mul_le_mul_of_nonneg_left h2 hτ₀,
      mul_le_mul_of_nonneg_right hu1 (mul_pos hε hR₀).le, mul_le_mul_of_nonneg_right hu1 hτ₀]
  have hR' := hM.le_dec_eighNextParams_fst y.R y.ε hu (by linarith) hτ₀ hτ1 hℓ hRτ (by linarith)
  have hhalf := hM.abs_dec_div_ofNat_two_sub_le (R := y.R) hu hu1 hτ₀ hτ1 (by linarith)
    (by linarith) (by linarith)
  set D := dec y.R / y.ℓ with hD
  have hD0 : 0 ≤ D := by positivity
  have hDℓ : D * y.ℓ = dec y.R := by rw [hD]; field_simp
  have hD20 : D ≤ dec y.R / 20 := by linarith [mul_le_mul_of_nonneg_left hℓ' hD0]
  have huR : u * dec y.R ≤ D / 100000 := by
    have := mul_le_mul_of_nonneg_right huℓ hD0
    rw [mul_assoc, mul_comm (y.ℓ : ℝ) D, hDℓ] at this
    linarith
  have huR0 : 0 ≤ u * dec y.R := mul_nonneg hu hR0.le
  rw [show (1 / 2 + 2 / (y.ℓ : ℝ)) * dec y.R = dec y.R / 2 + 2 * D by rw [hD]; ring] at hR'
  set m := dec y.R / 2 + D + 1.5 * (u * dec y.R) with hm
  have hm1 : m ≤ 0.6 * dec y.R := by linarith
  have hr : m + u * (m + τ) ≤ dec (eighNextParams M y.R y.ε y.ℓ).1 := by
    linarith [mul_le_mul_of_nonneg_left hm1 hu, mul_le_mul_of_nonneg_left hRτ hu]
  set η := (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) with hη
  have hηR : (2 + 2 * η) * dec y.R * η ≤ D / 19 := by
    have hη1 : η ≤ 1 / 800 := by linarith [mul_le_mul_of_nonneg_left hℓ' hη0]
    rw [show (2 + 2 * η) * dec y.R * η = (2 + 2 * η) * (η * y.ℓ) * D by rw [← hDℓ]; ring]
    have := mul_le_mul (by linarith : 2 + 2 * η ≤ 2.0025) hηℓ (by positivity) (by norm_num)
    linarith [mul_le_mul_of_nonneg_right this hD0]
  exact ⟨hhalf, hr, by linarith, by linarith⟩

/-- The rounded rank estimate of an internal node with a node budget and Event I is the inertia
$i_+(\mathbf{A} - c'\mathbf{I})$ of the ideal shift. -/
private theorem FloatMachine.IsAccurate.min_toNat_eq_inertiaPos_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
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
  have hA := hB.isHermitian
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hβ := hB.pos_β
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast (by omega : 1 ≤ y.k)
  have hkβ := hB.mul_β_le
  obtain ⟨hk2u, hkτ, -, ht2⟩ := hB.scalars (by omega)
  have hβ1 : dec β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  -- the computed projector is near the ideal one, whose trace is the inertia
  obtain ⟨hP, -⟩ := hM.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget hB hint hv hI
  set Pp := M.hermScale (M.hermShift (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) (M.neg M.one)) (M.ofNat 2)
  set S := cfc Real.sign (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))
  have hPid : specNorm ((2⁻¹ : ℝ) • (1 + S)) ≤ 1 := by
    rw [specNorm_real_smul, abs_of_pos (by norm_num)]
    linarith [(specNorm_add_le 1 S).trans (add_le_add specNorm_one_le
      (specNorm_cfc_sign_sub_smul_one_le hA _))]
  have htr := hA.re_trace_smul_one_add_cfc_sign (c := dec y.R / y.ℓ * smp.1) fun e he h => by
    have := hI e he
    rw [h, sub_self, abs_zero] at this
    linarith [hB.pos_w]
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
    (by linarith [hB.Ω_le, hB.pos_R₀, hB.pos_w.trans_le hB.w_le,
      (Nat.cast_nonneg y.ℓ : (0 : ℝ) ≤ y.ℓ)]) Pp hrk (hdiag.trans (by linarith))
    (hsabs.trans (by linarith))]
  exact min_eq_right (by exact_mod_cast hrk)

/-- **Child invariant under a node budget** (EB1a'): with budget and a good sample, every child
has a Hermitian matrix of norm at most its window. [Shah2024, proof of Lemma 4.1].
Proof: EB1a's proof with EB1d' and EB1b' in place of EB1d and EB1b. M, about 120 lines. -/
theorem FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    {smp : EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w x t y smp)
    {b : Bool} {y' : EighNode F} (hy' : eighChild M N signFuel R₀ β y smp b = some y') :
    (decodeMatrix dec y'.A).IsHermitian ∧ specNorm (decodeMatrix dec y'.A) ≤ dec y'.R := by
  have hk : 2 ≤ y.k := by
    by_contra hk
    simp [eighChild, eighStep, show y.k ≤ 1 by omega] at hy'
  have hint := (le_eq_false_and_le_and_eq_of_eighChild_eq_some hy').2.1
  obtain ⟨⟨hv, hI⟩, -⟩ := hgood hk hint
  obtain ⟨hhalf, hr, hrη, hmΩ⟩ := hM.child_numerics_of_isEighNodeBudget hB hk hint
  have hkp := hM.min_toNat_eq_inertiaPos_of_isEighNodeBudget hB hk hint hv hI
  have hA := hB.isHermitian
  have hR := hB.specNorm_le
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  set X := decodeMatrix dec y.A with hX
  set D := dec y.R / y.ℓ with hD
  set h := dec (M.div y.R (M.ofNat 2)) with hh
  set m := dec y.R / 2 + D + 1.5 * (u * dec y.R) with hm
  set η := (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) with hη
  have hR0 : 0 ≤ dec y.R := (specNorm_nonneg _).trans hR
  have hD0 : 0 ≤ D := div_nonneg hR0 (Nat.cast_nonneg _)
  have hc'1 : -D ≤ D * smp.1 := by linarith [mul_le_mul_of_nonneg_left hv.1 hD0]
  have hc'2 : D * smp.1 ≤ D := by linarith [mul_le_mul_of_nonneg_left hv.2 hD0]
  have huR0 : 0 ≤ u * dec y.R := mul_nonneg hu hR0
  obtain ⟨hh1, hh2⟩ := abs_le.mp hhalf
  have hm0 : 0 ≤ m := by linarith
  have hXR : X ≤ dec y.R • (1 : Matrix (Fin y.k) (Fin y.k) ℂ) := hA.le_smul_one_of_specNorm_le hR
  have hXR' : (-dec y.R) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ) ≤ X := by
    rw [neg_smul]; exact hA.neg_smul_one_le_of_specNorm_le hR
  have hshift := fun (s : F) (hs : specNorm (X - dec s • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) ≤ m) =>
    hM.isHermitian_and_specNorm_decodeMatrix_hermShift_le hA hu hτ₀ hs hmΩ hr
  unfold eighChild eighStep at hy'
  rw [if_neg (by omega), if_neg (by simp [hint])] at hy'
  dsimp only at hy'
  split_ifs at hy' with h1 h2 h3 h4
  · -- the shift child on the positive side
    simp only [h2, if_true, Option.some.injEq] at hy'
    subst hy'
    rw [hkp] at h1
    exact hshift _ (specNorm_sub_smul_one_le_of_le_of_le hA
      (smul_one_le_of_inertiaPos_eq_card hA (by rw [Fintype.card_fin]; exact h1)) hXR
      (by linarith) (by linarith) hm0)
  · simp [h2] at hy'
  · simp [h4] at hy'
  · -- the shift child on the negative side
    simp only [show b = false by simpa using h4, if_true, Option.some.injEq] at hy'
    subst hy'
    rw [hkp] at h3
    refine hshift _ (specNorm_sub_smul_one_le_of_le_of_le hA hXR'
      (le_smul_one_of_inertiaPos_eq_zero hA (by rw [Fintype.card_fin]; omega) h3) ?_ ?_ hm0) <;>
      rw [hM.dec_neg] <;> linarith
  all_goals
    obtain ⟨-, hP, hQ⟩ := hM.exists_hasOrthonormalCols_specNorm_sub_le_of_isEighNodeBudget hB hgood
      (by
        unfold eighStep
        rw [if_neg (by omega), if_neg (by simp [hint])]
        dsimp only
        rw [if_neg h1, if_neg h3])
    rw [← hη, ← hX, ← hD, ← hh] at hP hQ
    simp only [Option.some.injEq] at hy'
    subst hy'
    refine ⟨hM.isHermitian_decodeMatrix_hermFrom _ _, ?_⟩
  · -- the split child on the positive side
    obtain ⟨V, hV, -, hspec, W, hW, -, hAp⟩ := hP
    exact (specNorm_le_of_spectrum_subset_of_specNorm_sub_le hA hW hspec (by linarith)
      (by linarith) hm0 hAp).trans (by linarith)
  · -- the split child on the negative side
    obtain ⟨V, hV, -, hspec, W, hW, -, hAm⟩ := hQ
    rw [← sub_neg_eq_add, ← neg_smul] at hAm
    exact (specNorm_le_of_spectrum_subset_of_specNorm_sub_le hA hW hspec (by linarith)
      (by linarith) hm0 hAm).trans (by linarith)

-- Copies of the private node helpers of `NLAlib.Matrix.Computation.SpectralBisection.Node`.

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


/-- The smallness facts of a node budget at a node of size at least $2$: $10^6\ell u$,
$10^5\ell\mu_{\mathrm{MM}}(k)u$ and $2 \cdot 10^7u$ are at most $\varepsilon$, $\tau \le 1/4$,
$4\tau \le \varepsilon R_0$ and $16(R_0 + R + k + \ell) \le \Omega$. -/
private theorem FloatMachine.IsEighNodeBudget.mul_le_dec_ε
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk : 2 ≤ y.k) :
    (y.ℓ : ℝ) * u * 1000000 ≤ dec y.ε ∧ (y.ℓ : ℝ) * (μM y.k * u) * 100000 ≤ dec y.ε ∧
      u * 20000000 ≤ dec y.ε ∧ τ ≤ 1 / 4 ∧ τ * 4 ≤ dec y.ε * dec R₀ ∧
      16 * (dec R₀ + dec y.R + y.k + y.ℓ) ≤ Ω := by
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hε := hB.pos_ε
  have hμM := hB.nonneg_μM
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
  have hk2 : (2 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hsk : √2 ≤ √(y.k : ℝ) := Real.sqrt_le_sqrt hk2
  have hsk1 : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hs22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have ht4 : 4 ≤ t := by nlinarith [hB.le_t, Real.sqrt_nonneg 2]
  -- the stopping condition bounds $u$ and $\mu_{\mathrm{MM}}(k)u$ by multiples of $\beta$
  have hβu : 2048 * 3 * (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u ≤ dec β := by
    refine le_trans ?_ hB.stop_tol
    have hRw := hB.pos_w.trans_le hB.w_le
    have hN := newtonSchulzSteps_nonneg (s := w / (5 * dec y.R)) (ε := dec β / (16 * y.k))
      (by positivity [hB.pos_w]) (by rw [div_le_iff₀ (by positivity)]; linarith [hB.w_le])
      (by positivity [hB.pos_β])
      (by rw [div_le_iff₀ (by positivity)]; nlinarith [hB.mul_β_le, hB.pos_β])
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) hu
    linarith
  have hu1 : u * 122880 ≤ dec β := by
    nlinarith [mul_nonneg hμM hu, mul_le_mul_of_nonneg_right hsk1 hu]
  have hμu : μM y.k * u * 24576 ≤ dec β := by
    nlinarith [mul_nonneg hμM hu, mul_nonneg (Real.sqrt_nonneg (y.k : ℝ)) hu]
  -- the deflation tolerance bounds $40\ell\beta$ by $\varepsilon$ (as $t \ge 4$, $x \le 1$)
  have hℓβ : (y.ℓ : ℝ) * dec β * 40 ≤ dec y.ε := by
    have hx := hB.pos_x
    have h1 : 8 * dec β ≤ 2 * t / x * dec β := by
      refine mul_le_mul_of_nonneg_right ?_ hB.pos_β.le
      rw [le_div_iff₀ hx]; nlinarith [hB.x_le]
    have h2 : (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ≤ dec y.ε / (5 * y.ℓ) :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_left hε.le (sub_le_self _ (by positivity)))
        (by positivity)
    have h3 := (h1.trans hB.defl_tol).trans h2
    rw [le_div_iff₀ (by positivity)] at h3
    linarith
  have hux : (y.ℓ : ℝ) * u * 1000000 ≤ dec y.ε := by
    nlinarith [mul_le_mul_of_nonneg_left hu1 (by linarith : (0 : ℝ) ≤ y.ℓ)]
  have hkk : (1 : ℝ) ≤ y.k * √(y.k : ℝ) := by nlinarith
  have hτk : τ * 4 ≤ τ * (4 * y.k * √(y.k : ℝ)) := by nlinarith
  refine ⟨hux, ?_, by nlinarith, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hμu (by linarith : (0 : ℝ) ≤ y.ℓ)]
  · linarith [hB.τ_le.trans (min_le_left _ _), hB.x_le]
  · linarith [hB.τ_le.trans (min_le_right _ _)]
  · linarith [hB.Ω_le]

/-- **A shift node under a node budget**: the output of a node whose step is a shift is an
approximate diagonalization with $(\varepsilon(R + R_0), \varepsilon/3)$, given the child's. -/
private theorem FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_eighStep_eq_shift
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    {f : ℕ} {s : List Bool → EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w x t y (s []))
    (hchild : ∀ (b : Bool) (y' : EighNode F), eighChild M N signFuel R₀ β y (s []) b = some y' →
      IsApproxDiagonalization (decodeMatrix dec y'.A)
        (decodeMatrix dec (eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).1)
        (fun i => dec ((eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).2 i))
        (dec y'.ε * (dec y'.R + dec R₀)) (dec y'.ε / 3))
    (hk : 2 ≤ y.k) {b : Bool} {A' : Matrix (Fin y.k) (Fin y.k) (F × F)} {σ : F}
    (hst : eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s []) = .shift b A' σ) :
    IsApproxDiagonalization (decodeMatrix dec y.A)
      (decodeMatrix dec (eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).1)
      (fun i => dec ((eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).2 i))
      (dec y.ε * (dec y.R + dec R₀)) (dec y.ε / 3) := by
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hε := hB.pos_ε
  have hε₁ := hB.ε_le
  have hR₀ := hB.pos_R₀
  have hR0 : 0 ≤ dec y.R := (specNorm_nonneg _).trans hB.specNorm_le
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
  have hk0 : (0 : ℝ) ≤ y.k := Nat.cast_nonneg _
  obtain ⟨hux, hvx, huε, hτ4, h4τ, hΩ'⟩ := hB.mul_le_dec_ε hk
  obtain ⟨hp1, hp2, hp3⟩ := hM.dec_eighNextParams_le (R := y.R) (ε := y.ε) (m := y.ℓ) hu
    (by linarith) hτ₀ (by linarith) hB.twenty_le (by linarith) hR0 (by linarith) hε.le
    (by linarith [hB.ε_le])
  have hhalf := hM.abs_dec_div_ofNat_two_le (R := y.R) hu (by linarith [hB.ε_le]) hτ₀ hτ4 hR0
    (by linarith [hB.pos_R₀]) (by linarith [hB.pos_R₀])
  obtain ⟨rfl, hσ⟩ := eq_hermShift_and_of_eighStep_eq_shift hst
  have hy' : eighChild M N signFuel R₀ β y (s []) b = some ⟨y.k, M.hermShift y.A σ,
      (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩ := by
    simp [eighChild, hst]
  have hc := hchild b _ hy'
  obtain ⟨-, hA'R⟩ := hM.isHermitian_and_specNorm_le_of_isEighNodeBudget hB hgood hy'
  dsimp only at hc hA'R
  simp only [eighAux, hst]
  obtain ⟨hκ0, hκ1, hξ0, -, -, -, -, hDs, hsing, -, hshift⟩ := node_budget (x := (y.ℓ : ℝ))
    (R := dec y.R) (R₀ := dec R₀) (v := μM y.k * u) hε hB.ε_le hℓ' hR0 hB.pos_R₀.le hu hux
    (mul_nonneg hB.nonneg_μM hu) hvx hτ₀ hτ4 (by linarith) hp2 hp3
    ((specNorm_nonneg _).trans hA'R) hp1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hσabs : |dec σ| ≤ dec y.R / 2 + 2 * u * dec y.R + u * τ := by
    rcases hσ with rfl | rfl
    · exact hhalf
    · rw [hM.dec_neg, abs_neg]; exact hhalf
  have huR := mul_le_mul_of_nonneg_right (by linarith : u ≤ 1) hR0
  have huτ := mul_le_mul_of_nonneg_right (by linarith : u ≤ 1) hτ₀
  exact isApproxDiagonalization_of_le (hM.isApproxDiagonalization_add_of_hermShift hu hτ₀
    hB.isHermitian hB.specNorm_le hσabs hκ0 hκ1 hc hA'R (by linarith) (by linarith)) hshift hκ0
    (by linarith [mul_nonneg (Real.sqrt_nonneg 2) hξ0]) (by linarith)

/-- **A split node under a node budget**: the output of a node whose step is a split is an
approximate diagonalization with $(\varepsilon(R + R_0), \varepsilon/3)$, given the
children's. -/
private theorem FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_eighStep_eq_split
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    {f : ℕ} {s : List Bool → EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w x t y (s []))
    (hchild : ∀ (b : Bool) (y' : EighNode F), eighChild M N signFuel R₀ β y (s []) b = some y' →
      IsApproxDiagonalization (decodeMatrix dec y'.A)
        (decodeMatrix dec (eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).1)
        (fun i => dec ((eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).2 i))
        (dec y'.ε * (dec y'.R + dec R₀)) (dec y'.ε / 3))
    (hk : 2 ≤ y.k) {kp : ℕ} {hkp : kp ≤ y.k} {Qp : Matrix (Fin y.k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin y.k) (Fin (y.k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) (F × F)} {σ : F}
    (hst : eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s []) = .split kp hkp Qp Qm Ap Am σ) :
    IsApproxDiagonalization (decodeMatrix dec y.A)
      (decodeMatrix dec (eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).1)
      (fun i => dec ((eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).2 i))
      (dec y.ε * (dec y.R + dec R₀)) (dec y.ε / 3) := by
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hε := hB.pos_ε
  have hε₁ := hB.ε_le
  have hR₀ := hB.pos_R₀
  have hR0 : 0 ≤ dec y.R := (specNorm_nonneg _).trans hB.specNorm_le
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
  have hk0 : (0 : ℝ) ≤ y.k := Nat.cast_nonneg _
  obtain ⟨hux, hvx, huε, hτ4, h4τ, hΩ'⟩ := hB.mul_le_dec_ε hk
  obtain ⟨hp1, hp2, hp3⟩ := hM.dec_eighNextParams_le (R := y.R) (ε := y.ε) (m := y.ℓ) hu
    (by linarith) hτ₀ (by linarith) hB.twenty_le (by linarith) hR0 (by linarith) hε.le
    (by linarith [hB.ε_le])
  obtain ⟨hσR, ⟨Vp, hVp, hVpP, -, Wp, hWp, hQp, hAp⟩, ⟨Vm, hVm, hVmP, -, Wm, hWm, hQm, hAm⟩⟩ :=
    hM.exists_hasOrthonormalCols_specNorm_sub_le_of_isEighNodeBudget hB hgood hst
  have hyp : eighChild M N signFuel R₀ β y (s []) true = some ⟨kp, Ap,
      (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩ := by
    simp [eighChild, hst]
  have hym : eighChild M N signFuel R₀ β y (s []) false = some ⟨y.k - kp, Am,
      (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩ := by
    simp [eighChild, hst]
  obtain ⟨-, hApR⟩ := hM.isHermitian_and_specNorm_le_of_isEighNodeBudget hB hgood hyp
  obtain ⟨-, hAmR⟩ := hM.isHermitian_and_specNorm_le_of_isEighNodeBudget hB hgood hym
  have hcp := hchild true _ hyp
  have hcm := hchild false _ hym
  dsimp only at hcp hcm hApR hAmR
  simp only [eighAux, hst]
  obtain ⟨hκ0, hκ1, hξ0, -, -, -, -, hDs, hsing, hsplit, -⟩ := node_budget (x := (y.ℓ : ℝ))
    (R := dec y.R) (R₀ := dec R₀) (v := μM y.k * u) hε hB.ε_le hℓ' hR0 hB.pos_R₀.le hu hux
    (mul_nonneg hB.nonneg_μM hu) hvx hτ₀ hτ4 (by linarith) hp2 hp3
    ((specNorm_nonneg _).trans hApR) hp1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hsξ := mul_nonneg (Real.sqrt_nonneg 2) hξ0
  have hσabs : |dec σ| ≤ dec y.R / 2 + 2 * u * dec y.R + u * τ := by
    rw [abs_le] at hσR ⊢
    constructor <;> linarith [mul_nonneg hu hR0, mul_nonneg hu hτ₀]
  have hη1 : (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ≤ 1 := div_le_one_of_le₀
    ((mul_le_of_le_one_left hε.le (sub_le_self _ (by positivity))).trans
      (by linarith [hB.ε_le])) (by positivity)
  have key := hM.isApproxDiagonalization_submatrix_fromCols_mm hkp hB.nonneg_μM hu hτ₀ hVp hVm
    hWp hWm hVpP hVmP hQp hQm hAp hAm hcp hcm hApR hAmR hσabs hκ0 hκ1 (by linarith) hη1
    (by linarith) (by linarith) rfl rfl rfl
  exact isApproxDiagonalization_of_le key hsplit (by linarith) (by linarith) (by linarith)

/-- **Local guarantee under a node budget** (EB1'): with budget, a good sample when internal and
children that are approximate diagonalizations with $(\varepsilon'(R' + R_0), \varepsilon'/3)$,
the node's output is one with $(\varepsilon(R + R_0), \varepsilon/3)$. [Shah2024, Lemma 4.1].
Proof: Smallness facts: re-derive the conjuncts of `NLAlib.mul_le_of_le_bisectionSignTol` from the
budget ($k\beta \le 1/57600$ is `mul_β_le`; $k^2u$, $k^{3/2}u \le \beta/20480$ and $u \le
\beta/147456$ from `stop_tol`; $k\tau \le 1/4$ from `τ_le`; $10^6\ell u$, $10^5\ell\mu u \le
\varepsilon$ from `defl_tol` and `stop_tol`); the conjunct $k^{3/2}uR \le w\beta/20480$ is gone
(not derivable) and is replaced by the $\beta/64$ shift budget below. EB1's proof (the residual
budget closing through $\varepsilon' = (1 - 1/\ell)\varepsilon$
is unchanged, since the deflation error is still at most $\eta$) with EB1c', EB1b', EB1d', EB1a'.
H, about 300 lines (EB1's private node budget reused). -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    {f : ℕ} {s : List Bool → EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w x t y (s []))
    (hchild : ∀ (b : Bool) (y' : EighNode F), eighChild M N signFuel R₀ β y (s []) b = some y' →
      IsApproxDiagonalization (decodeMatrix dec y'.A)
        (decodeMatrix dec (eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).1)
        (fun i => dec ((eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).2 i))
        (dec y'.ε * (dec y'.R + dec R₀)) (dec y'.ε / 3)) :
    IsApproxDiagonalization (decodeMatrix dec y.A)
      (decodeMatrix dec (eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).1)
      (fun i => dec ((eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).2 i))
      (dec y.ε * (dec y.R + dec R₀)) (dec y.ε / 3) := by
  have hA := hB.isHermitian
  have hε := hB.pos_ε
  have hR₀ := hB.pos_R₀
  have hR0 : 0 ≤ dec y.R := (specNorm_nonneg _).trans hB.specNorm_le
  by_cases hk : y.k ≤ 1
  · exact hM.isApproxDiagonalization_eighAux_succ_of_leaf hA (by positivity)
      (by linarith [hB.ε_le]) (Or.inl ⟨hk, mul_nonneg hε.le (by linarith)⟩)
  have hk2 : 2 ≤ y.k := by omega
  obtain ⟨-, -, huε, -, h4τ, hΩ'⟩ := hB.mul_le_dec_ε hk2
  have hk0 : (0 : ℝ) ≤ y.k := Nat.cast_nonneg _
  have hℓ0 : (0 : ℝ) ≤ y.ℓ := Nat.cast_nonneg _
  by_cases ht : M.le y.R (M.mul y.ε R₀) = true
  · exact hM.isApproxDiagonalization_eighAux_succ_of_leaf hA (by positivity)
      (by linarith [hB.ε_le]) (Or.inr ⟨ht, hB.specNorm_le.trans
        (hM.le_mul_add_of_le_eq_true hB.nonneg_u hB.nonneg_τ hε hB.ε_le hR₀ hR0
          (by linarith) h4τ (by linarith) ht)⟩)
  have hint : M.le y.R (M.mul y.ε R₀) = false := by simpa using ht
  rcases hst : eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s []) with
    ⟨U, d⟩ | ⟨b, A', σ⟩ | ⟨kp, hkp, Qp, Qm, Ap, Am, σ⟩
  · exact absurd hst (eighStep_ne_leaf hk hint U d)
  · exact hM.isApproxDiagonalization_eighAux_succ_of_eighStep_eq_shift hB hgood hchild hk2 hst
  · exact hM.isApproxDiagonalization_eighAux_succ_of_eighStep_eq_split hB hgood hchild hk2 hst

/-- The rounded next tolerance of a node: $\varepsilon' \le \varepsilon$ and
$\varepsilon(L - 1) - 3uL\varepsilon \le \varepsilon' L$. -/
private theorem FloatMachine.IsAccurate.le_dec_eighNextParams_snd_mul {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (r e : F)
    {L : ℕ} (hu : 0 ≤ u) (huL : u * L ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 100)
    (he0 : 0 < dec e) (hτe : 30 * τ ≤ dec e) (he1 : dec e ≤ 1) (hL : 5 ≤ L)
    (hΩ : 2 + L ≤ Ω) :
    dec (eighNextParams M r e L).2 ≤ dec e ∧
      dec e * (L - 1) - 3 * u * L * dec e ≤ dec (eighNextParams M r e L).2 * L := by
  have hL' : (5 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hu5 : u ≤ 1 / 5000 := by nlinarith
  simp only [eighNextParams]
  obtain ⟨hla, hlb⟩ := le_and_le_of_isRoundingOf (hM.ofNat L) hL0.le (by linarith) hu hτ₀
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  have hdl : L - 0.002 ≤ dec (M.ofNat L) ∧ dec (M.ofNat L) ≤ L + 0.002 := by
    constructor <;> linarith
  have hdl0 : 0 < dec (M.ofNat L) := by linarith
  have hiL1 : 1 / (L : ℝ) * L = 1 := by field_simp
  have hiL5 : 1 / (L : ℝ) ≤ 1 / 5 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have huiL : u ≤ 1 / (L : ℝ) / 1000 := by
    rw [le_div_iff₀ (by norm_num), le_div_iff₀ hL0]; linarith
  -- the reciprocal of the depth counter
  have hq0 : |1 / dec (M.ofNat L) - 1 / L| ≤ u / 4 := by
    rw [div_sub_div _ _ hdl0.ne' hL0.ne', abs_div, abs_of_pos (mul_pos hdl0 hL0),
      div_le_iff₀ (mul_pos hdl0 hL0), abs_le]
    have h1 : L + τ ≤ dec (M.ofNat L) * L / 4 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ dec (M.ofNat L) - 4.99) hL0.le]
    have h2 := mul_le_mul_of_nonneg_left h1 hu
    constructor <;> linarith
  have hq0' := abs_le.mp hq0
  obtain ⟨hqa, hqb⟩ := le_and_le_of_isRoundingOf (hM.div M.one (M.ofNat L) hdl0.ne')
    (by rw [hM.dec_one]; positivity) (by rw [hM.dec_one]; linarith) hu hτ₀
  rw [hM.dec_one] at hqa hqb
  have hq021 : 1 / dec (M.ofNat L) ≤ 0.21 := by linarith
  have hdq : 1 / L - u / 2 ≤ dec (M.div M.one (M.ofNat L)) ∧
      dec (M.div M.one (M.ofNat L)) ≤ 1 / L + u / 2 := by
    have := mul_le_mul_of_nonneg_left hq021 hu
    constructor <;> linarith
  obtain ⟨hsa, hsb⟩ := le_and_le_of_isRoundingOf (hM.sub M.one (M.div M.one (M.ofNat L)))
    (by rw [hM.dec_one]; linarith) (by rw [hM.dec_one]; linarith) hu hτ₀
  rw [hM.dec_one] at hsa hsb
  have hds : 1 - 1 / L - 1.6 * u ≤ dec (M.sub M.one (M.div M.one (M.ofNat L))) ∧
      dec (M.sub M.one (M.div M.one (M.ofNat L))) ≤ 1 - 1 / L + 1.6 * u := by
    have := mul_le_mul_of_nonneg_left (show 1 - dec (M.div M.one (M.ofNat L)) ≤ 1 by linarith) hu
    constructor <;> linarith
  have hds0 : 0 ≤ dec (M.sub M.one (M.div M.one (M.ofNat L))) := by linarith
  have hds1 : dec (M.sub M.one (M.div M.one (M.ofNat L))) ≤ 1 := by linarith
  have hdse := mul_le_of_le_one_left he0.le hds1
  obtain ⟨hea, heb⟩ := le_and_le_of_isRoundingOf (hM.mul (M.sub M.one (M.div M.one (M.ofNat L))) e)
    (mul_nonneg hds0 he0.le) (by linarith) hu hτ₀
  have hde : (1 - 1 / L) * dec e - 3 * u * dec e ≤
      dec (M.mul (M.sub M.one (M.div M.one (M.ofNat L))) e) ∧
      dec (M.mul (M.sub M.one (M.div M.one (M.ofNat L))) e) ≤
        (1 - 1 / L) * dec e + 3 * u * dec e := by
    have h1 := mul_le_mul_of_nonneg_right hds.1 he0.le
    have h2 := mul_le_mul_of_nonneg_right hds.2 he0.le
    have h3 := mul_le_mul_of_nonneg_left hdse hu
    have h4 := mul_le_mul_of_nonneg_left hτe hu
    constructor <;> linarith
  have hue := mul_le_mul_of_nonneg_right huiL he0.le
  refine ⟨by linarith, ?_⟩
  have := mul_le_mul_of_nonneg_right hde.1 hL0.le
  linear_combination this + dec e * hiL1

/-- **The tolerance at a node, telescoped** (EB2a'): under the hypotheses of
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params`, every node $y$ below the root has
$$\varepsilon_y \ge (1 - 2^{-8})\,\frac{\ell - 1}{\ell_y - 1}\,\varepsilon \,,$$
in particular $\varepsilon_y \ge (1 - 2^{-8})(\ell - 1)\varepsilon/(2\ell - 1)$ since
$\ell_y \le 2\ell$; EB2a has $\varepsilon/3$. [Shah2024, proof of Theorem 4.2].
Proof: induction on the path as in EB2a: each level multiplies by $\mathrm{fl}(1 -
\mathrm{fl}(1/\ell_j)) \ge (1 - 1/\ell_j)(1 - 5u)$
(`NLAlib.FloatMachine.IsAccurate.dec_eighNextParams_le` and its lower companion), the exact
factors telescope to $(\ell - 1)/(\ell_y - 1)$, and
$(1 - 5u)^{\ell} \ge 1 - 5\ell u \ge 1 - 2^{-8}$ from $100\ell^2u \le 1$, $\ell \ge 20$. M, about
120 lines. -/
theorem FloatMachine.IsAccurate.mul_le_dec_ε_of_eighNodeAt_eq_some
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15)
    (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N)
    {a : List Bool} {y : EighNode F}
    (h : eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s = some y) :
    (1 - 2⁻¹ ^ 8) * (((ℓ : ℝ) - 1) / ((y.ℓ : ℝ) - 1)) * dec ε ≤ dec y.ε := by
  obtain ⟨hlen, -, hyℓ, -⟩ := hM.eighNodeAt_eq_some_params hε hε₁ hR₀ hℓ hu hu₁ hτ₀ hτ hΩ A s h
  have hℓ20 : (20 : ℝ) ≤ ℓ := by
    have h15 : (15 : ℝ) ≤ Real.logb 2 (dec ε)⁻¹ := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), show (15 : ℝ) = (15 : ℕ) by
        norm_num, Real.rpow_natCast, ← inv_inv ((2 : ℝ) ^ 15), ← inv_pow]
      exact inv_anti₀ hε (by simpa using hε₁)
    have := (h15.trans (Nat.le_ceil _))
    have : (bisectionDepth (dec ε) : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    simp only [bisectionDepth, Nat.cast_add] at this
    push_cast at this
    linarith
  have hε1 : dec ε ≤ 1 := hε₁.trans (by norm_num)
  have hτε : 100 * τ ≤ dec ε := hτ.trans (mul_le_of_le_one_right hε.le (min_le_right _ _))
  have huℓ : u * ℓ ≤ 1 / 2000 := by nlinarith
  -- the tolerance stays above a third of the root's
  have hlow : ∀ (x : EighNode F) (j : ℕ), j ≤ ℓ → x.ℓ = ℓ + j →
      dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * j ≤ dec x.ε * (x.ℓ - 1) → dec ε / 3 ≤ dec x.ε := by
    intro x j hj hxℓ hx
    have hj' : (j : ℝ) ≤ ℓ := by exact_mod_cast hj
    rw [hxℓ] at hx
    push_cast at hx
    have h1 := mul_le_mul_of_nonneg_left hj' (by positivity : 0 ≤ u * ℓ)
    have h2 := mul_le_mul_of_nonneg_right h1 hε.le
    by_contra hlt
    have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
    nlinarith [mul_lt_mul_of_pos_right (not_le.mp hlt) (by linarith : (0 : ℝ) < ℓ + j - 1)]
  -- each level loses at most `3 u ℓ_x ε_x ≤ 6 u ℓ ε` of `ε_x (ℓ_x - 1)`
  have key : ∀ (a : List Bool) (x : EighNode F) (s : List Bool → EighSample ℝ ℂ N) (j : ℕ)
      (y : EighNode F), j + a.length ≤ ℓ → x.ℓ = ℓ + j → dec x.ε ≤ dec ε →
      dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * j ≤ dec x.ε * (x.ℓ - 1) →
      eighNodeAt M N signFuel R₀ β a x s = some y →
      dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * (j + a.length : ℕ) ≤ dec y.ε * (y.ℓ - 1) := by
    intro a
    induction a with
    | nil =>
      intro x s j y _ h2 _ h4 h
      cases Option.some.inj h
      simpa using h4
    | cons b a ih =>
      intro x s j y hj h2 h3 h4 h
      simp only [eighNodeAt, Option.bind_eq_some_iff] at h
      obtain ⟨z, hz, hy⟩ := h
      obtain ⟨-, -, -, -, hzε, hzℓ⟩ := le_eq_false_and_le_and_eq_of_eighChild_eq_some hz
      simp only [List.length_cons] at hj
      have hxε := hlow x j (by omega) h2 h4
      have hx0 : 0 < dec x.ε := by linarith
      have hxℓ : (x.ℓ : ℝ) ≤ 2 * ℓ := by
        rw [h2]; push_cast; linarith [(by exact_mod_cast (by omega : j ≤ ℓ) : (j : ℝ) ≤ ℓ)]
      have hxℓ5 : 5 ≤ x.ℓ := by
        have : (5 : ℝ) ≤ x.ℓ := by rw [h2]; push_cast; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
        exact_mod_cast this
      have huL : u * x.ℓ ≤ 1 / 1000 := by nlinarith
      obtain ⟨hs1, hs2⟩ := hM.le_dec_eighNextParams_snd_mul x.R x.ε hu huL hτ₀ (by linarith) hx0
        (by linarith) (by linarith) hxℓ5 (by linarith)
      have hloss := mul_le_mul_of_nonneg_left
        (mul_le_mul hxℓ h3 hx0.le (by positivity)) (by positivity : (0 : ℝ) ≤ 3 * u)
      have r := ih z (fun a' => s (b :: a')) (j + 1) y (by omega) (by omega)
        (by rw [hzε]; linarith) (by
          rw [hzε, hzℓ]; push_cast at hs2 ⊢; nlinarith) hy
      rwa [show j + (b :: a).length = j + 1 + a.length by simp only [List.length_cons]; omega]
  have r := key a ⟨k, A, R₀, ε, ℓ⟩ s 0 y (by omega) rfl le_rfl (by simp) h
  rw [zero_add, hyℓ] at r
  rw [hyℓ]
  push_cast at r ⊢
  have hlen' : (a.length : ℝ) ≤ ℓ := by exact_mod_cast hlen
  have hd : (0 : ℝ) < ℓ + a.length - 1 := by linarith [(a.length.cast_nonneg : (0 : ℝ) ≤ _)]
  rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ hd]
  have h1 := mul_le_mul_of_nonneg_left hlen' (by positivity : 0 ≤ 6 * u * ℓ * dec ε)
  have h2 : 6 * u * ℓ * dec ε * ℓ ≤ 6 / 100 * dec ε := by nlinarith
  nlinarith

/-- The sizes of the two children of a node sum to at most its size. -/
private lemma sum_k_eighChild_le {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    {N signFuel : ℕ} {R₀ β : F} (x : EighNode F) (smp : EighSample Su Sg N) :
    (eighChild M N signFuel R₀ β x smp true).elim 0 EighNode.k +
      (eighChild M N signFuel R₀ β x smp false).elim 0 EighNode.k ≤ x.k := by
  unfold eighChild
  split
  · simp
  · rename_i b' _ _ _
    cases b' <;> simp
  · rename_i kp hkp _ _ _ _ _ _
    simp only [if_true, Option.elim_some, Bool.false_eq_true, if_false]
    omega

/-- **The sizes at one depth sum to at most the root size** (EB3'): for every machine, node
$x$, tree of samples and depth $j$, the sizes of the nodes at the paths of length $j$ sum to at
most $k_x$ (a node has no child, one child of its size, or two children of sizes $k_+$ and
$k - k_+$). [Shah2024, proof of Theorem 4.2], "$\sum_{x \in X_k} n_x \le n$".
Proof: induction on $j$ generalizing $x$ and the samples: split a path of length $j + 1$ by its
head (`Fin.consEquiv`, `List.ofFn_succ`, `Fintype.sum_prod_type`); `NLAlib.eighNodeAt` at
$b :: a$ is the node at $a$ below `NLAlib.eighChild` on side $b$; the induction hypothesis bounds
each side by its child's size (for its use in EV6' over the depths $j \le \ell$:
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params` gives $|a| \le \ell$ and $\ell_y = \ell +
|a|$); the children's sizes sum to at most $k_x$ by cases on
`NLAlib.eighStep` (`Nat.add_sub_cancel'`). L, about 120 lines (EB4's case analysis reused). -/
theorem sum_k_eighNodeAt_ofFn_le {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    {N signFuel : ℕ} {R₀ β : F} (x : EighNode F) (s : List Bool → EighSample Su Sg N) (j : ℕ) :
    ∑ a : Fin j → Bool,
      ((eighNodeAt M N signFuel R₀ β (List.ofFn a) x s).elim 0 EighNode.k) ≤ x.k := by
  induction j generalizing x s with
  | zero => simp [eighNodeAt]
  | succ j ih =>
    rw [← (Fin.consEquiv fun _ : Fin (j + 1) => Bool).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      eighNodeAt]
    have hb : ∀ b : Bool, ∑ a : Fin j → Bool,
        ((eighChild M N signFuel R₀ β x (s []) b).bind fun y =>
          eighNodeAt M N signFuel R₀ β (List.ofFn fun i => a i) y
            fun a' => s (b :: a')).elim 0 EighNode.k ≤
        (eighChild M N signFuel R₀ β x (s []) b).elim 0 EighNode.k := by
      intro b
      rcases eighChild M N signFuel R₀ β x (s []) b with _ | y
      · simp
      · exact ih y _
    exact (add_le_add (hb true) (hb false)).trans (sum_k_eighChild_le M x (s []))

/-- The global numeric consequences of the hypotheses of EB5': the depth counter is at least
$20$, the conditions of `NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params` hold, and
$n\beta \le \varepsilon/4000$. -/
private lemma eigh_global_bounds' {u τ Ω : ℝ} {μM : ℕ → ℝ} (hu : 0 ≤ u) (hμM : Monotone μM)
    (hμM₀ : 0 ≤ μM 0) {n : ℕ} (hn : 0 < n) {R₀ ε β θ : ℝ} (hR₀pos : 0 < R₀) (hε : 0 < ε)
    (hε₁ : ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ} (hℓ : bisectionDepth ε ≤ ℓ)
    (hβ : 0 < β)
    (hβle : β ≤ ((ℓ : ℝ) - 1) ^ 2 * ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * β)
    (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (ε * min R₀ 1))
    (hΩ : 16 * (2 * R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω) :
    20 ≤ ℓ ∧ 100 * ℓ ^ 2 * u ≤ 1 ∧ 100 * τ ≤ ε * min R₀ 1 ∧ 16 * (R₀ + ℓ) ≤ Ω ∧
      n * β ≤ ε / 4000 := by
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
  -- $n\beta \le \varepsilon / 4000$
  have hnβ : n * β ≤ ε / 4000 := by
    have hm1 : (1 : ℝ) ≤ min (n : ℝ) (ℓ + 1) := le_min hn' (by linarith)
    have he1 : (1 : ℝ) ≤ min (n : ℝ) (Real.exp 1) :=
      le_min hn' (by linarith [Real.add_one_le_exp (1 : ℝ)])
    have hP : √(n : ℝ) ≤ √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) := by
      refine Real.sqrt_le_sqrt ?_
      calc (n : ℝ) = n * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    have hT : 2 * √(n : ℝ) ≤ 2 * √2 * √(n : ℝ) +
        √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)) := by
      have : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
      nlinarith [Real.sqrt_nonneg (Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))]
    have hnn : (n : ℝ) = √(n : ℝ) * √(n : ℝ) := (Real.mul_self_sqrt (by positivity)).symm
    have hD : 52 * 39 * 2 * (n : ℝ) * ℓ ^ 2 ≤ 52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
        √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
        (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) := by
      have h39 : (39 : ℝ) ≤ 2 * ℓ - 1 := by linarith
      calc 52 * 39 * 2 * (n : ℝ) * ℓ ^ 2 =
          52 * (ℓ : ℝ) ^ 2 * 39 * √(n : ℝ) * (2 * √(n : ℝ)) := by
            linear_combination (52 * 39 * 2 * (ℓ : ℝ) ^ 2) * hnn
        _ ≤ _ := by gcongr
    have hnum : ((ℓ : ℝ) - 1) ^ 2 * ε * √θ ≤ ℓ ^ 2 * ε := by
      have h1 : ((ℓ : ℝ) - 1) ^ 2 ≤ ℓ ^ 2 := by nlinarith
      have h2 : √θ ≤ 1 := Real.sqrt_le_one.mpr hθ₁
      calc ((ℓ : ℝ) - 1) ^ 2 * ε * √θ ≤ ℓ ^ 2 * ε * 1 := by gcongr
        _ = _ := by ring
    rw [le_div_iff₀ (lt_of_lt_of_le (by positivity) hD)] at hβle
    have := mul_le_mul_of_nonneg_left hD hβ.le
    nlinarith
  have hβ₁ : β ≤ 1 := by
    have : β ≤ n * β := le_mul_of_one_le_left hβ.le hn'
    linarith [hε₁.trans (show (2⁻¹ : ℝ) ^ 15 ≤ 1 by norm_num)]
  have hu₁ : 100 * ℓ ^ 2 * u ≤ 1 := by
    have hμn : 0 ≤ μM n := hμM₀.trans (hμM (Nat.zero_le n))
    have hQ : 1460 * (ℓ : ℝ) ^ 2 ≤ 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) := by
      calc 1460 * (ℓ : ℝ) ^ 2 = 146 * 1 * ℓ * ℓ * 10 := by ring
        _ ≤ _ := by gcongr <;> linarith [Real.sqrt_nonneg (n : ℝ)]
    have hθβ : θ * β ≤ 1 := mul_le_one₀ hθ₁ hβ.le hβ₁
    have h0 : 0 ≤ (ℓ : ℝ) ^ 2 * u := by positivity
    linarith [mul_le_mul_of_nonneg_right hQ hu]
  have hτ' : 100 * τ ≤ ε * min R₀ 1 := by
    have : 100 * τ ≤ τ * (100 * n * √(n : ℝ)) := by
      have h1 : (1 : ℝ) ≤ n * √(n : ℝ) := one_le_mul_of_one_le_of_one_le hn' hs1
      linarith [mul_le_mul_of_nonneg_left h1 hτ₀]
    exact this.trans (hτ.trans (min_le_right _ _))
  have hΩ' : 16 * (R₀ + ℓ) ≤ Ω := by
    linarith [Real.sqrt_nonneg (Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)),
      Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg 2,
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (n : ℝ))]
  exact ⟨hℓ20, hu₁, hτ', hΩ', hnβ⟩

/-- The arithmetic core of the deflation tolerance of EB5': if $52Q\ell^2(2\ell - 1) \le
(\ell - 1)^2\varepsilon r$ then $2Q \le (1 - 2^{-8})(\ell - 1)\varepsilon s r/(20\ell^2)$ for
$s \ge 0.39$. -/
private lemma two_mul_le_of_mul_le {Q s r ℓ ε : ℝ} (hℓ : 20 ≤ ℓ) (hs : 39 / 100 ≤ s)
    (hr : 0 ≤ r) (hε : 0 < ε) (hQ : Q * (52 * ℓ ^ 2 * (2 * ℓ - 1)) ≤ (ℓ - 1) ^ 2 * ε * r) :
    2 * Q ≤ (1 - 2⁻¹ ^ 8) * (ℓ - 1) * ε / (20 * ℓ ^ 2) * (s * r) := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h3 : 40 * (ℓ - 1) ≤ (1 - 2⁻¹ ^ 8) * s * (52 * (2 * ℓ - 1)) := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3
    (by have : 0 ≤ ℓ - 1 := by linarith
        positivity : (0 : ℝ) ≤ (ℓ - 1) * ε * r)
  have h5 : 0 < 52 * (2 * ℓ - 1) := by linarith
  refine le_of_mul_le_mul_right ?_ h5
  nlinarith [h4, hQ]

/-- The singular value threshold of EB5' at a node of size $K$: with $\rho = \theta K/(6nm)$,
$5\theta/(32nm\min(n, e)) \le 15\rho/(16\min(K^2, eK)) \le 1$. -/
private lemma node_threshold_bounds {K n m e θ : ℝ} (hK2 : 2 ≤ K) (hKn : K ≤ n) (hm1 : 1 ≤ m)
    (he2 : 2 ≤ e) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) :
    5 * θ / (32 * (n * m * min n e)) ≤ 15 * (θ * K / (6 * n * m)) / (16 * min (K ^ 2) (e * K)) ∧
      15 * (θ * K / (6 * n * m)) / (16 * min (K ^ 2) (e * K)) ≤ 1 := by
  have hK0 : 0 < K := by linarith
  have hn0 : 0 < n := by linarith
  have hmin0 : 0 < min (K ^ 2) (e * K) := lt_min (by positivity) (by positivity)
  constructor
  · have h1 : min (K ^ 2) (e * K) ≤ K * min n e := by
      rw [mul_min_of_nonneg _ _ hK0.le]
      exact min_le_min (by rw [sq]; exact mul_le_mul_of_nonneg_left hKn hK0.le)
        (by rw [mul_comm])
    calc 5 * θ / (32 * (n * m * min n e)) = 15 * (θ * K / (6 * n * m)) / (16 * (K * min n e)) := by
          have : 0 < min n e := lt_min hn0 (by linarith)
          field_simp; ring
      _ ≤ _ := by gcongr
  · have h1 : 2 * K ≤ min (K ^ 2) (e * K) :=
      le_min (by rw [sq]; exact mul_le_mul_of_nonneg_right hK2 hK0.le)
        (mul_le_mul_of_nonneg_right he2 hK0.le)
    calc 15 * (θ * K / (6 * n * m)) / (16 * min (K ^ 2) (e * K)) ≤
          15 * (θ * K / (6 * n * m)) / (16 * (2 * K)) := by gcongr
      _ = 15 * θ / (192 * n * m) := by field_simp; ring
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [mul_le_mul (show (1 : ℝ) ≤ n by linarith) hm1 zero_le_one (by positivity)]

/-- The shift distance of EB5' at a node of window $R$: $w = 4\theta R/(9n\ell(\ell + 1)) \le R$,
and $w/(5R)$, $w/(2R)$ in closed form. -/
private lemma node_shift_bounds {θ R n ℓ : ℝ} (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hR : 0 < R)
    (hn : 1 ≤ n) (hℓ : 20 ≤ ℓ) :
    4 * θ * R / (9 * n * ℓ * (ℓ + 1)) ≤ R ∧
      4 * θ * R / (9 * n * ℓ * (ℓ + 1)) / (5 * R) = 4 * θ / (45 * n * ℓ * (ℓ + 1)) ∧
      4 * θ * R / (9 * n * ℓ * (ℓ + 1)) / (2 * R) = 2 * θ / (9 * n * ℓ * (ℓ + 1)) ∧
      θ / (12 * n * ℓ * (ℓ + 1)) ≤ |4 * θ * R / (9 * n * ℓ * (ℓ + 1)) / (5 * R)| := by
  have hD1 : (1 : ℝ) ≤ n * ℓ * (ℓ + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn (by linarith))
      (by linarith)
  have h5 : 4 * θ * R / (9 * n * ℓ * (ℓ + 1)) / (5 * R) = 4 * θ / (45 * n * ℓ * (ℓ + 1)) := by
    field_simp; ring
  refine ⟨?_, h5, by field_simp; ring, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hθ₁ hR.le, mul_le_mul_of_nonneg_left hD1 hR.le]
  · rw [h5, abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < θ * (n * ℓ * (ℓ + 1)) := by positivity
    linarith

/-- The deflation tolerance of EB5' at a node: with $t \le \hat T$, $x \ge \sqrt{5\theta/(32P)}$
and the accuracy bound on $\beta$, $2t\beta/x \le (1 - 1/L)\varepsilon_y/(5L)$. -/
private lemma node_defl_tol {ℓ L ε εy θ P T t x β : ℝ} (hℓ : 20 ≤ ℓ) (hL : ℓ ≤ L)
    (hL₂ : L ≤ 2 * ℓ) (hε : 0 < ε) (hεy : (1 - 2⁻¹ ^ 8) * ((ℓ - 1) / (L - 1)) * ε ≤ εy)
    (hθ : 0 < θ) (hP : 0 < P) (ht0 : 0 < t) (ht : t ≤ T) (hx : √(5 * θ / (32 * P)) ≤ x)
    (hβ : 0 ≤ β) (hβle : β ≤ (ℓ - 1) ^ 2 * ε * √θ / (52 * ℓ ^ 2 * (2 * ℓ - 1) * √P * T)) :
    2 * t / x * β ≤ (1 - 1 / L) * εy / (5 * L) := by
  have hc0 : 0 < √(5 * θ / (32 * P)) := Real.sqrt_pos.mpr (by positivity)
  have hT0 : 0 < T := ht0.trans_le ht
  have hcs : √(5 * θ / (32 * P)) = √(5 / 32) * (√θ / √P) := by
    rw [show 5 * θ / (32 * P) = 5 / 32 * (θ / P) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_div hθ.le]
  have hs : 39 / 100 ≤ √(5 / 32 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
  have hD : 0 < 52 * ℓ ^ 2 * (2 * ℓ - 1) * √P * T := by
    have : 0 < 2 * ℓ - 1 := by linarith
    positivity
  rw [le_div_iff₀ hD] at hβle
  have hL0 : 0 < L - 1 := by linarith
  have hLpos : 0 < L := by linarith
  calc 2 * t / x * β ≤ 2 * T / √(5 * θ / (32 * P)) * β := by gcongr
    _ ≤ (1 - 2⁻¹ ^ 8) * (ℓ - 1) * ε / (20 * ℓ ^ 2) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hc0, hcs]
      have hQ : T * β * (52 * ℓ ^ 2 * (2 * ℓ - 1)) ≤ (ℓ - 1) ^ 2 * ε * (√θ / √P) := by
        rw [mul_div_assoc', le_div_iff₀ (Real.sqrt_pos.mpr hP)]
        linarith
      linarith [two_mul_le_of_mul_le hℓ hs (by positivity) hε hQ]
    _ ≤ (1 - 2⁻¹ ^ 8) * (ℓ - 1) * ε / (5 * L ^ 2) :=
      div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hε.le)
        (by positivity) (by nlinarith)
    _ = (1 - 1 / L) / (5 * L) * ((1 - 2⁻¹ ^ 8) * ((ℓ - 1) / (L - 1)) * ε) := by
      field_simp
    _ ≤ (1 - 1 / L) / (5 * L) * εy := by
      refine mul_le_mul_of_nonneg_left hεy (div_nonneg ?_ (by positivity))
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    _ = (1 - 1 / L) * εy / (5 * L) := by ring

/-- The floor condition of EB5' at a node of size $K \le n$:
$4K^{3/2}\tau \le \min(x, \varepsilon_y R_0)$. -/
private lemma node_τ_le {τ K n m e θ x ε εy R₀ : ℝ} (hτ₀ : 0 ≤ τ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hm : 1 ≤ m) (he : 0 < e) (he4 : e ≤ 4) (hθ : 0 < θ)
    (hx : √(5 * θ / (32 * (n * m * min n e))) ≤ x)
    (hτ : τ * (100 * n * √n) ≤ min (√(θ / (8 * n * m))) (ε * min R₀ 1)) (hε : 0 < ε)
    (hεy : ε / 3 ≤ εy) (hR₀ : 0 < R₀) :
    τ * (4 * K * √K) ≤ min x (εy * R₀) := by
  have hn : 0 < n := by linarith
  have h0 : τ * (4 * K * √K) * 25 ≤ τ * (100 * n * √n) := by
    calc τ * (4 * K * √K) * 25 = τ * (100 * K * √K) := by ring
      _ ≤ _ := by gcongr
  have hsq : √(θ / (8 * n * m)) ≤ 25 * √(5 * θ / (32 * (n * m * min n e))) := by
    rw [show (25 : ℝ) = √(25 ^ 2) by rw [Real.sqrt_sq (by norm_num)],
      ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have h1 : 5 * θ / (128 * (n * m)) ≤ 5 * θ / (32 * (n * m * min n e)) := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      have := min_le_right n e
      nlinarith [mul_pos hn (by linarith : (0 : ℝ) < m)]
    have h2 : θ / (8 * n * m) ≤ 25 ^ 2 * (5 * θ / (128 * (n * m))) := by
      rw [show 25 ^ 2 * (5 * θ / (128 * (n * m))) = θ / (8 * n * m) * (3125 / 16) by
        field_simp; ring]
      exact le_mul_of_one_le_right (by positivity) (by norm_num)
    nlinarith
  have h3 : ε * min R₀ 1 ≤ ε * R₀ := by gcongr; exact min_le_left _ _
  have h4 := mul_le_mul_of_nonneg_right hεy hR₀.le
  have h5 := hτ.trans (min_le_left _ _)
  have h6 := hτ.trans (min_le_right _ _)
  exact le_min (by linarith) (by linarith [mul_pos hε hR₀])

/-- The Newton–Schulz step count of a node of EB5' is at most the global $N_*$, which is
nonnegative. -/
private lemma node_newtonSchulzSteps_le {n K ℓ θ R β ε : ℝ} (hn : 1 ≤ n) (hK2 : 2 ≤ K)
    (hKn : K ≤ n) (hℓ : 20 ≤ ℓ) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hR : 0 < R) (hβ : 0 < β)
    (hnβ : n * β ≤ ε / 4000) (hε₁ : ε ≤ 2⁻¹ ^ 15) :
    newtonSchulzSteps (4 * θ * R / (9 * n * ℓ * (ℓ + 1)) / (5 * R)) (β / (16 * K)) ≤
        newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (β / (16 * n)) ∧
      0 ≤ newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (β / (16 * n)) := by
  have hβ1 : β ≤ 1 := by
    linarith [le_mul_of_one_le_left hβ.le hn, show (2⁻¹ : ℝ) ^ 15 ≤ 1 by norm_num]
  have hβn : β / (16 * K) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hD1 : (1 : ℝ) ≤ n * ℓ * (ℓ + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn (by linarith))
      (by linarith)
  refine ⟨(newtonSchulzSteps_le_of_le_abs (by positivity)
    (node_shift_bounds hθ hθ₁ hR hn hℓ).2.2.2).trans
      (newtonSchulzSteps_le_of_le (by positivity) (by gcongr) hβn),
    newtonSchulzSteps_nonneg (by positivity) ?_ (by positivity) ?_⟩
  · rw [div_le_iff₀ (by positivity)]; linarith
  · exact (div_le_div_of_nonneg_left hβ.le (by positivity) (by linarith)).trans hβn

/-- A crude bound $e \le 4$, from $e^{-1/2} \ge 1/2$. -/
private lemma exp_one_le_four : Real.exp 1 ≤ 4 := by
  have h1 := Real.add_one_le_exp (-1 / 2 : ℝ)
  have h2 : Real.exp (-1) = Real.exp (-1 / 2) * Real.exp (-1 / 2) := by
    rw [← Real.exp_add]; norm_num
  have h3 : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have h4 : 1 / 4 ≤ Real.exp (-1) := by rw [h2]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h4 (Real.exp_pos 1).le]

/-- The precision budget `NLAlib.FloatMachine.IsEighNodeBudget` at an internal node of the tree
of `NLAlib.eigh`, with the parameters of EB5'. -/
private lemma isEighNodeBudget_of_node (hu : 0 ≤ u) (hμM : Monotone μM) (hμQ : Monotone μQ)
    (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN) {n : ℕ} {ε : F} {θ : ℝ}
    (hR₀pos : 0 < dec R₀) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1)
    {ℓ : ℕ} (hℓ : 20 ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * dec β)
    (hustop : 2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ dec β)
    (hudefl : 16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β)
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω)
    (hnβ : n * dec β ≤ dec ε / 4000)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hkn : y.k ≤ n) (hℓy : ℓ ≤ y.ℓ) (hℓy₂ : y.ℓ ≤ 2 * ℓ)
    (hεy : (1 - 2⁻¹ ^ 8) * (((ℓ : ℝ) - 1) / ((y.ℓ : ℝ) - 1)) * dec ε ≤ dec y.ε)
    (hεy3 : dec ε / 3 ≤ dec y.ε) (hεy' : dec y.ε ≤ dec ε) (hRy : dec y.R ≤ dec R₀)
    (hk : 2 ≤ y.k) (hRpos : 0 < dec y.R) :
    M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)))
      (√(15 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) /
        (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
      (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))))))
      y := by
  have hn : 0 < n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK2 : (2 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hKn : (y.k : ℝ) ≤ n := by exact_mod_cast hkn
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓy' : (ℓ : ℝ) ≤ y.ℓ := by exact_mod_cast hℓy
  have hℓy₂' : (y.ℓ : ℝ) ≤ 2 * ℓ := by exact_mod_cast hℓy₂
  have hm1 : (1 : ℝ) ≤ min (n : ℝ) (ℓ + 1) := le_min hn' (by linarith)
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hμMk : 0 ≤ μM y.k := hμM₀.trans (hμM (Nat.zero_le _))
  have hν : 4 * μM y.k + 10 + 10 * √(y.k : ℝ) ≤ 4 * μM n + 10 + 10 * √(n : ℝ) := by
    linarith [hμM hkn, Real.sqrt_le_sqrt hKn]
  obtain ⟨hXlow, hXup⟩ := node_threshold_bounds hK2 hKn hm1 he2 hθ hθ₁
  obtain ⟨hwR, -, hw2, -⟩ := node_shift_bounds hθ hθ₁ hRpos hn' hℓ'
  obtain ⟨hNy, hNst⟩ := node_newtonSchulzSteps_le hn' hK2 hKn hℓ' hθ hθ₁ hRpos hβ hnβ hε₁
  rw [← hN] at hNy hNst
  have hlog : Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1)))) ≤
      Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ) := by
    have h : 16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) =
        96 * n * min (n : ℝ) (ℓ + 1) / θ / y.k := by field_simp; ring
    rw [h]
    exact Real.log_le_log (by positivity) (div_le_self (by positivity) (by linarith))
  exact
  { nonneg_μM := hμMk
    nonneg_μQ := hμQ₀.trans (hμQ (Nat.zero_le _))
    nonneg_cN := hcN
    nonneg_u := hu
    isHermitian := hA
    specNorm_le := hR
    twenty_le := hℓ.trans hℓy
    pos_ε := by linarith
    ε_le := hεy'.trans (hε₁.trans (by norm_num))
    pos_R₀ := hR₀pos
    pos_w := by positivity
    w_le := hwR
    pos_x := Real.sqrt_pos.mpr ((by positivity : (0 : ℝ) < 5 * θ / (32 * (n * min (n : ℝ) (ℓ + 1) *
      min (n : ℝ) (Real.exp 1)))).trans_le hXlow)
    x_le := Real.sqrt_le_one.mpr hXup
    le_t := le_add_of_nonneg_right (Real.sqrt_nonneg _)
    pos_β := hβ
    defl_tol := node_defl_tol hℓ' hℓy' hℓy₂' hε hεy hθ (by positivity) (by positivity)
      (add_le_add (by gcongr) (Real.sqrt_le_sqrt hlog)) (Real.sqrt_le_sqrt hXlow) hβ.le hβle
    sign_tol := by
      rw [mul_div_assoc, hw2, show (1 - 2⁻¹ ^ 7) * (2 * θ / (9 * n * ℓ * (ℓ + 1))) * dec β =
        127 / 64 * (θ * dec β) / (9 * n * ℓ * (ℓ + 1)) by ring, le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hν hu)
        (by positivity : (0 : ℝ) ≤ n * ℓ * (ℓ + 1))
      linarith [mul_pos hθ hβ]
    stop_tol := by
      refine le_trans ?_ hustop
      have h1 : (y.k : ℝ) + newtonSchulzSteps (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)) /
          (5 * dec y.R)) (dec β / (16 * y.k)) + 1 ≤ n + Nst + 1 := by linarith
      have h2 := mul_le_mul h1 hν (by positivity) (by positivity)
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2048 * u)
      linarith
    defl_u := by
      refine le_trans ?_ hudefl
      have := hμQ hkn
      have := hμM hkn
      gcongr
    mul_β_le := by
      have := mul_le_mul_of_nonneg_right hKn hβ.le
      linarith [show (2⁻¹ : ℝ) ^ 15 / 4000 ≤ 1 / 57600 by norm_num]
    fuel := hNy.trans hfuel
    nonneg_τ := hτ₀
    τ_le := by
      exact node_τ_le hτ₀ (by linarith) hKn hm1 (Real.exp_pos 1) exp_one_le_four hθ
        (Real.sqrt_le_sqrt hXlow) hτ hε hεy3 hR₀pos
    Ω_le := by
      have := Real.sqrt_le_sqrt hlog
      have := Real.sqrt_le_sqrt hKn
      have : (2 : ℝ) * √2 * √(y.k : ℝ) ≤ 2 * √2 * √(n : ℝ) := by gcongr
      linarith }

/-- The child of the node at the path $a$ is the node at the path $a + [b]$. -/
private lemma eighNodeAt_append_singleton_eq_some' {F Su Sg : Type*} [Inhabited Sg]
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
    exact eighNodeAt_append_singleton_eq_some' a z _ hza h'

/-- **Global deterministic guarantee of spectral bisection, sharp budget** (EB5'): let the
machine meet `NLAlib.FloatMachine.IsAccurate` with $u \ge 0$, $\mu_{\mathrm{MM}}$,
$\mu_{\mathrm{QR}}$ monotone and nonnegative and $c_{\mathrm N} \ge 0$; let the stored
$\mathbf{A}$ have Hermitian decoding with $\|\mathbf{A}\|_2 \le R_0$, $R_0 > 0$,
$0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$, $\ell \ge$ `NLAlib.bisectionDepth`
$\varepsilon$, $m = \min(n, \ell + 1)$, $\hat T = 2\sqrt2\sqrt n + \sqrt{\log(96nm/\theta)}$,
$\nu = 4\mu_{\mathrm{MM}}(n) + 10 + 10\sqrt n$, the accuracy
$$0 < \beta \le \frac{(\ell - 1)^2\,\varepsilon\sqrt\theta}{52\,\ell^2(2\ell - 1)
\sqrt{n m \min(n, e)}\;\hat T} \,, \qquad
N_* = N\Bigl(\frac{\theta}{12n\ell(\ell + 1)}, \frac{\beta}{16n}\Bigr) \,,$$
$146\,n\ell(\ell + 1)\,\nu u \le \theta\beta$, $2048(n + N_* + 1)\nu u \le \beta$,
$16(4\mu_{\mathrm{QR}}(n) + 4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1)u \le \beta$,
at least $N_*$ sign steps, $0 \le \tau$, $100n^{3/2}\tau \le \min(\sqrt{\theta/(8nm)},
\varepsilon\min(R_0, 1))$ and $16(2R_0 + n + 2\ell + \hat T) \le \Omega$. If every internal node
$y$ has a good sample with $w_y = 4\theta R_y/(9n\ell(\ell + 1))$, $\rho_y = \theta k_y/(6nm)$,
$x_y = \sqrt{15\rho_y/(16\min(k_y^2, e k_y))}$ and $t_y = 2\sqrt2\sqrt{k_y} +
\sqrt{\log(16/\rho_y)}$, then `NLAlib.eigh` is an approximate diagonalization of $\mathbf{A}$
with residual $2\varepsilon R_0$ and singular values within $\varepsilon/3$ of $1$. [Shah2024,
Theorem 4.2], deterministic part.
Proof: EB5's induction over the tree with EB1' and EB1a' in place of EB1 and EB1a (the node
lemmas re-derive their smallness facts from the budget, not from
`NLAlib.mul_le_of_le_bisectionSignTol`; the $k^{3/2}uR$ conjunct is gone): at each node,
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params` (EB2a) and EB2a' give $k_y \le n$,
$\ell \le \ell_y \le 2\ell$, $\varepsilon_y \ge (1 - 2^{-8})(\ell -
1)\varepsilon/(2\ell - 1)$, $R_y \le R_0$; then `NLAlib.FloatMachine.IsEighNodeBudget` at
$(w_y, x_y, t_y)$: `defl_tol` since $x_y/t_y \ge \sqrt{5\theta/(32nm\min(n, e))}/\hat T$ and
$\eta_y \ge (1 - 2^{-8})(\ell - 1)^2\varepsilon/(10\ell^2(2\ell - 1))$; `sign_tol` from the
$146$-condition and monotone $\mu_{\mathrm{MM}}$; `fuel`, `stop_tol` by NS11/NS12 since
$w_y/(5R_y) \ge \theta/(12n\ell(\ell + 1))$; floor and range from the global ones. H, about 300
lines (EB5's skeleton reused). -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample'
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hμM : Monotone μM) (hμQ : Monotone μQ)
    (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian) {ε : F}
    {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * dec β)
    (hustop : 2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ dec β)
    (hudefl : 16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β)
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω)
    {s : List Bool → EighSample ℝ ℂ n}
    (hgood : ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → 2 ≤ y.k →
        M.le y.R (M.mul y.ε R₀) = false →
        IsEighGoodSample dec (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)))
          (√(15 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) /
            (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
          (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))))))
          y (s a)) :
    IsApproxDiagonalization (decodeMatrix dec A) (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β s).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β s).2 i)) (2 * dec ε * dec R₀) (dec ε / 3) := by
  have hκ₁ : dec ε / 3 ≤ 1 := by linarith [hε₁.trans (show (2⁻¹ : ℝ) ^ 15 ≤ 1 by norm_num)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hM.isApproxDiagonalization_eighAux_succ_of_leaf hA (by positivity) hκ₁
      (Or.inl ⟨Nat.zero_le 1, by positivity⟩)
  obtain ⟨hℓ20, hu₁, hτ', hΩ', hnβ⟩ := eigh_global_bounds' hu hμM hμM₀ hn hR₀pos hε hε₁ hθ hθ₁
    hℓ hβ hβle husign hτ₀ hτ hΩ
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
          linarith [Real.sqrt_nonneg (Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)),
            Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg 2])
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
      have hℓy₂ : y.ℓ ≤ 2 * ℓ := by omega
      have hεy₂ := hM.mul_le_dec_ε_of_eighNodeAt_eq_some hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ' hΩ' A s hy
      have hB := isEighNodeBudget_of_node (M := M) (signFuel := signFuel) hu hμM hμQ hμM₀ hμQ₀
        hcN hR₀pos hε hε₁ hθ hθ₁ hℓ20 hβ hβle hN husign hustop hudefl hfuel hτ₀ hτ hΩ hnβ hyA
        hyR hkn (by omega) hℓy₂ hεy₂ hεy hεy' hRy hleaf.1 hleaf.2
      have hg := hgood a y hy
      rw [← List.append_nil a] at hg
      refine hM.isApproxDiagonalization_eighAux_succ_of_isEighNodeBudget hB hg ?_
      intro b y' hy'
      obtain ⟨hA', hR'⟩ := hM.isHermitian_and_specNorm_le_of_isEighNodeBudget hB hg hy'
      simp only [List.append_nil] at hy'
      have h := ih (a ++ [b]) y' (eighNodeAt_append_singleton_eq_some' a _ s hy hy')
        (by simp only [List.length_append, List.length_singleton]; omega) hA' hR'
      have hs : (fun a'' => s (a ++ [b] ++ a'')) = fun a'' => s (a ++ b :: a'') := by
        funext a''
        simp
      rw [hs] at h
      exact h
  rw [show 2 * dec ε * dec R₀ = dec ε * (dec R₀ + dec R₀) by ring]
  exact key (ℓ + 1) [] _ rfl (by simp) hA hR₀

end NLAlib
