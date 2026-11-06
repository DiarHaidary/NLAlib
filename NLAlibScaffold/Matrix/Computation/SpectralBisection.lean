/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisection
public import NLAlibScaffold.Matrix.Computation.Deflation
public import NLAlibScaffold.Matrix.Computation.NewtonSchulzSign

/-!
# Deterministic analysis of randomized spectral bisection (scaffold)

Statements for `NLAlib/Matrix/Computation/SpectralBisection.lean` (stage HDIAG, wave W4, design
note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.8): the local guarantee of one
node of the machine algorithm, read through the decoding, given its good events and the
guarantees of its children ([Shah2024, Lemma 4.1]), the depth
of the recursion, the number of nodes and of splits, and the global deterministic guarantee: if
every internal node of the recursion tree has a good sample, the output is an approximate
diagonalization with residual $2\varepsilon R_0$ and singular values of $\mathbf{U}$ in
$[1 - \varepsilon/3, 1 + \varepsilon/3]$. The probability is in
`NLAlibScaffold/Eigensolvers/SpectralBisection.lean`.

## Main results

* `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le`: the computed
  projectors.
* `NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub`: rank recovery.
* `NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_eighStep_eq_split`:
  frames, deflated bases and compressions at a split.
* `NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some`: the child
  invariant.
* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`:
  Lemma 4.1.
* `NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`: the depth.
* `NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params`: the parameters of the nodes.
* `NLAlib.FloatMachine.IsAccurate.encard_eighNodeAt_ne_none_le`,
  `NLAlib.encard_eighNodeAt_isSplit_le`: the counts.
* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample`: the
  global deterministic guarantee.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib


private theorem abs_sub_le_of_isRoundingOf_eb1c {u τ Ω a z : ℝ} (h : IsRoundingOf u τ Ω a z)
    (ha : |a| ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) : |a - z| ≤ u * (|a| + τ) := by
  have hmax : max |a| τ ≤ |a| + τ := max_le (by linarith) (by linarith [abs_nonneg a])
  exact (h ha).trans (mul_le_mul_of_nonneg_left hmax hu)

private theorem newtonSchulzSteps_nonneg_eb1c {s ε : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1 / 2)
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 2) : 0 ≤ newtonSchulzSteps s ε := by
  have h₁ : 0 ≤ Real.logb 2 (min |s| (1 / 2))⁻¹ := by
    rw [abs_of_pos hs, min_eq_left hs₁]
    exact Real.logb_nonneg one_lt_two (one_le_inv₀ hs |>.mpr (by linarith))
  have h₂ : 0 ≤ Real.logb 2 (Real.logb 2 ε⁻¹) := by
    refine Real.logb_nonneg one_lt_two ?_
    rw [← Real.logb_self_eq_one one_lt_two]
    exact Real.logb_le_logb_of_le one_lt_two two_pos ((le_inv_comm₀ two_pos hε).mpr (by linarith))
  unfold newtonSchulzSteps
  linarith

private theorem exists_mem_spectrum_abs_sub_le_eb1c {k : ℕ} {X Y : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) {y : ℝ} (hy : y ∈ spectrum ℝ Y) :
    ∃ x ∈ spectrum ℝ X, |x - y| ≤ specNorm (X - Y) := by
  rw [hY.spectrum_eq_image_eigenvalue] at hy
  obtain ⟨j, hj, rfl⟩ := hy
  exact ⟨_, hX.eigenvalue_mem_spectrum hj, hX.abs_eigenvalue_sub_le hY j⟩

private theorem mem_spectrum_sub_smul_one_eb1c {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ} {c z : ℝ}
    (hz : z ∈ spectrum ℝ (X - c • (1 : Matrix (Fin k) (Fin k) ℂ))) :
    z + c ∈ spectrum ℝ X := by
  rw [spectrum.mem_iff] at hz ⊢
  have : algebraMap ℝ (Matrix (Fin k) (Fin k) ℂ) (z + c) - X =
      algebraMap ℝ (Matrix (Fin k) (Fin k) ℂ) z - (X - c • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
    simp only [Algebra.algebraMap_eq_smul_one, add_smul]
    abel
  rwa [this]

/-- Smallness facts at a node. -/
private theorem small_eb1c {u τ ρ w R ε β μ X : ℝ} {k ℓ : ℕ} (hk : 1 ≤ k)
    (hℓ : 20 ≤ ℓ) (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8) (hρ₁ : ρ ≤ 1) (hw : 0 < w)
    (hwR : w ≤ R) (hβ : 0 < β) (hβtol : β ≤ bisectionSignTol k ε ρ ℓ) (hμ : 0 ≤ μ) (hu : 0 ≤ u)
    (husign : 640 * k * √(k : ℝ) * (8 + μ) *
      (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) * u ≤ w / (4 * R) * β)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * k * √(k : ℝ)) ≤ min (√(ρ / 2)) X) :
    (k : ℝ) * β ≤ 1 / 57600 ∧ (k : ℝ) * τ ≤ 1 / 4 ∧
      k * √(k : ℝ) * u * R ≤ w * β / 20480 ∧ (ℓ : ℝ) * β ≤ 1 / 2880 ∧
      k * √(k : ℝ) * u ≤ β / 20480 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq1 : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hkk : (k : ℝ) ≤ k * √(k : ℝ) := le_mul_of_one_le_right (by linarith) hsq1
  have hR0 : 0 < R := hw.trans_le hwR
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hρ' : √ρ ≤ 1 := Real.sqrt_le_one.mpr hρ₁
  have hL := Real.sqrt_nonneg (2 * Real.log (4 / ρ))
  have hβk : β * (k * √(k : ℝ)) ≤ 1 / 57600 := by
    refine (mul_le_mul_of_nonneg_right hβtol (by positivity)).trans ?_
    unfold bisectionSignTol
    have hX : (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) ≤ 1 / 800 := by
      have : 1 / (ℓ : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith [div_pos one_pos (by linarith : (0 : ℝ) < ℓ)]
    have hX0 : 0 ≤ (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) := by
      have : 1 / (ℓ : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      exact div_nonneg (mul_nonneg (by linarith) hε.le) (by positivity)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h1 := mul_le_mul hX hρ' (Real.sqrt_nonneg _) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ k * √(k : ℝ))
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ k) hL]
  have hℓβ : (ℓ : ℝ) * β ≤ 1 / 2880 := by
    have hXℓ : (ℓ : ℝ) * ((1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ)) ≤ 1 / 40 := by
      have : (ℓ : ℝ) * ((1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ)) = (1 - 1 / (ℓ : ℝ)) * ε / 5 := by
        field_simp
      rw [this]
      have : 0 ≤ 1 / (ℓ : ℝ) := by positivity
      nlinarith
    have hX0 : 0 ≤ (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) := by
      have : 1 / (ℓ : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      exact div_nonneg (mul_nonneg (by linarith) hε.le) (by positivity)
    refine (mul_le_mul_of_nonneg_left hβtol (by positivity)).trans ?_
    unfold bisectionSignTol
    have hD : 72 ≤ 36 * (k : ℝ) * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ))) := by nlinarith
    rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
    have h1 := mul_le_mul hXℓ hρ' (Real.sqrt_nonneg _) (by norm_num)
    nlinarith
  have hNs := newtonSchulzSteps_nonneg_eb1c (s := w / (8 * R)) (ε := β / (16 * k))
    (by positivity) (by rw [div_le_iff₀ (by positivity)]; linarith) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  have h1 : 5120 * (k * √(k : ℝ)) * u ≤ 640 * k * √(k : ℝ) * (8 + μ) *
      (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) * u := by
    have := mul_le_mul (by linarith : (8 : ℝ) ≤ 8 + μ) (by linarith : (1 : ℝ) ≤
      newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) zero_le_one
      (by linarith)
    have h0 : 0 ≤ 640 * (k * √(k : ℝ)) * u := by positivity
    nlinarith
  have h2 := h1.trans husign
  have hw4 : w / (4 * R) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hku3 : k * √(k : ℝ) * u ≤ β / 20480 := by
    have := mul_le_mul_of_nonneg_right hw4 hβ.le
    linarith
  have hkuR : k * √(k : ℝ) * u * R ≤ w * β / 20480 := by
    have h3 := mul_le_mul_of_nonneg_right h2 hR0.le
    rw [show w / (4 * R) * β * R = w * β / 4 by field_simp] at h3
    linarith
  have hkβ : (k : ℝ) * β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_left hkk hβ.le]
  have hkτ : (k : ℝ) * τ ≤ 1 / 4 := by
    have : √(ρ / 2) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    have := hτ.trans (min_le_left _ _)
    linarith [mul_le_mul_of_nonneg_right hkk hτ₀]
  exact ⟨hkβ, hkτ, hkuR, hℓβ, hku3⟩

private theorem scale_eb1c {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 1000)
    (hτ₀ : 0 ≤ τ) {k : ℕ} (hk1 : (1 : ℝ) ≤ k) (hkτ : (k : ℝ) * τ ≤ 1 / 4) (hΩ : 4 ≤ Ω)
    {Z : Matrix (Fin k) (Fin k) (F × F)} (hZ : (decodeMatrix dec Z).IsHermitian)
    {Y : Matrix (Fin k) (Fin k) ℂ} (hY : specNorm Y ≤ 2) {δ : ℝ}
    (hδ : specNorm (decodeMatrix dec Z - Y) ≤ δ) (hδ1 : δ ≤ 1) :
    specNorm (decodeMatrix dec (M.hermScale Z (M.ofNat 2)) - (2⁻¹ : ℝ) • Y) ≤
      δ / 2 + u * (2 * √(k : ℝ) + 4) := by
  have hτ1 : τ ≤ 1 / 4 := by nlinarith
  have h2 := abs_le.mp (abs_sub_le_of_isRoundingOf_eb1c (hM.ofNat 2)
    (by norm_num; linarith) hu hτ₀)
  push_cast at h2
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
  have hs := hM.specNorm_sub_decodeMatrix_hermScale_le hu hτ₀ hZ (c := M.ofNat 2)
  set t := dec (M.ofNat 2) with ht
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  have ht1 : 2 - 3 * u ≤ t ∧ t ≤ 2 + 3 * u := by constructor <;> nlinarith
  have ht0 : 0 < t := by linarith
  set Zd := decodeMatrix dec Z
  have hZn : specNorm Zd ≤ 3 := by
    have := specNorm_add_le (Zd - Y) Y
    rw [sub_add_cancel] at this
    linarith
  have hZs : specNorm (t⁻¹ • Zd) ≤ 2 := by
    rw [specNorm_real_smul, abs_of_pos (inv_pos.mpr ht0), inv_mul_le_iff₀ ht0]
    linarith
  have hs1 := hs ht0.ne' (by rw [abs_of_pos ht0, div_le_iff₀ ht0]; nlinarith)
  have hs' : specNorm (t⁻¹ • Zd - decodeMatrix dec (M.hermScale Z (M.ofNat 2))) ≤
      u * (2 * √(k : ℝ) + 1 / 2) := by
    refine hs1.trans ?_
    have := mul_le_mul_of_nonneg_left hZs (Real.sqrt_nonneg (k : ℝ))
    nlinarith
  have hinv : |t⁻¹ - 2⁻¹| ≤ u := by
    rw [inv_sub_inv ht0.ne' two_ne_zero, abs_div, abs_of_pos (mul_pos ht0 two_pos),
      div_le_iff₀ (mul_pos ht0 two_pos), abs_le]
    constructor <;> nlinarith
  have hmid : specNorm (t⁻¹ • Zd - (2⁻¹ : ℝ) • Y) ≤ 3 * u + δ / 2 := by
    have heq : t⁻¹ • Zd - (2⁻¹ : ℝ) • Y = (t⁻¹ - 2⁻¹) • Zd + (2⁻¹ : ℝ) • (Zd - Y) := by
      module
    rw [heq]
    refine (specNorm_add_le _ _).trans ?_
    rw [specNorm_real_smul, specNorm_real_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    have := mul_le_mul hinv hZn (specNorm_nonneg _) hu
    linarith
  have heq2 : decodeMatrix dec (M.hermScale Z (M.ofNat 2)) - (2⁻¹ : ℝ) • Y =
      (t⁻¹ • Zd - (2⁻¹ : ℝ) • Y) -
        (t⁻¹ • Zd - decodeMatrix dec (M.hermScale Z (M.ofNat 2))) := by
    abel
  rw [heq2]
  refine (specNorm_sub_le _ _).trans ?_
  linarith

private theorem scal_eb1c {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hu : 0 ≤ u)
    (_hA : (decodeMatrix dec y.A).IsHermitian) (_hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8) (hR₀ : 0 < dec R₀)
    (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (_hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    (hint : M.le y.R (M.mul y.ε R₀) = false)
    {smp : EighSample ℝ ℂ N} (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (_hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|)
    (hk : 1 ≤ y.k) :
    |dec (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1) - dec y.R / y.ℓ * smp.1| ≤ 2 * u * dec y.R ∧
      |dec (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1)| ≤ dec y.R / 10 ∧
      |dec y.R / y.ℓ * smp.1| ≤ dec y.R / 20 ∧
      2 * dec y.R - 7 * u * dec y.R ≤ dec (M.mul (M.ofNat 2) y.R) ∧
      dec (M.mul (M.ofNat 2) y.R) ≤ 2 * dec y.R + 7 * u * dec y.R ∧
      τ ≤ dec y.R / 2 ∧ u * dec y.R ≤ w * dec β / 20480 ∧ u ≤ 1 / 1000000 ∧
      dec β ≤ 1 / 57600 ∧ (y.k : ℝ) * τ ≤ 1 / 4 := by
  obtain ⟨hkβ, hkτ, hkuR, hℓβ, hku3⟩ :=
    small_eb1c hk hℓ hε hε₁ hρ₁ hw hwR hβ hβtol hμM hu husign hτ₀ hτ
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hsq1 : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hkk : (1 : ℝ) ≤ y.k * √(y.k : ℝ) := by nlinarith
  have hR0 : 0 < dec y.R := hw.trans_le hwR
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) < y.ℓ := by linarith
  have huR : u * dec y.R ≤ w * dec β / 20480 := by
    have := mul_le_mul_of_nonneg_right hkk (mul_nonneg hu hR0.le)
    nlinarith
  have hβ1 : dec β ≤ 1 / 57600 := by nlinarith
  have huβ : u ≤ dec β / 20480 := by
    have := mul_le_mul_of_nonneg_right hkk hu
    linarith
  have huℓ : u * y.ℓ ≤ 1 / 1000 := by
    have := mul_le_mul_of_nonneg_right huβ (by linarith : (0 : ℝ) ≤ y.ℓ)
    linarith
  have hu1 : u ≤ 1 / 1000000 := by linarith
  have huw : u * w ≤ u * dec y.R := mul_le_mul_of_nonneg_left hwR hu
  have hwβ : w * dec β ≤ w * (1 / 57600) := mul_le_mul_of_nonneg_left hβ1 hw.le
  have hτ1 : τ ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_right hk1 hτ₀]
  have hsqL := Real.sqrt_nonneg (Real.log (4 / ρ))
  have hk0 : (0 : ℝ) ≤ y.k := by linarith
  have hΩR : 16 * dec y.R ≤ Ω := by linarith
  have hΩℓ : 16 * (y.ℓ : ℝ) ≤ Ω := by linarith
  have hΩR₀ : 16 * dec R₀ ≤ Ω := by linarith
  have hΩk : 16 * (y.k : ℝ) + 320 ≤ Ω := by linarith
  -- the window is above the floor
  have hτR : τ ≤ dec y.R / 2 := by
    have h4 : 4 * τ ≤ dec y.ε * dec R₀ := by
      have := hτ.trans (min_le_right _ _)
      linarith [mul_le_mul_of_nonneg_left hkk hτ₀]
    have hεR : 0 < dec y.ε * dec R₀ := mul_pos hε hR₀
    have hεR8 := mul_le_mul_of_nonneg_right hε₁ hR₀.le
    have hm := (hM.mul y.ε R₀) (by rw [abs_of_pos hεR]; linarith)
    rw [abs_of_pos hεR, max_eq_left (by linarith)] at hm
    have hm' := (abs_le.mp hm).2
    have hlt : dec (M.mul y.ε R₀) < dec y.R := by
      by_contra h
      have := (hM.le_iff _ _).mpr (not_lt.mp h)
      rw [hint] at this
      exact Bool.false_ne_true this
    have := mul_le_mul_of_nonneg_right hu1 hεR.le
    linarith
  -- the stored scale `b = fl(fl(2) R)`
  have hΩ2 : |((2 : ℕ) : ℝ)| ≤ Ω := by norm_num; linarith only [hΩk, hk0]
  have h2 := abs_le.mp (abs_sub_le_of_isRoundingOf_eb1c (hM.ofNat 2) hΩ2 hu hτ₀)
  push_cast at h2
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
  have hbr := abs_sub_le_of_isRoundingOf_eb1c (hM.mul (M.ofNat 2) y.R)
  set t := dec (M.ofNat 2) with ht
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  have ht1 : 2 - 3 * u ≤ t ∧ t ≤ 2 + 3 * u := by constructor <;> linarith
  have htR0 : 0 ≤ t * dec y.R := mul_nonneg (by linarith) hR0.le
  have htR : t * dec y.R ≤ 3 * dec y.R := by
    have := mul_le_mul_of_nonneg_right (by linarith : t ≤ 3) hR0.le
    linarith
  have hbr' := abs_le.mp (hbr (by rw [abs_of_nonneg htR0]; linarith) hu hτ₀)
  rw [abs_of_nonneg htR0] at hbr'
  set b := dec (M.mul (M.ofNat 2) y.R) with hb
  have hb1 : 2 * dec y.R - 7 * u * dec y.R ≤ b ∧ b ≤ 2 * dec y.R + 7 * u * dec y.R := by
    have e1 := mul_le_mul_of_nonneg_left htR hu
    have e2 := mul_le_mul_of_nonneg_left hτR hu
    have e3 := mul_le_mul_of_nonneg_right ht1.1 hR0.le
    have e4 := mul_le_mul_of_nonneg_right ht1.2 hR0.le
    constructor <;> linarith
  have hb0 : 0 < b := by linarith
  -- the rounded `ℓ`, scale and shift
  have hLr := (hM.ofNat y.ℓ) (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; linarith)
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (y.ℓ : ℝ) from Nat.cast_nonneg _),
    max_eq_left (by linarith : τ ≤ (y.ℓ : ℝ))] at hLr
  have hLr' := abs_le.mp hLr
  have hL1 : 19 ≤ dec (M.ofNat y.ℓ) := by linarith
  have hL0 : 0 < dec (M.ofNat y.ℓ) := by linarith
  have hq10 : dec y.R / dec (M.ofNat y.ℓ) ≤ dec y.R / 19 :=
    div_le_div_of_nonneg_left hR0.le (by norm_num) hL1
  have hq0 : 0 ≤ dec y.R / dec (M.ofNat y.ℓ) := div_nonneg hR0.le hL0.le
  have hsr := abs_sub_le_of_isRoundingOf_eb1c (hM.div y.R (M.ofNat y.ℓ) hL0.ne')
    (by rw [abs_of_nonneg hq0]; linarith) hu hτ₀
  rw [abs_of_nonneg hq0] at hsr
  set L := dec (M.ofNat y.ℓ) with hL
  set q := dec y.R / L with hq
  set s := dec (M.div y.R (M.ofNat y.ℓ)) with hs
  clear_value s q L
  have hqL : q * L = dec y.R := by rw [hq]; exact div_mul_cancel₀ _ hL0.ne'
  have hqd : |q - dec y.R / y.ℓ| ≤ u * q := by
    have : q - dec y.R / y.ℓ = q * (y.ℓ - L) / y.ℓ := by
      rw [← hqL]; field_simp
    rw [this, abs_div, abs_mul, abs_of_nonneg hq0, abs_of_pos hℓ0, div_le_iff₀ hℓ0]
    have := mul_le_mul_of_nonneg_left hLr hq0
    linarith
  have hsbd : |s - dec y.R / y.ℓ| ≤ u * dec y.R * (7 / 10) := by
    have e1 := abs_sub_le s q (dec y.R / y.ℓ)
    rw [abs_sub_comm s q] at e1
    have e2 := mul_le_mul_of_nonneg_left hq10 hu
    have e3 := mul_le_mul_of_nonneg_left hτR hu
    linarith [mul_nonneg hu hR0.le]
  have hRℓ : u * dec y.R ≤ dec y.R / y.ℓ := by
    rw [le_div_iff₀ hℓ0]
    linarith [mul_le_mul_of_nonneg_left huℓ hR0.le]
  have hRℓ2 : dec y.R / y.ℓ ≤ dec y.R / 20 :=
    div_le_div_of_nonneg_left hR0.le (by norm_num) hℓ'
  have hsbd' := abs_le.mp hsbd
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ dec y.R / 10 := by linarith
  obtain ⟨hc1, hc2⟩ := hM.isUnifSampler (M.div y.R (M.ofNat y.ℓ)) smp.1 (by rw [← hs]; exact hs0) hv
  rw [← hs] at hc1 hc2
  set c := dec (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1) with hc
  set cp := dec y.R / y.ℓ * smp.1 with hcp
  have hv' : |smp.1| ≤ 1 := abs_le.mpr ⟨hv.1, hv.2⟩
  have hcc : |c - cp| ≤ 2 * u * dec y.R := by
    have hmx : max s τ ≤ s + τ := max_le (by linarith) (by linarith)
    have e1 := abs_le.mp (hc2.trans (mul_le_mul_of_nonneg_left hmx hu))
    have e2 : |(s - dec y.R / y.ℓ) * smp.1| ≤ |s - dec y.R / y.ℓ| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hv'
    have e3 := abs_le.mp (e2.trans hsbd)
    have e4 := mul_le_mul_of_nonneg_left hs1 hu
    have e5 := mul_le_mul_of_nonneg_left hτR hu
    have e6 := mul_nonneg hu hR0.le
    rw [abs_le, hcp]
    constructor <;> linarith only [e1, e3, e4, e5, e6]
  have hcpR : |cp| ≤ dec y.R / 20 := by
    rw [hcp, abs_mul, abs_of_nonneg (div_nonneg hR0.le hℓ0.le)]
    exact (mul_le_of_le_one_right (div_nonneg hR0.le hℓ0.le) hv').trans hRℓ2
  exact ⟨hcc, hc1.trans hs1, hcpR, hb1.1, hb1.2, hτR, huR, hu1, hβ1, hkτ⟩

set_option maxHeartbeats 1000000 in
-- long `nlinarith` chains on the rounding budget
private theorem sign_eb1c {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
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
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|)
    (hk : 1 ≤ y.k) :
    specNorm (cfc Real.sign (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) -
      decodeMatrix dec (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
        (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1)))) ≤
      dec β + dec β / 2000 := by
  obtain ⟨hcc, hcR, hcpR, hb1l, hb1u, hτR, huR, hu1, hβ1, hkτ⟩ :=
    scal_eb1c hM hμM hu hA hR hℓ hε hε₁ hR₀ hρ₁ hw hwR hβ hβtol husign hfuel hτ₀ hτ hΩ hint hv hI hk
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hR0 : 0 < dec y.R := hw.trans_le hwR
  have huw : u * w ≤ u * dec y.R := mul_le_mul_of_nonneg_left hwR hu
  have hwβ : w * dec β ≤ w * (1 / 57600) := mul_le_mul_of_nonneg_left hβ1 hw.le
  have hτ1 : τ ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_right hk1 hτ₀]
  have hsqL := Real.sqrt_nonneg (Real.log (4 / ρ))
  have hk0 : (0 : ℝ) ≤ y.k := by linarith
  have hΩR : 16 * dec y.R ≤ Ω := by linarith
  have hΩk : 16 * (y.k : ℝ) + 320 ≤ Ω := by
    have : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hℓ
    linarith
  have hb1 := And.intro hb1l hb1u
  set b := dec (M.mul (M.ofNat 2) y.R) with hb
  have hb0 : 0 < b := by linarith
  set c := dec (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1) with hc
  set cp := dec y.R / y.ℓ * smp.1 with hcp
  -- the stored shifted matrix
  set Ad := decodeMatrix dec y.A
  set I := (1 : Matrix (Fin y.k) (Fin y.k) ℂ)
  have hI1 : specNorm I ≤ 1 := specNorm_one_le
  have hAc : specNorm (Ad - c • I) ≤ dec y.R * (11 / 10) := by
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_real_smul]
    have := mul_le_mul hcR hI1 (specNorm_nonneg _) (by positivity)
    linarith
  have hsh := hM.specNorm_sub_decodeMatrix_hermShift_le hu hA
    (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1) (le_trans hAc (by linarith))
  rw [← hc] at hsh
  set X := M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1) with hX
  set Xd := decodeMatrix dec X
  have hsh' : specNorm ((Ad - c • I) - Xd) ≤ u * (dec y.R * (11 / 10)) :=
    hsh.trans (mul_le_mul_of_nonneg_left (max_le hAc (by linarith)) hu)
  have he : specNorm ((Ad - cp • I) - Xd) ≤ 4 * u * dec y.R := by
    have heq : (Ad - cp • I) - Xd = ((Ad - c • I) - Xd) + (c - cp) • I := by
      rw [sub_smul]; abel
    rw [heq]
    refine (specNorm_add_le _ _).trans ?_
    rw [specNorm_real_smul]
    have := mul_le_mul hcc hI1 (specNorm_nonneg _) (by positivity)
    linarith
  have hXh : Xd.IsHermitian := by
    unfold Xd; rw [hX]; unfold FloatMachine.hermShift
    exact hM.isHermitian_decodeMatrix_hermFrom _ _
  have hAcp : (Ad - cp • I).IsHermitian := by
    refine hA.sub ?_
    unfold Matrix.IsHermitian
    simp only [I, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]
  have hspecA : ∀ z ∈ spectrum ℝ (Ad - cp • I), w ≤ |z| := fun z hz => by
    have := hI _ (mem_spectrum_sub_smul_one_eb1c hz)
    rwa [add_sub_cancel_right] at this
  set a := w / 2 + 2 * u * w with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have hspecX : ∀ x ∈ spectrum ℝ Xd, a ≤ |x| := fun x hx => by
    obtain ⟨z, hz, hzx⟩ := exists_mem_spectrum_abs_sub_le_eb1c hAcp hXh hx
    have := hspecA z hz
    have := abs_sub_abs_le_abs_sub z x
    rw [ha]
    linarith
  have hbX : specNorm Xd ≤ b := by
    have hAcpn : specNorm (Ad - cp • I) ≤ dec y.R + dec y.R / 20 := by
      refine (specNorm_sub_le _ _).trans ?_
      rw [specNorm_real_smul]
      have := mul_le_mul hcpR hI1 (specNorm_nonneg _) (by positivity)
      linarith
    have := specNorm_sub_le (Ad - cp • I) ((Ad - cp • I) - Xd)
    rw [sub_sub_cancel] at this
    linarith
  have huwR : 0 ≤ u * w * dec y.R := by positivity
  have hwb := mul_le_mul_of_nonneg_left hb1.2 hw.le
  have hN : newtonSchulzSteps (a / (2 * b)) (dec β / (16 * y.k)) ≤
      newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) := by
    refine newtonSchulzSteps_le_of_le_abs (by positivity) ?_
    rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity), ha]
    linarith
  have hab : w / (4 * dec y.R) ≤ a / b := by
    rw [div_le_div_iff₀ (by positivity) hb0, ha]
    linarith
  have hC : 0 ≤ 640 * (y.k : ℝ) * √(y.k : ℝ) * (8 + μM y.k) := by
    have : (0 : ℝ) ≤ 8 + μM y.k := by linarith
    positivity
  have huSN : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (a / (2 * b)) (dec β / (16 * y.k)) + 1) * u ≤ a / b * dec β :=
    calc _ ≤ 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
          (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC) hu
      _ ≤ w / (4 * dec y.R) * dec β := husign
      _ ≤ a / b * dec β := mul_le_mul_of_nonneg_right hab hβ.le
  have hSN := hM.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le hμM hu hτ₀
    (by nlinarith) (by linarith) hXh ha0 hspecX hbX hβ (by linarith) huSN
    (N := signFuel) (hN.trans hfuel)
  have hmove := Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le hAcp hXh hw hspecA
  have hmove' : 2 * specNorm ((Ad - cp • I) - Xd) / w ≤ dec β / 2000 := by
    rw [div_le_iff₀ hw]
    linarith
  have := specNorm_add_le (cfc Real.sign (Ad - cp • I) - cfc Real.sign Xd)
    (cfc Real.sign Xd - decodeMatrix dec (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R)
      signFuel X))
  rw [sub_add_sub_cancel] at this
  linarith

/-- The projector bound of
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le` when the leaf test
fails (`hint`): then the floor $\tau$ is below $R/2$, so every rounding is relative. Without
`hint` the window $R$ can lie far below $u\tau$ and the bound fails. -/
private theorem FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le_of_le_eq_false
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
  have hk : 1 ≤ y.k := by
    rcases Nat.eq_zero_or_pos y.k with h | h
    · exfalso
      rw [h] at hβtol
      simp [bisectionSignTol] at hβtol
      linarith
    · exact h
  obtain ⟨hkβ, hkτ, -, -, hku3⟩ :=
    small_eb1c hk hℓ hε hε₁ hρ₁ hw hwR hβ hβtol hμM hu husign hτ₀ hτ
  have hSB := sign_eb1c hM hμM hu hA hR hℓ hε hε₁ hR₀ hρ₁ hw hwR hβ hβtol husign hfuel hτ₀ hτ
    hΩ hint hv hI hk
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hksq : √(y.k : ℝ) ≤ y.k * √(y.k : ℝ) := le_mul_of_one_le_left (by positivity) hk1
  have huk : u * √(y.k : ℝ) ≤ dec β / 20480 := by
    linarith [mul_le_mul_of_nonneg_left hksq hu]
  have hsq1 : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr hk1
  have huβ : u ≤ dec β / 20480 := by linarith [mul_le_mul_of_nonneg_left hsq1 hu]
  have hβ1 : dec β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  have hu1 : u ≤ 1 / 1000 := by linarith
  have hτ1 : τ ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_right hk1 hτ₀]
  have hΩ4 : 4 ≤ Ω := by
    have := Real.sqrt_nonneg (Real.log (4 / ρ))
    have : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hℓ
    have : 0 < dec y.R := hw.trans_le hwR
    linarith
  have hBh := hM.isHermitian_decodeMatrix_newtonSchulzSign β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))
  set B := newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1)) with hB
  set S := cfc Real.sign (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) with hSdef
  set Bd := decodeMatrix dec B with hBd
  have hS : specNorm S ≤ 1 := by
    refine Matrix.IsHermitian.specNorm_cfc_le (hA.sub ?_) zero_le_one fun x _ => ?_
    · unfold Matrix.IsHermitian
      simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]
    · rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num
  have hBn : specNorm Bd ≤ 2 := by
    have := specNorm_sub_le S (S - Bd)
    rw [sub_sub_cancel] at this
    linarith
  have hBS : specNorm (Bd - S) ≤ dec β + dec β / 2000 := by
    rw [specNorm_sub_comm]; exact hSB
  have hI1 : specNorm (1 : Matrix (Fin y.k) (Fin y.k) ℂ) ≤ 1 := specNorm_one_le
  have hY1 : specNorm (1 + S) ≤ 2 := (specNorm_add_le _ _).trans (by linarith)
  have hY2 : specNorm (1 - S) ≤ 2 := (specNorm_sub_le _ _).trans (by linarith)
  have hδ1 : dec β + dec β / 2000 + 3 * u ≤ 1 := by linarith
  have hfin : (dec β + dec β / 2000 + 3 * u) / 2 + u * (2 * √(y.k : ℝ) + 4) ≤ dec β := by
    linarith
  have hBm : specNorm (Bd - -1) ≤ 3 := by
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_neg]
    linarith
  have hBp : specNorm (Bd - 1) ≤ 3 := by
    refine (specNorm_sub_le _ _).trans ?_
    linarith
  constructor
  · have hsh := hM.specNorm_sub_decodeMatrix_hermShift_le hu hBh (M.neg M.one) (by
      rw [hM.dec_neg, hM.dec_one, neg_one_smul]
      linarith)
    rw [hM.dec_neg, hM.dec_one, neg_one_smul] at hsh
    have hsh' := hsh.trans (mul_le_mul_of_nonneg_left (max_le hBm (by linarith)) hu)
    have hZ : (decodeMatrix dec (M.hermShift B (M.neg M.one))).IsHermitian := by
      unfold FloatMachine.hermShift; exact hM.isHermitian_decodeMatrix_hermFrom _ _
    have hZY : specNorm (decodeMatrix dec (M.hermShift B (M.neg M.one)) - (1 + S)) ≤
        dec β + dec β / 2000 + 3 * u := by
      have heq : decodeMatrix dec (M.hermShift B (M.neg M.one)) - (1 + S) =
          (Bd - S) - ((Bd - -1) - decodeMatrix dec (M.hermShift B (M.neg M.one))) := by
        abel
      rw [heq]
      refine (specNorm_sub_le _ _).trans ?_
      linarith
    exact (scale_eb1c hM hu hu1 hτ₀ hk1 hkτ hΩ4 hZ hY1 hZY hδ1).trans hfin
  · have hsh := hM.specNorm_sub_decodeMatrix_hermShift_le hu hBh M.one (by
      rw [hM.dec_one, one_smul]
      linarith)
    rw [hM.dec_one, one_smul] at hsh
    have hsh' := hsh.trans (mul_le_mul_of_nonneg_left (max_le hBp (by linarith)) hu)
    have hW : (decodeMatrix dec (M.hermShift B M.one)).IsHermitian := by
      unfold FloatMachine.hermShift; exact hM.isHermitian_decodeMatrix_hermFrom _ _
    have hZ : (decodeMatrix dec (M.negMat (M.hermShift B M.one))).IsHermitian := by
      rw [hM.decodeMatrix_negMat]; exact hW.neg
    have hZY : specNorm (decodeMatrix dec (M.negMat (M.hermShift B M.one)) - (1 - S)) ≤
        dec β + dec β / 2000 + 3 * u := by
      rw [hM.decodeMatrix_negMat]
      have heq : -decodeMatrix dec (M.hermShift B M.one) - (1 - S) =
          ((Bd - 1) - decodeMatrix dec (M.hermShift B M.one)) - (Bd - S) := by
        abel
      rw [heq]
      refine (specNorm_sub_le _ _).trans ?_
      linarith
    exact (scale_eb1c hM hu hu1 hτ₀ hk1 hkτ hΩ4 hZ hY2 hZY hδ1).trans hfin

/-- **The computed spectral projectors are accurate on Event I**: under the node hypotheses of
`NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub` (without the leaf test
and the size condition), for a seed $v \in [-1, 1]$ whose ideal shift $c' = (R/\ell)v$ is at
distance at least $w$ from every eigenvalue of $\mathbf{A}$, the stored projectors of
`NLAlib.eighStep`, $\mathbf{P}_+ = (\mathbf{B} + \mathbf{I})/2$ and $\mathbf{P}_- =
-(\mathbf{B} - \mathbf{I})/2$ with $\mathbf{B}$ the Newton–Schulz sign of the stored shifted
matrix, are within $\beta$ of $\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} -
c'\mathbf{I}))$. [Shah2024, proof of Lemma 4.1], (4.4)–(4.9).
Proof: the stored shift $c = \mathrm{unif}(\mathrm{fl}(R/\mathrm{fl}(\ell)), v)$ has
$|c - c'| \le 0.15uR + 2u\tau \le 0.33uR$ ($\tau \le \sqrt{\rho/2}/(4k^{3/2}) \le 1/16$ and
$\tau \le \varepsilon R_0/(4k^{3/2})$, so $\mathrm{fl}(\ell)$ is a relative rounding), and
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_le` adds $1.051uR$: the stored
shifted matrix is within $1.4uR$ of $\mathbf{A} - c'\mathbf{I}$, whose eigenvalues have modulus
$\ge w$; by Weyl (`Matrix.IsHermitian.abs_eigenvalue_sub_le`) its eigenvalues have modulus
$\ge a := w - 1.4uR$. Apply
`NLAlib.FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le` with this
$a$ and $b' = \mathrm{fl}(2R) \in [2R(1 - u), 2R(1 + u)]$: $a/b' \ge w/(4R)$ and
$N(a/(2b'), \beta/(16k)) \le N(w/(8R), \beta/(16k))$ (`NLAlib.newtonSchulzSteps_le_of_le_abs`), so
`husign` and `hfuel` give its hypotheses with a factor-2 margin; the modulus $w/2$ would not.
`Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le` moves the sign from the stored to the ideal
shift ($2.8uR/w$); the shift by $\mp1$ and the division by $\mathrm{fl}(2)$ cost
$1.05u + 1.01u\sqrt k + 2ku\tau$
(`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_le`,
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermScale_le`,
`NLAlib.FloatMachine.IsAccurate.decodeMatrix_negMat`). Total $\le \beta/2 + 2.8uR/w + 1.05u +
1.01u\sqrt k + 2ku\tau \le 0.51\beta$. M, about 100 lines. -/
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
  sorry

private theorem abs_sub_le_of_isRoundingOf_aux {u τ Ω a z : ℝ} (h : IsRoundingOf u τ Ω a z)
    (ha : |a| ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) : |a - z| ≤ u * (|a| + τ) := by
  have hmax : max |a| τ ≤ |a| + τ := max_le (by linarith) (by linarith [abs_nonneg a])
  exact (h ha).trans (mul_le_mul_of_nonneg_left hmax hu)

private theorem newtonSchulzSteps_nonneg_aux {s ε : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1 / 2)
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 2) : 0 ≤ newtonSchulzSteps s ε := by
  have h₁ : 0 ≤ Real.logb 2 (min |s| (1 / 2))⁻¹ := by
    rw [abs_of_pos hs, min_eq_left hs₁]
    exact Real.logb_nonneg one_lt_two (one_le_inv₀ hs |>.mpr (by linarith))
  have h₂ : 0 ≤ Real.logb 2 (Real.logb 2 ε⁻¹) := by
    refine Real.logb_nonneg one_lt_two ?_
    rw [← Real.logb_self_eq_one one_lt_two]
    exact Real.logb_le_logb_of_le one_lt_two two_pos ((le_inv_comm₀ two_pos hε).mpr (by linarith))
  unfold newtonSchulzSteps
  linarith

private theorem toNat_add_traceRe_div_eq_aux {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) {k : ℕ} (hk1 : (1 : ℝ) ≤ k) (hk2u : (k : ℝ) ^ 2 * u ≤ 1 / 100000)
    (hkτ : (k : ℝ) * τ ≤ 1 / 4) (hΩ : 16 * k ≤ Ω) (X : Matrix (Fin k) (Fin k) (F × F)) {r : ℕ}
    (hrk : (r : ℝ) ≤ k) (hdiag : |∑ i, dec (X i i).1 - r| ≤ 1 / 57600)
    (hsabs : ∑ i, |dec (X i i).1| ≤ 2 * k) :
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
  have h2 := abs_le.mp (abs_sub_le_of_isRoundingOf_aux (hM.ofNat 2)
    (by norm_num; linarith) hu hτ₀)
  push_cast at h2
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
  have hd2 : 1.9 ≤ dec (M.ofNat 2) ∧ dec (M.ofNat 2) ≤ 2.1 := by constructor <;> linarith
  have hd20 : 0 < dec (M.ofNat 2) := by linarith
  have hh2 : 1 / dec (M.ofNat 2) ≤ 1 := by rw [div_le_one hd20]; linarith
  have hh := abs_le.mp (abs_sub_le_of_isRoundingOf_aux (hM.div M.one (M.ofNat 2) hd20.ne')
    (by rw [hM.dec_one, abs_of_pos (div_pos one_pos hd20)]; linarith) hu hτ₀)
  rw [hM.dec_one, abs_of_pos (div_pos one_pos hd20)] at hh
  have hh1 : |1 / dec (M.ofNat 2) - 1 / 2| ≤ u := by
    rw [div_sub_div _ _ hd20.ne' (by norm_num), abs_div, abs_of_pos (mul_pos hd20 two_pos),
      div_le_iff₀ (mul_pos hd20 two_pos), abs_le]
    have := mul_le_mul_of_nonneg_left hd2.1 hu
    constructor <;> linarith
  have hh1' := abs_le.mp hh1
  have := mul_le_mul_of_nonneg_left hh2 hu
  have hdh : |dec (M.div M.one (M.ofNat 2)) - 1 / 2| ≤ 3 * u := by
    rw [abs_le]; constructor <;> linarith
  have hdh' := abs_le.mp hdh
  -- their rounded sum
  have hzabs : |dec (M.traceRe X) + dec (M.div M.one (M.ofNat 2))| ≤ k + 1 := by
    rw [abs_le]; constructor <;> linarith
  have hz := abs_le.mp (abs_sub_le_of_isRoundingOf_aux (hM.add (M.traceRe X)
    (M.div M.one (M.ofNat 2))) (by linarith) hu hτ₀)
  have hzu := mul_le_mul_of_nonneg_left hzabs hu
  rw [hM.toNat_eq, Nat.floor_eq_iff (by linarith)]
  constructor <;> linarith

private theorem bisection_small_aux {u τ ρ w R ε β μ X : ℝ} {k ℓ : ℕ} (hk : 1 ≤ k)
    (hℓ : 20 ≤ ℓ) (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8) (hρ₁ : ρ ≤ 1) (hw : 0 < w)
    (hwR : w ≤ R) (hβ : 0 < β) (hβtol : β ≤ bisectionSignTol k ε ρ ℓ) (hμ : 0 ≤ μ) (hu : 0 ≤ u)
    (husign : 640 * k * √(k : ℝ) * (8 + μ) *
      (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) * u ≤ w / (4 * R) * β)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * k * √(k : ℝ)) ≤ min (√(ρ / 2)) X) :
    (k : ℝ) * β ≤ 1 / 57600 ∧ (k : ℝ) ^ 2 * u ≤ 1 / 100000 ∧ (k : ℝ) * τ ≤ 1 / 4 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq1 : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hsq := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) k)
  have hkk : (k : ℝ) ≤ k * √(k : ℝ) := le_mul_of_one_le_right (by linarith) hsq1
  have hR0 : 0 < R := hw.trans_le hwR
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  -- the accuracy, the roundoff and the floor are small
  have hβk : β * (k * √(k : ℝ)) ≤ 1 / 57600 := by
    refine (mul_le_mul_of_nonneg_right hβtol (by positivity)).trans ?_
    unfold bisectionSignTol
    have hX : (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) ≤ 1 / 800 := by
      have : 1 / (ℓ : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith [div_pos one_pos (by linarith : (0 : ℝ) < ℓ)]
    have hX0 : 0 ≤ (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) := by
      have : 1 / (ℓ : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      exact div_nonneg (mul_nonneg (by linarith) hε.le) (by positivity)
    have hρ' : √ρ ≤ 1 := Real.sqrt_le_one.mpr hρ₁
    have hL := Real.sqrt_nonneg (2 * Real.log (4 / ρ))
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h1 := mul_le_mul hX hρ' (Real.sqrt_nonneg _) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ k * √(k : ℝ))
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ k) hL]
  have hNs := newtonSchulzSteps_nonneg_aux (s := w / (8 * R)) (ε := β / (16 * k))
    (by positivity) (by rw [div_le_iff₀ (by positivity)]; linarith) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  have hw4 : w / (4 * R) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hku3 : k * √(k : ℝ) * u ≤ β / 20480 := by
    have h1 : 5120 * (k * √(k : ℝ)) * u ≤ 640 * k * √(k : ℝ) * (8 + μ) *
        (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) * u := by
      have := mul_le_mul (by linarith : (8 : ℝ) ≤ 8 + μ) (by linarith : (1 : ℝ) ≤
        newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) zero_le_one
        (by linarith)
      have h0 : 0 ≤ 640 * (k * √(k : ℝ)) * u := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_right hw4 hβ.le
    linarith
  have hkk1 : (1 : ℝ) ≤ k * √(k : ℝ) := hk1.trans hkk
  have hβ1 : β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_left hkk1 hβ.le]
  have hku : (k : ℝ) * u ≤ 1 / 2 := by linarith [mul_le_mul_of_nonneg_right hkk hu]
  have hk2u : (k : ℝ) ^ 2 * u ≤ 1 / 100000 := by
    have : (k : ℝ) ^ 2 * u = (k * √(k : ℝ) * u) * √(k : ℝ) := by
      rw [pow_two]; nth_rewrite 1 [← hsq]; ring
    rw [this]
    have h1 := mul_le_mul_of_nonneg_right hku3 (Real.sqrt_nonneg (k : ℝ))
    have h2 : β * √(k : ℝ) ≤ β * (k * √(k : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hk1) hβ.le
    linarith
  have hkβ : (k : ℝ) * β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_left hkk hβ.le]
  have hkτ : (k : ℝ) * τ ≤ 1 / 4 := by
    have : √(ρ / 2) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    have := hτ.trans (min_le_left _ _)
    linarith [mul_le_mul_of_nonneg_right hkk hτ₀]
  exact ⟨hkβ, hk2u, hkτ⟩

/-- **Rank recovery on Event I**: under the node hypotheses of
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample`
(contracts, precision, step limit, floor and range), for an internal node ($k \ge 2$, $R >
\varepsilon R_0$) and a seed $v \in [-1, 1]$ whose ideal shift $c' = (R/\ell)v$ is at distance at
least $w$ from every eigenvalue (Event I), the node's step splits exactly when $0 < i_+(\mathbf{A}
- c'\mathbf{I}) < k$; moreover then $k_+ = i_+(\mathbf{A} - c'\mathbf{I})$. [Shah2024, proof of
Lemma 4.1], "the estimates $k_\pm$ are the exact ranks".
Proof: `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le` puts the
stored $\mathbf{P}_+$ within $\beta$ of the true projector (there the rounded shift is within
$1.4uR$ of $\mathbf{A} - c'\mathbf{I}$ and the sign is applied with modulus $a = w - 1.4uR$, not
$w/2$, which `husign` would not cover; $\tau \le \sqrt{\rho/2}/(4k^{3/2}) \le 1/16$); its
diagonal sum is within $k\beta$ of the trace
(`NLAlib.norm_apply_le_specNorm`), which is the inertia
(`Matrix.IsHermitian.re_trace_smul_one_add_cfc_sign`); with the rounded sum
(`NLAlib.FloatMachine.IsAccurate.abs_sum_sub_traceRe_le`) the rounded trace is within
$k\beta + 2.2k^2u + (k + 1.5)u < 1/4$ of the inertia, so $\mathrm{fl}(t +
\mathrm{fl}(1/2))$ lies in $(r + 1/4, r + 3/4)$ for the inertia $r$ and its floor (`toNat_eq`,
`Nat.floor_eq_iff`) is $r$; unfold `NLAlib.eighStep`. M, about 60 lines. -/
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
  set r := inertiaPos (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) with hr
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast (by omega : 1 ≤ y.k)
  -- the accuracy, the roundoff and the floor are small
  obtain ⟨hkβ, hk2u, hkτ⟩ := bisection_small_aux (by omega) hℓ hε hε₁ hρ₁ hw hwR hβ hβtol
    hμM hu husign hτ₀ hτ
  have hβ1 : dec β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  -- the computed projector is near the ideal one, whose trace is the inertia
  obtain ⟨hP, -⟩ := hM.specNorm_sub_decodeMatrix_eighProjectors_le_of_le_eq_false (N := N)
    (signFuel := signFuel) (R₀ := R₀) hμM hu hA hR hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol
    husign hfuel hτ₀ hτ hΩ hint hv hI
  set Pp := M.hermScale (M.hermShift (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) (M.neg M.one)) (M.ofNat 2)
    with hPp
  set S := cfc Real.sign (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))
  have hS : specNorm S ≤ 1 := by
    refine Matrix.IsHermitian.specNorm_cfc_le (hA.sub ?_) zero_le_one fun x _ => ?_
    · unfold Matrix.IsHermitian
      simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]
    · rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num
  have hPid : specNorm ((2⁻¹ : ℝ) • (1 + S)) ≤ 1 := by
    rw [specNorm_real_smul]
    have := (specNorm_add_le 1 S).trans (add_le_add specNorm_one_le hS)
    rw [abs_of_pos (by norm_num)]
    linarith
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
  have hβ2 : 1 + dec β ≤ 2 := by linarith
  have hk2 := mul_le_mul_of_nonneg_left hβ2 (Nat.cast_nonneg (α := ℝ) y.k)
  have hfl := toNat_add_traceRe_div_eq_aux hM hu hτ₀ hk1 hk2u hkτ
    (by linarith [Real.sqrt_nonneg (Real.log (4 / ρ))]) Pp hrk (hdiag.trans (by linarith))
    (hsabs.trans (by linarith))
  have hkp : min y.k (M.toNat (M.add (M.traceRe Pp) (M.div M.one (M.ofNat 2)))) = r := by
    rw [hfl]; exact min_eq_right (by exact_mod_cast hrk)
  -- unfold the step
  unfold eighStep
  rw [if_neg (by omega), if_neg (by simp [hint])]
  dsimp only
  rw [hPp] at hkp
  clear_value r
  split_ifs with h1 h2
  · rw [hkp] at h1
    exact iff_of_false id (by rw [h1]; exact fun h => h.2.false)
  · rw [hkp] at h2
    exact iff_of_false id (by rw [h2]; exact fun h => h.1.false)
  · rw [hkp] at h1 h2
    exact iff_of_true trivial ⟨Nat.pos_of_ne_zero h2, lt_of_le_of_ne (by exact_mod_cast hrk) h1⟩


/-- The rounded rank estimate $k_+$ of a node is the inertia on Event I. -/
private theorem FloatMachine.IsAccurate.min_toNat_eighProjector_eq_inertiaPos
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
  -- the accuracy, the roundoff and the floor are small
  obtain ⟨hkβ, hk2u, hkτ⟩ := bisection_small_aux (by omega) hℓ hε hε₁ hρ₁ hw hwR hβ hβtol
    hμM hu husign hτ₀ hτ
  have hβ1 : dec β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  -- the computed projector is near the ideal one, whose trace is the inertia
  obtain ⟨hP, -⟩ := hM.specNorm_sub_decodeMatrix_eighProjectors_le_of_le_eq_false (N := N)
    (signFuel := signFuel) (R₀ := R₀) hμM hu hA hR hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol
    husign hfuel hτ₀ hτ hΩ hint hv hI
  set Pp := M.hermScale (M.hermShift (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) (M.neg M.one)) (M.ofNat 2)
    with hPp
  set S := cfc Real.sign (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))
  have hS : specNorm S ≤ 1 := by
    refine Matrix.IsHermitian.specNorm_cfc_le (hA.sub ?_) zero_le_one fun x _ => ?_
    · unfold Matrix.IsHermitian
      simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]
    · rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num
  have hPid : specNorm ((2⁻¹ : ℝ) • (1 + S)) ≤ 1 := by
    rw [specNorm_real_smul]
    have := (specNorm_add_le 1 S).trans (add_le_add specNorm_one_le hS)
    rw [abs_of_pos (by norm_num)]
    linarith
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
  have hβ2 : 1 + dec β ≤ 2 := by linarith
  have hk2 := mul_le_mul_of_nonneg_left hβ2 (Nat.cast_nonneg (α := ℝ) y.k)
  have hfl := toNat_add_traceRe_div_eq_aux hM hu hτ₀ hk1 hk2u hkτ
    (by linarith [Real.sqrt_nonneg (Real.log (4 / ρ))]) Pp hrk (hdiag.trans (by linarith))
    (hsabs.trans (by linarith))
  have hkp : min y.k (M.toNat (M.add (M.traceRe Pp) (M.div M.one (M.ofNat 2)))) = r := by
    rw [hfl]; exact min_eq_right (by exact_mod_cast hrk)
  exact hkp

/-- The stored half window `fl(R / fl(2))` is within `3u` (relative) of `R/2`. -/
private theorem abs_dec_div_ofNat_two_sub_le_aux {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hu : 0 ≤ u) (hu1 : u ≤ 1 / 100000) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1 / 8) {R : F}
    (hR : 0 < dec R) (hτR : 6 * τ ≤ dec R) (hΩ2 : 2 ≤ Ω) (hΩR : dec R ≤ Ω) :
    |dec (M.div R (M.ofNat 2)) - dec R / 2| ≤ 3 * u * (dec R / 2) := by
  set d := dec (M.ofNat 2) with hd
  have h2 : |(2 : ℝ) - d| ≤ u * (2 + τ) := by
    have := abs_sub_le_of_isRoundingOf_aux (hM.ofNat 2) (by push_cast; rw [abs_two]; exact hΩ2)
      hu hτ0
    push_cast at this
    rwa [abs_two] at this
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  have huτ : u * (2 + τ) ≤ 3 * u := by nlinarith
  have hd1 : 199 / 100 ≤ d := by nlinarith
  have hd0 : d ≠ 0 := by linarith
  set q := dec R / d with hq
  have hqd : q * d = dec R := div_mul_cancel₀ _ hd0
  have hq0 : 0 < q := div_pos hR (by linarith)
  have hqR : q ≤ 51 / 100 * dec R := by nlinarith
  have hdiv := abs_sub_le_of_isRoundingOf_aux (hM.div R (M.ofNat 2) hd0)
    (by rw [← hq, abs_of_pos hq0]; linarith) hu hτ0
  rw [← hq, abs_of_pos hq0] at hdiv
  have hkey : |q - dec R / 2| ≤ q * (3 * u) / 2 := by
    have : q - dec R / 2 = q * (2 - d) / 2 := by rw [← hqd]; ring
    rw [this, abs_div, abs_mul, abs_of_pos hq0, abs_two]
    have := mul_le_mul_of_nonneg_left (h2.trans huτ) hq0.le
    linarith
  have h3 : |dec (M.div R (M.ofNat 2)) - dec R / 2| ≤
      |q - dec (M.div R (M.ofNat 2))| + |q - dec R / 2| := by
    rw [abs_sub_comm q]; exact abs_sub_le _ _ _
  have h4 : u * (q + τ) ≤ u * (51 / 100 * dec R + dec R / 6) :=
    mul_le_mul_of_nonneg_left (by linarith) hu
  have h5 : q * (3 * u) / 2 ≤ 51 / 100 * dec R * (3 * u) / 2 := by
    have := mul_le_mul_of_nonneg_right hqR (by linarith : 0 ≤ 3 * u)
    linarith
  nlinarith

/-- A Hermitian eigenvalue is bounded by the spectral norm. -/
private theorem abs_le_of_mem_spectrum_eighSplit_aux {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) {R x : ℝ} (hR : specNorm X ≤ R) (hx : x ∈ spectrum ℝ X) : |x| ≤ R := by
  rw [hX.spectrum_eq_image_eigenvalue] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact (hX.abs_eigenvalue_le_specNorm j).trans hR

/-- The frame of the positive spectral projector, with a prescribed column count. -/
private theorem exists_frame_pos_eighSplit_aux {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) {R c : ℝ} (hR : specNorm A ≤ R) (hc : ∀ x ∈ spectrum ℝ A, x ≠ c)
    {r : ℕ} (hr : inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) = r) :
    ∃ V : Matrix (Fin k) (Fin r) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) ∧
      spectrum ℝ (Vᴴ * A * V) ⊆ Set.Icc c R := by
  subst hr
  obtain ⟨V, hV, hVV, -, hsp⟩ := hA.exists_hasOrthonormalCols_mul_conjTranspose_eq hc
  refine ⟨V, hV, hVV, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hsp hx
  exact ⟨le_of_lt h2, (le_abs_self x).trans (abs_le_of_mem_spectrum_eighSplit_aux hA hR h1)⟩

/-- The frame of the negative spectral projector, with the complementary column count. -/
private theorem exists_frame_neg_eighSplit_aux {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) {R c : ℝ} (hR : specNorm A ≤ R) (hc : ∀ x ∈ spectrum ℝ A, x ≠ c)
    {r : ℕ} (hr : inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) + r = k) :
    ∃ V : Matrix (Fin k) (Fin r) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 - cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) ∧
      spectrum ℝ (Vᴴ * A * V) ⊆ Set.Icc (-R) c := by
  set X := A - c • (1 : Matrix (Fin k) (Fin k) ℂ) with hXdef
  have hX : X.IsHermitian := hA.sub (by simp [Matrix.IsHermitian, Matrix.conjTranspose_smul])
  have hA' : (-A).IsHermitian := hA.neg
  have hc' : ∀ x ∈ spectrum ℝ (-A), x ≠ -c := by
    intro x hx hxc
    rw [← spectrum.neg_eq] at hx
    exact hc (-x) (Set.mem_neg.mp hx) (by rw [hxc, neg_neg])
  have heq : -A - (-c) • (1 : Matrix (Fin k) (Fin k) ℂ) = -X := by
    rw [hXdef, neg_smul]; abel
  have hunit : IsUnit X := by
    have hcn : c ∉ spectrum ℝ A := fun h => hc c h rfl
    rw [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one] at hcn
    have : X = -(c • (1 : Matrix (Fin k) (Fin k) ℂ) - A) := by rw [hXdef]; abel
    rw [this]; exact hcn.neg
  have hrank : X.rank = k := by rw [Matrix.rank_of_isUnit X hunit, Fintype.card_fin]
  have hrk : inertiaPos (-A - (-c) • (1 : Matrix (Fin k) (Fin k) ℂ)) = r := by
    rw [heq, ← inertiaNeg_eq_inertiaPos_neg]
    have := hX.inertiaPos_add_inertiaNeg
    omega
  obtain ⟨V, hV, hVV, -, hsp⟩ := hA'.exists_hasOrthonormalCols_mul_conjTranspose_eq hc'
  subst hrk
  refine ⟨V, hV, ?_, fun x hx => ?_⟩
  · rw [hVV, heq]
    have hs : cfc Real.sign (-X) = -cfc Real.sign X := by
      rw [← cfc_comp_neg Real.sign X ((X.finite_real_spectrum.image _).continuousOn _)
        hX.isSelfAdjoint]
      have hf : (fun x : ℝ => Real.sign (-x)) = fun x => -Real.sign x :=
        funext fun x => Real.sign_neg
      rw [hf, cfc_neg]
    rw [hs, ← sub_eq_add_neg]
  · have hx' : -x ∈ spectrum ℝ (Vᴴ * -A * V) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, ← spectrum.neg_eq]
      exact Set.neg_mem_neg.mpr hx
    obtain ⟨h1, h2⟩ := hsp hx'
    rw [← spectrum.neg_eq] at h1
    have h1' : x ∈ spectrum ℝ A := by simpa using h1
    have := abs_le_of_mem_spectrum_eighSplit_aux hA hR h1'
    rw [Set.mem_Ioi] at h2
    exact ⟨(neg_abs_le x).trans' (by linarith), by linarith⟩

/-- A square matrix whose action is bounded below by `x` is a unit with inverse of norm `≤ 1/x`. -/
private lemma isUnit_and_specNorm_inv_le_eighSplit_aux {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ}
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
  refine ⟨hU, ?_⟩
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hU)
  refine (specNorm_le_iff (by positivity)).2 fun y => ?_
  have hz : M *ᵥ (M⁻¹ *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
  have h1 := h (M⁻¹ *ᵥ y)
  rw [hz] at h1
  rw [one_div_mul_eq_div, le_div_iff₀ hx]
  linarith [mul_comm x ‖WithLp.toLp 2 (M⁻¹ *ᵥ y)‖]

/-- Deflation of a true spectral projector `V Vᴴ` through a stored approximation, on Event II. -/
private theorem exists_hasOrthonormalCols_specNorm_sub_deflate_eighSplit_aux {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β t x η : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hr0 : 0 < r) (hr : r ≤ n)
    {V : Matrix (Fin n) (Fin r) ℂ} (hV : HasOrthonormalCols V) {P : Matrix (Fin n) (Fin n) (F × F)}
    (hP : specNorm (V * Vᴴ - decodeMatrix dec P) ≤ β) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    {G : Matrix (Fin n) (Fin n) ℂ} (hGt : specNorm G < t) (hx : 0 < x)
    (hσ : x < singularValues (Vᴴ * G.submatrix id (Fin.castLE hr)) (r - 1))
    (htx : t / x * β ≤ η / 18) (hη : η ≤ 1)
    (hu : (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β) (hτ0 : 0 ≤ τ)
    (hτ : τ * √(n : ℝ) ≤ x) (hΩ : 4 * t ≤ Ω) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (V * W - decodeMatrix dec (deflate M r P G)) ≤ (2 + β) * η / 3 := by
  have hlow : ∀ z : Fin r → ℂ, x * ‖WithLp.toLp 2 z‖ ≤
      ‖WithLp.toLp 2 ((Vᴴ * G.submatrix id (Fin.castLE hr)) *ᵥ z)‖ := by
    intro z
    have h1 := singularValues_last_mul_norm_le (Vᴴ * G.submatrix id (Fin.castLE hr))
      (k := r - 1) (by rw [Fintype.card_fin]; omega) z
    exact (mul_le_mul_of_nonneg_right hσ.le (norm_nonneg _)).trans h1
  obtain ⟨hGu, hinv⟩ := isUnit_and_specNorm_inv_le_eighSplit_aux hx hlow
  have h1 : specNorm Vᴴ ≤ 1 := by rw [specNorm_conjTranspose]; exact hV.specNorm_le_one
  have h2 : specNorm (G.submatrix id (Fin.castLE hr)) ≤ specNorm G :=
    specNorm_submatrix_le G Function.injective_id (Fin.castLE_injective hr)
  have hMG : specNorm (Vᴴ * G.submatrix id (Fin.castLE hr)) ≤ specNorm G :=
    (specNorm_mul_le _ _).trans ((mul_le_mul h1 h2 (specNorm_nonneg _) zero_le_one).trans
      (one_mul _).le)
  have hxG : x ≤ specNorm G := hσ.le.trans ((singularValues_le_specNorm _ _).trans hMG)
  have hn1 : (1 : ℝ) ≤ √(n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ n))
  have : Nonempty (Fin r) := ⟨⟨0, hr0⟩⟩
  have hS1 : specNorm (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := specNorm_one
  have hA : V * Vᴴ = V * (1 : Matrix (Fin r) (Fin r) ℂ) * Vᴴ := by rw [Matrix.mul_one]
  have hτ' : τ ≤ specNorm (1 : Matrix (Fin r) (Fin r) ℂ) * specNorm G := by
    rw [hS1, one_mul]; nlinarith
  have hτN' : τ * √(n : ℝ) ≤ specNorm G := hτ.trans hxG
  have hG0 := specNorm_nonneg G
  have ht0 : 0 < t := lt_of_le_of_lt hG0 hGt
  have hΩ' : 2 * (specNorm (1 : Matrix (Fin r) (Fin r) ℂ) + β) * specNorm G ≤ Ω := by
    rw [hS1]; nlinarith
  have hΩG : specNorm G ≤ Ω := by linarith
  have hinv1 : (1 : Matrix (Fin r) (Fin r) ℂ)⁻¹ = 1 := inv_one
  have hmval : (specNorm (1 : Matrix (Fin r) (Fin r) ℂ) + β + 1) *
      specNorm (1 : Matrix (Fin r) (Fin r) ℂ)⁻¹ * specNorm G *
      specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹ ≤ (2 + β) * (t / x) := by
    rw [hinv1, hS1, mul_one]
    have hI0 := specNorm_nonneg (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹
    calc (1 + β + 1) * specNorm G * specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹
        ≤ (1 + β + 1) * t * (1 / x) := by gcongr
      _ = (2 + β) * (t / x) := by ring
  have htx0 : 0 ≤ t / x * β := by positivity
  have hmβ : (2 + β) * (t / x) * β ≤ (2 + β) * (η / 18) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left htx (by linarith)
  have hu' : (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β := hu
  obtain ⟨W, hW, hWb⟩ :=
    FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le
      hM hr hV hV isUnit_one hA hP hGu rfl
      ((mul_le_mul_of_nonneg_right hmval hβ0).trans (hmβ.trans (by nlinarith))) hu' hτ' hτN' hΩ' hΩG
  refine ⟨W, hW, hWb.trans ?_⟩
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmval (by norm_num : (0:ℝ) ≤ 6)) hβ0
  nlinarith

/-- The product contract through `decodeMatrix`. -/
private theorem specNorm_mul_sub_decodeMatrix_mm_eighSplit_aux {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (F × F))
    (B : Matrix (Fin m) (Fin n) (F × F))
    (h : specNorm (decodeMatrix dec A) * specNorm (decodeMatrix dec B) ≤ Ω) :
    specNorm (decodeMatrix dec A * decodeMatrix dec B - decodeMatrix dec (M.mm A B)) ≤
      μM (max l (max m n)) * u *
        max (specNorm (decodeMatrix dec A) * specNorm (decodeMatrix dec B)) τ :=
  hM.isMatMulErr.specNorm_mul_sub_le A B h

/-- The two stored products of a compression, against the exact compression by `V W`. -/
private theorem specNorm_compress_sub_decodeMatrix_mm_le_eighSplit_aux {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k r : ℕ} (hk1 : 1 ≤ k) (hrk : r ≤ k) {β η R : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hμ0 : 0 ≤ μM k) (hμ : μM k * u ≤ β / 2)
    (hβ0 : 0 ≤ β) (hβη : β ≤ η / 144) (hη0 : 0 < η) (hη1 : η ≤ 1 / 800)
    (hR0 : 0 < R) (hτ0 : 0 ≤ τ) (hkτ : 3 * k * τ ≤ R) (hΩ : 4 * R ≤ Ω)
    {As : Matrix (Fin k) (Fin k) (F × F)}
    (hAR : specNorm (decodeMatrix dec As) ≤ R)
    {Q : Matrix (Fin k) (Fin r) (F × F)} {V : Matrix (Fin k) (Fin r) ℂ}
    {W : Matrix (Fin r) (Fin r) ℂ} (hV : HasOrthonormalCols V) (hW : HasOrthonormalCols W)
    (he : specNorm (V * W - decodeMatrix dec Q) ≤ (2 + β) * η / 3) :
    specNorm ((V * W)ᴴ * decodeMatrix dec As * (V * W) -
      decodeMatrix dec (M.mm (M.mm (M.conjTransposeMat Q) As) Q)) ≤
        R * ((2 + β) * η / 3 * (2 + (2 + β) * η / 3)) + 136 / 100 * β * R := by
  set A := decodeMatrix dec As with hAdef
  set Qb := decodeMatrix dec Q with hQdef
  set Z := V * W with hZdef
  have hZ : HasOrthonormalCols Z := hV.mul hW
  have hZ1 : specNorm Z ≤ 1 := hZ.specNorm_le_one
  set e := (2 + β) * η / 3 with he_def
  have hβ1 : β ≤ 1 / 115200 := by linarith
  have he0 : 0 ≤ e := div_nonneg (mul_nonneg (by linarith) hη0.le) (by norm_num)
  have heη : e ≤ (2 / 3 + 1 / 100000) * η := by
    have := mul_le_mul_of_nonneg_right hβ1 hη0.le
    rw [he_def]; linarith
  have he1 : e ≤ 1 / 1000 := by linarith
  have hβR : β * R ≤ R / 115200 := by
    have := mul_le_mul_of_nonneg_right hβ1 hR0.le; linarith
  have hβR0 : 0 ≤ β * R := mul_nonneg hβ0 hR0.le
  have heR' : (1 + e) * R ≤ 1001 / 1000 * R := mul_le_mul_of_nonneg_right (by linarith) hR0.le
  have hτR : τ ≤ R / 3 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have := mul_le_mul_of_nonneg_right this hτ0
    linarith
  have hA0 := specNorm_nonneg A
  have hμu0 : 0 ≤ μM k * u := mul_nonneg hμ0 hu0
  have hmax : ∀ a : ℝ, 0 ≤ a → max a τ ≤ a + τ := fun a ha =>
    max_le (by linarith) (by linarith)
  -- the stored basis
  have hQ : specNorm Qb ≤ 1 + e := by
    have : Qb = Z - (Z - Qb) := by abel
    rw [this]
    exact (specNorm_sub_le _ _).trans (by linarith)
  have hQ0 := specNorm_nonneg Qb
  -- the first product
  have hQH : decodeMatrix dec (M.conjTransposeMat Q) = Qbᴴ := hM.decodeMatrix_conjTransposeMat Q
  have hQHn : specNorm Qbᴴ = specNorm Qb := specNorm_conjTranspose Qb
  have hQA : specNorm Qbᴴ * specNorm A ≤ (1 + e) * R := by
    rw [hQHn]; exact mul_le_mul hQ hAR hA0 (by linarith)
  have heR : (1 + e) * R ≤ 2 * R := by linarith
  have hm1 := specNorm_mul_sub_decodeMatrix_mm_eighSplit_aux hM (M.conjTransposeMat Q) As
    (by rw [hQH]; linarith)
  rw [hQH, show max r (max k k) = k by omega] at hm1
  set C1 := decodeMatrix dec (M.mm (M.conjTransposeMat Q) As) with hC1def
  have hd1 : specNorm (Qbᴴ * A - C1) ≤ β / 2 * (134 / 100 * R) := by
    refine hm1.trans ?_
    have h1 : max (specNorm Qbᴴ * specNorm A) τ ≤ 134 / 100 * R := by
      refine (hmax _ (mul_nonneg (specNorm_nonneg _) hA0)).trans ?_
      linarith
    exact (mul_le_mul_of_nonneg_left h1 hμu0).trans
      (mul_le_mul_of_nonneg_right hμ (by linarith))
  have hC1 : specNorm C1 ≤ 1002 / 1000 * R := by
    have : C1 = Qbᴴ * A - (Qbᴴ * A - C1) := by abel
    rw [this]
    refine (specNorm_sub_le _ _).trans ?_
    have := (specNorm_mul_le Qbᴴ A).trans hQA
    linarith
  have hC10 := specNorm_nonneg C1
  -- the second product
  have hC1Q : specNorm C1 * specNorm Qb ≤ 1004 / 1000 * R := by
    have := mul_le_mul hC1 hQ hQ0 (by linarith)
    have h2 : 1002 / 1000 * R * (1 + e) ≤ 1002 / 1000 * R * (1001 / 1000) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hm2 := specNorm_mul_sub_decodeMatrix_mm_eighSplit_aux hM
    (M.mm (M.conjTransposeMat Q) As) Q (by rw [← hC1def]; linarith)
  rw [← hC1def, show max r (max k r) = k by omega] at hm2
  set C2 := decodeMatrix dec (M.mm (M.mm (M.conjTransposeMat Q) As) Q) with hC2def
  have hd2 : specNorm (C1 * Qb - C2) ≤ β / 2 * (134 / 100 * R) := by
    refine hm2.trans ?_
    have h1 : max (specNorm C1 * specNorm Qb) τ ≤ 134 / 100 * R := by
      refine (hmax _ (mul_nonneg hC10 hQ0)).trans ?_
      linarith
    exact (mul_le_mul_of_nonneg_left h1 hμu0).trans
      (mul_le_mul_of_nonneg_right hμ (by linarith))
  -- the exact compression
  set H := Zᴴ * A * Z with hHdef
  have hZH : specNorm Zᴴ ≤ 1 := by rw [specNorm_conjTranspose]; exact hZ1
  have hZA : specNorm (Zᴴ * A) ≤ R :=
    (specNorm_mul_le _ _).trans ((mul_le_mul hZH hAR hA0 zero_le_one).trans (one_mul R).le)
  have hHQ : specNorm (H - Qbᴴ * A * Qb) ≤ R * (e * (2 + e)) := by
    have hdec : H - Qbᴴ * A * Qb = Zᴴ * A * (Z - Qb) + (Z - Qb)ᴴ * A * Qb := by
      rw [hHdef, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]; abel
    rw [hdec]
    refine (specNorm_add_le _ _).trans ?_
    have h1 : specNorm (Zᴴ * A * (Z - Qb)) ≤ R * e :=
      (specNorm_mul_le _ _).trans (mul_le_mul hZA he (specNorm_nonneg _) hR0.le)
    have h2 : specNorm ((Z - Qb)ᴴ * A * Qb) ≤ R * e * (1 + e) := by
      refine (specNorm_mul_le _ _).trans ?_
      have : specNorm ((Z - Qb)ᴴ * A) ≤ R * e := by
        refine (specNorm_mul_le _ _).trans ?_
        rw [specNorm_conjTranspose, mul_comm R]
        exact mul_le_mul he hAR hA0 he0
      exact mul_le_mul this hQ hQ0 (mul_nonneg hR0.le he0)
    exact (add_le_add h1 h2).trans (le_of_eq (by ring))
  have hdec : H - C2 = (H - Qbᴴ * A * Qb) + (Qbᴴ * A - C1) * Qb + (C1 * Qb - C2) := by
    rw [Matrix.sub_mul]; abel
  rw [hdec]
  have h3 := specNorm_add_le (H - Qbᴴ * A * Qb + (Qbᴴ * A - C1) * Qb) (C1 * Qb - C2)
  have h4 := specNorm_add_le (H - Qbᴴ * A * Qb) ((Qbᴴ * A - C1) * Qb)
  have h1 := (specNorm_mul_le (Qbᴴ * A - C1) Qb).trans
    (mul_le_mul hd1 hQ hQ0 (by linarith))
  have : β / 2 * (134 / 100 * R) * (1 + e) ≤ β / 2 * (134 / 100 * R) * (1 + 1 / 1000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- The stored Hermitian average and shift of a matrix near a Hermitian `H`. -/
private theorem specNorm_decodeMatrix_hermShift_hermAvg_sub_le_eighSplit_aux {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {r : ℕ} {β R δ : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hu3 : u ≤ 1 / 115200) (hβ1 : β ≤ 1 / 115200) (hR0 : 0 < R)
    (hτ0 : 0 ≤ τ) (hτR : τ ≤ R / 3) (hrτ : (r : ℝ) * τ ≤ R / 3) (hsr : √(r : ℝ) * u ≤ β / 4)
    (hΩ : 4 * R ≤ Ω) {H : Matrix (Fin r) (Fin r) ℂ} (hHh : Hᴴ = H) (hH : specNorm H ≤ R)
    {X : Matrix (Fin r) (Fin r) (F × F)} (hHC2 : specNorm (H - decodeMatrix dec X) ≤ δ)
    (hδ : δ ≤ R / 100) {two s : F} (htwo : |dec two - 2| ≤ 3 * u) (hs : |dec s| ≤ R) :
    specNorm (decodeMatrix dec (M.hermShift (M.hermAvg X two) s) -
      (H - dec s • (1 : Matrix (Fin r) (Fin r) ℂ))) ≤
        δ + 3 * u * (R / 100) + 3 * u * R + (3 * (β / 4) * (102 / 100 * R) + 2 * (u * R)) +
          u * (21 / 10 * R + R / 3) := by
  have hH0 := specNorm_nonneg H
  have hβR : β * R ≤ R / 115200 := by
    have := mul_le_mul_of_nonneg_right hβ1 hR0.le; linarith
  have hβ0 : 0 ≤ β := hu0.trans hu1
  set C2 := decodeMatrix dec X with hC2def
  set d := dec two with hddef
  obtain ⟨hda, hdb⟩ := abs_le.mp htwo
  have hd1 : 1 ≤ d := by linarith
  set a := d⁻¹ with hadef
  have ha : a * d = 1 := inv_mul_cancel₀ (by linarith)
  have ha0 : 0 < a := inv_pos.mpr (by linarith)
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ hd1
  have h2a : 2 * a ≤ 1 + 3 * u := by
    have h1 : a * (2 - 3 * u) ≤ a * d := mul_le_mul_of_nonneg_left (by linarith) ha0.le
    have h2 : a * (3 * u) ≤ 1 * (3 * u) := mul_le_mul_of_nonneg_right ha1 (by linarith)
    linarith
  have h1a : |1 - 2 * a| ≤ 3 * u := by
    have : 1 - 2 * a = a * (d - 2) := by rw [mul_sub, ha]; ring
    rw [this, abs_mul, abs_of_pos ha0]
    have h1 : a * |d - 2| ≤ a * (3 * u) := mul_le_mul_of_nonneg_left htwo ha0.le
    have h2 : a * (3 * u) ≤ 1 * (3 * u) := mul_le_mul_of_nonneg_right ha1 (by linarith)
    linarith
  set Hs := a • (C2 + C2ᴴ) with hHsdef
  have hdecomp : H - Hs = a • ((H - C2) + (H - C2)ᴴ) + (1 - 2 * a) • H := by
    rw [hHsdef, Matrix.conjTranspose_sub, hHh]; module
  have hHC20 := specNorm_nonneg (H - C2)
  have hHC2s : specNorm (H - C2) ≤ R / 100 := hHC2.trans hδ
  have hHHs : specNorm (H - Hs) ≤ δ + 3 * u * (R / 100) + 3 * u * R := by
    rw [hdecomp]
    refine (specNorm_add_le _ _).trans ?_
    rw [specNorm_real_smul, specNorm_real_smul, abs_of_pos ha0]
    have h1 : specNorm ((H - C2) + (H - C2)ᴴ) ≤ 2 * specNorm (H - C2) := by
      have := specNorm_add_le (H - C2) (H - C2)ᴴ
      rw [specNorm_conjTranspose] at this; linarith
    have h2 : a * specNorm ((H - C2) + (H - C2)ᴴ) ≤ (1 + 3 * u) * specNorm (H - C2) := by
      have := mul_le_mul_of_nonneg_left h1 ha0.le
      have h3 := mul_le_mul_of_nonneg_right h2a hHC20
      linarith
    have h3 : |1 - 2 * a| * specNorm H ≤ 3 * u * R :=
      mul_le_mul h1a hH hH0 (by linarith)
    have h4 : 3 * u * specNorm (H - C2) ≤ 3 * u * (R / 100) :=
      mul_le_mul_of_nonneg_left hHC2s (by linarith)
    linarith
  have huR : u * R ≤ β * R := mul_le_mul_of_nonneg_right hu1 hR0.le
  have huR' : u * R ≤ R / 115200 := mul_le_mul_of_nonneg_right hu3 hR0.le |>.trans
    (le_of_eq (by ring))
  have hHs : specNorm Hs ≤ 102 / 100 * R := by
    have : Hs = H - (H - Hs) := by abel
    rw [this]
    refine (specNorm_sub_le _ _).trans ?_
    linarith
  have hHs0 := specNorm_nonneg Hs
  have hC2 : specNorm C2 ≤ 101 / 100 * R := by
    have : C2 = H - (H - C2) := by abel
    rw [this]
    refine (specNorm_sub_le _ _).trans ?_
    linarith
  have hAvg := hM.specNorm_sub_decodeMatrix_hermAvg_le hu0 (by linarith) hτ0 X (c := two)
    (by rw [← hddef, abs_of_pos (by linarith)]; exact hd1) (by rw [← hC2def]; linarith)
  rw [← hC2def, ← hddef, ← hadef, ← hHsdef] at hAvg
  set Y := decodeMatrix dec (M.hermAvg X two) with hYdef
  have hHsY : specNorm (Hs - Y) ≤ 3 * (β / 4) * (102 / 100 * R) + 2 * (u * R) := by
    refine hAvg.trans ?_
    have heq : 3 * u * (√(r : ℝ) * specNorm Hs + 2 * r * τ) =
        3 * (√(r : ℝ) * u) * specNorm Hs + 6 * u * (r * τ) := by ring
    rw [heq]
    have h1 : 3 * (√(r : ℝ) * u) * specNorm Hs ≤ 3 * (β / 4) * (102 / 100 * R) :=
      mul_le_mul (by linarith) hHs hHs0 (by linarith)
    have h2 : 6 * u * (r * τ) ≤ 6 * u * (R / 3) := mul_le_mul_of_nonneg_left hrτ (by linarith)
    linarith
  -- the shift
  have hYh : Y.IsHermitian := hM.isHermitian_decodeMatrix_hermFrom _ _
  have hs1 : specNorm (dec s • (1 : Matrix (Fin r) (Fin r) ℂ)) ≤ R := by
    rw [specNorm_real_smul]
    exact (mul_le_mul hs specNorm_one_le (specNorm_nonneg _) hR0.le).trans (mul_one R).le
  have hYs : specNorm (Y - dec s • (1 : Matrix (Fin r) (Fin r) ℂ)) ≤ 21 / 10 * R := by
    have : Y - dec s • (1 : Matrix (Fin r) (Fin r) ℂ) =
        Hs - (Hs - Y) - dec s • (1 : Matrix (Fin r) (Fin r) ℂ) := by abel
    rw [this]
    refine (specNorm_sub_le _ _).trans ?_
    have := specNorm_sub_le Hs (Hs - Y)
    linarith
  have hSh := hM.specNorm_sub_decodeMatrix_hermShift_le hu0 hYh s (by linarith)
  rw [← hYdef] at hSh
  have hSh' : specNorm ((Y - dec s • (1 : Matrix (Fin r) (Fin r) ℂ)) -
      decodeMatrix dec (M.hermShift (M.hermAvg X two) s)) ≤ u * (21 / 10 * R + R / 3) := by
    refine hSh.trans (mul_le_mul_of_nonneg_left ?_ hu0)
    exact max_le (by linarith [specNorm_nonneg (Y - dec s • (1 : Matrix (Fin r) (Fin r) ℂ))])
      (by linarith)
  have hfin : decodeMatrix dec (M.hermShift (M.hermAvg X two) s) -
      (H - dec s • (1 : Matrix (Fin r) (Fin r) ℂ)) =
      -((H - Hs) + (Hs - Y)) - ((Y - dec s • (1 : Matrix (Fin r) (Fin r) ℂ)) -
        decodeMatrix dec (M.hermShift (M.hermAvg X two) s)) := by abel
  rw [hfin]
  refine (specNorm_sub_le _ _).trans ?_
  rw [specNorm_neg]
  have h1 := specNorm_add_le (H - Hs) (Hs - Y)
  linarith

/-- The stored compression of a deflated basis near `V W`. -/
private theorem specNorm_decodeMatrix_compress_sub_le_eighSplit_aux {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k r : ℕ} (hk1 : 1 ≤ k) (hrk : r ≤ k) {β η R : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hμ0 : 0 ≤ μM k) (hμ : μM k * u ≤ β / 2)
    (hsk : √(k : ℝ) * u ≤ β / 4)
    (hβ0 : 0 ≤ β) (hβη : β ≤ η / 144) (hη0 : 0 < η) (hη1 : η ≤ 1 / 800)
    (hR0 : 0 < R) (hτ0 : 0 ≤ τ) (hkτ : 3 * k * τ ≤ R) (hΩ : 4 * R ≤ Ω)
    {As : Matrix (Fin k) (Fin k) (F × F)} (hAh : (decodeMatrix dec As).IsHermitian)
    (hAR : specNorm (decodeMatrix dec As) ≤ R)
    {Q : Matrix (Fin k) (Fin r) (F × F)} {V : Matrix (Fin k) (Fin r) ℂ}
    {W : Matrix (Fin r) (Fin r) ℂ} (hV : HasOrthonormalCols V) (hW : HasOrthonormalCols W)
    (he : specNorm (V * W - decodeMatrix dec Q) ≤ (2 + β) * η / 3)
    {two s : F} (htwo : |dec two - 2| ≤ 3 * u) (hs : |dec s| ≤ R) :
    specNorm (decodeMatrix dec
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) As) Q) two) s) -
      (Wᴴ * (Vᴴ * decodeMatrix dec As * V) * W - dec s • (1 : Matrix (Fin r) (Fin r) ℂ))) ≤
        (2 + 2 * η) * R * η := by
  have hP1 := specNorm_compress_sub_decodeMatrix_mm_le_eighSplit_aux hM hk1 hrk hu0 hu1 hμ0 hμ
    hβ0 hβη hη0 hη1 hR0 hτ0 hkτ hΩ hAR hV hW he
  set e := (2 + β) * η / 3 with he_def
  have hβ1 : β ≤ 1 / 115200 := by linarith
  have he0 : 0 ≤ e := div_nonneg (mul_nonneg (by linarith) hη0.le) (by norm_num)
  have heη : e ≤ (2 / 3 + 1 / 100000) * η := by
    have := mul_le_mul_of_nonneg_right hβ1 hη0.le
    rw [he_def]; linarith
  have he1 : e ≤ 1 / 1000 := by linarith
  have hβR : β * R ≤ R / 115200 := by
    have := mul_le_mul_of_nonneg_right hβ1 hR0.le; linarith
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hτR : τ ≤ R / 3 := by
    have := mul_le_mul_of_nonneg_right hk1' hτ0
    linarith
  have hsr : √(r : ℝ) * u ≤ β / 4 := by
    have : √(r : ℝ) ≤ √(k : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hrk)
    have := mul_le_mul_of_nonneg_right this hu0
    linarith
  have hrτ : (r : ℝ) * τ ≤ R / 3 := by
    have : (r : ℝ) ≤ k := by exact_mod_cast hrk
    have := mul_le_mul_of_nonneg_right this hτ0
    linarith
  have hHh : ((V * W)ᴴ * decodeMatrix dec As * (V * W))ᴴ =
      (V * W)ᴴ * decodeMatrix dec As * (V * W) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hAh.eq,
      Matrix.mul_assoc]
  have hZ1 : specNorm (V * W) ≤ 1 := (hV.mul hW).specNorm_le_one
  have hZH : specNorm (V * W)ᴴ ≤ 1 := by rw [specNorm_conjTranspose]; exact hZ1
  have hZA : specNorm ((V * W)ᴴ * decodeMatrix dec As) ≤ R :=
    (specNorm_mul_le _ _).trans ((mul_le_mul hZH hAR (specNorm_nonneg _) zero_le_one).trans
      (one_mul R).le)
  have hH : specNorm ((V * W)ᴴ * decodeMatrix dec As * (V * W)) ≤ R :=
    (specNorm_mul_le _ _).trans ((mul_le_mul hZA hZ1 (specNorm_nonneg _) hR0.le).trans
      (mul_one R).le)
  have hδ : R * (e * (2 + e)) + 136 / 100 * β * R ≤ R / 100 := by
    have h1 : e * (2 + e) ≤ 1 / 1000 * (2 + 1 / 1000) :=
      mul_le_mul he1 (by linarith) (by linarith) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left h1 hR0.le
    linarith
  have hP2 := specNorm_decodeMatrix_hermShift_hermAvg_sub_le_eighSplit_aux hM hu0 hu1
    (by linarith) hβ1 hR0 hτ0 hτR hrτ hsr hΩ hHh hH hP1 hδ htwo hs
  have hHW : Wᴴ * (Vᴴ * decodeMatrix dec As * V) * W =
      (V * W)ᴴ * decodeMatrix dec As * (V * W) := by
    rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [hHW]
  refine hP2.trans ?_
  have hee : e * (2 + e) ≤ (2 / 3 + 1 / 100000) * η * (2 + 1 / 1000) :=
    mul_le_mul heη (by linarith) (by linarith) (by positivity)
  have h2 := mul_le_mul_of_nonneg_left hee hR0.le
  have h3 : β * R ≤ η / 144 * R := mul_le_mul_of_nonneg_right hβη hR0.le
  have h4 : 0 ≤ R * η * η := by positivity
  have huR : u * R ≤ β * R := mul_le_mul_of_nonneg_right hu1 hR0.le
  have h5 : u * (R / 100) ≤ u * R := mul_le_mul_of_nonneg_left (by linarith) hu0
  have huR0 : 0 ≤ u * R := mul_nonneg hu0 hR0.le
  have h6 : u * (21 / 10 * R + R / 3) ≤ 3 * (u * R) := by linarith
  linarith

/-- The scalar budget of a split node. -/
private theorem eighSplit_numerics_aux {u τ Ω cN μMk μQk R R₀ ε β ρ w z : ℝ} {k ℓ : ℕ}
    (hk2 : 2 ≤ k) (hℓ : 20 ≤ ℓ) (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8) (hR₀ : 0 < R₀) (hρ : 0 < ρ)
    (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ R) (hβ : 0 < β)
    (hβtol : β ≤ bisectionSignTol k ε ρ ℓ) (hμM : 0 ≤ μMk) (hμQ : 0 ≤ μQk) (hcN : 0 ≤ cN)
    (hu : 0 ≤ u)
    (husign : 640 * k * √(k : ℝ) * (8 + μMk) *
      (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) * u ≤ w / (4 * R) * β)
    (hudefl : (4 * μQk + 4 * √(k : ℝ) * (cN + 1) + 2 * μMk + 1) * u ≤ β)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * k * √(k : ℝ)) ≤ min (√(ρ / 2)) (ε * R₀))
    (hΩ : 16 * (R₀ + R + k + ℓ + √(Real.log (4 / ρ))) ≤ Ω)
    (hz : IsRoundingOf u τ Ω (ε * R₀) z) (hlt : z < R) :
    u ≤ 1 / 100000 ∧ τ ≤ 1 / 8 ∧ 6 * τ ≤ R ∧ 3 * k * τ ≤ R ∧ 2 ≤ Ω ∧ 4 * R ≤ Ω ∧
    0 < (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) ∧ (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) ≤ 1 / 800 ∧
    β ≤ (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) / 144 ∧ β ≤ 1 / 57600 ∧
    √2 * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ))) / (√(ρ / 2) / k) * β ≤
      (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) / 18 ∧
    0 < √(ρ / 2) / k ∧ τ * √(k : ℝ) ≤ √(ρ / 2) / k ∧
    4 * (√2 * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ)))) ≤ Ω ∧
    (4 * μQk + 4 * √(k : ℝ) * cN + 2 * μMk) * u ≤ β ∧ μMk * u ≤ β / 2 ∧
    √(k : ℝ) * u ≤ β / 4 ∧ u ≤ β := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  obtain ⟨hkβ, hk2u, hkτ⟩ := bisection_small_aux (by omega) hℓ hε hε₁ hρ₁ hw hwR hβ hβtol
    hμM hu husign hτ₀ hτ
  have hR0 : 0 < R := hw.trans_le hwR
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hsqk : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hsqkk := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) k)
  have hlog0 := Real.sqrt_nonneg (Real.log (4 / ρ))
  have hL0 := Real.sqrt_nonneg (2 * Real.log (4 / ρ))
  have hΩ' : 16 * (R₀ + R + k + ℓ) ≤ Ω := by linarith
  have hu1 : u ≤ 1 / 100000 := by
    have : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
    have := mul_le_mul_of_nonneg_right this hu
    linarith
  have hβ1 : β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  have hτ1 : τ ≤ 1 / 8 := by linarith [mul_le_mul_of_nonneg_right hk2' hτ₀]
  have hτε : τ * (4 * k * √(k : ℝ)) ≤ ε * R₀ := hτ.trans (min_le_right _ _)
  have hτρ : τ * (4 * k * √(k : ℝ)) ≤ √(ρ / 2) := hτ.trans (min_le_left _ _)
  have hkτ4 : 4 * k * τ ≤ τ * (4 * k * √(k : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hsqk (by positivity : (0 : ℝ) ≤ 4 * k * τ)
    linarith
  have hεR₀ : 0 ≤ ε * R₀ := mul_nonneg hε.le hR₀.le
  have hεR₀' : ε * R₀ ≤ R₀ := mul_le_of_le_one_left hR₀.le (by linarith)
  have hmul := abs_sub_le_of_isRoundingOf_aux hz (by rw [abs_of_nonneg hεR₀]; linarith) hu hτ₀
  rw [abs_of_nonneg hεR₀] at hmul
  have hkτR : 3 * k * τ ≤ R := by
    obtain ⟨-, h2⟩ := abs_le.mp hmul
    have h3 := mul_le_mul_of_nonneg_right hu1 hεR₀
    have h4 := mul_le_mul_of_nonneg_right hu1 hτ₀
    have h5 := mul_le_mul_of_nonneg_right hk1 hτ₀
    have h6 : u * (ε * R₀ + τ) = u * (ε * R₀) + u * τ := by ring
    linarith
  have hτR6 : 6 * τ ≤ R := by
    have := mul_le_mul_of_nonneg_right hk2' hτ₀
    linarith
  -- the accuracy budget
  set η := (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) with hηdef
  have hℓinv : 1 / (ℓ : ℝ) ≤ 1 / 20 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hη0 : 0 < η := div_pos (mul_pos (by linarith) hε) (by linarith)
  have hη1 : η ≤ 1 / 800 := by
    rw [hηdef, div_le_iff₀ (by linarith)]
    have h1 : (1 - 1 / (ℓ : ℝ)) * ε ≤ 1 * (1 / 8) :=
      mul_le_mul (by linarith [div_pos one_pos (by linarith : (0 : ℝ) < ℓ)]) hε₁ hε.le
        (by norm_num)
    linarith
  set L := √(2 * Real.log (4 / ρ)) with hLdef
  have hkk2 : (2 : ℝ) ≤ k * √(k : ℝ) := by
    have := mul_le_mul hk2' hsqk zero_le_one (by linarith)
    linarith
  have hD : 144 ≤ 36 * k * (2 * √(k : ℝ) + L) := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 36 * k) hL0
    have h1 : 36 * k * (2 * √(k : ℝ) + L) = 72 * (k * √(k : ℝ)) + 36 * k * L := by ring
    linarith
  have hsρ : √ρ ≤ 1 := Real.sqrt_le_one.mpr hρ₁
  have htol : bisectionSignTol k ε ρ ℓ = η * √ρ / (36 * k * (2 * √(k : ℝ) + L)) := rfl
  have hβη : β ≤ η / 144 := by
    refine hβtol.trans ?_
    rw [htol, div_le_div_iff₀ (by linarith) (by norm_num)]
    have h1 : η * √ρ ≤ η := mul_le_of_le_one_right hη0.le hsρ
    have h2 := mul_le_mul_of_nonneg_left hD hη0.le
    linarith
  have hs2 : √(ρ / 2) * √2 = √ρ := by
    rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ (by norm_num)]
  have hsq2 : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsρ2 : 0 < √(ρ / 2) := Real.sqrt_pos.mpr (by linarith)
  have hx0 : 0 < √(ρ / 2) / k := div_pos hsρ2 (by linarith)
  have htx : √2 * (2 * √(k : ℝ) + L) / (√(ρ / 2) / k) * β ≤ η / 18 := by
    have h0 : 0 ≤ √2 * (2 * √(k : ℝ) + L) / (√(ρ / 2) / k) := by positivity
    refine (mul_le_mul_of_nonneg_left hβtol h0).trans (le_of_eq ?_)
    rw [htol, ← hs2]
    have hD0 : 0 < 2 * √(k : ℝ) + L := by linarith
    field_simp
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hτx : τ * √(k : ℝ) ≤ √(ρ / 2) / k := by
    rw [le_div_iff₀ (by linarith)]
    have : τ * √(k : ℝ) * k * 4 = τ * (4 * k * √(k : ℝ)) := by ring
    have : 0 ≤ τ * √(k : ℝ) * k := by positivity
    linarith
  have hΩt : 4 * (√2 * (2 * √(k : ℝ) + L)) ≤ Ω := by
    have hL : L = √2 * √(Real.log (4 / ρ)) := Real.sqrt_mul (by norm_num) _
    have h2 : √(2 : ℝ) ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hkk : √(k : ℝ) ≤ k := by
      have := mul_le_mul_of_nonneg_left hsqk (Real.sqrt_nonneg (k : ℝ)); linarith
    rw [hL]
    have h3 : 4 * (√2 * (2 * √(k : ℝ) + √2 * √(Real.log (4 / ρ)))) =
        8 * √2 * √(k : ℝ) + 4 * (√2 * √2) * √(Real.log (4 / ρ)) := by ring
    rw [h3, hsq2]
    have h4 : √2 * √(k : ℝ) ≤ 3 / 2 * k :=
      mul_le_mul h2 hkk (Real.sqrt_nonneg _) (by norm_num)
    have : (0 : ℝ) ≤ R₀ + R + ℓ := by linarith
    linarith
  have hsku0 : 0 ≤ √(k : ℝ) * u := mul_nonneg (Real.sqrt_nonneg _) hu
  have hμu0 : 0 ≤ μMk * u := mul_nonneg hμM hu
  have hcNu : 0 ≤ √(k : ℝ) * cN * u := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hcN) hu
  have hμQu : 0 ≤ μQk * u := mul_nonneg hμQ hu
  have hexp : (4 * μQk + 4 * √(k : ℝ) * (cN + 1) + 2 * μMk + 1) * u =
      4 * (μQk * u) + 4 * (√(k : ℝ) * cN * u) + 4 * (√(k : ℝ) * u) + 2 * (μMk * u) + u := by ring
  have hexp2 : (4 * μQk + 4 * √(k : ℝ) * cN + 2 * μMk) * u =
      4 * (μQk * u) + 4 * (√(k : ℝ) * cN * u) + 2 * (μMk * u) := by ring
  refine ⟨hu1, hτ1, hτR6, hkτR, by linarith, by linarith, hη0, hη1, hβη, hβ1, htx, hx0, hτx,
    hΩt, by linarith, by linarith, by linarith, by linarith⟩

/-- EB1d, stated above its first use (EB1a). -/
private theorem FloatMachine.IsAccurate.exists_frames_of_eighStep_eq_split_aux
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
    {smp : EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w (√(ρ / 2) / y.k)
        (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y smp)
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
  -- the node is internal and the leaf test fails
  have hk2 : 2 ≤ y.k := by
    by_contra h
    unfold eighStep at hsplit
    rw [if_pos (by omega)] at hsplit
    cases hsplit
  have hint : M.le y.R (M.mul y.ε R₀) = false := by
    cases h : M.le y.R (M.mul y.ε R₀)
    · rfl
    · unfold eighStep at hsplit
      rw [if_neg (by omega), if_pos h] at hsplit
      cases hsplit
  obtain ⟨⟨hv, hI⟩, hII⟩ := hgood hk2 hint
  have hlt : dec (M.mul y.ε R₀) < dec y.R :=
    not_le.mp (mt (hM.le_iff y.R (M.mul y.ε R₀)).mpr (by simp [hint]))
  obtain ⟨hu1, hτ1, hτR6, hkτR, hΩ2, hΩ4, hη0, hη1, hβη, hβ1, htx, hx0, hτx, hΩt, hdefl, hμ,
    hsk, huβ⟩ := eighSplit_numerics_aux hk2 hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol hμM hμQ hcN hu
      husign hudefl hτ₀ hτ hΩ (hM.mul y.ε R₀) hlt
  have hR0 : 0 < dec y.R := hw.trans_le hwR
  -- the shift
  have hσ := abs_dec_div_ofNat_two_sub_le_aux hM hu hu1 hτ₀ hτ1 hR0 hτR6 hΩ2 (by linarith)
  have hhalf : |dec (M.div y.R (M.ofNat 2))| ≤ dec y.R := by
    have h1 := abs_sub_abs_le_abs_sub (dec (M.div y.R (M.ofNat 2))) (dec y.R / 2)
    rw [abs_of_pos (by linarith : 0 < dec y.R / 2)] at h1
    have h2 := mul_le_mul_of_nonneg_right hu1 hR0.le
    have h3 : 3 * u * (dec y.R / 2) = 3 / 2 * (u * dec y.R) := by ring
    linarith
  have hhalf' : |dec (M.neg (M.div y.R (M.ofNat 2)))| ≤ dec y.R := by
    rw [hM.dec_neg, abs_neg]; exact hhalf
  have htwo : |dec (M.ofNat 2) - 2| ≤ 3 * u := by
    have h := abs_sub_le_of_isRoundingOf_aux (hM.ofNat 2)
      (by push_cast; rw [abs_two]; exact hΩ2) hu hτ₀
    push_cast at h
    rw [abs_two, abs_sub_comm] at h
    have : u * τ ≤ u * 1 := mul_le_mul_of_nonneg_left (by linarith) hu
    linarith
  -- Event I: the ideal shift is not an eigenvalue
  have hc : ∀ x ∈ spectrum ℝ (decodeMatrix dec y.A), x ≠ dec y.R / y.ℓ * smp.1 := by
    intro x hx hxc
    have := hI x hx
    rw [hxc, sub_self, abs_zero] at this
    linarith
  have hkpr := hM.min_toNat_eighProjector_eq_inertiaPos (N := N) (signFuel := signFuel)
    (R₀ := R₀) hμM hu hA hR hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol husign hfuel hτ₀ hτ hΩ hk2 hint
    hv hI
  obtain ⟨hPp, hPm⟩ := hM.specNorm_sub_decodeMatrix_eighProjectors_le_of_le_eq_false (N := N)
    (signFuel := signFuel) (R₀ := R₀) hμM hu hA hR hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol
    husign hfuel hτ₀ hτ hΩ hint hv hI
  have hk1 : 1 ≤ y.k := by omega
  have hη3 : (2 + dec β) * ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)) / 3 ≤
      (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) := by
    have := mul_le_mul_of_nonneg_right (by linarith : 2 + dec β ≤ 3) hη0.le
    linarith
  -- unfold the step
  unfold eighStep at hsplit
  rw [if_neg (by omega), if_neg (by simp [hint])] at hsplit
  dsimp only at hsplit
  split_ifs at hsplit with h1 h2
  cases hsplit
  refine ⟨hσ, ?_, ?_⟩
  · -- the positive side
    obtain ⟨V, hV, hVV, hsp⟩ := exists_frame_pos_eighSplit_aux hA hR hc hkpr.symm
    have hr0 : 0 < min y.k (M.toNat (M.add (M.traceRe (M.hermScale (M.hermShift
        (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
          (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) (M.neg M.one)) (M.ofNat 2)))
        (M.div M.one (M.ofNat 2)))) := Nat.pos_of_ne_zero h2
    have hrk := lt_of_le_of_ne (min_le_left _ _) h1
    obtain ⟨hGt, hσG⟩ := hII true _ V hr0 hrk hV (by rw [if_pos rfl, one_smul]; exact hVV)
    have hP' := hPp
    rw [specNorm_sub_comm, ← hVV] at hP'
    obtain ⟨W, hW, hWb⟩ := exists_hasOrthonormalCols_specNorm_sub_deflate_eighSplit_aux hM hr0
      hrk.le hV hP' hβ.le (by linarith) hGt hx0 (hσG hrk.le) htx (by linarith) hdefl hτ₀ hτx hΩt
    refine ⟨V, hV, hVV, hsp, W, hW, hWb.trans hη3, ?_⟩
    exact specNorm_decodeMatrix_compress_sub_le_eighSplit_aux hM hk1 hrk.le hu huβ hμM hμ hsk
      hβ.le hβη hη0 hη1 hR0 hτ₀ hkτR hΩ4 hA hR hV hW hWb htwo hhalf
  · -- the negative side
    have hfr : ∀ m : ℕ, inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) = m → m ≤ y.k →
        ∃ V : Matrix (Fin y.k) (Fin (y.k - m)) ℂ, HasOrthonormalCols V ∧
          V * Vᴴ = (2⁻¹ : ℝ) • (1 - cfc Real.sign (decodeMatrix dec y.A -
            (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))) ∧
          spectrum ℝ (Vᴴ * decodeMatrix dec y.A * V) ⊆
            Set.Icc (-dec y.R) (dec y.R / y.ℓ * smp.1) :=
      fun m hm hmk => exists_frame_neg_eighSplit_aux hA hR hc (by omega)
    obtain ⟨V, hV, hVV, hsp⟩ := hfr _ hkpr.symm (min_le_left _ _)
    have hr0 := Nat.sub_pos_of_lt (lt_of_le_of_ne (min_le_left _ _) h1)
    have hrk : y.k - _ < y.k := Nat.sub_lt (by omega) (Nat.pos_of_ne_zero h2)
    obtain ⟨hGt, hσG⟩ := hII false _ V hr0 hrk hV
      (by rw [if_neg (by simp), neg_one_smul, ← sub_eq_add_neg]; exact hVV)
    have hP' := hPm
    rw [specNorm_sub_comm, ← hVV] at hP'
    obtain ⟨W, hW, hWb⟩ := exists_hasOrthonormalCols_specNorm_sub_deflate_eighSplit_aux hM hr0
      hrk.le hV hP' hβ.le (by linarith) hGt hx0 (hσG hrk.le) htx (by linarith) hdefl hτ₀ hτx hΩt
    refine ⟨V, hV, hVV, hsp, W, hW, hWb.trans hη3, ?_⟩
    have hC := specNorm_decodeMatrix_compress_sub_le_eighSplit_aux hM hk1 hrk.le hu huβ hμM hμ hsk
      hβ.le hβη hη0 hη1 hR0 hτ₀ hkτR hΩ4 hA hR hV hW hWb htwo hhalf'
    rwa [hM.dec_neg, neg_smul, sub_neg_eq_add] at hC


-- copied from module (renamed)
private theorem le_eq_false_and_eq_of_eighChild_eq_some_eb1a {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) {N signFuel : ℕ} {R₀ β : F} {x y : EighNode F}
    {smp : EighSample Su Sg N} {b : Bool} (h : eighChild M N signFuel R₀ β x smp b = some y) :
    M.le x.R (M.mul x.ε R₀) = false ∧ y.R = (eighNextParams M x.R x.ε x.ℓ).1 ∧
      y.ε = (eighNextParams M x.R x.ε x.ℓ).2 ∧ y.ℓ = x.ℓ + 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hle
    rw [Bool.not_eq_false] at hle
    have hst : ∃ U d, eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ smp = .leaf U d := by
      unfold eighStep
      by_cases hk : x.k ≤ 1
      · rw [if_pos hk]; exact ⟨_, _, rfl⟩
      · rw [if_neg hk, if_pos hle]; exact ⟨_, _, rfl⟩
    obtain ⟨U, d, hst⟩ := hst
    simp [eighChild, hst] at h
  · unfold eighChild at h
    split at h
    · simp at h
    · split_ifs at h; cases h; exact ⟨rfl, rfl, rfl⟩
    · split_ifs at h <;> cases h <;> exact ⟨rfl, rfl, rfl⟩

/-- A Hermitian matrix between $a\mathbf{I}$ and $b\mathbf{I}$ is within $m$ of $c\mathbf{I}$ when
$b - c \le m$ and $c - a \le m$. -/
private theorem specNorm_sub_smul_one_le_of_le_eb1a {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) {a b c m : ℝ} (h₁ : a • (1 : Matrix n n ℂ) ≤ X)
    (h₂ : X ≤ b • (1 : Matrix n n ℂ)) (hb : b - c ≤ m) (ha : c - a ≤ m) (hm : 0 ≤ m) :
    specNorm (X - c • (1 : Matrix n n ℂ)) ≤ m := by
  refine (hX.sub (isHermitian_real_smul_one c)).specNorm_le_of_le_smul_one hm ?_ ?_
  · have h := (smul_one_le_smul_one (n := n) (𝕜 := ℂ) (by linarith : c - m ≤ a)).trans h₁
    rw [sub_smul] at h
    rw [le_sub_iff_add_le]
    simpa [neg_add_eq_sub] using h
  · have h := h₂.trans (smul_one_le_smul_one (n := n) (𝕜 := ℂ) (by linarith : b ≤ m + c))
    rw [add_smul] at h
    rw [sub_le_iff_le_add]
    exact h

/-- A Hermitian matrix with spectrum in $[a, b]$ lies between $a\mathbf{I}$ and $b\mathbf{I}$. -/
private theorem smul_one_le_and_le_smul_one_of_spectrum_subset_eb1a {n : Type*} [Fintype n]
    [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) {a b : ℝ}
    (h : spectrum ℝ X ⊆ Set.Icc a b) :
    a • (1 : Matrix n n ℂ) ≤ X ∧ X ≤ b • (1 : Matrix n n ℂ) := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
    exact ⟨le_of_eq (Subsingleton.elim _ _), le_of_eq (Subsingleton.elim _ _)⟩
  · constructor
    · obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n := ⟨Fintype.card n - 1, by omega⟩
      exact (smul_one_le_smul_one (h (hX.eigenvalue_mem_spectrum (by omega : k < _))).1).trans
        (hX.eigenvalue_last_smul_one_le hk)
    · exact hX.le_eigenvalue_zero_smul_one.trans
        (smul_one_le_smul_one (h (hX.eigenvalue_mem_spectrum h0)).2)

open scoped ComplexOrder in
/-- All eigenvalues above $c$: $c\mathbf{I} \preceq \mathbf{X}$ when $i_+(\mathbf{X} -
c\mathbf{I})$ is the size. -/
private theorem smul_one_le_of_inertiaPos_eq_card_eb1a {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) {c : ℝ}
    (h : inertiaPos (X - c • (1 : Matrix n n ℂ)) = Fintype.card n) :
    c • (1 : Matrix n n ℂ) ≤ X := by
  have hB : (X - c • (1 : Matrix n n ℂ)).IsHermitian := hX.sub (isHermitian_real_smul_one _)
  exact Matrix.le_iff.mpr (hB.posDef_iff_inertiaPos_eq_card.mpr h).posSemidef

/-- No eigenvalue above $c$: $\mathbf{X} \preceq c\mathbf{I}$ when $i_+(\mathbf{X} - c\mathbf{I})
= 0$. -/
private theorem le_smul_one_of_inertiaPos_eq_zero_eb1a {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) {c : ℝ} (hn : 0 < Fintype.card n)
    (h : inertiaPos (X - c • (1 : Matrix n n ℂ)) = 0) :
    X ≤ c • (1 : Matrix n n ℂ) := by
  have hB : (X - c • (1 : Matrix n n ℂ)).IsHermitian := hX.sub (isHermitian_real_smul_one _)
  have hpos : ¬ 0 < inertiaPos (X - c • (1 : Matrix n n ℂ)) := by rw [h]; exact lt_irrefl 0
  rw [hB.lt_inertiaPos_iff] at hpos
  have hev : eigenvalue (X - c • (1 : Matrix n n ℂ)) 0 ≤ 0 :=
    le_of_not_gt fun hc => hpos ⟨hn, hc⟩
  have h0 := hB.le_eigenvalue_zero_smul_one.trans (smul_one_le_smul_one (n := n) (𝕜 := ℂ) hev)
  rw [zero_smul] at h0
  exact sub_nonpos.mp h0

/-- The triangle inequality in the form $\|\mathbf{Z}\|_2 \le \|\mathbf{Y}\|_2 +
\|\mathbf{Z} - \mathbf{Y}\|_2$. -/
private theorem specNorm_le_add_specNorm_sub_eb1a {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq q] (Z Y : Matrix p q ℂ) : specNorm Z ≤ specNorm Y + specNorm (Z - Y) := by
  have h := specNorm_add_le Y (Z - Y)
  rwa [add_sub_cancel] at h

/-- The stored half window $\mathrm{fl}(R/\mathrm{fl}(2))$. -/
private theorem abs_dec_div_ofNat_two_sub_le_eb1a {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hu : 0 ≤ u) (hu1 : u ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 8) {R : F}
    (hRτ : 7 * τ ≤ dec R) (hΩ : 2 * dec R + 4 ≤ Ω) :
    |dec (M.div R (M.ofNat 2)) - dec R / 2| ≤ 3 * u * (dec R / 2) := by
  have h2 := abs_le.mp (abs_sub_le_of_isRoundingOf_aux (hM.ofNat 2)
    (by norm_num; linarith) hu hτ₀)
  push_cast at h2
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  set t := dec (M.ofNat 2) with ht
  have ht1 : 2 - 2.2 * u ≤ t := by linarith
  have ht2 : t ≤ 2 + 2.2 * u := by linarith
  have ht0 : 0 < t := by linarith
  have hR0 : 0 ≤ dec R := by linarith
  have hq : |dec R / t - dec R / 2| ≤ 0.6 * u * dec R := by
    rw [div_sub_div _ _ ht0.ne' (by norm_num), abs_div, abs_of_pos (mul_pos ht0 two_pos),
      div_le_iff₀ (mul_pos ht0 two_pos), abs_le]
    have e1 := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hu hR0)
    have e2 := mul_le_mul_of_nonneg_left ht2 (mul_nonneg hu hR0)
    have e3 := mul_le_mul_of_nonneg_left ht1 hR0
    have e4 := mul_le_mul_of_nonneg_left ht2 hR0
    have e5 := mul_le_mul_of_nonneg_left hu1 (mul_nonneg hu hR0)
    constructor <;> nlinarith
  have hq' := abs_le.mp hq
  have hRt : dec R / t ≤ 0.51 * dec R := by
    rw [div_le_iff₀ ht0]; nlinarith
  have hRt0 : 0 ≤ dec R / t := div_nonneg hR0 ht0.le
  have hz := abs_le.mp (abs_sub_le_of_isRoundingOf_aux (hM.div R (M.ofNat 2) ht0.ne')
    (by rw [abs_of_nonneg hRt0]; linarith) hu hτ₀)
  rw [abs_of_nonneg hRt0] at hz
  have := mul_le_mul_of_nonneg_left hRt hu
  have := mul_le_mul_of_nonneg_left hRτ hu
  rw [abs_le]; constructor <;> nlinarith

/-- The real arithmetic of the lower bound on the next window. -/
private theorem le_of_isRoundingOf_eighNextParams_fst_eb1a {u τ Ω m t L a1 a2 c p r : ℝ}
    (hu : 0 ≤ u) (hum : u * m ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 8) (hm : 20 ≤ m)
    (hrτ : 7 * τ ≤ r) (hΩ : 2 * r + 2 * m + 4 ≤ Ω)
    (ht : IsRoundingOf u τ Ω 2 t) (hL : IsRoundingOf u τ Ω m L)
    (ha1 : t ≠ 0 → IsRoundingOf u τ Ω (1 / t) a1) (ha2 : L ≠ 0 → IsRoundingOf u τ Ω (t / L) a2)
    (hc : IsRoundingOf u τ Ω (a1 + a2) c) (hp : IsRoundingOf u τ Ω (c * r) p) :
    (1 / 2 + 2 / m) * r - 4 * u * r ≤ p := by
  have rnd : ∀ {a z : ℝ}, IsRoundingOf u τ Ω a z → 0 ≤ a → a ≤ Ω →
      a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) := fun h ha0 ha => by
    have := abs_le.mp (abs_sub_le_of_isRoundingOf_aux h (by rwa [abs_of_nonneg ha0]) hu hτ₀)
    rw [abs_of_nonneg ha0] at this
    constructor <;> linarith [this.1, this.2]
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
private theorem le_dec_eighNextParams_fst_eb1a {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (R e : F) {ℓ : ℕ} (hu : 0 ≤ u) (huℓ : u * ℓ ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 8)
    (hℓ : 20 ≤ ℓ) (hRτ : 7 * τ ≤ dec R) (hΩ : 2 * dec R + 2 * ℓ + 4 ≤ Ω) :
    (1 / 2 + 2 / (ℓ : ℝ)) * dec R - 4 * u * dec R ≤ dec (eighNextParams M R e ℓ).1 := by
  have h2 := hM.ofNat 2
  push_cast at h2
  have hm' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  exact le_of_isRoundingOf_eighNextParams_fst_eb1a hu huℓ hτ₀ hτ1 hm' hRτ hΩ h2 (hM.ofNat ℓ)
    (fun h => hM.dec_one ▸ hM.div _ _ h) (fun h => hM.div _ _ h) (hM.add _ _) (hM.mul _ _)

/-- The deflation accuracy $\eta = (1 - 1/\ell)\varepsilon/(5\ell)$ has
$0 \le \eta\ell \le 1/40$. -/
private theorem eta_mul_le_eb1a {ε : ℝ} {ℓ : ℕ} (hℓ : 20 ≤ ℓ) (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8) :
    0 ≤ (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) ∧ (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) * ℓ ≤ 1 / 40 := by
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have h1 : 1 / (ℓ : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h0 : 0 ≤ 1 / (ℓ : ℝ) := by positivity
  refine ⟨div_nonneg (mul_nonneg (by linarith) hε.le) (by positivity), ?_⟩
  have e : (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) * ℓ = (1 - 1 / (ℓ : ℝ)) * ε / 5 := by
    field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_right (by linarith : 1 - 1 / (ℓ : ℝ) ≤ 1) hε.le
  linarith

/-- The unit roundoff is tiny against the depth counter: $u\ell \le 10^{-5}$. -/
private theorem u_mul_le_eb1a {u R w β ε ρ μ : ℝ} {k ℓ : ℕ} (hk : 1 ≤ k) (hℓ : 20 ≤ ℓ)
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8) (hρ₁ : ρ ≤ 1) (hw : 0 < w) (hwR : w ≤ R) (hβ : 0 < β)
    (hβtol : β ≤ bisectionSignTol k ε ρ ℓ) (hμ : 0 ≤ μ) (hu : 0 ≤ u)
    (husign : 640 * k * √(k : ℝ) * (8 + μ) *
      (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) * u ≤ w / (4 * R) * β) :
    u * ℓ ≤ 1 / 100000 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq1 : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hkk1 : (1 : ℝ) ≤ k * √(k : ℝ) := by nlinarith
  have hR0 : 0 < R := hw.trans_le hwR
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  obtain ⟨hη0, hηℓ⟩ := eta_mul_le_eb1a hℓ hε hε₁
  set η := (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) with hη
  have hβη : β ≤ η := by
    refine hβtol.trans ?_
    unfold bisectionSignTol
    rw [← hη]
    have hρ' : √ρ ≤ 1 := Real.sqrt_le_one.mpr hρ₁
    have hL := Real.sqrt_nonneg (2 * Real.log (4 / ρ))
    have hD : 1 ≤ 36 * k * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ))) := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hρ' hη0, mul_le_mul_of_nonneg_left hD hη0]
  have hβ1 : β ≤ 1 / 800 := by
    have : η ≤ 1 / 800 := by nlinarith
    linarith
  have hNs := newtonSchulzSteps_nonneg_aux (s := w / (8 * R)) (ε := β / (16 * k))
    (by positivity) (by rw [div_le_iff₀ (by positivity)]; linarith) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  have hw4 : w / (4 * R) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hu5 : 5120 * u ≤ β / 4 := by
    have h1 : 5120 * u ≤ 640 * k * √(k : ℝ) * (8 + μ) *
        (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) * u := by
      have := mul_le_mul (by linarith : (8 : ℝ) ≤ 8 + μ) (by linarith : (1 : ℝ) ≤
        newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) zero_le_one
        (by linarith)
      have h2 : 1 * (8 * 1) ≤ (k * √(k : ℝ)) * ((8 + μ) *
          (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1)) :=
        mul_le_mul hkk1 this (by norm_num) (by positivity)
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 640 * u)
      nlinarith
    have := mul_le_mul_of_nonneg_right hw4 hβ.le
    linarith
  have := mul_le_mul_of_nonneg_right hβη (by linarith : (0 : ℝ) ≤ ℓ)
  have := mul_le_mul_of_nonneg_right hu5 (by linarith : (0 : ℝ) ≤ ℓ)
  nlinarith

/-- The window is above the floor when the leaf test fails: $7\tau \le R$. -/
private theorem seven_mul_le_of_le_eq_false_eb1a {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    {R e R₀ : F} (hu : 0 ≤ u) (hu1 : u ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) {k : ℕ} (hk : 2 ≤ k)
    (hτ : τ * (4 * k * √(k : ℝ)) ≤ dec e * dec R₀) (he : 0 < dec e) (he1 : dec e ≤ 1)
    (hR₀ : 0 < dec R₀) (hΩ : dec R₀ ≤ Ω) (hint : M.le R (M.mul e R₀) = false) :
    7 * τ ≤ dec R := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq1 : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have h8 : 8 * τ ≤ dec e * dec R₀ := by
    have : (8 : ℝ) ≤ 4 * k * √(k : ℝ) := by nlinarith
    nlinarith
  have heR0 : 0 ≤ dec e * dec R₀ := by positivity
  have heR := mul_le_of_le_one_left hR₀.le he1
  have hm := abs_le.mp (abs_sub_le_of_isRoundingOf_aux (hM.mul e R₀)
    (by rw [abs_of_nonneg heR0]; linarith) hu hτ₀)
  rw [abs_of_nonneg heR0] at hm
  have hrm : dec (M.mul e R₀) < dec R := by
    rw [← not_le, ← hM.le_iff]; simp [hint]
  have := mul_le_mul_of_nonneg_left h8 hu
  have := mul_le_mul_of_nonneg_left hu1 hτ₀
  nlinarith

/-- **The children of a good node satisfy the node invariant**: under the node hypotheses of
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample` (without
the children's guarantee), every child $y'$ of the node (`NLAlib.eighChild`) has a Hermitian matrix
with $\|\mathbf{A}'\|_2 \le R'$, its own window. [Shah2024, proof of Lemma 4.1], (4.10)–(4.13).
Proof: leaves have no child. A shift child (all eigenvalues on one side of $c'$, by
`NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub` and the inertia) has
spectrum of $\mathbf{A} \mp (R/2)\mathbf{I}$ in $[-(1/2 + 1/\ell)R, (1/2 + 1/\ell)R]$ since $\lvert
c'\rvert \le R/\ell$; the diagonal rounding
(`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_le`,
`NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_hermFrom`) gives $\|\mathbf{A}'\|_2 \le
(1/2 + 1/\ell)R + 1.06uR$ against $R' \ge (1/2 + 2/\ell)R - 2.5uR$ (`NLAlib.eighNextParams`). A
split child: Hermitian by `NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_hermFrom`; for
the norm,
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_eighStep_eq_split`
gives the compression
$\mathbf{W}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}}\mathbf{A}\mathbf{V}\mathbf{W}$ with spectrum in
$[c', R]$ (resp. $[-R, c']$), so its shift by $\mp\sigma$ has norm at most $(1/2 + 1/\ell)R + 3uR$,
and the child within $(2 + 2\eta)R\eta \le 0.06R/\ell$ of it. M, about 60 lines. -/
theorem FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some
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
    {smp : EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w (√(ρ / 2) / y.k)
        (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y smp)
    {b : Bool} {y' : EighNode F} (hy' : eighChild M N signFuel R₀ β y smp b = some y') :
    (decodeMatrix dec y'.A).IsHermitian ∧ specNorm (decodeMatrix dec y'.A) ≤ dec y'.R := by
  have hk : 2 ≤ y.k := by
    by_contra hk
    simp [eighChild, eighStep, show y.k ≤ 1 by omega] at hy'
  obtain ⟨hint, -, -, -⟩ := le_eq_false_and_eq_of_eighChild_eq_some_eb1a M hy'
  obtain ⟨⟨hv, hI⟩, -⟩ := hgood hk hint
  have hk1 : 1 ≤ y.k := by omega
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hℓ
  have huℓ := u_mul_le_eb1a hk1 hℓ hε hε₁ hρ₁ hw hwR hβ hβtol hμM hu husign
  obtain ⟨hη0, hηℓ⟩ := eta_mul_le_eb1a hℓ hε hε₁
  obtain ⟨-, -, hkτ⟩ := bisection_small_aux hk1 hℓ hε hε₁ hρ₁ hw hwR hβ hβtol hμM hu husign hτ₀ hτ
  have hk2 : (2 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hu1 : u ≤ 1 / 1000 := by linarith [mul_le_mul_of_nonneg_left hℓ' hu]
  have hτ1 : τ ≤ 1 / 8 := by linarith [mul_le_mul_of_nonneg_right hk2 hτ₀]
  have hsqL := Real.sqrt_nonneg (Real.log (4 / ρ))
  have hRτ : 7 * τ ≤ dec y.R := seven_mul_le_of_le_eq_false_eb1a hM hu hu1 hτ₀ hk
    (hτ.trans (min_le_right _ _)) hε (by linarith) hR₀ (by linarith) hint
  have hR0 : 0 < dec y.R := hw.trans_le hwR
  have hR' := le_dec_eighNextParams_fst_eb1a hM y.R y.ε hu (by linarith) hτ₀ hτ1 hℓ hRτ
    (by linarith)
  have hhalf := abs_dec_div_ofNat_two_sub_le_eb1a hM hu hu1 hτ₀ hτ1 hRτ (by linarith)
  have hkp := hM.min_toNat_eighProjector_eq_inertiaPos (N := N) (signFuel := signFuel)
    (R₀ := R₀) hμM hu hA hR hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol husign hfuel hτ₀ hτ hΩ hk hint
    hv hI
  -- the ideal shift, the window, the floor and the roundoff
  set X := decodeMatrix dec y.A with hX
  set D := dec y.R / y.ℓ with hD
  set h := dec (M.div y.R (M.ofNat 2)) with hh
  have hD0 : 0 ≤ D := by positivity
  have hDℓ : D * y.ℓ = dec y.R := by rw [hD]; field_simp
  have hD20 : D ≤ dec y.R / 20 := by linarith [mul_le_mul_of_nonneg_left hℓ' hD0]
  have hc'1 : -D ≤ D * smp.1 := by linarith [mul_le_mul_of_nonneg_left hv.1 hD0]
  have hc'2 : D * smp.1 ≤ D := by linarith [mul_le_mul_of_nonneg_left hv.2 hD0]
  have huR : u * dec y.R ≤ D / 100000 := by
    have := mul_le_mul_of_nonneg_right huℓ hD0
    rw [mul_assoc, mul_comm (y.ℓ : ℝ) D, hDℓ] at this
    linarith
  have huR0 : 0 ≤ u * dec y.R := mul_nonneg hu hR0.le
  have huτR := mul_le_mul_of_nonneg_left hRτ hu
  have e2 : (1 / 2 + 2 / (y.ℓ : ℝ)) * dec y.R = dec y.R / 2 + 2 * D := by rw [hD]; ring
  rw [e2] at hR'
  obtain ⟨hh1, hh2⟩ := abs_le.mp hhalf
  set m := dec y.R / 2 + D + 1.5 * (u * dec y.R) with hm
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 0.6 * dec y.R := by linarith
  have hum := mul_le_mul_of_nonneg_left hm1 hu
  set η := (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) with hη
  have hηR : (2 + 2 * η) * dec y.R * η ≤ D / 19 := by
    have hη1 : η ≤ 1 / 800 := by linarith [mul_le_mul_of_nonneg_left hℓ' hη0]
    have e : (2 + 2 * η) * dec y.R * η = (2 + 2 * η) * (η * y.ℓ) * D := by rw [← hDℓ]; ring
    rw [e]
    have := mul_le_mul (by linarith : 2 + 2 * η ≤ 2.0025) hηℓ (by positivity) (by norm_num)
    have := mul_le_mul_of_nonneg_right this hD0
    linarith
  have hB : (X - (D * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)).IsHermitian :=
    hA.sub (isHermitian_real_smul_one _)
  have hXR : X ≤ dec y.R • (1 : Matrix (Fin y.k) (Fin y.k) ℂ) := hA.le_smul_one_of_specNorm_le hR
  have hXR' : (-dec y.R) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ) ≤ X := by
    rw [neg_smul]; exact hA.neg_smul_one_le_of_specNorm_le hR
  -- a shift child: the rounded diagonal shift
  have hshift : ∀ s : F, specNorm (X - dec s • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) ≤ m →
      (decodeMatrix dec (M.hermShift y.A s)).IsHermitian ∧
        specNorm (decodeMatrix dec (M.hermShift y.A s)) ≤ dec (eighNextParams M y.R y.ε y.ℓ).1 := by
    intro s hs
    refine ⟨hM.isHermitian_decodeMatrix_hermFrom _ _, ?_⟩
    have hS := hM.specNorm_sub_decodeMatrix_hermShift_le hu hA s (by linarith)
    have hmax : max (specNorm (X - dec s • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))) τ ≤ m + τ :=
      max_le (by linarith) (by linarith)
    have := mul_le_mul_of_nonneg_left hmax hu
    have htri := specNorm_sub_le (X - dec s • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))
      ((X - dec s • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) - decodeMatrix dec (M.hermShift y.A s))
    rw [sub_sub_cancel] at htri
    linarith
  unfold eighChild eighStep at hy'
  rw [if_neg (by omega), if_neg (by simp [hint])] at hy'
  dsimp only at hy'
  split_ifs at hy' with h1 h2 h3 h4
  · -- the shift child on the positive side
    simp only [h2, if_true, Option.some.injEq] at hy'
    subst hy'
    rw [hkp] at h1
    have hlo := smul_one_le_of_inertiaPos_eq_card_eb1a hA (by rw [Fintype.card_fin]; exact h1)
    exact hshift _ (specNorm_sub_smul_one_le_of_le_eb1a hA hlo hXR (by linarith) (by linarith) hm0)
  · simp [h2] at hy'
  · simp [h4] at hy'
  · -- the shift child on the negative side
    simp only [show b = false by simpa using h4, if_true, Option.some.injEq] at hy'
    subst hy'
    rw [hkp] at h3
    have hhi := le_smul_one_of_inertiaPos_eq_zero_eb1a hA (by rw [Fintype.card_fin]; omega) h3
    refine hshift _ (specNorm_sub_smul_one_le_of_le_eb1a hA hXR' hhi ?_ ?_ hm0)
    · rw [hM.dec_neg]; linarith
    · rw [hM.dec_neg]; linarith
  all_goals
    obtain ⟨-, hP, hQ⟩ := hM.exists_frames_of_eighStep_eq_split_aux hμM hμQ
      hcN hu hA hR hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol husign hudefl hfuel hτ₀ hτ hΩ hgood
      (by
        unfold eighStep
        rw [if_neg (by omega), if_neg (by simp [hint])]
        dsimp only
        rw [if_neg h1, if_neg h3])
    rw [← hη, ← hX, ← hD, ← hh] at hP hQ
    simp only [Option.some.injEq] at hy'
    subst hy'
  · -- the split child on the positive side
    obtain ⟨V, hV, -, hspec, W, hW, -, hAp⟩ := hP
    have hC : (Vᴴ * X * V).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul V hA
    obtain ⟨hlo, hhi⟩ := smul_one_le_and_le_smul_one_of_spectrum_subset_eb1a hC hspec
    have hCn := specNorm_sub_smul_one_le_of_le_eb1a hC hlo hhi (c := h) (m := m)
      (by linarith) (by linarith) hm0
    have hWC : specNorm (Wᴴ * (Vᴴ * X * V) * W - h • (1 : Matrix _ _ ℂ)) ≤ m := by
      have e : Wᴴ * (Vᴴ * X * V) * W - h • (1 : Matrix _ _ ℂ) =
          Wᴴ * (Vᴴ * X * V - h • (1 : Matrix _ _ ℂ)) * W := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          show Wᴴ * W = 1 from hW]
      rw [e]; exact (hW.specNorm_conjTranspose_mul_mul_le _).trans hCn
    refine ⟨?_, ?_⟩
    · unfold FloatMachine.hermShift; exact hM.isHermitian_decodeMatrix_hermFrom _ _
    · refine ((specNorm_le_add_specNorm_sub_eb1a _ _).trans (add_le_add hWC hAp)).trans ?_
      show m + (2 + 2 * η) * dec y.R * η ≤ dec (eighNextParams M y.R y.ε y.ℓ).1
      linarith
  · -- the split child on the negative side
    obtain ⟨V, hV, -, hspec, W, hW, -, hAm⟩ := hQ
    dsimp only
    have hC : (Vᴴ * X * V).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul V hA
    obtain ⟨hlo, hhi⟩ := smul_one_le_and_le_smul_one_of_spectrum_subset_eb1a hC hspec
    have hCn := specNorm_sub_smul_one_le_of_le_eb1a hC hlo hhi (c := -h) (m := m)
      (by linarith) (by linarith) hm0
    have hWC : specNorm (Wᴴ * (Vᴴ * X * V) * W + h • (1 : Matrix _ _ ℂ)) ≤ m := by
      have e : Wᴴ * (Vᴴ * X * V) * W + h • (1 : Matrix _ _ ℂ) =
          Wᴴ * (Vᴴ * X * V - (-h) • (1 : Matrix _ _ ℂ)) * W := by
        rw [neg_smul, sub_neg_eq_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one, show Wᴴ * W = 1 from hW]
      rw [e]; exact (hW.specNorm_conjTranspose_mul_mul_le _).trans hCn
    refine ⟨?_, ?_⟩
    · unfold FloatMachine.hermShift; exact hM.isHermitian_decodeMatrix_hermFrom _ _
    · refine ((specNorm_le_add_specNorm_sub_eb1a _ _).trans (add_le_add hWC hAm)).trans ?_
      show m + (2 + 2 * η) * dec y.R * η ≤ dec (eighNextParams M y.R y.ε y.ℓ).1
      linarith

/-- **A split node: frames, deflated bases and compressions**: under the node hypotheses of
`NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some`, if the node's
step (`NLAlib.eighStep`) is a split with sizes $k_+$, $k - k_+$, bases $\mathbf{Q}_\pm$, stored
children $\mathbf{A}_\pm$ and stored shift $\sigma$, then $\sigma$ is within $3u$ (relative) of
$R/2$ and, with $\eta = (1 - 1/\ell)\varepsilon/(5\ell)$ and $c' = (R/\ell)v$, each side has an
orthonormal frame $\mathbf{V}$ of the true spectral projector
$\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} - c'\mathbf{I}))$ whose compression has
spectrum in $[c', R]$ (resp. $[-R, c']$), a unitary $\mathbf{W}$ with
$\|\mathbf{V}\mathbf{W} - \mathbf{Q}_\pm\|_2 \le \eta$, and
$\|\mathbf{A}_\pm - (\mathbf{W}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}}\mathbf{A}\mathbf{V}\mathbf{W}
\mp \sigma\mathbf{I})\|_2 \le (2 + 2\eta)R\eta$. [Shah2024, proof of Lemma 4.1], (4.10)–(4.13).
(The shift bound is $3u$ rather than $u$: $\mathrm{fl}(2)$ is a rounded conversion.)
Proof: the split and the ranks come from
`NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub`'s argument, here via
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le` and the inertia;
the frames from `Matrix.IsHermitian.exists_hasOrthonormalCols_mul_conjTranspose_eq` (for the minus
side applied to $-\mathbf{A}$, $-c'$, with `NLAlib.inertiaNeg_eq_inertiaPos_neg` and
`Matrix.IsHermitian.inertiaPos_add_inertiaNeg` to identify $k - k_+$); deflation by
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le` with
$\mathbf{S} = \mathbf{I}_r$ ($6m\beta \le (2 + \beta)\eta/3 \le 0.67\eta$; its floor and range
hypotheses from `hτ` and `hΩ`, $\tau\sqrt k \le x/4$, $2(1 + \beta)t \le \Omega$); the compressions
through `NLAlib.FloatMachine.IsAccurate.decodeMatrix_conjTransposeMat`, the product contract,
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermAvg_le`,
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_le` and
`NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_hermFrom`. L, about 150 lines. -/
theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_eighStep_eq_split
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
    {smp : EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w (√(ρ / 2) / y.k)
        (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y smp)
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
  exact hM.exists_frames_of_eighStep_eq_split_aux hμM hμQ hcN hu hA hR
    hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol husign hudefl hfuel hτ₀ hτ hΩ hgood hsplit
/-- A rounding of a nonnegative number in range, with the floor as an absolute term. -/
private lemma le_and_le_of_isRoundingOf_eb1 {u τ Ω a z : ℝ} (h : IsRoundingOf u τ Ω a z)
    (ha0 : 0 ≤ a) (ha : a ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) :
    a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) := by
  have h1 := (h (by rwa [abs_of_nonneg ha0])).trans
    (mul_le_mul_of_nonneg_left (max_le_add_of_nonneg (abs_nonneg _) hτ) hu)
  rw [abs_of_nonneg ha0] at h1
  constructor <;> linarith [(abs_le.mp h1).1, (abs_le.mp h1).2]

/-- The real arithmetic of the next window of `NLAlib.eighNextParams`. -/
private lemma le_of_isRoundingOf_eighNextParams_fst_eb1 {u τ Ω m t L a1 a2 c p1 r : ℝ}
    (hu : 0 ≤ u) (hum : 500 * m * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1) (hm : 20 ≤ m)
    (hmΩ : 2 * m ≤ Ω) (hr : 0 ≤ r) (hrΩ : r ≤ Ω)
    (ht : IsRoundingOf u τ Ω 2 t) (hL : IsRoundingOf u τ Ω m L)
    (ha1 : t ≠ 0 → IsRoundingOf u τ Ω (1 / t) a1) (ha2 : L ≠ 0 → IsRoundingOf u τ Ω (t / L) a2)
    (hc : IsRoundingOf u τ Ω (a1 + a2) c) (hp1 : IsRoundingOf u τ Ω (c * r) p1) :
    p1 ≤ (1 / 2 + 2 / m) * (1 + 22 * u) * r + u * τ := by
  have rnd : ∀ {a z : ℝ}, IsRoundingOf u τ Ω a z → 0 ≤ a → a ≤ Ω →
      a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) :=
    fun h ha0 ha => le_and_le_of_isRoundingOf_eb1 h ha0 ha hu hτ₀
  have hm0 : 0 < m := by linarith
  obtain ⟨w, hw_def⟩ : ∃ w, w = 1 / m := ⟨_, rfl⟩
  have hwm : w * m = 1 := by rw [hw_def]; field_simp
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw20 : w ≤ 1 / 20 := by rw [hw_def, div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have hu' : u ≤ w / 500 := by
    have h := mul_le_mul_of_nonneg_left hum hw0.le
    have h' : w * (500 * m * u) = 500 * u * (w * m) := by ring
    rw [h', hwm] at h; linarith
  have hu1 : u ≤ 1 / 10000 := by linarith
  have huτ : u * τ ≤ u := mul_le_of_le_one_right hu hτ
  have huτ0 : 0 ≤ u * τ := mul_nonneg hu hτ₀
  have huu : u * u ≤ u / 10000 := by have := mul_le_mul_of_nonneg_left hu1 hu; linarith
  have huu0 : 0 ≤ u * u := mul_nonneg hu hu
  have huw' : u * w ≤ u / 20 := by have := mul_le_mul_of_nonneg_left hw20 hu; linarith
  have huw0 : 0 ≤ u * w := mul_nonneg hu hw0.le
  have hum1 : u * (w * m) = u := by rw [hwm, mul_one]
  have hum' : u * m ≤ 1 / 500 := by
    have := mul_le_mul_of_nonneg_right hu' hm0.le
    have h2 : w / 500 * m = (w * m) / 500 := by ring
    rw [h2, hwm] at this; linarith
  have hwuτ : w * (u * τ) ≤ u * τ := mul_le_of_le_one_left huτ0 (by linarith)
  -- the stored `2` and `ℓ`
  obtain ⟨ht1, ht2⟩ := rnd ht (by norm_num) (by linarith)
  obtain ⟨hL1, hL2⟩ := rnd hL hm0.le (by linarith)
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  have hwL1 : 1 - 2 * u ≤ w * L := by
    have := mul_le_mul_of_nonneg_left hL1 hw0.le; linarith
  have hwL2 : w * L ≤ 1 + 2 * u := by
    have := mul_le_mul_of_nonneg_left hL2 hw0.le; linarith
  -- `fl(1/2)`
  have hit1 : 1 / t ≤ 1 / 2 + u := by
    rw [div_le_iff₀ ht0]
    have := mul_le_mul_of_nonneg_left (by linarith : 2 - 3 * u ≤ t) (by linarith : 0 ≤ 1 / 2 + u)
    linarith
  have hit2 : 1 / 2 - u ≤ 1 / t := by
    rw [le_div_iff₀ ht0]
    have := mul_le_mul_of_nonneg_left (by linarith : t ≤ 2 + 3 * u) (by linarith : 0 ≤ 1 / 2 - u)
    linarith
  obtain ⟨ha11, ha12⟩ := rnd (ha1 ht0.ne') (one_div_nonneg.mpr ht0.le) (by linarith)
  have hut := mul_le_mul_of_nonneg_left hit1 hu
  have hA1 : a1 ≤ 1 / 2 + 3 * u := by linarith
  have hA1' : 1 / 2 - 3 * u ≤ a1 := by linarith
  -- `fl(2/ℓ)`
  have hq1 : t / L ≤ (2 + 8 * u) * w := by
    rw [div_le_iff₀ hL0, mul_assoc]
    have := mul_le_mul_of_nonneg_left hwL1 (by linarith : 0 ≤ 2 + 8 * u)
    linarith
  have hq0 : 0 ≤ t / L := div_nonneg ht0.le hL0.le
  have hq5 : t / L ≤ 1 / 5 := by linarith
  obtain ⟨ha21, ha22⟩ := rnd (ha2 hL0.ne') hq0 (by linarith)
  have huq := mul_le_mul_of_nonneg_left hq5 hu
  have huq0 := mul_nonneg hu hq0
  have hA2 : a2 ≤ 2 * w + 2 * u := by linarith
  have hA2' : -2 * u ≤ a2 := by linarith
  -- `fl(fl(1/2) + fl(2/ℓ))`
  obtain ⟨hc1, hc2⟩ := rnd hc (by linarith) (by linarith)
  have huS := mul_le_mul_of_nonneg_left (by linarith : a1 + a2 ≤ 61 / 100) hu
  have huS0 := mul_nonneg hu (by linarith : (0 : ℝ) ≤ a1 + a2)
  have hC : c ≤ (1 / 2 + 2 * w) * (1 + 14 * u) := by linarith
  have hC0 : 0 ≤ c := by linarith
  have hC1 : c ≤ 1 := by linarith
  obtain ⟨-, hp⟩ := rnd hp1 (mul_nonneg hC0 hr) (by linarith [mul_le_of_le_one_left hr hC1])
  have hK : 0 ≤ (1 / 2 + 2 * w) * r := mul_nonneg (by linarith) hr
  have h22 : (1 + 14 * u) * (1 + u) ≤ 1 + 22 * u := by linarith
  have hcr : c * r ≤ (1 / 2 + 2 * w) * (1 + 14 * u) * r := mul_le_mul_of_nonneg_right hC hr
  have h1 := mul_le_mul_of_nonneg_right hcr (by linarith : (0 : ℝ) ≤ 1 + u)
  have h2 := mul_le_mul_of_nonneg_left h22 hK
  have : (2 : ℝ) / m = 2 * w := by rw [hw_def]; ring
  rw [this]
  linarith

/-- The real arithmetic of the next tolerance of `NLAlib.eighNextParams`. -/
private lemma le_and_le_of_isRoundingOf_eighNextParams_snd_eb1 {u τ Ω m L e1 d p2 e : ℝ}
    (hu : 0 ≤ u) (hum : 500 * m * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1) (hm : 20 ≤ m)
    (hmΩ : 2 * m ≤ Ω) (he : 0 ≤ e) (he₁ : e ≤ 1) (hL : IsRoundingOf u τ Ω m L)
    (he1 : L ≠ 0 → IsRoundingOf u τ Ω (1 / L) e1) (hd : IsRoundingOf u τ Ω (1 - e1) d)
    (hp2 : IsRoundingOf u τ Ω (d * e) p2) :
    (1 - 1 / m) * (1 - 9 * u) * e - u * τ ≤ p2 ∧ p2 ≤ (1 - 1 / m) * e + 7 * u * e + u * τ := by
  have rnd : ∀ {a z : ℝ}, IsRoundingOf u τ Ω a z → 0 ≤ a → a ≤ Ω →
      a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) :=
    fun h ha0 ha => le_and_le_of_isRoundingOf_eb1 h ha0 ha hu hτ₀
  have hm0 : 0 < m := by linarith
  obtain ⟨w, hw_def⟩ : ∃ w, w = 1 / m := ⟨_, rfl⟩
  have hwm : w * m = 1 := by rw [hw_def]; field_simp
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw20 : w ≤ 1 / 20 := by rw [hw_def, div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have hu' : u ≤ w / 500 := by
    have h := mul_le_mul_of_nonneg_left hum hw0.le
    have h' : w * (500 * m * u) = 500 * u * (w * m) := by ring
    rw [h', hwm] at h; linarith
  have hu1 : u ≤ 1 / 10000 := by linarith
  have huτ : u * τ ≤ u := mul_le_of_le_one_right hu hτ
  have huτ0 : 0 ≤ u * τ := mul_nonneg hu hτ₀
  have huu : u * u ≤ u / 10000 := by have := mul_le_mul_of_nonneg_left hu1 hu; linarith
  have huu0 : 0 ≤ u * u := mul_nonneg hu hu
  have huw' : u * w ≤ u / 20 := by have := mul_le_mul_of_nonneg_left hw20 hu; linarith
  have huw0 : 0 ≤ u * w := mul_nonneg hu hw0.le
  have hum1 : u * (w * m) = u := by rw [hwm, mul_one]
  have hum' : u * m ≤ 1 / 500 := by
    have := mul_le_mul_of_nonneg_right hu' hm0.le
    have h2 : w / 500 * m = (w * m) / 500 := by ring
    rw [h2, hwm] at this; linarith
  have hwuτ : w * (u * τ) ≤ u * τ := mul_le_of_le_one_left huτ0 (by linarith)
  -- the stored `2` and `ℓ`
  obtain ⟨hL1, hL2⟩ := rnd hL hm0.le (by linarith)
  have hL0 : 0 < L := by linarith
  have hwL1 : 1 - 2 * u ≤ w * L := by
    have := mul_le_mul_of_nonneg_left hL1 hw0.le; linarith
  have hwL2 : w * L ≤ 1 + 2 * u := by
    have := mul_le_mul_of_nonneg_left hL2 hw0.le; linarith
  -- `fl(1/ℓ)` and `fl(1 - fl(1/ℓ))`
  have hiL1 : 1 / L ≤ (1 + 3 * u) * w := by
    rw [div_le_iff₀ hL0, mul_assoc]
    have := mul_le_mul_of_nonneg_left hwL1 (by linarith : 0 ≤ 1 + 3 * u)
    linarith
  have hiL2 : (1 - 3 * u) * w ≤ 1 / L := by
    rw [le_div_iff₀ hL0, mul_assoc]
    have := mul_le_mul_of_nonneg_left hwL2 (by linarith : 0 ≤ 1 - 3 * u)
    linarith
  have hiL0 : 0 ≤ 1 / L := one_div_nonneg.mpr hL0.le
  have hiL10 : 1 / L ≤ 1 / 10 := by linarith
  obtain ⟨he11, he12⟩ := rnd (he1 hL0.ne') hiL0 (by linarith)
  have huL := mul_le_mul_of_nonneg_left hiL10 hu
  have huL0 := mul_nonneg hu hiL0
  have hE1 : e1 ≤ w + 2 * u := by linarith
  have hE1' : w - 2 * u ≤ e1 := by linarith
  obtain ⟨hd1, hd2⟩ := rnd hd (by linarith) (by linarith)
  have hue := mul_le_mul_of_nonneg_left (by linarith : 1 - e1 ≤ 1 - w + 2 * u) hu
  have hue' := mul_le_mul_of_nonneg_left (by linarith : 1 - w - 2 * u ≤ 1 - e1) hu
  have hD : (1 - w) * (1 - 5 * u) ≤ d := by linarith
  have hD' : d ≤ 1 - w + 5 * u := by linarith
  have hD0 : 0 ≤ d := by linarith
  have hD1 : d ≤ 1 := by linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨hp, -⟩ := rnd hp2 (mul_nonneg hD0 he) (by linarith [mul_le_one₀ hD1 he he₁])
    have hde : (1 - w) * (1 - 5 * u) * e ≤ d * e := mul_le_mul_of_nonneg_right hD he
    have h9 : (1 - w) * (1 - 9 * u) ≤ (1 - w) * ((1 - 5 * u) * (1 - u)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h1 := mul_le_mul_of_nonneg_right hde (by linarith : (0 : ℝ) ≤ 1 - u)
    have h2 := mul_le_mul_of_nonneg_right h9 he
    rw [← hw_def]
    linarith
  · obtain ⟨-, hp⟩ := rnd hp2 (mul_nonneg hD0 he) (by linarith [mul_le_one₀ hD1 he he₁])
    have hde : d * e ≤ (1 - w + 5 * u) * e := mul_le_mul_of_nonneg_right hD' he
    have hkey : (1 - w + 5 * u) * (1 + u) ≤ 1 - w + 7 * u := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hde (by linarith : (0 : ℝ) ≤ 1 + u)
    have h2 := mul_le_mul_of_nonneg_right hkey he
    rw [← hw_def]
    linarith

/-- One level of the machine's next window and tolerance (`NLAlib.eighNextParams`). -/
private lemma dec_eighNextParams_le_eb1 {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R ε : F} {m : ℕ}
    (hu : 0 ≤ u) (hum : 500 * (m : ℝ) * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1) (hm : 20 ≤ m)
    (hmΩ : 2 * (m : ℝ) ≤ Ω) (hR : 0 ≤ dec R) (hRΩ : dec R ≤ Ω) (hε : 0 ≤ dec ε)
    (hε₁ : dec ε ≤ 1) :
    dec (eighNextParams M R ε m).1 ≤ (1 / 2 + 2 / m) * (1 + 22 * u) * dec R + u * τ ∧
    (1 - 1 / m) * (1 - 9 * u) * dec ε - u * τ ≤ dec (eighNextParams M R ε m).2 ∧
    dec (eighNextParams M R ε m).2 ≤ (1 - 1 / m) * dec ε + 7 * u * dec ε + u * τ := by
  have h2 := hM.ofNat 2
  push_cast at h2
  have hm' : (20 : ℝ) ≤ m := by exact_mod_cast hm
  exact ⟨le_of_isRoundingOf_eighNextParams_fst_eb1 hu hum hτ₀ hτ hm' hmΩ hR hRΩ h2 (hM.ofNat m)
    (fun h => hM.dec_one ▸ hM.div _ _ h) (fun h => hM.div _ _ h) (hM.add _ _) (hM.mul _ _),
    le_and_le_of_isRoundingOf_eighNextParams_snd_eb1 hu hum hτ₀ hτ hm' hmΩ hε hε₁ (hM.ofNat m)
    (fun h => hM.dec_one ▸ hM.div _ _ h) (hM.dec_one ▸ hM.sub _ _) (hM.mul _ _)⟩


/-- The roundoff and the floor are small at a node. -/
private theorem node_small_eb1 {u τ ρ w R ε β μ R₀ : ℝ} {k ℓ : ℕ} (hk : 1 ≤ k)
    (hℓ : 20 ≤ ℓ) (hε : 0 < ε) (hρ₁ : ρ ≤ 1) (hw : 0 < w)
    (hwR : w ≤ R) (hβ : 0 < β) (hβtol : β ≤ bisectionSignTol k ε ρ ℓ) (hμ : 0 ≤ μ) (hu : 0 ≤ u)
    (husign : 640 * k * √(k : ℝ) * (8 + μ) *
      (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) * u ≤ w / (4 * R) * β)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * k * √(k : ℝ)) ≤ min (√(ρ / 2)) (ε * R₀)) (hε₁ : ε ≤ 1 / 8) :
    (ℓ : ℝ) * u * 1000000 ≤ ε ∧ (ℓ : ℝ) * (μ * u) * 100000 ≤ ε ∧ τ ≤ 1 / 4 ∧
      τ * 4 ≤ ε * R₀ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq1 : 1 ≤ √(k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hkk1 : (1 : ℝ) ≤ k * √(k : ℝ) := by nlinarith
  have hR0 : 0 < R := hw.trans_le hwR
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  -- the accuracy is at most `ε / (360 ℓ)`
  have hβℓ : β * ℓ ≤ ε / 360 := by
    refine (mul_le_mul_of_nonneg_right hβtol hℓ0.le).trans ?_
    unfold bisectionSignTol
    have h1 : (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) * ℓ ≤ ε / 5 := by
      have : (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) * ℓ = (1 - 1 / (ℓ : ℝ)) * ε / 5 := by
        field_simp
      rw [this]
      have : 0 ≤ 1 / (ℓ : ℝ) := by positivity
      nlinarith
    have h10 : 0 ≤ (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) * ℓ := by
      have : 1 / (ℓ : ℝ) ≤ 1 := by rw [div_le_one hℓ0]; linarith
      have : 0 ≤ 1 - 1 / (ℓ : ℝ) := by linarith
      positivity
    have hρ' : √ρ ≤ 1 := Real.sqrt_le_one.mpr hρ₁
    have hL := Real.sqrt_nonneg (2 * Real.log (4 / ρ))
    have hD : 72 ≤ 36 * k * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ))) := by nlinarith
    have hD0 : 0 < 36 * k * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ))) := by linarith
    have e : (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) * √ρ /
        (36 * k * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ)))) * ℓ =
        ((1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) * ℓ) * √ρ /
        (36 * k * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ)))) := by ring
    rw [e, div_le_iff₀ hD0]
    have := mul_le_mul h1 hρ' (Real.sqrt_nonneg _) (by positivity)
    nlinarith
  have hNs := newtonSchulzSteps_nonneg_aux (s := w / (8 * R)) (ε := β / (16 * k))
    (by positivity) (by rw [div_le_iff₀ (by positivity)]; linarith) (by positivity)
    (by
      have : β ≤ 1 / 7200 := by nlinarith
      rw [div_le_iff₀ (by positivity)]; nlinarith)
  have hw4 : w / (4 * R) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hw4β := mul_le_mul_of_nonneg_right hw4 hβ.le
  have hbig : 640 * (8 + μ) * u ≤ 640 * k * √(k : ℝ) * (8 + μ) *
      (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) * u := by
    have h0 : 0 ≤ 640 * (8 + μ) * u := by positivity
    have e : 640 * k * √(k : ℝ) * (8 + μ) *
      (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1) * u = (640 * (8 + μ) * u) *
        ((k * √(k : ℝ)) * (newtonSchulzSteps (w / (8 * R)) (β / (16 * k)) + 1)) := by ring
    rw [e]
    refine le_mul_of_one_le_right h0 ?_
    nlinarith
  have hmain : 640 * (8 + μ) * u ≤ β / 4 := by linarith
  have hu1 : u * 20480 ≤ β := by nlinarith
  have hμ1 : μ * u * 2560 ≤ β := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hu1 hℓ0.le
    nlinarith
  · have := mul_le_mul_of_nonneg_right hμ1 hℓ0.le
    nlinarith
  · have hs : √(ρ / 2) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    have := hτ.trans (min_le_left _ _)
    nlinarith
  · have := hτ.trans (min_le_right _ _)
    nlinarith

/-- The stored half window `fl(R / fl(2))`. -/
private theorem abs_dec_half_le_eb1 {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R : F}
    (hu : 0 ≤ u) (hu1 : u ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1 / 4) (hR : 0 ≤ dec R)
    (hRΩ : dec R ≤ Ω) (hΩ : 2 ≤ Ω) :
    |dec (M.div R (M.ofNat 2))| ≤ dec R / 2 + 2 * u * dec R + u * τ := by
  have h2 := abs_le.mp (abs_sub_le_of_isRoundingOf_aux (hM.ofNat 2) (by norm_num; linarith) hu hτ₀)
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
  have hRtΩ : dec R / dec (M.ofNat 2) ≤ Ω := by nlinarith
  have hd := abs_sub_le_of_isRoundingOf_aux (hM.div R (M.ofNat 2) ht0.ne')
    (by rwa [abs_of_nonneg hRt0]) hu hτ₀
  rw [abs_of_nonneg hRt0] at hd
  have h3 := abs_sub_abs_le_abs_sub (dec (M.div R (M.ofNat 2))) (dec R / dec (M.ofNat 2))
  rw [abs_sub_comm] at hd
  rw [abs_of_nonneg hRt0] at h3
  have := mul_le_mul_of_nonneg_left hRt hu
  nlinarith [mul_nonneg (mul_nonneg hu hu) hR]

set_option maxHeartbeats 2000000 in
-- long `nlinarith` chains on the rounding budget
/-- The residual and singular-value budget of a node (pure real arithmetic). -/
private theorem node_budget_eb1 {ε x R R₀ u v τ e' r' η κ s ρ γ ξ Dn θ ε₀ : ℝ}
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
    0 ≤ e' ∧ 0 ≤ κ ∧ κ < 1 ∧ 0 ≤ ξ ∧ 0 ≤ θ ∧ 0 ≤ ρ ∧ 0 ≤ η ∧ 0 ≤ Dn ∧ 0 ≤ s ∧
    Dn + s ≤ 2 * R + R₀ ∧     κ + √2 * ξ ≤ ε / 3 ∧
    γ + ρ + s * (2 * κ + κ ^ 2) +
        2 * ((1 + κ) ^ 2 * θ + ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ)) ≤ ε * (R + R₀) ∧
    ε₀ + ρ + s * (2 * κ + κ ^ 2) + (1 + κ) ^ 2 * θ ≤ ε * (R + R₀) := by
  -- the depth parameter
  obtain ⟨w, hw_def⟩ : ∃ w, w = 1 / x := ⟨_, rfl⟩
  have hx0 : 0 < x := by linarith
  have hwx : w * x = 1 := by rw [hw_def]; field_simp
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw20 : w ≤ 1 / 20 := by rw [hw_def, div_le_div_iff₀ hx0 (by norm_num)]; linarith
  have hη' : η = (1 - w) * ε * w / 5 := by rw [hη, hw_def]; field_simp
  rw [← hw_def] at he'₁ he'₂
  have h2x : 2 / x = 2 * w := by rw [hw_def]; ring
  rw [h2x] at hr'
  have hεw : 0 ≤ ε * w := by positivity
  have hww : 0 ≤ w * w := by positivity
  have hεww : 0 ≤ ε * w * w := by positivity
  have hu' : u * 1000000 ≤ ε * w := by
    have := mul_le_mul_of_nonneg_left hux hw0.le
    have e : w * (x * u * 1000000) = (w * x) * u * 1000000 := by ring
    rw [e, hwx] at this; linarith
  have hv' : v * 100000 ≤ ε * w := by
    have := mul_le_mul_of_nonneg_left hvx hw0.le
    have e : w * (x * v * 100000) = (w * x) * v * 100000 := by ring
    rw [e, hwx] at this; linarith
  have hεw8 : ε * w ≤ w / 8 := by
    have := mul_le_mul_of_nonneg_right hε₁ hw0.le; linarith
  have hεw1 : ε * w ≤ 1 / 160 := by
    have := mul_le_mul hε₁ hw20 hw0.le (by norm_num); linarith
  have hu1 : u ≤ 1 / 10 ^ 8 := by linarith
  have huτ : u * τ ≤ u / 4 := by have := mul_le_mul_of_nonneg_left hτ hu; linarith
  have huτ0 : 0 ≤ u * τ := mul_nonneg hu hτ₀
  have huτR : u * τ * 10000000 ≤ ε * w * R₀ := by
    have h1 : u * τ * 4 ≤ u * (ε * R₀) := by
      have := mul_le_mul_of_nonneg_left hτR hu; linarith
    have h2 : u * (ε * R₀) * 1000000 ≤ ε * w * (ε * R₀) := by
      have := mul_le_mul_of_nonneg_right hu' (by positivity : 0 ≤ ε * R₀); linarith
    have h3 : ε * w * (ε * R₀) ≤ ε * w * R₀ / 8 := by
      have := mul_le_mul_of_nonneg_left hε₁ (by positivity : 0 ≤ ε * w * R₀)
      have e : ε * w * (ε * R₀) = ε * w * R₀ * ε := by ring
      rw [e]; linarith
    linarith
  have hεwR0 : 0 ≤ ε * w * R₀ := by positivity
  have hεwR : 0 ≤ ε * w * R := by positivity
  have huR : u * R * 1000000 ≤ ε * w * R := by
    have := mul_le_mul_of_nonneg_right hu' hR; linarith
  have hεwR8 : ε * w * R ≤ w * R / 8 := by
    have := mul_le_mul_of_nonneg_right hε₁ (by positivity : 0 ≤ w * R)
    have e : ε * w * R = ε * (w * R) := by ring
    rw [e]; linarith
  have hwR : w * R ≤ R / 20 := by have := mul_le_mul_of_nonneg_right hw20 hR; linarith
  have hwuR : w * (u * R) ≤ u * R / 20 := by
    have := mul_le_mul_of_nonneg_right hw20 (by positivity : 0 ≤ u * R); linarith
  have hεwR160 : ε * w * R ≤ R / 160 := by
    have := mul_le_mul_of_nonneg_right hεw1 hR; linarith
  have hεwR₀160 : ε * w * R₀ ≤ R₀ / 160 := by
    have := mul_le_mul_of_nonneg_right hεw1 hR₀; linarith
  -- the child's tolerance
  obtain ⟨E, hE⟩ : ∃ E, E = ε * (1 - w + 2 * w / 1000000) := ⟨_, rfl⟩
  have huε : 7 * u * ε + u * τ ≤ 2 * ε * w / 1000000 := by
    have := mul_le_mul_of_nonneg_left hε₁ (by positivity : 0 ≤ 7 * u); linarith
  have hE' : e' ≤ E := by rw [hE]; linarith
  have he'0 : 0 ≤ e' := by
    have h1 : (1 / 2 : ℝ) ≤ (1 - w) * (1 - 9 * u) := by linarith [mul_nonneg hw0.le hu]
    have h2 := mul_le_mul_of_nonneg_right h1 hε.le
    linarith
  have hE1 : E ≤ ε := by
    rw [hE]
    have := mul_le_mul_of_nonneg_left (by linarith : 1 - w + 2 * w / 1000000 ≤ 1) hε.le
    linarith
  have hE0 : 0 ≤ E := he'0.trans hE'
  have hκ0 : 0 ≤ κ := by rw [hκ]; linarith
  have hκ1 : κ ≤ 1 / 24 := by rw [hκ]; linarith
  -- the window, the shift and the compression scale
  obtain ⟨Rr, hRr⟩ : ∃ Rr, Rr = (1 / 2 + 2 * w + 2 * w / 1000000) * R + ε * w * R₀ / 10000000 :=
    ⟨_, rfl⟩
  have hr'R : r' ≤ Rr := by rw [hRr]; linarith
  obtain ⟨Sb, hSb⟩ : ∃ Sb, Sb = (1 / 2 + w / 1000000) * R + ε * w * R₀ / 10000000 := ⟨_, rfl⟩
  have hsS : s ≤ Sb := by rw [hs, hSb]; linarith
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hRr0 : 0 ≤ Rr := hr'₀.trans hr'R
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρE : ρ ≤ E * (Rr + R₀) := by
    rw [hρ]; exact mul_le_mul hE' (by linarith) (by positivity) hE0
  have hκ2 : 2 * κ + κ ^ 2 ≤ 49 / 72 * E := by
    have h := mul_le_mul_of_nonneg_left hκ1 hκ0
    have : κ ^ 2 = κ * κ := sq κ
    linarith
  have hsκ : s * (2 * κ + κ ^ 2) ≤ Sb * (49 / 72 * E) :=
    mul_le_mul hsS hκ2 (by positivity) (hs0.trans hsS)
  -- the gap
  have hη0 : 0 ≤ η := by
    rw [hη']
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) hε.le) hw0.le) (by norm_num)
  have hηw : η ≤ ε * w / 5 := by rw [hη']; linarith
  have hη1 : η ≤ 1 / 800 := by linarith
  have hγ' : γ ≤ 4005 / 10000 * (ε * w * R) := by
    rw [hγ]
    have h1 := mul_le_mul_of_nonneg_left hηw hR
    have h2 := mul_le_mul_of_nonneg_left hη1 (mul_nonneg hR hη0)
    linarith
  -- the deflation and product errors
  have hξ0 : 0 ≤ ξ := by rw [hξ]; positivity
  have hξ' : ξ ≤ 2084 / 10000 * (ε * w) := by
    rw [hξ]
    have h1 : η * (1 + κ) ≤ ε * w / 5 * (25 / 24) :=
      mul_le_mul hηw (by linarith) (by linarith) (by positivity)
    have h2 : (1 + η) * (1 + κ) ≤ (1 + 1 / 800) * (25 / 24) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    have h3 := mul_le_mul_of_nonneg_left (by linarith : (1 + η) * (1 + κ) + τ ≤ 1.31) hv
    linarith
  have hξ1 : ξ ≤ 14 / 10000 := by linarith
  -- the children's eigenvalues
  have hκd : (23 / 24 : ℝ) ^ 2 ≤ (1 - κ) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hDn0 : 0 ≤ Dn := by rw [hDn]; exact div_nonneg (by linarith) (sq_nonneg _)
  have hRr6 : Rr ≤ 6000001 / 10000000 * R + R₀ / 1000000000 := by rw [hRr]; linarith
  have hrρ : r' + ρ ≤ 6751 / 10000 * R + 1251 / 10000 * R₀ := by
    have h1 : E * (Rr + R₀) ≤ ε * (Rr + R₀) := mul_le_mul_of_nonneg_right hE1 (by positivity)
    have h2 : ε * (Rr + R₀) ≤ (Rr + R₀) / 8 := by
      have := mul_le_mul_of_nonneg_right hε₁ (by positivity : 0 ≤ Rr + R₀); linarith
    linarith
  have hDn' : Dn ≤ 7352 / 10000 * R + 1363 / 10000 * R₀ := by
    rw [hDn, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hκd)]
    have h0 : 0 ≤ 7352 / 10000 * R + 1363 / 10000 * R₀ := by positivity
    have := mul_le_mul_of_nonneg_left hκd h0
    linarith
  have hSb' : Sb ≤ 5001 / 10000 * R + R₀ / 10000 := by rw [hSb]; linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact mul_nonneg hu (by linarith)
  have hτR₀ : τ ≤ R₀ / 32 := by
    have := mul_le_mul_of_nonneg_right hε₁ hR₀; linarith
  have hY : (0 : ℝ) ≤ 124 / 100 * R + 17 / 100 * R₀ := by positivity
  have hθ' : θ * 1000000 ≤ ε * w * (124 / 100 * R + 17 / 100 * R₀) := by
    rw [hθ]
    have h1 : Dn + s + τ ≤ 124 / 100 * R + 17 / 100 * R₀ := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hu
    have h3 := mul_le_mul_of_nonneg_right hu' hY
    linarith
  have hθ1 : θ ≤ R / 10000 + R₀ / 10000 := by linarith
  have hDsθ : Dn + s + θ ≤ 12355 / 10000 * R + 1366 / 10000 * R₀ := by linarith
  have hκ3 : (1 + κ) ^ 2 ≤ 625 / 576 := by
    have := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + κ) (by linarith : 1 + κ ≤ 25 / 24) 2
    norm_num at this ⊢; linarith
  have hT1 : (1 + κ) ^ 2 * θ ≤ ε * w * (R + R₀) / 100000 := by
    have := mul_le_mul_of_nonneg_right hκ3 hθ0
    linarith
  have hT2 : ξ * (2 * (1 + κ) + ξ) ≤ 4345 / 10000 * (ε * w) := by
    have h1 : 2 * (1 + κ) + ξ ≤ 2.0848 := by linarith
    have := mul_le_mul hξ' h1 (by linarith) (by positivity)
    linarith
  have hT3 : ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ) ≤
      4345 / 10000 * (ε * w) * (12355 / 10000 * R + 1366 / 10000 * R₀) :=
    mul_le_mul hT2 hDsθ (by linarith) (by positivity)
  -- the singular values
  have hsq2 : √2 ≤ 1.4143 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hεR : 0 ≤ ε * R := by positivity
  have hεR₀ : 0 ≤ ε * R₀ := by positivity
  refine ⟨he'0, hκ0, by linarith, hξ0, hθ0, hρ0, hη0, hDn0, hs0, by linarith, ?_, ?_, ?_⟩
  · have h1 := mul_le_mul hsq2 hξ' hξ0 (by norm_num)
    rw [hκ]
    have h2 : E / 3 + 1.4143 * (2084 / 10000 * (ε * w)) ≤ ε / 3 := by
      rw [hE]; linarith
    linarith
  · -- the residual of a split
    have hfin : 4005 / 10000 * (ε * w * R) + E * (Rr + R₀) + Sb * (49 / 72 * E) +
        2 * (ε * w * (R + R₀) / 100000 +
          4345 / 10000 * (ε * w) * (12355 / 10000 * R + 1366 / 10000 * R₀)) ≤ ε * (R + R₀) := by
      have e : 4005 / 10000 * (ε * w * R) + E * (Rr + R₀) + Sb * (49 / 72 * E) +
          2 * (ε * w * (R + R₀) / 100000 +
            4345 / 10000 * (ε * w) * (12355 / 10000 * R + 1366 / 10000 * R₀)) =
          ε * R * ((1 - w + 2 * w / 1000000) * (1 / 2 + 2 * w + 2 * w / 1000000) +
            49 / 72 * (1 - w + 2 * w / 1000000) * (1 / 2 + w / 1000000) +
            (4005 / 10000 + 2 / 100000 + 2 * (4345 / 10000) * (12355 / 10000)) * w) +
          ε * R₀ * ((1 - w + 2 * w / 1000000) * (ε * w / 10000000 + 1) +
            49 / 72 * (1 - w + 2 * w / 1000000) * (ε * w / 10000000) +
            (2 / 100000 + 2 * (4345 / 10000) * (1366 / 10000)) * w) := by
        rw [hE, hRr, hSb]; ring
      rw [e]
      have h1 := mul_le_mul_of_nonneg_left (show (1 - w + 2 * w / 1000000) *
          (1 / 2 + 2 * w + 2 * w / 1000000) + 49 / 72 * (1 - w + 2 * w / 1000000) *
          (1 / 2 + w / 1000000) + (4005 / 10000 + 2 / 100000 + 2 * (4345 / 10000) *
          (12355 / 10000)) * w ≤ 1 by linarith) hεR
      have h2 := mul_le_mul_of_nonneg_left (show (1 - w + 2 * w / 1000000) *
          (ε * w / 10000000 + 1) + 49 / 72 * (1 - w + 2 * w / 1000000) *
          (ε * w / 10000000) + (2 / 100000 + 2 * (4345 / 10000) * (1366 / 10000)) * w ≤ 1 by
          linarith) hεR₀
      linarith
    linarith
  · -- the residual of a shift
    have hε₀' : ε₀ ≤ ε * w * (R + R₀) / 100000 := by
      rw [hε₀]
      have h1 : R + s + τ ≤ 2 * R + R₀ := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hu
      have h3 := mul_le_mul_of_nonneg_right hu' (by positivity : (0 : ℝ) ≤ 2 * R + R₀)
      linarith
    have hfin : 2 * (ε * w * (R + R₀) / 100000) + E * (Rr + R₀) + Sb * (49 / 72 * E) ≤
        ε * (R + R₀) := by
      have e : 2 * (ε * w * (R + R₀) / 100000) + E * (Rr + R₀) + Sb * (49 / 72 * E) =
          ε * R * ((1 - w + 2 * w / 1000000) * (1 / 2 + 2 * w + 2 * w / 1000000) +
            49 / 72 * (1 - w + 2 * w / 1000000) * (1 / 2 + w / 1000000) +
            (2 / 100000) * w) +
          ε * R₀ * ((1 - w + 2 * w / 1000000) * (ε * w / 10000000 + 1) +
            49 / 72 * (1 - w + 2 * w / 1000000) * (ε * w / 10000000) +
            (2 / 100000) * w) := by
        rw [hE, hRr, hSb]; ring
      rw [e]
      have h1 := mul_le_mul_of_nonneg_left (show (1 - w + 2 * w / 1000000) *
          (1 / 2 + 2 * w + 2 * w / 1000000) + 49 / 72 * (1 - w + 2 * w / 1000000) *
          (1 / 2 + w / 1000000) + (2 / 100000) * w ≤ 1 by linarith) hεR
      have h2 := mul_le_mul_of_nonneg_left (show (1 - w + 2 * w / 1000000) *
          (ε * w / 10000000 + 1) + 49 / 72 * (1 - w + 2 * w / 1000000) *
          (ε * w / 10000000) + (2 / 100000) * w ≤ 1 by linarith) hεR₀
      linarith
    linarith

/-- Widening the singular-value window. -/
private theorem loewner_mono_eb1 {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    {κ' κ : ℝ} (h₁ : (1 - κ') ^ 2 • (1 : Matrix n n ℂ) ≤ X)
    (h₂ : X ≤ (1 + κ') ^ 2 • (1 : Matrix n n ℂ)) (h0 : 0 ≤ κ') (hκ : κ' ≤ κ) (hκ1 : κ ≤ 1) :
    (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ X ∧ X ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ) :=
  ⟨(smul_one_le_smul_one (by nlinarith)).trans h₁, h₂.trans (smul_one_le_smul_one (by nlinarith))⟩

open scoped ComplexOrder in
/-- Reindexing the columns of an approximate diagonalization. -/
private theorem isApproxDiagonalization_submatrix_eb1 {m n : Type*} [Fintype m] [DecidableEq m]
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
private theorem specNorm_mul_mul_conjTranspose_le_eb1c {m n : Type*} [Fintype m] [Fintype n]
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
private theorem diagonal_shift_sub_eb1c {n : Type*} [DecidableEq n] (d e : n → ℝ) (σ : ℝ) :
    Matrix.diagonal (fun i => (d i : ℂ)) + σ • (1 : Matrix n n ℂ) -
        Matrix.diagonal (fun i => (e i : ℂ)) =
      Matrix.diagonal (fun i => ((d i + σ - e i : ℝ) : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

/-- Generic Loewner perturbation of a Gram matrix. -/
private theorem loewner_add_eb1c {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k]
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

/-- Orthonormality of the concatenated basis. -/
private theorem hasOrthonormalCols_fromCols_eb1c {m p q : Type*} [Fintype m]
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {Zp : Matrix m p ℂ} {Zm : Matrix m q ℂ}
    (hZp : HasOrthonormalCols Zp) (hZm : HasOrthonormalCols Zm) (hZpm : Zpᴴ * Zm = 0) :
    HasOrthonormalCols (Matrix.fromCols Zp Zm) := by
  show (Matrix.fromCols Zp Zm)ᴴ * Matrix.fromCols Zp Zm = 1
  have hmp : Zmᴴ * Zp = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose (Zmᴴ * Zp), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hZpm, Matrix.conjTranspose_zero]
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols,
    hmp, hZpm]
  rw [show Zpᴴ * Zp = 1 from hZp, show Zmᴴ * Zm = 1 from hZm, Matrix.fromBlocks_one]

/-- (B') A Loewner upper bound on the Gram matrix bounds the spectral norm. -/
private theorem specNorm_le_of_conjTranspose_mul_self_le_eb1 {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] {U : Matrix m n ℂ} {κ : ℝ} (hκ : 0 ≤ κ)
    (h : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ)) : specNorm U ≤ 1 + κ := by
  have h' := (specNorm_sq_le_iff_conjTranspose_mul_self_le (by positivity)).2 h
  exact (sq_le_sq₀ (specNorm_nonneg _) (by positivity)).1 h'

/-- (B) Near-unitary square matrix: `‖1 - U Uᴴ‖ ≤ 2κ + κ²`. -/
private theorem specNorm_one_sub_mul_conjTranspose_le_eb1 {n : Type*} [Fintype n]
    [DecidableEq n] {U : Matrix n n ℂ} {κ : ℝ} (hκ : 0 ≤ κ)
    (h₁ : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ Uᴴ * U)
    (h₂ : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ)) :
    specNorm (1 - U * Uᴴ) ≤ 2 * κ + κ ^ 2 := by
  have hn : specNorm U ≤ 1 + κ := specNorm_le_of_conjTranspose_mul_self_le_eb1 hκ h₂
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
private theorem abs_le_specNorm_mul_diagonal_mul_div_eb1 {n : Type*} [Fintype n]
    [DecidableEq n] {U : Matrix n n ℂ} {d : n → ℝ} {κ : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ < 1)
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
private theorem specNorm_sub_mul_diagonal_shift_le_eb1 {n : Type*} [Fintype n]
    [DecidableEq n] {A A' U : Matrix n n ℂ} {d e : n → ℝ} {σ s κ ρ θ ε₀ : ℝ}
    (hσ : |σ| ≤ s) (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (hU₁ : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ Uᴴ * U)
    (hU₂ : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ))
    (hA' : specNorm ((A - σ • (1 : Matrix n n ℂ)) - A') ≤ ε₀)
    (hF : specNorm (A' - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) ≤ ρ)
    (he : ∀ i, |e i - (d i + σ)| ≤ θ) :
    specNorm (A - U * Matrix.diagonal (fun i => (e i : ℂ)) * Uᴴ) ≤
      ε₀ + ρ + s * (2 * κ + κ ^ 2) + (1 + κ) ^ 2 * θ := by
  have hn : specNorm U ≤ 1 + κ := specNorm_le_of_conjTranspose_mul_self_le_eb1 hκ hU₂
  have hB := specNorm_one_sub_mul_conjTranspose_le_eb1 hκ hU₁ hU₂
  set D := Matrix.diagonal (fun i => (d i : ℂ))
  set E := Matrix.diagonal (fun i => (e i : ℂ))
  have key : A - U * E * Uᴴ = ((A - σ • (1 : Matrix n n ℂ)) - A') + (A' - U * D * Uᴴ) +
      σ • (1 - U * Uᴴ) + U * (D + σ • (1 : Matrix n n ℂ) - E) * Uᴴ := by
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, smul_sub]
    abel
  have hT : specNorm (U * (D + σ • (1 : Matrix n n ℂ) - E) * Uᴴ) ≤ (1 + κ) ^ 2 * θ := by
    refine (specNorm_mul_mul_conjTranspose_le_eb1c hn).trans ?_
    gcongr
    rw [diagonal_shift_sub_eb1c]
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
private theorem specNorm_congr_sub_le_eb1c {m p : Type*} [Fintype m] [Fintype p]
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
  have h1 := specNorm_mul_mul_conjTranspose_le_eb1c (M := D' - E) hG
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

/-- (C) with a nonnegative bound `Dn`. -/
private theorem specNorm_sub_fromCols_mul_diagonal_le_aux_eb1c {m p q : Type*} [Fintype m]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq p] [DecidableEq q]
    {A : Matrix m m ℂ} {Zp : Matrix m p ℂ} {Zm : Matrix m q ℂ}
    (hZp : HasOrthonormalCols Zp) (hZm : HasOrthonormalCols Zm) (hZpm : Zpᴴ * Zm = 0)
    (hA : A = Zp * (Zpᴴ * A * Zp) * Zpᴴ + Zm * (Zmᴴ * A * Zm) * Zmᴴ)
    {Ap Up : Matrix p p ℂ} {Am Um : Matrix q q ℂ} {Vp : Matrix m p ℂ} {Vm : Matrix m q ℂ}
    {dp ep : p → ℝ} {dm em : q → ℝ} {σp σm s γ ρ κ ξ θ Dn : ℝ}
    (hκ : 0 ≤ κ) (hξ : 0 ≤ ξ) (hθ : 0 ≤ θ) (hσp : |σp| ≤ s) (hσm : |σm| ≤ s) (hDn : 0 ≤ Dn)
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
    have := specNorm_sub_mul_diagonal_shift_le_eb1 (A := Zpᴴ * A * Zp) (e := fun i => dp i + σp)
      (θ := 0) (ε₀ := γ) hσp hκ le_rfl hUp₁ hUp₂ (by
        have h := specNorm_neg (Ap - (Zpᴴ * A * Zp - σp • (1 : Matrix _ _ ℂ)))
        rw [neg_sub] at h; rw [h]; exact hCp) hFp
      (fun i => by simp)
    exact (le_of_eq rfl).trans (this.trans (le_of_eq (by ring)))
  have hYm : specNorm Ym ≤ γ + ρ + s * (2 * κ + κ ^ 2) := by
    have := specNorm_sub_mul_diagonal_shift_le_eb1 (A := Zmᴴ * A * Zm) (e := fun i => dm i + σm)
      (θ := 0) (ε₀ := γ) hσm hκ le_rfl hUm₁ hUm₂ (by
        have h := specNorm_neg (Am - (Zmᴴ * A * Zm - σm • (1 : Matrix _ _ ℂ)))
        rw [neg_sub] at h; rw [h]; exact hCm) hFm
      (fun i => by simp)
    exact (le_of_eq rfl).trans (this.trans (le_of_eq (by ring)))
  set Z := Matrix.fromCols Zp Zm
  have hZ : HasOrthonormalCols Z := hasOrthonormalCols_fromCols_eb1c hZp hZm hZpm
  have hblk : Zp * Yp * Zpᴴ + Zm * Ym * Zmᴴ = Z * Matrix.fromBlocks Yp 0 0 Ym * Zᴴ := by
    simp only [Z, Matrix.fromCols_mul_fromBlocks,
      Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows, Matrix.mul_zero, add_zero, zero_add]
  have hB : specNorm (Zp * Yp * Zpᴴ + Zm * Ym * Zmᴴ) ≤ γ + ρ + s * (2 * κ + κ ^ 2) := by
    rw [hblk, hZ.specNorm_mul_conjTranspose_right, hZ.specNorm_mul_left,
      specNorm_fromBlocks_zero₁₂_zero₂₁]
    exact max_le hYp hYm
  -- the T terms
  have hTp : specNorm ((Zp * Up) * Dp' * (Zp * Up)ᴴ - Vp * Ep * Vpᴴ) ≤
      (1 + κ) ^ 2 * θ + ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ) := by
    refine specNorm_congr_sub_le_eb1c ?_ hVp ?_ ?_
    · rw [hZp.specNorm_mul_left]; exact specNorm_le_of_conjTranspose_mul_self_le_eb1 hκ hUp₂
    · have : Dp' - Ep = Matrix.diagonal (fun i => ((dp i + σp - ep i : ℝ) : ℂ)) := by
        ext i j; by_cases h : i = j
        · subst h; simp [Dp', Ep]
        · simp [Dp', Ep, Matrix.diagonal_apply_ne _ h]
      rw [this]
      refine specNorm_diagonal_le hθ fun i => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]; exact hep i
    · refine specNorm_diagonal_le (by positivity) fun i => ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 := hep i; have h2 := hdp i
      rw [abs_le] at h1 h2 hσp ⊢; constructor <;> linarith
  have hTm : specNorm ((Zm * Um) * Dm' * (Zm * Um)ᴴ - Vm * Em * Vmᴴ) ≤
      (1 + κ) ^ 2 * θ + ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ) := by
    refine specNorm_congr_sub_le_eb1c ?_ hVm ?_ ?_
    · rw [hZm.specNorm_mul_left]; exact specNorm_le_of_conjTranspose_mul_self_le_eb1 hκ hUm₂
    · have : Dm' - Em = Matrix.diagonal (fun i => ((dm i + σm - em i : ℝ) : ℂ)) := by
        ext i j; by_cases h : i = j
        · subst h; simp [Dm', Em]
        · simp [Dm', Em, Matrix.diagonal_apply_ne _ h]
      rw [this]
      refine specNorm_diagonal_le hθ fun i => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]; exact hem i
    · refine specNorm_diagonal_le (by positivity) fun i => ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 := hem i; have h2 := hdm i
      rw [abs_le] at h1 h2 hσm ⊢; constructor <;> linarith
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
private theorem loewner_fromCols_eb1 {m p q : Type*} [Fintype m]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq p] [DecidableEq q]
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
  have hZ : HasOrthonormalCols Z := hasOrthonormalCols_fromCols_eb1c hZp hZm hZpm
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
  have := loewner_add_eb1c (a := 1 - κ) (b := 1 + κ) (by linarith) (by positivity)
    (by linarith) h₁ h₂ hX
  rw [hGX]
  convert this using 3 <;> ring


/-- A rounding of a bounded number. -/
private theorem abs_sub_le_of_isRoundingOf_le_eb1 {u τ Ω a z c : ℝ} (h : IsRoundingOf u τ Ω a z)
    (ha : |a| ≤ c) (hc : c ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) : |z - a| ≤ u * (c + τ) := by
  rw [abs_sub_comm]
  exact (abs_sub_le_of_isRoundingOf_aux h (ha.trans hc) hu hτ).trans
    (mul_le_mul_of_nonneg_left (by linarith) hu)

/-- The eigenvalues of a child's approximate diagonalization are bounded. -/
private theorem abs_le_of_isApproxDiagonalization_eb1 {n : Type*} [Fintype n] [DecidableEq n]
    {A U : Matrix n n ℂ} {d : n → ℝ} {ρ κ r : ℝ} (h : IsApproxDiagonalization A U d ρ κ)
    (hA : specNorm A ≤ r) (hκ : 0 ≤ κ) (hκ1 : κ < 1) (i : n) :
    |d i| ≤ (r + ρ) / (1 - κ) ^ 2 := by
  refine (abs_le_specNorm_mul_diagonal_mul_div_eb1 hκ hκ1 h.smul_one_le i).trans ?_
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  have e : U * Matrix.diagonal (fun j => (d j : ℂ)) * Uᴴ =
      A - (A - U * Matrix.diagonal (fun j => (d j : ℂ)) * Uᴴ) := by abel
  rw [e]
  exact (specNorm_sub_le _ _).trans (add_le_add hA h.specNorm_sub_le)

/-- The computed product `mm(Q, U)` against the ideal frame. -/
private theorem specNorm_mm_sub_le_eb1 {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
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
/-- A leaf of `NLAlib.eighAux` (size at most one, or the machine's leaf test true) is an
approximate diagonalization. -/
private lemma isApproxDiagonalization_eighAux_succ_of_leaf_eb1 {F : Type*}
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
private theorem eighStep_eq_shift_eb1 {F Su Sg : Type*} [Inhabited Sg] {M : FloatMachine F Su Sg}
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
private theorem eighStep_ne_leaf_eb1 {F Su Sg : Type*} [Inhabited Sg] {M : FloatMachine F Su Sg}
    {N signFuel : ℕ} {R₀ β : F} {k : ℕ} {A : Matrix (Fin k) (Fin k) (F × F)} {R ε : F} {ℓ : ℕ}
    {smp : EighSample Su Sg N} (hk : ¬ k ≤ 1) (hint : M.le R (M.mul ε R₀) = false)
    (U : Matrix (Fin k) (Fin k) (F × F)) (d : Fin k → F) :
    eighStep M N signFuel R₀ β A R ε ℓ smp ≠ .leaf U d := by
  unfold eighStep
  rw [if_neg hk, if_neg (by simp [hint])]
  dsimp only
  split_ifs <;> simp

set_option maxHeartbeats 1000000 in
-- long `nlinarith` chains on the rounding budget
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
Events I–III as conditions.
Proof: unfold `NLAlib.eighAux` and `NLAlib.eighStep`. Leaves: $k \le 1$ is exact; on the
test-true leaf $R \le \mathrm{fl}(\varepsilon R_0)$ the residual is $\|\mathbf{A}\|_2 \le R \le
\varepsilon R_0(1 + u)$, and $uR_0 \le R$ when $R > \varepsilon R_0$ since $u < \varepsilon$. Note
$\tau \le \sqrt{\rho/2}/(4k^{3/2}) \le 1/16$ (SN4's $2k\tau \le 1$; $\mathrm{fl}(\ell)$ relative).
Otherwise follow [Shah2024, proof of Lemma 4.1]: the branch is the true one
(`NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub`), with
$\|\mathbf{P}_\pm - \mathbf{\Pi}_\pm\|_2 \le \beta$ from
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le`; the children satisfy
the node invariant
(`NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_eighChild_eq_some`); on a split,
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_eighStep_eq_split`
gives the frames $\mathbf{V}_\pm$, unitaries $\mathbf{W}_\pm$ with
$\|\mathbf{Q}_\pm - \mathbf{V}_\pm\mathbf{W}_\pm\|_2 \le \eta$ and the compressions; replace
$\mathbf{V}_\pm$ by $\mathbf{V}_\pm\mathbf{W}_\pm$ (assembly through
`NLAlib.FloatMachine.IsAccurate.decodeMatrix_conjTransposeMat`,
`NLAlib.FloatMachine.IsAccurate.decodeMatrix_identityMat`,
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermAvg_le` and the product contract).
The children's window and tolerance are the machine's `NLAlib.eighNextParams`: $R' \le (1/2 +
2/\ell)R(1 + \delta)$ and $(1 - 1/\ell)\varepsilon(1 - \delta) \le \varepsilon' \le (1 -
1/\ell)\varepsilon(1 + \delta)$ with $\delta \le 4u + u\tau/\varepsilon$ (each `ofNat`, `div`,
`add`/`sub`, `mul` one rounding, `IsRoundingOf`). The source's estimates are too loose at
$\varepsilon' = 1/8$; use this budget ($\eta = \varepsilon'/(5\ell)$; `husign` gives $u \le
10^{-13}\varepsilon\theta^{3/2}$, so every $u$-term is $< 0.01R\varepsilon'$):
$\|\mathbf{X}_\pm\|_2 \le \eta(1 + \varepsilon'/3)(1 + \mu u/\eta) \le 1.044\eta$ (not the source's
$(1 + 2\varepsilon')$), $\|\mathbf{D}_\pm\|_2 \le (R'(1 + \varepsilon') + \varepsilon'R_0)/(1 -
\varepsilon'/3)^2$, the term (4.21) on both sides $\le 5.4R\eta + 4.8\varepsilon'R_0\eta$ (the
source undercounts it), (4.20) $\le 2R\eta$, (4.18) $\le 0.334R\varepsilon'$; the residual is at
most $$\varepsilon'\Bigl[\Bigl(\frac12 + \frac2\ell\Bigr)(1 + \delta)^2 + 0.334 +
\frac{1.48}{\ell}\Bigr]R + \varepsilon'\Bigl(1 + \delta + \frac{0.12}{\ell}\Bigr)R_0 \le
\varepsilon(R + R_0) \,,$$
which closes only **using $\varepsilon' = (1 - 1/\ell)\varepsilon$** (the source never needs the
factor): $(1 - 1/\ell)(0.834 + 3.48/\ell) \le 0.958$ at $\ell = 20$, decreasing in $\ell$ (a
margin of 4.3 %). Singular values: $\varepsilon'/3 + \sqrt2 \cdot 1.044\eta \le (1 +
0.89/\ell)\varepsilon'/3$ and $(1 + 0.89/\ell)(1 - 1/\ell)(1 + \delta) \le 1$. Split into private
lemmas: assembly of $\mathbf{U}$, singular values, residual. H, about 150 lines. -/
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
  obtain ⟨hux, hvx, hτ4, hτR⟩ := node_small_eb1 (k := y.k) (R₀ := dec R₀) (by
    rcases Nat.eq_zero_or_pos y.k with h | h
    · exfalso
      have := hβtol
      rw [h] at this
      simp [bisectionSignTol] at this
      linarith
    · exact h) hℓ hε hρ₁ hw hwR hβ hβtol
    hμM hu husign hτ₀ hτ hε₁
  have hlu : 20 * u ≤ y.ℓ * u := mul_le_mul_of_nonneg_right hℓ' hu
  have hΩ' : 16 * (dec R₀ + dec y.R + y.k + y.ℓ) ≤ Ω := by
    have := Real.sqrt_nonneg (Real.log (4 / ρ)); linarith
  have hk0 : (0 : ℝ) ≤ y.k := Nat.cast_nonneg _
  obtain ⟨hp1, hp2, hp3⟩ := dec_eighNextParams_le_eb1 hM (R := y.R) (ε := y.ε) (m := y.ℓ) hu
    (by linarith) hτ₀ (by linarith) hℓ (by linarith) hR0 (by linarith) hε.le (by linarith)
  have hhalf := abs_dec_half_le_eb1 hM (R := y.R) hu (by linarith) hτ₀ hτ4 hR0 (by linarith)
    (by linarith)
  have budget := fun hr'₀ => node_budget_eb1 (x := (y.ℓ : ℝ)) (R := dec y.R) (R₀ := dec R₀)
    (v := μM y.k * u) (e' := dec (eighNextParams M y.R y.ε y.ℓ).2)
    (r' := dec (eighNextParams M y.R y.ε y.ℓ).1) hε hε₁ hℓ' hR0 hR₀.le hu hux
    (mul_nonneg hμM hu) hvx hτ₀ hτ4 hτR hp2 hp3 hr'₀ hp1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hεR : 0 ≤ dec y.ε * (dec y.R + dec R₀) := by positivity
  by_cases hk : y.k ≤ 1
  · exact isApproxDiagonalization_eighAux_succ_of_leaf_eb1 hM hA (by positivity) (by linarith)
      (Or.inl ⟨hk, hεR⟩)
  by_cases ht : M.le y.R (M.mul y.ε R₀) = true
  · refine isApproxDiagonalization_eighAux_succ_of_leaf_eb1 hM hA (by positivity) (by linarith)
      (Or.inr ⟨ht, hR.trans ?_⟩)
    have hle := (hM.le_iff _ _).mp ht
    have hεR₀ : dec y.ε * dec R₀ ≤ dec R₀ / 8 := by
      have := mul_le_mul_of_nonneg_right hε₁ hR₀.le; linarith
    have hm := abs_sub_le_of_isRoundingOf_le_eb1 (hM.mul y.ε R₀) (c := dec y.ε * dec R₀)
      (by rw [abs_of_nonneg (by positivity)]) (by linarith) hu hτ₀
    rw [abs_le] at hm
    have h1 : u * (dec y.ε * dec R₀ + τ) ≤ dec y.ε * dec y.ε * dec R₀ := by
      have h3 : u ≤ dec y.ε / 1000 := by linarith
      have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ dec y.ε * dec R₀ + τ)
      have h5 := mul_le_mul_of_nonneg_left (by linarith : dec y.ε * dec R₀ + τ ≤
        5 / 4 * (dec y.ε * dec R₀)) (by positivity : 0 ≤ dec y.ε / 1000)
      have h6 : 0 ≤ dec y.ε * dec y.ε * dec R₀ := by positivity
      linarith
    have hεR0 := mul_nonneg hε.le hR0
    rcases le_or_gt (dec y.R) (dec y.ε * dec R₀) with h | h
    · linarith
    · have := mul_le_mul_of_nonneg_left h.le hε.le
      linarith
  have hint : M.le y.R (M.mul y.ε R₀) = false := by simpa using ht
  rcases hst : eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s []) with
    ⟨U, d⟩ | ⟨b, A', σ⟩ | ⟨kp, hkp, Qp, Qm, Ap, Am, σ⟩
  · exact absurd hst (eighStep_ne_leaf_eb1 hk hint U d)
  · obtain ⟨hA'eq, hσ⟩ := eighStep_eq_shift_eb1 hst
    have hy' : eighChild M N signFuel R₀ β y (s []) b = some ⟨y.k, A',
        (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩ := by
      simp [eighChild, hst]
    have hc := hchild b _ hy'
    obtain ⟨-, hA'R⟩ := hM.isHermitian_and_specNorm_le_of_eighChild_eq_some hμM hμQ hcN hu hA
      hR hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol husign hudefl hfuel hτ₀ hτ hΩ hgood hy'
    dsimp only at hc hA'R
    simp only [eighAux, hst]
    obtain ⟨he'0, hκ0, hκ1, hξ0, hθ0, hρ0, hη0, hDn0, hs0, hDs, hsing, -, hshift⟩ :=
      budget ((specNorm_nonneg _).trans hA'R)
    have hσabs : |dec σ| ≤ dec y.R / 2 + 2 * u * dec y.R + u * τ := by
      rcases hσ with rfl | rfl
      · exact hhalf
      · rw [hM.dec_neg, abs_neg]; exact hhalf
    have hn : specNorm (decodeMatrix dec y.A - dec σ • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) ≤
        dec y.R + (dec y.R / 2 + 2 * u * dec y.R + u * τ) := by
      refine (specNorm_sub_le _ _).trans (add_le_add hR ?_)
      rw [specNorm_real_smul]
      exact (mul_le_mul_of_nonneg_left specNorm_one_le (abs_nonneg _)).trans (by linarith)
    have hA'err := hM.specNorm_sub_decodeMatrix_hermShift_le hu hA σ (hn.trans (by linarith))
    rw [← hA'eq] at hA'err
    have hA'err' := hA'err.trans (mul_le_mul_of_nonneg_left (max_le
      (c := dec y.R + (dec y.R / 2 + 2 * u * dec y.R + u * τ) + τ) (hn.trans (by linarith))
      (by linarith)) hu)
    have hd := abs_le_of_isApproxDiagonalization_eb1 hc hA'R hκ0 hκ1
    have he : ∀ i, |dec (M.add ((eighAux M N signFuel R₀ β f A' (eighNextParams M y.R y.ε y.ℓ).1
        (eighNextParams M y.R y.ε y.ℓ).2 (y.ℓ + 1) fun a => s (b :: a)).2 i) σ) -
        (dec ((eighAux M N signFuel R₀ β f A' (eighNextParams M y.R y.ε y.ℓ).1
        (eighNextParams M y.R y.ε y.ℓ).2 (y.ℓ + 1) fun a => s (b :: a)).2 i) + dec σ)| ≤
        u * ((dec (eighNextParams M y.R y.ε y.ℓ).1 +
          dec (eighNextParams M y.R y.ε y.ℓ).2 * (dec (eighNextParams M y.R y.ε y.ℓ).1 +
            dec R₀)) / (1 - dec (eighNextParams M y.R y.ε y.ℓ).2 / 3) ^ 2 +
          (dec y.R / 2 + 2 * u * dec y.R + u * τ) + τ) := fun i =>
      abs_sub_le_of_isRoundingOf_le_eb1 (hM.add _ _)
        ((abs_add_le _ _).trans (add_le_add (hd i) hσabs)) (by linarith) hu hτ₀
    have hκε : dec (eighNextParams M y.R y.ε y.ℓ).2 / 3 ≤ dec y.ε / 3 := by
      have := mul_nonneg (Real.sqrt_nonneg 2) hξ0; linarith
    obtain ⟨hlo, hhi⟩ := loewner_mono_eb1 hc.smul_one_le hc.le_smul_one hκ0 hκε (by linarith)
    exact ⟨(specNorm_sub_mul_diagonal_shift_le_eb1 hσabs hκ0 hθ0 hc.smul_one_le hc.le_smul_one
      hA'err' hc.specNorm_sub_le he).trans hshift, hlo, hhi⟩
  · obtain ⟨hσR, ⟨Vp, hVp, hVpP, -, Wp, hWp, hQp, hAp⟩, ⟨Vm, hVm, hVmP, -, Wm, hWm, hQm, hAm⟩⟩ :=
      hM.exists_hasOrthonormalCols_specNorm_sub_le_of_eighStep_eq_split hμM hμQ hcN hu hA hR hℓ
        hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol husign hudefl hfuel hτ₀ hτ hΩ hgood hst
    have hyp : eighChild M N signFuel R₀ β y (s []) true = some ⟨kp, Ap,
        (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩ := by
      simp [eighChild, hst]
    have hym : eighChild M N signFuel R₀ β y (s []) false = some ⟨y.k - kp, Am,
        (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩ := by
      simp [eighChild, hst]
    have hcp := hchild true _ hyp
    have hcm := hchild false _ hym
    obtain ⟨-, hApR⟩ := hM.isHermitian_and_specNorm_le_of_eighChild_eq_some hμM hμQ hcN hu hA
      hR hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol husign hudefl hfuel hτ₀ hτ hΩ hgood hyp
    obtain ⟨-, hAmR⟩ := hM.isHermitian_and_specNorm_le_of_eighChild_eq_some hμM hμQ hcN hu hA
      hR hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol husign hudefl hfuel hτ₀ hτ hΩ hgood hym
    dsimp only at hcp hcm hApR hAmR
    simp only [eighAux, hst]
    obtain ⟨he'0, hκ0, hκ1, hξ0, hθ0, hρ0, hη0, hDn0, hs0, hDs, hsing, hsplit, -⟩ :=
      budget ((specNorm_nonneg _).trans hApR)
    have hσabs : |dec σ| ≤ dec y.R / 2 + 2 * u * dec y.R + u * τ := by
      rw [abs_le] at hσR ⊢
      have := mul_nonneg hu hR0
      have := mul_nonneg hu hτ₀
      constructor <;> linarith
    -- the rotated frames
    set Ā := decodeMatrix dec y.A with hĀ
    set Zp := Vp * Wp with hZpdef
    set Zm := Vm * Wm with hZmdef
    have hZp : HasOrthonormalCols Zp := hVp.mul hWp
    have hZm : HasOrthonormalCols Zm := hVm.mul hWm
    have hWWp : Wp * Wpᴴ = 1 := mul_eq_one_comm.mp hWp
    have hWWm : Wm * Wmᴴ = 1 := mul_eq_one_comm.mp hWm
    have hPp : Zp * Zpᴴ = Vp * Vpᴴ := by
      rw [hZpdef, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wp, hWWp,
        Matrix.one_mul]
    have hPm : Zm * Zmᴴ = Vm * Vmᴴ := by
      rw [hZmdef, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wm, hWWm,
        Matrix.one_mul]
    set S := cfc Real.sign (Ā - (dec y.R / y.ℓ * (s []).1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))
      with hS
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
    have hcomm : Commute S Ā := Commute.cfc_real
      ((Commute.refl Ā).sub_left ((Commute.one_left Ā).smul_left _)) Real.sign
    have hPc : Commute (Zp * Zpᴴ) Ā := by
      rw [hPp, hVpP]; exact ((Commute.one_left Ā).add_left hcomm).smul_left _
    have hQc : Commute (Zm * Zmᴴ) Ā := by
      rw [show Zm * Zmᴴ = 1 - Zp * Zpᴴ by rw [← hPQ]; abel]
      exact (Commute.one_left Ā).sub_left hPc
    have hAdec : Ā = Zp * (Zpᴴ * Ā * Zp) * Zpᴴ + Zm * (Zmᴴ * Ā * Zm) * Zmᴴ := by
      have h1 : Zp * Zpᴴ * Ā * (Zm * Zmᴴ) = 0 := by
        rw [hPc.eq, Matrix.mul_assoc, Matrix.mul_assoc Zp, ← Matrix.mul_assoc Zpᴴ, hZpm,
          Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
      have h2 : Zm * Zmᴴ * Ā * (Zp * Zpᴴ) = 0 := by
        rw [hQc.eq, Matrix.mul_assoc, Matrix.mul_assoc Zm, ← Matrix.mul_assoc Zmᴴ, hZmp,
          Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
      calc Ā = (Zp * Zpᴴ + Zm * Zmᴴ) * Ā * (Zp * Zpᴴ + Zm * Zmᴴ) := by
            rw [hPQ, Matrix.one_mul, Matrix.mul_one]
        _ = Zp * Zpᴴ * Ā * (Zp * Zpᴴ) + Zm * Zmᴴ * Ā * (Zm * Zmᴴ) +
            (Zp * Zpᴴ * Ā * (Zm * Zmᴴ) + Zm * Zmᴴ * Ā * (Zp * Zpᴴ)) := by
          simp only [Matrix.mul_add, Matrix.add_mul]; abel
        _ = _ := by rw [h1, h2, add_zero, add_zero]; simp only [Matrix.mul_assoc]
    have hCp : specNorm (decodeMatrix dec Ap - (Zpᴴ * Ā * Zp -
        dec σ • (1 : Matrix (Fin kp) (Fin kp) ℂ))) ≤
          (2 + 2 * ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) * dec y.R *
            ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)) := by
      convert hAp using 4; rw [hZpdef]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have hCm : specNorm (decodeMatrix dec Am - (Zmᴴ * Ā * Zm -
        (-dec σ) • (1 : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) ℂ))) ≤
          (2 + 2 * ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) * dec y.R *
            ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)) := by
      rw [neg_smul, sub_neg_eq_add]
      convert hAm using 4; rw [hZmdef]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    -- the computed bases
    have hΩq : (1 + (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)) *
        (1 + dec (eighNextParams M y.R y.ε y.ℓ).2 / 3) ≤ Ω := by
      have h1 : (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have := mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / (y.ℓ : ℝ)) hε.le
        linarith
      have h2 : (1 + (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)) *
          (1 + dec (eighNextParams M y.R y.ε y.ℓ).2 / 3) ≤ 2 * 2 :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
      linarith
    have hVoutp := specNorm_mm_sub_le_eb1 hM hkp hZp (by rw [hZpdef]; exact hQp)
      (specNorm_le_of_conjTranspose_mul_self_le_eb1 hκ0 hcp.le_smul_one) hκ0 hΩq hμM hu hτ₀
      (X := (eighAux M N signFuel R₀ β f Ap (eighNextParams M y.R y.ε y.ℓ).1
        (eighNextParams M y.R y.ε y.ℓ).2 (y.ℓ + 1) fun a => s (true :: a)).1)
    have hVoutm := specNorm_mm_sub_le_eb1 hM (Nat.sub_le _ _) hZm (by rw [hZmdef]; exact hQm)
      (specNorm_le_of_conjTranspose_mul_self_le_eb1 hκ0 hcm.le_smul_one) hκ0 hΩq hμM hu hτ₀
      (X := (eighAux M N signFuel R₀ β f Am (eighNextParams M y.R y.ε y.ℓ).1
        (eighNextParams M y.R y.ε y.ℓ).2 (y.ℓ + 1) fun a => s (false :: a)).1)
    -- the eigenvalues
    have hdp := abs_le_of_isApproxDiagonalization_eb1 hcp hApR hκ0 hκ1
    have hdm := abs_le_of_isApproxDiagonalization_eb1 hcm hAmR hκ0 hκ1
    have hep := fun i => abs_sub_le_of_isRoundingOf_le_eb1 (hM.add
        ((eighAux M N signFuel R₀ β f Ap (eighNextParams M y.R y.ε y.ℓ).1
          (eighNextParams M y.R y.ε y.ℓ).2 (y.ℓ + 1) fun a => s (true :: a)).2 i) σ)
        ((abs_add_le _ _).trans (add_le_add (hdp i) hσabs)) (by linarith) hu hτ₀
    have hem := fun i => abs_sub_le_of_isRoundingOf_le_eb1 (hM.sub
        ((eighAux M N signFuel R₀ β f Am (eighNextParams M y.R y.ε y.ℓ).1
          (eighNextParams M y.R y.ε y.ℓ).2 (y.ℓ + 1) fun a => s (false :: a)).2 i) σ)
        ((abs_sub _ _).trans (add_le_add (hdm i) hσabs)) (by linarith) hu hτ₀
    have hres := specNorm_sub_fromCols_mul_diagonal_le_aux_eb1c hZp hZm hZpm hAdec hκ0 hξ0 hθ0
      hσabs (by rwa [abs_neg]) hDn0 hCp hCm hcp.specNorm_sub_le hcm.specNorm_sub_le
      hcp.smul_one_le hcp.le_smul_one hcm.smul_one_le hcm.le_smul_one hVoutp hVoutm hdp hdm
      hep (fun i => by rw [← sub_eq_add_neg]; exact hem i)
    have hsq := mul_nonneg (Real.sqrt_nonneg 2) hξ0
    obtain ⟨hlo, hhi⟩ := loewner_fromCols_eb1 hZp hZm hZpm hκ0 hξ0 (by linarith)
      hcp.smul_one_le hcp.le_smul_one hcm.smul_one_le hcm.le_smul_one hVoutp hVoutm
    obtain ⟨hlo', hhi'⟩ := loewner_mono_eb1 hlo hhi (by linarith) hsing (by linarith)
    have key := isApproxDiagonalization_submatrix_eb1
      ((finCongr (Nat.add_sub_of_le hkp).symm).trans finSumFinEquiv.symm)
      (hres.trans hsplit) hlo' hhi'
    convert key using 2
    · simp only [decodeMatrix, ← Matrix.submatrix_map, Matrix.fromCols_map]
    · rename_i i
      generalize ((finCongr (Nat.add_sub_of_le hkp).symm).trans finSumFinEquiv.symm) i = j
      cases j <;> rfl

/-- A rounding of a nonnegative number in range, with the floor as an absolute term. -/
private lemma le_and_le_of_isRoundingOf {u τ Ω a z : ℝ} (h : IsRoundingOf u τ Ω a z)
    (ha0 : 0 ≤ a) (ha : a ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) :
    a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) := by
  have h1 := (h (by rwa [abs_of_nonneg ha0])).trans
    (mul_le_mul_of_nonneg_left (max_le_add_of_nonneg (abs_nonneg _) hτ) hu)
  rw [abs_of_nonneg ha0] at h1
  constructor <;> linarith [(abs_le.mp h1).1, (abs_le.mp h1).2]

/-- The real arithmetic of the next window of `NLAlib.eighNextParams`. -/
private lemma le_of_isRoundingOf_eighNextParams_fst {u τ Ω m t L a1 a2 c p1 r : ℝ}
    (hu : 0 ≤ u) (hum : 25 * m ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1) (hm : 20 ≤ m)
    (hmΩ : 2 * m ≤ Ω) (hr : 0 ≤ r) (hrΩ : r ≤ Ω)
    (ht : IsRoundingOf u τ Ω 2 t) (hL : IsRoundingOf u τ Ω m L)
    (ha1 : t ≠ 0 → IsRoundingOf u τ Ω (1 / t) a1) (ha2 : L ≠ 0 → IsRoundingOf u τ Ω (t / L) a2)
    (hc : IsRoundingOf u τ Ω (a1 + a2) c) (hp1 : IsRoundingOf u τ Ω (c * r) p1) :
    p1 ≤ (1 / 2 + 2 / m) * (1 + 22 * u) * r + u * τ := by
  have rnd : ∀ {a z : ℝ}, IsRoundingOf u τ Ω a z → 0 ≤ a → a ≤ Ω →
      a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) :=
    fun h ha0 ha => le_and_le_of_isRoundingOf h ha0 ha hu hτ₀
  have hm0 : 0 < m := by linarith
  obtain ⟨w, hw_def⟩ : ∃ w, w = 1 / m := ⟨_, rfl⟩
  have hwm : w * m = 1 := by rw [hw_def]; field_simp
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw20 : w ≤ 1 / 20 := by rw [hw_def, div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have huw : 25 * u ≤ w ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hum (sq_nonneg w)
    have h' : w ^ 2 * (25 * m ^ 2 * u) = 25 * u * (w * m) ^ 2 := by ring
    rw [h', hwm] at h; linarith
  have hww : w ^ 2 ≤ w / 20 := by
    have := mul_le_mul_of_nonneg_left hw20 hw0.le; rw [sq]; linarith
  have hu' : u ≤ w / 500 := by linarith
  have hu1 : u ≤ 1 / 10000 := by linarith
  have huτ : u * τ ≤ u := mul_le_of_le_one_right hu hτ
  have huτ0 : 0 ≤ u * τ := mul_nonneg hu hτ₀
  have huu : u * u ≤ u / 10000 := by have := mul_le_mul_of_nonneg_left hu1 hu; linarith
  have huu0 : 0 ≤ u * u := mul_nonneg hu hu
  have huw' : u * w ≤ u / 20 := by have := mul_le_mul_of_nonneg_left hw20 hu; linarith
  have huw0 : 0 ≤ u * w := mul_nonneg hu hw0.le
  have hum1 : u * (w * m) = u := by rw [hwm, mul_one]
  have hum' : u * m ≤ 1 / 500 := by
    have := mul_le_mul_of_nonneg_right hu' hm0.le
    have h2 : w / 500 * m = (w * m) / 500 := by ring
    rw [h2, hwm] at this; linarith
  have hwuτ : w * (u * τ) ≤ u * τ := mul_le_of_le_one_left huτ0 (by linarith)
  -- the stored `2` and `ℓ`
  obtain ⟨ht1, ht2⟩ := rnd ht (by norm_num) (by linarith)
  obtain ⟨hL1, hL2⟩ := rnd hL hm0.le (by linarith)
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  have hwL1 : 1 - 2 * u ≤ w * L := by
    have := mul_le_mul_of_nonneg_left hL1 hw0.le; linarith
  have hwL2 : w * L ≤ 1 + 2 * u := by
    have := mul_le_mul_of_nonneg_left hL2 hw0.le; linarith
  -- `fl(1/2)`
  have hit1 : 1 / t ≤ 1 / 2 + u := by
    rw [div_le_iff₀ ht0]
    have := mul_le_mul_of_nonneg_left (by linarith : 2 - 3 * u ≤ t) (by linarith : 0 ≤ 1 / 2 + u)
    linarith
  have hit2 : 1 / 2 - u ≤ 1 / t := by
    rw [le_div_iff₀ ht0]
    have := mul_le_mul_of_nonneg_left (by linarith : t ≤ 2 + 3 * u) (by linarith : 0 ≤ 1 / 2 - u)
    linarith
  obtain ⟨ha11, ha12⟩ := rnd (ha1 ht0.ne') (one_div_nonneg.mpr ht0.le) (by linarith)
  have hut := mul_le_mul_of_nonneg_left hit1 hu
  have hA1 : a1 ≤ 1 / 2 + 3 * u := by linarith
  have hA1' : 1 / 2 - 3 * u ≤ a1 := by linarith
  -- `fl(2/ℓ)`
  have hq1 : t / L ≤ (2 + 8 * u) * w := by
    rw [div_le_iff₀ hL0, mul_assoc]
    have := mul_le_mul_of_nonneg_left hwL1 (by linarith : 0 ≤ 2 + 8 * u)
    linarith
  have hq0 : 0 ≤ t / L := div_nonneg ht0.le hL0.le
  have hq5 : t / L ≤ 1 / 5 := by linarith
  obtain ⟨ha21, ha22⟩ := rnd (ha2 hL0.ne') hq0 (by linarith)
  have huq := mul_le_mul_of_nonneg_left hq5 hu
  have huq0 := mul_nonneg hu hq0
  have hA2 : a2 ≤ 2 * w + 2 * u := by linarith
  have hA2' : -2 * u ≤ a2 := by linarith
  -- `fl(fl(1/2) + fl(2/ℓ))`
  obtain ⟨hc1, hc2⟩ := rnd hc (by linarith) (by linarith)
  have huS := mul_le_mul_of_nonneg_left (by linarith : a1 + a2 ≤ 61 / 100) hu
  have huS0 := mul_nonneg hu (by linarith : (0 : ℝ) ≤ a1 + a2)
  have hC : c ≤ (1 / 2 + 2 * w) * (1 + 14 * u) := by linarith
  have hC0 : 0 ≤ c := by linarith
  have hC1 : c ≤ 1 := by linarith
  obtain ⟨-, hp⟩ := rnd hp1 (mul_nonneg hC0 hr) (by linarith [mul_le_of_le_one_left hr hC1])
  have hK : 0 ≤ (1 / 2 + 2 * w) * r := mul_nonneg (by linarith) hr
  have h22 : (1 + 14 * u) * (1 + u) ≤ 1 + 22 * u := by linarith
  have hcr : c * r ≤ (1 / 2 + 2 * w) * (1 + 14 * u) * r := mul_le_mul_of_nonneg_right hC hr
  have h1 := mul_le_mul_of_nonneg_right hcr (by linarith : (0 : ℝ) ≤ 1 + u)
  have h2 := mul_le_mul_of_nonneg_left h22 hK
  have : (2 : ℝ) / m = 2 * w := by rw [hw_def]; ring
  rw [this]
  linarith

/-- The real arithmetic of the next tolerance of `NLAlib.eighNextParams`. -/
private lemma le_and_le_of_isRoundingOf_eighNextParams_snd {u τ Ω m L e1 d p2 e : ℝ}
    (hu : 0 ≤ u) (hum : 25 * m ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1) (hm : 20 ≤ m)
    (hmΩ : 2 * m ≤ Ω) (he : 0 ≤ e) (he₁ : e ≤ 1) (hL : IsRoundingOf u τ Ω m L)
    (he1 : L ≠ 0 → IsRoundingOf u τ Ω (1 / L) e1) (hd : IsRoundingOf u τ Ω (1 - e1) d)
    (hp2 : IsRoundingOf u τ Ω (d * e) p2) :
    (1 - 1 / m) * (1 - 9 * u) * e - u * τ ≤ p2 ∧ p2 ≤ (1 - 1 / (2 * m)) * e + u * τ := by
  have rnd : ∀ {a z : ℝ}, IsRoundingOf u τ Ω a z → 0 ≤ a → a ≤ Ω →
      a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) :=
    fun h ha0 ha => le_and_le_of_isRoundingOf h ha0 ha hu hτ₀
  have hm0 : 0 < m := by linarith
  obtain ⟨w, hw_def⟩ : ∃ w, w = 1 / m := ⟨_, rfl⟩
  have hwm : w * m = 1 := by rw [hw_def]; field_simp
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw20 : w ≤ 1 / 20 := by rw [hw_def, div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have huw : 25 * u ≤ w ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hum (sq_nonneg w)
    have h' : w ^ 2 * (25 * m ^ 2 * u) = 25 * u * (w * m) ^ 2 := by ring
    rw [h', hwm] at h; linarith
  have hww : w ^ 2 ≤ w / 20 := by
    have := mul_le_mul_of_nonneg_left hw20 hw0.le; rw [sq]; linarith
  have hu' : u ≤ w / 500 := by linarith
  have hu1 : u ≤ 1 / 10000 := by linarith
  have huτ : u * τ ≤ u := mul_le_of_le_one_right hu hτ
  have huτ0 : 0 ≤ u * τ := mul_nonneg hu hτ₀
  have huu : u * u ≤ u / 10000 := by have := mul_le_mul_of_nonneg_left hu1 hu; linarith
  have huu0 : 0 ≤ u * u := mul_nonneg hu hu
  have huw' : u * w ≤ u / 20 := by have := mul_le_mul_of_nonneg_left hw20 hu; linarith
  have huw0 : 0 ≤ u * w := mul_nonneg hu hw0.le
  have hum1 : u * (w * m) = u := by rw [hwm, mul_one]
  have hum' : u * m ≤ 1 / 500 := by
    have := mul_le_mul_of_nonneg_right hu' hm0.le
    have h2 : w / 500 * m = (w * m) / 500 := by ring
    rw [h2, hwm] at this; linarith
  have hwuτ : w * (u * τ) ≤ u * τ := mul_le_of_le_one_left huτ0 (by linarith)
  -- the stored `2` and `ℓ`
  obtain ⟨hL1, hL2⟩ := rnd hL hm0.le (by linarith)
  have hL0 : 0 < L := by linarith
  have hwL1 : 1 - 2 * u ≤ w * L := by
    have := mul_le_mul_of_nonneg_left hL1 hw0.le; linarith
  have hwL2 : w * L ≤ 1 + 2 * u := by
    have := mul_le_mul_of_nonneg_left hL2 hw0.le; linarith
  -- `fl(1/ℓ)` and `fl(1 - fl(1/ℓ))`
  have hiL1 : 1 / L ≤ (1 + 3 * u) * w := by
    rw [div_le_iff₀ hL0, mul_assoc]
    have := mul_le_mul_of_nonneg_left hwL1 (by linarith : 0 ≤ 1 + 3 * u)
    linarith
  have hiL2 : (1 - 3 * u) * w ≤ 1 / L := by
    rw [le_div_iff₀ hL0, mul_assoc]
    have := mul_le_mul_of_nonneg_left hwL2 (by linarith : 0 ≤ 1 - 3 * u)
    linarith
  have hiL0 : 0 ≤ 1 / L := one_div_nonneg.mpr hL0.le
  have hiL10 : 1 / L ≤ 1 / 10 := by linarith
  obtain ⟨he11, he12⟩ := rnd (he1 hL0.ne') hiL0 (by linarith)
  have huL := mul_le_mul_of_nonneg_left hiL10 hu
  have huL0 := mul_nonneg hu hiL0
  have hE1 : e1 ≤ w + 2 * u := by linarith
  have hE1' : w - 2 * u ≤ e1 := by linarith
  obtain ⟨hd1, hd2⟩ := rnd hd (by linarith) (by linarith)
  have hue := mul_le_mul_of_nonneg_left (by linarith : 1 - e1 ≤ 1 - w + 2 * u) hu
  have hue' := mul_le_mul_of_nonneg_left (by linarith : 1 - w - 2 * u ≤ 1 - e1) hu
  have hD : (1 - w) * (1 - 5 * u) ≤ d := by linarith
  have hD' : d ≤ 1 - w + 5 * u := by linarith
  have hD0 : 0 ≤ d := by linarith
  have hD1 : d ≤ 1 := by linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨hp, -⟩ := rnd hp2 (mul_nonneg hD0 he) (by linarith [mul_le_one₀ hD1 he he₁])
    have hde : (1 - w) * (1 - 5 * u) * e ≤ d * e := mul_le_mul_of_nonneg_right hD he
    have h9 : (1 - w) * (1 - 9 * u) ≤ (1 - w) * ((1 - 5 * u) * (1 - u)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h1 := mul_le_mul_of_nonneg_right hde (by linarith : (0 : ℝ) ≤ 1 - u)
    have h2 := mul_le_mul_of_nonneg_right h9 he
    rw [← hw_def]
    linarith
  · obtain ⟨-, hp⟩ := rnd hp2 (mul_nonneg hD0 he) (by linarith [mul_le_one₀ hD1 he he₁])
    have hde : d * e ≤ (1 - w + 5 * u) * e := mul_le_mul_of_nonneg_right hD' he
    have hkey : (1 - w + 5 * u) * (1 + u) ≤ 1 - w / 2 := by linarith
    have h1 := mul_le_mul_of_nonneg_right hde (by linarith : (0 : ℝ) ≤ 1 + u)
    have h2 := mul_le_mul_of_nonneg_right hkey he
    have : 1 / (2 * m) = w / 2 := by rw [hw_def]; field_simp
    rw [this]
    linarith

/-- One level of the machine's next window and tolerance (`NLAlib.eighNextParams`). -/
private lemma dec_eighNextParams_le {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R ε : F} {m : ℕ}
    (hu : 0 ≤ u) (hum : 25 * (m : ℝ) ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1) (hm : 20 ≤ m)
    (hmΩ : 2 * (m : ℝ) ≤ Ω) (hR : 0 ≤ dec R) (hRΩ : dec R ≤ Ω) (hε : 0 ≤ dec ε)
    (hε₁ : dec ε ≤ 1) :
    dec (eighNextParams M R ε m).1 ≤ (1 / 2 + 2 / m) * (1 + 22 * u) * dec R + u * τ ∧
    (1 - 1 / m) * (1 - 9 * u) * dec ε - u * τ ≤ dec (eighNextParams M R ε m).2 ∧
    dec (eighNextParams M R ε m).2 ≤ (1 - 1 / (2 * m)) * dec ε + u * τ := by
  have h2 := hM.ofNat 2
  push_cast at h2
  have hm' : (20 : ℝ) ≤ m := by exact_mod_cast hm
  exact ⟨le_of_isRoundingOf_eighNextParams_fst hu hum hτ₀ hτ hm' hmΩ hR hRΩ h2 (hM.ofNat m)
    (fun h => hM.dec_one ▸ hM.div _ _ h) (fun h => hM.div _ _ h) (hM.add _ _) (hM.mul _ _),
    le_and_le_of_isRoundingOf_eighNextParams_snd hu hum hτ₀ hτ hm' hmΩ hε hε₁ (hM.ofNat m)
    (fun h => hM.dec_one ▸ hM.div _ _ h) (hM.dec_one ▸ hM.sub _ _) (hM.mul _ _)⟩

/-- The children of a node that is not a leaf: the machine's test failed, and the child carries
the next parameters of `NLAlib.eighNextParams`. -/
private lemma le_eq_false_and_eq_of_eighChild_eq_some {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) {N signFuel : ℕ} {R₀ β : F} {x y : EighNode F}
    {smp : EighSample Su Sg N} {b : Bool} (h : eighChild M N signFuel R₀ β x smp b = some y) :
    M.le x.R (M.mul x.ε R₀) = false ∧ y.R = (eighNextParams M x.R x.ε x.ℓ).1 ∧
      y.ε = (eighNextParams M x.R x.ε x.ℓ).2 ∧ y.ℓ = x.ℓ + 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hle
    rw [Bool.not_eq_false] at hle
    have hst : ∃ U d, eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ smp = .leaf U d := by
      unfold eighStep
      by_cases hk : x.k ≤ 1
      · rw [if_pos hk]; exact ⟨_, _, rfl⟩
      · rw [if_neg hk, if_pos hle]; exact ⟨_, _, rfl⟩
    obtain ⟨U, d, hst⟩ := hst
    simp [eighChild, hst] at h
  · unfold eighChild at h
    split at h
    · simp at h
    · split_ifs at h; cases h; exact ⟨rfl, rfl, rfl⟩
    · split_ifs at h <;> cases h <;> exact ⟨rfl, rfl, rfl⟩

/-- The tolerance of a node of depth $j \le \ell$ stays above $\varepsilon/3$. -/
private lemma div_three_le_of_le_depth {x j u τ ε₀ Φ : ℝ} (hx : 20 ≤ x) (hj0 : 0 ≤ j)
    (hj : j ≤ x) (hu : 0 ≤ u) (hxu : 100 * x ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : 100 * τ ≤ ε₀)
    (hε₀ : 0 < ε₀) (hΦ : 1 - 9 * (j * u) ≤ Φ) :
    ε₀ / 3 ≤ ε₀ * ((x - 1) / (x + j - 1)) * Φ - j * (u * τ) := by
  have hxu' : 20 * (x * u) ≤ 1 / 100 := by
    have := mul_le_mul_of_nonneg_right hx (mul_nonneg (by linarith : (0 : ℝ) ≤ x) hu); nlinarith
  have hju : j * u ≤ x * u := mul_le_mul_of_nonneg_right hj hu
  have hρ : 2 / 5 ≤ (x - 1) / (x + j - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hΦ' : 99 / 100 ≤ Φ := by linarith
  have h1 := mul_le_mul hρ hΦ' (by norm_num) (by linarith)
  have h2 := mul_le_mul_of_nonneg_left h1 hε₀.le
  have hjuτ : j * (u * τ) ≤ ε₀ / 100 := by
    have : j * (u * τ) = (j * u) * τ := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right (hju.trans (by linarith : x * u ≤ 1)) hτ₀
    linarith
  nlinarith

/-- $(1 + 22u)^n \le 1 + 23nu$ for $nu \le 1/1000$. -/
private lemma one_add_pow_le_of_mul_le {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hnu : (n : ℝ) * u ≤ 1 / 1000) :
    (1 + 22 * u) ^ n ≤ 1 + 23 * (n * u) := by
  have h1 : (1 + 22 * u) ^ n ≤ Real.exp (n * (22 * u)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (22 * u)]) n
  have hy0 : 0 ≤ (n : ℝ) * (22 * u) := by positivity
  have hy : |(n : ℝ) * (22 * u)| ≤ 1 := by rw [abs_of_nonneg hy0]; linarith
  have h2 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hy)).2
  have h3 : ((n : ℝ) * (22 * u)) ^ 2 ≤ (n * (22 * u)) * (22 / 1000) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) hy0
  linarith

/-- The telescoped product of the windows against the tolerance factor: for $x \ge 20$,
$$\frac{1}{32}\frac{2x(2x+1)(2x+2)(2x+3)}{x(x+1)(x+2)(x+3)} \le \frac{x-1}{2x-1} - \frac1x \,.$$ -/
private lemma div_le_sub_one_div_of_le {x : ℝ} (hx : 20 ≤ x) :
    (x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) / (x * (x + 1) * (x + 2) * (x + 3)) / 32 ≤
      (x - 1) / (x + x - 1) - 1 / x := by
  have hx0 : 0 < x := by linarith
  set P := (x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) / (x * (x + 1) * (x + 2) * (x + 3))
  set ρ := (x - 1) / (x + x - 1)
  have hpoly : 0 ≤ 4 * x ^ 3 - 62 * x ^ 2 - 101 * x + 48 := by
    nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ x - 20),
      mul_nonneg hx0.le (by linarith : 0 ≤ 18 * x - 101)]
  have h2x : x + x - 1 ≠ 0 := by linarith
  have hQ : x * (x + 1) * (x + 2) * (x + 3) ≠ 0 := by positivity
  have hρ' : ρ * (x + x - 1) = x - 1 := div_mul_cancel₀ _ h2x
  have hP' : P * (x * (x + 1) * (x + 2) * (x + 3)) =
      (x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) := div_mul_cancel₀ _ hQ
  have hx' : 1 / x * x = 1 := one_div_mul_cancel hx0.ne'
  have key : (ρ - 1 / x - P / 32) * (8 * x * (x + x - 1) * (x + 2) * (x + 3) * (x + 1)) =
      (4 * x ^ 3 - 62 * x ^ 2 - 101 * x + 48) * (x + 1) := by
    linear_combination (8 * x * (x + 2) * (x + 3) * (x + 1)) * hρ' -
      (8 * (x + x - 1) * (x + 2) * (x + 3) * (x + 1)) * hx' - ((x + x - 1) / 4) * hP'
  have hD : 0 < 8 * x * (x + x - 1) * (x + 2) * (x + 3) * (x + 1) :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hx0) (by linarith))
      (by linarith)) (by linarith)) (by linarith)
  have : 0 ≤ ρ - 1 / x - P / 32 :=
    le_of_mul_le_mul_right (by rw [zero_mul, key]; exact mul_nonneg hpoly (by linarith)) hD
  linarith

/-- The real arithmetic of the leaf test at depth $\ell$. -/
private lemma le_of_le_depth_eq {x u τ R₀ ε₀ X Ψ Φ R e z : ℝ} (hx : 20 ≤ x) (hu : 0 ≤ u)
    (hxu : 100 * x ^ 2 * u ≤ 1) (hτ1 : 100 * τ ≤ ε₀ * R₀) (hτ2 : 100 * τ ≤ ε₀)
    (hR₀ : 0 < R₀) (hε₀ : 0 < ε₀) (hX : X ≤ ε₀ / 32) (hΨ0 : 0 ≤ Ψ)
    (hΨ : Ψ ≤ 1 + 23 * (x * u)) (hΦ : 1 - 9 * (x * u) ≤ Φ)
    (hR : R ≤ R₀ * (X * ((x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) /
      (x * (x + 1) * (x + 2) * (x + 3))) * Ψ) + x * (u * τ))
    (he : ε₀ * ((x - 1) / (x + x - 1)) * Φ - x * (u * τ) ≤ e)
    (hz : e * R₀ - u * (e * R₀ + τ) ≤ z) : R ≤ z := by
  have hx0 : 0 < x := by linarith
  obtain ⟨w, hw⟩ : ∃ w, w = x * u := ⟨_, rfl⟩
  have hwτ : x * (u * τ) = w * τ := by rw [hw]; ring
  rw [← hw] at hΨ hΦ
  rw [hwτ] at hR he
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hwx : 100 * w * x ≤ 1 := by rw [hw]; linarith
  have hw1 : w ≤ 1 / 2000 := by
    have := mul_le_mul_of_nonneg_left hx hw0; linarith
  have huw : 20 * u ≤ w := by
    have := mul_le_mul_of_nonneg_right hx hu; rw [hw]; linarith
  set P := (x + x) * (x + x + 1) * (x + x + 2) * (x + x + 3) / (x * (x + 1) * (x + 2) * (x + 3))
  set ρ := (x - 1) / (x + x - 1)
  have hP0 : 0 ≤ P := by positivity
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
  have hρ1 : ρ ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hP : P / 32 ≤ ρ - 1 / x := div_le_sub_one_div_of_le hx
  have hP16 : P / 32 ≤ 1 / 2 := by have : 0 < 1 / x := by positivity
                                   linarith
  set Y := ε₀ * R₀
  have hY : 0 < Y := by positivity
  have hYx : 100 * (w * Y) ≤ Y / x := by
    rw [le_div_iff₀ hx0]
    have := mul_le_mul_of_nonneg_left hwx hY.le
    linarith
  -- the window
  have hA1 : R₀ * (X * P * Ψ) ≤ Y / 32 * P * Ψ := by
    have := mul_le_mul_of_nonneg_right hX (mul_nonneg (mul_nonneg hR₀.le hP0) hΨ0)
    simp only [Y]; linarith
  have hA2 := mul_le_mul_of_nonneg_left hΨ (mul_nonneg (by positivity : 0 ≤ Y / 32) hP0)
  have hA3 := mul_le_mul_of_nonneg_left hP hY.le
  have hA4 := mul_le_mul_of_nonneg_left hP16 (mul_nonneg hw0 hY.le)
  have hA5 : w * τ ≤ w * Y / 100 := by
    have := mul_le_mul_of_nonneg_left hτ1 hw0; simp only [Y]; linarith
  -- the test
  have hB1 := mul_le_mul_of_nonneg_right he hR₀.le
  have hB2 := mul_le_mul_of_nonneg_left hΦ (mul_nonneg hY.le hρ0)
  have hB3 : w * τ * R₀ ≤ w * Y / 100 := by
    have := mul_le_mul_of_nonneg_left hτ2 (mul_nonneg hw0 hR₀.le); simp only [Y]; linarith
  have hB4 := mul_le_mul_of_nonneg_left hρ1 (mul_nonneg hw0 hY.le)
  have hlow : Y * ρ * (1 - 9 * w) - w * Y / 100 ≤ e * R₀ := by
    have : ε₀ * ρ * Φ * R₀ = Y * ρ * Φ := by simp only [Y]; ring
    linarith
  have hlow2 : Y * ρ * (1 - 9 * w) - w * Y / 100 ≤ Y / 2 := by
    have := mul_le_mul_of_nonneg_left hρ1 hY.le
    have := mul_nonneg (mul_nonneg hY.le hρ0) hw0
    have := mul_nonneg hw0 hY.le
    linarith
  have hC1 := mul_le_mul_of_nonneg_right hlow (by linarith : (0 : ℝ) ≤ 1 - u)
  have hC2 := mul_le_mul_of_nonneg_left hlow2 hu
  have hC3 : u * τ ≤ u * Y / 100 := by
    have := mul_le_mul_of_nonneg_left hτ1 hu; simp only [Y]; linarith
  have hC4 := mul_le_mul_of_nonneg_left huw hY.le
  have hwY := mul_nonneg hw0 hY.le
  clear_value Y P ρ
  have h1 : Y / 32 * P * (1 + 23 * w) = Y * (P / 32) + 23 * (w * Y * (P / 32)) := by ring
  have h2 : Y * (ρ - 1 / x) = Y * ρ - Y / x := by ring
  have hup : R ≤ Y * ρ - Y / x + 23 / 2 * (w * Y) + w * Y / 100 := by
    linarith only [hR, hA1, hA2, hA3, hA4, hA5, h1, h2]
  have hdown : Y * ρ - 9 / 2 * (w * Y) - w * Y / 100 - 51 / 100 * (u * Y) ≤ z := by
    linarith only [hz, hC1, hC2, hC3, hB4]
  linarith only [hup, hdown, hYx, hC4, hwY]

/-- One level of the tolerance bound: $(1 - 1/m)(\ell - 1)/(m - 1) = (\ell - 1)/m$ for
$m = \ell + j$. -/
private lemma mul_div_sub_one_pow_succ (ε u : ℝ) {ℓ j : ℕ} (hm0 : (0 : ℝ) < ℓ + j)
    (hm1 : (ℓ : ℝ) + j - 1 ≠ 0) :
    ε * (((ℓ : ℝ) - 1) / (ℓ + (j + 1) - 1)) * (1 - 9 * u) ^ (j + 1) =
      (1 - 1 / ((ℓ : ℝ) + j)) * (1 - 9 * u) * (ε * (((ℓ : ℝ) - 1) / (ℓ + j - 1)) *
        (1 - 9 * u) ^ j) := by
  have : (ℓ : ℝ) + j ≠ 0 := hm0.ne'
  have h' : (ℓ : ℝ) + (j + 1) - 1 = ℓ + j := by ring
  rw [h', pow_succ]; field_simp

/-- One level of the window bound: $(1/2 + 2/m)\,m(m+1)(m+2)(m+3) =
\tfrac12(m+1)(m+2)(m+3)(m+4)$ for $m = \ell + j$. -/
private lemma mul_window_bound_eq (R u : ℝ) {ℓ j : ℕ} (hm0 : (0 : ℝ) < ℓ + j) :
    (1 / 2 + 2 / ((ℓ : ℝ) + j)) * (1 + 22 * u) * (R * (2⁻¹ ^ j *
      (((ℓ : ℝ) + j) * (ℓ + j + 1) * (ℓ + j + 2) * (ℓ + j + 3) /
        ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ j)) =
      R * (2⁻¹ ^ (j + 1) * (((ℓ : ℝ) + (j + 1)) * (ℓ + (j + 1) + 1) * (ℓ + (j + 1) + 2) *
        (ℓ + (j + 1) + 3) / ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) *
          (1 + 22 * u) ^ (j + 1)) := by
  have : (ℓ : ℝ) + j ≠ 0 := hm0.ne'
  rw [pow_succ, pow_succ]; field_simp; ring

/-- One level of the invariants of the recursion below a node at depth $j < \ell$. -/
private lemma invariants_of_eighChild_eq_some {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    {N signFuel : ℕ} {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : 20 ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ1 : 100 * τ ≤ dec ε * dec R₀) (hτ2 : 100 * τ ≤ dec ε) (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω)
    {j : ℕ} (hj : j < ℓ) {x y : EighNode F} {smp : EighSample ℝ ℂ N} {b : Bool}
    (hxy : eighChild M N signFuel R₀ β x smp b = some y) (h1 : x.ℓ = ℓ + j)
    (h2 : dec x.ε ≤ 1)
    (h3 : dec ε * (((ℓ : ℝ) - 1) / (ℓ + j - 1)) * (1 - 9 * u) ^ j - j * (u * τ) ≤ dec x.ε)
    (h4 : dec x.R ≤ dec R₀)
    (h5 : dec x.R ≤ dec R₀ * (2⁻¹ ^ j * (((ℓ : ℝ) + j) * (ℓ + j + 1) * (ℓ + j + 2) * (ℓ + j + 3) /
      ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ j) + j * (u * τ)) :
    y.ℓ = ℓ + (j + 1) ∧ dec y.ε ≤ 1 ∧
    dec ε * (((ℓ : ℝ) - 1) / (ℓ + ((j + 1 : ℕ) : ℝ) - 1)) * (1 - 9 * u) ^ (j + 1) -
      ((j + 1 : ℕ) : ℝ) * (u * τ) ≤ dec y.ε ∧ dec y.R ≤ dec R₀ ∧
    dec y.R ≤ dec R₀ * (2⁻¹ ^ (j + 1) * (((ℓ : ℝ) + ((j + 1 : ℕ) : ℝ)) *
      (ℓ + ((j + 1 : ℕ) : ℝ) + 1) * (ℓ + ((j + 1 : ℕ) : ℝ) + 2) * (ℓ + ((j + 1 : ℕ) : ℝ) + 3) /
      ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ (j + 1)) +
      ((j + 1 : ℕ) : ℝ) * (u * τ) := by
  obtain ⟨hle, hyR, hyε, hyℓ⟩ := le_eq_false_and_eq_of_eighChild_eq_some M hxy
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hjℓ : (j : ℝ) + 1 ≤ ℓ := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
  have hℓu : 20 * ((ℓ : ℝ) * u) ≤ 1 / 100 := by
    have := mul_le_mul_of_nonneg_right hℓ' (mul_nonneg (by linarith : (0 : ℝ) ≤ ℓ) hu)
    linarith
  have hu40 : u ≤ 1 / 40000 := by
    have := mul_le_mul_of_nonneg_right hℓ' hu; linarith
  have hτ1' : τ ≤ 1 := by linarith
  have huτ : u * τ ≤ u := mul_le_of_le_one_right hu hτ1'
  have hjuτ : 0 ≤ j * (u * τ) := mul_nonneg hj0 (mul_nonneg hu hτ₀)
  have hεx : dec ε / 3 ≤ dec x.ε := by
    refine (div_three_le_of_le_depth hℓ' hj0 (by linarith) hu hu₁ hτ₀ hτ2 hε ?_).trans h3
    have := one_add_mul_le_pow (a := -(9 * u)) (by linarith) j
    rw [← sub_eq_add_neg] at this
    linarith
  -- the window is nonnegative at a node that is not a leaf
  have hxR0 : dec x.ε * dec R₀ ≤ dec R₀ := mul_le_of_le_one_left hR₀.le h2
  have hRx : 0 ≤ dec x.R := by
    have hmul := (le_and_le_of_isRoundingOf (hM.mul x.ε R₀)
      (mul_nonneg (by linarith) hR₀.le) (by linarith) hu hτ₀).1
    have hnot : ¬ dec x.R ≤ dec (M.mul x.ε R₀) := fun h => by
      rw [← hM.le_iff] at h; rw [h] at hle; exact Bool.noConfusion hle
    have h1' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hεx hR₀.le) (by linarith : (0 : ℝ) ≤ 1 - u)
    have h2' := mul_le_mul_of_nonneg_left hτ1 hu
    have h3' := mul_le_mul_of_nonneg_left hu40 (mul_nonneg hε.le hR₀.le)
    linarith
  have hm : 25 * ((x.ℓ : ℕ) : ℝ) ^ 2 * u ≤ 1 := by
    rw [h1]; push_cast
    have := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by linarith) (by linarith : (ℓ : ℝ) + j ≤ 2 * ℓ) 2) hu
    nlinarith
  obtain ⟨s1, s2, s3⟩ := dec_eighNextParams_le hM (R := x.R) (ε := x.ε) (m := x.ℓ) hu hm hτ₀
    hτ1' (by omega) (by rw [h1]; push_cast; linarith) hRx (by linarith) (by linarith) h2
  rw [← hyR] at s1
  rw [← hyε] at s2 s3
  rw [h1] at s1 s2 s3
  rw [hyℓ, h1]
  push_cast at s1 s2 s3 ⊢
  have hm0 : (0 : ℝ) < ℓ + j := by linarith
  have hc : (1 / 2 + 2 / ((ℓ : ℝ) + j)) * (1 + 22 * u) ≤ 61 / 100 := by
    have : 2 / ((ℓ : ℝ) + j) ≤ 1 / 10 := by rw [div_le_iff₀ hm0]; linarith
    have := mul_le_mul (by linarith : 1 / 2 + 2 / ((ℓ : ℝ) + j) ≤ 6 / 10)
      (by linarith : 1 + 22 * u ≤ 1 + 22 / 40000) (by linarith) (by norm_num)
    linarith
  have hc0 : 0 ≤ (1 / 2 + 2 / ((ℓ : ℝ) + j)) * (1 + 22 * u) := by positivity
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · have hu2 : u ≤ 1 / (2 * ((ℓ : ℝ) + j)) := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left (by linarith : (j : ℝ) ≤ ℓ) hu
      linarith
    have : (1 - 1 / (2 * ((ℓ : ℝ) + j))) * dec x.ε ≤ 1 - 1 / (2 * ((ℓ : ℝ) + j)) :=
      mul_le_of_le_one_right (by rw [sub_nonneg, div_le_one (by positivity)]; linarith) h2
    linarith
  · have hk0 : 0 ≤ (1 - 1 / ((ℓ : ℝ) + j)) * (1 - 9 * u) :=
      mul_nonneg (by rw [sub_nonneg, div_le_one hm0]; linarith) (by linarith)
    have hk1 : (1 - 1 / ((ℓ : ℝ) + j)) * (1 - 9 * u) ≤ 1 :=
      mul_le_one₀ (by have : 0 < 1 / ((ℓ : ℝ) + j) := by positivity
                      linarith) (by linarith) (by linarith)
    have hid := mul_div_sub_one_pow_succ (dec ε) u hm0 (by linarith : (ℓ : ℝ) + j - 1 ≠ 0)
    rw [hid]
    have := mul_le_mul_of_nonneg_left h3 hk0
    have := mul_le_of_le_one_left hjuτ hk1
    linarith
  · have := mul_le_mul_of_nonneg_left h4 hc0
    have := mul_le_mul_of_nonneg_right hc hR₀.le
    have := mul_le_of_le_one_left hτ₀ (by linarith : u ≤ 1)
    have := mul_le_of_le_one_left hR₀.le hε₁
    linarith
  · have hid := mul_window_bound_eq (dec R₀) u hm0
    have := mul_le_mul_of_nonneg_left h5 hc0
    have := mul_le_of_le_one_left hjuτ (hc.trans (by norm_num))
    linarith

/-- A node at depth $\ell$ with the invariants of the recursion is a leaf. -/
private lemma eighChild_eq_none_of_invariants {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    {N signFuel : ℕ} {R₀ β ε : F} (hε : 0 < dec ε) (hR₀ : 0 < dec R₀) {ℓ : ℕ} (hℓ : 20 ≤ ℓ)
    (hhalf : (2⁻¹ : ℝ) ^ ℓ ≤ dec ε / 32) (hu : 0 ≤ u) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1)
    (hτ₀ : 0 ≤ τ) (hτ1 : 100 * τ ≤ dec ε * dec R₀) (hτ2 : 100 * τ ≤ dec ε)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {x : EighNode F} (smp : EighSample ℝ ℂ N) (b : Bool)
    (h2 : dec x.ε ≤ 1)
    (h3 : dec ε * (((ℓ : ℝ) - 1) / (ℓ + ℓ - 1)) * (1 - 9 * u) ^ ℓ - ℓ * (u * τ) ≤ dec x.ε)
    (h5 : dec x.R ≤ dec R₀ * (2⁻¹ ^ ℓ * (((ℓ : ℝ) + ℓ) * (ℓ + ℓ + 1) * (ℓ + ℓ + 2) * (ℓ + ℓ + 3) /
      ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ ℓ) + ℓ * (u * τ)) :
    eighChild M N signFuel R₀ β x smp b = none := by
  rcases hc : eighChild M N signFuel R₀ β x smp b with _ | y
  · rfl
  exfalso
  have hle := (le_eq_false_and_eq_of_eighChild_eq_some M hc).1
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓu : (ℓ : ℝ) * u ≤ 1 / 2000 := by
    have := mul_le_mul_of_nonneg_right hℓ' (mul_nonneg (by linarith : (0 : ℝ) ≤ ℓ) hu)
    linarith
  have hεx : dec ε / 3 ≤ dec x.ε := by
    refine (div_three_le_of_le_depth hℓ' (by positivity) le_rfl hu hu₁ hτ₀ hτ2 hε ?_).trans h3
    have := one_add_mul_le_pow (a := -(9 * u)) (by nlinarith) ℓ
    rw [← sub_eq_add_neg] at this
    linarith
  have hmul := (le_and_le_of_isRoundingOf (hM.mul x.ε R₀)
    (mul_nonneg (by linarith) hR₀.le) (by nlinarith) hu hτ₀).1
  have hR : dec x.R ≤ dec (M.mul x.ε R₀) := by
    refine le_of_le_depth_eq hℓ' hu hu₁ hτ1 hτ2 hR₀ hε hhalf (by positivity)
      (one_add_pow_le_of_mul_le hu (hℓu.trans (by norm_num))) ?_ h5 h3 hmul
    have := one_add_mul_le_pow (a := -(9 * u)) (by nlinarith) ℓ
    rw [← sub_eq_add_neg] at this
    linarith
  rw [← hM.le_iff] at hR
  rw [hR] at hle
  exact Bool.noConfusion hle

/-- **The recursion stops by depth $\ell$**: under `NLAlib.FloatMachine.IsAccurate` with
$0 \le u$, $100\ell^2u \le 1$, $0 \le \tau$, $100\tau \le \varepsilon\min(R_0, 1)$ (an absolute
floor bound: the rounded parameters $\mathrm{fl}(2/\ell)$, $\mathrm{fl}((1 - 1/\ell)\varepsilon_j)$
have floor errors $u\tau$) and $16(R_0 + \ell) \le \Omega$, for stored $\varepsilon$, $R_0$ with $0
< \varepsilon \le 2^{-15}$, $R_0 > 0$ and a depth counter $\ell \ge \lceil \log_2(1/\varepsilon)
\rceil + 5$ (`NLAlib.bisectionDepth`), the tree of `NLAlib.eighNodeAt` from the root
$(\mathbf{A}, R_0, \varepsilon, \ell)$ has no node at a path longer than $\ell$, for every
accuracy and samples. [Shah2024, proof of Theorem 4.2], "the
depth of the tree $d$ is no more than $\ell$".
Proof: a node at depth $j$ has window $R_j$ within a factor $(1 + u)^{4j}$ of
$R_0\prod_{i<j}(1/2 + 2/(\ell + i))$ and tolerance $\varepsilon_j$ within $(1 - u)^{4j}$ of
$\varepsilon(\ell - 1)/(\ell + j - 1)$ (the machine's rounded parameters, `NLAlib.eighNextParams`)
and depth parameter $\ell + j$ (induction on the path, unfolding `NLAlib.eighChild`); the products
telescope: $\prod_{i<\ell}(\ell + i + 4)/(\ell + i) = \frac{2\ell(2\ell+1)(2\ell+2)(2\ell+3)}
{\ell(\ell+1)(\ell+2)(\ell+3)} =: P_\ell$; with $2^{-\ell} \le \varepsilon/32$ (`Nat.le_ceil`,
`Real.rpow_logb`) it suffices that $P_\ell/32 \le (\ell - 1)/(2\ell - 1)$, i.e.
$(2\ell+1)(2\ell+3)(2\ell-1) \le 8(\ell-1)(\ell+2)(\ell+3)$, whose difference is
$20\ell^2 + 10\ell - 45 > 0$ for $\ell \ge 2$ (at $\ell = 20$: $0.4355 \le 0.487$), so
$R_\ell \le \varepsilon_\ell R_0$ with a relative margin of order $1/\ell$, which absorbs
$(1 + u)^{8\ell} \le 1 + 1/(10\ell)$ and the rounding of the test $\mathrm{fl}(\varepsilon_\ell
R_0)$ (floor: $\tau \le \varepsilon R_0/100$), and
the node at depth $\ell$ is a leaf of `NLAlib.eighStep`. Since $\ell$ is any number $\ge$
`NLAlib.bisectionDepth`, $R_j$ may drop below $\tau$: state the invariant with the additive floor
term, $R_{j+1} \le (\tfrac12 + \tfrac2{\ell_j})R_j(1 + u)^4 + u\tau$, summed $\le 2\ell u\tau \le
\varepsilon R_0/(5000\ell)$, far inside the margin. L, about 60 lines (path induction with four
roundings per level, the telescoping identity over $\mathbb{N}$, `Real.logb`). -/
theorem FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ}
    {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N)
    {a : List Bool} (ha : ℓ < a.length) :
    eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s = none := by
  -- $2^\ell \ge 32/\varepsilon$, hence $\ell \ge 20$
  have hpow : 32 ≤ dec ε * 2 ^ ℓ := by
    have hlog : Real.logb 2 (dec ε)⁻¹ ≤ (ℓ : ℝ) - 5 := by
      have h2 : ((⌈Real.logb 2 (dec ε)⁻¹⌉₊ + 5 : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast hℓ
      push_cast at h2
      linarith [Nat.le_ceil (Real.logb 2 (dec ε)⁻¹)]
    have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (inv_pos.mpr hε)).mp hlog
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast] at h
    norm_num at h
    have := mul_le_mul_of_nonneg_left h hε.le
    rw [mul_inv_cancel₀ hε.ne'] at this
    linarith
  have hℓ20 : 20 ≤ ℓ := by
    have h := hpow.trans (mul_le_mul_of_nonneg_right hε₁ (by positivity))
    have h' : (2 : ℝ) ^ 20 ≤ 2 ^ ℓ := by norm_num at h ⊢; linarith
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h'
  have hhalf : (2⁻¹ : ℝ) ^ ℓ ≤ dec ε / 32 := by
    rw [inv_pow, ← one_div, div_le_iff₀ (by positivity)]; linarith
  have hε1 : dec ε ≤ 1 := hε₁.trans (by norm_num)
  have hτ1 : 100 * τ ≤ dec ε * dec R₀ :=
    hτ.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hε.le)
  have hτ2 : 100 * τ ≤ dec ε := hτ.trans (mul_le_of_le_one_right hε.le (min_le_right _ _))
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ20
  -- induction on the path with the invariants of the recursion
  have key : ∀ (a : List Bool) (j : ℕ) (x : EighNode F) (s : List Bool → EighSample ℝ ℂ N),
      j ≤ ℓ → x.ℓ = ℓ + j → dec x.ε ≤ 1 →
      dec ε * (((ℓ : ℝ) - 1) / (ℓ + j - 1)) * (1 - 9 * u) ^ j - j * (u * τ) ≤ dec x.ε →
      dec x.R ≤ dec R₀ →
      dec x.R ≤ dec R₀ * (2⁻¹ ^ j * (((ℓ : ℝ) + j) * (ℓ + j + 1) * (ℓ + j + 2) * (ℓ + j + 3) /
        ((ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3))) * (1 + 22 * u) ^ j) + j * (u * τ) →
      ℓ < j + a.length → eighNodeAt M N signFuel R₀ β a x s = none := by
    intro a
    induction a with
    | nil => intro j x s hj _ _ _ _ _ hlt; simp only [List.length_nil] at hlt; omega
    | cons b a ih =>
      intro j x s hj h1 h2 h3 h4 h5 hlt
      simp only [eighNodeAt]
      rcases hc : eighChild M N signFuel R₀ β x (s []) b with _ | y
      · rfl
      rcases Nat.lt_or_ge j ℓ with hjl | hjl
      · obtain ⟨g1, g2, g3, g4, g5⟩ := invariants_of_eighChild_eq_some hM hε hε1 hR₀ hℓ20 hu
          hu₁ hτ₀ hτ1 hτ2 hΩ hjl hc h1 h2 h3 h4 h5
        exact ih (j + 1) y _ (by omega) g1 g2 g3 g4 g5
          (by simp only [List.length_cons] at hlt; omega)
      · obtain rfl : j = ℓ := by omega
        rw [eighChild_eq_none_of_invariants hM hε hR₀ hℓ20 hhalf hu hu₁ hτ₀ hτ1 hτ2 hΩ _ _ h2
          h3 h5] at hc
        exact absurd hc (by simp)
  have hQ : (ℓ : ℝ) * (ℓ + 1) * (ℓ + 2) * (ℓ + 3) ≠ 0 := by positivity
  refine key a 0 _ s (Nat.zero_le _) rfl hε1 ?_ le_rfl ?_ (by simpa using ha)
  · rw [Nat.cast_zero, add_zero, div_self (by linarith), pow_zero]; simp
  · simp only [Nat.cast_zero, add_zero, pow_zero, div_self hQ, mul_one, zero_mul]
    exact le_rfl

private theorem eighChild_eq_some_params_aux {F : Type*} {M : FloatMachine F ℝ ℂ}
    {N signFuel : ℕ} {R₀ β : F} {x y : EighNode F} {s : EighSample ℝ ℂ N} {b : Bool}
    (h : eighChild M N signFuel R₀ β x s b = some y) :
    y.k ≤ x.k ∧ y.ℓ = x.ℓ + 1 ∧ y.R = (eighNextParams M x.R x.ε x.ℓ).1 ∧
      y.ε = (eighNextParams M x.R x.ε x.ℓ).2 ∧ M.le x.R (M.mul x.ε R₀) = false := by
  unfold eighChild eighStep at h
  by_cases h1 : x.k ≤ 1
  · simp [h1] at h
  by_cases h2 : M.le x.R (M.mul x.ε R₀) = true
  · simp [h1, h2] at h
  simp only [h1, h2, if_false] at h
  split_ifs at h <;> dsimp only at h <;> (try split_ifs at h) <;> cases h <;>
    exact ⟨by dsimp only; omega, rfl, rfl, rfl, by simpa using h2⟩

private theorem rnd_aux_of_nonneg {u τ Ω a z : ℝ} (h : IsRoundingOf u τ Ω a z) (ha0 : 0 ≤ a)
    (ha : a ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) :
    a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) := by
  have hmax : max |a| τ ≤ a + τ := max_le (by rw [abs_of_nonneg ha0]; linarith) (by linarith)
  have := abs_le.mp ((h (by rwa [abs_of_nonneg ha0])).trans (mul_le_mul_of_nonneg_left hmax hu))
  constructor <;> linarith [this.1, this.2]

private theorem eighNextParams_snd_aux {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
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
  obtain ⟨hla, hlb⟩ := rnd_aux_of_nonneg (hM.ofNat L) hL0.le (by linarith) hu hτ₀
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
  obtain ⟨hqa, hqb⟩ := rnd_aux_of_nonneg (hM.div M.one (M.ofNat L) hdl0.ne')
    (by rw [hM.dec_one]; positivity) (by rw [hM.dec_one]; linarith) hu hτ₀
  rw [hM.dec_one] at hqa hqb
  have hq021 : 1 / dec (M.ofNat L) ≤ 0.21 := by linarith
  have hdq : 1 / L - u / 2 ≤ dec (M.div M.one (M.ofNat L)) ∧
      dec (M.div M.one (M.ofNat L)) ≤ 1 / L + u / 2 := by
    have := mul_le_mul_of_nonneg_left hq021 hu
    constructor <;> linarith
  obtain ⟨hsa, hsb⟩ := rnd_aux_of_nonneg (hM.sub M.one (M.div M.one (M.ofNat L)))
    (by rw [hM.dec_one]; linarith) (by rw [hM.dec_one]; linarith) hu hτ₀
  rw [hM.dec_one] at hsa hsb
  have hds : 1 - 1 / L - 1.6 * u ≤ dec (M.sub M.one (M.div M.one (M.ofNat L))) ∧
      dec (M.sub M.one (M.div M.one (M.ofNat L))) ≤ 1 - 1 / L + 1.6 * u := by
    have := mul_le_mul_of_nonneg_left (show 1 - dec (M.div M.one (M.ofNat L)) ≤ 1 by linarith) hu
    constructor <;> linarith
  have hds0 : 0 ≤ dec (M.sub M.one (M.div M.one (M.ofNat L))) := by linarith
  have hds1 : dec (M.sub M.one (M.div M.one (M.ofNat L))) ≤ 1 := by linarith
  have hdse := mul_le_of_le_one_left he0.le hds1
  obtain ⟨hea, heb⟩ := rnd_aux_of_nonneg (hM.mul (M.sub M.one (M.div M.one (M.ofNat L))) e)
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

private theorem eighNextParams_fst_aux {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R₀ r : F} (e : F)
    {L : ℕ} (hu : 0 ≤ u) (huL : u * L ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 100)
    (he0 : 0 < dec e) (hτeR : 30 * τ ≤ dec e * dec R₀) (he1 : dec e ≤ 1) (hL : 5 ≤ L)
    (hΩ : 2 + L + dec R₀ ≤ Ω) (hR₀ : 0 < dec R₀) (hr : dec r ≤ dec R₀)
    (hint : M.le r (M.mul e R₀) = false) :
    dec (eighNextParams M r e L).1 ≤ dec r := by
  have hL' : (5 : ℝ) ≤ L := by exact_mod_cast hL
  have hu5 : u ≤ 1 / 5000 := by nlinarith
  simp only [eighNextParams]
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  obtain ⟨h2a, h2b⟩ := rnd_aux_of_nonneg (hM.ofNat 2) (by norm_num) (by push_cast; linarith)
    hu hτ₀
  obtain ⟨hla, hlb⟩ := rnd_aux_of_nonneg (hM.ofNat L) (by positivity) (by linarith) hu hτ₀
  push_cast at h2a h2b
  have hd2 : 1.99 ≤ dec (M.ofNat 2) ∧ dec (M.ofNat 2) ≤ 2.01 := by constructor <;> linarith
  have hdl : L - 0.002 ≤ dec (M.ofNat L) := by linarith
  have hdl0 : 0 < dec (M.ofNat L) := by linarith
  -- the factor is at most `0.95`
  have hh1 : 1 / dec (M.ofNat 2) ≤ 0.51 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hh2 : 0.49 ≤ 1 / dec (M.ofNat 2) := by rw [le_div_iff₀ (by linarith)]; linarith
  obtain ⟨hha, hhb⟩ := rnd_aux_of_nonneg (hM.div M.one (M.ofNat 2) (by linarith))
    (by rw [hM.dec_one]; positivity) (by rw [hM.dec_one]; linarith) hu hτ₀
  rw [hM.dec_one] at hha hhb
  have ht1 : dec (M.ofNat 2) / dec (M.ofNat L) ≤ 0.41 := by rw [div_le_iff₀ hdl0]; linarith
  have ht0 : 0 ≤ dec (M.ofNat 2) / dec (M.ofNat L) := div_nonneg (by linarith) hdl0.le
  obtain ⟨hta, htb⟩ := rnd_aux_of_nonneg (hM.div (M.ofNat 2) (M.ofNat L) hdl0.ne') ht0
    (by linarith) hu hτ₀
  have := mul_le_mul_of_nonneg_left hh1 hu
  have := mul_le_mul_of_nonneg_left ht1 hu
  have hdh : 0.48 ≤ dec (M.div M.one (M.ofNat 2)) ∧ dec (M.div M.one (M.ofNat 2)) ≤ 0.52 := by
    constructor <;> linarith
  have hdt : -0.01 ≤ dec (M.div (M.ofNat 2) (M.ofNat L)) ∧
      dec (M.div (M.ofNat 2) (M.ofNat L)) ≤ 0.42 := by
    constructor <;> linarith
  obtain ⟨haa, hab⟩ := rnd_aux_of_nonneg (hM.add (M.div M.one (M.ofNat 2))
    (M.div (M.ofNat 2) (M.ofNat L))) (by linarith) (by linarith) hu hτ₀
  have := mul_le_mul_of_nonneg_left (show dec (M.div M.one (M.ofNat 2)) +
    dec (M.div (M.ofNat 2) (M.ofNat L)) ≤ 0.94 by linarith) hu
  have hda : 0 ≤ dec (M.add (M.div M.one (M.ofNat 2)) (M.div (M.ofNat 2) (M.ofNat L))) ∧
      dec (M.add (M.div M.one (M.ofNat 2)) (M.div (M.ofNat 2) (M.ofNat L))) ≤ 0.95 := by
    constructor <;> linarith
  -- the window is above the floor
  have heR := mul_le_of_le_one_left hR₀.le he1
  have hm := rnd_aux_of_nonneg (hM.mul e R₀) (mul_pos he0 hR₀).le (by linarith) hu hτ₀
  have hrm : dec (M.mul e R₀) < dec r := by
    rw [← not_le, ← hM.le_iff]; simp [hint]
  have := mul_le_mul_of_nonneg_left heR hu
  have := mul_le_mul_of_nonneg_right hu5 (mul_pos he0 hR₀).le
  have := mul_le_mul_of_nonneg_right hu5 hτ₀
  have hr0 : 29 * τ ≤ dec r := by linarith [hm.1]
  have hdar := mul_le_of_le_one_left (by linarith : 0 ≤ dec r) (by linarith : dec (M.add
    (M.div M.one (M.ofNat 2)) (M.div (M.ofNat 2) (M.ofNat L))) ≤ 1)
  obtain ⟨hra, hrb⟩ := rnd_aux_of_nonneg (hM.mul (M.add (M.div M.one (M.ofNat 2))
    (M.div (M.ofNat 2) (M.ofNat L))) r) (mul_nonneg hda.1 (by linarith)) (by linarith) hu hτ₀
  have := mul_le_mul_of_nonneg_left hdar hu
  have := mul_le_mul_of_nonneg_right hda.2 (by linarith : 0 ≤ dec r)
  have := mul_le_mul_of_nonneg_right hu5 (by linarith : 0 ≤ dec r)
  linarith

/-- **The parameters of the nodes**: under the hypotheses of
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`, every node $y$ of the tree at a
path $a$ has $\lvert a \rvert \le \ell$, size at most the root's, depth counter $\ell +
\lvert a\rvert$, tolerance in $[\varepsilon/3, \varepsilon]$ and window at most $R_0$. (Not
$R_y \ge 0$: a rounded product can be $-u\tau$; such a node is a leaf.) [Shah2024, proof of
Theorem 4.2].
Proof: induction on the path with the invariants of
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`'s proof (sizes do not grow: a
split partitions, a shift keeps; $\varepsilon_j \ge \tfrac{19}{39}(1 - \delta)^\ell\varepsilon$;
$R_j \le R_0$ since $(1/2 + 2/\ell)(1 + u)^4 \le 1$ plus the summed floor term). M, about 80
lines. -/
theorem FloatMachine.IsAccurate.eighNodeAt_eq_some_params
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ}
    {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N)
    {a : List Bool} {y : EighNode F}
    (h : eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s = some y) :
    a.length ≤ ℓ ∧ y.k ≤ k ∧ y.ℓ = ℓ + a.length ∧ dec ε / 3 ≤ dec y.ε ∧ dec y.ε ≤ dec ε ∧
      dec y.R ≤ dec R₀ := by
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
  have hτR : 100 * τ ≤ dec ε * dec R₀ := hτ.trans (by gcongr; exact min_le_left _ _)
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
  have key : ∀ (a : List Bool) (x : EighNode F) (s : List Bool → EighSample ℝ ℂ N) (j : ℕ)
      (y : EighNode F), j + a.length ≤ ℓ → x.k ≤ k → x.ℓ = ℓ + j → dec x.ε ≤ dec ε →
      dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * j ≤ dec x.ε * (x.ℓ - 1) → dec x.R ≤ dec R₀ →
      eighNodeAt M N signFuel R₀ β a x s = some y →
      y.k ≤ k ∧ y.ℓ = ℓ + (j + a.length) ∧ dec y.ε ≤ dec ε ∧
        dec ε * (ℓ - 1) - 6 * u * ℓ * dec ε * (j + a.length : ℕ) ≤ dec y.ε * (y.ℓ - 1) ∧
        dec y.R ≤ dec R₀ := by
    intro a
    induction a with
    | nil =>
      intro x s j y _ h1 h2 h3 h4 h5 h
      cases Option.some.inj h
      exact ⟨h1, h2, h3, by simpa using h4, h5⟩
    | cons b a ih =>
      intro x s j y hj h1 h2 h3 h4 h5 h
      simp only [eighNodeAt, Option.bind_eq_some_iff] at h
      obtain ⟨z, hz, hy⟩ := h
      obtain ⟨hzk, hzℓ, hzR, hzε, hint⟩ := eighChild_eq_some_params_aux hz
      simp only [List.length_cons] at hj
      have hxε := hlow x j (by omega) h2 h4
      have hx0 : 0 < dec x.ε := by linarith
      have hxℓ : (x.ℓ : ℝ) ≤ 2 * ℓ := by
        rw [h2]; push_cast; linarith [(by exact_mod_cast (by omega : j ≤ ℓ) : (j : ℝ) ≤ ℓ)]
      have hxℓ5 : 5 ≤ x.ℓ := by
        have : (5 : ℝ) ≤ x.ℓ := by rw [h2]; push_cast; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
        exact_mod_cast this
      have huL : u * x.ℓ ≤ 1 / 1000 := by nlinarith
      have hR := mul_le_mul_of_nonneg_right hxε hR₀.le
      obtain ⟨hs1, hs2⟩ := eighNextParams_snd_aux hM x.R x.ε hu huL hτ₀ (by linarith) hx0
        (by linarith) (by linarith) hxℓ5 (by linarith)
      have hf := eighNextParams_fst_aux hM x.ε hu huL hτ₀ (by linarith) hx0 (by linarith)
        (by linarith) hxℓ5 (by linarith) hR₀ h5 hint
      have hloss := mul_le_mul_of_nonneg_left
        (mul_le_mul hxℓ h3 hx0.le (by positivity)) (by positivity : (0 : ℝ) ≤ 3 * u)
      obtain ⟨r1, r2, r3, r4, r5⟩ := ih z (fun a' => s (b :: a')) (j + 1) y (by omega)
        (by omega) (by omega) (by rw [hzε]; linarith) (by
          rw [hzε, hzℓ]; push_cast at hs2 ⊢; nlinarith) (by rw [hzR]; linarith) hy
      rw [show j + (b :: a).length = j + 1 + a.length by simp only [List.length_cons]; omega]
      exact ⟨r1, r2, r3, r4, r5⟩
  have hlen : a.length ≤ ℓ := by
    by_contra hlt
    rw [eighNodeAt_eq_none_of_lt_length hM hε hε₁ hR₀ hℓ hu hu₁ hτ₀ hτ hΩ A s
      (not_le.mp hlt)] at h
    cases h
  obtain ⟨r1, r2, r3, r4, r5⟩ := key a ⟨k, A, R₀, ε, ℓ⟩ s 0 y (by omega) le_rfl rfl le_rfl
    (by simp) le_rfl h
  rw [zero_add] at r2 r4
  exact ⟨hlen, r1, r2, hlow y _ hlen r2 r4, r3, r5⟩

/-- A split of `NLAlib.eighStep` has both parts nonempty. -/
private lemma pos_and_lt_of_eighStep_eq_split_of_ne_none {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) {N signFuel : ℕ} {R₀ β : F} {k : ℕ}
    {A : Matrix (Fin k) (Fin k) (F × F)} {R ε : F} {ℓ : ℕ} {s : EighSample Su Sg N} {kp : ℕ}
    {h : kp ≤ k} {Qp : Matrix (Fin k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)} {σ : F}
    (hst : eighStep M N signFuel R₀ β A R ε ℓ s = .split kp h Qp Qm Ap Am σ) :
    0 < kp ∧ kp < k := by
  unfold eighStep at hst
  dsimp only at hst
  split_ifs at hst with h1 h2 h3 h4
  obtain ⟨rfl, -⟩ := EighStep.split.inj hst
  omega

/-- The nodes at one depth number at most $\max(k, 1)$. -/
private lemma encard_eighNodeAt_length_eq_le {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) {N signFuel : ℕ} {R₀ β : F} (j : ℕ) :
    ∀ (x : EighNode F) (s : List Bool → EighSample Su Sg N),
    {a : List Bool | a.length = j ∧ eighNodeAt M N signFuel R₀ β a x s ≠ none}.encard ≤
      (max x.k 1 : ℕ) := by
  induction j with
  | zero =>
    intro x s
    refine (Set.encard_le_encard (t := {[]}) fun a ha => ?_).trans ?_
    · exact List.eq_nil_of_length_eq_zero ha.1
    · rw [Set.encard_singleton]; exact_mod_cast le_max_right _ _
  | succ j ih =>
    intro x s
    have hmem : ∀ a ∈ {a : List Bool | a.length = j + 1 ∧
        eighNodeAt M N signFuel R₀ β a x s ≠ none},
        ∃ b a', a = b :: a' ∧ ∃ y', eighChild M N signFuel R₀ β x (s []) b = some y' ∧
          a' ∈ {a : List Bool | a.length = j ∧
            eighNodeAt M N signFuel R₀ β a y' (fun a' => s (b :: a')) ≠ none} := by
      rintro (_ | ⟨b, a'⟩) ⟨hlen, hy⟩
      · simp at hlen
      · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hy
        simp only [eighNodeAt, Option.bind_eq_some_iff] at hy
        obtain ⟨y', hy', hy⟩ := hy
        exact ⟨b, a', rfl, y', hy', by simpa using hlen, by simp [hy]⟩
    rcases hst : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (s []) with
      ⟨U, d⟩ | ⟨b, A', σ⟩ | ⟨kp, hkp, Qp, Qm, Ap, Am, σ⟩
    · refine le_of_eq_of_le (b := 0) (Set.encard_eq_zero.mpr ?_) bot_le
      refine Set.eq_empty_of_forall_notMem fun a ha => ?_
      obtain ⟨b, a', -, y', hy', -⟩ := hmem a ha
      simp [eighChild, hst] at hy'
    · set y' : EighNode F := ⟨x.k, A', (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      refine (Set.encard_le_encard (t := List.cons b '' {a : List Bool | a.length = j ∧
            eighNodeAt M N signFuel R₀ β a y' (fun a' => s (b :: a')) ≠ none})
          fun a ha => ?_).trans ?_
      · obtain ⟨b', a', rfl, z, hz, ha'⟩ := hmem a ha
        simp only [eighChild, hst] at hz
        split_ifs at hz with hb
        subst hb
        simp only [Option.some.injEq] at hz
        subst hz
        exact ⟨a', ha', rfl⟩
      · rw [(List.cons_injective).encard_image]
        exact ih y' _
    · obtain ⟨hkp0, hkpk⟩ := pos_and_lt_of_eighStep_eq_split_of_ne_none M hst
      set yp : EighNode F := ⟨kp, Ap, (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      set ym : EighNode F := ⟨x.k - kp, Am, (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      refine (Set.encard_le_encard (t := List.cons true '' {a : List Bool | a.length = j ∧
            eighNodeAt M N signFuel R₀ β a yp (fun a' => s (true :: a')) ≠ none} ∪
          List.cons false '' {a : List Bool | a.length = j ∧
            eighNodeAt M N signFuel R₀ β a ym (fun a' => s (false :: a')) ≠ none})
          fun a ha => ?_).trans ?_
      · obtain ⟨b', a', rfl, z, hz, ha'⟩ := hmem a ha
        simp only [eighChild, hst] at hz
        cases b'
        · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hz
          subst hz
          exact Or.inr ⟨a', ha', rfl⟩
        · simp only [↓reduceIte, Option.some.injEq] at hz
          subst hz
          exact Or.inl ⟨a', ha', rfl⟩
      · refine (Set.encard_union_le _ _).trans ?_
        rw [(List.cons_injective).encard_image, (List.cons_injective).encard_image]
        refine (add_le_add (ih yp _) (ih ym _)).trans ?_
        have hk : max yp.k 1 + max ym.k 1 ≤ max x.k 1 := by simp only [yp, ym]; omega
        exact_mod_cast hk

/-- **The recursion tree has at most $(k + 1)(\ell + 1)$ nodes**: under the hypotheses of
`NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_none_of_lt_length`, the set of paths at which
`NLAlib.eighNodeAt` has a node has at most $(k + 1)(\ell + 1)$ elements, $k$ the size of the root.
[Shah2024, proof of Theorem 4.2], $\lvert X \rvert \le nd$ there.
Proof: below the root every node has size at least $1$, and the sizes of the nodes at one depth
sum to at most $k$ (a split partitions its size, a shift keeps it, a leaf has no child: unfold
`NLAlib.eighChild`, `NLAlib.eighStep`); with the depth bound, at most $k + 1$ nodes at each of the
depths $0, \dots, \ell$ (`Set.encard_le_card`-type counting over `List Bool` of bounded length,
`Set.encard_iUnion_le`). L, about 70 lines. -/
theorem FloatMachine.IsAccurate.encard_eighNodeAt_ne_none_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ}
    {R₀ β ε : F} (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hR₀ : 0 < dec R₀) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u) (hu₁ : 100 * ℓ ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ : 16 * (dec R₀ + ℓ) ≤ Ω) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (s : List Bool → EighSample ℝ ℂ N) :
    {a : List Bool | eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s ≠ none}.encard ≤
      (k + 1) * (ℓ + 1) := by
  have hU : ∀ n : ℕ, {a : List Bool | a.length < n ∧
      eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s ≠ none}.encard ≤ (n * max k 1 : ℕ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine (Set.encard_le_encard (t := {a : List Bool | a.length < n ∧
          eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s ≠ none} ∪
          {a : List Bool | a.length = n ∧
          eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s ≠ none}) fun a ha => ?_).trans ?_
      · rcases Nat.lt_succ_iff_lt_or_eq.mp ha.1 with h | h
        · exact Or.inl ⟨h, ha.2⟩
        · exact Or.inr ⟨h, ha.2⟩
      · refine (Set.encard_union_le _ _).trans ?_
        refine (add_le_add ih (encard_eighNodeAt_length_eq_le M n ⟨k, A, R₀, ε, ℓ⟩ s)).trans ?_
        rw [Nat.succ_mul]
        exact_mod_cast le_rfl
  refine (Set.encard_le_encard (t := {a : List Bool | a.length < ℓ + 1 ∧
      eighNodeAt M N signFuel R₀ β a ⟨k, A, R₀, ε, ℓ⟩ s ≠ none}) fun a ha => ?_).trans
    ((hU (ℓ + 1)).trans ?_)
  · refine ⟨Nat.lt_succ_of_le (not_lt.mp fun hlt => ha ?_), ha⟩
    exact hM.eighNodeAt_eq_none_of_lt_length hε hε₁ hR₀ hℓ hu hu₁ hτ₀ hτ hΩ A s hlt
  · have hk : (ℓ + 1) * max k 1 ≤ (k + 1) * (ℓ + 1) := by
      rw [mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
    exact_mod_cast hk

/-- A split of `NLAlib.eighStep` has both parts nonempty. -/
private lemma pos_and_lt_of_eighStep_eq_split {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) {N signFuel : ℕ} {R₀ β : F} {k : ℕ}
    {A : Matrix (Fin k) (Fin k) (F × F)} {R ε : F} {ℓ : ℕ} {s : EighSample Su Sg N} {kp : ℕ}
    {h : kp ≤ k} {Qp : Matrix (Fin k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)} {σ : F}
    (hst : eighStep M N signFuel R₀ β A R ε ℓ s = .split kp h Qp Qm Ap Am σ) :
    0 < kp ∧ kp < k := by
  unfold eighStep at hst
  dsimp only at hst
  split_ifs at hst with h1 h2 h3 h4
  obtain ⟨rfl, -⟩ := EighStep.split.inj hst
  omega

/-- The split paths of length less than `m` number at most $k - 1$. -/
private lemma encard_eighNodeAt_isSplit_length_lt_le {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) {N signFuel : ℕ} {R₀ β : F} (m : ℕ) :
    ∀ (x : EighNode F) (s : List Bool → EighSample Su Sg N),
    {a : List Bool | a.length < m ∧ ∃ y, eighNodeAt M N signFuel R₀ β a x s = some y ∧
      (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit}.encard ≤ (x.k - 1 : ℕ) := by
  induction m with
  | zero => intro x s; simp
  | succ m ih =>
    intro x s
    have hmem : ∀ a ∈ {a : List Bool | a.length < m + 1 ∧
        ∃ y, eighNodeAt M N signFuel R₀ β a x s = some y ∧
          (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit},
        (a = [] ∧ (eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (s [])).IsSplit) ∨
        ∃ b a', a = b :: a' ∧ ∃ y', eighChild M N signFuel R₀ β x (s []) b = some y' ∧
          a' ∈ {a : List Bool | a.length < m ∧
            ∃ y, eighNodeAt M N signFuel R₀ β a y' (fun a' => s (b :: a')) = some y ∧
              (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s (b :: a))).IsSplit} := by
      rintro (_ | ⟨b, a'⟩) ⟨hlen, y, hy, hsp⟩
      · simp only [eighNodeAt, Option.some.injEq] at hy
        subst hy
        exact Or.inl ⟨rfl, hsp⟩
      · simp only [eighNodeAt, Option.bind_eq_some_iff] at hy
        obtain ⟨y', hy', hy⟩ := hy
        exact Or.inr ⟨b, a', rfl, y', hy', by simpa using hlen, y, hy, hsp⟩
    rcases hst : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (s []) with
      ⟨U, d⟩ | ⟨b, A', σ⟩ | ⟨kp, hkp, Qp, Qm, Ap, Am, σ⟩
    · refine le_of_eq_of_le (b := 0) (Set.encard_eq_zero.mpr ?_) bot_le
      refine Set.eq_empty_of_forall_notMem fun a ha => ?_
      rcases hmem a ha with ⟨-, h⟩ | ⟨b, a', -, y', hy', -⟩
      · rw [hst] at h; exact h
      · simp [eighChild, hst] at hy'
    · set y' : EighNode F := ⟨x.k, A', (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      refine (Set.encard_le_encard (t := List.cons b '' {a : List Bool | a.length < m ∧
            ∃ y, eighNodeAt M N signFuel R₀ β a y' (fun a' => s (b :: a')) = some y ∧
              (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s (b :: a))).IsSplit})
          fun a ha => ?_).trans ?_
      · rcases hmem a ha with ⟨-, h⟩ | ⟨b', a', rfl, z, hz, ha'⟩
        · rw [hst] at h; exact h.elim
        · simp only [eighChild, hst] at hz
          split_ifs at hz with hb
          · subst hb
            simp only [Option.some.injEq] at hz
            subst hz
            exact ⟨a', ha', rfl⟩
      · rw [(List.cons_injective).encard_image]
        exact ih y' _
    · obtain ⟨hkp0, hkpk⟩ := pos_and_lt_of_eighStep_eq_split M hst
      set yp : EighNode F := ⟨kp, Ap, (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      set ym : EighNode F := ⟨x.k - kp, Am, (eighNextParams M x.R x.ε x.ℓ).1,
        (eighNextParams M x.R x.ε x.ℓ).2, x.ℓ + 1⟩
      refine (Set.encard_le_encard (t := {[]} ∪ (List.cons true '' {a : List Bool |
            a.length < m ∧ ∃ y, eighNodeAt M N signFuel R₀ β a yp (fun a' => s (true :: a')) =
              some y ∧ (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s (true :: a))).IsSplit} ∪
          List.cons false '' {a : List Bool | a.length < m ∧ ∃ y, eighNodeAt M N signFuel R₀ β
            a ym (fun a' => s (false :: a')) = some y ∧
              (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s (false :: a))).IsSplit}))
          fun a ha => ?_).trans ?_
      · rcases hmem a ha with ⟨rfl, -⟩ | ⟨b', a', rfl, z, hz, ha'⟩
        · exact Or.inl rfl
        · simp only [eighChild, hst] at hz
          cases b'
          · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hz
            subst hz
            exact Or.inr (Or.inr ⟨a', ha', rfl⟩)
          · simp only [↓reduceIte, Option.some.injEq] at hz
            subst hz
            exact Or.inr (Or.inl ⟨a', ha', rfl⟩)
      · refine (Set.encard_union_le _ _).trans ?_
        refine (add_le_add le_rfl (Set.encard_union_le _ _)).trans ?_
        rw [Set.encard_singleton, (List.cons_injective).encard_image,
          (List.cons_injective).encard_image]
        refine (add_le_add le_rfl (add_le_add (ih yp _) (ih ym _))).trans ?_
        have hk : 1 + (yp.k - 1 + (ym.k - 1)) ≤ x.k - 1 := by simp only [yp, ym]; omega
        exact_mod_cast hk

/-- **At most $k$ nodes split**: for every machine, root of size $k$, accuracy and samples, the set
of paths at which `NLAlib.eighNodeAt` has a node whose step `NLAlib.eighStep` (with that path's
sample) is a split has at most $k$ elements. [Shah2024, proof of Theorem 4.2],
$\lvert X_D \rvert = n - 1$ there.
Proof: the tree may be infinite (chains of shifts), so do not induct on the size alone: prove
$S_m(x) \le \max(k - 1, 0)$ for the splits at paths of length at most $m$, by induction on $m$
uniformly in $x$ (a shift: $S_m(x) = S_{m-1}(x')$ with the same size; a split: children of sizes
$k_+, k - k_+ \ge 1$ and $\max(k_+ - 1, 0) + \max(k - k_+ - 1, 0) + 1 \le k - 1$; a leaf: $0$;
count with `Set.encard_union_le` over the paths starting with `true` and `false`), then pass to
the union over $m$ (`Set.encard_iUnion_le`-type monotone limit). L, about 80 lines. -/
theorem encard_eighNodeAt_isSplit_le {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    {N signFuel : ℕ} {R₀ β : F} (x : EighNode F) (s : List Bool → EighSample Su Sg N) :
    {a : List Bool | ∃ y, eighNodeAt M N signFuel R₀ β a x s = some y ∧
      (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit}.encard ≤ x.k := by
  by_contra hlt
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt (not_le.mp hlt))
  have htf : t.Finite := Set.finite_of_encard_eq_coe (k := x.k + 1) (by simpa using htc)
  obtain ⟨m, hm⟩ := (htf.image List.length).bddAbove
  have hsub := Set.encard_le_encard (s := t) (t := {a : List Bool | a.length < m + 1 ∧
      ∃ y, eighNodeAt M N signFuel R₀ β a x s = some y ∧
        (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit})
    fun a ha => ⟨Nat.lt_succ_of_le (hm ⟨a, ha, rfl⟩), hts ha⟩
  have h := hsub.trans (encard_eighNodeAt_isSplit_length_lt_le M (m + 1) x s)
  rw [htc] at h
  have h' : x.k + 1 ≤ x.k - 1 := by exact_mod_cast h
  omega

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

/-- The Newton–Schulz step count is nonnegative in the regime of the analysis. -/
private lemma newtonSchulzSteps_nonneg_of_le_half {s ε : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1 / 2)
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 2) : 0 ≤ newtonSchulzSteps s ε := by
  have h₁ : 0 ≤ Real.logb 2 (min |s| (1 / 2))⁻¹ := by
    rw [abs_of_pos hs, min_eq_left hs₁]
    exact Real.logb_nonneg one_lt_two (one_le_inv₀ hs |>.mpr (by linarith))
  have h₂ : 0 ≤ Real.logb 2 (Real.logb 2 ε⁻¹) := by
    refine Real.logb_nonneg one_lt_two ?_
    rw [← Real.logb_self_eq_one one_lt_two]
    exact Real.logb_le_logb_of_le one_lt_two two_pos ((le_inv_comm₀ two_pos hε).mpr (by linarith))
  unfold newtonSchulzSteps
  linarith

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
    refine newtonSchulzSteps_nonneg_of_le_half (by positivity) ?_ (by positivity) ?_
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

/-- A leaf of `NLAlib.eighAux` (size at most one, or the machine's leaf test true) is an
approximate diagonalization. -/
private lemma isApproxDiagonalization_eighAux_succ_of_leaf {F : Type*}
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
  · exact isApproxDiagonalization_eighAux_succ_of_leaf hM hA (by positivity) hκ₁
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
      · refine isApproxDiagonalization_eighAux_succ_of_leaf hM hyA (by positivity)
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
