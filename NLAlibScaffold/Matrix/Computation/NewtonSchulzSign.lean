/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.NewtonSchulzSign

/-!
# Sharper constants for the rounded Newton–Schulz sign (scaffold, stage HDIAG-BOUNDS)

Statements for `NLAlib/Matrix/Computation/NewtonSchulzSign.lean` (design note
`docs/design/Eigensolvers-HermitianDiagonalization-Bounds.md`, items I8 and I9): one rounded
step with the $\sqrt n$ of the Hermitian rounding on the rounding constant only, not on
$\mu_{\mathrm{MM}}$ (SN3'), and [Shah2024, Theorem 2.6] with the step errors summed as a
geometric series, so that the step count no longer multiplies the precision condition and the
dimension factor of the componentwise stopping test sits in a separate, non-binding condition
(SN4').

## Main results

* `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le_add` (SN3').
* `NLAlib.FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le_of_mul_le`
  (SN4').
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μ μQ : ℕ → ℝ}
  {n : ℕ}

/-- The stored conversion of a natural number $k$ with $\tau \le k \le \Omega$ errs by at most
$ku$. -/
private theorem abs_sub_dec_ofNat_le (hM : M.IsAccurate dec u τ Ω μ μQ cN) {k : ℕ}
    (hkΩ : (k : ℝ) ≤ Ω) (hkτ : τ ≤ k) : |(k : ℝ) - dec (M.ofNat k)| ≤ k * u := by
  have h := hM.ofNat k (by rwa [Nat.abs_cast])
  rwa [Nat.abs_cast, max_eq_left hkτ, mul_comm] at h

/-- The stored $3\mathbf{I} - \mathrm{mm}(\mathbf{A}, \mathbf{A})$ of a rounded Newton–Schulz
step is within $1.21\mu u + 7.5u$ of $3\mathbf{I} - \mathbf{A}^2$. -/
private theorem specNorm_sub_decodeMatrix_negMat_hermShift_le
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ : τ ≤ 1 / 2) (hΩ : 9 ≤ Ω)
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    (hA₁ : specNorm (decodeMatrix dec A) ≤ 11 / 10) :
    specNorm (((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      decodeMatrix dec A * decodeMatrix dec A) -
        decodeMatrix dec (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))) ≤
      121 / 100 * μ n * u + 15 / 2 * u := by
  set a := decodeMatrix dec A
  set x := decodeMatrix dec (M.mm A A)
  set t := dec (M.ofNat 3)
  have ht : |3 - t| ≤ 3 * u := by
    have h := abs_sub_dec_ofNat_le (k := 3) hM (by norm_num; linarith) (by norm_num; linarith)
    simpa only [Nat.cast_ofNat] using h
  have hx : x.IsHermitian := hM.isMatMulErr.isHermitian_of_map_eq_conjTranspose A A hA.eq.symm
  have ha0 := specNorm_nonneg a
  have hsq : specNorm a * specNorm a ≤ 121 / 100 := by nlinarith
  have hw : μ n * u ≤ 1 / 10 := by nlinarith
  have e1 : specNorm (a * a - x) ≤ μ n * u * (121 / 100) := by
    have h := hM.isMatMulErr.specNorm_mul_sub_le A A (hsq.trans (by linarith))
    simp only [max_self] at h
    exact h.trans (mul_le_mul_of_nonneg_left (max_le hsq (by linarith)) (mul_nonneg hμ hu₀))
  have h1 := specNorm_one_le (n := Fin n) (𝕜 := ℂ)
  have hK : specNorm (x - t • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ 9 / 2 := by
    have hxa := specNorm_sub_le (a * a) (a * a - x)
    rw [sub_sub_cancel] at hxa
    have hat := specNorm_mul_le a a
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_real_smul]
    have htt : |t| ≤ 3 + 3 * u := abs_le.mpr ⟨by linarith [(abs_le.mp ht).2],
      by linarith [(abs_le.mp ht).1]⟩
    nlinarith [abs_nonneg t, specNorm_nonneg (1 : Matrix (Fin n) (Fin n) ℂ)]
  have e2 := hM.specNorm_sub_decodeMatrix_hermShift_le hu₀ hx (M.ofNat 3) (hK.trans (by linarith))
  rw [hM.decodeMatrix_negMat]
  have heq : ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - a * a) -
      -decodeMatrix dec (M.hermShift (M.mm A A) (M.ofNat 3)) =
      -((a * a - x) + (t - 3) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        ((x - t • 1) - decodeMatrix dec (M.hermShift (M.mm A A) (M.ofNat 3)))) := by
    module
  rw [heq, specNorm_neg]
  have h3 : specNorm ((t - 3) • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ 3 * u := by
    rw [specNorm_real_smul, abs_sub_comm]; nlinarith [abs_nonneg (3 - t)]
  have h4 : u * max (specNorm (x - t • (1 : Matrix (Fin n) (Fin n) ℂ))) τ ≤ u * (9 / 2) :=
    mul_le_mul_of_nonneg_left (max_le hK (by linarith)) hu₀
  linarith [specNorm_add_le (a * a - x) ((t - 3) • (1 : Matrix (Fin n) (Fin n) ℂ)),
    specNorm_add_le (a * a - x + (t - 3) • (1 : Matrix (Fin n) (Fin n) ℂ))
      ((x - t • 1) - decodeMatrix dec (M.hermShift (M.mm A A) (M.ofNat 3)))]

/-- The stored $\mathrm{mm}(\mathbf{A}, 3\mathbf{I} - \mathbf{A}^2)$ of a rounded Newton–Schulz
step is within $6.3\mu u + 8.25u$ of $\mathbf{A}(3\mathbf{I} - \mathbf{A}^2)$. -/
private theorem specNorm_decodeMatrix_mm_negMat_hermShift_sub_le
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ : τ ≤ 1 / 2) (hΩ : 9 ≤ Ω)
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    (hA₁ : specNorm (decodeMatrix dec A) ≤ 11 / 10) :
    specNorm (decodeMatrix dec (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))) -
      decodeMatrix dec A * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        decodeMatrix dec A * decodeMatrix dec A)) ≤ 63 / 10 * μ n * u + 33 / 4 * u := by
  have eB := specNorm_sub_decodeMatrix_negMat_hermShift_le hM hμ hu₀ hu hτ hΩ hA hA₁
  set a := decodeMatrix dec A
  set b := decodeMatrix dec (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))
  set z := (3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - a * a
  have ha0 := specNorm_nonneg a
  have hw : μ n * u ≤ 1 / 10 := by nlinarith
  have hz : specNorm z ≤ 3 + 121 / 100 := by
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_real_smul]
    nlinarith [specNorm_one_le (n := Fin n) (𝕜 := ℂ), specNorm_mul_le a a]
  have hb : specNorm b ≤ 9 / 2 := by
    have h := specNorm_sub_le z (z - b)
    rw [sub_sub_cancel] at h
    nlinarith
  have hab : specNorm a * specNorm b ≤ 99 / 20 :=
    (mul_le_mul hA₁ hb (specNorm_nonneg b) (by norm_num)).trans (by norm_num)
  have e3 := hM.isMatMulErr.specNorm_mul_sub_le A
    (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3))) (hab.trans (by linarith))
  simp only [max_self] at e3
  have e3' : specNorm (a * b - decodeMatrix dec
      (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3))))) ≤ μ n * u * (99 / 20) :=
    e3.trans (mul_le_mul_of_nonneg_left (max_le hab (by linarith)) (mul_nonneg hμ hu₀))
  have heq : decodeMatrix dec (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))) - a * z =
      -(a * b - decodeMatrix dec (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3))))) +
        a * (b - z) := by
    rw [Matrix.mul_sub a b z]; abel
  rw [heq]
  refine (specNorm_add_le _ _).trans ?_
  rw [specNorm_neg]
  have h5 := (specNorm_mul_le a (b - z)).trans
    (mul_le_mul hA₁ ((specNorm_sub_comm b z).trans_le eB) (specNorm_nonneg _) (by norm_num))
  nlinarith

/-- The Hermitian part divided by $t$ is near $\mathbf{G}$ when $\mathbf{Y}$ is near
$2\mathbf{G}$, for Hermitian $\mathbf{G}$ and $t > 0$. -/
private theorem specNorm_sub_smul_add_conjTranspose_le {g y : Matrix (Fin n) (Fin n) ℂ}
    (hg : gᴴ = g) {t e : ℝ} (ht : 0 < t) (hE : specNorm (y - (2 : ℝ) • g) ≤ e) :
    specNorm (g - t⁻¹ • (y + yᴴ)) ≤ |1 - 4 * t⁻¹| * specNorm g + 2 * t⁻¹ * e := by
  set E := y - (2 : ℝ) • g with hE_def
  have hy : y = E + (2 : ℝ) • g := by rw [hE_def, sub_add_cancel]
  have heq : g - t⁻¹ • (y + yᴴ) = (1 - 4 * t⁻¹) • g - t⁻¹ • (E + Eᴴ) := by
    rw [hy, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hg, star_trivial]
    module
  rw [heq]
  refine (specNorm_sub_le _ _).trans ?_
  rw [specNorm_real_smul, specNorm_real_smul, abs_of_pos (inv_pos.mpr ht)]
  have h := (specNorm_add_le E Eᴴ).trans_eq (by rw [specNorm_conjTranspose])
  have h2 : specNorm (E + Eᴴ) ≤ 2 * e := by linarith
  nlinarith [inv_pos.mpr ht]

/-- **One rounded Newton–Schulz step, sharp form** (SN3'): under the hypotheses of
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le`,
$$\|g(\mathbf{A}) - \tilde g(\mathbf{A})\|_2 \le \bigl(4\mu(n) + 10 + 10\sqrt n\bigr)u \,.$$
The $\sqrt n$ comes only from the entrywise rounding of the stored Hermitian part (gap G1 of
[Shah2024]); the product errors are normwise. [Shah2024, Lemma 2.1].
Proof: the proof of SN3 with its last step changed: the bound on the Hermitian part of the
product, $(3.23\mu + 6.23)u$, and the rounding of `NLAlib.FloatMachine.hermAvg`,
$3u(\sqrt n\|\mathbf{Z}\|_2 + 2n\tau) \le 3u(2\sqrt n + 1)$
(`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermAvg_le`), are added instead of
multiplying the first by $\sqrt n$; $3.23\mu + 9.23 + 6\sqrt n \le 4\mu + 10 + 10\sqrt n$.
M, about 120 lines (mostly SN3's, made public or copied). -/
theorem FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_newtonSchulzRounded_le_add
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 ≤ Ω)
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    (hA₁ : specNorm (decodeMatrix dec A) ≤ 11 / 10) :
    specNorm ((2⁻¹ : ℝ) • (decodeMatrix dec A * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      decodeMatrix dec A * decodeMatrix dec A)) - decodeMatrix dec (newtonSchulzRounded M A)) ≤
        (4 * μ n + 10 + 10 * √(n : ℝ)) * u := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ∀ X : Matrix (Fin 0) (Fin 0) ℂ, specNorm X = 0 := fun X => by
      rw [Subsingleton.elim X 0, specNorm_zero]
    rw [h0]
    exact mul_nonneg (by simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, add_zero]; linarith)
      hu₀
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hτ' : τ ≤ 1 / 2 := by nlinarith
  have hs : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hw : 8 * u + μ n * u ≤ 1 / 10 := by linarith [mul_add u 8 (μ n)]
  have hw0 := mul_nonneg hμ hu₀
  have hu' : u ≤ 1 / 80 := by linarith
  have eY := specNorm_decodeMatrix_mm_negMat_hermShift_sub_le hM hμ hu₀ hu hτ' hΩ hA hA₁
  set a := decodeMatrix dec A
  set Y := M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))
  set g := (2⁻¹ : ℝ) • (a * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - a * a))
  have hgc : cfc newtonSchulz a = g := hA.cfc_newtonSchulz
  have hgH : gᴴ = g := by
    have h : (cfc newtonSchulz a).IsHermitian := cfc_predicate newtonSchulz a
    rw [hgc] at h; exact h.eq
  have hg1 : specNorm g ≤ 1 := by
    rw [← hgc]
    refine hA.specNorm_cfc_le zero_le_one fun x hx => abs_newtonSchulz_le_one ?_
    rw [hA.spectrum_eq_image_eigenvalue] at hx
    obtain ⟨k, -, rfl⟩ := hx
    linarith [hA.abs_eigenvalue_le_specNorm k]
  have h2g : a * ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) - a * a) = (2 : ℝ) • g := by
    rw [smul_smul]; norm_num
  rw [h2g] at eY
  set t := dec (M.ofNat 4)
  have ht : |4 - t| ≤ 4 * u := by
    have h := abs_sub_dec_ofNat_le (k := 4) hM (by norm_num; linarith) (by norm_num; linarith)
    simpa only [Nat.cast_ofNat] using h
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  have ht0 : 0 < t := by linarith
  have htinv : t⁻¹ ≤ 10 / 39 :=
    (inv_anti₀ (by norm_num) (by linarith : (39 / 10 : ℝ) ≤ t)).trans_eq (by norm_num)
  have htinv0 : 0 < t⁻¹ := inv_pos.mpr (by linarith)
  have h4 : |1 - 4 * t⁻¹| ≤ 2 * u := by
    rw [show 1 - 4 * t⁻¹ = (t - 4) * t⁻¹ by field_simp, abs_mul, abs_of_pos htinv0,
      abs_sub_comm]
    nlinarith [abs_nonneg (4 - t)]
  set D := specNorm (g - t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ))
  have hD : D ≤ 2 * u + 2 * (10 / 39) * (63 / 10 * μ n * u + 33 / 4 * u) :=
    (specNorm_sub_smul_add_conjTranspose_le hgH (by linarith) eY).trans
      (add_le_add (by nlinarith [specNorm_nonneg g])
        (by gcongr))
  have hy : specNorm (decodeMatrix dec Y) ≤ 263 / 100 := by
    have h := specNorm_add_le ((2 : ℝ) • g) (decodeMatrix dec Y - (2 : ℝ) • g)
    rw [add_sub_cancel, specNorm_real_smul, abs_two] at h
    nlinarith
  have e5 := hM.specNorm_sub_decodeMatrix_hermAvg_le hu₀ (by linarith) hτ₀ Y (c := M.ofNat 4)
    (by rw [abs_of_pos (by linarith)]; linarith) (by linarith)
  have hN1 : specNorm (t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ)) ≤ 2 := by
    have h := specNorm_sub_le g (g - t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ))
    rw [sub_sub_cancel] at h
    nlinarith [mul_nonneg hμ hu₀]
  have hfin : g - decodeMatrix dec (newtonSchulzRounded M A) =
      (g - t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ)) +
        (t⁻¹ • (decodeMatrix dec Y + (decodeMatrix dec Y)ᴴ) -
          decodeMatrix dec (M.hermAvg Y (M.ofNat 4))) := by
    rw [sub_add_sub_cancel]; rfl
  rw [hfin]
  refine (specNorm_add_le _ _).trans ?_
  -- the stored Hermitian average costs `3u(2√n + 1)`, since `2nτ ≤ 1`
  have k1 := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hN1 (Real.sqrt_nonneg (n : ℝ)))
    (by linarith : 2 * (n : ℝ) * τ ≤ 1)) (by positivity : (0 : ℝ) ≤ 3 * u)
  have k2 := e5.trans k1
  have k3 := mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hu₀
  linarith

/-! ### Helpers copied from the proof of SN4 (private there) -/

private theorem cfc_sign_smul {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian)
    {c : ℝ} (hc : 0 < c) : cfc Real.sign (c • X) = cfc Real.sign X := by
  rw [← cfc_const_mul_id c X hX.isSelfAdjoint,
    ← cfc_comp' Real.sign (c * ·) X ((X.finite_real_spectrum.image _).continuousOn _)]
  congr 1
  funext x
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hc h)]
  · rw [mul_zero]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hc h)]

private theorem cfc_sq_sub_one {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian) :
    cfc (fun x : ℝ => x ^ 2 - 1) X = X * X - 1 := by
  rw [cfc_sub (fun x : ℝ => x ^ 2) (fun _ => 1) X, cfc_pow_id X 2 hX.isSelfAdjoint,
    cfc_const_one ℝ X, sq]

private theorem abs_one_sub_sq_le_specNorm {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) {x : ℝ} (hx : x ∈ spectrum ℝ X) : |1 - x ^ 2| ≤ specNorm (X * X - 1) := by
  rw [← cfc_sq_sub_one hX]
  have hH : (cfc (fun x : ℝ => x ^ 2 - 1) X).IsHermitian := cfc_predicate _ X
  rw [abs_sub_comm]
  refine hH.abs_le_specNorm_of_mem_spectrum ?_
  rw [cfc_map_spectrum (fun x : ℝ => x ^ 2 - 1) X hX.isSelfAdjoint]
  exact ⟨x, hx, rfl⟩

private theorem specNorm_mul_self_sub_one_le {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ spectrum ℝ X, |1 - x ^ 2| ≤ c) :
    specNorm (X * X - 1) ≤ c := by
  rw [← cfc_sq_sub_one hX]
  exact hX.specNorm_cfc_le hc fun x hx => abs_sub_comm (x ^ 2) 1 ▸ h x hx

/-- A $k \times k$ matrix with entries of modulus at most $c$ has spectral norm at most $kc$. -/
private theorem specNorm_le_card_mul_of_norm_apply_le {k : ℕ}
    {X : Matrix (Fin k) (Fin k) ℂ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖X i j‖ ≤ c) :
    specNorm X ≤ k * c := by
  refine (specNorm_le_frobNorm X).trans ?_
  refine (pow_le_pow_iff_left₀ (frobNorm_nonneg X) (by positivity) two_ne_zero).mp ?_
  rw [frobNorm_sq_eq_sum]
  calc ∑ i, ∑ j, ‖X i j‖ ^ 2 ≤ ∑ _i : Fin k, ∑ _j : Fin k, c ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (k * c) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### Scalar chains of the perturbed iteration -/

private theorem IsNewtonSchulzChain.succ {s δ y z : ℝ} {k : ℕ}
    (h : IsNewtonSchulzChain s δ y k) (hδ : 0 ≤ δ) (hz : |z - newtonSchulz y| ≤ δ) :
    IsNewtonSchulzChain s δ z (k + 1) := by
  obtain ⟨x, hxk, h₁, h₂, hstep⟩ := h
  refine ⟨fun j => if j ≤ k then x j else newtonSchulz^[j - (k + 1)] z, ?_, ?_, ?_, ?_⟩
  · simp
  · simpa using h₁
  · simpa using h₂
  · intro j
    rcases lt_trichotomy j k with hj | rfl | hj
    · simp only [show j + 1 ≤ k by omega, hj.le, if_true]
      exact hstep j
    · simp only [le_refl, if_true, show ¬ j + 1 ≤ j by omega, if_false, Nat.sub_self,
        Function.iterate_zero, id, hxk]
      exact hz
    · simp only [show ¬ j + 1 ≤ k by omega, show ¬ j ≤ k by omega, if_false,
        show j + 1 - (k + 1) = (j - (k + 1)) + 1 by omega, Function.iterate_succ_apply',
        sub_self, abs_zero]
      exact hδ

private theorem IsNewtonSchulzChain.le_abs {s δ y : ℝ} {k : ℕ}
    (h : IsNewtonSchulzChain s δ y k) (hs : s ≤ 1 / 2) (hδ : 20 * δ ≤ s) : s ≤ |y| := by
  obtain ⟨x, rfl, h₁, h₂, hstep⟩ := h
  have := min_abs_le_abs_of_abs_sub_newtonSchulz_le (by linarith) (by linarith) (by linarith)
    hstep k
  exact le_trans (le_min h₁ hs) this

/-! ### One step of the matrix iteration -/

/-! ### The stopping test -/

/-- The stored threshold $\mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$ is close to
$\varepsilon/(4n)$. -/
private theorem threshold_bounds (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hu₀ : 0 ≤ u)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {ε : F}
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1 / 2) (hu : 640 * n * u ≤ dec ε) :
    n * dec (M.div ε (M.ofNat (4 * n))) ≤ 13 / 50 * dec ε ∧
      dec ε / 5 ≤ n * dec (M.div ε (M.ofNat (4 * n))) := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc := hM.ofNat (4 * n) (by push_cast; rw [abs_of_nonneg (by positivity)]; linarith)
  push_cast at hc
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * n),
    max_eq_left (by nlinarith : τ ≤ 4 * n)] at hc
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hc
  set c := dec (M.ofNat (4 * n))
  have hu₁ : u ≤ 1 / 1280 := by nlinarith
  have hcpos : 0 < c := by nlinarith
  set q := dec ε / c with hqdef
  have hq : q * c = dec ε := div_mul_cancel₀ _ hcpos.ne'
  have hq₀ : 0 < q := div_pos hε hcpos
  have hq₁ : q ≤ 1 / 4 := by nlinarith
  have hd := hM.div ε (M.ofNat (4 * n)) hcpos.ne' (by rw [abs_of_pos hq₀]; linarith)
  rw [← hqdef, abs_of_pos hq₀] at hd
  have hd' : |q - dec (M.div ε (M.ofNat (4 * n)))| ≤ u * (q + τ) :=
    hd.trans (mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hu₀)
  obtain ⟨hd₁, hd₂⟩ := abs_le.mp hd'
  have hnτ : n * τ ≤ 1 / 2 := by linarith
  constructor <;> nlinarith [mul_nonneg hu₀ hq₀.le, mul_le_mul_of_nonneg_left hnτ hu₀]

/-- The computed test matrix $\mathrm{mm}(\mathbf{X}, \mathbf{X}) - \mathbf{I}$ is within
$2(8 + \mu(n))u$ of $\mathbf{X}^2 - \mathbf{I}$. -/
private theorem specNorm_mul_self_sub_one_sub_decodeMatrix_le
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u)
    (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₁ : τ ≤ 1) (hΩ : 9 ≤ Ω)
    {X : Matrix (Fin n) (Fin n) (F × F)} (hX : (decodeMatrix dec X).IsHermitian)
    (hXn : specNorm (decodeMatrix dec X) ≤ 11 / 10) :
    specNorm ((decodeMatrix dec X * decodeMatrix dec X - 1) -
      decodeMatrix dec (M.hermShift (M.mm X X) M.one)) ≤ 2 * (8 + μ n) * u := by
  set Xd := decodeMatrix dec X
  set P := decodeMatrix dec (M.mm X X)
  have hX₀ := specNorm_nonneg Xd
  have hsq : specNorm Xd * specNorm Xd ≤ 121 / 100 := by nlinarith
  have hE₁ : specNorm (Xd * Xd - P) ≤ μ n * u * (121 / 100) := by
    have h := hM.isMatMulErr.specNorm_mul_sub_le X X (le_trans hsq (by linarith))
    simp only [max_self] at h
    exact h.trans (mul_le_mul_of_nonneg_left (max_le hsq (by linarith)) (by positivity))
  have hPH : P.IsHermitian := hM.isMatMulErr.isHermitian_of_map_eq_conjTranspose X X hX.symm
  have hX₁ : specNorm (Xd * Xd - 1) ≤ 1 :=
    specNorm_mul_self_sub_one_le hX zero_le_one fun x hx => by
      have := (hX.abs_le_specNorm_of_mem_spectrum hx).trans hXn
      rw [abs_le]; constructor <;> nlinarith [abs_nonneg x, sq_abs x]
  have hP₁ : specNorm (P - 1) ≤ 2 := by
    have : P - 1 = (Xd * Xd - 1) - (Xd * Xd - P) := by abel
    rw [this]
    refine (specNorm_sub_le _ _).trans ?_
    nlinarith
  have hE₂ := hM.specNorm_sub_decodeMatrix_hermShift_le hu₀ hPH M.one
    (by rw [hM.dec_one, one_smul]; linarith)
  rw [hM.dec_one, one_smul] at hE₂
  have hE₂' : specNorm ((P - 1) - decodeMatrix dec (M.hermShift (M.mm X X) M.one)) ≤ 2 * u :=
    hE₂.trans (by nlinarith [mul_le_mul_of_nonneg_left (max_le hP₁ (by linarith : τ ≤ 2)) hu₀])
  have : (Xd * Xd - 1) - decodeMatrix dec (M.hermShift (M.mm X X) M.one) =
      (Xd * Xd - P) + ((P - 1) - decodeMatrix dec (M.hermShift (M.mm X X) M.one)) := by abel
  rw [this]
  refine (specNorm_add_le _ _).trans ?_
  nlinarith

private theorem newtonSchulzTest_eq_true_iff (hM : M.IsAccurate dec u τ Ω μ μQ cN) (η : F)
    (X : Matrix (Fin n) (Fin n) (F × F)) :
    newtonSchulzTest M η X = true ↔ ∀ i j,
      |dec (M.hermShift (M.mm X X) M.one i j).1| ≤ dec η ∧
        |dec (M.hermShift (M.mm X X) M.one i j).2| ≤ dec η := by
  simp only [newtonSchulzTest, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.and_eq_true, hM.le_iff, hM.dec_neg, abs_le, and_assoc]

/-- The size condition $640n(8 + \mu(n))u \le \varepsilon \le 1/2$ bounds $640nu$ by
$\varepsilon$ and $u(8 + \mu(n))$ by $1/10$. -/
private theorem unitRoundoff_bounds {μn u ε : ℝ} (hn : 0 < n) (hμ : 0 ≤ μn) (hu₀ : 0 ≤ u)
    (hε₁ : ε ≤ 1 / 2) (hk : 640 * n * (8 + μn) * u ≤ ε) :
    640 * n * u ≤ ε ∧ u * (8 + μn) ≤ 1 / 10 := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · nlinarith [mul_nonneg hμ hu₀, mul_nonneg hu₀ (by positivity : (0 : ℝ) ≤ n)]
  · nlinarith [mul_nonneg hu₀ (by linarith : 0 ≤ 8 + μn)]

/-- If the test passes, the iterate is within `2ε/3` of its sign. -/
private theorem specNorm_sub_cfc_sign_le_of_newtonSchulzTest
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {ε : F} (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 1 / 2) (hk : 640 * n * (8 + μ n) * u ≤ dec ε)
    {X : Matrix (Fin n) (Fin n) (F × F)} (hX : (decodeMatrix dec X).IsHermitian)
    (hXn : specNorm (decodeMatrix dec X) ≤ 11 / 10)
    (htest : newtonSchulzTest M (M.div ε (M.ofNat (4 * n))) X = true) :
    specNorm (decodeMatrix dec X - cfc Real.sign (decodeMatrix dec X)) ≤ 2 / 3 * dec ε := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hun, hu⟩ := unitRoundoff_bounds hn hμ hu₀ hε₁ hk
  have hη := (threshold_bounds hM hu₀ hτ₀ hτ hΩ hn hε hε₁ hun).1
  set η := dec (M.div ε (M.ofNat (4 * n)))
  have hE := specNorm_mul_self_sub_one_sub_decodeMatrix_le hM hμ hu₀ hu (by nlinarith)
    (by linarith) hX hXn
  rw [newtonSchulzTest_eq_true_iff hM] at htest
  have hη₀ : 0 ≤ η := le_trans (abs_nonneg _) (htest ⟨0, hn⟩ ⟨0, hn⟩).1
  have hT := specNorm_le_card_mul_of_norm_apply_le
    (X := decodeMatrix dec (M.hermShift (M.mm X X) M.one)) (by positivity : 0 ≤ 2 * η)
    fun i j => (Complex.norm_le_abs_re_add_abs_im _).trans
      ((add_le_add (htest i j).1 (htest i j).2).trans_eq (two_mul η).symm)
  have hS : specNorm (decodeMatrix dec X * decodeMatrix dec X - 1) ≤ 2 / 3 * dec ε := by
    have := specNorm_add_le (decodeMatrix dec X * decodeMatrix dec X - 1 -
      decodeMatrix dec (M.hermShift (M.mm X X) M.one))
      (decodeMatrix dec (M.hermShift (M.mm X X) M.one))
    rw [sub_add_cancel] at this
    nlinarith [mul_nonneg hu₀ (by linarith : 0 ≤ 8 + μ n)]
  exact hX.specNorm_sub_cfc_sign_le (by positivity) fun x hx =>
    (abs_one_sub_sq_le_specNorm hX hx).trans hS

/-- If every eigenvalue is close to `±1`, the test passes. -/
private theorem newtonSchulzTest_of_forall_mem_spectrum
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {ε : F} (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 1 / 2) (hk : 640 * n * (8 + μ n) * u ≤ dec ε)
    {X : Matrix (Fin n) (Fin n) (F × F)} (hX : (decodeMatrix dec X).IsHermitian)
    (hXn : specNorm (decodeMatrix dec X) ≤ 11 / 10)
    (h : ∀ x ∈ spectrum ℝ (decodeMatrix dec X), |1 - x ^ 2| ≤ dec ε / (16 * n)) :
    newtonSchulzTest M (M.div ε (M.ofNat (4 * n))) X = true := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hun, hu⟩ := unitRoundoff_bounds hn hμ hu₀ hε₁ hk
  have hη := (threshold_bounds hM hu₀ hτ₀ hτ hΩ hn hε hε₁ hun).2
  set η := dec (M.div ε (M.ofNat (4 * n)))
  have hE := specNorm_mul_self_sub_one_sub_decodeMatrix_le hM hμ hu₀ hu (by nlinarith)
    (by linarith) hX hXn
  have hS := specNorm_mul_self_sub_one_le hX (by positivity) h
  have hT : specNorm (decodeMatrix dec (M.hermShift (M.mm X X) M.one)) ≤
      dec ε / (16 * n) + 2 * (8 + μ n) * u := by
    have := specNorm_sub_le (decodeMatrix dec X * decodeMatrix dec X - 1)
      (decodeMatrix dec X * decodeMatrix dec X - 1 -
        decodeMatrix dec (M.hermShift (M.mm X X) M.one))
    rw [sub_sub_cancel] at this
    linarith
  have hη' : dec ε / (16 * n) + 2 * (8 + μ n) * u ≤ η := by
    rw [div_add' _ _ _ (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hu₀ (by linarith : 0 ≤ 8 + μ n)]
  rw [newtonSchulzTest_eq_true_iff hM]
  intro i j
  have hij := (norm_apply_le_specNorm _ i j).trans (hT.trans hη')
  exact ⟨(Complex.abs_re_le_norm _).trans hij, (Complex.abs_im_le_norm _).trans hij⟩


/-! ### Geometric growth of the least eigenvalue modulus -/

/-- For $t \le |x| \le 11/10$, $|g(x)| \ge \min(11t/8, 11/16)$. -/
private theorem min_le_abs_newtonSchulz {t x : ℝ} (ht : 0 ≤ t) (htx : t ≤ |x|)
    (hx : |x| ≤ 11 / 10) : min (11 / 8 * t) (11 / 16) ≤ |newtonSchulz x| := by
  have hx0 := abs_nonneg x
  have hg : |newtonSchulz x| = |x| * (3 - |x| ^ 2) / 2 := by
    unfold newtonSchulz
    rw [abs_div, abs_mul, sq_abs, abs_of_pos (by nlinarith [sq_abs x] : (0 : ℝ) < 3 - x ^ 2),
      abs_two]
  rw [hg]
  rcases le_or_gt |x| (1 / 2) with h | h
  · exact (min_le_left _ _).trans (by nlinarith)
  · have h₁ : 0 ≤ 11 / 4 - |x| ^ 2 - |x| / 2 := by nlinarith
    exact (min_le_right _ _).trans (by nlinarith [mul_nonneg (sub_nonneg.2 h.le) h₁])

/-- The potential `7δ/t` pays for one step at the new bound `t'`, up to `4δ`. -/
private theorem nine_mul_div_min_le {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) (ht₁ : 12 * δ ≤ t)
    (ht₂ : t ≤ 1 / 2) : 9 * δ / min (11 / 8 * t - δ) (1 / 2) ≤ 7 * δ / t + 4 * δ := by
  rcases min_cases (11 / 8 * t - δ) (1 / 2 : ℝ) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · have hq : 9 * δ / (11 / 8 * t - δ) ≤ 7 * δ / t := by
      rw [div_le_div_iff₀ (by linarith) ht]
      nlinarith [mul_le_mul_of_nonneg_left ht₁ hδ]
    linarith
  · have : 14 * δ ≤ 7 * δ / t := by rw [le_div_iff₀ ht]; nlinarith
    linarith

/-- One rounded step keeps every eigenvalue on a perturbed scalar chain, raises the lower bound
`t` on the eigenvalue moduli to `min (11t/8 − δ) (1/2)`, and moves the sign by at most `2δ`
over the new bound, for `δ` the error of SN3'. -/
private theorem newtonSchulzRounded_chain_and_specNorm_le_add
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n)
    (hu₀ : 0 ≤ u) (hu : u * (8 + μ n) ≤ 1 / 10) (hτ₀ : 0 ≤ τ) (hτ : τ * (2 * n) ≤ 1)
    (hΩ : 9 ≤ Ω) {s t : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1 / 2)
    (hδ : 20 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) ≤ s) (ht : 0 < t)
    (ht₁ : 12 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) ≤ t) {k : ℕ}
    {X : Matrix (Fin n) (Fin n) (F × F)} (hX : (decodeMatrix dec X).IsHermitian)
    (hch : ∀ y ∈ spectrum ℝ (decodeMatrix dec X),
      IsNewtonSchulzChain s ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) y k)
    (hXt : ∀ y ∈ spectrum ℝ (decodeMatrix dec X), t ≤ |y|) :
    (∀ z ∈ spectrum ℝ (decodeMatrix dec (newtonSchulzRounded M X)),
      IsNewtonSchulzChain s ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) z (k + 1) ∧
        min (11 / 8 * t - (4 * μ n + 10 + 10 * √(n : ℝ)) * u) (1 / 2) ≤ |z|) ∧
    specNorm (cfc Real.sign (decodeMatrix dec X) -
      cfc Real.sign (decodeMatrix dec (newtonSchulzRounded M X))) ≤
        2 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) /
          min (11 / 8 * t - (4 * μ n + 10 + 10 * √(n : ℝ)) * u) (1 / 2) := by
  set δ := (4 * μ n + 10 + 10 * √(n : ℝ)) * u
  set t' := min (11 / 8 * t - δ) (1 / 2)
  have hδ₀ : 0 ≤ δ := by positivity
  have ht' : 0 < t' := lt_min (by linarith) (by norm_num)
  have hY := hM.isHermitian_decodeMatrix_newtonSchulzRounded X
  have hgX : (cfc newtonSchulz (decodeMatrix dec X)).IsHermitian := cfc_predicate _ _
  have hXn : specNorm (decodeMatrix dec X) ≤ 11 / 10 :=
    hX.specNorm_le_of_forall_mem_spectrum_abs_le (by norm_num) fun y hy =>
      (hch y hy).abs_le (by linarith)
  have herr : specNorm (cfc newtonSchulz (decodeMatrix dec X) -
      decodeMatrix dec (newtonSchulzRounded M X)) ≤ δ := by
    rw [hX.cfc_newtonSchulz]
    exact hM.specNorm_sub_decodeMatrix_newtonSchulzRounded_le_add hμ hu₀ hu hτ₀ hτ hΩ hX hXn
  have ht'δ : t' ≤ min (11 / 8 * t) (11 / 16) - δ := by
    rcases min_cases (11 / 8 * t) (11 / 16 : ℝ) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (by linarith)
  have hchY : ∀ z ∈ spectrum ℝ (decodeMatrix dec (newtonSchulzRounded M X)),
      IsNewtonSchulzChain s δ z (k + 1) ∧ t' ≤ |z| := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hgX.exists_mem_spectrum_abs_sub_le hY hz
    rw [cfc_map_spectrum newtonSchulz (decodeMatrix dec X) hX.isSelfAdjoint
      ((decodeMatrix dec X).finite_real_spectrum.continuousOn _)] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    have hyz : |z - newtonSchulz y| ≤ δ := by rw [abs_sub_comm]; exact hwz.trans herr
    refine ⟨(hch y hy).succ hδ₀ hyz, ?_⟩
    have h₁ := min_le_abs_newtonSchulz ht.le (hXt y hy) ((hch y hy).abs_le (by linarith))
    have h₂ := abs_sub_abs_le_abs_sub (newtonSchulz y) z
    rw [abs_sub_comm (newtonSchulz y)] at h₂
    linarith
  refine ⟨hchY, ?_⟩
  have h3 : (11 / 10 : ℝ) < √3 := Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [← hX.cfc_sign_cfc_newtonSchulz fun y hy =>
    ⟨hs.trans_le ((hch y hy).le_abs hs₁ hδ), ((hch y hy).abs_le (by linarith)).trans_lt h3⟩,
    specNorm_sub_comm]
  refine (hY.specNorm_cfc_sign_sub_cfc_sign_le hgX ht' fun z hz => (hchY z hz).2).trans ?_
  rw [specNorm_sub_comm]
  gcongr

/-! ### The loop -/

/-- **The loop invariant**: from an iterate at step `k` whose eigenvalues lie on perturbed scalar
chains and have modulus at least `t`, the loop returns a matrix within `2ε/3 + 7δ/t` plus `4δ`
per remaining step of the sign. -/
private theorem specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzLoop_le_add
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) (hn : 0 < n) {ε : F} (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 1 / 2) (hk : 640 * n * (8 + μ n) * u ≤ dec ε) {s : ℝ} (hs : 0 < s)
    (hs₁ : s ≤ 1 / 2) (hδs : 20 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) ≤ s)
    (hδε : 10 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) ≤ dec ε / (16 * n)) (N k : ℕ)
    (X : Matrix (Fin n) (Fin n) (F × F)) (hX : (decodeMatrix dec X).IsHermitian)
    (hch : ∀ y ∈ spectrum ℝ (decodeMatrix dec X),
      IsNewtonSchulzChain s ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) y k)
    {t : ℝ} (ht : 0 < t) (ht₁ : 12 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) ≤ t)
    (ht₂ : t ≤ 1 / 2) (hXt : ∀ y ∈ spectrum ℝ (decodeMatrix dec X), t ≤ |y|)
    (hN : newtonSchulzSteps s (dec ε / (16 * n)) ≤ k + N) :
    specNorm (cfc Real.sign (decodeMatrix dec X) -
      decodeMatrix dec (newtonSchulzLoop M (M.div ε (M.ofNat (4 * n))) N X)) ≤
        2 / 3 * dec ε + 7 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u) / t +
          max 0 (newtonSchulzSteps s (dec ε / (16 * n)) + 1 - k) *
            (4 * ((4 * μ n + 10 + 10 * √(n : ℝ)) * u)) := by
  set δ := (4 * μ n + 10 + 10 * √(n : ℝ)) * u
  set N₀ := newtonSchulzSteps s (dec ε / (16 * n))
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hδ₀ : 0 ≤ δ := by positivity
  have hε' : 0 < dec ε / (16 * n) := by positivity
  have hε'₁ : dec ε / (16 * n) ≤ 3 / 80 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hXn : ∀ {j : ℕ} {Y : Matrix (Fin n) (Fin n) (F × F)}, (decodeMatrix dec Y).IsHermitian →
      (∀ y ∈ spectrum ℝ (decodeMatrix dec Y), IsNewtonSchulzChain s δ y j) →
        specNorm (decodeMatrix dec Y) ≤ 11 / 10 := fun hY hchY =>
    hY.specNorm_le_of_forall_mem_spectrum_abs_le (by norm_num) fun y hy =>
      (hchY y hy).abs_le (by linarith)
  induction N generalizing k X t with
  | zero =>
    have hrest : 0 ≤ max 0 (N₀ + 1 - k) * (4 * δ) := by positivity
    have hpot : 0 ≤ 7 * δ / t := by positivity
    have h := hX.specNorm_sub_cfc_sign_le hε'.le fun y hy =>
      (hch y hy).abs_one_sub_sq_le hs hδs hε' hδε hε'₁ (by simpa using hN)
    have hε'₂ : dec ε / (16 * n) ≤ 2 / 3 * dec ε := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    rw [newtonSchulzLoop, specNorm_sub_comm]
    linarith
  | succ N ih =>
    rw [newtonSchulzLoop]
    by_cases htest : newtonSchulzTest M (M.div ε (M.ofNat (4 * n))) X = true
    · rw [if_pos htest, specNorm_sub_comm]
      have hrest : 0 ≤ max 0 (N₀ + 1 - k) * (4 * δ) := by positivity
      have hpot : 0 ≤ 7 * δ / t := by positivity
      have := specNorm_sub_cfc_sign_le_of_newtonSchulzTest hM hμ hu₀ hτ₀ hτ hΩ hn hε hε₁ hk hX
        (hXn hX hch) htest
      linarith
    · rw [if_neg htest]
      have hkN : (k : ℝ) < N₀ := by
        by_contra hk'
        exact htest (newtonSchulzTest_of_forall_mem_spectrum hM hμ hu₀ hτ₀ hτ hΩ hn hε hε₁ hk
          hX (hXn hX hch) fun y hy =>
            (hch y hy).abs_one_sub_sq_le hs hδs hε' hδε hε'₁ (not_lt.mp hk'))
      obtain ⟨hchY, hstep⟩ := newtonSchulzRounded_chain_and_specNorm_le_add hM hμ hu₀
        (unitRoundoff_bounds hn hμ hu₀ hε₁ hk).2 hτ₀ hτ (by linarith) hs hs₁ hδs ht ht₁ hX hch hXt
      have ht' : t ≤ min (11 / 8 * t - δ) (1 / 2) := le_min (by linarith) ht₂
      have hIH := ih (k := k + 1) (X := newtonSchulzRounded M X)
        (hX := hM.isHermitian_decodeMatrix_newtonSchulzRounded X)
        (hch := fun z hz => (hchY z hz).1) (ht := ht.trans_le ht') (ht₁ := ht₁.trans ht')
        (ht₂ := min_le_right _ _) (hXt := fun z hz => (hchY z hz).2)
        (hN := by push_cast at hN ⊢; linarith)
      have htri := specNorm_add_le
        (cfc Real.sign (decodeMatrix dec X) -
          cfc Real.sign (decodeMatrix dec (newtonSchulzRounded M X)))
        (cfc Real.sign (decodeMatrix dec (newtonSchulzRounded M X)) - decodeMatrix dec
          (newtonSchulzLoop M (M.div ε (M.ofNat (4 * n))) N (newtonSchulzRounded M X)))
      rw [sub_add_sub_cancel] at htri
      push_cast at hIH
      rw [max_eq_right (by linarith)] at hIH ⊢
      have hpot := nine_mul_div_min_le hδ₀ ht ht₁ ht₂
      have hsplit : 9 * δ / min (11 / 8 * t - δ) (1 / 2) =
          2 * δ / min (11 / 8 * t - δ) (1 / 2) + 7 * δ / min (11 / 8 * t - δ) (1 / 2) := by
        ring
      linarith

/-- The two size conditions of SN4' in terms of the step error `δ` of SN3'. -/
private theorem stepError_bounds (hn : 0 < n) {μn u r ε N₀ δ : ℝ} (hμ : 0 ≤ μn) (hu₀ : 0 ≤ u)
    (hr₀ : 0 ≤ r) (hε₁ : ε ≤ 1 / 2) (hN₀ : 0 ≤ N₀)
    (hδ : δ = (4 * μn + 10 + 10 * √(n : ℝ)) * u)
    (hu : 32 * (4 * μn + 10 + 10 * √(n : ℝ)) * u ≤ r * ε)
    (hstop : 640 * (n + N₀ + 1) * (4 * μn + 10 + 10 * √(n : ℝ)) * u ≤ ε) :
    32 * δ ≤ r * ε ∧ 640 * (N₀ + 1) * δ ≤ ε ∧ 640 * n * (8 + μn) * u ≤ ε ∧
      20 * δ ≤ r / 2 ∧ 10 * δ ≤ ε / (16 * n) ∧ (√(n : ℝ) + 1) * u ≤ δ / 10 := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqn : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hδ₀ : 0 ≤ δ := by rw [hδ]; positivity
  have h₁ : 32 * δ ≤ r * ε := by rw [hδ]; linarith
  have h₂ : 640 * (n + N₀ + 1) * δ ≤ ε := by rw [hδ]; linarith
  have h₃ : 640 * n * δ ≤ ε := by nlinarith [mul_nonneg (by linarith : 0 ≤ N₀ + 1) hδ₀]
  have h₄ : (8 + μn) * u ≤ δ := by
    rw [hδ]; nlinarith [mul_nonneg hμ hu₀, mul_nonneg hsqn hu₀]
  refine ⟨h₁, by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n) hδ₀], ?_,
    by nlinarith [mul_le_mul_of_nonneg_left hε₁ hr₀],
    by rw [le_div_iff₀ (by positivity)]; nlinarith, by rw [hδ]; nlinarith [mul_nonneg hμ hu₀]⟩
  nlinarith [mul_le_mul_of_nonneg_left h₄ (by positivity : (0 : ℝ) ≤ 640 * n)]

/-- The potential at the start bound `min (r − δ/10) (1/2)` under `32δ ≤ rε`. -/
private theorem seven_mul_div_min_le {δ r ε : ℝ} (hδ₀ : 0 ≤ δ) (hε : 0 < ε) (hε₁ : ε ≤ 1 / 2)
    (hδr : 32 * δ ≤ r * ε) (hr : 0 < r - δ / 10) :
    7 * δ / min (r - δ / 10) (1 / 2) ≤ ε / 4 + 14 * δ := by
  rcases min_cases (r - δ / 10) (1 / 2 : ℝ) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · rw [div_le_iff₀ hr]
    nlinarith [mul_nonneg hδ₀ hr.le, mul_nonneg hδ₀ hε.le]
  · rw [div_div_eq_mul_div, div_one]; linarith

/-- **Accuracy of the rounded Newton–Schulz sign with geometric error propagation** (SN4'): let
the machine meet `NLAlib.FloatMachine.IsAccurate`, $\mathbf{A}$ have Hermitian decoding with
$\|\mathbf{A}\|_2 \le b$ and every eigenvalue of modulus at least $a > 0$, $0 < \varepsilon \le
1/2$, $\nu = 4\mu(n) + 10 + 10\sqrt n$, $N_0 = N(a/(2b), \varepsilon/(16n))$ and
$$32\,\nu u \le \frac ab\,\varepsilon \,, \qquad 640\,(n + N_0 + 1)\,\nu u \le \varepsilon \,.$$
Then `NLAlib.newtonSchulzSign` with at least $N_0$ steps is within $\varepsilon$ of
$\operatorname{sign}\mathbf{A}$. Compared with
`NLAlib.FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le`
($640n^{3/2}(8 + \mu)(N_0 + 1)u \le (a/b)\varepsilon$), the step count and the dimension factor
of the stopping test leave the binding condition. [Shah2024, Theorem 2.6].
Proof: as SN4 (start error, stopping test, final $\|\mathbf{X} - \operatorname{sign}\mathbf{X}\|_2
\le \|\mathbf{I} - \mathbf{X}^2\|_2$ by `Matrix.IsHermitian.specNorm_sub_cfc_sign_le`),
except the propagation: with $a_k$ the least eigenvalue modulus of the $k$-th stored iterate and
$\delta = \nu u$ (SN3'), Weyl and NS13 give $a_{k+1} \ge \tfrac{11}{8}a_k - \delta \ge
1.325\,a_k$ while $a_k \le 1/2$, and $a_{k+1} \ge 1/2$ afterwards
(`NLAlib.abs_newtonSchulz_le_one`, NS9); each step changes the sign by at most
$2\delta/g(a_k)$ (`Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le` with
`Matrix.IsHermitian.cfc_sign_cfc_newtonSchulz`), so the total is at most
$\delta(5.93/a_0 + 2.91(N_0 + 1))$ with $a_0 \ge a/b - 2\sqrt n u$; the first condition bounds
the first term by $0.19\varepsilon$, the second the rest, and the stopping test leaves
$\tfrac23\varepsilon$ as in SN4. The second condition implies $640n(8 + \mu)u \le \varepsilon$
(since $\nu \ge 8 + \mu$), the hypothesis `hk` of SN4's private stopping-test lemmas, for every
$n$. L, about 250 lines (SN4's private lemmas reused). -/
theorem FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le_of_mul_le
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian) {a : ℝ} {b ε : F} (ha : 0 < a)
    (hspec : ∀ x ∈ spectrum ℝ (decodeMatrix dec A), a ≤ |x|)
    (hb : specNorm (decodeMatrix dec A) ≤ dec b) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1 / 2)
    (hu : 32 * (4 * μ n + 10 + 10 * √(n : ℝ)) * u ≤ a / dec b * dec ε)
    (hstop : 640 * (n + newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) + 1) *
      (4 * μ n + 10 + 10 * √(n : ℝ)) * u ≤ dec ε)
    {N : ℕ} (hN : newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) ≤ N) :
    specNorm (cfc Real.sign (decodeMatrix dec A) - decodeMatrix dec (newtonSchulzSign M ε b N A)) ≤
      dec ε := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim (_ - _) 0, specNorm_zero]
    exact hε.le
  set Ad := decodeMatrix dec A
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqn : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn₁
  -- the scale `b` is positive and at least `a`
  have hab : a ≤ dec b := by
    have hx := hA.eigenvalue_mem_spectrum (k := 0) (by simpa using hn)
    exact ((hspec _ hx).trans (hA.abs_le_specNorm_of_mem_spectrum hx)).trans hb
  have hb₀ : 0 < dec b := ha.trans_le hab
  set r := a / dec b with hr
  have hr₀ : 0 < r := div_pos ha hb₀
  have hr₁ : r ≤ 1 := (div_le_one hb₀).mpr hab
  have hs : a / (2 * dec b) = r / 2 := by rw [hr]; field_simp
  rw [hs] at hstop hN
  set N₀ := newtonSchulzSteps (r / 2) (dec ε / (16 * n))
  have hN₀ : 0 ≤ N₀ := newtonSchulzSteps_nonneg (by positivity) (by linarith) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  -- the size conditions in terms of the step error `δ` of SN3'
  set δ := (4 * μ n + 10 + 10 * √(n : ℝ)) * u with hδdef
  have hδ₀ : 0 ≤ δ := by positivity
  obtain ⟨hδr, hδN, hk, hδs, hδε, hδu⟩ :=
    stepError_bounds hn hμ hu₀ hr₀.le hε₁ hN₀ hδdef hu hstop
  -- the start `A₀ = fl(A / b)`
  have hA₀ : (decodeMatrix dec (M.hermScale A b)).IsHermitian :=
    hM.isHermitian_decodeMatrix_hermFrom _ _
  have hAs : ((dec b)⁻¹ • Ad).IsHermitian := hA.smul (IsSelfAdjoint.all _)
  have hAs₁ : specNorm ((dec b)⁻¹ • Ad) ≤ 1 :=
    hAs.specNorm_le_of_forall_mem_spectrum_abs_le zero_le_one fun y hy => by
      obtain ⟨x, hx, rfl⟩ := hA.exists_mem_spectrum_eq_mul _ hy
      rw [abs_mul, abs_of_pos (inv_pos.mpr hb₀), inv_mul_le_one₀ hb₀]
      exact (hA.abs_le_specNorm_of_mem_spectrum hx).trans hb
  have hrx : ∀ x ∈ spectrum ℝ Ad, r ≤ |(dec b)⁻¹ * x| := fun x hx => by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hb₀), hr, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hspec x hx) (inv_pos.mpr hb₀).le
  have he := hM.specNorm_sub_decodeMatrix_hermScale_le hu₀ hτ₀ hA hb₀.ne'
    (by rw [abs_of_pos hb₀, div_le_iff₀ hb₀]; nlinarith [specNorm_nonneg Ad])
  have he' : specNorm ((dec b)⁻¹ • Ad - decodeMatrix dec (M.hermScale A b)) ≤ δ / 10 := by
    refine he.trans ?_
    linarith [mul_le_mul_of_nonneg_left hAs₁ (by positivity : (0 : ℝ) ≤ u * √(n : ℝ)),
      mul_le_mul_of_nonneg_left hτ hu₀]
  set t₀ := min (r - δ / 10) (1 / 2)
  have ht₀ : 0 < t₀ := lt_min (by linarith) (by norm_num)
  have hδ₁ : δ ≤ 1 / 40 := by linarith
  have ht₀₁ : 12 * δ ≤ t₀ := le_min (by linarith) (by linarith)
  have hch₀ : ∀ y ∈ spectrum ℝ (decodeMatrix dec (M.hermScale A b)),
      IsNewtonSchulzChain (r / 2) δ y 0 ∧ t₀ ≤ |y| := by
    intro y hy
    obtain ⟨w, hw, hwy⟩ := hAs.exists_mem_spectrum_abs_sub_le hA₀ hy
    have hw₁ := (hAs.abs_le_specNorm_of_mem_spectrum hw).trans hAs₁
    obtain ⟨x, hx, rfl⟩ := hA.exists_mem_spectrum_eq_mul _ hw
    have hw₂ := hrx x hx
    have h₁ := abs_sub_abs_le_abs_sub ((dec b)⁻¹ * x) y
    have h₂ := abs_sub_abs_le_abs_sub y ((dec b)⁻¹ * x)
    rw [abs_sub_comm] at h₂
    exact ⟨isNewtonSchulzChain_zero hδ₀ (by linarith) (by linarith),
      (min_le_left _ _).trans (by linarith)⟩
  have hloop := specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzLoop_le_add hM hμ hu₀ hτ₀ hτ hΩ
    hn hε hε₁ hk (by positivity) (by linarith) hδs hδε N 0 _ hA₀ (fun y hy => (hch₀ y hy).1)
    ht₀ ht₀₁ (min_le_right _ _) (fun y hy => (hch₀ y hy).2) (by simpa using hN)
  rw [Nat.cast_zero, sub_zero, max_eq_right (by linarith)] at hloop
  -- the first rounding moves the sign by at most `2‖A/b − A₀‖₂ / (a/b)`
  have hsign := hAs.specNorm_cfc_sign_sub_cfc_sign_le hA₀ hr₀ fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hA.exists_mem_spectrum_eq_mul _ hy
    exact hrx x hx
  rw [cfc_sign_smul hA (inv_pos.mpr hb₀)] at hsign
  have htri := specNorm_add_le (cfc Real.sign Ad - cfc Real.sign
    (decodeMatrix dec (M.hermScale A b))) (cfc Real.sign (decodeMatrix dec (M.hermScale A b)) -
      decodeMatrix dec (newtonSchulzSign M ε b N A))
  rw [sub_add_sub_cancel, newtonSchulzSign] at htri
  have h₁ : 2 * specNorm ((dec b)⁻¹ • Ad - decodeMatrix dec (M.hermScale A b)) / r ≤
      dec ε / 160 := by
    rw [div_le_iff₀ hr₀]; linarith
  -- the potential at the start: `7δ/t₀ ≤ ε/4 + 14δ`
  have h₂ : 7 * δ / t₀ ≤ dec ε / 4 + 14 * δ :=
    seven_mul_div_min_le hδ₀ hε hε₁ hδr (by linarith)
  have h₃ := mul_nonneg hN₀ hδ₀
  exact htri.trans (by linarith [hsign.trans h₁])

end NLAlib
