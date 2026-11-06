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
  sorry

end NLAlib
