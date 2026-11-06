/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Matrix.Computation.Deflation
public import NLAlibScaffold.RandomMatrix.Gaussian.Complex

/-!
# Randomized deflation with a complex Gaussian test matrix (scaffold)

Statement for a new file `NLAlib/Eigensolvers/RandomizedDeflation.lean` (stage HDIAG, wave W3,
design note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.6; the folder
`NLAlib/Eigensolvers` is open question OQ1 of the note). With a standard complex Gaussian sample,
the deterministic bound of
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le`
holds with $m$ replaced by its high-probability bound ([Shah2024, Theorem 3.3]).

## Main results

* `NLAlib.FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- A square matrix whose action is bounded below by `x` is a unit with inverse of norm `≤ 1/x`. -/
private lemma isUnit_and_specNorm_inv_le_of_lower_bound {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ}
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

/-- A zero-dimensional spectral norm vanishes. -/
private lemma specNorm_eq_zero_of_eq_zero {r : ℕ} (hr : r = 0) (A : Matrix (Fin r) (Fin r) ℂ) :
    specNorm A = 0 := by
  subst hr
  exact le_antisymm ((specNorm_le_iff le_rfl).2 fun y => by simp [Subsingleton.elim y 0])
    (specNorm_nonneg _)

/-- The event that the last singular value of `Vᴴ G₁` is at most `x` has probability at most
`r² x²`. -/
private lemma measureReal_rank_deflate_le {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} {n r : ℕ} (hr : r ≤ n) {V : Matrix (Fin n) (Fin r) ℂ}
    (hV : HasOrthonormalCols V) {G : Ω' → Matrix (Fin n) (Fin n) ℂ}
    (hG : HasLaw G (complexGaussianMatrix (Fin n) (Fin n)) μ) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | r ≠ 0 ∧
      singularValues (Vᴴ * (G ω).submatrix id (Fin.castLE hr)) (r - 1) ≤ x} ≤
      (r : ℝ) ^ 2 * x ^ 2 := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  rcases eq_or_ne r 0 with h0 | h0
  · subst h0
    simp
  · have hL1 := hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix hG hV
    have hL2 := hasLaw_submatrix_of_hasLaw_complexGaussianMatrix hL1
      (f := id) Function.injective_id (e := Fin.castLE hr) (Fin.castLE_injective hr)
    have hfun : (fun ω => Vᴴ * (G ω).submatrix id (Fin.castLE hr)) =
        (fun ω => (Vᴴ * G ω).submatrix id (Fin.castLE hr)) := by
      funext ω
      ext i j
      simp [Matrix.mul_apply]
    rw [← hfun] at hL2
    have hL := measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix hL2
      (k := r - 1) (by rw [Fintype.card_fin]; omega) hx
    refine le_trans (measureReal_mono (fun ω hω => hω.2)) (le_trans hL ?_)
    simp

/-- **Randomized deflation** (Theorem 3.3): under the machine contract
`NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ with constants $\mu_{\mathrm{MM}}$,
$\mu_{\mathrm{QR}}$, $c_{\mathrm N}$, let $r \le n$, $\mathbf{U}, \mathbf{V} \in
\mathbb{C}^{n \times r}$ have orthonormal columns, $\mathbf{S}$ be invertible, $\mathbf{A} =
\mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$ and the stored $\widetilde{\mathbf{A}}$ decode
within $\beta \le 1$ of $\mathbf{A}$, and let $\mathbf{G}$ be a standard complex Gaussian $n \times
n$ matrix. For $t \ge 0$ and $x > 0$ put
$$\bar m = (\|\mathbf{S}\|_2 + 2)\|\mathbf{S}^{-1}\|_2\,\frac{\sqrt2\,(2\sqrt n + t)}{x} \,.$$
If $\bar m\beta \le 1/5$,
$(4\mu_{\mathrm{QR}}(n) + 4\sqrt n\,c_{\mathrm N} + 2\mu_{\mathrm{MM}}(n))u
\le \beta$, $\tau \le \|\mathbf{S}\|_2 x$, $\sqrt n\,\tau \le x$ and $2(\|\mathbf{S}\|_2 +
1)\sqrt2(2\sqrt n + t) \le \Omega$, then
$$\mathbb{P}\bigl[\text{no unitary } \mathbf{W} \text{ has }
\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le 6\bar m\beta\bigr]
\le 2e^{-t^2/2} + r^2x^2 \,,$$
$\mathsf{deflate}$ the algorithm `NLAlib.deflate` with sample $\mathbf{G}$. [Shah2024, Theorem 3.3],
there with $(2\sqrt2 + t)\sqrt n$, failure $2e^{-nt^2} + (r/2)x^2$ and the requirement on $\beta$
written out; the constants differ through Lemmas 3.1 and 3.2.
Proof: outside the events $\{\|\mathbf{G}\|_2 \ge \sqrt2(2\sqrt n + t)\}$
(`NLAlib.measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix`) and
$\{\sigma_{r-1}(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1) \le x\}$
(`NLAlib.hasLaw_submatrix_of_hasLaw_complexGaussianMatrix`,
`NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix`,
`NLAlib.measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix`), the matrix
$\mathbf{V}^{\mathsf{H}}\mathbf{G}_1$ is invertible with inverse of norm below $1/x$
(`NLAlib.singularValues_last_mul_norm_le`), $\|\mathbf{G}\|_2 \ge x$, so $m \le \bar m$,
$\|\mathbf{G}\|_2 < \sqrt2(2\sqrt n + t) \le \Omega$ (from `hΩ`), and
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le` applies;
union bound (`MeasureTheory.measureReal_union_le`, `MeasureTheory.measureReal_mono`). Case $r = 0$
trivial. M, about 60 lines. -/
theorem FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β t x : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β) (hβ₁ : β ≤ 1) (ht : 0 ≤ t) (hx : 0 < x)
    (hmβ : (specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) / x * β ≤ 1 / 5)
    (hu : (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β) (hτ : τ ≤ specNorm S * x)
    (hτN : τ * √(n : ℝ) ≤ x)
    (hΩ : 2 * (specNorm S + 1) * (√2 * (2 * √(n : ℝ) + t)) ≤ Ω)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {G : Ω' → Matrix (Fin n) (Fin n) ℂ}
    (hG : HasLaw G (complexGaussianMatrix (Fin n) (Fin n)) μ) :
    μ.real {ω | ¬ ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' (G ω))) ≤
        6 * ((specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) / x) * β} ≤
      2 * Real.exp (-t ^ 2 / 2) + r ^ 2 * x ^ 2 := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hβ0 : 0 ≤ β := (specNorm_nonneg _).trans hβ
  have hσ0 : 0 ≤ specNorm S := specNorm_nonneg S
  have hB0 : 0 ≤ √2 * (2 * √(n : ℝ) + t) := by positivity
  -- the deterministic bound on the good event
  have key : ∀ Gm : Matrix (Fin n) (Fin n) ℂ, specNorm Gm < √2 * (2 * √(n : ℝ) + t) →
      (r ≠ 0 → x < singularValues (Vᴴ * Gm.submatrix id (Fin.castLE hr)) (r - 1)) →
      ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
        specNorm (U * W - decodeMatrix dec (deflate M r A' Gm)) ≤
          6 * ((specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) / x) * β := by
    intro Gm hGB hσ
    have hlow : ∀ z : Fin r → ℂ, x * ‖WithLp.toLp 2 z‖ ≤
        ‖WithLp.toLp 2 ((Vᴴ * Gm.submatrix id (Fin.castLE hr)) *ᵥ z)‖ := by
      intro z
      rcases eq_or_ne r 0 with h0 | h0
      · have hz0 : ∀ v : Fin 0 → ℂ, ‖WithLp.toLp 2 v‖ = 0 := fun v => by
          rw [Subsingleton.elim v 0]
          simp
        subst h0
        simp [hz0]
      · have h1 := singularValues_last_mul_norm_le (Vᴴ * Gm.submatrix id (Fin.castLE hr))
          (k := r - 1) (by rw [Fintype.card_fin]; omega) z
        exact (mul_le_mul_of_nonneg_right (hσ h0).le (norm_nonneg _)).trans h1
    obtain ⟨hGu, hinv⟩ := isUnit_and_specNorm_inv_le_of_lower_bound hx hlow
    have h1 : specNorm Vᴴ ≤ 1 := by rw [specNorm_conjTranspose]; exact hV.specNorm_le_one
    have h2 : specNorm (Gm.submatrix id (Fin.castLE hr)) ≤ specNorm Gm :=
      specNorm_submatrix_le Gm Function.injective_id (Fin.castLE_injective hr)
    have hMG : specNorm (Vᴴ * Gm.submatrix id (Fin.castLE hr)) ≤ specNorm Gm :=
      (specNorm_mul_le _ _).trans ((mul_le_mul h1 h2 (specNorm_nonneg _) zero_le_one).trans
        (one_mul _).le)
    have hxG : r ≠ 0 → x ≤ specNorm Gm := fun h0 =>
      (hσ h0).le.trans ((singularValues_le_specNorm _ _).trans hMG)
    have hτ0 : r = 0 → τ ≤ 0 := fun h0 => by
      rw [specNorm_eq_zero_of_eq_zero h0 S, zero_mul] at hτ; exact hτ
    have hτ' : τ ≤ specNorm S * specNorm Gm := by
      rcases eq_or_ne r 0 with h0 | h0
      · rw [specNorm_eq_zero_of_eq_zero h0 S, zero_mul]
        exact hτ0 h0
      · exact hτ.trans (mul_le_mul_of_nonneg_left (hxG h0) hσ0)
    have hτN' : τ * √(n : ℝ) ≤ specNorm Gm := by
      rcases eq_or_ne r 0 with h0 | h0
      · nlinarith [Real.sqrt_nonneg (n : ℝ), specNorm_nonneg Gm, hτ0 h0]
      · exact hτN.trans (hxG h0)
    have hΩ' : 2 * (specNorm S + β) * specNorm Gm ≤ Ω := by
      have h1 : 2 * (specNorm S + β) ≤ 2 * (specNorm S + 1) := by linarith
      nlinarith [mul_le_mul h1 hGB.le (specNorm_nonneg _) (by positivity)]
    have hΩG : specNorm Gm ≤ Ω := by nlinarith [mul_nonneg hσ0 hB0, hGB.le]
    have hmval : (specNorm S + β + 1) * specNorm S⁻¹ * specNorm Gm *
        specNorm (Vᴴ * Gm.submatrix id (Fin.castLE hr))⁻¹ ≤
        (specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) / x := by
      have h1 : specNorm S + β + 1 ≤ specNorm S + 2 := by linarith
      calc (specNorm S + β + 1) * specNorm S⁻¹ * specNorm Gm *
            specNorm (Vᴴ * Gm.submatrix id (Fin.castLE hr))⁻¹
          ≤ (specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) * (1 / x) := by
            gcongr
        _ = _ := by ring
    obtain ⟨W, hW, hWb⟩ :=
      FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le
        hM hr hU hV hS hA hβ hGu rfl (mul_le_mul_of_nonneg_right hmval hβ0 |>.trans hmβ)
        hu hτ' hτN' hΩ' hΩG
    exact ⟨W, hW, hWb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmval (by norm_num)) hβ0)⟩
  -- the two bad events
  have hE1 : μ.real {ω | √2 * (2 * √(n : ℝ) + t) ≤ specNorm (G ω)} ≤ 2 * Real.exp (-t ^ 2 / 2) := by
    refine le_trans (measureReal_mono (fun ω hω => ?_))
      (measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix hG ht)
    simp only [Set.mem_setOf_eq, Fintype.card_fin] at hω ⊢
    linarith
  have hE2 := measureReal_rank_deflate_le hr hV hG hx.le
  have hsub : {ω | ¬ ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' (G ω))) ≤
        6 * ((specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) / x) * β} ⊆
      {ω | √2 * (2 * √(n : ℝ) + t) ≤ specNorm (G ω)} ∪
        {ω | r ≠ 0 ∧ singularValues (Vᴴ * (G ω).submatrix id (Fin.castLE hr)) (r - 1) ≤ x} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le, not_and] at hcon hω
    exact hω (key (G ω) hcon.1 hcon.2)
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  exact add_le_add hE1 hE2

end NLAlib
