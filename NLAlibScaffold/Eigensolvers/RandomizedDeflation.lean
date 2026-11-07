/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.RandomizedDeflation
public import NLAlibScaffold.Matrix.Computation.Deflation
public import NLAlibScaffold.RandomMatrix.Gaussian.Complex

/-!
# Randomized deflation with sharper Gaussian tails (scaffold, stage HDIAG-BOUNDS)

Statement for `NLAlib/Eigensolvers/RandomizedDeflation.lean` (design note
`docs/design/Eigensolvers-HermitianDiagonalization-Bounds.md`, items I5–I7): [Shah2024,
Theorem 3.3] with DF2', the norm tail CG4' and the smallest singular value tail
$\min(r^2, e r)x^2$ (CG6 and CG6').

## Main results

* [DP1'](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le_exp_neg_sq_add_of_hasLaw_complexGaussianMatrix).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- At $u = 0$ the machine contract holds with any matrix-multiplication constant. -/
private lemma isAccurate_of_u_eq_zero' {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec 0 τ Ω μM μQ cN)
    (μM' : ℕ → ℝ) : M.IsAccurate dec 0 τ Ω μM' μQ cN :=
  { hM with
    isMatMulErr :=
      { specNorm_mul_sub_le := fun A B h => by
          have := hM.isMatMulErr.specNorm_mul_sub_le A B h
          rw [mul_zero, zero_mul] at this ⊢
          exact this
        isHermitian_of_map_eq_conjTranspose :=
          hM.isMatMulErr.isHermitian_of_map_eq_conjTranspose } }

/-- With range $\Omega \ge 1$ the contract forces $u \ge 0$, and $\mu_{\mathrm{MM}}(n) \ge 0$ when
$u > 0$ and $n \ge 1$ (the stored identity times itself). -/
private lemma isAccurate_nonneg_of_one_le' {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    {n : ℕ} (hn : 0 < n) (hΩ : 1 ≤ Ω) : 0 ≤ u ∧ (0 < u → 0 ≤ μM n) := by
  have hmax : (0 : ℝ) < max 1 τ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hu : 0 ≤ u := by
    have h := hM.ofNat 1
    simp only [IsRoundingOf, Nat.cast_one, abs_one] at h
    have h0 := (abs_nonneg _).trans (h hΩ)
    by_contra hneg
    push Not at hneg
    linarith [mul_neg_of_neg_of_pos hneg hmax]
  refine ⟨hu, fun hpos => ?_⟩
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let I' : Matrix (Fin n) (Fin n) (F × F) :=
    Matrix.of fun i j => (if i = j then M.one else M.zero, M.zero)
  have hI : I'.map (decodeComplex dec) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [I', decodeComplex, hM.dec_one, hM.dec_zero]
      rfl
    · simp [I', decodeComplex, hM.dec_zero, hij, Matrix.one_apply_ne hij]
      rfl
  have h := hM.isMatMulErr.specNorm_mul_sub_le I' I' (by rw [hI, specNorm_one, mul_one]; exact hΩ)
  rw [hI, specNorm_one, mul_one, mul_one, max_self, max_self] at h
  by_contra hneg
  push Not at hneg
  linarith [specNorm_nonneg (1 - (M.mm I' I').map (decodeComplex dec)),
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hpos) hmax]

/-- A square matrix whose action is bounded below by `x` is a unit with inverse of norm `≤ 1/x`. -/
private lemma isUnit_and_specNorm_inv_le_of_lower_bound' {r : ℕ}
    {M : Matrix (Fin r) (Fin r) ℂ}
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

/-- The event that the last singular value of `Vᴴ G₁` is at most `x` has probability at most
`min(r², e r) x²`. -/
private lemma measureReal_rank_deflate_le_min {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} {n r : ℕ} (hr : r ≤ n) {V : Matrix (Fin n) (Fin r) ℂ}
    (hV : HasOrthonormalCols V) {G : Ω' → Matrix (Fin n) (Fin n) ℂ}
    (hG : HasLaw G (complexGaussianMatrix (Fin n) (Fin n)) μ) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | r ≠ 0 ∧
      singularValues (Vᴴ * (G ω).submatrix id (Fin.castLE hr)) (r - 1) ≤ x} ≤
      min ((r : ℝ) ^ 2) (Real.exp 1 * r) * x ^ 2 := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  rcases eq_or_ne r 0 with h0 | h0
  · subst h0
    simp
  have hL1 := hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix hG hV
  have hL2 := hasLaw_submatrix_of_hasLaw_complexGaussianMatrix hL1
    (f := id) Function.injective_id (e := Fin.castLE hr) (Fin.castLE_injective hr)
  have hfun : (fun ω => Vᴴ * (G ω).submatrix id (Fin.castLE hr)) =
      (fun ω => (Vᴴ * G ω).submatrix id (Fin.castLE hr)) := by
    funext ω
    ext i j
    simp [Matrix.mul_apply]
  rw [← hfun] at hL2
  have hk : r - 1 + 1 = Fintype.card (Fin r) := by rw [Fintype.card_fin]; omega
  have h1 := measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix hL2 hk hx
  have h2 := measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix hL2 hk hx
  rw [Fintype.card_fin] at h1 h2
  rw [min_mul_of_nonneg _ _ (by positivity)]
  exact (measureReal_mono fun ω hω => hω.2).trans (le_min h1 h2)

/-- The deterministic step of DP1': on the event
$\|\mathbf{G}\|_2 < 2\sqrt2\sqrt n + t$, $\sigma_{r-1}(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1) > x$,
DF2' applies with $m \le \bar m$. -/
private lemma exists_specNorm_mul_sub_deflate_le_of_good'
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β t x : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β) (hβ₁ : β ≤ 1) (ht : 0 ≤ t) (hx : 0 < x)
    (hmβ : (1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x * β ≤
      1 / 64)
    (hu : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β) (hτ : τ ≤ specNorm S * x)
    (hτN : τ * √(n : ℝ) ≤ x)
    (hΩ : 2 * (specNorm S + 1) * (2 * √2 * √(n : ℝ) + t) ≤ Ω)
    {Gm : Matrix (Fin n) (Fin n) ℂ} (hGB : specNorm Gm < 2 * √2 * √(n : ℝ) + t)
    (hσ : r ≠ 0 → x < singularValues (Vᴴ * Gm.submatrix id (Fin.castLE hr)) (r - 1)) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' Gm)) ≤
        3 / 2 * ((1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x) *
          β := by
  have hβ0 : 0 ≤ β := (specNorm_nonneg _).trans hβ
  have hσ0 : 0 ≤ specNorm S := specNorm_nonneg S
  have hB0 : 0 ≤ 2 * √2 * √(n : ℝ) + t := by positivity
  rcases eq_or_ne r 0 with h0 | h0
  · subst h0
    refine ⟨1, hasOrthonormalCols_one, ?_⟩
    rw [Subsingleton.elim (U * 1 - _) 0, specNorm_zero]
    have := specNorm_nonneg S⁻¹
    positivity
  have hn : 0 < n := by omega
  have hΩ1 : 1 ≤ Ω := by
    have hn1 : (1 : ℝ) ≤ √(n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
    have hs2 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
    nlinarith [mul_le_mul hs2 hn1 zero_le_one (by positivity)]
  obtain ⟨hu0, hμpos⟩ := isAccurate_nonneg_of_one_le' hM hn hΩ1
  obtain ⟨μ', hM', hμ', hu''⟩ : ∃ μ' : ℕ → ℝ, M.IsAccurate dec u τ Ω μ' μQ cN ∧ 0 ≤ μ' n ∧
      16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μ' n) * u ≤ β := by
    rcases hu0.eq_or_lt with h | h
    · subst h
      exact ⟨fun _ => 0, isAccurate_of_u_eq_zero' hM _, le_rfl, by rw [mul_zero]; exact hβ0⟩
    · exact ⟨μM, hM, hμpos h, hu⟩
  have hlow : ∀ z : Fin r → ℂ, x * ‖WithLp.toLp 2 z‖ ≤
      ‖WithLp.toLp 2 ((Vᴴ * Gm.submatrix id (Fin.castLE hr)) *ᵥ z)‖ := fun z =>
    (mul_le_mul_of_nonneg_right (hσ h0).le (norm_nonneg _)).trans
      (singularValues_last_mul_norm_le _ (k := r - 1) (by rw [Fintype.card_fin]; omega) z)
  obtain ⟨hGu, hinv⟩ := isUnit_and_specNorm_inv_le_of_lower_bound' hx hlow
  have hMG : specNorm (Vᴴ * Gm.submatrix id (Fin.castLE hr)) ≤ specNorm Gm := by
    have h1 : specNorm Vᴴ ≤ 1 := by rw [specNorm_conjTranspose]; exact hV.specNorm_le_one
    have h2 := specNorm_submatrix_le Gm Function.injective_id (Fin.castLE_injective hr)
    calc _ ≤ specNorm Vᴴ * specNorm (Gm.submatrix id (Fin.castLE hr)) := specNorm_mul_le _ _
      _ ≤ 1 * specNorm Gm := by gcongr
      _ = specNorm Gm := one_mul _
  have hxG : x ≤ specNorm Gm := (hσ h0).le.trans ((singularValues_le_specNorm _ _).trans hMG)
  have hΩ' : 2 * (specNorm S + β) * specNorm Gm ≤ Ω := by
    have h1 : 2 * (specNorm S + β) ≤ 2 * (specNorm S + 1) := by linarith
    nlinarith [mul_le_mul h1 hGB.le (specNorm_nonneg _) (by positivity)]
  have hΩG : specNorm Gm ≤ Ω := by nlinarith [mul_nonneg hσ0 hB0, hGB.le]
  have hmval : (1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * specNorm Gm *
      specNorm (Vᴴ * Gm.submatrix id (Fin.castLE hr))⁻¹ ≤
      (1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x := by
    rw [mul_assoc _ (specNorm Gm), mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by linarith) (specNorm_nonneg _))
    rw [div_eq_mul_one_div]
    gcongr
  obtain ⟨W, hW, hWb⟩ :=
    FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le
      hM' hμ' hu0 hr hU hV hS hA hβ hGu rfl (mul_le_mul_of_nonneg_right hmval hβ0 |>.trans hmβ)
      hu'' (hτ.trans (mul_le_mul_of_nonneg_left hxG hσ0)) (hτN.trans hxG) hΩ' hΩG
  exact ⟨W, hW, hWb.trans (by gcongr)⟩

-- The declaration name and a docstring line exceed 100 characters.
set_option linter.style.longLine false in
/-- **Accuracy of randomized deflation with probability, sharp tails** (DP1'): under the
hypotheses of DF2' for a standard complex Gaussian $\mathbf{G}$, with $t \ge 0$, $x > 0$,
$\bar m = (1 + 2\beta + \|\mathbf{S}\|_2/8)\|\mathbf{S}^{-1}\|_2(2\sqrt2\sqrt n + t)/x$ and
$\bar m\beta \le 1/64$, the probability that no unitary $\mathbf{W}$ has
$\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le \tfrac32\bar m\beta$
is at most $e^{-t^2} + \min(r^2, e\,r)\,x^2$. [Shah2024, Theorem 3.3].
Proof: as DP1: on $\{\|\mathbf{G}\|_2 < 2\sqrt2\sqrt n + t\} \cap
\{\sigma_{\min}(\mathbf{V}^{\mathsf H}\mathbf{G}_1) > x\}$ apply DF2' (its $m$ is at most $\bar m$);
the first event fails with probability at most $e^{-t^2}$
(`NLAlib.measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix`), the second, through
`NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix` and
`NLAlib.hasLaw_submatrix_of_hasLaw_complexGaussianMatrix`, with probability at most $r^2x^2$
(`NLAlib.measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix`) and at most
$e\,r x^2$ (`NLAlib.measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix`);
$u \ge 0$ and $\mu_{\mathrm{MM}}(n) \ge 0$ are derived as in DP1. M, about 100 lines (DP1's
proof with the two tails swapped). -/
theorem
    FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le_exp_neg_sq_add_of_hasLaw_complexGaussianMatrix
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β t x : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β) (hβ₁ : β ≤ 1) (ht : 0 ≤ t) (hx : 0 < x)
    (hmβ : (1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x * β ≤
      1 / 64)
    (hu : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β) (hτ : τ ≤ specNorm S * x)
    (hτN : τ * √(n : ℝ) ≤ x)
    (hΩ : 2 * (specNorm S + 1) * (2 * √2 * √(n : ℝ) + t) ≤ Ω)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {G : Ω' → Matrix (Fin n) (Fin n) ℂ}
    (hG : HasLaw G (complexGaussianMatrix (Fin n) (Fin n)) μ) :
    μ.real {ω | ¬ ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' (G ω))) ≤
        3 / 2 * ((1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x) *
          β} ≤
      Real.exp (-t ^ 2) + min ((r : ℝ) ^ 2) (Real.exp 1 * r) * x ^ 2 := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hE1 : μ.real {ω | 2 * √2 * √(n : ℝ) + t ≤ specNorm (G ω)} ≤ Real.exp (-t ^ 2) := by
    refine le_trans (measureReal_mono fun ω hω => ?_)
      (measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix hG ht)
    simp only [Set.mem_ofPred_eq, Fintype.card_fin] at hω ⊢
    linarith
  have hsub : {ω | ¬ ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' (G ω))) ≤
        3 / 2 * ((1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x) *
          β} ⊆
      {ω | 2 * √2 * √(n : ℝ) + t ≤ specNorm (G ω)} ∪
        {ω | r ≠ 0 ∧ singularValues (Vᴴ * (G ω).submatrix id (Fin.castLE hr)) (r - 1) ≤ x} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_and] at hcon hω
    exact hω (exists_specNorm_mul_sub_deflate_le_of_good' hM hr hU hV hS hA hβ hβ₁ ht hx hmβ hu
      hτ hτN hΩ hcon.1 hcon.2)
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add hE1 (measureReal_rank_deflate_le_min hr hV hG hx.le)))

end NLAlib
