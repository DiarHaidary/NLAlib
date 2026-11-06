/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.Deflation
public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Norms.Compare
public import NLAlib.Matrix.Spectral.LeastSingularValue

/-!
# Deterministic accuracy of randomized deflation (scaffold)

Statements for `NLAlib/Matrix/Computation/Deflation.lean` (stage HDIAG, wave W3, design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` §3.6): the deterministic half of
[Shah2024, Theorem 3.3]. If $\widetilde{\mathbf{A}}$ is within $\beta$ of
$\mathbf{A} = \mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$ of rank $r$ and the sample
$\mathbf{G}$ has $\mathbf{V}^{\mathsf{H}}\mathbf{G}_1$ invertible ($\mathbf{G}_1$ its first $r$
columns), the computed basis is within $6m\beta$ of $\mathbf{U}\mathbf{W}$ for a unitary
$\mathbf{W}$, where $m = (\|\mathbf{S}\|_2 + \beta + 1)\|\mathbf{S}^{-1}\|_2\|\mathbf{G}\|_2
\|(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)^{-1}\|_2$. The probabilistic half is in
`NLAlibScaffold/Eigensolvers/RandomizedDeflation.lean`.

## Main results

* `NLAlib.HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le`: a basis that spans
  nearly the range of a frame is near a rotation of the frame.
* `NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le`: the
  deterministic bound.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m r : Type*} [Fintype m] [Fintype r] [DecidableEq r]

/-- The reverse triangle inequality for two matrices at one vector. -/
private theorem abs_norm_mulVec_sub_norm_mulVec_le {p q : Type*} [Fintype p] [Fintype q]
    (X Y : Matrix p q 𝕜) (x : q → 𝕜) :
    |‖WithLp.toLp 2 (X *ᵥ x)‖ - ‖WithLp.toLp 2 (Y *ᵥ x)‖| ≤
      specNorm (X - Y) * ‖WithLp.toLp 2 x‖ :=
  (abs_norm_sub_norm_le _ _).trans <| by
    rw [← WithLp.toLp_sub, ← Matrix.sub_mulVec]; exact norm_toLp_mulVec_le _ _

open scoped MatrixOrder in
/-- A square matrix that is an $a$-near isometry, $a < 1$, is within $a$ of its polar factor. -/
private theorem exists_hasOrthonormalCols_specNorm_sub_le_of_abs_norm_mulVec_sub_le
    {B : Matrix r r 𝕜} {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1)
    (hB : ∀ x, |‖WithLp.toLp 2 (B *ᵥ x)‖ - ‖WithLp.toLp 2 x‖| ≤ a * ‖WithLp.toLp 2 x‖) :
    ∃ W : Matrix r r 𝕜, HasOrthonormalCols W ∧ specNorm (W - B) ≤ a := by
  have hlo : ∀ x, (1 - a) * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (B *ᵥ x)‖ := fun x => by
    have := (abs_le.mp (hB x)).1; linarith
  have hinj : Function.Injective B.mulVec := by
    intro x y hxy
    have h := hlo (x - y)
    rw [Matrix.mulVec_sub, hxy, sub_self, WithLp.toLp_zero, norm_zero] at h
    have h0 : ‖WithLp.toLp 2 (x - y)‖ = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right h (by linarith)) (norm_nonneg _)
    rw [norm_eq_zero, WithLp.toLp_eq_zero] at h0
    exact sub_eq_zero.mp h0
  have hB1 : specNorm B ≤ 1 + a := by
    rw [specNorm_le_iff (by linarith)]
    intro x; have := (abs_le.mp (hB x)).2; linarith
  set H := CFC.sqrt (Bᴴ * B)
  have hS : H.IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hW := hasOrthonormalCols_polarFactor_iff.mpr hinj
  refine ⟨polarFactor B, hW, ?_⟩
  have heq : polarFactor B - B = polarFactor B * -(H - 1) := by
    rw [neg_sub, Matrix.mul_sub, Matrix.mul_one,
      show polarFactor B * H = B from polarFactor_mul_sqrt B]
  have hH : specNorm (H - 1) ≤ a := by
    rcases isEmpty_or_nonempty r with hr | hr
    · rw [Subsingleton.elim (H - 1) 0, specNorm_zero]
      exact ha0
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := r))
    have hsub : H - 1 = H + (-1 : ℝ) • (1 : Matrix r r 𝕜) := by
      rw [neg_one_smul, sub_eq_add_neg]
    have hσ : ∀ i ≤ k, |eigenvalue (H - 1) i| ≤ a := fun i hi => by
      rw [hsub, hS.eigenvalue_add_smul_one (-1) (by omega),
        eigenvalue_sqrt_conjTranspose_mul_self B (by omega)]
      have h1 := (singularValues_le_specNorm B i).trans hB1
      have h2 := (le_singularValues_last B hk.symm hlo).trans (singularValues_antitone B hi)
      rw [abs_le]; constructor <;> linarith
    rw [(hS.sub Matrix.isHermitian_one).specNorm_eq_max hk.symm]
    exact max_le (hσ 0 (Nat.zero_le _)) (hσ k le_rfl)
  rw [heq]
  calc _ ≤ specNorm (polarFactor B) * specNorm (-(H - 1)) := specNorm_mul_le _ _
    _ ≤ 1 * a := by
      rw [specNorm_neg]
      exact mul_le_mul hW.specNorm_le_one hH (specNorm_nonneg _) zero_le_one
    _ = a := one_mul a

/-- **A near-basis close to a frame up to a change of basis is close to a rotation of it**: let
$\mathbf{U}, \mathbf{Q}' \in \Bbbk^{m \times r}$ have orthonormal columns, and
$\mathbf{Q}_1 \in \Bbbk^{m \times r}$, $\mathbf{C} \in \Bbbk^{r \times r}$ satisfy
$\|\mathbf{Q}_1 - \mathbf{Q}'\|_2 \le \nu$ and $\|\mathbf{U} - \mathbf{Q}_1\mathbf{C}\|_2 \le
\delta$ with $\nu \le \delta \le 1/5$. Then there is a unitary $\mathbf{W}$ with
$$\|\mathbf{U}\mathbf{W} - \mathbf{Q}_1\|_2 \le 6\delta \,.$$
[Shah2024, proof of Theorem 3.3]: the three inequalities there, which avoid the square-root loss
of [BanksGarzaVargasKulkarniSrivastava2020].
Proof: from $\|\mathbf{U} - \mathbf{Q}_1\mathbf{C}\|_2 \le \delta$, the singular values of
$\mathbf{C}$ lie in $[(1 - \delta)/(1 + \nu), (1 + \delta)/(1 - \nu)]$, those of
$\mathbf{U}^{\mathsf{H}}\mathbf{Q}_1$ in $[(1 - \delta)(1 - \nu)/(1 + \delta),
(1 + \delta)(1 + \nu)/(1 - \delta)]$, and $\|(\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf{H}})
\mathbf{Q}_1\|_2 \le \delta(1 + \nu)/(1 - \delta)$ (`NLAlib.singularValues_last_mul_norm_le`,
`NLAlib.exists_norm_eq_one_and_norm_mulVec_eq_singularValues`). Take $\mathbf{W}$ the polar factor
of $\mathbf{U}^{\mathsf{H}}\mathbf{Q}_1$ (`NLAlib.polarFactor`); then $\|\mathbf{W} -
\mathbf{U}^{\mathsf{H}}\mathbf{Q}_1\|_2 = \max_i \lvert \sigma_i - 1 \rvert \le 4\delta$, and
$\mathbf{U}\mathbf{W} - \mathbf{Q}_1 = \mathbf{U}(\mathbf{W} - \mathbf{U}^{\mathsf{H}}\mathbf{Q}_1)
- (\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf{H}})\mathbf{Q}_1$ gives $4\delta + 1.5\delta$.
M, about 70 lines. -/
theorem HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le {U Q' Q₁ : Matrix m r 𝕜}
    (hU : HasOrthonormalCols U) (hQ' : HasOrthonormalCols Q') {C : Matrix r r 𝕜} {ν δ : ℝ}
    (hν : specNorm (Q₁ - Q') ≤ ν) (hδ : specNorm (U - Q₁ * C) ≤ δ) (hνδ : ν ≤ δ)
    (hδ₅ : δ ≤ 1 / 5) :
    ∃ W : Matrix r r 𝕜, HasOrthonormalCols W ∧ specNorm (U * W - Q₁) ≤ 6 * δ := by
  classical
  have hδ0 : 0 ≤ δ := (specNorm_nonneg _).trans hδ
  have hQ₁ : ∀ x, |‖WithLp.toLp 2 (Q₁ *ᵥ x)‖ - ‖WithLp.toLp 2 x‖| ≤
      ν * ‖WithLp.toLp 2 x‖ := fun x => by
    have h := abs_norm_mulVec_sub_norm_mulVec_le Q₁ Q' x
    rw [hQ'.norm_toLp_mulVec] at h
    exact h.trans (by gcongr)
  have hC : ∀ x, ‖WithLp.toLp 2 x‖ ≤ 3 / 2 * ‖WithLp.toLp 2 (C *ᵥ x)‖ := fun x => by
    have h := abs_norm_mulVec_sub_norm_mulVec_le U (Q₁ * C) x
    rw [hU.norm_toLp_mulVec, ← Matrix.mulVec_mulVec] at h
    have h1 := (abs_le.mp h).2
    have h2 := (abs_le.mp (hQ₁ (C *ᵥ x))).2
    have hx := norm_nonneg (WithLp.toLp 2 x)
    have hCx := norm_nonneg (WithLp.toLp 2 (C *ᵥ x))
    nlinarith [mul_le_mul_of_nonneg_right hδ hx, mul_le_mul_of_nonneg_right hνδ hCx,
      mul_nonneg (sub_nonneg.mpr hδ₅) hx, mul_nonneg (sub_nonneg.mpr hδ₅) hCx]
  have hCsurj : Function.Surjective C.mulVec := by
    refine Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp ?_)
    intro x y hxy
    have h := hC (x - y)
    rw [Matrix.mulVec_sub, hxy, sub_self] at h
    simp only [Matrix.mulVec_zero, WithLp.toLp_zero, norm_zero, mul_zero] at h
    have h0 : ‖WithLp.toLp 2 (x - y)‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [norm_eq_zero, WithLp.toLp_eq_zero] at h0
    exact sub_eq_zero.mp h0
  set D := Q₁ - U * (Uᴴ * Q₁)
  have hDC : D * C = (1 - U * Uᴴ) * (Q₁ * C - U) := by
    simp only [D, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc,
      hU.conjTranspose_mul_self, Matrix.mul_one]
    abel
  have hD : specNorm D ≤ 3 / 2 * δ := by
    rw [specNorm_le_iff (by positivity)]
    intro y
    obtain ⟨x, rfl⟩ := hCsurj y
    rw [Matrix.mulVec_mulVec, hDC, ← Matrix.mulVec_mulVec]
    refine (hU.isStarProjection_mul_conjTranspose.one_sub.norm_toLp_mulVec_le _).trans ?_
    refine (norm_toLp_mulVec_le _ _).trans ?_
    rw [specNorm_sub_comm]
    have := hC x
    calc _ ≤ δ * ‖WithLp.toLp 2 x‖ := by gcongr
      _ ≤ _ := by nlinarith
  obtain ⟨W, hW, hWB⟩ := exists_hasOrthonormalCols_specNorm_sub_le_of_abs_norm_mulVec_sub_le
    (B := Uᴴ * Q₁) (a := 5 / 2 * δ) (by positivity) (by linarith) fun x => by
      have h := abs_norm_mulVec_sub_norm_mulVec_le Q₁ (U * (Uᴴ * Q₁)) x
      rw [← Matrix.mulVec_mulVec, hU.norm_toLp_mulVec] at h
      have h1 := h.trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
      have h2 := hQ₁ x
      have hx := norm_nonneg (WithLp.toLp 2 x)
      rw [abs_le] at h1 h2 ⊢
      constructor <;> nlinarith
  refine ⟨W, hW, ?_⟩
  have heq : U * W - Q₁ = U * (W - Uᴴ * Q₁) - D := by
    simp only [D, Matrix.mul_sub]; abel
  rw [heq]
  calc _ ≤ specNorm (U * (W - Uᴴ * Q₁)) + specNorm D := specNorm_sub_le _ _
    _ ≤ 5 / 2 * δ + 3 / 2 * δ := by rw [hU.specNorm_mul_left]; exact add_le_add hWB hD
    _ ≤ 6 * δ := by linarith

/-- Selecting columns of a matrix with orthonormal columns keeps orthonormal columns. -/
private theorem HasOrthonormalCols.submatrix_castLE_aux {m : Type*} [Fintype m] {n r : ℕ}
    (hr : r ≤ n) {Q : Matrix m (Fin n) ℂ} (hQ : HasOrthonormalCols Q) :
    HasOrthonormalCols (Q.submatrix id (Fin.castLE hr)) := by
  rw [hasOrthonormalCols_iff]
  ext i j
  have h := congrFun (congrFun hQ.conjTranspose_mul_self (Fin.castLE hr i)) (Fin.castLE hr j)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h ⊢
  simpa [(Fin.castLE_injective hr).eq_iff] using h

/-- The first $r$ columns of $\mathbf{Q}\mathbf{R}$, $\mathbf{R}$ upper trapezoidal, are
$\mathbf{Q}_1\mathbf{R}_{11}$. -/
private theorem submatrix_mul_castLE_of_isUpperTrapezoidal_aux {n r : ℕ} (hr : r ≤ n)
    (Q R : Matrix (Fin n) (Fin n) ℂ) (hR : IsUpperTrapezoidal R) :
    (Q * R).submatrix id (Fin.castLE hr) =
      Q.submatrix id (Fin.castLE hr) * R.submatrix (Fin.castLE hr) (Fin.castLE hr) := by
  ext i j
  simp only [Matrix.submatrix_apply, id, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _ ?_ fun _ => rfl
  intro k hk
  have hkr : r ≤ (k : ℕ) := by
    by_contra h
    exact hk ⟨⟨k, by omega⟩, rfl⟩
  rw [hR k (Fin.castLE hr j) (by simp; omega), mul_zero]

/-- The decoded output of `NLAlib.deflate` is the first $r$ columns of the decoded $\mathbf{Q}$. -/
private theorem decodeMatrix_deflate_aux {F : Type*} (M : FloatMachine F ℝ ℂ) (dec : F → ℝ)
    {n r : ℕ} (hr : r ≤ n) (A' : Matrix (Fin n) (Fin n) (F × F))
    (G : Matrix (Fin n) (Fin n) ℂ) :
    decodeMatrix dec (deflate M r A' G) =
      ((M.qr (M.mm A' (G.map M.normal))).1.map (decodeComplex dec)).submatrix id
        (Fin.castLE hr) := by
  ext i j
  simp [decodeMatrix, deflate, lt_of_lt_of_le j.2 hr, Fin.castLE]

/-- The error of the stored sample: $\|\mathbf{G} - \widetilde{\mathbf{G}}\|_2 \le
2\sqrt n\,c_{\mathrm N}u\|\mathbf{G}\|_2$. -/
private theorem specNorm_sub_map_normal_le_aux {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (hcu : 0 ≤ cN * u) (hτN : τ * √(n : ℝ) ≤ specNorm G)
    (hΩG : specNorm G ≤ Ω) :
    specNorm (G - (G.map M.normal).map (decodeComplex dec)) ≤
      2 * (√(n : ℝ) * cN * u) * specNorm G := by
  set g := specNorm G
  set E := G - (G.map M.normal).map (decodeComplex dec)
  have hent : ∀ i j, ‖E i j‖ ^ 2 ≤ (cN * u) ^ 2 * (‖G i j‖ ^ 2 + max τ 0 ^ 2) := by
    intro i j
    have h := hM.isNormalSampler (G i j) ((norm_apply_le_specNorm G i j).trans hΩG)
    have hmx : max ‖G i j‖ τ ^ 2 ≤ ‖G i j‖ ^ 2 + max τ 0 ^ 2 := by
      rcases le_total ‖G i j‖ τ with h1 | h1
      · rw [max_eq_right h1, max_eq_left ((norm_nonneg _).trans h1)]
        nlinarith [sq_nonneg ‖G i j‖]
      · rw [max_eq_left h1]; nlinarith [sq_nonneg (max τ 0)]
    have hE : E i j = G i j - decodeComplex dec (M.normal (G i j)) := rfl
    rw [hE]
    calc ‖_‖ ^ 2 ≤ (cN * u * max ‖G i j‖ τ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = (cN * u) ^ 2 * max ‖G i j‖ τ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmx (sq_nonneg _)
  have hτ' : max τ 0 ^ 2 * n ≤ g ^ 2 := by
    have h1 : max τ 0 * √(n : ℝ) ≤ g := by
      rw [max_mul_of_nonneg _ _ (Real.sqrt_nonneg _), zero_mul]
      exact max_le hτN (specNorm_nonneg _)
    have h2 := pow_le_pow_left₀ (mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)) h1 2
    rwa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at h2
  have hfG := frobNorm_sq_le_card_mul_specNorm_sq G
  rw [Fintype.card_fin] at hfG
  have hfE : frobNorm E ^ 2 ≤ (cN * u) ^ 2 * (2 * n * g ^ 2) := by
    rw [frobNorm_sq_eq_sum]
    calc ∑ i, ∑ j, ‖E i j‖ ^ 2
        ≤ ∑ i, ∑ j, (cN * u) ^ 2 * (‖G i j‖ ^ 2 + max τ 0 ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j
      _ = (cN * u) ^ 2 * (frobNorm G ^ 2 + n * n * max τ 0 ^ 2) := by
          rw [frobNorm_sq_eq_sum]
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
  refine (specNorm_le_frobNorm E).trans ((sq_le_sq₀ (frobNorm_nonneg _) ?_).1 ?_)
  · have := specNorm_nonneg G
    have := Real.sqrt_nonneg (n : ℝ)
    have : 0 ≤ √(n : ℝ) * cN * u := by rw [mul_assoc]; positivity
    positivity
  · have hsq : (2 * (√(n : ℝ) * cN * u) * g) ^ 2 = 4 * n * (cN * u) ^ 2 * g ^ 2 := by
      rw [show 2 * (√(n : ℝ) * cN * u) * g = 2 * √(n : ℝ) * (cN * u) * g by ring, mul_pow,
        mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    rw [hsq]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (cN * u)) (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
      (sq_nonneg g)]

/-- The arithmetic of the bound on $\mathbf{Z}$. -/
private theorem z_bound_arith_aux {s β g c a q : ℝ} (hs : 0 ≤ s) (hβ0 : 0 ≤ β) (hg : 0 ≤ g)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hq : 0 ≤ q) (hbud : 4 * q + 4 * c + 2 * a ≤ β)
    (hβ5 : β ≤ 1 / 5) :
    β * g + (s + β) * (2 * c * g) + a * ((s + β) * ((1 + 2 * c) * g)) +
        q * ((1 + a) * ((s + β) * ((1 + 2 * c) * g))) ≤
      g * (β + 3 / 5 * (s + β) * β) := by
  have hbr : 2 * c + a * (1 + 2 * c) + q * ((1 + a) * (1 + 2 * c)) ≤ 3 / 5 * β := by
    have hc' : c ≤ 1 / 20 := by linarith
    have ha' : a ≤ 1 / 10 := by linarith
    nlinarith [mul_nonneg ha hc, mul_nonneg hq hc, mul_nonneg hq ha,
      mul_nonneg (mul_nonneg hq ha) hc]
  have hsg : 0 ≤ (s + β) * g := mul_nonneg (by linarith) hg
  nlinarith [mul_le_mul_of_nonneg_left hbr hsg]

/-- The arithmetic giving $m \ge 1$ and $\beta \le 1/5$. -/
private theorem one_le_and_le_fifth_arith_aux {s β g si kk mval : ℝ} (hs : 0 ≤ s) (hβ0 : 0 ≤ β)
    (hg : 0 ≤ g) (hsi : 0 ≤ si) (hkk : 0 ≤ kk) (hssi : 1 ≤ s * si) (hgk : 1 ≤ g * kk)
    (hmv : mval = (s + β + 1) * (g * kk * si)) (hmβ : mval * β ≤ 1 / 5) :
    1 ≤ s * (g * kk * si) ∧ β ≤ 1 / 5 := by
  have hX : 1 ≤ s * (g * kk * si) := by
    have h := mul_le_mul hssi hgk zero_le_one (mul_nonneg hs hsi)
    nlinarith
  have hX0 : 0 ≤ g * kk * si := mul_nonneg (mul_nonneg hg hkk) hsi
  have hm1 : 1 ≤ mval := by
    rw [hmv]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ β + 1) hX0]
  exact ⟨hX, by nlinarith⟩

/-- The arithmetic of the range conditions. -/
private theorem range_arith_aux {s β g c a : ℝ} (hs : 0 ≤ s) (hβ0 : 0 ≤ β) (hg : 0 ≤ g)
    (hc : 0 ≤ c) (hc5 : c ≤ 1 / 20) (ha5 : a ≤ 1 / 10) :
    (1 + a) * ((s + β) * ((1 + 2 * c) * g)) ≤ 2 * (s + β) * g := by
  have h1 : (1 + a) * (1 + 2 * c) ≤ 2 := by nlinarith
  have h2 : 0 ≤ (s + β) * g := mul_nonneg (by linarith) hg
  nlinarith [mul_le_mul_of_nonneg_left h1 h2]

/-- The arithmetic of the final bound: $\delta = m\beta - q/6$ dominates the bound on
$\|\mathbf{Z}\mathbf{K}^{-1}\mathbf{S}^{-1}\|_2$. -/
private theorem delta_arith_aux {s β g si kk q : ℝ} (hβ0 : 0 ≤ β) (hg : 0 ≤ g)
    (hsi : 0 ≤ si) (hkk : 0 ≤ kk) (hX : 1 ≤ s * (g * kk * si)) (hq4 : q ≤ β / 4) :
    g * (β + 3 / 5 * (s + β) * β) * kk * si ≤ (s + β + 1) * (g * kk * si) * β - q / 6 := by
  have hX0 : 0 ≤ g * kk * si := mul_nonneg (mul_nonneg hg hkk) hsi
  have hXβ : β ≤ (s + β) * (g * kk * si) * β := by nlinarith [mul_nonneg hβ0 hX0]
  nlinarith

/-- Corrected DF2: the deterministic bound, with `0 ≤ μM n` and `0 ≤ u` added. -/
private theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_aux
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β mval : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hμM : 0 ≤ μM n) (hu₀ : 0 ≤ u) (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A G : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β)
    (hG : IsUnit (Vᴴ * G.submatrix id (Fin.castLE hr)))
    (hm : mval = (specNorm S + β + 1) * specNorm S⁻¹ * specNorm G *
      specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹)
    (hmβ : mval * β ≤ 1 / 5) (hu : (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β)
    (hτ : τ ≤ specNorm S * specNorm G) (hτN : τ * √(n : ℝ) ≤ specNorm G)
    (hΩ : 2 * (specNorm S + β) * specNorm G ≤ Ω) (hΩG : specNorm G ≤ Ω) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' G)) ≤ 6 * mval * β := by
  classical
  have hβ0 : 0 ≤ β := (specNorm_nonneg _).trans hβ
  have hm0 : 0 ≤ mval := by
    rw [hm]
    have := specNorm_nonneg S
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (specNorm_nonneg _))
      (specNorm_nonneg _)) (specNorm_nonneg _)
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · refine ⟨1, hasOrthonormalCols_one, ?_⟩
    rw [Subsingleton.elim (U * 1 - _) 0, specNorm_zero]
    have := mul_nonneg hm0 hβ0
    linarith
  have : Nonempty (Fin r) := ⟨⟨0, hr1⟩⟩
  set s := specNorm S with hs_def
  set g := specNorm G with hg_def
  set G₁ := G.submatrix id (Fin.castLE hr) with hG₁_def
  set K := Vᴴ * G₁ with hK_def
  set si := specNorm S⁻¹ with hsi_def
  set kk := specNorm K⁻¹ with hkk_def
  have hs0 : 0 ≤ s := specNorm_nonneg _
  have hg0 : 0 ≤ g := specNorm_nonneg _
  have hsi0 : 0 ≤ si := specNorm_nonneg _
  have hkk0 : 0 ≤ kk := specNorm_nonneg _
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hKdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hG
  have hssi : 1 ≤ s * si := by
    calc (1 : ℝ) = specNorm (S * S⁻¹) := by rw [Matrix.mul_nonsing_inv S hSdet, specNorm_one]
      _ ≤ s * si := specNorm_mul_le _ _
  have hKG : specNorm K ≤ g := (hV.specNorm_conjTranspose_mul_le G₁).trans
    (specNorm_submatrix_le G Function.injective_id (Fin.castLE_injective hr))
  have hgk : 1 ≤ g * kk := by
    calc (1 : ℝ) = specNorm (K * K⁻¹) := by rw [Matrix.mul_nonsing_inv K hKdet, specNorm_one]
      _ ≤ specNorm K * kk := specNorm_mul_le _ _
      _ ≤ g * kk := mul_le_mul_of_nonneg_right hKG hkk0
  have hmv : mval = (s + β + 1) * (g * kk * si) := by rw [hm]; ring
  obtain ⟨hX, hβ5⟩ := one_le_and_le_fifth_arith_aux hs0 hβ0 hg0 hsi0 hkk0 hssi hgk hmv hmβ
  have hgne : g ≠ 0 := by intro h; rw [h, zero_mul] at hgk; linarith
  -- signs of the constants
  have hcu : 0 ≤ cN * u := by
    by_contra hneg
    replace hneg := not_le.mp hneg
    apply hgne
    have hG0 : G = 0 := by
      ext i j
      by_contra hij
      have h := hM.isNormalSampler (G i j) ((norm_apply_le_specNorm G i j).trans hΩG)
      have hpos : 0 < max ‖G i j‖ τ := lt_max_of_lt_left (norm_pos_iff.mpr hij)
      have := mul_neg_of_neg_of_pos hneg hpos
      linarith [norm_nonneg (G i j - decodeComplex dec (M.normal (G i j)))]
    rw [hg_def, hG0, specNorm_zero]
  have hq0 : 0 ≤ μQ n * u := by
    have hz : (Matrix.of fun (_ : Fin n) (_ : Fin n) => (M.zero, M.zero)).map
        (decodeComplex dec) = 0 := by
      ext i j; apply Complex.ext <;> simp [decodeComplex, hM.dec_zero]
    obtain ⟨_, Q0, _, hQ0, _⟩ := hM.isQRErr
      (Matrix.of fun (_ : Fin n) (_ : Fin n) => (M.zero, M.zero))
      (by rw [hz, specNorm_zero]; exact hg0.trans hΩG)
    rw [max_self] at hQ0
    exact (specNorm_nonneg _).trans hQ0
  have ha0 : 0 ≤ μM n * u := mul_nonneg hμM hu₀
  set c := √(n : ℝ) * cN * u with hc_def
  set q := μQ n * u with hq_def
  set a := μM n * u with ha_def
  have hc0 : 0 ≤ c := by rw [hc_def, mul_assoc]; exact mul_nonneg (Real.sqrt_nonneg _) hcu
  have hbud : 4 * q + 4 * c + 2 * a ≤ β := by
    have : (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u = 4 * q + 4 * c + 2 * a := by ring
    linarith
  -- the stored sample
  set At := A'.map (decodeComplex dec) with hAt_def
  set Gs := G.map M.normal with hGs_def
  set Gt := Gs.map (decodeComplex dec) with hGt_def
  have hβ' : specNorm (A - At) ≤ β := hβ
  have hEG : specNorm (G - Gt) ≤ 2 * c * g :=
    specNorm_sub_map_normal_le_aux hM G hcu hτN hΩG
  have hAle : specNorm A ≤ s := by
    rw [hA]
    calc specNorm (U * S * Vᴴ) ≤ specNorm (U * S) * specNorm Vᴴ := specNorm_mul_le _ _
      _ = s * specNorm V := by rw [hU.specNorm_mul_left, specNorm_conjTranspose]
      _ ≤ s * 1 := mul_le_mul_of_nonneg_left hV.specNorm_le_one hs0
      _ = s := mul_one s
  have hAtle : specNorm At ≤ s + β := by
    calc specNorm At = specNorm (A - (A - At)) := by rw [sub_sub_cancel]
      _ ≤ specNorm A + specNorm (A - At) := specNorm_sub_le _ _
      _ ≤ s + β := add_le_add hAle hβ'
  have hGtle : specNorm Gt ≤ (1 + 2 * c) * g := by
    calc specNorm Gt = specNorm (G - (G - Gt)) := by rw [sub_sub_cancel]
      _ ≤ g + specNorm (G - Gt) := specNorm_sub_le _ _
      _ ≤ g + 2 * c * g := add_le_add le_rfl hEG
      _ = (1 + 2 * c) * g := by ring
  set P := (s + β) * ((1 + 2 * c) * g) with hP_def
  have hP0 : 0 ≤ P := by positivity
  have hprod : specNorm At * specNorm Gt ≤ P :=
    mul_le_mul hAtle hGtle (specNorm_nonneg _) (by linarith)
  have hτP : τ ≤ P := by
    refine hτ.trans ?_
    rw [hP_def]
    have h1 : g ≤ (1 + 2 * c) * g := le_mul_of_one_le_left hg0 (by linarith)
    calc s * g ≤ s * ((1 + 2 * c) * g) := mul_le_mul_of_nonneg_left h1 hs0
      _ ≤ (s + β) * ((1 + 2 * c) * g) :=
        mul_le_mul_of_nonneg_right (by linarith) (hg0.trans h1)
  have hc5 : c ≤ 1 / 20 := by linarith
  have ha5 : a ≤ 1 / 10 := by linarith
  have hP2 : (1 + a) * P ≤ 2 * (s + β) * g := range_arith_aux hs0 hβ0 hg0 hc0 hc5 ha5
  have hPa : P ≤ (1 + a) * P := le_mul_of_one_le_left hP0 (by linarith)
  -- the product
  set Ms := M.mm A' Gs with hMs_def
  set Mt := Ms.map (decodeComplex dec) with hMt_def
  have hMM : specNorm (At * Gt - Mt) ≤ a * P := by
    have h := hM.isMatMulErr.specNorm_mul_sub_le A' Gs (by linarith)
    rw [max_self, max_self] at h
    exact h.trans (mul_le_mul_of_nonneg_left (max_le hprod hτP) ha0)
  have hMtle : specNorm Mt ≤ (1 + a) * P := by
    calc specNorm Mt = specNorm (At * Gt - (At * Gt - Mt)) := by rw [sub_sub_cancel]
      _ ≤ specNorm (At * Gt) + specNorm (At * Gt - Mt) := specNorm_sub_le _ _
      _ ≤ P + a * P := add_le_add ((specNorm_mul_le _ _).trans hprod) hMM
      _ = (1 + a) * P := by ring
  -- the QR factorization
  obtain ⟨hR, Q', hQ', hQQ, hMQR⟩ := hM.isQRErr Ms (hMtle.trans (hP2.trans hΩ))
  rw [max_self] at hQQ hMQR
  set Qb := (M.qr Ms).1.map (decodeComplex dec) with hQb_def
  set Rb := (M.qr Ms).2.map (decodeComplex dec) with hRb_def
  have hQR : specNorm (Mt - Q' * Rb) ≤ q * ((1 + a) * P) :=
    hMQR.trans (mul_le_mul_of_nonneg_left (max_le hMtle (hτP.trans hPa)) hq0)
  -- the total error
  set T := A * G - Q' * Rb with hT_def
  have hT : specNorm T ≤ g * (β + 3 / 5 * (s + β) * β) := by
    have heq : T = (A - At) * G + At * (G - Gt) + (At * Gt - Mt) + (Mt - Q' * Rb) := by
      rw [hT_def, Matrix.sub_mul, Matrix.mul_sub]; abel
    have h1 : specNorm ((A - At) * G) ≤ β * g :=
      (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hβ' hg0)
    have h2 : specNorm (At * (G - Gt)) ≤ (s + β) * (2 * c * g) :=
      (specNorm_mul_le _ _).trans (mul_le_mul hAtle hEG (specNorm_nonneg _) (by linarith))
    refine le_trans ?_ (z_bound_arith_aux hs0 hβ0 hg0 hc0 ha0 hq0 hbud hβ5)
    rw [heq]
    refine (specNorm_add_le _ _).trans ?_
    refine add_le_add ((specNorm_add_le _ _).trans ?_) hQR
    exact add_le_add ((specNorm_add_le _ _).trans (add_le_add h1 h2)) hMM
  -- the first `r` columns
  set e := Fin.castLE hr with he_def
  set Q'₁ := Q'.submatrix id e with hQ'₁_def
  set R₁₁ := Rb.submatrix e e with hR₁₁_def
  set Z := T.submatrix id e with hZ_def
  have hZ : specNorm Z ≤ specNorm T :=
    specNorm_submatrix_le T Function.injective_id (Fin.castLE_injective hr)
  have hAG₁ : A * G₁ = Q'₁ * R₁₁ + Z := by
    rw [hQ'₁_def, hR₁₁_def, ← submatrix_mul_castLE_of_isUpperTrapezoidal_aux hr Q' Rb hR]
    ext i j
    simp only [hZ_def, hT_def, hG₁_def, Matrix.add_apply, Matrix.submatrix_apply, id,
      Matrix.sub_apply, Matrix.mul_apply]
    ring
  set C := R₁₁ * K⁻¹ * S⁻¹ with hC_def
  have hUeq : U - Q'₁ * C = Z * K⁻¹ * S⁻¹ := by
    have hU' : U = A * G₁ * K⁻¹ * S⁻¹ := by
      calc U = U * S * K * K⁻¹ * S⁻¹ := by
            rw [Matrix.mul_nonsing_inv_cancel_right K _ hKdet,
              Matrix.mul_nonsing_inv_cancel_right S _ hSdet]
        _ = A * G₁ * K⁻¹ * S⁻¹ := by rw [hA, hK_def]; simp only [Matrix.mul_assoc]
    rw [hU', hAG₁, hC_def]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    abel
  set δ := mval * β - q / 6 with hδ_def
  have hδ : specNorm (U - Q'₁ * C) ≤ δ := by
    rw [hUeq]
    have h1 : specNorm (Z * K⁻¹ * S⁻¹) ≤ specNorm Z * kk * si :=
      (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) hsi0)
    refine h1.trans ?_
    have h2 : specNorm Z * kk * si ≤ g * (β + 3 / 5 * (s + β) * β) * kk * si :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hZ.trans hT) hkk0) hsi0
    refine h2.trans ?_
    rw [hδ_def, hmv]
    exact delta_arith_aux hβ0 hg0 hsi0 hkk0 hX (by linarith)
  have hδ0 : 0 ≤ δ := (specNorm_nonneg _).trans hδ
  obtain ⟨W, hW, hUW⟩ := HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le hU
    (HasOrthonormalCols.submatrix_castLE_aux hr hQ') (ν := 0) (by rw [sub_self, specNorm_zero])
    hδ hδ0 (by rw [hδ_def]; linarith)
  refine ⟨W, hW, ?_⟩
  rw [decodeMatrix_deflate_aux M dec hr A' G]
  have hQ₁ : specNorm (Q'₁ - Qb.submatrix id e) ≤ q := by
    rw [hQ'₁_def, show Q'.submatrix id e - Qb.submatrix id e = (Q' - Qb).submatrix id e from rfl]
    exact (specNorm_submatrix_le _ Function.injective_id (Fin.castLE_injective hr)).trans hQQ
  calc specNorm (U * W - Qb.submatrix id e)
      = specNorm ((U * W - Q'₁) + (Q'₁ - Qb.submatrix id e)) := by rw [sub_add_sub_cancel]
    _ ≤ 6 * δ + q := (specNorm_add_le _ _).trans (add_le_add hUW hQ₁)
    _ = 6 * mval * β := by rw [hδ_def]; ring

/-- **Deterministic accuracy of randomized deflation** (Theorem 3.3, deterministic half): under
the machine contract `NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ with constants
$\mu_{\mathrm{MM}}$, $\mu_{\mathrm{QR}}$, $c_{\mathrm N}$, let
$r \le n$, $\mathbf{U}, \mathbf{V} \in \mathbb{C}^{n \times r}$ have orthonormal columns,
$\mathbf{S} \in \mathbb{C}^{r \times r}$ be invertible, $\mathbf{A} =
\mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$, $\widetilde{\mathbf{A}}$ stored with
$\|\mathbf{A} - \bar{\widetilde{\mathbf{A}}}\|_2 \le \beta$, and $\mathbf{G}$ have
$\mathbf{V}^{\mathsf{H}}\mathbf{G}_1$ invertible, $\mathbf{G}_1$ its first $r$ columns. With
$m = (\|\mathbf{S}\|_2 + \beta + 1)\|\mathbf{S}^{-1}\|_2\|\mathbf{G}\|_2
\|(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)^{-1}\|_2$, if $m\beta \le 1/5$,
$(4\mu_{\mathrm{QR}}(n) + 4\sqrt n\,c_{\mathrm N} + 2\mu_{\mathrm{MM}}(n))u \le \beta$,
$\tau \le \|\mathbf{S}\|_2\|\mathbf{G}\|_2$, $\sqrt n\,\tau \le \|\mathbf{G}\|_2$ (the floor of the
normal sampler, absorbed into a factor $2$) and $2(\|\mathbf{S}\|_2 + \beta)\|\mathbf{G}\|_2 \le
\Omega$, $\|\mathbf{G}\|_2 \le \Omega$ (so the normal sampler's contract covers every entry), then
there is a unitary $\mathbf{W}$ with $$\|\mathbf{U}\mathbf{W} -
\mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le 6m\beta \,,$$ $\mathsf{deflate}$ the decoded
output of `NLAlib.deflate` with ideal sample $\mathbf{G}$. [Shah2024, Theorem 3.3], there for
$\mathbf{S}$ the diagonal of singular values and with the probability folded in.
Proof: [Shah2024, proof of Theorem 3.3], (3.1) there: write $\widetilde{\mathbf{G}} =
\mathbf{G} + \mathbf{E}_{\mathbf{G}}$ with $\|\mathbf{E}_{\mathbf{G}}\|_2 \le \sqrt n\,c_{\mathrm N}
u\|\mathbf{G}\|_2$ (entrywise, `NLAlib.specNorm_le_frobNorm`,
`NLAlib.frobNorm_le_sqrt_card_mul_specNorm`), $\mathbf{M} = \widetilde{\mathbf{A}}
\widetilde{\mathbf{G}} + \mathbf{F}$ (product contract), $\mathbf{M}' = \mathbf{Q}'\mathbf{R}$
and $\mathbf{Q} = \mathbf{Q}' + \mathbf{E}_{\mathbf{Q}}$ (QR contract), $\mathbf{R}$ upper
trapezoidal so its first $r$ columns are $\mathbf{R}_{11}$ on top of $\mathbf{0}$; then
$\mathbf{U} = \mathbf{Q}_1\mathbf{C} + \mathbf{Z}(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)^{-1}
\mathbf{S}^{-1}$ with $\mathbf{C} = \mathbf{R}_{11}(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)^{-1}
\mathbf{S}^{-1}$ and $\|\mathbf{Z}\|_2 \le [(4\mu_{\mathrm{QR}} + 2\sqrt n c_{\mathrm N} +
2\mu_{\mathrm{MM}})(\|\mathbf{S}\|_2 + \beta)u + \beta]\|\mathbf{G}\|_2$, so
$\|\mathbf{U} - \mathbf{Q}_1\mathbf{C}\|_2 \le m\beta$; conclude with
`NLAlib.HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le`
($\nu = \mu_{\mathrm{QR}}u \le \beta/4 \le m\beta$; $m \ge 1$ when $r \ge 1$, and $r = 0$ is
trivial). The floor and range conditions make each contract applicable with the upper bounds
used. Split into private lemmas for $\mathbf{E}_{\mathbf{G}}$, the identity for $\mathbf{U}$ and
the bound on $\mathbf{Z}$. L, about 140 lines. -/
theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β mval : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A G : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β)
    (hG : IsUnit (Vᴴ * G.submatrix id (Fin.castLE hr)))
    (hm : mval = (specNorm S + β + 1) * specNorm S⁻¹ * specNorm G *
      specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹)
    (hmβ : mval * β ≤ 1 / 5) (hu : (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β)
    (hτ : τ ≤ specNorm S * specNorm G) (hτN : τ * √(n : ℝ) ≤ specNorm G)
    (hΩ : 2 * (specNorm S + β) * specNorm G ≤ Ω) (hΩG : specNorm G ≤ Ω) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' G)) ≤ 6 * mval * β := by
  sorry

end NLAlib
