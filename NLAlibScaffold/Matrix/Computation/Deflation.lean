/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.Deflation

/-!
# Sharper constants for deflation (scaffold, stage HDIAG-BOUNDS)

Statements for `NLAlib/Matrix/Computation/Deflation.lean` (design note
`docs/design/Eigensolvers-HermitianDiagonalization-Bounds.md`, item I7): the nearest unitary
rotation between two orthonormal bases at canonical-angle distance $\delta$ is within
$\sqrt2\,\delta$ (DF1', in place of $6\delta$), and the deterministic deflation bound with the
roundings charged at $1/16$ of the accuracy, so that the output error is $\tfrac32 m\beta$ with
$m \approx \|\mathbf{S}^{-1}\|_2\|\mathbf{G}\|_2\|(\mathbf{V}^{\mathsf H}\mathbf{G}_1)^{-1}\|_2$
(DF2', in place of $6m\beta$ with the factor $\|\mathbf{S}\|_2 + \beta + 1$).

## Main results

* `NLAlib.HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le_sqrt_two_mul` (DF1').
* `NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le`
  (DF2').
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- The key identity: for $\mathbf{Q} = \mathbf{U}\mathbf{W} - \mathbf{Q}'$ with orthonormal
columns, $\mathbf{Q}^{\mathsf H}\mathbf{Q} = \mathbf{W}^{\mathsf H}(\mathbf{W} - \mathbf{T}) +
(\mathbf{W} - \mathbf{T})^{\mathsf H}\mathbf{W}$ where $\mathbf{T} = \mathbf{U}^{\mathsf H}
\mathbf{Q}'$. -/
private theorem conjTranspose_mul_self_sub_eq {m r 𝕜 : Type*} [RCLike 𝕜] [Fintype m]
    [Fintype r] [DecidableEq r] {U Q' : Matrix m r 𝕜} {W : Matrix r r 𝕜}
    (hU : HasOrthonormalCols U) (hQ' : HasOrthonormalCols Q') (hW : HasOrthonormalCols W) :
    (U * W - Q')ᴴ * (U * W - Q') = Wᴴ * (W - Uᴴ * Q') + (W - Uᴴ * Q')ᴴ * W := by
  rw [hasOrthonormalCols_iff] at hU hQ' hW
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul, hQ', hW]
  abel

open scoped MatrixOrder in
/-- A square near-isometry $\mathbf{B}$ with $|\|\mathbf{B}\mathbf{x}\| - \|\mathbf{x}\|| \le
a\|\mathbf{x}\|$, $a < 1$, is within $a$ of a unitary. -/
private theorem exists_hasOrthonormalCols_specNorm_sub_le_of_near_isometry
    {𝕜 : Type*} [RCLike 𝕜] {r : Type*} [Fintype r] [DecidableEq r]
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

open scoped MatrixOrder in
/-- For $\delta \ge 1$ the bound is trivial: the polar factor $\mathbf{V}$ of
$\mathbf{U}^{\mathsf H}\mathbf{Q}'$ gives
$\|\mathbf{U}\mathbf{V} - \mathbf{Q}'\|_2^2 \le 2 \le 2\delta^2$. -/
private theorem exists_hasOrthonormalCols_specNorm_mul_sub_le_of_one_le
    {𝕜 : Type*} [RCLike 𝕜] {m r : Type*} [Fintype m] [Fintype r] [DecidableEq r]
    {U Q' : Matrix m r 𝕜} (hU : HasOrthonormalCols U) (hQ' : HasOrthonormalCols Q') {δ : ℝ}
    (h1 : 1 ≤ δ) :
    ∃ W : Matrix r r 𝕜, HasOrthonormalCols W ∧ specNorm (U * W - Q') ≤ √2 * δ := by
  have hδ0 : 0 ≤ δ := zero_le_one.trans h1
  have hsq : ∀ s : ℝ, 0 ≤ s → s ^ 2 ≤ 2 * δ ^ 2 → s ≤ √2 * δ := fun s hs h => by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h3 := Real.sqrt_nonneg 2
    nlinarith [mul_nonneg h3 hδ0]
  obtain ⟨V, hV, hVT⟩ := exists_hasOrthonormalCols_mul_sqrt_eq (Uᴴ * Q') le_rfl
  have hP0 := CFC.sqrt_nonneg ((Uᴴ * Q')ᴴ * (Uᴴ * Q'))
  set P := CFC.sqrt ((Uᴴ * Q')ᴴ * (Uᴴ * Q')) with hPdef
  have hPh : Pᴴ = P := hP0.isSelfAdjoint
  have h1' : Vᴴ * (Uᴴ * Q') = P := by
    rw [← hVT, ← Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.one_mul]
  have h2 : (Uᴴ * Q')ᴴ * V = P := by
    rw [← hVT, Matrix.conjTranspose_mul, Matrix.mul_assoc, hV.conjTranspose_mul_self,
      Matrix.mul_one, hPh]
  have hQQ : (U * V - Q')ᴴ * (U * V - Q') = (1 + 1) - (P + P) := by
    rw [conjTranspose_mul_self_sub_eq hU hQ' hV, Matrix.mul_sub, Matrix.conjTranspose_sub,
      Matrix.sub_mul, hV.conjTranspose_mul_self, h1', h2]
    abel
  have hle : (U * V - Q')ᴴ * (U * V - Q') ≤ (2 : ℝ) • (1 : Matrix r r 𝕜) := by
    have e : (2 : ℝ) • (1 : Matrix r r 𝕜) - (U * V - Q')ᴴ * (U * V - Q') = P + P := by
      rw [hQQ, two_smul]; abel
    exact sub_nonneg.mp (e ▸ add_nonneg hP0 hP0)
  have hn := (specNorm_sq_le_iff_conjTranspose_mul_self_le (by norm_num : (0 : ℝ) ≤ 2)).mpr hle
  refine ⟨V, hV, hsq _ (specNorm_nonneg _) ?_⟩
  nlinarith

open scoped MatrixOrder in
/-- **Orthonormal bases close up to a rotation, with constant $\sqrt2$** (DF1'): if
$\mathbf{U}, \mathbf{Q}'$ have orthonormal columns and $\|\mathbf{U} - \mathbf{Q}'\mathbf{C}\|_2
\le \delta$ for some $\mathbf{C}$, there is a unitary $\mathbf{W}$ with $\|\mathbf{U}\mathbf{W} -
\mathbf{Q}'\|_2 \le \sqrt2\,\delta$. The orthogonal Procrustes rotation: for canonical angles
$\theta_i$ the optimum is $\max_i 2\sin(\theta_i/2)$ [StewartSun1990, Chapter I.5].
Proof: $(\mathbf{I} - \mathbf{Q}'\mathbf{Q}'^{\mathsf H})\mathbf{U} = (\mathbf{I} -
\mathbf{Q}'\mathbf{Q}'^{\mathsf H})(\mathbf{U} - \mathbf{Q}'\mathbf{C})$, so for a unit $v$,
$\|\mathbf{Q}'^{\mathsf H}\mathbf{U}v\|^2 \ge 1 - \delta^2$ and
$\sigma_{\min}(\mathbf{Q}'^{\mathsf H}\mathbf{U}) \ge \sqrt{1 - \delta^2}$ (for $\delta \le 1$;
for $\delta > 1$ use $\|\mathbf{U}\mathbf{W} - \mathbf{Q}'\|_2^2 \le 2$ below). Take $\mathbf{W}$
the polar factor of $\mathbf{U}^{\mathsf H}\mathbf{Q}'$ (`NLAlib.polarFactor`), so that
$\mathbf{W}^{\mathsf H}\mathbf{U}^{\mathsf H}\mathbf{Q}' = \mathbf{P} \succeq 0$ with
eigenvalues the singular values; then $(\mathbf{U}\mathbf{W} - \mathbf{Q}')^{\mathsf
H}(\mathbf{U}\mathbf{W} - \mathbf{Q}') = 2(\mathbf{I} - \mathbf{P})$ and
$\|\mathbf{U}\mathbf{W} - \mathbf{Q}'\|_2^2 = 2(1 - \sigma_{\min}) \le 2(1 - \sqrt{1 - \delta^2})
\le 2\delta^2$. M, about 90 lines (DF1's polar-factor facts reused). -/
theorem HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le_sqrt_two_mul
    {𝕜 : Type*} [RCLike 𝕜] {m r : Type*} [Fintype m] [Fintype r] [DecidableEq r]
    {U Q' : Matrix m r 𝕜} (hU : HasOrthonormalCols U) (hQ' : HasOrthonormalCols Q')
    {C : Matrix r r 𝕜} {δ : ℝ} (hδ : specNorm (U - Q' * C) ≤ δ) :
    ∃ W : Matrix r r 𝕜, HasOrthonormalCols W ∧ specNorm (U * W - Q') ≤ √2 * δ := by
  classical
  have hδ0 : 0 ≤ δ := (specNorm_nonneg _).trans hδ
  have hsq : ∀ s : ℝ, 0 ≤ s → s ^ 2 ≤ 2 * δ ^ 2 → s ≤ √2 * δ := fun s hs h => by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have h3 := Real.sqrt_nonneg 2
    nlinarith [mul_nonneg h3 hδ0]
  rcases lt_or_ge δ 1 with h1 | h1
  · -- Near case: the near-isometry `Q'ᴴ U` is within δ² of a unitary `W0`; take `W = W0ᴴ`.
    have hpy : ∀ y : r → 𝕜, ‖WithLp.toLp 2 y‖ ^ 2 =
        ‖WithLp.toLp 2 ((Q'ᴴ * U) *ᵥ y)‖ ^ 2 +
          ‖WithLp.toLp 2 ((1 - Q' * Q'ᴴ) *ᵥ (U *ᵥ y))‖ ^ 2 := by
      intro y
      have h := (hQ'.isStarProjection_mul_conjTranspose).norm_toLp_sq_eq_add (U *ᵥ y)
      have e : (Q' * Q'ᴴ) *ᵥ (U *ᵥ y) = Q' *ᵥ ((Q'ᴴ * U) *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [hU.norm_toLp_mulVec] at h
      rw [h, e, hQ'.norm_toLp_mulVec]
    have hEb : ∀ y : r → 𝕜,
        ‖WithLp.toLp 2 ((1 - Q' * Q'ᴴ) *ᵥ (U *ᵥ y))‖ ≤ δ * ‖WithLp.toLp 2 y‖ := by
      intro y
      have hF : (1 - Q' * Q'ᴴ) * Q' = 0 := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hQ'.conjTranspose_mul_self,
          Matrix.mul_one, sub_self]
      have hmat : (1 - Q' * Q'ᴴ) * U = (1 - Q' * Q'ᴴ) * (U - Q' * C) := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc (1 - Q' * Q'ᴴ) Q' C, hF, Matrix.zero_mul, sub_zero]
      have hP1 := hQ'.isStarProjection_mul_conjTranspose.one_sub
      calc ‖WithLp.toLp 2 ((1 - Q' * Q'ᴴ) *ᵥ (U *ᵥ y))‖
          = ‖WithLp.toLp 2 ((1 - Q' * Q'ᴴ) *ᵥ ((U - Q' * C) *ᵥ y))‖ := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]
        _ ≤ ‖WithLp.toLp 2 ((U - Q' * C) *ᵥ y)‖ := hP1.norm_toLp_mulVec_le _
        _ ≤ specNorm (U - Q' * C) * ‖WithLp.toLp 2 y‖ := norm_toLp_mulVec_le _ _
        _ ≤ δ * ‖WithLp.toLp 2 y‖ := mul_le_mul_of_nonneg_right hδ (norm_nonneg _)
    have hB : ∀ y : r → 𝕜, |‖WithLp.toLp 2 ((Q'ᴴ * U) *ᵥ y)‖ - ‖WithLp.toLp 2 y‖| ≤
        δ ^ 2 * ‖WithLp.toLp 2 y‖ := by
      intro y
      have hp := hpy y
      have he := hEb y
      have he0 := norm_nonneg (WithLp.toLp 2 ((1 - Q' * Q'ᴴ) *ᵥ (U *ᵥ y)))
      have hn := norm_nonneg (WithLp.toLp 2 y)
      have hs := norm_nonneg (WithLp.toLp 2 ((Q'ᴴ * U) *ᵥ y))
      generalize ‖WithLp.toLp 2 ((Q'ᴴ * U) *ᵥ y)‖ = s at *
      generalize ‖WithLp.toLp 2 ((1 - Q' * Q'ᴴ) *ᵥ (U *ᵥ y))‖ = e at *
      generalize ‖WithLp.toLp 2 y‖ = n at *
      have hd0 : 0 ≤ 1 - δ ^ 2 := by nlinarith
      have hlo2 : ((1 - δ ^ 2) * n) ^ 2 ≤ s ^ 2 := by
        nlinarith [mul_le_mul he he he0 (mul_nonneg hδ0 hn),
          mul_nonneg (mul_nonneg hd0 (sq_nonneg δ)) (sq_nonneg n)]
      have hlo : (1 - δ ^ 2) * n ≤ s :=
        (pow_le_pow_iff_left₀ (mul_nonneg hd0 hn) hs two_ne_zero).mp hlo2
      have hup2 : s ^ 2 ≤ n ^ 2 := by nlinarith [sq_nonneg e]
      have hup : s ≤ n := (pow_le_pow_iff_left₀ hs hn two_ne_zero).mp hup2
      rw [abs_le]; constructor <;> nlinarith
    obtain ⟨W0, hW0, hW0S⟩ :=
      exists_hasOrthonormalCols_specNorm_sub_le_of_near_isometry (B := Q'ᴴ * U) (a := δ ^ 2)
        (sq_nonneg δ) (by nlinarith) hB
    have hW : HasOrthonormalCols W0ᴴ := hW0.conjTranspose_of_card_eq rfl
    have hT : Uᴴ * Q' = (Q'ᴴ * U)ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    have hD : specNorm (W0ᴴ - Uᴴ * Q') ≤ δ ^ 2 := by
      rw [hT, ← Matrix.conjTranspose_sub, specNorm_conjTranspose]; exact hW0S
    have hWn : specNorm W0ᴴ ≤ 1 := by rw [specNorm_conjTranspose]; exact hW0.specNorm_le_one
    have hWn' : specNorm (W0ᴴ)ᴴ ≤ 1 := by rw [specNorm_conjTranspose]; exact hWn
    have hDh : specNorm (W0ᴴ - Uᴴ * Q')ᴴ ≤ δ ^ 2 := by rw [specNorm_conjTranspose]; exact hD
    have hn2 : specNorm ((U * W0ᴴ - Q')ᴴ * (U * W0ᴴ - Q')) ≤ 2 * δ ^ 2 := by
      rw [conjTranspose_mul_self_sub_eq hU hQ' hW]
      refine (specNorm_add_le _ _).trans ?_
      have h1 := (specNorm_mul_le _ _).trans (mul_le_mul hWn' hD (specNorm_nonneg _) zero_le_one)
      have h2 := (specNorm_mul_le _ _).trans (mul_le_mul hDh hWn (specNorm_nonneg _) (sq_nonneg δ))
      rw [one_mul] at h1
      rw [mul_one] at h2
      linarith
    refine ⟨W0ᴴ, hW, hsq _ (specNorm_nonneg _) ?_⟩
    rw [specNorm_conjTranspose_mul_self] at hn2
    exact hn2
  · exact exists_hasOrthonormalCols_specNorm_mul_sub_le_of_one_le hU hQ' h1

/-- The first $r$ columns of $\mathbf{Q}\mathbf{R}$, $\mathbf{R}$ upper trapezoidal, are
$\mathbf{Q}_1\mathbf{R}_{11}$. -/
private theorem submatrix_mul_castLE_of_isUpperTrapezoidal {n r : ℕ} (hr : r ≤ n)
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
private theorem decodeMatrix_deflate {F : Type*} (M : FloatMachine F ℝ ℂ) (dec : F → ℝ)
    {n r : ℕ} (hr : r ≤ n) (A' : Matrix (Fin n) (Fin n) (F × F))
    (G : Matrix (Fin n) (Fin n) ℂ) :
    decodeMatrix dec (deflate M r A' G) =
      ((M.qr (M.mm A' (G.map M.normal))).1.map (decodeComplex dec)).submatrix id
        (Fin.castLE hr) := by
  ext i j
  simp [decodeMatrix, deflate, lt_of_lt_of_le j.2 hr, Fin.castLE]

/-- The error of the stored sample: $\|\mathbf{G} - \widetilde{\mathbf{G}}\|_2 \le
2\sqrt n\,c_{\mathrm N}u\|\mathbf{G}\|_2$. -/
private theorem specNorm_sub_map_normal_le {F : Type*} {M : FloatMachine F ℝ ℂ}
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

/-- Under the contract, $\mu_{\mathrm{QR}}(n)u \ge 0$: the QR error bound of the zero matrix. -/
private theorem FloatMachine.IsAccurate.qrConst_mul_nonneg {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (n : ℕ)
    (hΩ : 0 ≤ Ω) : 0 ≤ μQ n * u := by
  have hz : (Matrix.of fun (_ : Fin n) (_ : Fin n) => (M.zero, M.zero)).map
      (decodeComplex dec) = 0 := by
    ext i j; apply Complex.ext <;> simp [decodeComplex, hM.dec_zero]
  obtain ⟨_, Q0, _, hQ0, _⟩ := hM.isQRErr
    (Matrix.of fun (_ : Fin n) (_ : Fin n) => (M.zero, M.zero))
    (by rw [hz, specNorm_zero]; exact hΩ)
  rw [max_self] at hQ0
  exact (specNorm_nonneg _).trans hQ0

/-- Under the contract, $c_{\mathrm N}u \ge 0$ once the normal sampler is applied to a nonzero
entry in range. -/
private theorem FloatMachine.IsAccurate.normalConst_mul_nonneg {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G ≠ 0)
    (hΩG : specNorm G ≤ Ω) : 0 ≤ cN * u := by
  by_contra hneg
  replace hneg := not_le.mp hneg
  apply hG
  ext i j
  by_contra hij
  have h := hM.isNormalSampler (G i j) ((norm_apply_le_specNorm G i j).trans hΩG)
  have hpos : 0 < max ‖G i j‖ τ := lt_max_of_lt_left (norm_pos_iff.mpr hij)
  have := mul_neg_of_neg_of_pos hneg hpos
  linarith [norm_nonneg (G i j - decodeComplex dec (M.normal (G i j)))]

/-- The arithmetic of the range conditions. -/
private theorem deflate_arith_range {s β g c a : ℝ} (hs : 0 ≤ s) (hβ0 : 0 ≤ β) (hg : 0 ≤ g)
    (hc : 0 ≤ c) (hc5 : c ≤ 1 / 20) (ha5 : a ≤ 1 / 10) :
    (1 + a) * ((s + β) * ((1 + 2 * c) * g)) ≤ 2 * (s + β) * g := by
  have h1 : (1 + a) * (1 + 2 * c) ≤ 2 := by nlinarith
  have h2 : 0 ≤ (s + β) * g := mul_nonneg (by linarith) hg
  nlinarith [mul_le_mul_of_nonneg_left h1 h2]

/-- The arithmetic of the bound on $\mathbf{Z}$, roundings charged at $1/16$. -/
private theorem deflate_arith_error_of_mul_le {s β g c a q : ℝ} (hs : 0 ≤ s) (hβ0 : 0 ≤ β)
    (hg : 0 ≤ g) (hc : 0 ≤ c) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hbud : 16 * (4 * q + 4 * c + 2 * a) ≤ β) (hβ8 : β ≤ 1 / 8) :
    β * g + (s + β) * (2 * c * g) + a * ((s + β) * ((1 + 2 * c) * g)) +
        q * ((1 + a) * ((s + β) * ((1 + 2 * c) * g))) ≤
      g * (β + (s + β) * β / 16) := by
  have hbr : 2 * c + a * (1 + 2 * c) + q * ((1 + a) * (1 + 2 * c)) ≤ β / 16 := by
    have hc' : c ≤ 1 / 20 := by linarith
    have ha' : a ≤ 1 / 10 := by linarith
    nlinarith [mul_nonneg ha hc, mul_nonneg hq hc, mul_nonneg hq ha,
      mul_nonneg (mul_nonneg hq ha) hc]
  have hsg : 0 ≤ (s + β) * g := mul_nonneg (by linarith) hg
  nlinarith [mul_le_mul_of_nonneg_left hbr hsg]

/-- The computed product and QR factorization of `NLAlib.deflate`, roundings charged at $1/16$:
an exact factorization $\mathbf{Q}'\mathbf{R}$, $\mathbf{R}$ upper trapezoidal, within
$\|\mathbf{G}\|_2(\beta + (s + \beta)\beta/16)$ of $\mathbf{A}\mathbf{G}$, with $\mathbf{Q}'$
within $\mu_{\mathrm{QR}}(n)u$ of the computed $\mathbf{Q}$. -/
private theorem FloatMachine.IsAccurate.exists_specNorm_mul_sub_mul_qr_le_of_mul_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β s : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n : ℕ} {A G : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hs0 : 0 ≤ s) (hβ0 : 0 ≤ β) (hβ8 : β ≤ 1 / 8)
    (hAle : specNorm A ≤ s) (hβ : specNorm (A - decodeMatrix dec A') ≤ β)
    (hcu : 0 ≤ cN * u) (hq0 : 0 ≤ μQ n * u) (ha0 : 0 ≤ μM n * u)
    (hu : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β)
    (hτ : τ ≤ s * specNorm G) (hτN : τ * √(n : ℝ) ≤ specNorm G)
    (hΩ : 2 * (s + β) * specNorm G ≤ Ω) (hΩG : specNorm G ≤ Ω) :
    ∃ Q' R : Matrix (Fin n) (Fin n) ℂ, HasOrthonormalCols Q' ∧ IsUpperTrapezoidal R ∧
      specNorm (Q' - (M.qr (M.mm A' (G.map M.normal))).1.map (decodeComplex dec)) ≤ μQ n * u ∧
      specNorm (A * G - Q' * R) ≤ specNorm G * (β + (s + β) * β / 16) := by
  set g := specNorm G with hg_def
  have hg0 : 0 ≤ g := specNorm_nonneg _
  set c := √(n : ℝ) * cN * u with hc_def
  set q := μQ n * u with hq_def
  set a := μM n * u with ha_def
  have hc0 : 0 ≤ c := by rw [hc_def, mul_assoc]; exact mul_nonneg (Real.sqrt_nonneg _) hcu
  have hbud : 16 * (4 * q + 4 * c + 2 * a) ≤ β := by
    have : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u =
        16 * (4 * q + 4 * c + 2 * a) := by ring
    linarith
  -- the stored sample
  set At := A'.map (decodeComplex dec) with hAt_def
  set Gs := G.map M.normal with hGs_def
  set Gt := Gs.map (decodeComplex dec) with hGt_def
  have hβ' : specNorm (A - At) ≤ β := hβ
  have hEG : specNorm (G - Gt) ≤ 2 * c * g :=
    specNorm_sub_map_normal_le hM G hcu hτN hΩG
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
  have hP2 : (1 + a) * P ≤ 2 * (s + β) * g := deflate_arith_range hs0 hβ0 hg0 hc0 hc5 ha5
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
  have hT : specNorm T ≤ g * (β + (s + β) * β / 16) := by
    have heq : T = (A - At) * G + At * (G - Gt) + (At * Gt - Mt) + (Mt - Q' * Rb) := by
      rw [hT_def, Matrix.sub_mul, Matrix.mul_sub]; abel
    have h1 : specNorm ((A - At) * G) ≤ β * g :=
      (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hβ' hg0)
    have h2 : specNorm (At * (G - Gt)) ≤ (s + β) * (2 * c * g) :=
      (specNorm_mul_le _ _).trans (mul_le_mul hAtle hEG (specNorm_nonneg _) (by linarith))
    refine le_trans ?_ (deflate_arith_error_of_mul_le hs0 hβ0 hg0 hc0 ha0 hq0 hbud hβ8)
    rw [heq]
    refine (specNorm_add_le _ _).trans ?_
    refine add_le_add ((specNorm_add_le _ _).trans ?_) hQR
    exact add_le_add ((specNorm_add_le _ _).trans (add_le_add h1 h2)) hMM
  exact ⟨Q', Rb, hQ', hR, hQQ, hT⟩

/-- The first $r$ columns of an exact factorization $\mathbf{Q}'\mathbf{R}$ near
$\mathbf{A}\mathbf{G}$, $\mathbf{A} = \mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$, are within
$\sqrt2\,\delta$ of $\mathbf{U}$ up to a rotation, and so are those of a matrix near
$\mathbf{Q}'$. -/
private theorem exists_hasOrthonormalCols_specNorm_mul_sub_submatrix_le_sqrt_two_mul {n r : ℕ}
    (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) {S : Matrix (Fin r) (Fin r) ℂ}
    (hS : IsUnit S) {A G Q' R Q : Matrix (Fin n) (Fin n) ℂ} (hA : A = U * S * Vᴴ)
    (hG : IsUnit (Vᴴ * G.submatrix id (Fin.castLE hr))) (hQ' : HasOrthonormalCols Q')
    (hR : IsUpperTrapezoidal R) {q δ : ℝ} (hQ : specNorm (Q' - Q) ≤ q)
    (hδ : specNorm (A * G - Q' * R) * specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹ *
      specNorm S⁻¹ ≤ δ) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - Q.submatrix id (Fin.castLE hr)) ≤ √2 * δ + q := by
  set e := Fin.castLE hr with he_def
  set G₁ := G.submatrix id e with hG₁_def
  set K := Vᴴ * G₁ with hK_def
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hKdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hG
  set T := A * G - Q' * R with hT_def
  set Q'₁ := Q'.submatrix id e with hQ'₁_def
  set Z := T.submatrix id e with hZ_def
  have hAG₁ : A * G₁ = Q'₁ * R.submatrix e e + Z := by
    rw [hQ'₁_def, ← submatrix_mul_castLE_of_isUpperTrapezoidal hr Q' R hR]
    ext i j
    simp only [hZ_def, hT_def, hG₁_def, Matrix.add_apply, Matrix.submatrix_apply, id,
      Matrix.sub_apply, Matrix.mul_apply]
    ring
  set C := R.submatrix e e * K⁻¹ * S⁻¹ with hC_def
  have hUeq : U - Q'₁ * C = Z * K⁻¹ * S⁻¹ := by
    have hU' : U = A * G₁ * K⁻¹ * S⁻¹ := by
      calc U = U * S * K * K⁻¹ * S⁻¹ := by
            rw [Matrix.mul_nonsing_inv_cancel_right K _ hKdet,
              Matrix.mul_nonsing_inv_cancel_right S _ hSdet]
        _ = A * G₁ * K⁻¹ * S⁻¹ := by rw [hA, hK_def]; simp only [Matrix.mul_assoc]
    rw [hU', hAG₁, hC_def]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    abel
  have hδ' : specNorm (U - Q'₁ * C) ≤ δ := by
    rw [hUeq]
    refine ((specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _)
      (specNorm_nonneg _))).trans (le_trans ?_ hδ)
    gcongr
    exact specNorm_submatrix_le T Function.injective_id (Fin.castLE_injective hr)
  have hQ'₁ : HasOrthonormalCols Q'₁ := hQ'.submatrix (Equiv.refl _) (Fin.castLE_injective hr)
  obtain ⟨W, hW, hUW⟩ := hU.exists_hasOrthonormalCols_specNorm_mul_sub_le_sqrt_two_mul
    hQ'₁ hδ'
  refine ⟨W, hW, ?_⟩
  have hQ₁ : specNorm (Q'₁ - Q.submatrix id e) ≤ q := by
    rw [hQ'₁_def, show Q'.submatrix id e - Q.submatrix id e = (Q' - Q).submatrix id e from rfl]
    exact (specNorm_submatrix_le _ Function.injective_id (Fin.castLE_injective hr)).trans hQ
  calc specNorm (U * W - Q.submatrix id e)
      = specNorm ((U * W - Q'₁) + (Q'₁ - Q.submatrix id e)) := by rw [sub_add_sub_cancel]
    _ ≤ √2 * δ + q := (specNorm_add_le _ _).trans (add_le_add hUW hQ₁)

/-- The arithmetic of the final bound: $\sqrt2$ times the bound on
$\|\mathbf{Z}\mathbf{K}^{-1}\mathbf{S}^{-1}\|_2$, plus $q$, is at most $\tfrac32 m\beta$. -/
private theorem deflate_arith_sqrt_two {s β g si kk q : ℝ} (hβ0 : 0 ≤ β) (hg : 0 ≤ g)
    (hsi : 0 ≤ si) (hkk : 0 ≤ kk) (hs : 0 ≤ s) (hX : 1 ≤ s * (g * kk * si)) (hq : q ≤ β / 64) :
    √2 * (g * (β + (s + β) * β / 16) * kk * si) + q ≤
      3 / 2 * ((1 + 2 * β + s / 8) * (g * kk * si)) * β := by
  have hX0 : 0 ≤ g * kk * si := mul_nonneg (mul_nonneg hg hkk) hsi
  have h2 : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hY : 0 ≤ g * (β + (s + β) * β / 16) * kk * si := by
    have : 0 ≤ β + (s + β) * β / 16 := by positivity
    have := mul_nonneg this hX0
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right h2 hY
  nlinarith [mul_nonneg hβ0 hX0, mul_nonneg (mul_nonneg hβ0 hβ0) hX0, mul_nonneg hs hX0]

/-- **Deterministic accuracy of randomized deflation, sharp constants** (DF2'): under the
hypotheses of `NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le`
with the precision condition strengthened to $16(4\mu_{\mathrm{QR}}(n) + 4\sqrt n\,c_{\mathrm N} +
2\mu_{\mathrm{MM}}(n))u \le \beta$, the factor
$m = (1 + 2\beta + \|\mathbf{S}\|_2/8)\|\mathbf{S}^{-1}\|_2\|\mathbf{G}\|_2
\|(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)^{-1}\|_2$ and $m\beta \le 1/64$, there is a unitary
$\mathbf{W}$ with $\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le
\tfrac32 m\beta$. [Shah2024, Theorem 3.3].
Proof: DF2's proof up to the bound $\|\mathbf{U} - \mathbf{Q}'_1\mathbf{C}\|_2 \le \delta$, where
the perturbation of $\mathbf{M}_1 = \mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf H}\mathbf{G}_1$ is
$\beta\|\mathbf{G}\|_2(1 + \beta)$ from $\widetilde{\mathbf{A}}$ plus the sampler, product and QR
roundings, at most $(\|\mathbf{S}\|_2 + \beta)\beta\|\mathbf{G}\|_2/16$ by the strengthened
condition, so $\delta \le m\beta$; then DF1' in place of DF1 ($\sqrt2\delta$). DF2's helper
`deflate_arith_one_le` ($1 \le m$) does not carry over, since now only $m \ge 1/8$: absorb the QR
orthogonality error $\mu_{\mathrm{QR}}u \le \beta/64$ through
$\|\mathbf S\|_2\|\mathbf S^{-1}\|_2 \ge 1$ and
$\|\mathbf G\|_2\|(\mathbf V^{\mathsf H}\mathbf G_1)^{-1}\|_2 \ge 1$; $\beta \le 1/8$ (from
$m\beta \le 1/64$)
replaces DF2's $\beta \le 1/5$. L, about 200 lines (DF2's
helpers reused). -/
theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β mval : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hμM : 0 ≤ μM n) (hu₀ : 0 ≤ u) (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A G : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β)
    (hG : IsUnit (Vᴴ * G.submatrix id (Fin.castLE hr)))
    (hm : mval = (1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * specNorm G *
      specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹)
    (hmβ : mval * β ≤ 1 / 64) (hu : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β)
    (hτ : τ ≤ specNorm S * specNorm G) (hτN : τ * √(n : ℝ) ≤ specNorm G)
    (hΩ : 2 * (specNorm S + β) * specNorm G ≤ Ω) (hΩG : specNorm G ≤ Ω) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' G)) ≤ 3 / 2 * mval * β := by
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
  set K := Vᴴ * G.submatrix id (Fin.castLE hr) with hK_def
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
  have hKG : specNorm K ≤ g := (hV.specNorm_conjTranspose_mul_le _).trans
    (specNorm_submatrix_le G Function.injective_id (Fin.castLE_injective hr))
  have hgk : 1 ≤ g * kk := by
    calc (1 : ℝ) = specNorm (K * K⁻¹) := by rw [Matrix.mul_nonsing_inv K hKdet, specNorm_one]
      _ ≤ specNorm K * kk := specNorm_mul_le _ _
      _ ≤ g * kk := mul_le_mul_of_nonneg_right hKG hkk0
  have hmv : mval = (1 + 2 * β + s / 8) * (g * kk * si) := by rw [hm]; ring
  have hX0 : 0 ≤ g * kk * si := mul_nonneg (mul_nonneg hg0 hkk0) hsi0
  have hX : 1 ≤ s * (g * kk * si) := by
    have h := mul_le_mul hssi hgk zero_le_one (mul_nonneg hs0 hsi0)
    nlinarith
  have hβ8 : β ≤ 1 / 8 := by
    have : 1 / 8 ≤ mval := by rw [hmv]; nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + 2 * β) hX0]
    nlinarith
  have hgne : g ≠ 0 := by intro h; rw [h, zero_mul] at hgk; linarith
  have hcu : 0 ≤ cN * u :=
    hM.normalConst_mul_nonneg (fun h => hgne (by rw [hg_def, h, specNorm_zero])) hΩG
  have hq0 := hM.qrConst_mul_nonneg n (hg0.trans hΩG)
  have hq64 : μQ n * u ≤ β / 64 := by
    have hc0 := mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hcu
    have ha0 := mul_nonneg hμM hu₀
    have : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u =
        64 * (μQ n * u) + 64 * (√(n : ℝ) * (cN * u)) + 32 * (μM n * u) := by ring
    linarith
  have hAle : specNorm A ≤ s := by
    rw [hA]
    calc specNorm (U * S * Vᴴ) ≤ specNorm (U * S) * specNorm Vᴴ := specNorm_mul_le _ _
      _ = s * specNorm V := by rw [hU.specNorm_mul_left, specNorm_conjTranspose]
      _ ≤ s * 1 := mul_le_mul_of_nonneg_left hV.specNorm_le_one hs0
      _ = s := mul_one s
  obtain ⟨Q', R, hQ', hR, hQQ, hT⟩ := hM.exists_specNorm_mul_sub_mul_qr_le_of_mul_le hs0 hβ0
    hβ8 hAle hβ hcu hq0 (mul_nonneg hμM hu₀) hu hτ hτN hΩ hΩG
  obtain ⟨W, hW, hUW⟩ := exists_hasOrthonormalCols_specNorm_mul_sub_submatrix_le_sqrt_two_mul hr
    hU hS hA hG hQ' hR hQQ le_rfl
  refine ⟨W, hW, ?_⟩
  rw [decodeMatrix_deflate M dec hr A' G]
  refine hUW.trans (le_trans ?_ ((deflate_arith_sqrt_two hβ0 hg0 hsi0 hkk0 hs0 hX hq64).trans
    (by rw [hmv])))
  gcongr

end NLAlib
