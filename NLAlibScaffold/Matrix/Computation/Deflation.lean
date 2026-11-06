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
  sorry

end NLAlib
