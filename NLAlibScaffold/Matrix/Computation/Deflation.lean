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
