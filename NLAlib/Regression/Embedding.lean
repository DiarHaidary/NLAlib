/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Matrix.ColumnRowPartitioned
public import NLAlib.Sketching.Properties.SubspaceEmbedding
public import NLAlib.Matrix.Pseudoinverse.LeastSquares
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Pseudoinverse.NormBounds
public import NLAlib.Matrix.Factorizations.QR

/-!
# Sketched least squares

The deterministic consequences of a subspace embedding or injection for least squares. If
$\mathbf{S}$ is a subspace embedding with constants $a$, $b$ for a subspace containing
$\operatorname{range}\mathbf{A}$ and $\mathbf{y}$, every minimizer $\mathbf{x}$ of the sketched
problem $\|\mathbf{S}\mathbf{A}\mathbf{x} - \mathbf{S}\mathbf{y}\|$ has residual within $b / a$
(squared) of the optimal residual $(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}$
(sketch-and-solve). If $\mathbf{S}$ embeds $\operatorname{range}\mathbf{A}$ and
$\mathbf{S}\mathbf{A}\mathbf{M}$ has orthonormal columns (QR's $\mathbf{R}^{-1}$, SVD's
$\mathbf{V}\mathbf{\Sigma}^{-1}$), then $\mathbf{A}\mathbf{M}$ has pseudo-condition number
$\|\mathbf{A}\mathbf{M}\|_2 \|(\mathbf{A}\mathbf{M})^{+}\|_2$ (`NLAlib.pseudoConditionNumber`) at
most $\sqrt{b / a}$ (sketch-and-precondition).

The injection alone controls the error of the sketched solution against the sketched residual
(CEMT's Lemma 2.6), for a vector and for a matrix right-hand side, and gives the deterministic
half of CEMT's Lemma 2.1. These are what the tail bounds for oblivious subspace injections in
`NLAlib.Regression.Oblivious` use.

## Main results

* `NLAlib.IsSubspaceEmbedding.norm_sub_mulVec_sq_le`: sketch-and-solve.
* `NLAlib.IsSubspaceEmbedding.pseudoConditionNumber_mul_sq_le`: sketch-and-precondition.
* `NLAlib.IsSubspaceEmbedding.spectrum_pinv_mul_subset_Icc`: its spectral form, the spectrum
  of the sketch-preconditioned normal equations, used by `NLAlib.sketchAndPrecondition`.
* `NLAlib.IsSubspaceInjection.norm_sub_mulVec_sq_le`: the sketch-and-solve error formula.
* `NLAlib.IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le`: its matrix form.
* `NLAlib.IsSubspaceInjection.frobNorm_mul_pinv_sq_le`: the deterministic half of CEMT
  Lemma 2.1.
-/

@[expose] public section

open scoped Matrix MatrixOrder ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {k l n p q r : Type*} [Fintype k] [Fintype l] [Fintype n]
  [Fintype p] [Fintype q] {S : Matrix k n 𝕜} {U : Matrix n p 𝕜}
  {A : Matrix n q 𝕜} {y : n → 𝕜} {x : q → 𝕜} {a b : ℝ}

/-! ### Sketch-and-solve -/

section LeastSquares

variable [DecidableEq n]

/-- **Sketch-and-solve.** If $\mathbf{S}$ is a subspace embedding with constants $a > 0$, $b$ for
a subspace $\operatorname{range}\mathbf{U}$ containing $\operatorname{range}\mathbf{A}$ and
$\mathbf{y}$, every minimizer $\mathbf{x}$ of
$\|\mathbf{S}\mathbf{A}\mathbf{x} - \mathbf{S}\mathbf{y}\|$ satisfies
$$\|\mathbf{y} - \mathbf{A}\mathbf{x}\|^2
\le \frac{b}{a} \|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2,$$
the last being the optimal residual.
[Woodruff2014, proof of Theorem 21], there $(1 + \varepsilon) / (1 - \varepsilon)$ in squared
norms; [MartinssonTropp2020, §10.3], there
$\|\mathbf{A}\hat{\mathbf{x}} - \mathbf{b}\| \le (1 + \varepsilon) \|\mathbf{A}\mathbf{x}_\star -
\mathbf{b}\|$, unsquared (after Sarlós). Here any constants and any subspace containing
$\operatorname{range}\mathbf{A}$ and $\mathbf{y}$.
Result: sketch-and-solve-ls -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_sq_le (h : IsSubspaceEmbedding S U a b) (ha : 0 < a)
    (hA : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hy : y ∈ LinearMap.range U.mulVecLin) (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ^ 2 ≤
      b / a * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 := by
  obtain ⟨x₀, hx₀⟩ := exists_isLeastSquaresSolution A y
  have hAx : ∀ z, A *ᵥ z ∈ LinearMap.range U.mulVecLin := fun z => hA ⟨z, rfl⟩
  have hv := isSubspaceEmbedding_iff_forall_mem_range.mp h
  have h₁ := (hv _ (sub_mem hy (hAx x))).1
  have h₂ := (hv _ (sub_mem hy (hAx x₀))).2
  have h₃ : ‖WithLp.toLp 2 (S *ᵥ (y - A *ᵥ x))‖ ^ 2 ≤ ‖WithLp.toLp 2 (S *ᵥ (y - A *ᵥ x₀))‖ ^ 2 := by
    have := hx x₀
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub,
      ← Matrix.mulVec_sub] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  rw [hx₀.sub_mulVec_eq] at h₂ h₃
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀' ha).2 (h₁.trans (h₃.trans h₂))

/-- **Sketch-and-solve**, unsquared:
$\|\mathbf{y} - \mathbf{A}\mathbf{x}\|
\le \sqrt{b / a}\, \|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|$.
[MartinssonTropp2020, §10.3], unsquared there. -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_le (h : IsSubspaceEmbedding S U a b) (ha : 0 < a)
    (hA : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hy : y ∈ LinearMap.range U.mulVecLin) (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ≤ √(b / a) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ := by
  calc ‖WithLp.toLp 2 (y - A *ᵥ x)‖ = √(‖WithLp.toLp 2 (y - A *ᵥ x)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(b / a * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2) :=
        Real.sqrt_le_sqrt (h.norm_sub_mulVec_sq_le ha hA hy hx)
    _ = √(b / a) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ := by
        rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- **Sketch-and-solve** with an embedding of $\operatorname{range}[\mathbf{A}, \mathbf{y}]$, the
form in which the literature states it. [Woodruff2014, proof of Theorem 21]. -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_sq_le_of_fromCols
    (h : IsSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y)) a b) (ha : 0 < a)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ^ 2 ≤
      b / a * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 := by
  exact h.norm_sub_mulVec_sq_le ha (Matrix.range_le_range_fromCols_left A _)
    (Matrix.mem_range_fromCols_replicateCol A y) hx

end LeastSquares

/-! ### Sketch-and-precondition -/

/-- Sketch-and-precondition, lower half of the spectral equivalence: if $\mathbf{S}$ embeds
$\operatorname{range}\mathbf{A}$ with upper constant $b > 0$ and $\mathbf{S}\mathbf{A}\mathbf{M}$
has orthonormal columns, then
$b^{-1}\mathbf{I} \preceq (\mathbf{A}\mathbf{M})^{\mathsf{H}}\mathbf{A}\mathbf{M}$. Any such
$\mathbf{M}$ (QR's $\mathbf{R}^{-1}$, SVD's $\mathbf{V}\mathbf{\Sigma}^{-1}$, Cholesky-QR)
qualifies. -/
theorem IsSubspaceEmbedding.inv_smul_one_le_conjTranspose_mul_self [DecidableEq r]
    {M : Matrix q r 𝕜} (h : IsSubspaceEmbedding S A a b) (hb : 0 < b)
    (hM : HasOrthonormalCols (S * A * M)) : b⁻¹ • (1 : Matrix r r 𝕜) ≤ (A * M)ᴴ * (A * M) := by
  have hup := (h.mul_right M).upper
  rw [← Matrix.mul_assoc S A M, hM.conjTranspose_mul_self] at hup
  have h' := smul_le_smul_of_nonneg hup (inv_nonneg.mpr hb.le)
  rwa [smul_smul, inv_mul_cancel₀ hb.ne', one_smul] at h'

/-- Sketch-and-precondition, upper half of the spectral equivalence: if $\mathbf{S}$ embeds
$\operatorname{range}\mathbf{A}$ with lower constant $a > 0$ and $\mathbf{S}\mathbf{A}\mathbf{M}$
has orthonormal columns, then
$(\mathbf{A}\mathbf{M})^{\mathsf{H}}\mathbf{A}\mathbf{M} \preceq a^{-1}\mathbf{I}$. -/
theorem IsSubspaceEmbedding.conjTranspose_mul_self_le_inv_smul_one [DecidableEq r]
    {M : Matrix q r 𝕜} (h : IsSubspaceEmbedding S A a b) (ha : 0 < a)
    (hM : HasOrthonormalCols (S * A * M)) : (A * M)ᴴ * (A * M) ≤ a⁻¹ • (1 : Matrix r r 𝕜) := by
  have hlow : a • ((A * M)ᴴ * (A * M)) ≤ (S * (A * M))ᴴ * (S * (A * M)) := (h.mul_right M).lower
  rw [← Matrix.mul_assoc S A M, hM.conjTranspose_mul_self] at hlow
  have h' := smul_le_smul_of_nonneg hlow (inv_nonneg.mpr ha.le)
  rwa [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h'

/-- **Sketch-and-precondition**: if $\mathbf{S}$ embeds $\operatorname{range}\mathbf{A}$ with
constants $a > 0$, $b \ge 0$ and $\mathbf{S}\mathbf{A}\mathbf{M}$ has orthonormal columns, the
preconditioned matrix has pseudo-condition number (`NLAlib.pseudoConditionNumber`)
$$\bigl(\|\mathbf{A}\mathbf{M}\|_2 \|(\mathbf{A}\mathbf{M})^{+}\|_2\bigr)^2 \le \frac{b}{a}\,.$$
For empty $r$ (the column index of $\mathbf{M}$) the pseudo-condition number is $0$ and the bound
is the hypothesis $0 \le b$; for nonempty $r$ the hypotheses force $0 < b$. No rank hypothesis is
needed:
$\mathbf{A}\mathbf{M}$ has full column rank because $\mathbf{S}\mathbf{A}\mathbf{M}$ does, so the
pseudo-condition number is the classical
$\sigma_0(\mathbf{A}\mathbf{M}) / \sigma_{\min}(\mathbf{A}\mathbf{M})$
(`NLAlib.pseudoConditionNumber_of_injective`). [MartinssonTropp2020, §10.5]; there for
$\mathbf{M} = \mathbf{R}^{-1}$ from a QR factorization of $\mathbf{S}\mathbf{A}$.
Result: sketch-and-precondition -/
theorem IsSubspaceEmbedding.pseudoConditionNumber_mul_sq_le [Fintype r] [DecidableEq r]
    {M : Matrix q r 𝕜} (h : IsSubspaceEmbedding S A a b) (ha : 0 < a) (hb : 0 ≤ b)
    (hM : HasOrthonormalCols (S * A * M)) : pseudoConditionNumber (A * M) ^ 2 ≤ b / a := by
  rcases isEmpty_or_nonempty r with hr | hr
  · rw [Subsingleton.elim (A * M) 0, pseudoConditionNumber_zero]
    simpa using div_nonneg hb ha.le
  · have hb₀ : 0 < b := by
      rcases hb.lt_or_eq with hb₀ | rfl
      · exact hb₀
      exfalso
      have hup := (h.mul_right M).upper
      rw [← Matrix.mul_assoc S A M, hM.conjTranspose_mul_self, zero_smul] at hup
      have h₁ : (1 : ℝ) • (1 : Matrix r r 𝕜) ≤ (0 : ℝ) • (1 : Matrix r r 𝕜) := by
        rwa [one_smul, zero_smul]
      exact absurd (smul_one_le_smul_one_iff.mp h₁) (by norm_num)
    rw [← inv_div_inv]
    exact pseudoConditionNumber_sq_le_div_of_smul_one_le_of_le_smul_one (inv_pos.mpr hb₀)
      (inv_nonneg.mpr ha.le) (h.inv_smul_one_le_conjTranspose_mul_self hb₀ hM)
      (h.conjTranspose_mul_self_le_inv_smul_one ha hM)

/-- **Sketch-and-precondition with QR**: if $\mathbf{S}$ embeds $\operatorname{range}\mathbf{A}$
with constants $a > 0$, $b \ge 0$, then for a thin QR factorization
$\mathbf{S}\mathbf{A} = \mathbf{Q}\mathbf{R}$ with $\mathbf{R}$ invertible the pseudo-condition
number (`NLAlib.pseudoConditionNumber`) satisfies
$$\bigl(\|\mathbf{A}\mathbf{R}^{-1}\|_2 \|(\mathbf{A}\mathbf{R}^{-1})^{+}\|_2\bigr)^2
\le \frac{b}{a}\,.$$
[MartinssonTropp2020, §10.5]. -/
theorem IsSubspaceEmbedding.pseudoConditionNumber_mul_inv_sq_le_of_isQR [LinearOrder q]
    [DecidableEq q] {Q : Matrix k q 𝕜} {R : Matrix q q 𝕜} (h : IsSubspaceEmbedding S A a b)
    (ha : 0 < a) (hb : 0 ≤ b) (hQR : IsQR (S * A) Q R) (hR : IsUnit R) :
    pseudoConditionNumber (A * R⁻¹) ^ 2 ≤ b / a := by
  refine h.pseudoConditionNumber_mul_sq_le ha hb ?_
  rw [hQR.mul_inv_eq hR]
  exact hQR.hasOrthonormalCols

/-- **Sketch-and-precondition, spectral form**: if $\mathbf{S}$ is a subspace embedding of
$\operatorname{range}\mathbf{A}$ with constants $a > 0$, $b$ (squared norms,
$a\|\mathbf{y}\|^2 \le \|\mathbf{S}\mathbf{y}\|^2 \le b\|\mathbf{y}\|^2$ on the range) and
$\mathbf{A}$ has full column rank, then with
$\mathbf{G} = (\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A}$ the real spectrum of
$\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}\mathbf{A}$ lies in $[b^{-1}, a^{-1}]$: the preconditioned
normal equations have condition number at most $b/a$. [Epperly2024, Fact 3], there as singular
values of $\mathbf{A}\mathbf{R}^{-1}$ in the unsquared convention
$(1 - \eta)\|\mathbf{y}\| \le \|\mathbf{S}\mathbf{y}\| \le (1 + \eta)\|\mathbf{y}\|$, the
case $a = (1 - \eta)^2$, $b = (1 + \eta)^2$. -/
theorem IsSubspaceEmbedding.spectrum_pinv_mul_subset_Icc [DecidableEq q]
    (h : IsSubspaceEmbedding S A a b) (ha : 0 < a) (hA : Function.Injective A.mulVec) :
    spectrum ℝ (pinv ((S * A)ᴴ * (S * A)) * (Aᴴ * A)) ⊆ Set.Icc b⁻¹ a⁻¹ := by
  rcases isEmpty_or_nonempty q with hq | hq
  · rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  have hb := h.pos_right_of_injective ha hA
  have hG : ((S * A)ᴴ * (S * A)).PosDef :=
    posDef_conjTranspose_mul_self_iff.mpr (h.lower.injective_mulVec ha hA)
  rw [pinv_of_isUnit hG.isUnit]
  refine (hG.smul_le_and_le_smul_iff_spectrum_subset (Matrix.isHermitian_conjTranspose_mul_self A)
    _ _).mp ⟨?_, ?_⟩
  · have h' := smul_le_smul_of_nonneg_left h.upper (inv_nonneg.mpr hb.le)
    rwa [smul_smul, inv_mul_cancel₀ hb.ne', one_smul] at h'
  · have hlow : a • (Aᴴ * A) ≤ (S * A)ᴴ * (S * A) := h.lower
    have h' := smul_le_smul_of_nonneg_left hlow (inv_nonneg.mpr ha.le)
    rwa [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h'

/-! ### The error formula, from the injection alone -/

section ErrorFormula

variable [DecidableEq n]

/-- The error of a sketched solution against the optimal fit, from the injection alone: for a
subspace injection for $\operatorname{range}\mathbf{A}$ with constant $a > 0$,
$$\|\mathbf{A}\mathbf{x} - \mathbf{P}_{\mathbf{A}}\mathbf{y}\|^2
\le \frac{\|\mathbf{S}(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2}{a}$$
for every minimizer $\mathbf{x}$ of $\|\mathbf{S}\mathbf{A}\mathbf{x} - \mathbf{S}\mathbf{y}\|$.
[CamanoEpperlyMeyerTropp2025, Lemma 2.6]; there an identity for the minimum-norm solution, here
a bound in norm for every minimizer. -/
theorem IsSubspaceInjection.norm_mulVec_sub_rangeProjector_mulVec_sq_le
    (h : IsSubspaceInjection S A a) (ha : 0 < a)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (A *ᵥ x - rangeProjector A *ᵥ y)‖ ^ 2 ≤
      ‖WithLp.toLp 2 (S *ᵥ ((1 - rangeProjector A) *ᵥ y))‖ ^ 2 / a := by
  obtain ⟨x₀, hx₀⟩ := exists_isLeastSquaresSolution A y
  have hw : A *ᵥ x - rangeProjector A *ᵥ y = A *ᵥ (x - x₀) := by
    rw [← hx₀.mulVec_eq_rangeProjector_mulVec, Matrix.mulVec_sub]
  have hpy := hx.norm_sub_mulVec_sq_eq_add x₀
  have e₁ : S *ᵥ y - (S * A) *ᵥ x₀ = S *ᵥ ((1 - rangeProjector A) *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, hx₀.sub_mulVec_eq]
  have e₂ : (S * A) *ᵥ (x - x₀) = S *ᵥ (A *ᵥ x - rangeProjector A *ᵥ y) := by
    rw [hw, Matrix.mulVec_mulVec]
  rw [e₁, e₂] at hpy
  have hinj := isSubspaceInjection_iff_forall_mem_range.mp h _ ⟨x - x₀, hw.symm⟩
  refine (le_div_iff₀' ha).2 (hinj.trans ?_)
  rw [hpy]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- **Sketch-and-solve error formula**: for a subspace injection for
$\operatorname{range}\mathbf{A}$ with constant $a > 0$ and every minimizer $\mathbf{x}$ of
$\|\mathbf{S}\mathbf{A}\mathbf{x} - \mathbf{S}\mathbf{y}\|$,
$$\|\mathbf{y} - \mathbf{A}\mathbf{x}\|^2
\le \|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 +
\frac{\|\mathbf{S}(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2}{a}\,.$$
[CamanoEpperlyMeyerTropp2025, Lemma 2.6, proof of Theorem 2.7]; there an identity for the
minimum-norm solution, here a bound for every minimizer. -/
theorem IsSubspaceInjection.norm_sub_mulVec_sq_le (h : IsSubspaceInjection S A a) (ha : 0 < a)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ^ 2 ≤ ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 +
      ‖WithLp.toLp 2 (S *ᵥ ((1 - rangeProjector A) *ᵥ y))‖ ^ 2 / a := by
  obtain ⟨x₀, hx₀⟩ := exists_isLeastSquaresSolution A y
  have hpy := hx₀.norm_sub_mulVec_sq_eq_add x
  have e : A *ᵥ (x₀ - x) = -(A *ᵥ x - rangeProjector A *ᵥ y) := by
    rw [Matrix.mulVec_sub, hx₀.mulVec_eq_rangeProjector_mulVec, neg_sub]
  rw [hx₀.sub_mulVec_eq, e, WithLp.toLp_neg, norm_neg] at hpy
  rw [hpy]
  exact add_le_add_right (h.norm_mulVec_sub_rangeProjector_mulVec_sq_le ha hx) _

/-- **Sketch-and-solve error formula, matrix right-hand side**, for the minimum-norm output
$(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{Y}$, as generalized Nyström uses it: for a subspace
injection for $\operatorname{range}\mathbf{A}$ with constant $a > 0$,
$$\|\mathbf{Y} - \mathbf{A}(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{Y}\|_{\mathsf{F}}^2
\le \|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{Y}\|_{\mathsf{F}}^2 +
\frac{\|\mathbf{S}(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{Y}\|_{\mathsf{F}}^2}{a}\,.$$
[CamanoEpperlyMeyerTropp2025, Lemma 2.6, proof of Theorem 2.7]; there an identity. -/
theorem IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le [Fintype r]
    (h : IsSubspaceInjection S A a) (ha : 0 < a) (Y : Matrix n r 𝕜) :
    frobNorm (Y - A * (pinv (S * A) * (S * Y))) ^ 2 ≤
      frobNorm ((1 - rangeProjector A) * Y) ^ 2 +
        frobNorm (S * ((1 - rangeProjector A) * Y)) ^ 2 / a := by
  rw [frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, Finset.sum_div,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  exact h.norm_sub_mulVec_sq_le ha (isLeastSquaresSolution_pinv_mulVec (S * A) (S *ᵥ Y.col j))

end ErrorFormula

/-- **Deterministic half of CEMT Lemma 2.1**: for $\mathbf{U}$ with orthonormal columns and a
subspace injection for $\operatorname{range}\mathbf{U}$ with constant $a > 0$,
$$\bigl\|\mathbf{X}((\mathbf{S}\mathbf{U})^{\mathsf{H}})^{+}\bigr\|_{\mathsf{F}}^2
\le \frac{\|\mathbf{X}\|_{\mathsf{F}}^2}{a}\,.$$
CEMT apply it at $\mathbf{X} = \mathbf{B}(\mathbf{S}\mathbf{Q}_\perp)^{\mathsf{H}}$.
[CamanoEpperlyMeyerTropp2025, proof of Lemma 2.1]. -/
theorem IsSubspaceInjection.frobNorm_mul_pinv_sq_le [DecidableEq p]
    (h : IsSubspaceInjection S U a) (hU : HasOrthonormalCols U) (ha : 0 < a)
    (X : Matrix l k 𝕜) : frobNorm (X * pinv ((S * U)ᴴ)) ^ 2 ≤ frobNorm X ^ 2 / a := by
  have hp := specNorm_pinv_sq_le_inv_of_smul_one_le ha (hU.isSubspaceInjection_iff.mp h)
  rw [div_eq_mul_inv]
  calc frobNorm (X * pinv ((S * U)ᴴ)) ^ 2 ≤ (frobNorm X * specNorm (pinv ((S * U)ᴴ))) ^ 2 :=
        pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_mul_le_frobNorm_mul_specNorm _ _) 2
    _ = frobNorm X ^ 2 * specNorm (pinv (S * U)) ^ 2 := by
        rw [pinv_conjTranspose, specNorm_conjTranspose, mul_pow]
    _ ≤ frobNorm X ^ 2 * a⁻¹ := mul_le_mul_of_nonneg_left hp (sq_nonneg _)

/-! ### Deprecated aliases -/

@[deprecated IsSubspaceEmbedding.pseudoConditionNumber_mul_sq_le (since := "2026-10-14")]
alias IsSubspaceEmbedding.conditionNumber_mul_sq_le :=
  IsSubspaceEmbedding.pseudoConditionNumber_mul_sq_le

@[deprecated (since := "2026-10-14")]
alias IsSubspaceEmbedding.conditionNumber_mul_inv_sq_le_of_isQR :=
  IsSubspaceEmbedding.pseudoConditionNumber_mul_inv_sq_le_of_isQR

end NLAlib
