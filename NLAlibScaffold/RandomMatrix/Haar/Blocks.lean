/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Haar.Blocks
public import NLAlib.RandomMatrix.UnitaryInvariance
public import NLAlibScaffold.Matrix.Pseudoinverse.NormBounds

/-!
# The random orthonormal sketching inequality with a weight (stage S10)

Epperly and Webber's Proposition 5.7 for a general invertible weight $\mathbf{R}$: the Haar block
moment `NLAlib.integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame` (the case
$\mathbf{R} = \mathbf{I}$, an equality) becomes a lower bound. It joins
`NLAlib/RandomMatrix/Haar/Blocks.lean`; its proof is deferred. Design:
`docs/design/LowRank-EstimatorLowerBounds.md` §3.3.

## Main results

* `NLAlib.mul_le_integral_frobNorm_pinv_conjTranspose_mul_mul_sq_of_hasLaw_haarFrame`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m p r s a : Type*} [Fintype m]
  [Fintype p] [Fintype r] [Fintype s] [Fintype a] {Q : Ω → Matrix m p ℝ}

/-- The weighted factor $G(\mathbf{x}) = (\mathbf{R}^{\mathsf{H}}\mathbf{x}^{\mathsf{H}})^{+}
\mathbf{R}^{\mathsf{H}}$ of the weighted sketching inequality. -/
private noncomputable def weightedFactor (R : Matrix p p ℝ) (x : Matrix r p ℝ) : Matrix r p ℝ :=
  pinv (Rᴴ * xᴴ) * Rᴴ

private theorem measurable_weightedFactor_gram (R : Matrix p p ℝ) :
    Measurable fun x : Matrix r p ℝ => (weightedFactor R x)ᴴ * weightedFactor R x := by
  have hT : Measurable fun x : Matrix r p ℝ => xᴴ := continuous_id.matrix_conjTranspose.measurable
  have hG : Measurable (weightedFactor (r := r) R) :=
    (measurable_pinv.comp (measurable_const.matrix_mul hT)).matrix_mul measurable_const
  exact (continuous_id.matrix_conjTranspose.measurable.comp hG).matrix_mul hG

/-- The squared norm in the weighted inequality as a trace against the conjugated Gram matrix of
the weighted factor. -/
private theorem frobNorm_pinv_conjTranspose_mul_mul_sq_eq_trace (R : Matrix p p ℝ)
    (Q₀ : Matrix m p ℝ) (V₁ : Matrix m r ℝ) (V₂ : Matrix m s ℝ) (B : Matrix s a ℝ) :
    frobNorm (pinv (Rᴴ * (Q₀ᴴ * V₁)) * (Rᴴ * (Q₀ᴴ * V₂)) * B) ^ 2 =
      (V₂ᴴ * Q₀ * ((weightedFactor R (V₁ᴴ * Q₀))ᴴ * weightedFactor R (V₁ᴴ * Q₀)) *
        (V₂ᴴ * Q₀)ᴴ * (B * Bᴴ)).trace := by
  have h1 : (V₁ᴴ * Q₀)ᴴ = Q₀ᴴ * V₁ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h2 : (V₂ᴴ * Q₀)ᴴ = Q₀ᴴ * V₂ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [frobNorm_sq_eq_re_trace, RCLike.re_to_real]
  have e : (pinv (Rᴴ * (Q₀ᴴ * V₁)) * (Rᴴ * (Q₀ᴴ * V₂)) * B)ᴴ *
      (pinv (Rᴴ * (Q₀ᴴ * V₁)) * (Rᴴ * (Q₀ᴴ * V₂)) * B) =
      Bᴴ * (V₂ᴴ * Q₀ * ((weightedFactor R (V₁ᴴ * Q₀))ᴴ * weightedFactor R (V₁ᴴ * Q₀)) *
        (V₂ᴴ * Q₀)ᴴ * B) := by
    rw [weightedFactor, h1, h2]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- The trace of the conjugated Gram matrix, on the event that $\mathbf{Q}$ has orthonormal
columns and $\mathbf{R}^{\mathsf{H}}\mathbf{Q}^{\mathsf{H}}\mathbf{V}_1$ has full column rank. -/
private theorem trace_conj_weightedFactor_gram_eq [DecidableEq m] [DecidableEq p]
    (R : Matrix p p ℝ) {Q₀ : Matrix m p ℝ} (hQ₀ : HasOrthonormalCols Q₀) {V₁ : Matrix m r ℝ}
    {V₂ : Matrix m s ℝ} (hVV : V₁ * V₁ᴴ + V₂ * V₂ᴴ = 1)
    (hinj : Function.Injective (Rᴴ * (Q₀ᴴ * V₁)).mulVec) :
    (V₂ᴴ * Q₀ * ((weightedFactor R (V₁ᴴ * Q₀))ᴴ * weightedFactor R (V₁ᴴ * Q₀)) *
        (V₂ᴴ * Q₀)ᴴ).trace =
      frobNorm (weightedFactor R (V₁ᴴ * Q₀)) ^ 2 - Fintype.card r := by
  classical
  have h1 : (V₁ᴴ * Q₀)ᴴ = Q₀ᴴ * V₁ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  set G := weightedFactor R (V₁ᴴ * Q₀) with hGdef
  have hL : G * (V₁ᴴ * Q₀)ᴴ = 1 := by
    rw [hGdef, weightedFactor, Matrix.mul_assoc, h1]
    exact pinv_mul_self_of_injective hinj
  have hG : (V₂ᴴ * Q₀)ᴴ * (V₂ᴴ * Q₀) = 1 - (V₁ᴴ * Q₀)ᴴ * (V₁ᴴ * Q₀) := by
    have e : Q₀ᴴ * (V₁ * V₁ᴴ + V₂ * V₂ᴴ) * Q₀ = 1 := by
      rw [hVV, Matrix.mul_one, hQ₀.conjTranspose_mul_self]
    rw [eq_sub_iff_add_eq, ← e]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
    abel
  have hr : (Gᴴ * G * ((V₁ᴴ * Q₀)ᴴ * (V₁ᴴ * Q₀))).trace = Fintype.card r := by
    rw [show Gᴴ * G * ((V₁ᴴ * Q₀)ᴴ * (V₁ᴴ * Q₀)) = Gᴴ * (G * (V₁ᴴ * Q₀)ᴴ) * (V₁ᴴ * Q₀) by
        simp only [Matrix.mul_assoc], hL, Matrix.mul_one, Matrix.trace_mul_comm,
      show V₁ᴴ * Q₀ * Gᴴ = (G * (V₁ᴴ * Q₀)ᴴ)ᴴ by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose], hL,
      Matrix.conjTranspose_one, Matrix.trace_one]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hG, Matrix.mul_sub,
    Matrix.mul_one, Matrix.trace_sub, hr, frobNorm_sq_eq_re_trace, RCLike.re_to_real]

/-- Multiplying by an invertible $\mathbf{R}^{\mathsf{H}}$ keeps full column rank. -/
private theorem injective_mulVec_conjTranspose_mul [DecidableEq p] {R : Matrix p p ℝ}
    (hR : IsUnit R) {M : Matrix p r ℝ} (hM : Function.Injective M.mulVec) :
    Function.Injective (Rᴴ * M).mulVec := by
  classical
  have e : (Rᴴ * M).mulVec = Rᴴ.mulVec ∘ M.mulVec := by
    funext v; simp only [Function.comp_apply, Matrix.mulVec_mulVec]
  rw [e]
  exact (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_conjTranspose R).mpr hR)).comp hM

/-- With $\mathbf{x}^{\mathsf{H}}$ of full column rank, $\|G(\mathbf{x})\|_{\mathsf{F}} \le
\|(\mathbf{x}^{\mathsf{H}})^{+}\|_{\mathsf{F}}\|\mathbf{R}^{-\mathsf{H}}\|_2\|\mathbf{R}\|_2$:
$(\mathbf{x}^{\mathsf{H}})^{+}\mathbf{R}^{-\mathsf{H}}$ is a left inverse of
$\mathbf{R}^{\mathsf{H}}\mathbf{x}^{\mathsf{H}}$. -/
private theorem frobNorm_weightedFactor_le [DecidableEq p] {R : Matrix p p ℝ}
    (hR : IsUnit R) {x : Matrix r p ℝ} (hinj : Function.Injective xᴴ.mulVec) :
    frobNorm (weightedFactor R x) ≤ frobNorm (pinv xᴴ) * specNorm (Rᴴ)⁻¹ * specNorm R := by
  classical
  have hRT : IsUnit Rᴴ := (Matrix.isUnit_conjTranspose R).mpr hR
  have hX : pinv xᴴ * (Rᴴ)⁻¹ * (Rᴴ * xᴴ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Rᴴ)⁻¹, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp hRT), Matrix.one_mul]
    exact pinv_mul_self_of_injective hinj
  have hP : pinv (Rᴴ * xᴴ) = pinv xᴴ * (Rᴴ)⁻¹ * rangeProjector (Rᴴ * xᴴ) := by
    rw [← mul_pinv, ← Matrix.mul_assoc, hX, Matrix.one_mul]
  rw [weightedFactor, hP]
  refine (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans ?_
  rw [specNorm_conjTranspose]
  gcongr
  refine (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans ?_
  refine (mul_le_of_le_one_right (frobNorm_nonneg _)
    (isStarProjection_rangeProjector _).specNorm_le_one).trans ?_
  exact frobNorm_mul_le_frobNorm_mul_specNorm _ _

/-- Almost surely $\mathbf{Q}^{\mathsf{H}}\mathbf{V}_1$ has full column rank. -/
private theorem ae_injective_mulVec_conjTranspose_mul [DecidableEq p] [DecidableEq r]
    (hQ : HasLaw Q (haarFrame m p) μ) {V₁ : Matrix m r ℝ} (hV₁ : HasOrthonormalCols V₁)
    (hrp : Fintype.card r + 2 ≤ Fintype.card p) :
    ∀ᵐ ω ∂μ, Function.Injective ((Q ω)ᴴ * V₁).mulVec := by
  filter_upwards [ae_rank_mul_eq_min_of_hasLaw_haarFrame V₁ᴴ hQ] with ω hω
  rw [mulVec_injective_iff_rank_eq, show (Q ω)ᴴ * V₁ = (V₁ᴴ * Q ω)ᴴ by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose], Matrix.rank_conjTranspose,
    hω, Matrix.rank_conjTranspose, hV₁.rank_eq]
  omega

open scoped Matrix.Norms.L2Operator in
/-- The conjugated Gram matrix of the weighted factor is integrable: its norm is at most
$(\|\mathbf{R}^{-\mathsf{H}}\|_2\|\mathbf{R}\|_2)^2\|(\mathbf{V}_1^{\mathsf{H}}\mathbf{Q})^{+}
\|_{\mathsf{F}}^2$. -/
private theorem integrable_conj_weightedFactor_gram_of_hasLaw_haarFrame [DecidableEq p]
    [DecidableEq r] [DecidableEq s]
    (hQ : HasLaw Q (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)
    {V₁ : Matrix m r ℝ} {V₂ : Matrix m s ℝ} (hV₁ : HasOrthonormalCols V₁)
    (hV₂ : HasOrthonormalCols V₂) (hrp : Fintype.card r + 2 ≤ Fintype.card p)
    {R : Matrix p p ℝ} (hR : IsUnit R) :
    Integrable (fun ω => V₂ᴴ * Q ω * ((weightedFactor R (V₁ᴴ * Q ω))ᴴ *
      weightedFactor R (V₁ᴴ * Q ω)) * (V₂ᴴ * Q ω)ᴴ) μ := by
  classical
  have hW : HasOrthonormalCols (V₁ᴴ)ᴴ := by rwa [Matrix.conjTranspose_conjTranspose]
  have hpinv := integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame hQ hpm hW hrp
  set F := fun x : Matrix r p ℝ => (weightedFactor R x)ᴴ * weightedFactor R x
  have hZm : Measurable fun Q₀ : Matrix m p ℝ => V₂ᴴ * Q₀ * F (V₁ᴴ * Q₀) * (V₂ᴴ * Q₀)ᴴ :=
    (((measurable_const.matrix_mul measurable_id).matrix_mul
      ((measurable_weightedFactor_gram R).comp
        (measurable_const.matrix_mul measurable_id))).matrix_mul
      (continuous_id.matrix_conjTranspose.measurable.comp
        (measurable_const.matrix_mul measurable_id)))
  set C := (specNorm (Rᴴ)⁻¹ * specNorm R) ^ 2
  have hG : ∀ᵐ ω ∂μ, frobNorm (weightedFactor R (V₁ᴴ * Q ω)) ^ 2 ≤
      C * frobNorm (pinv (V₁ᴴ * Q ω)) ^ 2 := by
    filter_upwards [ae_injective_mulVec_conjTranspose_mul hQ hV₁ hrp] with ω hω
    have h := frobNorm_weightedFactor_le hR (x := V₁ᴴ * Q ω) (by
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose])
    rw [pinv_conjTranspose, frobNorm_conjTranspose] at h
    calc _ ≤ (frobNorm (pinv (V₁ᴴ * Q ω)) * specNorm (Rᴴ)⁻¹ * specNorm R) ^ 2 := by gcongr
      _ = _ := by ring
  refine Integrable.mono' (hpinv.const_mul C)
    (hZm.comp_aemeasurable hQ.aemeasurable).aestronglyMeasurable ?_
  filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hQ, hG] with ω hω hGω
  rw [← specNorm_eq_norm]
  have hY : specNorm (V₂ᴴ * Q ω) ≤ 1 := (hV₂.specNorm_conjTranspose_mul_le _).trans hω
  have hM : specNorm (F (V₁ᴴ * Q ω)) ≤ C * frobNorm (pinv (V₁ᴴ * Q ω)) ^ 2 := by
    refine (specNorm_mul_le _ _).trans (le_trans ?_ hGω)
    rw [specNorm_conjTranspose, ← sq]
    exact pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_le_frobNorm _) 2
  change specNorm (V₂ᴴ * Q ω * F (V₁ᴴ * Q ω) * (V₂ᴴ * Q ω)ᴴ) ≤ _
  calc specNorm (V₂ᴴ * Q ω * F (V₁ᴴ * Q ω) * (V₂ᴴ * Q ω)ᴴ)
      ≤ specNorm (V₂ᴴ * Q ω) * specNorm (F (V₁ᴴ * Q ω)) * specNorm (V₂ᴴ * Q ω) := by
        refine (specNorm_mul_le _ _).trans ?_
        rw [specNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
    _ ≤ 1 * (C * frobNorm (pinv (V₁ᴴ * Q ω)) ^ 2) * 1 := by gcongr
    _ = _ := by ring

/-- **A weight does not help a random orthonormal sketch** (Epperly and Webber's
Proposition 5.7): for an $m \times p$ Haar frame $\mathbf{Q}$ with $p \le m$, orthonormal
$\mathbf{V}_1 \in \mathbb{R}^{m \times r}$, $\mathbf{V}_2 \in \mathbb{R}^{m \times s}$ with
orthogonal
ranges and $r + s = m$, $r + 2 \le p$, any $\mathbf{B} \in \mathbb{R}^{s \times a}$ and any
invertible $\mathbf{R} \in \mathbb{R}^{p \times p}$,
$$\frac{m - p}{m - r}\cdot\frac{r}{p - r - 1}\,\|\mathbf{B}\|_{\mathsf{F}}^2 \le
\mathbb{E}\bigl\|(\mathbf{R}^{\mathsf{H}}\mathbf{Q}^{\mathsf{H}}\mathbf{V}_1)^{+}
\mathbf{R}^{\mathsf{H}}\mathbf{Q}^{\mathsf{H}}\mathbf{V}_2\mathbf{B}\bigr\|_{\mathsf{F}}^2\,,$$
with equality at $\mathbf{R} = \mathbf{I}$
(`NLAlib.integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame`). The integrand is integrable
(it is at most $\|\mathbf{R}\|_2^2\|\mathbf{R}^{-1}\|_2^2$ times the $\mathbf{R} = \mathbf{I}$ one).
[EpperlyWebber2026, Proposition 5.7]; there over $\mathbb{R}$ and $\mathbb{C}$ with the rows of
$\mathbf{\Omega}$ split, here with the blocks $\mathbf{V}_1^{\mathsf{H}}\mathbf{Q}$,
$\mathbf{V}_2^{\mathsf{H}}\mathbf{Q}$.
Proof: L, about 120 lines. EW's proof. (1) With $\mathbf{\Omega}_i =
\mathbf{V}_i^{\mathsf{H}}\mathbf{Q}$
and $F(\mathbf{x}) = \mathbf{R}(\mathbf{x}\mathbf{R})^{+}((\mathbf{x}\mathbf{R})^{+})^{\mathsf{H}}
\mathbf{R}^{\mathsf{H}}$, the matrix
$\mathbf{\Omega}_2 F(\mathbf{\Omega}_1)\mathbf{\Omega}_2^{\mathsf{H}}$ has mean a multiple of
$\mathbf{I}_s$ (`integral_conjTranspose_mul_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant`,
`isLeftUnitarilyInvariant_haarFrame`), so the expectation is
$\|\mathbf{B}\|_{\mathsf{F}}^2\,\mathbb{E}\operatorname{tr}(\cdots)/s$. (2) The trace: with
$\mathbf{\Omega}_1^{\mathsf{H}}\mathbf{\Omega}_1 + \mathbf{\Omega}_2^{\mathsf{H}}\mathbf{\Omega}_2 =
\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{I}$ and
$\mathbf{\Omega}_1 F(\mathbf{\Omega}_1)\mathbf{\Omega}_1^{\mathsf{H}}$ a rank-$r$ projector
(a.s. $\mathbf{\Omega}_1$ has full row rank, `ae_rank_mul_eq_min_of_hasLaw_haarFrame`),
$\operatorname{tr}(\mathbf{\Omega}_2 F\mathbf{\Omega}_2^{\mathsf{H}})$ equals
$\|(\mathbf{R}^{\mathsf{H}}\mathbf{\Omega}_1^{\mathsf{H}})^{+}
\mathbf{R}^{\mathsf{H}}\|_{\mathsf{F}}^2 - r$.
(3) `frobNorm_pinv_le_frobNorm_pinv_conjTranspose_mul_mul_conjTranspose` with
$\mathbf{M} = \mathbf{\Omega}_1^{\mathsf{H}}$, then the Beta trace
`integral_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame`:
$\mathbb{E}\|(\mathbf{\Omega}_1^{\mathsf{H}})^{+}\|_{\mathsf{F}}^2 = r(1 + (m - p)/(p - r - 1))$.
Arithmetic: $(r(1 + \frac{m-p}{p-r-1}) - r)/(m - r)$. -/
theorem mul_le_integral_frobNorm_pinv_conjTranspose_mul_mul_sq_of_hasLaw_haarFrame [DecidableEq p]
    [DecidableEq r] [DecidableEq s] (hQ : HasLaw Q (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) {V₁ : Matrix m r ℝ} {V₂ : Matrix m s ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0)
    (hrs : Fintype.card r + Fintype.card s = Fintype.card m)
    (hrp : Fintype.card r + 2 ≤ Fintype.card p) (B : Matrix s a ℝ) {R : Matrix p p ℝ}
    (hR : IsUnit R) :
    frobNorm B ^ 2 * (((Fintype.card m : ℝ) - Fintype.card p) /
        ((Fintype.card m : ℝ) - Fintype.card r) *
          ((Fintype.card r : ℝ) / ((Fintype.card p : ℝ) - Fintype.card r - 1))) ≤
      ∫ ω, frobNorm (pinv (Rᴴ * ((Q ω)ᴴ * V₁)) * (Rᴴ * ((Q ω)ᴴ * V₂)) * B) ^ 2 ∂μ := by
  classical
  have := hQ.isProbabilityMeasure
  have hVV : V₁ * V₁ᴴ + V₂ * V₂ᴴ = 1 :=
    (hasOrthonormalCols_fromCols_iff.mpr ⟨hV₁, hV₂, h₁₂⟩).mul_conjTranspose_add_mul_conjTranspose
      hrs
  have hW : HasOrthonormalCols (V₁ᴴ)ᴴ := by rwa [Matrix.conjTranspose_conjTranspose]
  have hpinv := integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame hQ hpm hW hrp
  have hc : ∀ Q₀ : Matrix m p ℝ, (V₁ᴴ * Q₀)ᴴ = Q₀ᴴ * V₁ := fun Q₀ => by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  set F := fun x : Matrix r p ℝ => (weightedFactor R x)ᴴ * weightedFactor R x
  set Z : Ω → Matrix s s ℝ := fun ω => V₂ᴴ * Q ω * F (V₁ᴴ * Q ω) * (V₂ᴴ * Q ω)ᴴ
  have hrank := ae_injective_mulVec_conjTranspose_mul hQ hV₁ hrp
  have hRinj : ∀ᵐ ω ∂μ, Function.Injective (Rᴴ * ((Q ω)ᴴ * V₁)).mulVec :=
    hrank.mono fun ω hω => injective_mulVec_conjTranspose_mul hR hω
  open scoped Matrix.Norms.L2Operator in
  have hZ : Integrable Z μ :=
    integrable_conj_weightedFactor_gram_of_hasLaw_haarFrame hQ hpm hV₁ hV₂ hrp hR
  have htr : ∀ᵐ ω ∂μ,
      (Z ω).trace = frobNorm (weightedFactor R (V₁ᴴ * Q ω)) ^ 2 - Fintype.card r := by
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hQ hpm, hRinj] with ω h1 h2
    exact trace_conj_weightedFactor_gram_eq R h1 hVV h2
  have hU2 := integral_conjTranspose_mul_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant hQ hV₂
    h₁₂ (measurable_weightedFactor_gram R) hZ
  have hval := integral_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame hQ hpm hW hrp
  have htrZ : Fintype.card r * (1 + ((Fintype.card m : ℝ) - Fintype.card p) /
      ((Fintype.card p : ℝ) - Fintype.card r - 1)) - Fintype.card r ≤ ∫ ω, (Z ω).trace ∂μ := by
    have htrint : Integrable (fun ω => (Z ω).trace) μ := by
      simp only [Matrix.trace, Matrix.diag]
      exact integrable_finsetSum _ fun i _ => Matrix.integrable_iff.mp hZ i i
    have e : ∫ ω, frobNorm (pinv (V₁ᴴ * Q ω)) ^ 2 ∂μ - Fintype.card r =
        ∫ ω, (frobNorm (pinv (V₁ᴴ * Q ω)) ^ 2 - Fintype.card r) ∂μ := by
      rw [integral_sub hpinv (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [← hval, e]
    refine integral_mono_ae (hpinv.sub (integrable_const _)) htrint ?_
    filter_upwards [htr] with ω h1
    rw [h1, weightedFactor, hc]
    have h := frobNorm_pinv_le_frobNorm_pinv_conjTranspose_mul_mul_conjTranspose ((Q ω)ᴴ * V₁) hR
    rw [show pinv ((Q ω)ᴴ * V₁) = (pinv (V₁ᴴ * Q ω))ᴴ by rw [← hc, pinv_conjTranspose],
      frobNorm_conjTranspose] at h
    gcongr
  have hC : (B * Bᴴ).trace = frobNorm B ^ 2 := by
    rw [← frobNorm_conjTranspose B, frobNorm_sq_eq_re_trace, Matrix.conjTranspose_conjTranspose,
      RCLike.re_to_real]
  simp only [frobNorm_pinv_conjTranspose_mul_mul_sq_eq_trace]
  rw [Matrix.integral_trace (hZ.mul_const _), Matrix.integral_mul_const hZ, hU2]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  rw [hC]
  have hs : (Fintype.card s : ℝ) = Fintype.card m - Fintype.card r := by
    rw [← hrs]; push_cast; ring
  have hmr : (0 : ℝ) < (Fintype.card m : ℝ) - Fintype.card r := by
    have : (Fintype.card r : ℝ) + 2 ≤ Fintype.card m := by exact_mod_cast hrp.trans hpm
    linarith
  have hpr : (0 : ℝ) < (Fintype.card p : ℝ) - Fintype.card r - 1 := by
    have : (Fintype.card r : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hrp
    linarith
  calc frobNorm B ^ 2 * (((Fintype.card m : ℝ) - Fintype.card p) /
        ((Fintype.card m : ℝ) - Fintype.card r) *
          ((Fintype.card r : ℝ) / ((Fintype.card p : ℝ) - Fintype.card r - 1)))
      = (Fintype.card r * (1 + ((Fintype.card m : ℝ) - Fintype.card p) /
          ((Fintype.card p : ℝ) - Fintype.card r - 1)) - Fintype.card r) / Fintype.card s *
            frobNorm B ^ 2 := by
        rw [hs]; field_simp; ring
    _ ≤ (∫ ω, (Z ω).trace ∂μ) / Fintype.card s * frobNorm B ^ 2 := by
        rw [hs]; gcongr
    _ = _ := rfl

end NLAlib
