/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RotationInvariantFactor

/-!
# The two-eigenvalue instance attains Epperly and Webber's factor (stage S10)

Epperly and Webber's Lemma 6.2 as a limit: on $\mathbf{D}_a = \operatorname{diag}(a\mathbf{I}_q,
b\mathbf{I}_{r-q})$ the expected trace error of Nyström tends, as $a \to \infty$,
to the factor <!-- value rotationInvariantFactor r \ell q -->
$(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))$ times $b(r - q)$, the bound that
`NLAlib.integral_nuclearNorm_fromBlocks_sub_nystrom_le_of_isLeftUnitarilyInvariant` proves at every
$a$. It joins `NLAlib/LowRank/Gaussian/RotationInvariantFactor.lean` (whose docstring reserves the
file for the matching lower bounds); its proof is deferred. Design:
`docs/design/LowRank-EstimatorLowerBounds.md` §3.3.

## Main results

* `NLAlib.tendsto_integral_nuclearNorm_fromBlocks_sub_nystrom_of_isLeftUnitarilyInvariant`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l : Type*} [Fintype l]

/-- As $a \to \infty$, $ab\operatorname{tr}(b\mathbf{I} + (a - b)\mathbf{X})^{-1} \to
b\operatorname{tr}\mathbf{X}^{-1}$ for an invertible $\mathbf{X}$. -/
private theorem tendsto_mul_trace_inv_smul_one_add_smul {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℝ} (hX : X.det ≠ 0) (b : ℝ) :
    Tendsto (fun a : ℝ => a * b * ((b • (1 : Matrix n n ℝ) + (a - b) • X)⁻¹).trace) atTop
      (𝓝 (b * (X⁻¹).trace)) := by
  set N : ℝ → Matrix n n ℝ := fun ε => (ε * b) • (1 : Matrix n n ℝ) + (1 - ε * b) • X
  have hN : Tendsto (fun a : ℝ => N a⁻¹) atTop (𝓝 X) := by
    have hc : Continuous N := by fun_prop
    convert (hc.tendsto 0).comp tendsto_inv_atTop_zero using 2 <;> simp [N]
  have hinv : ContinuousAt Inv.inv X :=
    continuousAt_matrix_inv X (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hX)
  have hdet : ∀ᶠ a : ℝ in atTop, (N a⁻¹).det ≠ 0 :=
    ((continuous_id.matrix_det.tendsto X).comp hN).eventually_ne hX
  refine (((continuous_id.matrix_trace.tendsto _).comp (hinv.tendsto.comp hN)).const_mul
    b).congr' ?_
  filter_upwards [hdet, eventually_gt_atTop 0] with a hd ha
  have hM : b • (1 : Matrix n n ℝ) + (a - b) • X = a • N a⁻¹ := by
    simp only [N, smul_add, smul_smul]
    rw [show a * (a⁻¹ * b) = b by field_simp, show a * (1 - a⁻¹ * b) = a - b by field_simp]
  have := invertibleOfNonzero ha.ne'
  rw [hM, Matrix.inv_smul (A := N a⁻¹) a hd.isUnit, invOf_eq_inv, Matrix.trace_smul]
  simp only [Function.comp_apply, id, smul_eq_mul]
  field_simp

/-- The value of the dominator's integral: for $q + 2 \le \ell \le q + t$,
$b\,q(1 + (q + t - \ell)/(\ell - q - 1)) + b(t - \ell)$ is the factor times $bt$. -/
private theorem rotationInvariantFactor_mul_eq {q l t : ℕ} (hq : q + 2 ≤ l) (hl : l ≤ q + t)
    (b : ℝ) : b * (q * (1 + (((q + t : ℕ) : ℝ) - l) / ((l : ℝ) - q - 1))) + b * ((t : ℝ) - l) =
      rotationInvariantFactor (q + t) l q * (b * t) := by
  rw [rotationInvariantFactor_def]
  have hq' : (q : ℝ) + 2 ≤ l := by exact_mod_cast hq
  have hl' : (l : ℝ) ≤ q + t := by exact_mod_cast hl
  have h1 : (l : ℝ) - q - 1 ≠ 0 := by linarith
  have h2 : ((q + t : ℕ) : ℝ) - q ≠ 0 := by
    push_cast; linarith
  push_cast at h2 ⊢
  field_simp
  ring

/-- **The two-eigenvalue instance attains the factor** (Epperly and Webber's Lemma 6.2): for
$\mathbf{Y}$ on $(s \oplus t) \times l$ with a left unitarily invariant law and full column rank
almost surely, $q = \lvert s\rvert$, $r = \lvert s\rvert + \lvert t\rvert$, $q + 2 \le \ell$,
$b \ge 0$ and $\mathbf{D}_a = \operatorname{diag}(a\mathbf{I}, b\mathbf{I})$,
so <!-- value rotationInvariantFactor r \ell q -->
$$\lim_{a \to \infty}\mathbb{E}\bigl\|\mathbf{D}_a - \mathsf{nystrom}(\mathbf{D}_a,
\mathbf{Y})\bigr\|_*
= \frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,b\,\lvert t\rvert\,.$$
With the upper bound at every $a$
(`NLAlib.integral_nuclearNorm_fromBlocks_sub_nystrom_le_of_isLeftUnitarilyInvariant`) this is the
sharpness of Epperly and Webber's factor on this instance. At $\ell = r$ both sides are $0$.
[EpperlyWebber2026, Lemma 6.2]; there over $\mathbb{R}$ and $\mathbb{C}$ with $a > b > 0$ and a zero
block, here real, $b \ge 0$, no zero block.
Proof: L, about 120 lines. Pass to the polar factor $\mathbf{\Psi}$, a Haar frame with the same
Nyström approximation (`hasLaw_polarFactor_of_isLeftUnitarilyInvariant`,
`Matrix.PosSemidef.nystrom_eq_of_range_eq`, as in the upper bound's proof). Dominated
convergence (`tendsto_integral_filter_of_dominated_convergence`): the dominator is the upper
bound's pointwise bound $b\|(\mathbf{W}\mathbf{\Psi})^{+}\|_{\mathsf{F}}^2 + b(\lvert t\rvert -
\ell)$
(`HasOrthonormalCols.nuclearNorm_fromBlocks_sub_nystrom_le`), integrable by
`integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame`, and it is also the pointwise limit.
For the limit, a.s. $\mathbf{\Psi}_1 = \mathbf{W}\mathbf{\Psi}$ ($q \times \ell$) has full row rank
(`ae_rank_mul_eq_min_of_hasLaw_haarFrame`). For $b > 0$ and $a > 0$ the error is exactly
$b(\lvert t\rvert - \ell) + ab\operatorname{Re}\operatorname{tr}\bigl(b\mathbf{I} +
(a-b)\mathbf{\Psi}_1\mathbf{\Psi}_1^{\mathsf{H}}\bigr)^{-1}$
(`HasOrthonormalCols.nuclearNorm_fromBlocks_sub_nystrom`); since $ab(b\mathbf{I} +
(a-b)\mathbf{K}\mathbf{K}^{\mathsf{H}})^{-1} = b\bigl((b/a)\mathbf{I} + (1 - b/a)
\mathbf{K}\mathbf{K}^{\mathsf{H}}\bigr)^{-1}$ and $\mathbf{K}\mathbf{K}^{\mathsf{H}}$
($\mathbf{K} = \mathbf{\Psi}_1$) is invertible, continuity of inversion gives the limit
$b(\lvert t\rvert - \ell) + b\operatorname{tr}(\mathbf{K}\mathbf{K}^{\mathsf{H}})^{-1} =
b(\lvert t\rvert - \ell) + b\|\mathbf{\Psi}_1^{+}\|_{\mathsf{F}}^2$, the dominator; no Schur
or QR form is needed. For $b = 0$ the error is $0$ for $a > 0$ (both sides vanish). The limit
value is the upper bound's computation. -/
theorem tendsto_integral_nuclearNorm_fromBlocks_sub_nystrom_of_isLeftUnitarilyInvariant
    {s t : Type*} [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    {ν' : Measure (Matrix (s ⊕ t) l ℝ)} [IsProbabilityMeasure ν'] [IsLeftUnitarilyInvariant ν']
    {Y : Ω → Matrix (s ⊕ t) l ℝ} (hY : HasLaw Y ν' μ)
    (hYr : ∀ᵐ ω ∂μ, Function.Injective (Y ω).mulVec) (hsl : Fintype.card s + 2 ≤ Fintype.card l)
    {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun a : ℝ => ∫ ω, nuclearNorm (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0
        (b • (1 : Matrix t t ℝ)) - nystrom (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0
          (b • (1 : Matrix t t ℝ))) (Y ω)) ∂μ) atTop
      (𝓝 (rotationInvariantFactor (Fintype.card s + Fintype.card t) (Fintype.card l)
        (Fintype.card s) * (b * Fintype.card t))) := by
  classical
  have := hY.isProbabilityMeasure_iff.2 inferInstance
  have hΨ := hasLaw_polarFactor_of_isLeftUnitarilyInvariant hY hYr
  have hl : Fintype.card l ≤ Fintype.card (s ⊕ t) := by
    obtain ⟨ω, hω⟩ := hYr.exists
    exact (hasOrthonormalCols_polarFactor_iff.2 hω).card_le
  set W : Matrix s (s ⊕ t) ℝ := (selectionMatrix Sum.inl)ᴴ
  have hW : HasOrthonormalCols Wᴴ := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hasOrthonormalCols_selectionMatrix Sum.inl_injective
  have hWrank : W.rank = Fintype.card s := by
    rw [Matrix.rank_conjTranspose]
    exact (hasOrthonormalCols_selectionMatrix Sum.inl_injective).rank_eq
  have hWΨ : ∀ Ψ : Matrix (s ⊕ t) l ℝ, W * Ψ = Ψ.toRows₁ := fun Ψ => by
    rw [conjTranspose_selectionMatrix_mul]
    rfl
  set D : ℝ → Matrix (s ⊕ t) (s ⊕ t) ℝ := fun a =>
    Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (b • (1 : Matrix t t ℝ))
  have hD : ∀ a, 0 ≤ a → (D a).PosSemidef := fun a ha =>
    (Matrix.PosSemidef.one.smul ha).fromBlocks_zero₁₂_zero₂₁ (Matrix.PosSemidef.one.smul hb)
  set g : Ω → ℝ := fun ω => b * frobNorm (pinv (W * polarFactor (Y ω))) ^ 2 +
    b * ((Fintype.card t : ℝ) - Fintype.card l)
  have hint : Integrable g μ :=
    ((integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame hΨ hl hW hsl).const_mul b).add
      (integrable_const _)
  -- almost surely the polar factor is a frame whose top block has full row rank
  have hgood : ∀ᵐ ω ∂μ, HasOrthonormalCols (polarFactor (Y ω)) ∧
      Function.Injective ((polarFactor (Y ω)).toRows₁)ᴴ.mulVec := by
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hΨ hl,
      ae_rank_mul_eq_min_of_hasLaw_haarFrame W hΨ] with ω hω hr
    refine ⟨hω, ?_⟩
    rw [mulVec_injective_iff_rank_eq, Matrix.rank_conjTranspose, ← hWΨ, hr, hWrank,
      min_eq_left (by omega)]
  have hnys : ∀ a ω, 0 ≤ a →
      nystrom (D a) (Y ω) = nystrom (D a) (polarFactor (Y ω)) := fun a ω ha =>
    (hD a ha).nystrom_eq_of_range_eq
      (rangeProjector_inj.mp (rangeProjector_polarFactor (Y ω))).symm
  have hval : ∫ ω, g ω ∂μ = rotationInvariantFactor (Fintype.card s + Fintype.card t)
      (Fintype.card l) (Fintype.card s) * (b * Fintype.card t) := by
    rw [integral_add ((integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame hΨ hl hW
      hsl).const_mul b) (integrable_const _), integral_const_mul,
      integral_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame hΨ hl hW hsl, integral_const,
      probReal_univ, one_smul, Fintype.card_sum]
    rw [Fintype.card_sum] at hl
    exact rotationInvariantFactor_mul_eq hsl hl b
  rw [← hval]
  refine tendsto_integral_filter_of_dominated_convergence (l := atTop)
    (F := fun a ω => nuclearNorm (D a - nystrom (D a) (Y ω))) g ?_ ?_ hint ?_
  · filter_upwards [eventually_ge_atTop 0] with a ha
    exact ((hD a ha).integrable_nuclearNorm_sub_nystrom hY.aemeasurable).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 0] with a ha
    filter_upwards [hgood] with ω hω
    rw [Real.norm_of_nonneg (nuclearNorm_nonneg _), hnys a ω ha]
    simp only [g, hWΨ]
    exact hω.1.nuclearNorm_fromBlocks_sub_nystrom_le hω.2 ha hb
  · filter_upwards [hgood] with ω ⟨hω, hK⟩
    simp only [g, hWΨ]
    rcases hb.eq_or_lt with rfl | hb'
    · -- for `b = 0` the error vanishes for every `a ≥ 0`
      simp only [zero_mul, add_zero]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with a ha
      have h := hω.nuclearNorm_fromBlocks_sub_nystrom_le hK ha le_rfl
      simp only [zero_mul, add_zero] at h
      rw [hnys a ω ha]
      exact (le_antisymm h (nuclearNorm_nonneg _)).symm
    · -- for `b > 0` the exact error formula and the limit of the trace of the inverse
      have hdet : ((polarFactor (Y ω)).toRows₁ * ((polarFactor (Y ω)).toRows₁)ᴴ).det ≠ 0 := by
        have hP := posDef_conjTranspose_mul_self_iff.mpr hK
        rw [Matrix.conjTranspose_conjTranspose] at hP
        exact hP.det_pos.ne'
      rw [frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose hK, RCLike.re_to_real,
        add_comm]
      refine ((tendsto_mul_trace_inv_smul_one_add_smul hdet b).const_add _).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with a ha
      rw [hnys a ω ha.le, hω.nuclearNorm_fromBlocks_sub_nystrom ha hb', RCLike.re_to_real]

end NLAlib
