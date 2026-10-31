/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.GeneralizedNystrom
public import NLAlib.LowRank.Gaussian.RotationInvariant
public import NLAlib.LowRank.Gaussian.RotationInvariantFactor

/-!
# Epperly and Webber's factors are sharp for rotation-invariant test matrices

For a test matrix with a left unitarily invariant law and full column rank almost surely
(Gaussian, Haar, ...), the library proves Epperly and Webber's sharp upper bounds: Nyström and the
randomized SVD with the factor <!-- value rotationInvariantFactor r \ell q -->
$(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))$ over matrices of rank at most $r$, and
generalized Nyström with that factor times the co-range completion factor
(`NLAlib.LowRank.Gaussian.RotationInvariant`, `NLAlib.LowRank.Gaussian.GeneralizedNystrom`). This
file shows the factors cannot be lowered. On the two-eigenvalue instance
$\mathbf{D}_a = \operatorname{diag}(a\mathbf{I}_q, b\mathbf{I}_{r-q})$ the expected trace error of
Nyström tends to the factor times $b(r - q)$ as $a \to \infty$ (Epperly and Webber's Lemma 6.2),
the bound `NLAlib.integral_nuclearNorm_fromBlocks_sub_nystrom_le_of_isLeftUnitarilyInvariant`
proves at every $a$. So for every constant below the factor some matrix of rank $r$ has a larger
expected error: Epperly and Webber's Theorems 3.3, 3.6(b) and 4.2(b) for rotation-invariant laws.
Their versions for an arbitrary full-rank law (an extra Haar rotation of the instance) are deferred.
Real field.

## Main results

* `NLAlib.tendsto_integral_nuclearNorm_fromBlocks_sub_nystrom_of_isLeftUnitarilyInvariant`: the
  two-eigenvalue instance attains the factor.
* `NLAlib.exists_lt_integral_nuclearNorm_sub_nystrom_of_isLeftUnitarilyInvariant`: Nyström.
* `NLAlib.exists_lt_integral_frobNorm_sub_rsvd_sq_of_isLeftUnitarilyInvariant`: the randomized SVD.
* generalized Nyström,
  [Gaussian co-range](https://nla-lib.org/explore/#d/NLAlib.exists_lt_integral_frobNorm_sub_generalizedNystrom_sq_of_isLeftUnitarilyInvariant_of_hasLaw_gaussianMatrix)
  and
  [Haar co-range](https://nla-lib.org/explore/#d/NLAlib.exists_lt_integral_frobNorm_sub_generalizedNystrom_sq_of_isLeftUnitarilyInvariant_of_hasLaw_haarFrame).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix ComplexOrder MatrixOrder Topology

namespace NLAlib

/-! ### The two-eigenvalue instance attains the factor -/

section Limit

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
block, here real, $b \ge 0$, no zero block. -/
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

end Limit

/-! ### The factors are sharp -/


variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l p : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype p] {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}
  [DecidableEq n] {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν]
  [IsLeftUnitarilyInvariant ν]

/-- The two-level diagonal $\operatorname{diag}(a\mathbf{I}_q, \mathbf{I}_d)$ of the hard
instance. -/
private abbrev twoLevel (q d : ℕ) (a : ℝ) : Matrix (Fin q ⊕ Fin d) (Fin q ⊕ Fin d) ℝ :=
  Matrix.fromBlocks (a • (1 : Matrix (Fin q) (Fin q) ℝ)) 0 0
    ((1 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ))

omit [Fintype n] [DecidableEq n] in
/-- The two-level block diagonal as a diagonal matrix. -/
private theorem twoLevel_eq_diagonal (q d : ℕ) (a : ℝ) :
    twoLevel q d a = Matrix.diagonal (Sum.elim (fun _ => a) fun _ => 1) := by
  rw [twoLevel, Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal,
    Matrix.fromBlocks_diagonal]

omit [Fintype m] [Fintype n] [Fintype l] [Fintype p] [DecidableEq n] in
/-- The hard instance $\mathbf{V}\operatorname{diag}(a\mathbf{I}_q, \mathbf{I}_d)
\mathbf{V}^{\mathsf{H}}$ is positive semidefinite for $a \ge 0$. -/
private theorem posSemidef_twoLevel [Finite n] {q d : ℕ} (V : Matrix n (Fin q ⊕ Fin d) ℝ)
    {a : ℝ} (ha : 0 ≤ a) : (V * twoLevel q d a * Vᴴ).PosSemidef := by
  have := Fintype.ofFinite n
  refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ V
  rw [twoLevel_eq_diagonal]
  exact Matrix.PosSemidef.diagonal fun i => by cases i <;> simp [ha]

omit [Fintype m] [Fintype l] [Fintype p] [DecidableEq n] in
/-- The hard instance has rank $q + d$ for $a > 0$. -/
private theorem rank_twoLevel {q d : ℕ} {V : Matrix n (Fin q ⊕ Fin d) ℝ}
    (hV : HasOrthonormalCols V) {a : ℝ} (ha : 0 < a) : (V * twoLevel q d a * Vᴴ).rank = q + d := by
  have hDr : (twoLevel q d a).rank = q + d := by
    rw [twoLevel_eq_diagonal, Matrix.rank_diagonal,
      Fintype.card_congr (Equiv.subtypeUnivEquiv fun i => by cases i <;> simp [ha.ne']),
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  refine le_antisymm (hDr ▸ (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))
    ?_
  have h : Vᴴ * (V * twoLevel q d a * Vᴴ) * V = twoLevel q d a := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.one_mul,
      Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.mul_one]
  calc q + d = (Vᴴ * (V * twoLevel q d a * Vᴴ) * V).rank := by rw [h, hDr]
    _ ≤ _ := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

omit [Fintype m] [Fintype l] [Fintype p] [DecidableEq n] in
/-- The optimal rank-$q$ trace error of the hard instance is at most $d$. -/
private theorem nuclearNorm_sub_truncatedSVD_twoLevel_le {q d : ℕ}
    {V : Matrix n (Fin q ⊕ Fin d) ℝ} (hV : HasOrthonormalCols V) (a : ℝ) :
    nuclearNorm (V * twoLevel q d a * Vᴴ - truncatedSVD (V * twoLevel q d a * Vᴴ) q) ≤ d := by
  set B := V * Matrix.fromBlocks (a • (1 : Matrix (Fin q) (Fin q) ℝ)) 0 0 0 * Vᴴ
  have hB : B.rank ≤ q := by
    refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans ?_)
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal,
      Matrix.rank_diagonal]
    have hl : ∀ i : Fin q ⊕ Fin d, Sum.elim (fun _ => a) (fun _ => (0 : ℝ)) i ≠ 0 →
        i.isLeft := by
      rintro (i | i) hi <;> simp at hi ⊢
    refine (Fintype.card_le_of_injective (fun i => i.1.getLeft (hl i.1 i.2)) ?_).trans_eq
      (Fintype.card_fin q)
    rintro ⟨i | i, hi⟩ ⟨j | j, hj⟩ h <;>
      first | exact Subtype.ext (congrArg Sum.inl h) | simp at hi hj
  have h := (lpGauge 1).matrixNorm_sub_truncatedSVD_le_of_rank_le (V * twoLevel q d a * Vᴴ) hB
  rw [lpGauge_one_matrixNorm, lpGauge_one_matrixNorm] at h
  refine h.trans (le_of_eq ?_)
  have hsub : V * twoLevel q d a * Vᴴ - B =
      V * Matrix.fromBlocks 0 0 0 ((1 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) * Vᴴ := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, sub_eq_add_neg, Matrix.fromBlocks_neg,
      Matrix.fromBlocks_add]
    simp only [add_neg_cancel, neg_zero, add_zero]
  rw [hsub, hV.nuclearNorm_mul_conjTranspose_right, hV.nuclearNorm_mul_left,
    Matrix.PosSemidef.nuclearNorm_eq_re_trace ?_]
  · simp [Matrix.trace_fromBlocks]
  · rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal]
    exact Matrix.PosSemidef.diagonal fun i => by cases i <;> simp

omit [Fintype m] [Fintype p] in
/-- The expected Nyström error on the hard instance is the Gaussian one on the diagonal. -/
private theorem integral_nuclearNorm_sub_nystrom_twoLevel (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {q d : ℕ}
    {V : Matrix n (Fin q ⊕ Fin d) ℝ} (hV : HasOrthonormalCols V) {a : ℝ} (ha : 0 ≤ a) :
    ∫ ω, nuclearNorm (V * twoLevel q d a * Vᴴ - nystrom (V * twoLevel q d a * Vᴴ) (X ω)) ∂μ =
      ∫ G, nuclearNorm (twoLevel q d a - nystrom (twoLevel q d a) (Vᴴ * G))
        ∂(gaussianMatrix n l) := by
  obtain ⟨S, hS⟩ : ∃ S : Matrix n n ℝ, ∀ G : Matrix n l ℝ,
      nystrom (V * twoLevel q d a * Vᴴ) G = S * rangeProjector (S * G) * S :=
    ⟨_, (posSemidef_twoLevel V ha).nystrom_eq⟩
  have hg : Measurable fun P : Matrix n n ℝ => nuclearNorm (V * twoLevel q d a * Vᴴ - S * P * S) :=
    continuous_nuclearNorm.measurable.comp (measurable_const.sub
      ((measurable_const.matrix_mul measurable_id).matrix_mul measurable_const))
  rw [integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant S hX hXr
    (f := fun Y => nuclearNorm (V * twoLevel q d a * Vᴴ - nystrom (V * twoLevel q d a * Vᴴ) Y))
    hg fun Y => by rw [hS]]
  refine integral_congr_ae (ae_of_all _ fun G => ?_)
  have h := nystrom_conjTranspose_mul_mul Vᴴ (twoLevel q d a) G
  rw [Matrix.conjTranspose_conjTranspose] at h
  simp only [h, ← Matrix.sub_mul, ← Matrix.mul_sub, hV.nuclearNorm_mul_conjTranspose_right,
    hV.nuclearNorm_mul_left]

/-- **Epperly and Webber's Nyström factor is sharp**: for a test matrix $\mathbf{X}$ with a left
unitarily invariant law and full column rank almost surely, $q + 2 \le \ell \le r \le n$ and every
$c$ below the factor, <!-- value rotationInvariantFactor r \ell q -->
$$c < \frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,,$$
there is a positive semidefinite $\mathbf{H}$ of rank $r$ with
$$c\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_* <
\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_*\,.$$
The matching upper bound is
`Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant_of_rank_le`.
[EpperlyWebber2026, Theorem 3.6(b)]; there for every full-rank law (with a Haar rotation of the
instance), here for left unitarily invariant laws, which need none.
Result: randomized-nystrom-lower-bound -/
theorem exists_lt_integral_nuclearNorm_sub_nystrom_of_isLeftUnitarilyInvariant
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {r q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) (hlr : Fintype.card l ≤ r) (hrn : r ≤ Fintype.card n) {c : ℝ}
    (hc : c < rotationInvariantFactor r (Fintype.card l) q) :
    ∃ H : Matrix n n ℝ, H.PosSemidef ∧ H.rank = r ∧
      c * nuclearNorm (H - truncatedSVD H q) < ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ := by
  classical
  set d := r - q with hd_def
  have hd : q + d = r := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨V, hV⟩ := exists_hasOrthonormalCols_of_card_le (n := n) (p := Fin q ⊕ Fin d) ℝ
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  have hY : HasLaw (fun G : Matrix n l ℝ => Vᴴ * G) (gaussianMatrix (Fin q ⊕ Fin d) l)
      (gaussianMatrix n l) :=
    hasLaw_const_mul_of_hasLaw_gaussianMatrix HasLaw.id
      (by rwa [Matrix.conjTranspose_conjTranspose])
  have hYr : ∀ᵐ G ∂(gaussianMatrix n l), Function.Injective (Vᴴ * G).mulVec := by
    filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hY] with G hG
    rw [mulVec_injective_iff_rank_eq, hG, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    exact min_eq_right (by omega)
  have hlim := tendsto_integral_nuclearNorm_fromBlocks_sub_nystrom_of_isLeftUnitarilyInvariant hY
    hYr (by simp only [Fintype.card_fin]; exact hq) zero_le_one
  simp only [Fintype.card_fin, hd, one_mul] at hlim
  rcases lt_or_ge c 0 with hc0 | hc0
  · refine ⟨V * twoLevel q d 1 * Vᴴ, posSemidef_twoLevel V zero_le_one,
      hd ▸ rank_twoLevel hV one_pos, ?_⟩
    have hpos : 0 < nuclearNorm (V * twoLevel q d 1 * Vᴴ -
        truncatedSVD (V * twoLevel q d 1 * Vᴴ) q) := by
      refine (nuclearNorm_nonneg _).lt_of_ne fun h => ?_
      have h' := sub_eq_zero.mp (nuclearNorm_eq_zero_iff.mp h.symm)
      have := rank_truncatedSVD_le (V * twoLevel q d 1 * Vᴴ) q
      rw [← h', rank_twoLevel hV one_pos] at this
      omega
    exact (mul_neg_of_neg_of_pos hc0 hpos).trans_le
      (integral_nonneg fun ω => nuclearNorm_nonneg _)
  · obtain ⟨a, ha, ha1⟩ := ((hlim.eventually (lt_mem_nhds (mul_lt_mul_of_pos_right hc hd0))).and
      (Filter.eventually_ge_atTop 1)).exists
    refine ⟨V * twoLevel q d a * Vᴴ, posSemidef_twoLevel V (by linarith),
      hd ▸ rank_twoLevel hV (by linarith), ?_⟩
    rw [integral_nuclearNorm_sub_nystrom_twoLevel hX hXr hV (by linarith)]
    exact (mul_le_mul_of_nonneg_left (nuclearNorm_sub_truncatedSVD_twoLevel_le hV a) hc0).trans_lt
      ha

/-- **Epperly and Webber's randomized SVD factor is sharp**: for a test matrix $\mathbf{X}$ with a
left unitarily invariant law and full column rank almost surely, $q + 2 \le \ell \le r$,
$r \le \min(m, n)$ and every $c$ below the factor, <!-- value rotationInvariantFactor r \ell q -->
$$c < \frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,,$$
there is $\mathbf{A} \in \mathbb{R}^{m \times n}$ of rank $r$ with
$$c\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2 <
\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2\,.$$
The matching upper bound is
`NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant_of_rank_le`.
[EpperlyWebber2026, Theorem 3.3]; there for every full-rank law, here for left unitarily
invariant laws.
Result: randomized-svd-lower-bound -/
theorem exists_lt_integral_frobNorm_sub_rsvd_sq_of_isLeftUnitarilyInvariant
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {r q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) (hlr : Fintype.card l ≤ r) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) {c : ℝ} (hc : c < rotationInvariantFactor r (Fintype.card l) q) :
    ∃ A : Matrix m n ℝ, A.rank = r ∧
      c * frobNorm (A - truncatedSVD A q) ^ 2 < ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  obtain ⟨H, hH, hrank, hineq⟩ :=
    exists_lt_integral_nuclearNorm_sub_nystrom_of_isLeftUnitarilyInvariant hX hXr hq hlr hrn hc
  have hSH : (CFC.sqrt H)ᴴ * CFC.sqrt H = H := hH.conjTranspose_sqrt_mul_sqrt
  have hrS : (CFC.sqrt H).rank = r := by
    rw [← Matrix.rank_conjTranspose_mul_self, hSH, hrank]
  obtain ⟨Z, hZ, hZP⟩ :=
    (isStarProjection_rangeProjector (CFC.sqrt H)).exists_hasOrthonormalCols_mul_conjTranspose_eq
      (p := Fin r) (by rw [rank_rangeProjector, hrS, Fintype.card_fin])
  obtain ⟨J, hJ⟩ := exists_hasOrthonormalCols_of_card_le (p := Fin r) ℝ (by simpa using hrm)
  have hAH : (J * (Zᴴ * CFC.sqrt H))ᴴ * (J * (Zᴴ * CFC.sqrt H)) = H := by
    have hZZ : Z * Zᴴ * CFC.sqrt H = CFC.sqrt H := by
      rw [hZP, rangeProjector_mul_self]
    have hJJ : Jᴴ * J = 1 := hJ
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Jᴴ J, hJJ, Matrix.one_mul, ← Matrix.mul_assoc Z, hZZ]
    exact hSH
  refine ⟨J * (Zᴴ * CFC.sqrt H), ?_, ?_⟩
  · rw [← Matrix.rank_conjTranspose_mul_self, hAH, hrank]
  · rw [← nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
    simp only [← nuclearNorm_conjTranspose_mul_self_sub_nystrom]
    rw [hAH]
    exact hineq

-- A docstring line and the declaration name exceed 100 characters.
set_option linter.style.longLine false in
/-- **Epperly and Webber's generalized Nyström factor is sharp, Gaussian co-range**: for a test
matrix $\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely, an
independent standard Gaussian $\mathbf{\Psi}$ ($m \times p$), $q + 2 \le \ell \le r$,
$r \le \min(m, n)$, $\ell + 2 \le p$ and every $c$ below the factor, that
is <!-- value gaussianProjectionFactor \ell p --> <!-- value rotationInvariantFactor r \ell q -->
$$c < \Bigl(1 + \frac{\ell}{p - \ell - 1}\Bigr)
\frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,,$$
there is $\mathbf{A} \in \mathbb{R}^{m \times n}$ of rank $r$ with
$$c\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2 <
\mathbb{E}\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{X}, \mathbf{\Psi})\|_{\mathsf{F}}^2\,.$$
So with a Gaussian co-range the product of the two factors cannot be lowered. Epperly and
Webber's §4.2 turns this into "$k' + \ell = \Theta(q/\varepsilon^2)$ samples"; that arithmetic over
$\mathbb{R}$ is not proved here. The matching upper bound is
`NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_hasLaw_gaussianMatrix_of_rank_le`.
[EpperlyWebber2026, Theorem 4.2(b)]; there for every full-rank pair of laws and an orthonormal
co-range, here for a left unitarily invariant range law and a Gaussian co-range ($\gamma = 1$).
Result: generalized-nystrom-lower-bound -/
theorem
    exists_lt_integral_frobNorm_sub_generalizedNystrom_sq_of_isLeftUnitarilyInvariant_of_hasLaw_gaussianMatrix
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {r q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) (hlr : Fintype.card l ≤ r) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) (hlp : Fintype.card l + 2 ≤ Fintype.card p) {c : ℝ}
    (hc : c < gaussianProjectionFactor (Fintype.card l) (Fintype.card p) *
      rotationInvariantFactor r (Fintype.card l) q) :
    ∃ A : Matrix m n ℝ, A.rank = r ∧
      c * frobNorm (A - truncatedSVD A q) ^ 2 <
        ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ := by
  classical
  set g := gaussianProjectionFactor (Fintype.card l) (Fintype.card p) with hg_def
  have hg0 : 0 < g := zero_lt_one.trans_le (one_le_gaussianProjectionFactor hlp)
  have hc' : c / g < rotationInvariantFactor r (Fintype.card l) q := by
    rw [div_lt_iff₀ hg0, mul_comm]
    exact hc
  obtain ⟨A, hA, hlt⟩ :=
    exists_lt_integral_frobNorm_sub_rsvd_sq_of_isLeftUnitarilyInvariant hX hXr hq hlr hrm hrn hc'
  have hrank : ∀ᵐ ω ∂μ, (A * X ω).rank = Fintype.card l := by
    filter_upwards [ae_rank_mul_eq_min_of_isLeftUnitarilyInvariant A hX hXr] with ω hω
    rw [hω, hA, min_eq_right hlr]
  have hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p :=
    hrank.mono fun ω hω => by rw [hω]; exact hlp
  have heq : ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ =
      g * ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
    rw [integral_frobNorm_sub_generalizedNystrom_sq_eq_integral_of_hasLaw_gaussianMatrix A
      hX.aemeasurable hΨ hXΨ hr, ← integral_const_mul]
    exact integral_congr_ae (hrank.mono fun ω hω => by
      change gaussianProjectionFactor (A * X ω).rank (Fintype.card p) * _ = g * _
      rw [hω])
  refine ⟨A, hA, ?_⟩
  rw [heq]
  have hcg : c * frobNorm (A - truncatedSVD A q) ^ 2 =
      g * (c / g * frobNorm (A - truncatedSVD A q) ^ 2) := by
    field_simp
  rw [hcg]
  exact mul_lt_mul_of_pos_left hlt hg0

-- A docstring line and the declaration name exceed 100 characters.
set_option linter.style.longLine false in
/-- **Epperly and Webber's generalized Nyström factor is sharp, random orthonormal co-range**: for
a test matrix $\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely,
an independent $m \times p$ Haar frame $\mathbf{\Psi}$, $q + 2 \le \ell \le r$, $r \le \min(m, n)$,
$\ell + 2 \le p \le m$ and every $c$ below the
factor, <!-- value haarProjectionFactor m p \ell --> <!-- value rotationInvariantFactor r \ell q -->
$$c < \Bigl(1 + \frac{m - p}{m - \ell}\cdot\frac{\ell}{p - \ell - 1}\Bigr)
\frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,,$$
there is $\mathbf{A} \in \mathbb{R}^{m \times n}$ of rank $r$ with
$$c\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2 <
\mathbb{E}\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{X}, \mathbf{\Psi})\|_{\mathsf{F}}^2\,.$$
The matching upper bound is
`NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_hasLaw_haarFrame_of_rank_le`.
[EpperlyWebber2026, Theorem 4.2(b)]; there for every full-rank pair of laws, here for a left
unitarily invariant range law and a Haar co-range ($\gamma = (d - k)/(d - \ell)$ in their letters).
Result: generalized-nystrom-lower-bound -/
theorem
    exists_lt_integral_frobNorm_sub_generalizedNystrom_sq_of_isLeftUnitarilyInvariant_of_hasLaw_haarFrame
    [DecidableEq p] (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)
    (hΨ : HasLaw Ψ (haarFrame m p) μ) (hXΨ : IndepFun X Ψ μ) {r q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) (hlr : Fintype.card l ≤ r) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) (hlp : Fintype.card l + 2 ≤ Fintype.card p)
    (hpm : Fintype.card p ≤ Fintype.card m) {c : ℝ}
    (hc : c < haarProjectionFactor (Fintype.card m) (Fintype.card p) (Fintype.card l) *
      rotationInvariantFactor r (Fintype.card l) q) :
    ∃ A : Matrix m n ℝ, A.rank = r ∧
      c * frobNorm (A - truncatedSVD A q) ^ 2 <
        ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hf := one_le_haarProjectionFactor hlp hpm
  obtain ⟨A, hA, hlt⟩ := exists_lt_integral_frobNorm_sub_rsvd_sq_of_isLeftUnitarilyInvariant
    hX hXr hq hlr hrm hrn (c := c / haarProjectionFactor (Fintype.card m) (Fintype.card p)
      (Fintype.card l)) (by rwa [div_lt_iff₀' (by linarith)])
  refine ⟨A, hA, ?_⟩
  have hk : ∀ᵐ ω ∂μ, (A * X ω).rank = Fintype.card l :=
    (ae_rank_mul_eq_min_of_isLeftUnitarilyInvariant A hX hXr).mono fun ω hω => by
      rw [hω, hA, min_eq_right hlr]
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (haarFrame m p) (haarFrame m p) := HasLaw.id
  -- The Haar identity, integrated over the range test matrix: the fixed-`X` form inside.
  have hlin := hXΨ.lintegral_ofReal_comp_eq_lintegral_ofReal_integral hX.aemeasurable hΨ
    (F := fun q : Matrix n l ℝ × Matrix m p ℝ => frobNorm (A - generalizedNystrom A q.1 q.2) ^ 2)
    ((continuous_frobNorm.measurable.comp
      (measurable_const.sub (measurable_generalizedNystrom A))).pow_const 2)
    (fun _ => sq_nonneg _) (hk.mono fun ω hω =>
      integrable_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_haarFrame A aemeasurable_const hid
        hpm (indepFun_const_left _ _) (ae_of_all _ fun _ => hω ▸ hlp))
  have hgm : AEStronglyMeasurable
      (fun ω => frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2) μ :=
    (((continuous_frobNorm.measurable.comp (measurable_const.sub
      (measurable_generalizedNystrom A))).pow_const 2).comp_aemeasurable
        (hX.aemeasurable.prodMk hΨ.aemeasurable)).aestronglyMeasurable
  have hR := (integrable_frobNorm_sub_rsvd_sq A hX.aemeasurable).const_mul
    (haarProjectionFactor (Fintype.card m) (Fintype.card p) (Fintype.card l))
  have heq : ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ =
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (Fintype.card l) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
    rw [← integral_const_mul,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) hgm,
      integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun _ => mul_nonneg (by linarith) (sq_nonneg _))
        hR.aestronglyMeasurable, hlin]
    refine congrArg ENNReal.toReal (lintegral_congr_ae (hk.mono fun ω hω => ?_))
    refine congrArg ENNReal.ofReal ?_
    rw [← hω]
    exact integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_haarFrame A (X ω) hid hpm
      (hω ▸ hlp)
  rw [heq]
  rw [div_mul_eq_mul_div, div_lt_iff₀' (by linarith)] at hlt
  exact hlt

end NLAlib
