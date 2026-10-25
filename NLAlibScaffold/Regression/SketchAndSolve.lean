/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Regression.SketchAndSolve
public import NLAlibScaffold.RandomMatrix.Haar.Blocks

/-!
# No sketch beats a random orthonormal one for sketch-and-solve (stage S10)

Epperly and Webber's Theorem 2.2: for every sketch with full column rank, some rotation of
any least-squares problem with $\operatorname{rank}\mathbf{A} = r$ has expected sketch-and-solve
residual at least the random orthonormal factor <!-- value haarProjectionFactor m \ell r -->
$1 + (m - \ell)/(m - r) \cdot (r/(\ell - r - 1))$ times the optimum, the exact value for a Haar
sketch (`NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame`). Three forms:
averaged over a Haar rotation for a fixed sketch, a single rotation for a fixed sketch, and a
single rotation for a random sketch of any law (in `lintegral`, since the expectation may be
infinite). They join `NLAlib/Regression/SketchAndSolve.lean`; proofs deferred. Design:
`docs/design/LowRank-EstimatorLowerBounds.md` §3.3.

## Main results

* `NLAlib.le_integral_frobNorm_mul_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame`
* `NLAlib.exists_hasOrthonormalCols_le_frobNorm_mul_sub_mul_sketchAndSolve_sq`
* `NLAlib.exists_hasOrthonormalCols_le_lintegral_frobNorm_mul_sub_mul_sketchAndSolve_sq`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l r : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype r] [DecidableEq m]

omit [Fintype r] in
/-- Complementary orthonormal frames $\mathbf{Q}_1$ of $\operatorname{range}\mathbf{X}$ and
$\mathbf{Q}_2$ of its orthogonal complement; the second reproduces every residual
$(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$. -/
private theorem exists_compl_frames {s : Type*} [Fintype s] (X : Matrix m s ℝ)
    (B : Matrix m r ℝ) :
    ∃ (Q₁ : Matrix m (Fin X.rank) ℝ) (Q₂ : Matrix m (Fin (Fintype.card m - X.rank)) ℝ),
      HasOrthonormalCols Q₁ ∧ HasOrthonormalCols Q₂ ∧ Q₁ᴴ * Q₂ = 0 ∧
        LinearMap.range Q₁.mulVecLin = LinearMap.range X.mulVecLin ∧
          Q₂ * (Q₂ᴴ * ((1 - rangeProjector X) * B)) = (1 - rangeProjector X) * B := by
  obtain ⟨Q₁, Q₂, hQ, h₁, h₂⟩ :=
    (isStarProjection_rangeProjector X).exists_hasOrthonormalCols_fromCols_mul_conjTranspose_eq
      (p := Fin X.rank) (q := Fin (Fintype.card m - X.rank))
      (by rw [rank_rangeProjector, Fintype.card_fin])
      (by have := Matrix.rank_le_card_height X; simp only [Fintype.card_fin]; omega)
  obtain ⟨hQ₁, hQ₂, h₁₂⟩ := hasOrthonormalCols_fromCols_iff.mp hQ
  refine ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, rangeProjector_inj.mp (hQ₁.rangeProjector_eq.trans h₁), ?_⟩
  rw [← Matrix.mul_assoc, h₂, ← Matrix.mul_assoc,
    (isStarProjection_one_sub_rangeProjector X).mul_self]

omit [Fintype m] [DecidableEq m] in
/-- A weight costs at most its inverse's norm in the pseudoinverse: for invertible $\mathbf{R}$
and $\mathbf{X}$ of full column rank, $\|(\mathbf{R}^{\mathsf{H}}\mathbf{X})^{+}\|_2^2 \le
(\|\mathbf{R}^{-1}\|_2\|\mathbf{X}^{+}\|_2)^2 + 1$. -/
private theorem specNorm_pinv_conjTranspose_mul_sq_le {p : Type*} [Fintype p] [DecidableEq p]
    {R : Matrix p p ℝ} (hR : IsUnit R) {X : Matrix p r ℝ}
    (hX : Function.Injective X.mulVec) :
    specNorm (pinv (Rᴴ * X)) ^ 2 ≤ (specNorm R⁻¹ * specNorm (pinv X)) ^ 2 + 1 := by
  classical
  have hc : 0 < (specNorm R⁻¹ * specNorm (pinv X)) ^ 2 + 1 := by positivity
  have hXN : X = R⁻¹ᴴ * (Rᴴ * X) := by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det R).mp hR),
      Matrix.conjTranspose_one, Matrix.one_mul]
  have h := specNorm_pinv_sq_le_inv_of_smul_one_le (A := Rᴴ * X) (inv_pos.mpr hc)
    (smul_one_le_conjTranspose_mul_self_iff.mpr fun x => ?_)
  · rwa [inv_inv] at h
  have h1 := norm_le_specNorm_pinv_mul_norm_mulVec hX x
  have h2 := norm_toLp_mulVec_le R⁻¹ᴴ ((Rᴴ * X) *ᵥ x)
  rw [Matrix.mulVec_mulVec, ← hXN, specNorm_conjTranspose] at h2
  have h3 : ‖WithLp.toLp 2 x‖ ≤
      specNorm R⁻¹ * specNorm (pinv X) * ‖WithLp.toLp 2 ((Rᴴ * X) *ᵥ x)‖ := by
    calc ‖WithLp.toLp 2 x‖ ≤ specNorm (pinv X) * ‖WithLp.toLp 2 (X *ᵥ x)‖ := h1
      _ ≤ specNorm (pinv X) * (specNorm R⁻¹ * ‖WithLp.toLp 2 ((Rᴴ * X) *ᵥ x)‖) := by gcongr
      _ = _ := by ring
  rw [inv_mul_le_iff₀ hc]
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  nlinarith [sq_nonneg ‖WithLp.toLp 2 ((Rᴴ * X) *ᵥ x)‖]

omit [DecidableEq m] in
/-- The weighted Haar block is square integrable. -/
private theorem integrable_frobNorm_pinv_conjTranspose_mul_mul_sq {p s a : Type*} [Fintype p]
    [Fintype s] [Fintype a] [DecidableEq p] [DecidableEq r] [DecidableEq s]
    {Q : Ω → Matrix m p ℝ} (hQ : HasLaw Q (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) {V₁ : Matrix m r ℝ} {V₂ : Matrix m s ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (hrp : Fintype.card r + 2 ≤ Fintype.card p) (B : Matrix s a ℝ) {R : Matrix p p ℝ}
    (hR : IsUnit R) :
    Integrable (fun ω => frobNorm (pinv (Rᴴ * ((Q ω)ᴴ * V₁)) * (Rᴴ * ((Q ω)ᴴ * V₂)) * B) ^ 2)
      μ := by
  have := hQ.isProbabilityMeasure
  have hW : HasOrthonormalCols (V₁ᴴ)ᴴ := by rwa [Matrix.conjTranspose_conjTranspose]
  have hint := integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame hQ hpm hW hrp
  have hT : Measurable fun Q₀ : Matrix m p ℝ => Q₀ᴴ :=
    continuous_id.matrix_conjTranspose.measurable
  have hmeas : Measurable fun Q₀ : Matrix m p ℝ =>
      frobNorm (pinv (Rᴴ * (Q₀ᴴ * V₁)) * (Rᴴ * (Q₀ᴴ * V₂)) * B) ^ 2 :=
    (measurable_frobNorm.comp (((measurable_pinv.comp (measurable_const.matrix_mul
      (hT.matrix_mul measurable_const))).matrix_mul (measurable_const.matrix_mul
        (hT.matrix_mul measurable_const))).matrix_mul measurable_const)).pow_const 2
  refine Integrable.mono'
    (((hint.const_mul (specNorm R⁻¹ ^ 2)).add (integrable_const 1)).mul_const
      (specNorm R ^ 2 * frobNorm B ^ 2))
    (hmeas.comp_aemeasurable hQ.aemeasurable).aestronglyMeasurable ?_
  filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hQ,
    ae_rank_mul_eq_min_of_hasLaw_haarFrame V₁ᴴ hQ] with ω hω hrk
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hX : (Q ω)ᴴ * V₁ = (V₁ᴴ * Q ω)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hinj : Function.Injective ((Q ω)ᴴ * V₁).mulVec := by
    rw [mulVec_injective_iff_rank_eq, hX, Matrix.rank_conjTranspose, hrk,
      Matrix.rank_conjTranspose, hV₁.rank_eq, min_eq_left (by omega)]
  have hP := specNorm_pinv_conjTranspose_mul_sq_le hR hinj
  have hPF : specNorm (pinv ((Q ω)ᴴ * V₁)) ≤ frobNorm (pinv (V₁ᴴ * Q ω)) := by
    rw [hX, pinv_conjTranspose, ← frobNorm_conjTranspose]
    exact specNorm_le_frobNorm _
  have hY : specNorm (Rᴴ * ((Q ω)ᴴ * V₂)) ≤ specNorm R := by
    refine (specNorm_mul_le _ _).trans ?_
    rw [specNorm_conjTranspose]
    refine mul_le_of_le_one_right (specNorm_nonneg _) ?_
    rw [← specNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact (hV₂.specNorm_conjTranspose_mul_le _).trans hω
  have hF : frobNorm (pinv (Rᴴ * ((Q ω)ᴴ * V₁)) * (Rᴴ * ((Q ω)ᴴ * V₂)) * B) ≤
      specNorm (pinv (Rᴴ * ((Q ω)ᴴ * V₁))) * specNorm (Rᴴ * ((Q ω)ᴴ * V₂)) * frobNorm B :=
    (frobNorm_mul_le_specNorm_mul_frobNorm _ B).trans (by gcongr; exact specNorm_mul_le _ _)
  have hP' : specNorm (pinv (Rᴴ * ((Q ω)ᴴ * V₁))) ^ 2 ≤
      specNorm R⁻¹ ^ 2 * frobNorm (pinv (V₁ᴴ * Q ω)) ^ 2 + 1 :=
    hP.trans (by rw [mul_pow]; gcongr)
  simp only [Pi.add_apply]
  calc frobNorm (pinv (Rᴴ * ((Q ω)ᴴ * V₁)) * (Rᴴ * ((Q ω)ᴴ * V₂)) * B) ^ 2
      ≤ (specNorm (pinv (Rᴴ * ((Q ω)ᴴ * V₁))) * specNorm (Rᴴ * ((Q ω)ᴴ * V₂)) *
          frobNorm B) ^ 2 := pow_le_pow_left₀ (frobNorm_nonneg _) hF 2
    _ = specNorm (pinv (Rᴴ * ((Q ω)ᴴ * V₁))) ^ 2 *
          (specNorm (Rᴴ * ((Q ω)ᴴ * V₂)) ^ 2 * frobNorm B ^ 2) := by ring
    _ ≤ _ := by gcongr

/-- **A Haar rotation of the problem defeats every fixed sketch**: for a fixed sketch
$\mathbf{\Omega}_0 \in \mathbb{R}^{m \times \ell}$ of full column rank, $\mathbf{A} \in
\mathbb{R}^{m \times n}$
with $r = \operatorname{rank}\mathbf{A}$, $r + 2 \le \ell$, any $\mathbf{B} \in \mathbb{R}^{m \times
r'}$ and
an $m \times m$ Haar orthogonal $\mathbf{U}$, <!-- value haarProjectionFactor m \ell r -->
$$\Bigl(1 + \frac{m - \ell}{m - r}\cdot\frac{r}{\ell - r - 1}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{B}\|_{\mathsf{F}}^2 \le
\mathbb{E}\|\mathbf{U}\mathbf{B} -
\mathbf{U}\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{U}\mathbf{A},
\mathbf{\Omega}_0^{\mathsf{H}}, \mathbf{U}\mathbf{B})\|_{\mathsf{F}}^2\,,$$
the factor being `haarProjectionFactor m ℓ r` and the left side's minimum the optimum of every
rotated problem.
[EpperlyWebber2026, Theorem 2.2 (§5.5)]; there as a supremum over problems for a random sketch,
here averaged over the rotation for a fixed one (the core of their proof).
Proof: L, about 100 lines. Polar/QR factor $\mathbf{\Omega}_0 = \mathbf{W}\mathbf{R}$ with
$\mathbf{W}$ orthonormal, $\mathbf{R}$ invertible (`polarFactor`, full column rank). The estimator
on
$(\mathbf{U}\mathbf{A}, \mathbf{U}\mathbf{B})$ with sketch $\mathbf{\Omega}_0^{\mathsf{H}}$ is the
estimator on $(\mathbf{A}, \mathbf{B})$ with sketch
$(\mathbf{U}^{\mathsf{H}}\mathbf{\Omega}_0)^{\mathsf{H}}$,
and $\mathbf{U}^{\mathsf{H}}\mathbf{W}$ is an $m \times \ell$ Haar frame
(`isRightUnitarilyInvariant_haarFrame`, `haarFrame_eq_map_haarMeasure`). Split
$\mathbf{B}$ along $\operatorname{range}\mathbf{A}$ with an orthonormal basis $\mathbf{V}_1$ and its
complement $\mathbf{V}_2$ (`exists_hasOrthonormalCols_range_eq`): the residual is
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{B}\|_{\mathsf{F}}^2$ plus the weighted block term
(EW Lemma 5.1, the rank-$r$ decomposition used in
`integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame`), whose mean is bounded below by
`mul_le_integral_frobNorm_pinv_conjTranspose_mul_mul_sq_of_hasLaw_haarFrame` with weight
$\mathbf{R}$. -/
theorem le_integral_frobNorm_mul_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame {r' : Type*}
    [Fintype r'] {U : Ω → Matrix m m ℝ} (hU : HasLaw U (haarFrame m m) μ) {Ω₀ : Matrix m l ℝ}
    (hΩ₀ : Ω₀.rank = Fintype.card l) {A : Matrix m n ℝ} (hA : A.rank + 2 ≤ Fintype.card l)
    (B : Matrix m r' ℝ) :
    haarProjectionFactor (Fintype.card m) (Fintype.card l) A.rank *
        frobNorm ((1 - rangeProjector A) * B) ^ 2 ≤
      ∫ ω, frobNorm (U ω * B - U ω * A * sketchAndSolve (U ω * A) Ω₀ᴴ (U ω * B)) ^ 2 ∂μ := by
  classical
  have := hU.isProbabilityMeasure
  have hlm : Fintype.card l ≤ Fintype.card m := hΩ₀ ▸ Matrix.rank_le_card_height Ω₀
  have hinj : Function.Injective Ω₀.mulVec := mulVec_injective_iff_rank_eq.mpr hΩ₀
  set W := polarFactor Ω₀
  have hW : HasOrthonormalCols W := hasOrthonormalCols_polarFactor_iff.mpr hinj
  obtain ⟨Rp, hRp, hWR⟩ : ∃ Rp : Matrix l l ℝ, IsUnit Rp ∧ W * Rp = Ω₀ := by
    open scoped MatrixOrder in
    exact ⟨_, (posDef_conjTranspose_mul_self_iff.mpr hinj).isUnit_sqrt, polarFactor_mul_sqrt Ω₀⟩
  have hQ : HasLaw (fun ω => (U ω)ᴴ * W) (haarFrame m l) μ :=
    hasLaw_mul_const_of_hasLaw_haarFrame (hasLaw_conjTranspose_of_hasLaw_haarFrame hU) le_rfl hW
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_compl_frames A B
  set E := (1 - rangeProjector A) * B
  have hrp : Fintype.card (Fin A.rank) + 2 ≤ Fintype.card l := by rwa [Fintype.card_fin]
  have hrs : Fintype.card (Fin A.rank) + Fintype.card (Fin (Fintype.card m - A.rank)) =
      Fintype.card m := by
    have := Matrix.rank_le_card_height A
    simp only [Fintype.card_fin]; omega
  have hae : ∀ᵐ ω ∂μ,
      frobNorm (U ω * B - U ω * A * sketchAndSolve (U ω * A) Ω₀ᴴ (U ω * B)) ^ 2 =
        frobNorm E ^ 2 + frobNorm (pinv (Rpᴴ * (((U ω)ᴴ * W)ᴴ * Q₁)) *
          (Rpᴴ * (((U ω)ᴴ * W)ᴴ * Q₂)) * (Q₂ᴴ * E)) ^ 2 := by
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hU le_rfl,
      ae_rank_mul_eq_min_of_hasLaw_haarFrame Aᴴ hQ] with ω hUω hrk
    set S := Rpᴴ * ((U ω)ᴴ * W)ᴴ
    have hS : Ω₀ᴴ * U ω = S := by
      simp only [S, ← hWR, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    have hSA : (S * A).rank = A.rank := by
      rw [show S * A = Rpᴴ * (Aᴴ * ((U ω)ᴴ * W))ᴴ by
          simp only [S, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc],
        Matrix.rank_mul_eq_right_of_isUnit_det Rpᴴ _
          ((Matrix.isUnit_iff_isUnit_det _).mp hRp.star),
        Matrix.rank_conjTranspose, hrk, Matrix.rank_conjTranspose, min_eq_left (by omega)]
    have hres : U ω * B - U ω * A * sketchAndSolve (U ω * A) Ω₀ᴴ (U ω * B) =
        U ω * ((1 - obliqueProjector A S) * B) := by
      rw [Matrix.sub_mul, Matrix.one_mul, ← mul_sketchAndSolve, sketchAndSolve, sketchAndSolve,
        ← Matrix.mul_assoc Ω₀ᴴ, ← Matrix.mul_assoc Ω₀ᴴ, hS, Matrix.mul_sub, Matrix.mul_assoc]
    rw [hres, hUω.frobNorm_mul_left, frobNorm_one_sub_obliqueProjector_mul_sq hSA,
      obliqueProjector_eq_of_range_eq hSA hR₁.symm, obliqueProjector]
    change frobNorm E ^ 2 + frobNorm (Q₁ * pinv (S * Q₁) * S * E) ^ 2 = _
    rw [← hQ₁.frobNorm_mul_left (pinv _ * _ * _)]
    conv_lhs => rw [← hE]
    simp only [S, Matrix.mul_assoc]
    rw [hE]
  have hint := integrable_frobNorm_pinv_conjTranspose_mul_mul_sq hQ hlm hQ₁ hQ₂ hrp (Q₂ᴴ * E) hRp
  have hW2 := mul_le_integral_frobNorm_pinv_conjTranspose_mul_mul_sq_of_hasLaw_haarFrame hQ hlm
    hQ₁ hQ₂ h₁₂ hrs hrp (Q₂ᴴ * E) hRp
  have hQE : frobNorm (Q₂ᴴ * E) = frobNorm E := by rw [← hQ₂.frobNorm_mul_left, hE]
  rw [integral_congr_ae hae, integral_add (integrable_const _) hint, integral_const,
    probReal_univ, one_smul, haarProjectionFactor_def]
  rw [hQE, Fintype.card_fin] at hW2
  linarith

/-- **Some rotation of the problem defeats a fixed sketch**: for a fixed sketch
$\mathbf{\Omega}_0 \in \mathbb{R}^{m \times \ell}$ of full column rank, $\mathbf{A} \in
\mathbb{R}^{m \times n}$
with $r = \operatorname{rank}\mathbf{A}$, $r + 2 \le \ell$ and any $\mathbf{B}$, there is an
orthogonal
$\mathbf{U}$ with <!-- value haarProjectionFactor m \ell r -->
$$\Bigl(1 + \frac{m - \ell}{m - r}\cdot\frac{r}{\ell - r - 1}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{B}\|_{\mathsf{F}}^2 \le
\|\mathbf{U}\mathbf{B} - \mathbf{U}\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{U}\mathbf{A},
\mathbf{\Omega}_0^{\mathsf{H}}, \mathbf{U}\mathbf{B})\|_{\mathsf{F}}^2\,.$$
[EpperlyWebber2026, Theorem 2.2]; there for a random sketch.
Proof: S, about 20 lines. Apply
`le_integral_frobNorm_mul_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame` on the probability space
`haarFrame m m` with `U = id`; an integrable function exceeds its mean somewhere on a set of
positive measure (`MeasureTheory.exists_notMem_null_integral_le`, with $N$ the null set of
non-orthogonal samples), and almost every sample is orthogonal
(`ae_hasOrthonormalCols_of_hasLaw_haarFrame`). -/
theorem exists_hasOrthonormalCols_le_frobNorm_mul_sub_mul_sketchAndSolve_sq {r' : Type*}
    [Fintype r'] {Ω₀ : Matrix m l ℝ} (hΩ₀ : Ω₀.rank = Fintype.card l) {A : Matrix m n ℝ}
    (hA : A.rank + 2 ≤ Fintype.card l) (B : Matrix m r' ℝ) :
    ∃ U : Matrix m m ℝ, HasOrthonormalCols U ∧
      haarProjectionFactor (Fintype.card m) (Fintype.card l) A.rank *
          frobNorm ((1 - rangeProjector A) * B) ^ 2 ≤
        frobNorm (U * B - U * A * sketchAndSolve (U * A) Ω₀ᴴ (U * B)) ^ 2 := by
  by_contra hcon
  push Not at hcon
  set c := haarProjectionFactor (Fintype.card m) (Fintype.card l) A.rank *
    frobNorm ((1 - rangeProjector A) * B) ^ 2 with hc
  set f : Matrix m m ℝ → ℝ := fun U =>
    frobNorm (U * B - U * A * sketchAndSolve (U * A) Ω₀ᴴ (U * B)) ^ 2 with hf
  have hU := HasLaw.id (μ := haarFrame m m)
  have hW : c ≤ ∫ U, f U ∂haarFrame m m :=
    le_integral_frobNorm_mul_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame hU hΩ₀ hA B
  have hae : ∀ᵐ U ∂haarFrame m m, HasOrthonormalCols U :=
    ae_hasOrthonormalCols_of_hasLaw_haarFrame hU le_rfl
  have hlt : ∀ᵐ U ∂haarFrame m m, f U < c := hae.mono fun U hU' => hcon U hU'
  have hc0 : 0 < c := by
    have h1 := hcon 1 NLAlib.hasOrthonormalCols_one
    have h2 : 0 ≤ f 1 := by simp only [hf]; positivity
    linarith
  have hint : Integrable f (haarFrame m m) := by
    by_contra hni
    rw [integral_undef hni] at hW
    linarith
  have hsub : ∫ U, (c - f U) ∂haarFrame m m = c - ∫ U, f U ∂haarFrame m m := by
    rw [integral_sub (integrable_const c) hint, integral_const, probReal_univ, one_smul]
  have hnn : 0 ≤ ∫ U, (c - f U) ∂haarFrame m m :=
    integral_nonneg_of_ae (hlt.mono fun U h => sub_nonneg.2 h.le)
  have hg0 : ∫ U, (c - f U) ∂haarFrame m m = 0 := by linarith
  have heq := (integral_eq_zero_iff_of_nonneg_ae
    (hlt.mono fun U h => sub_nonneg.2 h.le) (integrable_const c |>.sub hint)).1 hg0
  have hfc : ∀ᵐ U ∂haarFrame m m, f U = c := heq.mono fun U h => by
    simp only [Pi.zero_apply] at h
    linarith
  obtain ⟨U, h1, h2⟩ := (hlt.and hfc).exists
  linarith

/-- **No random sketch beats a random orthonormal one** (Epperly and Webber's minimax lower bound
for sketch-and-solve): for a random sketch $\mathbf{\Omega} \in \mathbb{R}^{m \times \ell}$ of any
law with full column rank almost surely, $\mathbf{A} \in \mathbb{R}^{m \times n}$ with
$r = \operatorname{rank}\mathbf{A}$, $r + 2 \le \ell$ and any $\mathbf{B}$, there is an orthogonal
$\mathbf{U}$ with <!-- value haarProjectionFactor m \ell r -->
$$\Bigl(1 + \frac{m - \ell}{m - r}\cdot\frac{r}{\ell - r - 1}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{B}\|_{\mathsf{F}}^2 \le
\mathbb{E}\|\mathbf{U}\mathbf{B} -
\mathbf{U}\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{U}\mathbf{A},
\mathbf{\Omega}^{\mathsf{H}}, \mathbf{U}\mathbf{B})\|_{\mathsf{F}}^2\,,$$
in extended reals (the expectation may be infinite). With
`NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame` (equality for a Haar
sketch): the random orthonormal sketch is minimax optimal.
[EpperlyWebber2026, Theorem 2.2]; there as a supremum over problems of rank $r$.
Proof: M, about 50 lines. Tonelli on $\mu \otimes$ `haarFrame m m` (`lintegral_lintegral_swap`,
measurability of the integrand from `measurable_pinv`-type lemmas): for almost every $\omega$
the inner Haar average is at least the factor
(`le_integral_frobNorm_mul_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame` with
`ofReal_integral_eq_lintegral_ofReal`), so the double integral is; then some $\mathbf{U}$ in the
support has $\int^-$ at least the factor (`exists_le_lintegral`-type argument on the Haar
probability space, by contradiction if every $\mathbf{U}$ is below; the value $\infty$ is
harmless), and a.e. $\mathbf{U}$ is orthogonal.
Result: sketch-and-solve-lower-bound -/
theorem exists_hasOrthonormalCols_le_lintegral_frobNorm_mul_sub_mul_sketchAndSolve_sq
    {r' : Type*} [Fintype r'] [IsProbabilityMeasure μ] {X : Ω → Matrix m l ℝ}
    (hX : AEMeasurable X μ) (hXr : ∀ᵐ ω ∂μ, (X ω).rank = Fintype.card l) {A : Matrix m n ℝ}
    (hA : A.rank + 2 ≤ Fintype.card l) (B : Matrix m r' ℝ) :
    ∃ U : Matrix m m ℝ, HasOrthonormalCols U ∧
      ENNReal.ofReal (haarProjectionFactor (Fintype.card m) (Fintype.card l) A.rank *
          frobNorm ((1 - rangeProjector A) * B) ^ 2) ≤
        ∫⁻ ω, ENNReal.ofReal
          (frobNorm (U * B - U * A * sketchAndSolve (U * A) (X ω)ᴴ (U * B)) ^ 2) ∂μ := by
  set c := haarProjectionFactor (Fintype.card m) (Fintype.card l) A.rank *
    frobNorm ((1 - rangeProjector A) * B) ^ 2
  set g : Matrix m m ℝ × Matrix m l ℝ → ℝ := fun p =>
    frobNorm (p.1 * B - p.1 * A * sketchAndSolve (p.1 * A) p.2ᴴ (p.1 * B)) ^ 2 with hg_def
  have hg : Measurable g := by
    have hS : Measurable fun p : Matrix m m ℝ × Matrix m l ℝ => p.2ᴴ :=
      Measurable.matrix_conjTranspose continuous_star.measurable measurable_snd
    have hU : Measurable fun p : Matrix m m ℝ × Matrix m l ℝ => p.1 := measurable_fst
    have hUA := hU.matrix_mul (measurable_const (a := A))
    have hUB := hU.matrix_mul (measurable_const (a := B))
    exact (continuous_frobNorm.measurable.comp (hUB.sub (hUA.matrix_mul
      ((measurable_pinv.comp (hS.matrix_mul hUA)).matrix_mul (hS.matrix_mul hUB))))).pow_const 2
  have h1 : ∀ᵐ ω ∂μ, ENNReal.ofReal c ≤
      ∫⁻ u, ENNReal.ofReal (g (u, X ω)) ∂(haarFrame m m) := by
    filter_upwards [hXr] with ω hω
    refine ENNReal.ofReal_le_of_le_toReal ?_
    rw [← integral_eq_lintegral_of_nonneg_ae (f := fun u => g (u, X ω))
      (ae_of_all _ fun u => sq_nonneg _)
      (hg.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable]
    exact le_integral_frobNorm_mul_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame HasLaw.id hω hA B
  have h2 : ENNReal.ofReal c ≤ ∫⁻ u, ∫⁻ ω, ENNReal.ofReal (g (u, X ω)) ∂μ ∂(haarFrame m m) := by
    rw [← lintegral_lintegral_swap]
    · calc ENNReal.ofReal c = ∫⁻ _, ENNReal.ofReal c ∂μ := by simp
        _ ≤ _ := lintegral_mono_ae h1
    · exact (ENNReal.measurable_ofReal.comp hg).comp_aemeasurable
        (measurable_snd.aemeasurable.prodMk hX.comp_fst)
  by_contra hcon
  push Not at hcon
  have h3 : ∀ᵐ u ∂(haarFrame m m), ∫⁻ ω, ENNReal.ofReal (g (u, X ω)) ∂μ < ENNReal.ofReal c := by
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame HasLaw.id le_rfl] with u hu
    exact hcon u hu
  refine (lt_irrefl _ (h2.trans_lt ?_))
  calc _ < ∫⁻ _, ENNReal.ofReal c ∂(haarFrame m m) :=
        lintegral_strict_mono (IsProbabilityMeasure.ne_zero _) aemeasurable_const
          ((lintegral_mono_ae (h3.mono fun _ h => h.le)).trans_lt (by simp)).ne h3
    _ = ENNReal.ofReal c := by simp

end NLAlib
