/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Haar.Blocks
public import NLAlib.Regression.SketchAndSolve

/-!
# No sketch beats a random orthonormal one for sketch-and-solve

Epperly and Webber's minimax lower bound for sketch-and-solve (their Theorem 2.2): for every sketch
with full column rank, some rotation of any least-squares problem with
$\operatorname{rank}\mathbf{A} = r$ has expected sketch-and-solve residual at least the random
orthonormal factor <!-- value haarProjectionFactor m \ell r -->
$1 + (m - \ell)/(m - r) \cdot (r/(\ell - r - 1))$ times the optimum, which is the exact value
for a Haar sketch (`NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame`). Three
forms: averaged over a Haar rotation for a fixed sketch, a single rotation for a fixed sketch, and a
single rotation for a random sketch of any law (in `lintegral`, since the expectation may be
infinite). The deterministic step is
`NLAlib.frobNorm_pinv_le_frobNorm_pinv_conjTranspose_mul_mul_conjTranspose` (a weight does not
shrink the pseudoinverse) through
`NLAlib.mul_le_integral_frobNorm_pinv_conjTranspose_mul_mul_sq_of_hasLaw_haarFrame`. Design:
`docs/design/LowRank-EstimatorLowerBounds.md` §3.3.

## Main results

* `NLAlib.le_integral_frobNorm_mul_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame`: a fixed sketch
  against a Haar rotation of the problem.
* `NLAlib.exists_hasOrthonormalCols_le_frobNorm_mul_sub_mul_sketchAndSolve_sq`: one rotation.
* `NLAlib.exists_hasOrthonormalCols_le_lintegral_frobNorm_mul_sub_mul_sketchAndSolve_sq`: a random
  sketch of any law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l r : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype r] [DecidableEq m]

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
here averaged over the rotation for a fixed one (the core of their proof). -/
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
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl A B
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
  have hint := integrable_frobNorm_pinv_conjTranspose_mul_mul_sq_of_hasLaw_haarFrame hQ hlm hQ₁ hQ₂
    hrp (Q₂ᴴ * E) hRp
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
[EpperlyWebber2026, Theorem 2.2]; there for a random sketch. -/
theorem exists_hasOrthonormalCols_le_frobNorm_mul_sub_mul_sketchAndSolve_sq {r' : Type*}
    [Fintype r'] {Ω₀ : Matrix m l ℝ} (hΩ₀ : Ω₀.rank = Fintype.card l) {A : Matrix m n ℝ}
    (hA : A.rank + 2 ≤ Fintype.card l) (B : Matrix m r' ℝ) :
    ∃ U : Matrix m m ℝ, HasOrthonormalCols U ∧
      haarProjectionFactor (Fintype.card m) (Fintype.card l) A.rank *
          frobNorm ((1 - rangeProjector A) * B) ^ 2 ≤
        frobNorm (U * B - U * A * sketchAndSolve (U * A) Ω₀ᴴ (U * B)) ^ 2 := by
  have hU := HasLaw.id (μ := haarFrame m m)
  have hW := le_integral_frobNorm_mul_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame hU hΩ₀ hA B
  simp only [id] at hW
  by_cases hint : Integrable (fun U : Matrix m m ℝ =>
      frobNorm (U * B - U * A * sketchAndSolve (U * A) Ω₀ᴴ (U * B)) ^ 2) (haarFrame m m)
  · obtain ⟨U, hU', hle⟩ := exists_notMem_null_integral_le hint
      (ae_iff.mp (ae_hasOrthonormalCols_of_hasLaw_haarFrame hU le_rfl))
    exact ⟨U, not_not.mp hU', hW.trans hle⟩
  · rw [integral_undef hint] at hW
    exact ⟨1, hasOrthonormalCols_one, hW.trans (sq_nonneg _)⟩

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
