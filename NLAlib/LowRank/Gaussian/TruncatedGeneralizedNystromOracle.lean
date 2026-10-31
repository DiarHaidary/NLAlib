/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.TruncatedGeneralizedNystrom

/-!
# Truncated generalized Nyström: the dominant-subspace noise and the oracle truncation

Exact Gaussian expectations behind the lower bound for truncated generalized Nyström: for
independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$, the Lean `X`)
and $\mathbf{\Psi}$ ($m \times p$), the core noise of generalized Nyström in the dominant rank-$k$
subspace of the randomized SVD, and the expected error of the oracle truncation that keeps that
subspace. Split from `NLAlib.LowRank.Gaussian.TruncatedGeneralizedNystrom` (the expected error of
the late truncation). Real throughout.

## Main results

* `NLAlib.integral_frobNorm_rangeProjector_mul_obliqueProjector_sq_of_hasLaw_gaussianMatrix`: the
  core noise in the dominant rank-$k$ subspace of the randomized SVD has mean
  $k/(p - \ell - 1)$ times the range-finder error, exactly.
* `NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_of_hasLaw_gaussianMatrix`:
  the oracle truncation's expected error, exactly, and its bound
  `integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_le_of_hasLaw_gaussianMatrix`.
  Both are new; they feed the lower bound
  `NLAlib.LowerBounds.LowRank.TruncatedGeneralizedNystrom`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l p : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype p] {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}

/-! ### The noise in the dominant subspace and the oracle truncation -/

section Oracle

/-- Almost surely $\|\mathbf{G}^{+}\mathbf{M}\|_{\mathsf{F}}^2 =
\operatorname{tr}(\mathbf{M}^{\mathsf{H}}(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}\mathbf{M})$ for a
standard Gaussian $r \times k$ matrix $\mathbf{G}$ with $\lvert r \rvert \le \lvert k \rvert$. -/
private theorem ae_frobNorm_pinv_mul_sq_eq_trace {r k a : Type*} [Fintype r] [Fintype k]
    [Fintype a] [DecidableEq r] {Y : Ω → Matrix r k ℝ} (hY : HasLaw Y (gaussianMatrix r k) μ)
    (hrk : Fintype.card r ≤ Fintype.card k) (M : Matrix r a ℝ) :
    ∀ᵐ ω ∂μ, frobNorm (pinv (Y ω) * M) ^ 2 = (Mᴴ * (Y ω * (Y ω)ᴴ)⁻¹ * M).trace := by
  filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hY] with ω hω
  have hu : IsUnit (Y ω * (Y ω)ᴴ) := by
    have h := (isUnit_conjTranspose_mul_self_iff_rank (A := (Y ω)ᴴ)).2
      (by rw [Matrix.rank_conjTranspose, hω, min_eq_left hrk])
    rwa [Matrix.conjTranspose_conjTranspose] at h
  rw [frobNorm_sq_eq_re_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ M,
    ← pinv_mul_conjTranspose_self, pinv_of_isUnit hu, ← Matrix.mul_assoc, RCLike.re_to_real]

open scoped Matrix.Norms.L2Operator in
/-- The weighted inverse moment: $\mathbb{E}\|\mathbf{G}^{+}\mathbf{M}\|_{\mathsf{F}}^2 =
\|\mathbf{M}\|_{\mathsf{F}}^2/(\lvert k \rvert - \lvert r \rvert - 1)$, with integrability. -/
private theorem integral_frobNorm_pinv_mul_sq {r k a : Type*} [Fintype r] [Fintype k]
    [Fintype a] {Y : Ω → Matrix r k ℝ} (hY : HasLaw Y (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) (M : Matrix r a ℝ) :
    Integrable (fun ω => frobNorm (pinv (Y ω) * M) ^ 2) μ ∧
      ∫ ω, frobNorm (pinv (Y ω) * M) ^ 2 ∂μ =
        frobNorm M ^ 2 / ((Fintype.card k : ℝ) - Fintype.card r - 1) := by
  classical
  have := hY.isProbabilityMeasure
  have hZ := integrable_mul_conjTranspose_inv_of_hasLaw_gaussianMatrix hY hrk
  have hZ' := Matrix.integrable_iff.1 hZ
  have hMZ : Integrable (fun ω => Mᴴ * (Y ω * (Y ω)ᴴ)⁻¹ * M) μ := by
    refine Matrix.integrable_iff.2 fun i j => ?_
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun b _ => (integrable_finsetSum _ fun c _ =>
      (hZ' c b).const_mul _).mul_const _
  have htr : Integrable (fun ω => (Mᴴ * (Y ω * (Y ω)ᴴ)⁻¹ * M).trace) μ :=
    integrable_finsetSum _ fun i _ => Matrix.integrable_iff.1 hMZ i i
  have hae := ae_frobNorm_pinv_mul_sq_eq_trace hY (by omega) M
  refine ⟨htr.congr (hae.mono fun _ h => h.symm), ?_⟩
  rw [integral_congr_ae hae, Matrix.integral_trace hMZ, Matrix.integral_mul_const
    (Matrix.integrable_iff.2 fun i j => by
      simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun c _ => (hZ' c j).const_mul _) M,
    Matrix.integral_const_mul _ hZ,
    integral_mul_conjTranspose_inv_of_hasLaw_gaussianMatrix hY hrk, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, frobNorm_sq_eq_re_trace, RCLike.re_to_real,
    div_eq_inv_mul]

/-- The Gaussian block with a left factor, conjugate-transposed. -/
private theorem frobNorm_mul_pinv_mul_mul_eq {r s c a : Type*} [Fintype r] [Fintype s]
    [Fintype c] [Fintype a] (G : Matrix m p ℝ) (V₁ : Matrix m r ℝ) (V₂ : Matrix m s ℝ)
    (T : Matrix c r ℝ) (W : Matrix s a ℝ) :
    frobNorm (T * pinv (Gᴴ * V₁) * (Gᴴ * V₂) * W) =
      frobNorm (Wᴴ * (V₂ᴴ * G) * (pinv (V₁ᴴ * G) * Tᴴ)) := by
  rw [← frobNorm_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← pinv_conjTranspose,
    Matrix.mul_assoc]

/-- The Gaussian block with a fixed left factor: for frames $\mathbf{V}_1$, $\mathbf{V}_2$ with
$\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$,
$\mathbb{E}\|\mathbf{T}(\mathbf{G}^{\mathsf{H}}\mathbf{V}_1)^{+}
(\mathbf{G}^{\mathsf{H}}\mathbf{V}_2)\mathbf{W}\|_{\mathsf{F}}^2 =
\|\mathbf{T}\|_{\mathsf{F}}^2\|\mathbf{W}\|_{\mathsf{F}}^2/(\lvert p \rvert - \lvert r \rvert - 1)$,
with integrability. -/
private theorem integral_frobNorm_mul_pinv_mul_mul_sq {r s c a : Type*} [Fintype r] [Fintype s]
    [Fintype c] [Fintype a] [DecidableEq r] [DecidableEq s] {G : Ω → Matrix m p ℝ}
    (hG : HasLaw G (gaussianMatrix m p) μ) {V₁ : Matrix m r ℝ} {V₂ : Matrix m s ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0)
    (hrk : Fintype.card r + 2 ≤ Fintype.card p) (T : Matrix c r ℝ) (W : Matrix s a ℝ) :
    Integrable (fun ω => frobNorm (T * pinv ((G ω)ᴴ * V₁) * ((G ω)ᴴ * V₂) * W) ^ 2) μ ∧
      ∫ ω, frobNorm (T * pinv ((G ω)ᴴ * V₁) * ((G ω)ᴴ * V₂) * W) ^ 2 ∂μ =
        frobNorm W ^ 2 * (frobNorm T ^ 2 / ((Fintype.card p : ℝ) - Fintype.card r - 1)) := by
  simp only [frobNorm_mul_pinv_mul_mul_eq]
  have hY := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hG hV₁
  have hX := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hG hV₂
  have hI := indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hG hV₁ hV₂ h₁₂
  have hT : Measurable fun y : Matrix r p ℝ => pinv y * Tᴴ := measurable_pinv.matrix_mul
    measurable_const
  obtain ⟨hint, hval⟩ := integral_frobNorm_pinv_mul_sq hY hrk Tᴴ
  refine ⟨(integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun hX
    hY.aemeasurable hI (S := fun _ => Wᴴ) measurable_const hT).2 (hint.const_mul _), ?_⟩
  rw [integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun hX hY.aemeasurable hI
    (S := fun _ => Wᴴ) measurable_const hT, integral_const_mul, hval, frobNorm_conjTranspose,
    frobNorm_conjTranspose]

/-- Fixed range test matrix: for $\mathbf{F}$ with
$\mathbf{F}\mathbf{P}_{\mathbf{A}\mathbf{\Omega}} = \mathbf{F}$ and
$q = \operatorname{rank}(\mathbf{A}\mathbf{\Omega})$, $q + 2 \le p$,
$\mathbb{E}_{\mathbf{\Psi}}\|\mathbf{F}\mathbf{N}\|_{\mathsf{F}}^2 =
\|\mathbf{F}\|_{\mathsf{F}}^2/(p - q - 1) \cdot \|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2$,
with integrability. -/
private theorem integral_frobNorm_mul_obliqueProjector_sq_of_fixed {c : Type*} [Fintype c]
    (A : Matrix m n ℝ) (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hr : (A * X₀).rank + 2 ≤ Fintype.card p) (F : Matrix c m ℝ)
    (hF : F * rangeProjector (A * X₀) = F) :
    Integrable (fun ω => frobNorm (F * (obliqueProjector (A * X₀) (Ψ ω)ᴴ *
      (A - rsvd A X₀))) ^ 2) μ ∧
      ∫ ω, frobNorm (F * (obliqueProjector (A * X₀) (Ψ ω)ᴴ * (A - rsvd A X₀))) ^ 2 ∂μ =
        frobNorm F ^ 2 / ((Fintype.card p : ℝ) - (A * X₀).rank - 1) *
          frobNorm (A - rsvd A X₀) ^ 2 := by
  classical
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl (A * X₀) A
  have hrk : Fintype.card (Fin (A * X₀).rank) + 2 ≤ Fintype.card p := by rwa [Fintype.card_fin]
  obtain ⟨hint, hval⟩ := integral_frobNorm_mul_pinv_mul_mul_sq hΨ hQ₁ hQ₂ h₁₂ hrk (F * Q₁)
    (Q₂ᴴ * ((1 - rangeProjector (A * X₀)) * A))
  have hae : ∀ᵐ ω ∂μ, frobNorm (F * (obliqueProjector (A * X₀) (Ψ ω)ᴴ *
      (A - rsvd A X₀))) ^ 2 = frobNorm (F * Q₁ * pinv ((Ψ ω)ᴴ * Q₁) * ((Ψ ω)ᴴ * Q₂) *
        (Q₂ᴴ * ((1 - rangeProjector (A * X₀)) * A))) ^ 2 := by
    filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix (A * X₀) hΨ
      (by omega)] with ω hω
    rw [sub_rsvd, obliqueProjector_eq_of_range_eq hω hR₁.symm, obliqueProjector]
    conv_lhs => rw [← hE]
    simp only [Matrix.mul_assoc]
  have hFQ : frobNorm (F * Q₁) = frobNorm F := by
    rw [← frobNorm_conjTranspose, ← hQ₁.frobNorm_mul_left, ← frobNorm_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← hQ₁.rangeProjector_eq, rangeProjector_inj.mpr hR₁, hF]
  have hW : frobNorm (Q₂ᴴ * ((1 - rangeProjector (A * X₀)) * A)) = frobNorm (A - rsvd A X₀) := by
    rw [← hQ₂.frobNorm_mul_left, hE, sub_rsvd]
  refine ⟨hint.congr (hae.mono fun _ h => h.symm), ?_⟩
  rw [integral_congr_ae hae, hval, hFQ, hW, Fintype.card_fin]
  ring

/-- The squared core noise in the dominant subspace is measurable in the pair. -/
private theorem measurable_frobNorm_rangeProjector_mul_obliqueProjector_sq (A : Matrix m n ℝ)
    (k : ℕ) : Measurable fun q : Matrix n l ℝ × Matrix m p ℝ =>
      frobNorm (rangeProjector (truncatedSVD (rsvd A q.1) k) *
        (obliqueProjector (A * q.1) q.2ᴴ * (A - rsvd A q.1))) ^ 2 :=
  (continuous_frobNorm.measurable.comp ((measurable_rangeProjector.comp
    (((measurable_truncatedSVD k).comp (measurable_rsvd A)).comp measurable_fst)).matrix_mul
      (measurable_obliqueProjector_mul_sub_rsvd A))).pow_const 2

/-- The rank of the truncated randomized SVD is $k$ once the sketch has rank $\ge k$. -/
private theorem rank_truncatedSVD_rsvd (A : Matrix m n ℝ) (x : Matrix n l ℝ) {k : ℕ}
    (hk : k ≤ (A * x).rank) : (truncatedSVD (rsvd A x) k).rank = k := by
  classical
  have h : (A * x).rank ≤ (rsvd A x).rank := by
    have := Matrix.rank_mul_le_left (rsvd A x) x
    rwa [rsvd, Matrix.mul_assoc, rangeProjector_mul_self] at this
  rw [rank_truncatedSVD, min_eq_left (hk.trans h)]

/-- The core noise in the dominant subspace: for independent standard Gaussian test
matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$), $k \le \ell$,
$\ell + 2 \le p$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ and
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$,
$$\mathbb{E}\|\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}\|_{\mathsf{F}}^2 =
\frac{k}{p - \ell - 1}\,\mathbb{E}\|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2\,.$$
Every rank of $\mathbf{A}$: if $\operatorname{rank}\mathbf{A} < \ell$ both sides vanish
($\mathbf{R} = \mathbf{A}$ almost surely). For the choice `truncatedSVD` makes.
No printed source. New. -/
theorem integral_frobNorm_rangeProjector_mul_obliqueProjector_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkl : k ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
        (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2 ∂μ =
      k / ((Fintype.card p : ℝ) - Fintype.card l - 1) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  classical
  have := hΨ.isProbabilityMeasure
  rcases lt_or_ge A.rank (Fintype.card l) with hA | hA
  · have h0 := ae_rsvd_eq_self_of_hasLaw_gaussianMatrix A hX hA.le
    rw [integral_eq_zero_of_ae (h0.mono fun ω h => by
        simp only [h, sub_self, Matrix.mul_zero, frobNorm_zero, Pi.zero_apply]; norm_num),
      integral_eq_zero_of_ae (h0.mono fun ω h => by
        simp only [h, sub_self, frobNorm_zero, Pi.zero_apply]; norm_num), mul_zero]
  have hrk : ∀ᵐ ω ∂μ, (A * X ω).rank = Fintype.card l :=
    (ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix A hX).mono fun ω h => by rw [h, min_eq_right hA]
  have hF (x : Matrix n l ℝ) : rangeProjector (truncatedSVD (rsvd A x) k) *
      rangeProjector (A * x) = rangeProjector (truncatedSVD (rsvd A x) k) :=
    rangeProjector_mul_rangeProjector_of_range_le'
      ((range_truncatedSVD_le _ k).trans (range_rsvd_le A x))
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  have hc : 0 ≤ (k : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) := by
    have : (Fintype.card l : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hlp
    exact div_nonneg (Nat.cast_nonneg k) (by linarith)
  have hm := measurable_frobNorm_rangeProjector_mul_obliqueProjector_sq A k (l := l) (p := p)
  rw [← integral_const_mul, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      (hm.comp_aemeasurable (hX.aemeasurable.prodMk hΨ.aemeasurable)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => mul_nonneg hc (sq_nonneg _))
      ((integrable_frobNorm_sub_rsvd_sq A hX.aemeasurable).const_mul _).aestronglyMeasurable]
  congr 1
  refine (hXΨ.lintegral_ofReal_comp_eq_lintegral_ofReal_integral hX.aemeasurable hΨ hm
    (fun _ => sq_nonneg _) (hrk.mono fun ω hω =>
      (integral_frobNorm_mul_obliqueProjector_sq_of_fixed A (X ω) hid (by omega) _
        (hF (X ω))).1)).trans (lintegral_congr_ae (hrk.mono fun ω hω => ?_))
  dsimp only
  rw [(integral_frobNorm_mul_obliqueProjector_sq_of_fixed A (X ω) hid (by omega) _
    (hF (X ω))).2, frobNorm_rangeProjector_sq, rank_truncatedSVD_rsvd A (X ω) (by omega), hω]

/-- The oracle-truncated generalized Nyström error, exactly: for independent standard Gaussian
test matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$), $k \le \ell$,
$\ell + 2 \le p$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$,
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$
and the oracle truncation $\widehat{\mathbf{A}} = \llbracket\mathbf{R}\rrbracket_k +
\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}$ (truncation in the dominant subspace of
$\mathbf{R}$ instead of that of $\mathsf{gn}$; not computable from the sketches),
$$\mathbb{E}\|\mathbf{A} - \widehat{\mathbf{A}}\|_{\mathsf{F}}^2 =
\mathbb{E}\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2 +
\frac{k}{p - \ell - 1}\,\mathbb{E}\|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2\,.$$
The noise costs $k/(p - \ell - 1)$, not $\ell/(p - \ell - 1)$: what truncated generalized Nyström
loses beyond this is the misalignment of its truncation subspace.
No printed source. New. -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkl : k ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k -
        rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
          (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2 ∂μ =
      ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ +
        k / ((Fintype.card p : ℝ) - Fintype.card l - 1) *
          ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  classical
  have := hΨ.isProbabilityMeasure
  have hpt (ω : Ω) : frobNorm (A - truncatedSVD (rsvd A (X ω)) k -
      rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
        (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2 =
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
        frobNorm (rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
          (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2 := by
    refine frobNorm_sub_sq_of_frobInner_eq_zero ?_
    -- the cross term vanishes pointwise: `P (A - T) = P A - T = 0` with `T = P A`
    rw [frobInner_comm, frobInner_mul_left, conjTranspose_rangeProjector,
      Matrix.mul_sub (rangeProjector _), rangeProjector_mul_self,
      ← truncatedSVD_rsvd_eq_rangeProjector_mul, sub_self, frobInner_zero_right]
  have hT := (measurable_truncatedSVD k).comp (measurable_rsvd (l := l) A)
  have hf := integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX.aemeasurable k
  have hN := measurable_obliqueProjector_mul_sub_rsvd (l := l) (p := p) A
  have hgn := integrable_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix A
    hX.aemeasurable hΨ hXΨ
    (ae_of_all _ fun ω => by have := Matrix.rank_le_card_width (A * X ω); omega)
  have hg : Integrable (fun ω => frobNorm (rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
      (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2) μ := by
    refine hgn.mono' (((continuous_frobNorm.measurable.comp
      ((measurable_rangeProjector.comp (hT.comp measurable_fst)).matrix_mul hN)).pow_const
        2).comp_aemeasurable (hX.aemeasurable.prodMk hΨ.aemeasurable)).aestronglyMeasurable ?_
    filter_upwards [ae_rank_conjTranspose_mul_mul_eq A hX.aemeasurable hΨ hXΨ
      (fun x => by have := Matrix.rank_le_card_width (A * x); omega)] with ω hω
    rw [Real.norm_of_nonneg (sq_nonneg _), frobNorm_sub_generalizedNystrom_sq hω]
    have h := (isStarProjection_rangeProjector (truncatedSVD (rsvd A (X ω)) k)).frobNorm_mul_le
      (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))
    nlinarith [frobNorm_nonneg (rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
      (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))),
      sq_nonneg (frobNorm (A - rsvd A (X ω)))]
  rw [← integral_frobNorm_rangeProjector_mul_obliqueProjector_sq_of_hasLaw_gaussianMatrix A hX hΨ
    hXΨ hkl hlp, ← integral_add hf hg]
  exact integral_congr_ae (ae_of_all _ hpt)

/-- The expected error of the oracle truncation: for
independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and
$\mathbf{\Psi}$ ($m \times p$), $k + 2 \le \ell$, $\ell + 2 \le p$,
$\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$,
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$
and $\widehat{\mathbf{A}} = \llbracket\mathbf{R}\rrbracket_k +
\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}$,
so <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A} - \widehat{\mathbf{A}}\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\Bigl(1 + \frac{k}{p - \ell - 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
A statement about an analysis device, not an algorithm: the dominant subspace of $\mathbf{R}$
is not available from the two sketches, so this says nothing about what an estimator built from
them can reach. It separates the two losses of truncated generalized Nyström: the noise in a
fixed rank-$k$ subspace costs $k/(p - \ell - 1)$; the rest is the misalignment of the data-driven
truncation subspace.
No printed source. New. -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkl : k + 2 ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k -
        rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
          (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) *
        (1 + k / ((Fintype.card p : ℝ) - Fintype.card l - 1)) *
          frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  have hc : 0 ≤ (k : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) := by
    apply div_nonneg (Nat.cast_nonneg _)
    have : (Fintype.card l : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hlp
    linarith
  have hI := integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_of_hasLaw_gaussianMatrix
    A hX hΨ hXΨ (k := k) (by omega) hlp
  have hmono : ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ :=
    integral_mono (integrable_frobNorm_sub_rsvd_sq A hX.aemeasurable)
      (integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX.aemeasurable k) fun ω => by
        rw [frobNorm_sub_truncatedSVD_rsvd_sq]
        exact le_add_of_nonneg_right (sq_nonneg _)
  have h2 := integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX (k := k)
    (by omega)
  have h3 := mul_le_mul_of_nonneg_left hmono hc
  have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 + k / ((Fintype.card p : ℝ) -
    Fintype.card l - 1))
  rw [hI]
  nlinarith [h3, h4]

end Oracle

end NLAlib
