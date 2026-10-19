/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.LowRank.Structural.Filter

/-!
# The filtered range finder with a Gaussian test matrix

The expected error of the randomized SVD at a polynomially filtered Gaussian test matrix
$f(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{X}$, for $\mathbf{X}$ a standard Gaussian
$n \times \ell$ matrix. The filter is described by two numbers: a lower bound $c > 0$ on
$\lvert f \rvert$ at the squared singular values $\sigma_i(\mathbf{A})^2$ of the head, $i < r$,
and an upper bound $a$ on $\lvert f \rvert$ on the interval $[0, \sigma_t(\mathbf{A})^2]$ that
contains the tail, $r \le t$ and $t + 2 \le \ell$. Then
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, f(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{X})
\|_2^2 \le \sigma_r(\mathbf{A})^2 + \Bigl(\frac{a}{c}\Bigr)^2 \frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
and likewise in the Frobenius norm and every quadratic unitarily invariant norm. Randomized
subspace iteration and randomized block Krylov iteration are instances
(`NLAlib.LowRank.Gaussian.BlockKrylov`).

Indices from $0$: the head is $\sigma_0, \dots, \sigma_{r-1}$ and $\sigma_r$ is the first
singular value not captured; the tail interval $[0, \sigma_t^2]$ also covers the zero padding of
the singular values, so no hypothesis on the shape of $\mathbf{A}$ is needed. Integrability of
the errors is `NLAlib.integrable_specNorm_sub_rsvd_sq` and its siblings at the test matrix
$f(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{X}$.

## Main results

* the Gram form, every quadratic unitarily invariant norm, in the `NLAlib.SymmetricGauge`
  namespace:
  `integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_aeval_le_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_specNorm_sub_rsvd_aeval_sq_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_rsvd_aeval_sq_le_of_hasLaw_gaussianMatrix`: spectral and Frobenius.
* `NLAlib.integral_frobNorm_one_sub_rangeProjector_mul_truncatedSVD_sq_le_of_hasLaw_gaussianMatrix`:
  head capture in expectation, for the truncated outputs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Polynomial
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] [DecidableEq n] {X : Ω → Matrix n l ℝ}

-- Stage B5a

/-- The sketch residual of the filtered range finder in expectation, for $t \le \lvert n \rvert$:
with the nested frames of
`NLAlib.exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal` at $k = t$
(head $\mathbf{W} = \mathbf{Z}_r$, tail $\mathbf{V}$), the residual
$\mathbf{M} = (\mathbf{B}\mathbf{V})(\mathbf{V}^{\mathsf{H}}\mathbf{X})
(\mathbf{Z}^{\mathsf{H}}\mathbf{X})^{+}$,
$\mathbf{B} = \mathbf{A}f(\mathbf{A}^{\mathsf{H}}\mathbf{A})$, has
$\mathbb{E}\|\mathbf{M}\|_{\mathsf{F}}^2 \le a^2 (t/(\ell - t - 1))
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2$ and bounds, almost surely, the
Gram-form error and the head capture of the deterministic filtered range finder. -/
private theorem exists_filter_residual [DecidableEq m] (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (f : ℝ[X]) {r t : ℕ} (hrt : r ≤ t)
    (htn : t ≤ Fintype.card n) (ht : t + 2 ≤ Fintype.card l) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a) :
    ∃ M : Ω → Matrix m (Fin t) ℝ, Integrable (fun ω => frobNorm (M ω) ^ 2) μ ∧
      ∫ ω, frobNorm (M ω) ^ 2 ∂μ ≤
        a ^ 2 * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 ∧
      ∀ᵐ ω ∂μ, (∀ Φ : SymmetricGauge,
        Φ.matrixNorm ((A - rsvd A (aeval (Aᴴ * A) f * X ω))ᴴ *
          (A - rsvd A (aeval (Aᴴ * A) f * X ω))) ≤
        Φ.matrixNorm ((A - truncatedSVD A r)ᴴ * (A - truncatedSVD A r)) +
          c⁻¹ ^ 2 * (Φ (Finsupp.single 0 1) * frobNorm (M ω) ^ 2)) ∧
        frobNorm ((1 - rangeProjector (A * aeval (Aᴴ * A) f * X ω)) * truncatedSVD A r) ≤
          c⁻¹ * frobNorm (M ω) := by
  have hG : cfc (fun x => f.eval x) (Aᴴ * A) = aeval (Aᴴ * A) f :=
    cfc_polynomial f (Aᴴ * A) (Matrix.isHermitian_conjTranspose_mul_self A)
  obtain ⟨Z, V, hZ, hV, hZV, hZZ, hAZ, hAV, hpre⟩ :=
    exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal A htn
  set G := aeval (Aᴴ * A) f
  set W := Z.submatrix id (Fin.castLE hrt) with hWdef
  have hW : HasOrthonormalCols W := by
    rw [hasOrthonormalCols_iff, hWdef, Matrix.conjTranspose_submatrix,
      ← Matrix.submatrix_mul Zᴴ Z (Fin.castLE hrt) id (Fin.castLE hrt) Function.bijective_id,
      hZ.conjTranspose_mul_self, Matrix.submatrix_one _ (Fin.castLE_injective hrt)]
  have hWZ : LinearMap.range W.mulVecLin ≤ LinearMap.range Z.mulVecLin :=
    range_le_iff_exists_mul.mpr
      ⟨(1 : Matrix (Fin t) (Fin t) ℝ).submatrix (Equiv.refl _) (Fin.castLE hrt), by
        rw [Matrix.mul_submatrix_one]; rfl⟩
  have hAW : Aᴴ * A * W =
      W * Matrix.diagonal fun i : Fin r => ((singularValues A i ^ 2 : ℝ) : ℝ) := by
    ext x j
    have h := congrFun (congrFun hAZ x) (Fin.castLE hrt j)
    simp only [Matrix.mul_diagonal] at h ⊢
    exact h
  have hg : ∀ i : Fin r, c ≤ |(fun x => f.eval x) (singularValues A i ^ 2)| := fun i =>
    hhead i i.2
  have hAWW : A * W * Wᴴ = truncatedSVD A r := hpre r hrt
  have hVV : V * Vᴴ = 1 - Z * Zᴴ := by rw [← hZZ, add_sub_cancel_left]
  have hEt : A - truncatedSVD A t = A * V * Vᴴ := by
    have h := hpre t le_rfl
    rw [Fin.castLE_rfl, Matrix.submatrix_id_id] at h
    rw [← h, Matrix.mul_assoc A V, hVV, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  have ha : 0 ≤ a := (abs_nonneg _).trans (htail 0 ⟨le_rfl, sq_nonneg _⟩)
  have hS : frobNorm (A * G * V) ≤ a * frobNorm (A - truncatedSVD A t) := by
    have hGV := (Matrix.isHermitian_conjTranspose_mul_self A).cfc_mul_eq_mul_diagonal_of_mul_eq
      hAV (fun x => f.eval x)
    rw [hG] at hGV
    rw [Matrix.mul_assoc, hGV, ← Matrix.mul_assoc, hEt, hV.frobNorm_mul_conjTranspose_right,
      mul_comm a]
    refine (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
      (mul_le_mul_of_nonneg_left (specNorm_diagonal_le ha fun j => ?_) (frobNorm_nonneg _))
    rw [RCLike.norm_ofReal]
    exact htail _ ⟨sq_nonneg _, pow_le_pow_left₀ (singularValues_nonneg _ _)
      (singularValues_antitone A (Nat.le_add_right t j)) 2⟩
  have hM (Ω' : Matrix n l ℝ) : (A * G - A * G * Z * Zᴴ) * Ω' * pinv (Zᴴ * Ω') =
      A * G * V * (Vᴴ * Ω') * pinv (Zᴴ * Ω') := by
    have h : A * G - A * G * Z * Zᴴ = A * G * V * Vᴴ := by
      rw [Matrix.mul_assoc (A * G) V Vᴴ, hVV, Matrix.mul_sub, Matrix.mul_one,
        Matrix.mul_assoc (A * G) Z Zᴴ]
    rw [h, Matrix.mul_assoc (A * G * V) Vᴴ Ω']
  have hk' : Fintype.card (Fin t) + 2 ≤ Fintype.card l := by rwa [Fintype.card_fin]
  have hk : 0 ≤ (t : ℝ) / ((Fintype.card l : ℝ) - t - 1) := by
    have : (t : ℝ) + 2 ≤ Fintype.card l := by exact_mod_cast ht
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  refine ⟨fun ω => A * G * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω),
    integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk' _, ?_, ?_⟩
  · rw [integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk',
      Fintype.card_fin]
    have hS2 : frobNorm (A * G * V) ^ 2 ≤ a ^ 2 * frobNorm (A - truncatedSVD A t) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (frobNorm_nonneg _) hS 2
    calc frobNorm (A * G * V) ^ 2 * t / ((Fintype.card l : ℝ) - t - 1)
        = (t : ℝ) / ((Fintype.card l : ℝ) - t - 1) * frobNorm (A * G * V) ^ 2 := by ring
      _ ≤ (t : ℝ) / ((Fintype.card l : ℝ) - t - 1) *
          (a ^ 2 * frobNorm (A - truncatedSVD A t) ^ 2) := mul_le_mul_of_nonneg_left hS2 hk
      _ = _ := by ring
  · filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix Z hX
      (by rw [hZ.rank_eq, Fintype.card_fin]; omega)] with ω hω
    refine ⟨fun Φ => ?_, ?_⟩
    · have h := Φ.matrixNorm_conjTranspose_mul_self_sub_rsvd_cfc_le (fun x => f.eval x) hW hAW
        hZ hω hWZ hc hg
      rw [hG, hAWW, hM] at h
      refine h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)))
      rw [← nuclearNorm_conjTranspose_mul_self]
      exact Φ.matrixNorm_le_apply_single_mul_nuclearNorm _
    · have h := hW.matrixNorm_one_sub_rangeProjector_mul_mul_le (lpGauge 2 one_le_two)
        (fun x => f.eval x) hAW hZ hω hWZ hc hg
      rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm, hG, hM, hAWW] at h
      exact h

omit [DecidableEq n] in
/-- The index reduction of the filtered range finder in expectation: for $t > \lvert n \rvert$
the statement at $(r, t)$ is the statement at $(\min(r, \lvert n \rvert), \lvert n \rvert)$, the
tail terms being $\mathbf{0}$ and $\sigma_t = \sigma_{\lvert n \rvert} = 0$. -/
private theorem filter_reduction (A : Matrix m n ℝ) {r t : ℕ} (htn : Fintype.card n < t) :
    truncatedSVD A (min r (Fintype.card n)) = truncatedSVD A r ∧
      A - truncatedSVD A t = 0 ∧ A - truncatedSVD A (Fintype.card n) = 0 ∧
      singularValues A (Fintype.card n) = singularValues A t := by
  have hTn : truncatedSVD A (Fintype.card n) = A := truncatedSVD_of_rank_le A A.rank_le_card_width
  refine ⟨?_, by rw [truncatedSVD_of_rank_le A (A.rank_le_card_width.trans htn.le), sub_self],
    by rw [hTn, sub_self], by
      rw [singularValues_of_card_cols_le A le_rfl, singularValues_of_card_cols_le A htn.le]⟩
  rcases le_total r (Fintype.card n) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, hTn, truncatedSVD_of_rank_le A (A.rank_le_card_width.trans h)]

/-- The Gram form of the filtered range finder in expectation for $t \le \lvert n \rvert$. -/
private theorem integral_matrixNorm_filter_le_of_le_card (Φ : SymmetricGauge) (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (f : ℝ[X]) {r t : ℕ} (hrt : r ≤ t)
    (htn : t ≤ Fintype.card n) (ht : t + 2 ≤ Fintype.card l) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a) :
    ∫ ω, Φ.matrixNorm ((A - rsvd A (aeval (Aᴴ * A) f * X ω))ᴴ *
        (A - rsvd A (aeval (Aᴴ * A) f * X ω))) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A r)ᴴ * (A - truncatedSVD A r)) +
        Φ (Finsupp.single 0 1) * (a / c) ^ 2 * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
          frobNorm (A - truncatedSVD A t) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  obtain ⟨M, hMi, hMint, hae⟩ := exists_filter_residual A hX f hrt htn ht hc hhead htail
  have hmeas : AEMeasurable (fun ω => aeval (Aᴴ * A) f * X ω) μ :=
    (measurable_const.matrix_mul measurable_id).comp_aemeasurable hX.aemeasurable
  have hI : Integrable (fun ω => Φ.matrixNorm ((A - truncatedSVD A r)ᴴ * (A - truncatedSVD A r)) +
      c⁻¹ ^ 2 * (Φ (Finsupp.single 0 1) * frobNorm (M ω) ^ 2)) μ :=
    (integrable_const _).add ((hMi.const_mul _).const_mul _)
  refine (integral_mono_ae (Φ.integrable_matrixNorm_conjTranspose_mul_self_sub_rsvd A hmeas) hI
    (hae.mono fun ω h => h.1 Φ)).trans ?_
  rw [integral_add (integrable_const _) ((hMi.const_mul _).const_mul _), integral_const,
    probReal_univ, one_smul, integral_const_mul, integral_const_mul]
  refine add_le_add le_rfl ?_
  have hΦ : 0 ≤ Φ (Finsupp.single 0 1) := apply_nonneg _ _
  calc c⁻¹ ^ 2 * (Φ (Finsupp.single 0 1) * ∫ ω, frobNorm (M ω) ^ 2 ∂μ)
      ≤ c⁻¹ ^ 2 * (Φ (Finsupp.single 0 1) * (a ^ 2 * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
          frobNorm (A - truncatedSVD A t) ^ 2)) := by gcongr
    _ = _ := by ring

/-- Head capture in expectation for $t \le \lvert n \rvert$. -/
private theorem integral_frobNorm_head_filter_le_of_le_card [DecidableEq m] (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (f : ℝ[X]) {r t : ℕ} (hrt : r ≤ t)
    (htn : t ≤ Fintype.card n) (ht : t + 2 ≤ Fintype.card l) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a) :
    ∫ ω, frobNorm ((1 - rangeProjector (A * aeval (Aᴴ * A) f * X ω)) * truncatedSVD A r) ^ 2 ∂μ ≤
      (a / c) ^ 2 * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
        frobNorm (A - truncatedSVD A t) ^ 2 := by
  have := hX.isProbabilityMeasure
  obtain ⟨M, hMi, hMint, hae⟩ := exists_filter_residual A hX f hrt htn ht hc hhead htail
  have hm : Measurable fun Y : Matrix n l ℝ =>
      frobNorm ((1 - rangeProjector (A * aeval (Aᴴ * A) f * Y)) * truncatedSVD A r) ^ 2 :=
    (measurable_frobNorm.comp ((measurable_const.sub (measurable_rangeProjector.comp
      (measurable_const.matrix_mul measurable_id))).matrix_mul measurable_const)).pow_const 2
  have hint : Integrable (fun ω =>
      frobNorm ((1 - rangeProjector (A * aeval (Aᴴ * A) f * X ω)) * truncatedSVD A r) ^ 2) μ :=
    Integrable.of_bound (hm.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
      (frobNorm (truncatedSVD A r) ^ 2) (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_one_sub_rangeProjector_mul_le _ _) 2)
  refine (integral_mono_ae hint (hMi.const_mul (c⁻¹ ^ 2)) (hae.mono fun ω h => ?_)).trans ?_
  · simp only [← mul_pow]
    exact pow_le_pow_left₀ (frobNorm_nonneg _) h.2 2
  · rw [integral_const_mul]
    calc c⁻¹ ^ 2 * ∫ ω, frobNorm (M ω) ^ 2 ∂μ
        ≤ c⁻¹ ^ 2 * (a ^ 2 * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
          frobNorm (A - truncatedSVD A t) ^ 2) := by gcongr
      _ = _ := by ring

namespace SymmetricGauge

/-- **The filtered range finder in expectation, Gram form**: for a standard Gaussian $n \times \ell$
test matrix $\mathbf{X}$, a real polynomial $f$ and $c > 0$ with
$c \le \lvert f(\sigma_i(\mathbf{A})^2) \rvert$ for $i < r$ and $\lvert f \rvert \le a$ on
$[0, \sigma_t(\mathbf{A})^2]$, $r \le t$, $t + 2 \le \ell$ and every unitarily invariant norm,
$$\mathbb{E}\bigl\|\mathbf{E}_f^{\mathsf{H}}\mathbf{E}_f\bigr\|_{\Phi} \le
\bigl\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r)^{\mathsf{H}}
(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r)\bigr\|_{\Phi} +
\Phi(\mathbf{e}_0)\Bigl(\frac{a}{c}\Bigr)^2\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
with $\mathbf{E}_f = \mathbf{A} - \mathsf{rsvd}(\mathbf{A},
f(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{X})$ and $\Phi(\mathbf{e}_0) = 1$ for every Schatten
gauge. At $f = 1$, $r = t$ it is the Gram-form bound of the randomized SVD in
`NLAlib.LowRank.Gaussian.RangeFinder`.
[TroppWebber2023, Lemma 9.5]; there for a diagonal positive semidefinite matrix and Schatten
$p \ge 2$, with $\lvert f \rvert \ge c$ on the head written through a filter $\varphi$ and indices
from $1$ ($\sigma_s$ for our $\sigma_t$); here every quadratic gauge and any matrix.
Result: filtered-range-finder-bound -/
theorem integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_aeval_le_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) (f : ℝ[X])
    {r t : ℕ} (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a) :
    ∫ ω, Φ.matrixNorm ((A - rsvd A (aeval (Aᴴ * A) f * X ω))ᴴ *
        (A - rsvd A (aeval (Aᴴ * A) f * X ω))) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A r)ᴴ * (A - truncatedSVD A r)) +
        Φ (Finsupp.single 0 1) * (a / c) ^ 2 * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
          frobNorm (A - truncatedSVD A t) ^ 2 := by
  rcases le_or_gt t (Fintype.card n) with htn | htn
  · exact integral_matrixNorm_filter_le_of_le_card Φ A hX f hrt htn ht hc hhead htail
  · obtain ⟨hTr, hEt, hEn, hσ⟩ := filter_reduction A (r := r) htn
    have h := integral_matrixNorm_filter_le_of_le_card Φ A hX f (min_le_right r _) le_rfl
      (by omega) hc (fun i hi => hhead i (hi.trans_le (min_le_left _ _))) (by rwa [hσ])
    rw [hTr, hEn, frobNorm_zero] at h
    rw [hEt, frobNorm_zero]
    simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] using h

end SymmetricGauge

open SymmetricGauge in
/-- **The filtered range finder in expectation, spectral norm**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$, a real polynomial $f$ and $c > 0$ with
$c \le \lvert f(\sigma_i(\mathbf{A})^2) \rvert$ for $i < r$ and $\lvert f \rvert \le a$ on
$[0, \sigma_t(\mathbf{A})^2]$, $r \le t$ and $t + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A},
f(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{X})\|_2^2 \le \sigma_r(\mathbf{A})^2 +
\Bigl(\frac{a}{c}\Bigr)^2\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
The Gram form, in every unitarily invariant norm, is
`NLAlib.integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_aeval_le_of_hasLaw_gaussianMatrix`.
[TroppWebber2023, Lemma 9.5], at $p = \infty$.
Result: filtered-range-finder-bound -/
theorem integral_specNorm_sub_rsvd_aeval_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (f : ℝ[X]) {r t : ℕ} (hrt : r ≤ t)
    (ht : t + 2 ≤ Fintype.card l) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a) :
    ∫ ω, specNorm (A - rsvd A (aeval (Aᴴ * A) f * X ω)) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        (a / c) ^ 2 * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
          frobNorm (A - truncatedSVD A t) ^ 2 := by
  have h :=
    integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_aeval_le_of_hasLaw_gaussianMatrix
      (lpGauge ⊤ le_top) A hX f hrt ht hc hhead htail
  simp only [lpGauge_top_matrixNorm, specNorm_conjTranspose_mul_self,
    lpGauge_apply_single_zero le_top, one_mul, specNorm_sub_truncatedSVD] at h
  exact h

open SymmetricGauge in
/-- **The filtered range finder in expectation, Frobenius norm**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$, a real polynomial $f$ and $c > 0$ with
$c \le \lvert f(\sigma_i(\mathbf{A})^2) \rvert$ for $i < r$ and $\lvert f \rvert \le a$ on
$[0, \sigma_t(\mathbf{A})^2]$, $r \le t$ and $t + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A},
f(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{X})\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
\Bigl(\frac{a}{c}\Bigr)^2\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
The Gram form, in every unitarily invariant norm, is
`NLAlib.integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_aeval_le_of_hasLaw_gaussianMatrix`.
[TroppWebber2023, Lemma 9.5], at $p = 2$.
Result: filtered-range-finder-bound -/
theorem integral_frobNorm_sub_rsvd_aeval_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (f : ℝ[X]) {r t : ℕ} (hrt : r ≤ t)
    (ht : t + 2 ≤ Fintype.card l) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a) :
    ∫ ω, frobNorm (A - rsvd A (aeval (Aᴴ * A) f * X ω)) ^ 2 ∂μ ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        (a / c) ^ 2 * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
          frobNorm (A - truncatedSVD A t) ^ 2 := by
  have h :=
    integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_aeval_le_of_hasLaw_gaussianMatrix
      (lpGauge 1 le_rfl) A hX f hrt ht hc hhead htail
  simp only [lpGauge_one_matrixNorm, nuclearNorm_conjTranspose_mul_self,
    lpGauge_apply_single_zero, one_mul] at h
  exact h

/-- **Head capture in expectation**: for a standard Gaussian $n \times \ell$ test matrix
$\mathbf{X}$, a real polynomial $f$ and $c > 0$ with $c \le \lvert f(\sigma_i(\mathbf{A})^2) \rvert$
for $i < r$ and $\lvert f \rvert \le a$ on $[0, \sigma_t(\mathbf{A})^2]$, $r \le t$ and
$t + 2 \le \ell$, the filtered sketch $\mathbf{A}f(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{X}$
captures the best rank-$r$ approximation up to
$$\mathbb{E}\bigl\|(\mathbf{I} -
\mathbf{P}_{\mathbf{A}f(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{X}})
\llbracket\mathbf{A}\rrbracket_r\bigr\|_{\mathsf{F}}^2 \le
\Bigl(\frac{a}{c}\Bigr)^2\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
With Gu's projected form
(`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add`) it bounds the
truncated outputs. [TroppWebber2023, Lemma 9.5 (proof)]; [MuscoMusco2015, Lemma 9, property 1]. -/
theorem integral_frobNorm_one_sub_rangeProjector_mul_truncatedSVD_sq_le_of_hasLaw_gaussianMatrix
    [DecidableEq m] (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) (f : ℝ[X])
    {r t : ℕ} (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a) :
    ∫ ω, frobNorm ((1 - rangeProjector (A * aeval (Aᴴ * A) f * X ω)) * truncatedSVD A r) ^ 2 ∂μ ≤
      (a / c) ^ 2 * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
        frobNorm (A - truncatedSVD A t) ^ 2 := by
  rcases le_or_gt t (Fintype.card n) with htn | htn
  · exact integral_frobNorm_head_filter_le_of_le_card A hX f hrt htn ht hc hhead htail
  · obtain ⟨hTr, hEt, hEn, hσ⟩ := filter_reduction A (r := r) htn
    have h := integral_frobNorm_head_filter_le_of_le_card A hX f (min_le_right r _) le_rfl
      (by omega) hc (fun i hi => hhead i (hi.trans_le (min_le_left _ _))) (by rwa [hσ])
    rw [hTr, hEn, frobNorm_zero] at h
    rw [hEt, frobNorm_zero]
    simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] using h

end NLAlib
