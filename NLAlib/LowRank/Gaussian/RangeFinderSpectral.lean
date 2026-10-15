/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.RandomMatrix.Gaussian.BlockMomentsSpectral

/-!
# The expected squared spectral error of the Gaussian randomized SVD

The second-moment form of Halko, Martinsson and Tropp's Theorem 10.6: for a standard Gaussian
$n \times \ell$ test matrix and $k + 2 \le \ell$, the expected squared spectral error of
$\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ is at most $\sigma_k^2$ plus the second spectral
moment of the Gaussian block
(`NLAlib.integral_specNorm_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix`), in which the Frobenius
tail enters with weight $O(1/\ell)$. A side file that merges into
`NLAlib/LowRank/Gaussian/RangeFinder.lean`, beside the first spectral moment
(`docs/design/LowRank-S6.md` §3.3, §4, D1).

## Main results

* `NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] {X : Ω → Matrix n l ℝ}

/-- If the target rank exceeds the number of columns, the optimal error is $\mathbf{0}$ and so is
the error of the randomized SVD, almost surely (restated from
`NLAlib/LowRank/Gaussian/RangeFinder.lean`, where it is private; removed at the merge). -/
private theorem ae_sub_rsvd_eq_zero_of_card_lt' (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hkn : Fintype.card n < k)
    (hkl : k ≤ Fintype.card l) :
    A - truncatedSVD A k = 0 ∧ ∀ᵐ ω ∂μ, A - rsvd A (X ω) = 0 := by
  have hr : A.rank ≤ k := (A.rank_le_card_width).trans hkn.le
  refine ⟨by rw [truncatedSVD_of_rank_le A hr, sub_self], ?_⟩
  filter_upwards [ae_rsvd_eq_self_of_hasLaw_gaussianMatrix A hX (hr.trans hkl)] with ω hω
  rw [hω, sub_self]

/-- **The expected squared spectral error of the randomized SVD, HMT 10.6 form**: for a standard
Gaussian $n \times \ell$ test matrix and
$k + 2 \le \ell$, <!-- value gaussianPinvSpecNormBound k \ell -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_2^2 \le \sigma_k^2 +
\Bigl(\sigma_k\sqrt{\tfrac{k}{\ell-k-1}} + \frac{e}{\ell - k}\sqrt{(\ell + k - 1)/2}\,
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}\Bigr)^2 +
\sigma_k^2\Bigl(\frac{e}{\ell - k}\sqrt{(\ell + k - 1)/2}\Bigr)^2\,,$$
singular values of $\mathbf{A}$ from $0$; the bound is written in
`gaussianPinvSpecNormBound k ℓ`, whence the name's suffix. The last factor being $O(1/\ell)$,
the Frobenius tail enters with weight $O(1/\ell)$, against $\frac{k}{\ell-k-1}$ in
`NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`; the two are incomparable
(this one is better when the tail is heavy and $\ell \gg k$). Applied at a comparison rank near
$\ell/2$ with the tail flattening
`NLAlib.natCast_mul_singularValues_add_sq_le_frobNorm_sub_truncatedSVD_sq`, it bounds the
spectral error by $O(1/\ell)$ times the Frobenius tail at any $k \le \ell/4$.
[HalkoMartinssonTropp2011, Theorem 10.6]; there the first moment; proved without a literature
source in this second-moment form.
Result: randomized-svd-average-spectral-error -/
theorem integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      singularValues A k ^ 2 +
        (singularValues A k * √((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) +
          gaussianPinvSpecNormBound k (Fintype.card l) * frobNorm (A - truncatedSVD A k)) ^ 2 +
        (singularValues A k * gaussianPinvSpecNormBound k (Fintype.card l)) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  rcases le_or_gt k (Fintype.card n) with hkn | hkn
  · obtain ⟨Z, V, hZ, hV, hZV, hZA, hEV⟩ :=
      exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion (p := Fin k)
        (q := Fin (Fintype.card n - k)) A (Fintype.card_fin k)
        (by simp only [Fintype.card_fin]; omega)
    have hk' : Fintype.card (Fin k) + 2 ≤ Fintype.card l := by rwa [Fintype.card_fin]
    have hMi := integrable_specNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hM := integral_specNorm_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hpt : ∀ᵐ ω ∂μ, specNorm (A - rsvd A (X ω)) ^ 2 ≤ singularValues A k ^ 2 +
        specNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) ^ 2 := by
      filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix Z hX
        (by rw [hZ.rank_eq, Fintype.card_fin]; omega)]
        with ω hω
      have h := hZ.specNorm_sub_rsvd_sq_le hω A
      rw [hZA, specNorm_sub_truncatedSVD] at h
      rwa [← Matrix.mul_assoc ((A - truncatedSVD A k) * V), hEV]
    have hI : Integrable (fun ω => singularValues A k ^ 2 +
        specNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) ^ 2) μ :=
      (integrable_const _).add hMi
    refine (integral_mono_ae (integrable_specNorm_sub_rsvd_sq A hX.aemeasurable) hI hpt).trans ?_
    rw [integral_add (integrable_const _) hMi, integral_const, probReal_univ, one_smul]
    have hF := (lpGauge 2 one_le_two).matrixNorm_mul_of_mul_mul_conjTranspose_eq hV hEV
    rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at hF
    have hS := (lpGauge ⊤ le_top).matrixNorm_mul_of_mul_mul_conjTranspose_eq hV hEV
    rw [lpGauge_top_matrixNorm, lpGauge_top_matrixNorm, specNorm_sub_truncatedSVD] at hS
    rw [hF, hS, Fintype.card_fin] at hM
    linarith
  · obtain ⟨hE, hae⟩ := ae_sub_rsvd_eq_zero_of_card_lt' A hX hkn (by omega)
    rw [integral_congr_ae (hae.mono fun ω hω => by simp only [hω, specNorm_zero]; rfl)]
    simp only [integral_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

end NLAlib
