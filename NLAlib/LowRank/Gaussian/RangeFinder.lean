/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Random.RangeFinder
public import NLAlib.LowRank.Structural.RangeFinder
public import NLAlib.Matrix.Norms.GaugeExamples
public import NLAlib.RandomMatrix.Gaussian.BlockMoments
public import NLAlib.RandomMatrix.Gaussian.Rank

/-!
# The expected error of the Gaussian randomized SVD

For a real $\mathbf{A}$ and a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, the
randomized SVD $\mathsf{rsvd}(\mathbf{A}, \mathbf{X})$ (`NLAlib.rsvd`) has, for a target rank
$k$ with $k + 2 \le \ell$ and $\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{E}\|_{\mathsf{F}}^2\,,$$
Halko, Martinsson and Tropp's Theorem 10.5, and its Gram form in every quadratic unitarily
invariant norm, of which the Schatten forms of Tropp and Webber's Theorem 8.1 (RSVD2) and the
squared spectral form are corollaries. The first spectral moment (HMT Theorem 10.6) and the
late-truncated output `truncatedSVD (rsvd A (X ω)) k` in the Frobenius norm, with HMT's constant,
are here too. Every error is $\mathbf{A}$ minus the named output.

The proof completes a top-$k$ frame $\mathbf{Z}$ by $\mathbf{V}$ to an orthogonal matrix
(`NLAlib.exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion`), so that
the structural bounds of `NLAlib.LowRank.Structural.RangeFinder` hold almost surely with
$\mathbf{M} = (\mathbf{E}\mathbf{V})(\mathbf{V}^{\mathsf{H}}\mathbf{X})
(\mathbf{Z}^{\mathsf{H}}\mathbf{X})^{+}$, and integrates them with the block moments of
`NLAlib.RandomMatrix.Gaussian.BlockMoments`. No hypothesis on the shape of $\mathbf{A}$ is needed:
if $k$ exceeds the number of columns, $\operatorname{rank}\mathbf{A} \le \ell$ and the error is
$\mathbf{0}$ almost surely (`NLAlib.ae_rsvd_eq_self_of_hasLaw_gaussianMatrix`). The hypothesis
$k + 2 \le \ell$ is necessary: at $\ell = k + 1$ the expectation is not bounded by any multiple of
$\|\mathbf{E}\|_{\mathsf{F}}^2$.

The spectral error of the truncated output depends on the choice `truncatedSVD` makes; its
expectation is stated for any measurable choice of best approximations and, directly, for
`truncatedSVD`, which is Borel measurable (`NLAlib.measurable_truncatedSVD`). The integrability
companions are law-free, in `NLAlib.LowRank.Random.RangeFinder`. Design:
`docs/design/LowRank-S3.md` §3.5, §8; `docs/design/LowRank-S2c.md` §8 item 7.

## Main results

* `NLAlib.ae_rsvd_eq_self_of_hasLaw_gaussianMatrix`: exact recovery at
  $\operatorname{rank}\mathbf{A} \le \ell$.
* the Gram form, every quadratic unitarily invariant norm, in the `NLAlib.SymmetricGauge`
  namespace:
  `integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix`: HMT Theorem 10.5, squared and
  as printed.
* `NLAlib.integral_schattenNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`: TW Theorem 8.1 (RSVD2).
* `NLAlib.integral_specNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix`: HMT Theorem 10.6.
* `NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix`: the truncated
  output, Frobenius norm.
* `NLAlib.integral_specNorm_sub_sq_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix`: the truncated
  output, spectral norm, for a measurable selector;
  `NLAlib.integral_specNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix`, its direct
  form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] {X : Ω → Matrix n l ℝ}

/-! ### The completed top-`k` frame -/

omit [Fintype m] in
/-- The block of the structural bound in the completed frame:
$$\mathbf{E}\mathbf{X}(\mathbf{Z}^{\mathsf{H}}\mathbf{X})^{+} =
(\mathbf{E}\mathbf{V})(\mathbf{V}^{\mathsf{H}}\mathbf{X})
(\mathbf{Z}^{\mathsf{H}}\mathbf{X})^{+}\,.$$ -/
private theorem sub_mul_mul_pinv_eq_block {E : Matrix m n ℝ} {p q : Type*} [Fintype p]
    [Fintype q] {V : Matrix n q ℝ} (hEV : E * V * Vᴴ = E) (Z : Matrix n p ℝ)
    (Ω : Matrix n l ℝ) : E * Ω * pinv (Zᴴ * Ω) = E * V * (Vᴴ * Ω) * pinv (Zᴴ * Ω) := by
  rw [← Matrix.mul_assoc (E * V), hEV]

/-! ### Exact recovery -/

/-- **A Gaussian sketch at least as wide as the rank recovers the matrix**: if
$\operatorname{rank}\mathbf{A} \le \ell$, then $\mathsf{rsvd}(\mathbf{A}, \mathbf{X}) =
\mathbf{A}$ almost surely, for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$. -/
theorem ae_rsvd_eq_self_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (hA : A.rank ≤ Fintype.card l) :
    ∀ᵐ ω ∂μ, rsvd A (X ω) = A := by
  filter_upwards [ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix A hX] with ω hω
  exact rsvd_eq_self_of_rank_eq (hω.trans (min_eq_left hA))

/-- If the target rank exceeds the number of columns, the optimal error is $\mathbf{0}$ and so is
the error of the randomized SVD, almost surely. -/
private theorem ae_sub_rsvd_eq_zero_of_card_lt (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hkn : Fintype.card n < k)
    (hkl : k ≤ Fintype.card l) :
    A - truncatedSVD A k = 0 ∧ ∀ᵐ ω ∂μ, A - rsvd A (X ω) = 0 := by
  have hr : A.rank ≤ k := (A.rank_le_card_width).trans hkn.le
  refine ⟨by rw [truncatedSVD_of_rank_le A hr, sub_self], ?_⟩
  filter_upwards [ae_rsvd_eq_self_of_hasLaw_gaussianMatrix A hX (hr.trans hkl)] with ω hω
  rw [hω, sub_self]

/-! ### The Gram form and its corollaries -/

namespace SymmetricGauge

/-- **The expected error of the randomized SVD, Gram form**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$, $k + 2 \le \ell$ and every unitarily invariant norm,
$$\mathbb{E}\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))\bigr\|_{\Phi} \le
\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{k}{\ell - k - 1}\,
\|\mathbf{E}\|_{\mathsf{F}}^2\,,\qquad
\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\,,$$
with $\mathbf{e}_0$ the first unit coordinate sequence ($\Phi(\mathbf{e}_0) = 1$ for every
Schatten gauge, `NLAlib.lpGauge_apply_single_zero`). This covers every quadratic unitarily
invariant norm: squared Schatten $p$-norms for $p \ge 2$, the squared Frobenius norm at the
nuclear gauge, the squared spectral norm. No hypothesis on the shape of $\mathbf{A}$.
[TroppWebber2023, Theorem 8.1 (RSVD2)]; [HalkoMartinssonTropp2011, Theorem 10.5 (proof)];
[MartinssonTropp2020, Theorem 11.4 and remark]; there for Schatten $p \ge 2$ (TW), here every
quadratic unitarily invariant norm, with the factor $\Phi(\mathbf{e}_0)$.
Result: randomized-svd-expected-error -/
theorem integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        Φ (Finsupp.single 0 1) * ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
          frobNorm (A - truncatedSVD A k) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  rcases le_or_gt k (Fintype.card n) with hkn | hkn
  · obtain ⟨Z, V, hZ, hV, hZV, hZA, hEV⟩ :=
      exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion (p := Fin k)
        (q := Fin (Fintype.card n - k)) A (Fintype.card_fin k)
        (by simp only [Fintype.card_fin]; omega)
    have hk' : Fintype.card (Fin k) + 2 ≤ Fintype.card l := by rwa [Fintype.card_fin]
    have hMi := integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hM := integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hpt : ∀ᵐ ω ∂μ, Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) ≤
        Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
          Φ (Finsupp.single 0 1) *
            frobNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) ^ 2 := by
      filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix Z hX
        (by rw [hZ.rank_eq, Fintype.card_fin]; omega)]
        with ω hω
      have h := Φ.matrixNorm_conjTranspose_mul_self_sub_rsvd_le hZ hω A
      rw [hZA, sub_mul_mul_pinv_eq_block hEV] at h
      refine h.trans (add_le_add le_rfl ?_)
      rw [← nuclearNorm_conjTranspose_mul_self]
      exact Φ.matrixNorm_le_apply_single_mul_nuclearNorm _
    have hI : Integrable (fun ω => Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        Φ (Finsupp.single 0 1) *
          frobNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) ^ 2) μ :=
      (integrable_const _).add (hMi.const_mul _)
    refine (integral_mono_ae (Φ.integrable_matrixNorm_conjTranspose_mul_self_sub_rsvd A
      hX.aemeasurable) hI hpt).trans_eq ?_
    rw [integral_add (integrable_const _) (hMi.const_mul _), integral_const, probReal_univ,
      one_smul, integral_const_mul, hM, Fintype.card_fin]
    have hF := (lpGauge 2 one_le_two).matrixNorm_mul_of_mul_mul_conjTranspose_eq hV hEV
    rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at hF
    rw [hF]
    ring
  · obtain ⟨hE, hae⟩ := ae_sub_rsvd_eq_zero_of_card_lt A hX hkn (by omega)
    rw [integral_congr_ae (hae.mono fun ω hω => by
      simp only [hω, Matrix.conjTranspose_zero, Matrix.zero_mul, Φ.matrixNorm_zero]; rfl)]
    simp only [hE, Matrix.conjTranspose_zero, Matrix.zero_mul, Φ.matrixNorm_zero, frobNorm_zero,
      integral_zero]
    norm_num

end SymmetricGauge

open SymmetricGauge in
/-- **The expected error of the randomized SVD, Frobenius norm** (HMT Theorem 10.5, squared):
for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and
$k + 2 \le \ell$, <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,;$$
the factor is `gaussianProjectionFactor k ℓ`. The Frobenius instance of the Gram-form bound above;
Epperly and Webber's sharper factor, with a rank parameter, is
`NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_of_rank_le`.
[HalkoMartinssonTropp2011, Theorem 10.5]; [TroppWebber2023, Theorem 8.7]; HMT state the
bound for $\mathbb{E}\|\cdot\|_{\mathsf{F}}$ (it follows by Jensen,
`NLAlib.integral_frobNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix`) and assume $k \ge 2$ and
$k + p \le \min\{m, n\}$, neither needed here.
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have h := integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix
    (lpGauge 1 le_rfl) A hX hk
  simp only [lpGauge_one_matrixNorm, nuclearNorm_conjTranspose_mul_self,
    lpGauge_apply_single_zero, one_mul] at h
  rw [gaussianProjectionFactor_def]
  linarith

/-- **The expected error of the randomized SVD, Frobenius norm, as printed** (HMT Theorem 10.5):
for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}} \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)^{1/2}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}\,,$$
by Jensen from the squared form `NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`.
[HalkoMartinssonTropp2011, Theorem 10.5]; [TroppWebber2023, Theorem 8.7]; there (HMT) with
$k \ge 2$ and $k + p \le \min\{m, n\}$, neither needed here.
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ∂μ ≤
      √(gaussianProjectionFactor k (Fintype.card l)) * frobNorm (A - truncatedSVD A k) := by
  have := hX.isProbabilityMeasure
  have hm : AEStronglyMeasurable (fun ω => frobNorm (A - rsvd A (X ω))) μ :=
    (integrable_frobNorm_sub_rsvd A hX.aemeasurable).aestronglyMeasurable
  have hL2 : MemLp (fun ω => frobNorm (A - rsvd A (X ω))) 2 μ :=
    (memLp_two_iff_integrable_sq hm).2 (integrable_frobNorm_sub_rsvd_sq A hX.aemeasurable)
  have hvar := variance_nonneg (fun ω => frobNorm (A - rsvd A (X ω))) μ
  rw [variance_eq_sub hL2] at hvar
  simp only [Pi.pow_apply] at hvar
  have h2 := integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk
  rw [← Real.sqrt_sq (frobNorm_nonneg (A - truncatedSVD A k)), ← Real.sqrt_mul
    (zero_le_one.trans (one_le_gaussianProjectionFactor hk))]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))

open SymmetricGauge in
/-- **The expected error of the randomized SVD, Schatten norms** (TW Theorem 8.1 (RSVD2)): for a
standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $k + 2 \le \ell$ and
$2 \le p \le \infty$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{S_p}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^2 + \frac{k}{\ell - k - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
The Gram form at the Schatten gauge of order $p/2$.
[TroppWebber2023, Theorem 8.1 (RSVD2)]; [HalkoMartinssonTropp2011, Theorem 10.5 (proof)].
Result: randomized-svd-expected-error -/
theorem integral_schattenNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) {p : ℝ≥0∞}
    (hp : 2 ≤ p) :
    ∫ ω, schattenNorm p (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      schattenNorm p (A - truncatedSVD A k) ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have hq : 1 ≤ p / 2 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), one_mul]
    exact hp
  have hq0 : p / 2 ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have h2 : 2 * (p / 2) = p := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
  have h := integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix
    (lpGauge (p / 2) hq) A hX hk
  simp only [lpGauge_matrixNorm hq, schattenNorm_conjTranspose_mul_self hq0, h2,
    lpGauge_apply_single_zero hq, one_mul] at h
  exact h

open SymmetricGauge in
/-- **The expected error of the randomized SVD, squared spectral norm** (TW Theorem 8.1 (RSVD2) at
$p = \infty$): for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and
$k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_2^2 \le
\sigma_k(\mathbf{A})^2 + \frac{k}{\ell - k - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
Incomparable with `NLAlib.integral_specNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix` (the first
moment, HMT Theorem 10.6): this one is better for small $k$ and is the form with a Nyström twin.
[TroppWebber2023, Theorem 8.1 (RSVD2)]; [MartinssonTropp2020, Theorem 11.4 and remark].
Result: randomized-svd-expected-error -/
theorem integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      singularValues A k ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have h := integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix
    (lpGauge ⊤ le_top) A hX hk
  simp only [lpGauge_top_matrixNorm, specNorm_conjTranspose_mul_self,
    lpGauge_apply_single_zero le_top, one_mul, specNorm_sub_truncatedSVD] at h
  exact h

/-! ### The first spectral moment -/

/-- **The average spectral error of the randomized SVD** (HMT Theorem 10.6): for a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and
$k + 2 \le \ell$, <!-- value gaussianPinvSpecNormBound k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_2 \le
\Bigl(1 + \sqrt{\tfrac{k}{\ell - k - 1}}\Bigr)\sigma_k(\mathbf{A}) +
\frac{e}{\ell - k}\sqrt{(\ell + k - 1)/2}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}\,,$$
whose constant, `gaussianPinvSpecNormBound k ℓ`, is at most HMT's $e\sqrt{\ell}/(\ell - k)$
(`NLAlib.gaussianPinvSpecNormBound_le`). Incomparable with the squared form
`NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`: this one is better for large
$k$.
[HalkoMartinssonTropp2011, Theorem 10.6]; [MartinssonTropp2020, Theorem 11.5]; there with the
constant $e\sqrt{k + p}/p$, $p = \ell - k$, and $k \ge 2$, here any $k$ with $k + 2 \le \ell$.
Result: randomized-svd-average-spectral-error -/
theorem integral_specNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ∂μ ≤
      (1 + √((k : ℝ) / ((Fintype.card l : ℝ) - k - 1))) * singularValues A k +
        gaussianPinvSpecNormBound k (Fintype.card l) * frobNorm (A - truncatedSVD A k) := by
  classical
  have := hX.isProbabilityMeasure
  have hC : 0 ≤ gaussianPinvSpecNormBound k (Fintype.card l) :=
    gaussianPinvSpecNormBound_nonneg (by omega)
  rcases le_or_gt k (Fintype.card n) with hkn | hkn
  · obtain ⟨Z, V, hZ, hV, hZV, hZA, hEV⟩ :=
      exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion (p := Fin k)
        (q := Fin (Fintype.card n - k)) A (Fintype.card_fin k)
        (by simp only [Fintype.card_fin]; omega)
    have hk' : Fintype.card (Fin k) + 2 ≤ Fintype.card l := by rwa [Fintype.card_fin]
    have hMi := integrable_specNorm_mul_mul_pinv_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hM := integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hpt : ∀ᵐ ω ∂μ, specNorm (A - rsvd A (X ω)) ≤ singularValues A k +
        specNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) := by
      filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix Z hX
        (by rw [hZ.rank_eq, Fintype.card_fin]; omega)]
        with ω hω
      have h := hZ.specNorm_sub_rsvd_le hω A
      rwa [hZA, sub_mul_mul_pinv_eq_block hEV, specNorm_sub_truncatedSVD] at h
    have hI : Integrable (fun ω => singularValues A k +
        specNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω))) μ :=
      (integrable_const _).add hMi
    refine (integral_mono_ae (integrable_specNorm_sub_rsvd A hX.aemeasurable) hI hpt).trans ?_
    rw [integral_add (integrable_const _) hMi, integral_const, probReal_univ, one_smul]
    have hF := (lpGauge 2 one_le_two).matrixNorm_mul_of_mul_mul_conjTranspose_eq hV hEV
    rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at hF
    have hS := (lpGauge ⊤ le_top).matrixNorm_mul_of_mul_mul_conjTranspose_eq hV hEV
    rw [lpGauge_top_matrixNorm, lpGauge_top_matrixNorm, specNorm_sub_truncatedSVD] at hS
    rw [hF, hS, Fintype.card_fin, ← gaussianPinvSpecNormBound_def] at hM
    linarith
  · obtain ⟨hE, hae⟩ := ae_sub_rsvd_eq_zero_of_card_lt A hX hkn (by omega)
    have hσ : singularValues A k = 0 := by rw [← specNorm_sub_truncatedSVD, hE, specNorm_zero]
    rw [integral_congr_ae (hae.mono fun ω hω => by simp only [hω, specNorm_zero]; rfl)]
    simp only [hE, hσ, frobNorm_zero, integral_zero, mul_zero, add_zero, le_refl]

/-! ### The late-truncated output -/

/-- **The expected error of the truncated randomized SVD, Frobenius norm**: the late truncation
keeps HMT's constant,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{A} -
\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $k + 2 \le \ell$ and every
choice of the truncation (the squared Frobenius error does not depend on it,
`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq`).
[HalkoMartinssonTropp2011, Theorem 10.5]; [Woodruff2014, Lemma 48];
[CamanoEpperlyMeyerTropp2025, remark after Theorem 2.2]; there the untruncated bound with the
truncation for free of Woodruff, or the truncation through the spectral HMT Theorem 9.3 (CEMT).
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  rcases le_or_gt k (Fintype.card n) with hkn | hkn
  · obtain ⟨Z, V, hZ, hV, hZV, hZA, hEV⟩ :=
      exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion (p := Fin k)
        (q := Fin (Fintype.card n - k)) A (Fintype.card_fin k)
        (by simp only [Fintype.card_fin]; omega)
    have hk' : Fintype.card (Fin k) + 2 ≤ Fintype.card l := by rwa [Fintype.card_fin]
    have hMi := integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hM := integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hZ hV hZV hk'
      ((A - truncatedSVD A k) * V)
    have hpt : ∀ᵐ ω ∂μ, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ≤
        frobNorm (A - truncatedSVD A k) ^ 2 +
          frobNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) ^ 2 := by
      filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix Z hX
        (by rw [hZ.rank_eq, Fintype.card_fin]; omega)]
        with ω hω
      have h := hZ.frobNorm_sub_truncatedSVD_rsvd_sq_le hω A
        (by rw [Fintype.card_fin] : Fintype.card (Fin k) ≤ k)
      rwa [hZA, sub_mul_mul_pinv_eq_block hEV] at h
    have hI : Integrable (fun ω => frobNorm (A - truncatedSVD A k) ^ 2 +
        frobNorm ((A - truncatedSVD A k) * V * (Vᴴ * X ω) * pinv (Zᴴ * X ω)) ^ 2) μ :=
      (integrable_const _).add hMi
    refine (integral_mono_ae (integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX.aemeasurable k)
      hI hpt).trans_eq ?_
    rw [integral_add (integrable_const _) hMi, integral_const, probReal_univ, one_smul, hM,
      Fintype.card_fin, gaussianProjectionFactor_def]
    have hF := (lpGauge 2 one_le_two).matrixNorm_mul_of_mul_mul_conjTranspose_eq hV hEV
    rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at hF
    rw [hF]
    ring
  · obtain ⟨hE, hae⟩ := ae_sub_rsvd_eq_zero_of_card_lt A hX hkn (by omega)
    have hpt : ∀ᵐ ω ∂μ, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 = 0 := by
      filter_upwards [hae] with ω hω
      have h := frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_rsvd_sq_add A (X ω) k
      rw [hω, hE, frobNorm_zero] at h
      exact le_antisymm (by linarith) (sq_nonneg _)
    rw [integral_congr_ae hpt]
    simp only [hE, frobNorm_zero, integral_zero]
    norm_num

/-- **The expected spectral error of the truncated randomized SVD**, for a measurable choice
$\mathbf{Y}$ of best rank-$k$ approximations of $\mathsf{rsvd}(\mathbf{A}, \mathbf{X})$: for
a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \mathbf{Y}\|_2^2 \le \sigma_k(\mathbf{A})^2 + \frac{k}{\ell - k - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
the bound of the untruncated output
(`NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`). Direct form at
`truncatedSVD`: `NLAlib.integral_specNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix`.
[Gu2015, Theorem 3.4]; [TroppYurtseverUdellCevher2017a, Proposition A.8];
[TroppWebber2023, p. 42]; there a remark on truncated outputs, here explicit, under a selector.
Result: randomized-svd-expected-error -/
theorem integral_specNorm_sub_sq_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) {Y : Ω → Matrix m n ℝ}
    (hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω)) (hYm : AEStronglyMeasurable Y μ) :
    ∫ ω, specNorm (A - Y ω) ^ 2 ∂μ ≤
      singularValues A k ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  have h1 := integral_specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_isBestRankApprox A
    hX.aemeasurable hY hYm
  have h2 := integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk
  have h3 : gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 =
      frobNorm (A - truncatedSVD A k) ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2 := by
    rw [gaussianProjectionFactor_def]
    ring
  linarith

/-- **The expected spectral error of the truncated randomized SVD**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$ and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k\|_2^2 \le
\sigma_k(\mathbf{A})^2 + \frac{k}{\ell - k - 1}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,,$$
the bound of the untruncated output. The direct form of
`NLAlib.integral_specNorm_sub_sq_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix`, which covers any
other measurable choice of the truncation.
[Gu2015, Theorem 3.4]; [TroppYurtseverUdellCevher2017a, Proposition A.8];
[TroppWebber2023, p. 42]; there a remark on truncated outputs, here explicit.
Result: randomized-svd-expected-error -/
theorem integral_specNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ ≤
      singularValues A k ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2 :=
  integral_specNorm_sub_sq_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix A hX hk
    (fun _ => isBestRankApprox_truncatedSVD _ k)
    (((measurable_rsvd A).comp_aemeasurable hX.aemeasurable).truncatedSVD k).aestronglyMeasurable

end NLAlib
