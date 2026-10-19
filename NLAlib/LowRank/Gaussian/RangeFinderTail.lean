/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.LowRank.Structural.RangeFinder
public import NLAlib.LowRank.Structural.Truncation
public import NLAlib.RandomMatrix.Gaussian.BlockTail
public import NLAlib.RandomMatrix.Gaussian.Rank

/-!
# Tail bounds for the Gaussian range finder and the randomized SVD

For $\mathbf{A} \in \mathbb{R}^{m \times n}$, a standard Gaussian test matrix
$\mathbf{X} \in \mathbb{R}^{n \times \ell}$ and a target rank $k$, the error of the randomized SVD
is `A - rsvd A (X ω)`, $\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})$, and the error of
its late truncation is `A - truncatedSVD (rsvd A (X ω)) k`. Throughout,
$$\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k,\qquad
\|\mathbf{E}\|_2 = \sigma_k(\mathbf{A}),\qquad d = \ell - k + 1\,,$$
the last written `hd : k + d = Fintype.card l + 1` (singular values are indexed from $0$).

Every statement bounds the probability of the failure event, written positively
(CONTRIBUTING §4 N15), `μ.real {ω | bound < error ω}`. The primary tail is Tropp and Webber's
(RSVD1): in Gram form for every unitarily invariant norm, with its Schatten, Frobenius and spectral
corollaries and
the truncated outputs; the failure probability is <!-- value gaussianPinvFrobTail k d t -->
$e^{-(u-2)/4} + 2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$, whose second term
(`NLAlib.gaussianPinvFrobTail k d t`) is smaller than their $\sqrt{\pi k}\,(e/t)^{d/2}$. Beside it,
Halko, Martinsson and Tropp's deviation bounds (Theorems 10.7 and 10.8) with the constants the
library reaches; they are incomparable with (RSVD1) and better when
$\sigma_k(\mathbf{A}) \ll \|\mathbf{E}\|_{\mathsf{F}}$.

All proofs follow one route. A frame $\mathbf{Z}$ with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_k$ and its orthogonal
complement $\mathbf{V}_2$ turn the structural bound of
`NLAlib/LowRank/Structural/RangeFinder.lean`, which holds almost surely, into a bound by the
Gaussian block
$$\mathbf{S}(\mathbf{V}_2^{\mathsf{H}}\mathbf{X})(\mathbf{Z}^{\mathsf{H}}\mathbf{X})^{+},\qquad
\mathbf{S} = \mathbf{E}\mathbf{V}_2\,,$$
whose tails are in `NLAlib/RandomMatrix/Gaussian/BlockTail.lean`.

**Measurability.** The spectral error of the truncated output depends on the choice the truncation
makes. Its tails hold for every choice of best approximations, measurable or not; for a
non-measurable one they bound `μ.real` of a possibly non-measurable set, which is the outer
measure: the failure event lies in a measurable event of at most the stated probability. At
`truncatedSVD`, which is Borel measurable (`NLAlib.measurable_truncatedSVD`), the failure event
is measurable and the success-set form follows by `measureReal_compl`. Design:
`docs/design/LowRank-S3.md` §3.7 and §8.

## Main results

* The Gram form, every unitarily invariant norm, in the namespace `NLAlib.SymmetricGauge`:
  `measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix`.
* `NLAlib.measureReal_schattenNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.measureReal_specNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`: Schatten
  $p \in [2, \infty]$, Frobenius and spectral.
* `NLAlib.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.measureReal_specNorm_sub_sq_gt_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix`,
  `NLAlib.measureReal_specNorm_sub_truncatedSVD_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`: the
  truncated outputs.
* `NLAlib.measureReal_frobNorm_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.measureReal_specNorm_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix`: the deviation bounds
  of Halko, Martinsson and Tropp.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] {X : Ω → Matrix n l ℝ}

/-! ### The common step -/

/-- A set that lies, outside a null set, inside a set of probability at most $\delta$ has
`μ.real` at most $\delta$; no measurability is needed. -/
private theorem measureReal_le_of_ae_imp [IsFiniteMeasure μ] {s t : Set Ω} {δ : ℝ}
    (hst : ∀ᵐ ω ∂μ, ω ∈ s → ω ∈ t) (ht : μ.real t ≤ δ) : μ.real s ≤ δ :=
  (ENNReal.toReal_mono (measure_ne_top μ t) (measure_mono_ae hst)).trans ht

/-- The common reduction of every tail of this file to a block tail. If $\lvert n \rvert < k$, the
error vanishes almost surely and $\llbracket\mathbf{A}\rrbracket_k = \mathbf{A}$, and `h₀` says
that the failure event is then empty. Otherwise `h₁` receives the frame, its complement and the
block form of the noise term and supplies an event of probability at most $\delta$ that contains
the failure event wherever the rank hypothesis of the structural bound holds. -/
private theorem measureReal_le_of_frame (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    {k : ℕ} (hkl : k ≤ Fintype.card l) {s : Set Ω} {δ : ℝ} (hδ : 0 ≤ δ)
    (h₀ : ∀ ω, A - rsvd A (X ω) = 0 → truncatedSVD A k = A → ω ∉ s)
    (h₁ : ∀ (Z : Matrix n (Fin k) ℝ) (V₂ : Matrix n (Fin (Fintype.card n - k)) ℝ),
      HasOrthonormalCols Z → HasOrthonormalCols V₂ → Zᴴ * V₂ = 0 →
      A * Z * Zᴴ = truncatedSVD A k →
      frobNorm ((A - truncatedSVD A k) * V₂) = frobNorm (A - truncatedSVD A k) →
      specNorm ((A - truncatedSVD A k) * V₂) = singularValues A k →
      (∀ Ω : Matrix n l ℝ, (A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω) =
        (A - truncatedSVD A k) * V₂ * (V₂ᴴ * Ω) * pinv (Zᴴ * Ω)) →
      ∃ s' : Set Ω, μ.real s' ≤ δ ∧ ∀ ω, ((X ω)ᴴ * Z).rank = Z.rank → ω ∈ s → ω ∈ s') :
    μ.real s ≤ δ := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 inferInstance
  rcases le_or_gt k (Fintype.card n) with hkn | hkn
  · obtain ⟨Z, V₂, hZ, hV₂, hZV, hZA, hEV⟩ :=
      exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion (p := Fin k)
        (q := Fin (Fintype.card n - k)) A (Fintype.card_fin k)
        (by simp only [Fintype.card_fin]; omega)
    have hF : frobNorm ((A - truncatedSVD A k) * V₂) = frobNorm (A - truncatedSVD A k) := by
      conv_rhs => rw [← hEV]
      rw [hV₂.frobNorm_mul_conjTranspose_right]
    have hS : specNorm ((A - truncatedSVD A k) * V₂) = singularValues A k := by
      rw [← specNorm_sub_truncatedSVD]
      conv_rhs => rw [← hEV]
      rw [hV₂.specNorm_mul_conjTranspose_right]
    have hM : ∀ Ω : Matrix n l ℝ, (A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω) =
        (A - truncatedSVD A k) * V₂ * (V₂ᴴ * Ω) * pinv (Zᴴ * Ω) := fun Ω => by
      rw [hZA]
      conv_lhs => rw [← hEV]
      simp only [Matrix.mul_assoc]
    obtain ⟨s', hs', hss'⟩ := h₁ Z V₂ hZ hV₂ hZV hZA hF hS hM
    refine measureReal_le_of_ae_imp ?_ hs'
    filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix Z hX
      (by rwa [hZ.rank_eq, Fintype.card_fin])] with ω hω
    exact hss' ω hω
  · have hA : truncatedSVD A k = A := truncatedSVD_of_rank_le A (A.rank_le_card_width.trans hkn.le)
    refine measureReal_le_of_ae_imp (t := ∅) ?_ (by rwa [measureReal_empty])
    filter_upwards [ae_rsvd_eq_self_of_hasLaw_gaussianMatrix A hX
      (A.rank_le_card_width.trans (hkn.le.trans hkl))] with ω hω hs
    exact h₀ ω (by rw [hω, sub_self]) hA hs
/-- The reduction of the (RSVD1) tails to the Frobenius block tail: a statistic $F$ bounded, under
the rank hypothesis, by $b + c\|\mathbf{M}\|_{\mathsf{F}}^2$ for the noise term $\mathbf{M}$ of the
structural bound, and by $b$ when the error vanishes, exceeds
$b + c\,(utk/d)\|\mathbf{E}\|_{\mathsf{F}}^2$ with probability at
most <!-- value gaussianPinvFrobTail k d t -->
$e^{-(u-2)/4} + 2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$ (the second term is
`gaussianPinvFrobTail k d t`). -/
private theorem measureReal_not_le_of_frobNorm_sq_le (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ} (hd : k + d = Fintype.card l + 1) (u : ℝ)
    {t : ℝ} (ht : 0 < t) {F : Ω → ℝ} {b c : ℝ} (hc : 0 ≤ c)
    (hF₀ : ∀ ω, A - rsvd A (X ω) = 0 → truncatedSVD A k = A → F ω ≤ b)
    (hF : ∀ ω (Z : Matrix n (Fin k) ℝ), HasOrthonormalCols Z → A * Z * Zᴴ = truncatedSVD A k →
      ((X ω)ᴴ * Z).rank = Z.rank →
      F ω ≤ b + c * frobNorm ((A - A * Z * Zᴴ) * X ω * pinv (Zᴴ * X ω)) ^ 2) :
    μ.real {ω | ¬ F ω ≤ b + c * (u * t * k / d) * frobNorm (A - truncatedSVD A k) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 inferInstance
  have h0 := gaussianPinvFrobTail_nonneg k d ht
  have he := Real.exp_nonneg (-(u - 2) / 4)
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · have := one_le_gaussianPinvFrobTail_zero (k := k) (by omega) t
    exact measureReal_le_one.trans (by linarith)
  refine measureReal_le_of_frame (k := k) A hX (by omega) (by positivity) (fun ω h hA => ?_)
    (fun Z V₂ hZ hV₂ hZV hZA hSF _ hM => ?_)
  · simp only [Set.mem_ofPred_eq, not_not]
    rw [hA, sub_self, frobNorm_zero]
    simpa using hF₀ ω h hA
  · have hB := measureReal_frobNorm_mul_mul_pinv_sq_gt_le_of_hasLaw_gaussianMatrix hX hZ hV₂
      hZV (by rwa [Fintype.card_fin]) ((A - truncatedSVD A k) * V₂) u ht
    simp only [Fintype.card_fin] at hB
    simp only [← not_le] at hB
    refine ⟨_, hB, fun ω hω hs => ?_⟩
    simp only [Set.mem_ofPred_eq] at hs ⊢
    intro hB'
    rw [hSF] at hB'
    refine hs ?_
    have h := hF ω Z hZ hZA hω
    rw [hM] at h
    calc F ω ≤ b + c * frobNorm ((A - truncatedSVD A k) * V₂ * (V₂ᴴ * X ω) *
          pinv (Zᴴ * X ω)) ^ 2 := h
      _ ≤ b + c * (u * t * k / d * frobNorm (A - truncatedSVD A k) ^ 2) := by gcongr
      _ = b + c * (u * t * k / d) * frobNorm (A - truncatedSVD A k) ^ 2 := by ring

/-! ### The tail of the randomized SVD -/

namespace SymmetricGauge

/-- **The tail of the randomized SVD, Gram form**: for a standard Gaussian $n \times \ell$ test
matrix $\mathbf{X}$, $d = \ell - k + 1$, every unitarily invariant norm, any $u$ and $t > 0$,
$$\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))\bigr\|_{\Phi} \le
\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{utk}{d}\,
\|\mathbf{E}\|_{\mathsf{F}}^2\,,\qquad
\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\,,$$
outside probability <!-- value gaussianPinvFrobTail k d t -->
$e^{-(u-2)/4} + 2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$ (the second term is
`gaussianPinvFrobTail k d t`), with $\mathbf{e}_0$ the first unit coordinate sequence.
[TroppWebber2023, Theorem 8.1 (RSVD1)]; there for squared Schatten
norms, $p \ge 2$, with second failure term $\sqrt{\pi k}\,(t/e)^{-d/2}$; here every quadratic
unitarily invariant norm, and the library's second failure term is smaller than theirs.
For $u \le 2$, or $d = 0$, the bound is at least $1$.
Result: randomized-svd-tail -/
theorem measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        Φ (Finsupp.single 0 1) * (u * t * k / d) * frobNorm (A - truncatedSVD A k) ^ 2 <
        Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  simp only [← not_le]
  refine measureReal_not_le_of_frobNorm_sq_le A hX hd u ht Φ.apply_single_pos.le
    (F := fun ω => Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))))
    (b := Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)))
    (fun ω h hA => by rw [h, hA, sub_self]) (fun ω Z hZ hZA hω => ?_)
  have h := Φ.matrixNorm_conjTranspose_mul_self_sub_rsvd_le hZ hω A
  rw [hZA] at h ⊢
  refine h.trans (add_le_add le_rfl ?_)
  rw [← nuclearNorm_conjTranspose_mul_self]
  exact Φ.matrixNorm_le_apply_single_mul_nuclearNorm _

end SymmetricGauge

/-- **The tail of the randomized SVD, Schatten norms**: for $2 \le p \le \infty$, with the
hypotheses of the Gram form above
(`measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix`
in the namespace `NLAlib.SymmetricGauge`),
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{S_p}^2 \le
\|\mathbf{E}\|_{S_p}^2 + \frac{utk}{d}\,\|\mathbf{E}\|_{\mathsf{F}}^2$$
outside probability <!-- value gaussianPinvFrobTail k d t -->
$e^{-(u-2)/4} + 2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$ (the second term is
`gaussianPinvFrobTail k d t`).
[TroppWebber2023, Theorem 8.1 (RSVD1)]; as printed there, with a smaller second failure term.
Result: randomized-svd-tail -/
theorem measureReal_schattenNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ} (hd : k + d = Fintype.card l + 1)
    {p : ℝ≥0∞} (hp : 2 ≤ p) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | schattenNorm p (A - truncatedSVD A k) ^ 2 + u * t * k / d *
        frobNorm (A - truncatedSVD A k) ^ 2 <
        schattenNorm p (A - rsvd A (X ω)) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  have hq : 1 ≤ p / 2 := by
    rw [ENNReal.le_div_iff_mul_le (by simp) (by simp), one_mul]
    exact hp
  have hq0 : p / 2 ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have h2 : 2 * (p / 2) = p := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
  have h := open SymmetricGauge in
    measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix
      (lpGauge (p / 2) hq) A hX hd u ht
  simpa only [lpGauge_matrixNorm, schattenNorm_conjTranspose_mul_self hq0, h2,
    lpGauge_apply_single_zero, one_mul] using h

/-- **The tail of the randomized SVD, Frobenius norm**: for
$\mathbf{A} \in \mathbb{R}^{m \times n}$, a test matrix $\mathbf{X} \in \mathbb{R}^{n \times \ell}$
with independent standard Gaussian entries (`HasLaw X (gaussianMatrix n l) μ`), a target rank $k$
with $d = \ell - k + 1$ (`hd : k + d = Fintype.card l + 1`),
any $u$ and $t > 0$, <!-- value gaussianPinvFrobTail k d t -->
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 >
\Bigl(1 + \frac{utk}{d}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\Bigr]
\le e^{-(u-2)/4} + \frac{2\sqrt{k}\,(d/(2t))^{d/2}}{\Gamma(d/2 + 1)}\,,$$
the second failure term being `gaussianPinvFrobTail k d t`.
[TroppWebber2023, Theorem 8.1 (RSVD1)]; there at $p = 2$, with a larger second failure term.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ} (hd : k + d = Fintype.card l + 1) (u : ℝ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | (1 + u * t * k / d) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - rsvd A (X ω)) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  have h := measureReal_schattenNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix A hX hd le_rfl
    u ht
  simp only [schattenNorm_two] at h
  rwa [add_mul, one_mul]

/-- **The tail of the randomized SVD, spectral norm**: for
$\mathbf{A} \in \mathbb{R}^{m \times n}$, a test matrix $\mathbf{X} \in \mathbb{R}^{n \times \ell}$
with independent standard Gaussian entries (`HasLaw X (gaussianMatrix n l) μ`), a target rank $k$
with $d = \ell - k + 1$ (`hd : k + d = Fintype.card l + 1`),
any $u$ and $t > 0$, <!-- value gaussianPinvFrobTail k d t -->
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_2^2 >
\sigma_k(\mathbf{A})^2 +
\frac{utk}{d}\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\Bigr]
\le e^{-(u-2)/4} + \frac{2\sqrt{k}\,(d/(2t))^{d/2}}{\Gamma(d/2 + 1)}\,,$$
the second failure term being `gaussianPinvFrobTail k d t`. Singular values are indexed from $0$.
[TroppWebber2023, Theorem 8.1 (RSVD1)]; there at $p = \infty$, with a larger second failure term.
Incomparable with `NLAlib.measureReal_specNorm_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix`, which
is better when
$\sigma_k(\mathbf{A}) \ll \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}$ and small
failure probabilities are wanted.
Result: randomized-svd-tail -/
theorem measureReal_specNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ} (hd : k + d = Fintype.card l + 1) (u : ℝ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | singularValues A k ^ 2 + u * t * k / d * frobNorm (A - truncatedSVD A k) ^ 2 <
        specNorm (A - rsvd A (X ω)) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  have h := measureReal_schattenNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix A hX hd le_top
    u ht
  simpa only [schattenNorm_top, specNorm_sub_truncatedSVD] using h

/-! ### The tail of the truncated randomized SVD -/

/-- **The tail of the truncated randomized SVD, Frobenius norm**: for
$\mathbf{A} \in \mathbb{R}^{m \times n}$, a test matrix $\mathbf{X} \in \mathbb{R}^{n \times \ell}$
with independent standard Gaussian entries (`HasLaw X (gaussianMatrix n l) μ`), a target rank $k$
with $d = \ell - k + 1$ (`hd : k + d = Fintype.card l + 1`),
any $u$ and $t > 0$, <!-- value gaussianPinvFrobTail k d t -->
$$\mathbb{P}\Bigl[
\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k\|_{\mathsf{F}}^2 >
\Bigl(1 + \frac{utk}{d}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\Bigr]
\le e^{-(u-2)/4} + \frac{2\sqrt{k}\,(d/(2t))^{d/2}}{\Gamma(d/2 + 1)}\,,$$
the second failure term being `gaussianPinvFrobTail k d t`. The bound is that of the untruncated
output, for every choice of the truncation: the late truncation costs nothing. The error does not
depend on the choice (`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq`), so the failure event is
measurable.
[TroppWebber2023, Theorem 8.1 (RSVD1)] with [Woodruff2014, Lemma 48]; composed here.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | (1 + u * t * k / d) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  have h := measureReal_not_le_of_frobNorm_sq_le A hX hd u ht zero_le_one
    (F := fun ω => frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2)
    (b := frobNorm (A - truncatedSVD A k) ^ 2)
    (fun ω h hA => by rw [← sub_eq_zero.mp h])
    (fun ω Z hZ hZA hω => by
      have h := hZ.frobNorm_sub_truncatedSVD_rsvd_sq_le hω A (Fintype.card_fin k).le
      rw [hZA] at h ⊢
      rwa [one_mul])
  simp only [not_le] at h
  rw [add_mul, one_mul]
  simpa only [one_mul] using h

/-- **The tail of the truncated randomized SVD, spectral norm**, for any best rank-$k$
approximations: for $\mathbf{A} \in \mathbb{R}^{m \times n}$, a test matrix
$\mathbf{X} \in \mathbb{R}^{n \times \ell}$ with independent standard Gaussian entries
(`HasLaw X (gaussianMatrix n l) μ`), a target rank $k$ with $d = \ell - k + 1$
(`hd : k + d = Fintype.card l + 1`), any
$\mathbf{Y}(\omega) \in \mathbb{R}^{m \times n}$ that is, for every $\omega$, a best rank-$k$
approximation of $\mathsf{rsvd}(\mathbf{A}, \mathbf{X}(\omega))$ (`hY`; no measurability is
assumed), any $u$ and $t > 0$, <!-- value gaussianPinvFrobTail k d t -->
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathbf{Y}\|_2^2 > \sigma_k(\mathbf{A})^2 +
\frac{utk}{d}\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\Bigr]
\le e^{-(u-2)/4} + \frac{2\sqrt{k}\,(d/(2t))^{d/2}}{\Gamma(d/2 + 1)}\,,$$
the second failure term being `gaussianPinvFrobTail k d t`. This is the bound of the untruncated
output; singular values are indexed from $0$. The event may be non-measurable; `μ.real` is then
the outer measure, so this bound says exactly that the failure event lies in a measurable event of
at most this probability (`MeasureTheory.exists_measurable_superset`), and such bounds compose by
`MeasureTheory.measureReal_union_le`. The success-set form, probability at least $1 - \delta$ for
the good event, does not follow without measurability (`MeasureTheory.measureReal_compl` needs
`MeasurableSet`).
[TroppWebber2023, Theorem 8.1 (RSVD1)] with [Gu2015, Theorem 3.4]; composed here.
Result: randomized-svd-tail -/
theorem measureReal_specNorm_sub_sq_gt_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) {Y : Ω → Matrix m n ℝ}
    (hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω)) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | singularValues A k ^ 2 + u * t * k / d * frobNorm (A - truncatedSVD A k) ^ 2 <
        specNorm (A - Y ω) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  have h := measureReal_not_le_of_frobNorm_sq_le A hX hd u ht zero_le_one
    (F := fun ω => specNorm (A - Y ω) ^ 2) (b := singularValues A k ^ 2)
    (fun ω h hA => by
      have h1 := (hY ω).specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le
      have h2 := frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_rsvd_sq_add A (X ω) k
      rw [h, frobNorm_zero] at h2
      linarith)
    (fun ω Z hZ hZA hω => by
      have h1 := (hY ω).specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le
      have h2 := hZ.frobNorm_sub_truncatedSVD_rsvd_sq_le hω A (Fintype.card_fin k).le
      rw [hZA] at h2 ⊢
      linarith)
  simp only [not_le] at h
  simpa only [one_mul] using h

/-- **The tail of the truncated randomized SVD, spectral norm**, for the output
`truncatedSVD (rsvd A (X ω)) k`: for $\mathbf{A} \in \mathbb{R}^{m \times n}$, a test matrix
$\mathbf{X} \in \mathbb{R}^{n \times \ell}$ with independent standard Gaussian entries
(`HasLaw X (gaussianMatrix n l) μ`), a target rank $k$ with $d = \ell - k + 1$
(`hd : k + d = Fintype.card l + 1`),
any $u$ and $t > 0$, <!-- value gaussianPinvFrobTail k d t -->
$$\mathbb{P}\Bigl[
\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k\|_2^2 >
\sigma_k(\mathbf{A})^2 +
\frac{utk}{d}\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\Bigr]
\le e^{-(u-2)/4} + \frac{2\sqrt{k}\,(d/(2t))^{d/2}}{\Gamma(d/2 + 1)}\,,$$
the second failure term being `gaussianPinvFrobTail k d t`. Singular values are indexed from
$0$. The event may be non-measurable (the truncation is a choice); `μ.real` is then the outer
measure, and the bound says that the failure event lies in a measurable event of at most this
probability. The success-set form, probability at least $1 - \delta$ for the good event, does not
follow without measurability (`MeasureTheory.measureReal_compl` needs `MeasurableSet`).
[TroppWebber2023, Theorem 8.1 (RSVD1)] with [Gu2015, Theorem 3.4]; composed here.
Result: randomized-svd-tail -/
theorem measureReal_specNorm_sub_truncatedSVD_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | singularValues A k ^ 2 + u * t * k / d * frobNorm (A - truncatedSVD A k) ^ 2 <
        specNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t :=
  measureReal_specNorm_sub_sq_gt_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix A hX hd
    (fun _ => isBestRankApprox_truncatedSVD _ k) u ht

/-! ### The deviation bounds of Halko, Martinsson and Tropp -/

/-- **Deviation bound for the Frobenius error of the randomized SVD**: for a standard Gaussian
$n \times \ell$ test matrix, $k < \ell$, $d = \ell - k + 1$, $u \ge 0$ and
$t > 0$, <!-- value gaussianPinvSpecNormBound k \ell -->
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}} \le
\Bigl(1 + t\sqrt{k/d}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}} +
ut\,\frac{e}{\ell - k}\sqrt{(\ell + k - 1)/2}\,\sigma_k(\mathbf{A})$$
outside probability <!-- value gaussianPinvFrobTail k d t^2 -->
$t^{-(\ell - k)} + 2\sqrt{k}\,(d/(2t^2))^{d/2}/\Gamma(d/2 + 1) + e^{-u^2/2}$; the constant is
`gaussianPinvSpecNormBound k ℓ`, the second failure term `gaussianPinvFrobTail k d (t ^ 2)`.
[HalkoMartinssonTropp2011, Theorem 10.7]; HMT print $\sqrt{12k/p}$, $e\sqrt{k+p}/(p+1)$ and
$5t^{-p} + 2e^{-u^2/2}$ for $p = \ell - k \ge 4$ and $u, t \ge 1$, from their Proposition 10.4,
whose tails are not reached here; the Frobenius part of this failure term is below HMT's in every
practical regime, the spectral part loses one power of $t$. Given `hd`, `hkl` is $d \ge 2$.
Incomparable with `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`
(Tropp and Webber's form): this one is better when
$\sigma_k(\mathbf{A}) \ll \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}$ and small
failure probabilities are wanted.
Result: randomized-svd-deviation-bound -/
theorem measureReal_frobNorm_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ} (hd : k + d = Fintype.card l + 1)
    (hkl : k < Fintype.card l) {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    μ.real {ω | (1 + t * √((k : ℝ) / d)) * frobNorm (A - truncatedSVD A k) + u * t *
        gaussianPinvSpecNormBound k (Fintype.card l) * singularValues A k <
        frobNorm (A - rsvd A (X ω))} ≤
      t ^ (-((Fintype.card l : ℝ) - k)) + gaussianPinvFrobTail k d (t ^ 2) +
        Real.exp (-u ^ 2 / 2) := by
  simp only [← not_le]
  have hC := gaussianPinvSpecNormBound_nonneg hkl
  refine measureReal_le_of_frame A hX hkl.le (by
      have := gaussianPinvFrobTail_nonneg k d (pow_pos ht 2)
      positivity) (fun ω h hA => ?_) (fun Z V₂ hZ hV₂ hZV hZA hSF hS2 hM => ?_)
  · simp only [Set.mem_ofPred_eq, not_not]
    rw [h, frobNorm_zero]
    have := singularValues_nonneg A k
    positivity
  · have hB := measureReal_frobNorm_mul_mul_pinv_gt_le_of_hasLaw_gaussianMatrix hX hZ hV₂ hZV
      (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin]) ((A - truncatedSVD A k) * V₂) hu ht
    simp only [Fintype.card_fin, hSF, hS2] at hB
    simp only [← not_le] at hB
    refine ⟨_, hB, fun ω hω hs => ?_⟩
    simp only [Set.mem_ofPred_eq] at hs ⊢
    intro hB'
    refine hs ?_
    have h := hZ.frobNorm_sub_rsvd_sq_le hω A
    rw [hM, hZA] at h
    have hsq : frobNorm (A - rsvd A (X ω)) ≤ frobNorm (A - truncatedSVD A k) +
        frobNorm ((A - truncatedSVD A k) * V₂ * (V₂ᴴ * X ω) * pinv (Zᴴ * X ω)) := by
      refine (pow_le_pow_iff_left₀ (frobNorm_nonneg _) (by positivity) two_ne_zero).mp
        (h.trans ?_)
      nlinarith [frobNorm_nonneg (A - truncatedSVD A k),
        frobNorm_nonneg ((A - truncatedSVD A k) * V₂ * (V₂ᴴ * X ω) * pinv (Zᴴ * X ω))]
    linarith

/-- **Deviation bound for the spectral error of the randomized SVD**: for
$\mathbf{A} \in \mathbb{R}^{m \times n}$, a test matrix $\mathbf{X} \in \mathbb{R}^{n \times \ell}$
with independent standard Gaussian entries (`HasLaw X (gaussianMatrix n l) μ`), a target rank
$k < \ell$ (`hkl`) with $d = \ell - k + 1$ (`hd : k + d = Fintype.card l + 1`), $u \ge 0$ and
$t > 0$, <!-- value gaussianPinvSpecNormBound k \ell --> <!-- value gaussianPinvFrobTail k d t^2 -->
$$\begin{aligned}&\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_2 >
\Bigl(1 + t\sqrt{k/d}\Bigr)\sigma_k(\mathbf{A}) +
t\,\frac{e}{\ell - k}\sqrt{(\ell + k - 1)/2}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}} \\
&\qquad + ut\,\frac{e}{\ell - k}\sqrt{(\ell + k - 1)/2}\,\sigma_k(\mathbf{A})\Bigr]
\le t^{-(\ell - k)} + \frac{2\sqrt{k}\,(d/(2t^2))^{d/2}}{\Gamma(d/2 + 1)} + e^{-u^2/2}\,,
\end{aligned}$$
singular values indexed from $0$; the constant is `gaussianPinvSpecNormBound k ℓ`, the second
failure term `gaussianPinvFrobTail k d (t ^ 2)`.
[HalkoMartinssonTropp2011, Theorem 10.8]; HMT print $\sqrt{12k/p}$, $e\sqrt{k+p}/(p+1)$ and
$5t^{-p} + e^{-u^2/2}$ for $p = \ell - k \ge 4$ and $u, t \ge 1$, from their Proposition 10.4,
whose tails are not reached here; the Frobenius part of this failure term is below HMT's in every
practical regime, the spectral part loses one power of $t$. Given `hd`, `hkl` is $d \ge 2$.
Incomparable with `NLAlib.measureReal_specNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`
(Tropp and Webber's form).
Result: randomized-svd-deviation-bound -/
theorem measureReal_specNorm_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ} (hd : k + d = Fintype.card l + 1)
    (hkl : k < Fintype.card l) {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    μ.real {ω | (1 + t * √((k : ℝ) / d)) * singularValues A k + t *
        gaussianPinvSpecNormBound k (Fintype.card l) * frobNorm (A - truncatedSVD A k) + u * t *
        gaussianPinvSpecNormBound k (Fintype.card l) * singularValues A k <
        specNorm (A - rsvd A (X ω))} ≤
      t ^ (-((Fintype.card l : ℝ) - k)) + gaussianPinvFrobTail k d (t ^ 2) +
        Real.exp (-u ^ 2 / 2) := by
  simp only [← not_le]
  have hC := gaussianPinvSpecNormBound_nonneg hkl
  refine measureReal_le_of_frame A hX hkl.le (by
      have := gaussianPinvFrobTail_nonneg k d (pow_pos ht 2)
      positivity) (fun ω h hA => ?_) (fun Z V₂ hZ hV₂ hZV hZA hSF hS2 hM => ?_)
  · simp only [Set.mem_ofPred_eq, not_not]
    rw [h, specNorm_zero]
    have := singularValues_nonneg A k
    positivity
  · have hB := measureReal_specNorm_mul_mul_pinv_gt_le_of_hasLaw_gaussianMatrix hX hZ hV₂ hZV
      (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin]) ((A - truncatedSVD A k) * V₂) hu ht
    simp only [Fintype.card_fin, hSF, hS2] at hB
    simp only [← not_le] at hB
    refine ⟨_, hB, fun ω hω hs => ?_⟩
    simp only [Set.mem_ofPred_eq] at hs ⊢
    intro hB'
    refine hs ?_
    have h := hZ.specNorm_sub_rsvd_le hω A
    rw [hM, hZA, specNorm_sub_truncatedSVD] at h
    linarith

end NLAlib
