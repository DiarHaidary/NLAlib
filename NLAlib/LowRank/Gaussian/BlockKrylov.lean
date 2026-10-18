/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Growth
public import NLAlib.LowRank.Gaussian.Filter
public import NLAlib.LowRank.Structural.BlockKrylov

/-!
# Gapped bounds for randomized block Krylov and subspace iteration

Expected errors of randomized block Krylov iteration $\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)$
and of randomized subspace iteration with $p$ power steps,
$\mathsf{rsvd}(\mathbf{A}, (\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})$, for a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$, in terms of the relative gap
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$ (`NLAlib.singularGapRatio A h t`) between
the last singular value $\sigma_h$ of the head, $h + 1 = r$, and a tail index $t \ge r$ with
$t + 2 \le \ell$:
$$\mathbb{E}\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_2^2 \le
\sigma_r(\mathbf{A})^2 + 4e^{-8(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
and the same with $e^{-8p\gamma}$ for subspace iteration; likewise in the Frobenius norm, in every
quadratic unitarily invariant norm, and for the late-truncated outputs
$\llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r$ with the same right sides (reverse
Eckart–Young and Gu's projected form). These are Tropp and Webber's gapped bounds at an even number
$m = 2q$, respectively $m = 2p + 2$, of matrix products. The RBKI bounds come from the filtered
range finder (`NLAlib.LowRank.Gaussian.Filter`) at the Chebyshev filter
$T_{q-1}(2x/\sigma_t^2 - 1)$, of degree $q - 1$, through
`NLAlib.singularValues_sub_rbki_le_of_degree_lt`.

## Main results

* `NLAlib.integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`, and the
  Gram form in the `NLAlib.SymmetricGauge` namespace: RBKI.
* `NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`, and
  the Gram form: RSI.
* `NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
  and their RSI twins: the late-truncated outputs.

The integrability companions are law-free, in `NLAlib.LowRank.Random.RangeFinder`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] [DecidableEq n] {X : Ω → Matrix n l ℝ}

-- Stage B5b

/-! ### Randomized block Krylov iteration -/

/-- **The gapped bound for randomized block Krylov iteration, spectral norm**: for a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $q \ge 1$ blocks, a head of $r = h + 1$
singular values, a tail index $t \ge r$ with $t + 2 \le \ell$, and
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_2^2 \le
\sigma_r(\mathbf{A})^2 + 4e^{-8(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
No positivity hypothesis: when $\sigma_t = 0$ the error is zero almost surely.
[TroppWebber2023, Theorem 9.2 (RBKI)], at $p = \infty$; there with $m$ products and the exponent
$4(m - 2)\sqrt{\gamma}$, indices from $1$ ($\sigma_r$, $\sigma_s$ for our $\sigma_h$, $\sigma_t$),
$k \ge s + 1$ for our $t + 2 \le \ell$; here $m = 2q$ (odd $m$ is not covered).
Result: rbki-gapped-error -/
theorem integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, specNorm (A - rbki A (X ω) q) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  sorry

/-- **The gapped bound for randomized block Krylov iteration, Frobenius norm**: under the
hypotheses of the spectral form
(`NLAlib.integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`),
$$\mathbb{E}\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
4e^{-8(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
[TroppWebber2023, Theorem 9.2 (RBKI)], at $p = 2$; there with $m = 2q$ products.
Result: rbki-gapped-error -/
theorem integral_frobNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, frobNorm (A - rbki A (X ω) q) ^ 2 ∂μ ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  sorry

-- The declaration name alone, with its `SymmetricGauge` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for randomized block Krylov iteration, Gram form**: under the hypotheses of
the spectral form, in every unitarily invariant norm,
$$\mathbb{E}\bigl\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\bigr\|_{\Phi} \le
\bigl\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r)^{\mathsf{H}}
(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r)\bigr\|_{\Phi} +
\Phi(\mathbf{e}_0)\,4e^{-8(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
with $\mathbf{E} = \mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)$: every quadratic
unitarily invariant norm, squared Schatten norms for $p \ge 2$ included ($\Phi(\mathbf{e}_0) = 1$).
[TroppWebber2023, Theorem 9.2 (RBKI)]; there for Schatten $2 \le p \le \infty$ and $m = 2q$.
Result: rbki-gapped-error -/
theorem
SymmetricGauge.integral_matrixNorm_conjTranspose_mul_self_sub_rbki_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    {h r t q : ℕ} (hr : h + 1 = r) (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, Φ.matrixNorm ((A - rbki A (X ω) q)ᴴ * (A - rbki A (X ω) q)) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A r)ᴴ * (A - truncatedSVD A r)) +
        Φ (Finsupp.single 0 1) *
          (4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t))) *
            ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  sorry

/-! ### Randomized subspace iteration -/

-- SKELETON-NOTE: the filter x ↦ x^p has c = σ_h^{2p}, zero when σ_h = 0 and p ≥ 1; that case
-- (rank A ≤ h) needs exact recovery, not the filtered bound. Likewise σ_t = 0 for RBKI (§6.2).
/-- **The gapped bound for randomized subspace iteration, spectral norm**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$, $p$ power steps, a head of $r = h + 1$ singular values, a
tail index $t \ge r$ with $t + 2 \le \ell$, and $\gamma = (\sigma_h - \sigma_t)/(\sigma_h +
\sigma_t)$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, (\mathbf{A}^{\mathsf{H}}\mathbf{A})^p
\mathbf{X})\|_2^2 \le \sigma_r(\mathbf{A})^2 + e^{-8p\gamma}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
At $p = 0$ it is the bound of the randomized SVD at rank $t$, weakened to $\sigma_r$.
[TroppWebber2023, Theorem 9.2 (RSI)], at $p = \infty$; there with $m$ products and the exponent
$4(m - 2)\gamma$; here $m = 2p + 2$ (odd $m$ is not covered).
Result: rsi-gapped-error -/
theorem integral_specNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (p : ℕ) :
    ∫ ω, specNorm (A - rsvd A ((Aᴴ * A) ^ p * X ω)) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        Real.exp (-8 * (p : ℝ) * singularGapRatio A h t) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  sorry

/-- **The gapped bound for randomized subspace iteration, Frobenius norm**: under the hypotheses
of the spectral form
(`NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`),
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, (\mathbf{A}^{\mathsf{H}}\mathbf{A})^p
\mathbf{X})\|_{\mathsf{F}}^2 \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
e^{-8p\gamma}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
[TroppWebber2023, Theorem 9.2 (RSI)], at $p = 2$; there with $m = 2p + 2$ products.
Result: rsi-gapped-error -/
theorem integral_frobNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (p : ℕ) :
    ∫ ω, frobNorm (A - rsvd A ((Aᴴ * A) ^ p * X ω)) ^ 2 ∂μ ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        Real.exp (-8 * (p : ℝ) * singularGapRatio A h t) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  sorry

-- The declaration name alone, with its `SymmetricGauge` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for randomized subspace iteration, Gram form**: under the hypotheses of the
spectral form, in every unitarily invariant norm,
$$\mathbb{E}\bigl\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\bigr\|_{\Phi} \le
\bigl\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r)^{\mathsf{H}}
(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r)\bigr\|_{\Phi} +
\Phi(\mathbf{e}_0)\,e^{-8p\gamma}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
with $\mathbf{E} = \mathbf{A} - \mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})$.
[TroppWebber2023, Theorem 9.2 (RSI)]; there for Schatten $2 \le p \le \infty$ and $m = 2p + 2$.
Result: rsi-gapped-error -/
theorem
SymmetricGauge.integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_pow_mul_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    {h r t : ℕ} (hr : h + 1 = r) (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (p : ℕ) :
    ∫ ω, Φ.matrixNorm ((A - rsvd A ((Aᴴ * A) ^ p * X ω))ᴴ * (A - rsvd A ((Aᴴ * A) ^ p * X ω))) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A r)ᴴ * (A - truncatedSVD A r)) +
        Φ (Finsupp.single 0 1) * Real.exp (-8 * (p : ℝ) * singularGapRatio A h t) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  sorry

/-! ### The late-truncated outputs -/

/-- **The gapped bound for truncated randomized block Krylov iteration, spectral norm**: under the
hypotheses of the untruncated form
(`NLAlib.integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`), the rank-$r$
truncation keeps its right side,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r\|_2^2 \le
\sigma_r(\mathbf{A})^2 + 4e^{-8(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
by reverse Eckart–Young
(`NLAlib.IsBestRankApprox.specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le`) and Gu's projected
form. [TroppWebber2023, §9.1, remark after Theorem 9.2]; [Gu2015, Theorem 3.4]; there stated
without a proof.
Result: rbki-gapped-error -/
theorem integral_specNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  sorry

/-- **The gapped bound for truncated randomized block Krylov iteration, Frobenius norm**: under
the hypotheses of the untruncated form, the rank-$r$ truncation keeps its right side,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r
\|_{\mathsf{F}}^2 \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
4e^{-8(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,,$$
by Gu's projected form
(`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add`) and head capture
in expectation. [TroppWebber2023, §9.1, remark after Theorem 9.2]; there stated without a proof.
Result: rbki-gapped-error -/
theorem integral_frobNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, frobNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2 ∂μ ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  sorry

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for truncated randomized subspace iteration, spectral norm**: under the
hypotheses of the untruncated form, the rank-$r$ truncation keeps its right side,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})\rrbracket_r\|_2^2 \le \sigma_r(\mathbf{A})^2 +
e^{-8p\gamma}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
[TroppWebber2023, §9.1, remark after Theorem 9.2]; there stated without a proof.
Result: rsi-gapped-error -/
theorem
integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (p : ℕ) :
    ∫ ω, specNorm (A - truncatedSVD (rsvd A ((Aᴴ * A) ^ p * X ω)) r) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        Real.exp (-8 * (p : ℝ) * singularGapRatio A h t) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  sorry

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for truncated randomized subspace iteration, Frobenius norm**: under the
hypotheses of the untruncated form, the rank-$r$ truncation keeps its right side,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})\rrbracket_r\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
e^{-8p\gamma}\,\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
[TroppWebber2023, §9.1, remark after Theorem 9.2]; there stated without a proof.
Result: rsi-gapped-error -/
theorem
integral_frobNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (p : ℕ) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A ((Aᴴ * A) ^ p * X ω)) r) ^ 2 ∂μ ≤
      frobNorm (A - truncatedSVD A r) ^ 2 +
        Real.exp (-8 * (p : ℝ) * singularGapRatio A h t) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2 := by
  sorry

end NLAlib
