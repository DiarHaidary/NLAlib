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

namespace SymmetricGauge

-- SKELETON-NOTE: for r or t beyond |n| the frames have |n| columns and `hhead` at padded
-- indices asks c ≤ |f(0)|; the RBKI and RSI instances meet that case through σ_t = 0 or
-- σ_h = 0 (exact recovery), not through this lemma.
/-- **The filtered range finder in expectation, Gram form**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$, a real polynomial $f$ with
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
  sorry

end SymmetricGauge

/-- **The filtered range finder in expectation, spectral norm**: under the hypotheses of the Gram
form above,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A},
f(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{X})\|_2^2 \le \sigma_r(\mathbf{A})^2 +
\Bigl(\frac{a}{c}\Bigr)^2\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
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
  sorry

/-- **The filtered range finder in expectation, Frobenius norm**: under the hypotheses of the Gram
form above,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A},
f(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{X})\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 +
\Bigl(\frac{a}{c}\Bigr)^2\frac{t}{\ell - t - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
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
  sorry

/-- **Head capture in expectation**: under the hypotheses of the Gram form above, the
filtered sketch captures the best rank-$r$ approximation up to
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
  sorry

end NLAlib
