/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.Convex.Integral
public import NLAlib.LowRank.Gaussian.BlockKrylov
public import NLAlib.Matrix.Functions.TraceFunctions
public import NLAlib.Polynomial.Chebyshev.Filter

/-!
# Gapless bounds for randomized block Krylov and subspace iteration

Expected spectral errors of randomized block Krylov iteration $\mathsf{rbki}(\mathbf{A},
\mathbf{X}, q)$ and of randomized subspace iteration with $p$ power steps, for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$ and a target rank $r$ with $r + 2 \le \ell$, that need no
gap in the spectrum of $\mathbf{A}$. Two incomparable forms.

**The $(1 + \varepsilon)$ form** (Musco and Musco's case split, applied to the gapped bounds of
`NLAlib.LowRank.Gaussian.BlockKrylov`): for every $\varepsilon > 0$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r\|_2^2
\le (1 + \varepsilon)^2\sigma_r(\mathbf{A})^2 +
4e^{-8(q-1)\sqrt{\varepsilon/(2 + \varepsilon)}}\,\frac{r}{\ell - r - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,,$$
for the truncated and the untruncated output, so that depth
$q = O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\varepsilon})$ gives relative error
$1 + \varepsilon$.
The case split is on the number of singular values at least $(1 + \varepsilon)\sigma_r$; it is
deterministic and uses only the gapped bound, `NLAlib.singularValues_sub_truncatedSVD_rsvd_le_of_le`
and reverse Eckart–Young.

**Tropp and Webber's form**, with the exact constants of their Theorem 9.1 at an even number of
products: $\sigma_r(\mathbf{A})^2$ times a factor tending to $1$ at the rate $1/(q-1)^2$ for RBKI
and $1/(2p + 1)$ for RSI, through the range-finder tail ratio `NLAlib.rangeFinderTailRatio`
<!-- mention rangeFinderTailRatio --> and the almost-convex Jensen inequality
(`HasSupportingLineOn.le_integral_comp`).

## Main results

* `NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_specNorm_sub_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`: the
  $(1 + \varepsilon)$ form for RBKI, truncated and untruncated, and its asymptotic form
  `NLAlib.exists_forall_integral_specNorm_sub_truncatedSVD_rbki_sq_le_of_hasLaw_gaussianMatrix`.
* the same for RSI, truncated and untruncated:
  `integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_mul_rpow_of_hasLaw_gaussianMatrix`: Tropp and
  Webber's form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] [DecidableEq n] {X : Ω → Matrix n l ℝ}

-- Stage B6a

/-- **The gapless bound for truncated randomized block Krylov iteration, $(1 + \varepsilon)$
form**: for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $q \ge 1$ blocks, a
target rank $r$ with $r + 2 \le \ell$, and every $\varepsilon > 0$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r\|_2^2
\le (1 + \varepsilon)^2\sigma_r(\mathbf{A})^2 +
4e^{-8(q-1)\sqrt{\varepsilon/(2 + \varepsilon)}}\,\frac{r}{\ell - r - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,.$$
No gap is assumed: with $h$ the number of singular values at least
$(1 + \varepsilon)\sigma_r(\mathbf{A})$, either $h = 0$ and the error is at most
$\|\mathbf{A}\|_2 < (1 + \varepsilon)\sigma_r$, or the gapped bound at head $h$ and tail index $r$
applies with gap at least $\varepsilon/(2 + \varepsilon)$. The constants are composed here, not
printed in either source: $4$ and $8$ from TW Theorem 9.2 at $m = 2q$, the gap from MM's case
split with $1 + \varepsilon$ in place of their $1 + \varepsilon/2$. Better than Tropp and Webber's
gapless form (`NLAlib.integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix`) for a
fixed relative accuracy $\varepsilon$; that one is better as $q \to \infty$ at fixed $\mathbf{A}$.
Asymptotic form:
`NLAlib.exists_forall_integral_specNorm_sub_truncatedSVD_rbki_sq_le_of_hasLaw_gaussianMatrix`.
[MuscoMusco2015, Theorem 10 (proof)]; [TroppWebber2023, Theorem 9.2]; there with probability
$99/100$ (MM) or untruncated and gapped (TW); here in expectation.
Result: rbki-gapless-error -/
theorem integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2 ∂μ ≤
      (1 + ε) ^ 2 * singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (ε / (2 + ε))) *
          ((r : ℝ) / ((Fintype.card l : ℝ) - r - 1)) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  sorry

/-- **The gapless bound for randomized block Krylov iteration, $(1 + \varepsilon)$ form**: under
the hypotheses of the truncated form
(`NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`),
$$\mathbb{E}\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_2^2
\le (1 + \varepsilon)^2\sigma_r(\mathbf{A})^2 +
4e^{-8(q-1)\sqrt{\varepsilon/(2 + \varepsilon)}}\,\frac{r}{\ell - r - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,.$$
[MuscoMusco2015, Theorem 10 (proof)]; [TroppWebber2023, Theorem 9.2]; constants composed here.
Result: rbki-gapless-error -/
theorem integral_specNorm_sub_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, specNorm (A - rbki A (X ω) q) ^ 2 ∂μ ≤
      (1 + ε) ^ 2 * singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (ε / (2 + ε))) *
          ((r : ℝ) / ((Fintype.card l : ℝ) - r - 1)) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  sorry

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapless bound for truncated randomized subspace iteration, $(1 + \varepsilon)$ form**:
for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $p$ power steps, a target rank
$r$ with $r + 2 \le \ell$, and every $\varepsilon > 0$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})\rrbracket_r\|_2^2
\le (1 + \varepsilon)^2\sigma_r(\mathbf{A})^2 +
e^{-8p\varepsilon/(2 + \varepsilon)}\,\frac{r}{\ell - r - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,.$$
[MuscoMusco2015, Theorem 10 (proof)]; [TroppWebber2023, Theorem 9.2 (RSI)]; there for block Krylov
iteration (MM) or gapped (TW); constants composed here.
Result: rsi-gapless-error -/
theorem
integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, specNorm (A - truncatedSVD (rsvd A ((Aᴴ * A) ^ p * X ω)) r) ^ 2 ∂μ ≤
      (1 + ε) ^ 2 * singularValues A r ^ 2 +
        Real.exp (-8 * (p : ℝ) * (ε / (2 + ε))) *
          ((r : ℝ) / ((Fintype.card l : ℝ) - r - 1)) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  sorry

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapless bound for randomized subspace iteration, $(1 + \varepsilon)$ form**: under the
hypotheses of the truncated form
(`NLAlib.integral_specNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`),
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})\|_2^2
\le (1 + \varepsilon)^2\sigma_r(\mathbf{A})^2 +
e^{-8p\varepsilon/(2 + \varepsilon)}\,\frac{r}{\ell - r - 1}
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,.$$
[MuscoMusco2015, Theorem 10 (proof)]; [TroppWebber2023, Theorem 9.2 (RSI)]; constants composed
here.
Result: rsi-gapless-error -/
theorem integral_specNorm_sub_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, specNorm (A - rsvd A ((Aᴴ * A) ^ p * X ω)) ^ 2 ∂μ ≤
      (1 + ε) ^ 2 * singularValues A r ^ 2 +
        Real.exp (-8 * (p : ℝ) * (ε / (2 + ε))) *
          ((r : ℝ) / ((Fintype.card l : ℝ) - r - 1)) * frobNorm (A - truncatedSVD A r) ^ 2 := by
  sorry

-- SKELETON-NOTE: checked on paper with ε₀ = 1/2, the explicit bound at ε/3, a large C and
-- ‖A - ⟦A⟧_r‖_F² ≤ |n| σ_r², r/(ℓ - r - 1) ≤ |n|; at |n| = 0, log 0 = 0 allows q = 0, harmless
-- since then A = 0.
/-- **Depth $O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\varepsilon})$ suffices for randomized
block Krylov iteration**, spectral norm, truncated output: there are absolute constants
$C, \varepsilon_0 > 0$ such that for a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$,
a target rank $r$ with $r + 2 \le \ell$, $0 < \varepsilon \le \varepsilon_0$ and
$q \ge C\log(\lvert n \rvert/\varepsilon)/\sqrt{\varepsilon}$ blocks,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_r\|_2^2
\le (1 + \varepsilon)\,\sigma_r(\mathbf{A})^2\,.$$
The asymptotic form of
`NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`, at
$\varepsilon/3$, with $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 \le
\lvert n \rvert\,\sigma_r(\mathbf{A})^2$ and $r/(\ell - r - 1) \le \lvert n \rvert$ when
$r < \lvert n \rvert$ (for $r \ge \lvert n \rvert$ the error is zero almost surely).
[MuscoMusco2015, Theorem 10]; [MartinssonTropp2020, Theorem 11.11]; there with probability $99/100$
and $q = \Theta(\log(d/\varepsilon)/\sqrt{\varepsilon})$ (MM), or stated without proof (MT).
Asymptotic:
NLAlib.integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
Result: rbki-gapless-error -/
theorem exists_forall_integral_specNorm_sub_truncatedSVD_rbki_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (r q : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ → r + 2 ≤ Fintype.card l → 0 < ε →
      ε ≤ ε₀ → C * Real.log (Fintype.card n / ε) / Real.sqrt ε ≤ q →
      ∫ ω, specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2 ∂μ ≤
        (1 + ε) * singularValues A r ^ 2 := by
  sorry

-- Stage B6b

-- SKELETON-NOTE: constants as in TW Theorem 9.1 (RBKI) at m = 2q, checked against the text and by
-- a Monte Carlo run on 8 × 7 matrices (worst ratio of mean to bound 0.97); the proof needs TW
-- Lemma 9.3 part 5 rescaled to [σ_r², ∞); `hasSupportingLineOn_mul_eval_T_sq` is the case σ_r = 1.
/-- **Tropp and Webber's gapless bound for randomized block Krylov iteration**: for a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $q \ge 2$ blocks, a target rank $r$ with
$r + 2 \le \ell$ and $\sigma_r(\mathbf{A}) > 0$,
the bound <!-- value rangeFinderTailRatio \mathbf{A} r \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\|_2^2 \le
\sigma_r(\mathbf{A})^2\exp\biggl(\frac{1}{16(q-1)^2}\log^2\biggl(4\Bigl(1 + \frac{r}{\ell - r - 1}\,
\frac{\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2}{\sigma_r(\mathbf{A})^2}
\Bigr)\biggr)\biggr)\,,$$
the argument of the logarithm being four times the range-finder tail ratio
`NLAlib.rangeFinderTailRatio`. Both hypotheses are needed: at $q = 1$ the right side is
$\sigma_r(\mathbf{A})^2$, below the error of the randomized SVD, and $\sigma_r(\mathbf{A}) > 0$
normalises the ratio. Incomparable with the $(1 + \varepsilon)$ form
(`NLAlib.integral_specNorm_sub_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`): this one
tends to $\sigma_r(\mathbf{A})^2$ as $q \to \infty$.
[TroppWebber2023, Theorem 9.1 (RBKI)]; there in logarithmic form with $m$ products and the rate
$1/(4(m-2)^2)$, indices from $1$; here $m = 2q$ (odd $m$ is not covered).
Result: rbki-gapless-error -/
theorem integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ} (hr : r + 2 ≤ Fintype.card l) (hq : 2 ≤ q)
    (hσ : 0 < singularValues A r) :
    ∫ ω, specNorm (A - rbki A (X ω) q) ^ 2 ∂μ ≤
      singularValues A r ^ 2 *
        Real.exp (Real.log (4 * rangeFinderTailRatio A r (Fintype.card l)) ^ 2 /
          (16 * ((q : ℝ) - 1) ^ 2)) := by
  sorry

/-- **Tropp and Webber's gapless bound for randomized subspace iteration**: for a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $p$ power steps, a target rank $r$ with
$r + 2 \le \ell$ and $\sigma_r(\mathbf{A}) > 0$,
the bound <!-- value rangeFinderTailRatio \mathbf{A} r \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A},
(\mathbf{A}^{\mathsf{H}}\mathbf{A})^p\mathbf{X})\|_2^2 \le
\sigma_r(\mathbf{A})^2\Bigl(1 + \frac{r}{\ell - r - 1}\,
\frac{\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2}{\sigma_r(\mathbf{A})^2}
\Bigr)^{1/(2p+1)}\,,$$
the range-finder tail ratio `NLAlib.rangeFinderTailRatio` to the power $1/(2p + 1)$. At $p = 0$
it is the bound of the randomized SVD (TW Theorem 8.1). The proof uses the power lemma
(`IsStarProjection.specNorm_mul_pow_le`) in place of the almost-convex Jensen inequality.
[TroppWebber2023, Theorem 9.1 (RSI)]; there in logarithmic form with $m$ products and the rate
$1/(m - 1)$; here $m = 2p + 2$. The power lemma is [HalkoMartinssonTropp2011, Proposition 8.6].
Result: rsi-gapless-error -/
theorem integral_specNorm_sub_rsvd_pow_mul_sq_le_mul_rpow_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (p : ℕ) (hσ : 0 < singularValues A r) :
    ∫ ω, specNorm (A - rsvd A ((Aᴴ * A) ^ p * X ω)) ^ 2 ∂μ ≤
      singularValues A r ^ 2 *
        rangeFinderTailRatio A r (Fintype.card l) ^ (1 / (2 * (p : ℝ) + 1)) := by
  sorry

end NLAlib
