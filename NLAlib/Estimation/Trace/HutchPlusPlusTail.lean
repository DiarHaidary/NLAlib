/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus
public import NLAlib.LowRank.Oblivious.SubGaussian

/-!
# Hutch++: high-probability bounds

The deviation of Hutch++ (`NLAlib.hutchpp`) with residual probes that have independent
sub-Gaussian entries. The primary theorem takes the range-finder guarantee as a hypothesis: if
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{S})\|_{\mathsf{F}}^2 \le
K\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2$ fails with probability at most
$\delta_1$, the Girard–Hutchinson tail (`NLAlib.measureReal_abs_girardHutchinson_sub_trace_ge_le`,
from Hanson–Wright) on the compressed residual, conditionally on the sketch, adds a sub-exponential
term. The sub-Gaussian range finder
(`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`) and the nuclear-norm
tail bound (`NLAlib.frobNorm_sub_truncatedSVD_le_nuclearNorm_div`) turn it into the relative-error
guarantee of Meyer, Musco, Musco and Woodruff: $O(\sqrt{\log(1/\delta)}/\varepsilon +
\log(1/\delta))$ products give $\lvert \mathsf{hutchpp} - \operatorname{tr}\mathbf{A} \rvert \le
\varepsilon\|\mathbf{A}\|_*$ with probability $1 - \delta$. Real throughout. The constants are
explicit: the range-finder factor $1 + 10c$ replaces MMMW's $2$ (their route through Musco and
Musco is not in the library), and the Hanson–Wright constant is $1/196$. Design:
`docs/design/Estimation-HutchPP.md` §3.4.

## Main results

* `NLAlib.measureReal_abs_hutchpp_sub_trace_ge_le`: the tail given a range-finder guarantee.
* `NLAlib.measureReal_abs_hutchpp_sub_trace_ge_le_of_isSubgaussianVector`,
  `NLAlib.measureReal_abs_hutchpp_sub_trace_ge_le_of_hasLaw_gaussianMatrix`: sub-Gaussian and
  Gaussian sketches.
* `NLAlib.measureReal_abs_hutchpp_sub_trace_gt_le_of_isSubgaussianVector`: the relative error in
  the nuclear norm, and its asymptotic form
  `NLAlib.exists_forall_measureReal_abs_hutchpp_sub_trace_gt_le_of_isSubgaussianVector`.
* `Matrix.PosSemidef.measureReal_hutchpp_lt_one_sub_mul_trace_le_of_isSubgaussianVector`,
  `Matrix.PosSemidef.measureReal_one_add_mul_trace_lt_hutchpp_le_of_isSubgaussianVector`: the two
  one-sided $(1 \pm \varepsilon)$ bounds for positive semidefinite matrices.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n s t : Type*} [Fintype n]
  [Fintype s] [Fintype t] [DecidableEq n]

-- Stage TE-5

/-- **The deviation of Hutch++ given a range-finder guarantee.** Let the sketch test matrix
$\mathbf{S}$ be almost everywhere measurable and the $n \times \ell$ residual test matrix
$\mathbf{G}$ be independent of it, with independent entries that each satisfy the sub-Gaussian
moment generating function bound with variance proxy $c$ (`HasSubgaussianMGF`) and have second
moment $1$. If, for some $r$ and $K \ge 0$, the range-finder event
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{S})\|_{\mathsf{F}}^2 \le
K\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2$ fails with probability at most
$\delta_1$, then for every real square $\mathbf{A}$ and every $\tau \ge 0$, with
$\mathbf{E}_r = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_r$, <!-- value hansonWrightConstant -->
$$\mathbb{P}\bigl[\lvert \mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) -
\operatorname{tr}\mathbf{A} \rvert \ge \tau\bigr] \le \delta_1 + 2\exp\Bigl(-\frac{1}{196}\min\Bigl(
\frac{\ell\tau^2}{c^2 K\|\mathbf{E}_r\|_{\mathsf{F}}^2},
\frac{\ell\tau}{c\sqrt{K}\|\mathbf{E}_r\|_{\mathsf{F}}}\Bigr)\Bigr)\,;$$
the constant is `hansonWrightConstant`. On the range-finder event the compressed residual has
Frobenius (hence spectral) norm at most $\sqrt{K}\|\mathbf{E}_r\|_{\mathsf{F}}$; conditionally on
$\mathbf{S}$ the Girard–Hutchinson tail applies
(`NLAlib.measureReal_abs_girardHutchinson_sub_trace_ge_le`), and
`ProbabilityTheory.IndepFun.measureReal_mem_le_add` integrates it over the sketch. A zero
denominator makes its fraction $0$, and the bound is then at least $2$. Instances:
`NLAlib.measureReal_abs_hutchpp_sub_trace_ge_le_of_isSubgaussianVector`,
`NLAlib.measureReal_abs_hutchpp_sub_trace_ge_le_of_hasLaw_gaussianMatrix`.
[MeyerMuscoMuscoWoodruff2021, Theorem 4 and Lemma 2]; there for positive semidefinite
$\mathbf{A}$ with $\|\mathbf{\Delta}\|_{\mathsf{F}} \le 2\|\mathbf{E}_r\|_{\mathsf{F}}$ given,
unspecified constants and a sample-size form.
Result: hutchpp-tail -/
theorem measureReal_abs_hutchpp_sub_trace_ge_le (A : Matrix n n ℝ) {S : Ω → Matrix n s ℝ}
    {G : Ω → Matrix n t ℝ} {c : ℝ≥0} (hS : AEMeasurable S μ) (hSG : IndepFun S G μ)
    (hGind : iIndepFun (fun p : n × t => fun ω => G ω p.1 p.2) μ)
    (hGsub : ∀ i j, HasSubgaussianMGF (fun ω => G ω i j) c μ)
    (hGvar : ∀ i j, ∫ ω, G ω i j ^ 2 ∂μ = 1) {r : ℕ} {K δ₁ : ℝ} (hK : 0 ≤ K)
    (hRF : μ.real {ω | K * frobNorm (A - truncatedSVD A r) ^ 2 <
      frobNorm (A - rsvd A (S ω)) ^ 2} ≤ δ₁) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |hutchpp A (S ω) (G ω) - A.trace|} ≤
      δ₁ + 2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card t * τ ^ 2 / ((c : ℝ) ^ 2 * K * frobNorm (A - truncatedSVD A r) ^ 2))
          (Fintype.card t * τ / ((c : ℝ) * √K * frobNorm (A - truncatedSVD A r))))) := by
  -- SKELETON-NOTE: `hK` and `hτ` are not needed for truth: for `K < 0` (where `√K = 0`) or
  -- `τ < 0` the right side is at least `2`. Kept as in the design note (§3.4); drop if the
  -- review asks for minimal hypotheses.
  sorry

/-- **The deviation of Hutch++ with a sub-Gaussian sketch.** Let the sketch
$\mathbf{S}^{\mathsf{H}}$ of the $n \times \lvert s \rvert$ sketch test matrix $\mathbf{S}$,
$\lvert s \rvert \ge 1$, have independent, isotropic, sub-Gaussian rows with proxy $c$, and let the
$n \times \ell$ residual test matrix $\mathbf{G}$ be independent of $\mathbf{S}$, with independent
entries that each satisfy the sub-Gaussian moment generating function bound with variance proxy
$c'$ and have second moment $1$. If $\delta > 0$
and <!-- value subgaussianEmbeddingDim c r (1/2) (\delta/2) -->
$\lvert s \rvert \ge 4 c^2 (r \log 9 + \log(2/(\delta/2)))/(C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/64$, then for every real square $\mathbf{A}$ and
every $\tau \ge 0$, with $\mathbf{E}_r = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_r$, we
get <!-- value subgaussianRangeFinderFactor c --> <!-- value hansonWrightConstant -->
$$\mathbb{P}\bigl[\lvert \mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) -
\operatorname{tr}\mathbf{A} \rvert \ge \tau\bigr] \le \delta + 2\exp\Bigl(-\frac{1}{196}\min\Bigl(
\frac{\ell\tau^2}{c'^2 (1 + 10c)\|\mathbf{E}_r\|_{\mathsf{F}}^2},
\frac{\ell\tau}{c'\sqrt{1 + 10c}\,\|\mathbf{E}_r\|_{\mathsf{F}}}\Bigr)\Bigr)\,;$$
the size is `subgaussianEmbeddingDim c r (1 / 2) (δ / 2)`, $C$ is `subgaussianJLConstant`, the
factor is `subgaussianRangeFinderFactor c` and the constant in the exponent is
`hansonWrightConstant`. `NLAlib.measureReal_abs_hutchpp_sub_trace_ge_le` with the range finder
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`. Sign sketches and
residual probes are the case $c = c' = 1$.
[MeyerMuscoMuscoWoodruff2021, Theorem 4 and §3, proof of Theorem 1]; there with sign test
matrices, the factor $2$ and unspecified constants.
Result: hutchpp-tail -/
theorem measureReal_abs_hutchpp_sub_trace_ge_le_of_isSubgaussianVector [Nonempty s]
    (A : Matrix n n ℝ) {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ} {c c' : ℝ≥0}
    (hSind : iIndepFun (fun i ω => (S ω)ᴴ i) μ)
    (hSsub : ∀ i, IsSubgaussianVector (fun ω => (S ω)ᴴ i) c μ)
    (hSiso : ∀ i, IsIsotropic (fun ω => (S ω)ᴴ i) μ)
    (hGind : iIndepFun (fun p : n × t => fun ω => G ω p.1 p.2) μ)
    (hGsub : ∀ i j, HasSubgaussianMGF (fun ω => G ω i j) c' μ)
    (hGvar : ∀ i j, ∫ ω, G ω i j ^ 2 ∂μ = 1) (hSG : IndepFun S G μ) {r : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hs : subgaussianEmbeddingDim c r (1 / 2) (δ / 2) ≤ Fintype.card s) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |hutchpp A (S ω) (G ω) - A.trace|} ≤
      δ + 2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card t * τ ^ 2 / ((c' : ℝ) ^ 2 * subgaussianRangeFinderFactor c *
            frobNorm (A - truncatedSVD A r) ^ 2))
          (Fintype.card t * τ / ((c' : ℝ) * √(subgaussianRangeFinderFactor c) *
            frobNorm (A - truncatedSVD A r))))) := by
  sorry

/-- **The deviation of Gaussian Hutch++.** Let the $n \times \lvert s \rvert$ sketch test matrix
$\mathbf{S}$, $\lvert s \rvert \ge 1$, and the $n \times \ell$ residual test matrix $\mathbf{G}$ be
independent and standard Gaussian. If $\delta > 0$
and <!-- value subgaussianEmbeddingDim {\cdot 1} r (1/2) (\delta/2) -->
$\lvert s \rvert \ge 4 \cdot 1^2 (r \log 9 + \log(2/(\delta/2)))/(C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/64$, that is
$\lvert s \rvert \ge 1024(r \log 9 + \log(4/\delta))$, then for every real square $\mathbf{A}$
and every $\tau \ge 0$, with $\mathbf{E}_r = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_r$, we
get <!-- value subgaussianRangeFinderFactor {\cdot 1} --> <!-- value hansonWrightConstant -->
$$\mathbb{P}\bigl[\lvert \mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) -
\operatorname{tr}\mathbf{A} \rvert \ge \tau\bigr] \le \delta + 2\exp\Bigl(-\frac{1}{196}\min\Bigl(
\frac{\ell\tau^2}{(1 + 10\cdot 1)\|\mathbf{E}_r\|_{\mathsf{F}}^2},
\frac{\ell\tau}{\sqrt{1 + 10\cdot 1}\,\|\mathbf{E}_r\|_{\mathsf{F}}}\Bigr)\Bigr)\,;$$
the size is `subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2)`, $C$ is `subgaussianJLConstant`, the
factor is `subgaussianRangeFinderFactor 1` and the constant in the exponent is
`hansonWrightConstant`. The case $c = c' = 1$ of
`NLAlib.measureReal_abs_hutchpp_sub_trace_ge_le_of_isSubgaussianVector`.
[MeyerMuscoMuscoWoodruff2021, Theorem 4 and §5, Algorithm 3]; there with unspecified constants.
Result: hutchpp-tail -/
theorem measureReal_abs_hutchpp_sub_trace_ge_le_of_hasLaw_gaussianMatrix [Nonempty s]
    (A : Matrix n n ℝ) {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ}
    (hS : HasLaw S (gaussianMatrix n s) μ) (hG : HasLaw G (gaussianMatrix n t) μ)
    (hSG : IndepFun S G μ) {r : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hs : subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2) ≤ Fintype.card s) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |hutchpp A (S ω) (G ω) - A.trace|} ≤
      δ + 2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card t * τ ^ 2 / (subgaussianRangeFinderFactor 1 *
            frobNorm (A - truncatedSVD A r) ^ 2))
          (Fintype.card t * τ / (√(subgaussianRangeFinderFactor 1) *
            frobNorm (A - truncatedSVD A r))))) := by
  sorry

/-- **Hutch++ to relative error in the nuclear norm.** Let the sketch $\mathbf{S}^{\mathsf{H}}$
of the $n \times \lvert s \rvert$ sketch test matrix $\mathbf{S}$, $\lvert s \rvert \ge 1$, have
independent, isotropic, sub-Gaussian rows with proxy $c$, and let the $n \times \ell$ residual
test matrix $\mathbf{G}$ be independent of $\mathbf{S}$, with independent entries that each satisfy
the sub-Gaussian moment generating function bound with variance proxy $c'$ and have second moment
$1$. If $r \ge 1$, $\varepsilon > 0$,
$\delta > 0$, <!-- value subgaussianEmbeddingDim c r (1/2) (\delta/4) -->
$\lvert s \rvert \ge 4 c^2 (r \log 9 + \log(2/(\delta/4)))/(C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/64$,
and <!-- value subgaussianRangeFinderFactor c --> <!-- value hansonWrightConstant -->
$$\log\frac{4}{\delta} \le \frac{1}{196}\cdot\frac{4\ell r\varepsilon^2}{c'^2(1 + 10c)}\,,\qquad
\log\frac{4}{\delta} \le \frac{1}{196}\cdot\frac{2\ell\sqrt{r}\,\varepsilon}{c'\sqrt{1 + 10c}}\,,$$
then for every real square $\mathbf{A}$
$$\mathbb{P}\bigl[\lvert \mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) -
\operatorname{tr}\mathbf{A} \rvert > \varepsilon\|\mathbf{A}\|_*\bigr] \le \delta\,;$$
the size is `subgaussianEmbeddingDim c r (1 / 2) (δ / 4)`, $C$ is `subgaussianJLConstant`, the
factor is `subgaussianRangeFinderFactor c` and $1/196$ is `hansonWrightConstant`. From
`NLAlib.measureReal_abs_hutchpp_sub_trace_ge_le_of_isSubgaussianVector` at $\delta/2$ and
$\tau = \varepsilon\|\mathbf{A}\|_*$, with
$\|\mathbf{E}_r\|_{\mathsf{F}} \le \|\mathbf{A}\|_*/(2\sqrt{r})$
(`NLAlib.frobNorm_sub_truncatedSVD_le_nuclearNorm_div`). Asymptotic form:
`NLAlib.exists_forall_measureReal_abs_hutchpp_sub_trace_gt_le_of_isSubgaussianVector`. The
positive semidefinite forms are
`Matrix.PosSemidef.measureReal_hutchpp_lt_one_sub_mul_trace_le_of_isSubgaussianVector` and
`Matrix.PosSemidef.measureReal_one_add_mul_trace_lt_hutchpp_le_of_isSubgaussianVector`.
[MeyerMuscoMuscoWoodruff2021, Theorem 5]; there with sign test matrices and
$m = O(\sqrt{\log(1/\delta)}/\varepsilon + \log(1/\delta))$, constants unspecified.
Result: hutchpp-relative-error -/
theorem measureReal_abs_hutchpp_sub_trace_gt_le_of_isSubgaussianVector [Nonempty s]
    (A : Matrix n n ℝ) {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ} {c c' : ℝ≥0}
    (hSind : iIndepFun (fun i ω => (S ω)ᴴ i) μ)
    (hSsub : ∀ i, IsSubgaussianVector (fun ω => (S ω)ᴴ i) c μ)
    (hSiso : ∀ i, IsIsotropic (fun ω => (S ω)ᴴ i) μ)
    (hGind : iIndepFun (fun p : n × t => fun ω => G ω p.1 p.2) μ)
    (hGsub : ∀ i j, HasSubgaussianMGF (fun ω => G ω i j) c' μ)
    (hGvar : ∀ i j, ∫ ω, G ω i j ^ 2 ∂μ = 1) (hSG : IndepFun S G μ) {r : ℕ} (hr : 0 < r)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hs : subgaussianEmbeddingDim c r (1 / 2) (δ / 4) ≤ Fintype.card s)
    (ht₁ : Real.log (4 / δ) ≤ hansonWrightConstant *
      (4 * Fintype.card t * r * ε ^ 2 / ((c' : ℝ) ^ 2 * subgaussianRangeFinderFactor c)))
    (ht₂ : Real.log (4 / δ) ≤ hansonWrightConstant *
      (2 * Fintype.card t * √(r : ℝ) * ε / ((c' : ℝ) * √(subgaussianRangeFinderFactor c)))) :
    μ.real {ω | ε * nuclearNorm A < |hutchpp A (S ω) (G ω) - A.trace|} ≤ δ := by
  sorry

/-- **Hutch++ does not underestimate a positive semidefinite trace by a factor $1 - \varepsilon$.**
With the hypotheses of `NLAlib.measureReal_abs_hutchpp_sub_trace_gt_le_of_isSubgaussianVector`:
the sketch $\mathbf{S}^{\mathsf{H}}$, $\lvert s \rvert \ge 1$, has independent, isotropic,
sub-Gaussian rows with proxy $c$; the $n \times \ell$ residual test matrix $\mathbf{G}$ is
independent of $\mathbf{S}$ with independent entries, sub-Gaussian with variance proxy $c'$ and of
second moment $1$; $r \ge 1$, $\varepsilon > 0$,
$\delta > 0$, <!-- value subgaussianEmbeddingDim c r (1/2) (\delta/4) -->
$\lvert s \rvert \ge 4 c^2 (r \log 9 + \log(2/(\delta/4)))/(C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/64$,
and <!-- value subgaussianRangeFinderFactor c --> <!-- value hansonWrightConstant -->
$$\log\frac{4}{\delta} \le \frac{1}{196}\cdot\frac{4\ell r\varepsilon^2}{c'^2(1 + 10c)}\,,\qquad
\log\frac{4}{\delta} \le \frac{1}{196}\cdot\frac{2\ell\sqrt{r}\,\varepsilon}{c'\sqrt{1 + 10c}}\,.$$
Then for every real positive semidefinite $\mathbf{A}$
$$\mathbb{P}\bigl[\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) <
(1 - \varepsilon)\operatorname{tr}\mathbf{A}\bigr] \le \delta\,,$$
since $\|\mathbf{A}\|_* = \operatorname{tr}\mathbf{A}$; the size is
`subgaussianEmbeddingDim c r (1 / 2) (δ / 4)`, $C$ is `subgaussianJLConstant`, the factor is
`subgaussianRangeFinderFactor c` and $1/196$ is `hansonWrightConstant`. The upper half is
`Matrix.PosSemidef.measureReal_one_add_mul_trace_lt_hutchpp_le_of_isSubgaussianVector`.
[MeyerMuscoMuscoWoodruff2021, Theorem 1]; there both halves together, with sign test matrices and
unspecified constants.
Result: hutchpp-relative-error -/
theorem _root_.Matrix.PosSemidef.measureReal_hutchpp_lt_one_sub_mul_trace_le_of_isSubgaussianVector
    [Nonempty s] {A : Matrix n n ℝ} (hA : A.PosSemidef) {S : Ω → Matrix n s ℝ}
    {G : Ω → Matrix n t ℝ} {c c' : ℝ≥0} (hSind : iIndepFun (fun i ω => (S ω)ᴴ i) μ)
    (hSsub : ∀ i, IsSubgaussianVector (fun ω => (S ω)ᴴ i) c μ)
    (hSiso : ∀ i, IsIsotropic (fun ω => (S ω)ᴴ i) μ)
    (hGind : iIndepFun (fun p : n × t => fun ω => G ω p.1 p.2) μ)
    (hGsub : ∀ i j, HasSubgaussianMGF (fun ω => G ω i j) c' μ)
    (hGvar : ∀ i j, ∫ ω, G ω i j ^ 2 ∂μ = 1) (hSG : IndepFun S G μ) {r : ℕ} (hr : 0 < r)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hs : subgaussianEmbeddingDim c r (1 / 2) (δ / 4) ≤ Fintype.card s)
    (ht₁ : Real.log (4 / δ) ≤ hansonWrightConstant *
      (4 * Fintype.card t * r * ε ^ 2 / ((c' : ℝ) ^ 2 * subgaussianRangeFinderFactor c)))
    (ht₂ : Real.log (4 / δ) ≤ hansonWrightConstant *
      (2 * Fintype.card t * √(r : ℝ) * ε / ((c' : ℝ) * √(subgaussianRangeFinderFactor c)))) :
    μ.real {ω | hutchpp A (S ω) (G ω) < (1 - ε) * A.trace} ≤ δ := by
  sorry

/-- **Hutch++ does not overestimate a positive semidefinite trace by a factor $1 + \varepsilon$.**
With the hypotheses of `NLAlib.measureReal_abs_hutchpp_sub_trace_gt_le_of_isSubgaussianVector`:
the sketch $\mathbf{S}^{\mathsf{H}}$, $\lvert s \rvert \ge 1$, has independent, isotropic,
sub-Gaussian rows with proxy $c$; the $n \times \ell$ residual test matrix $\mathbf{G}$ is
independent of $\mathbf{S}$ with independent entries, sub-Gaussian with variance proxy $c'$ and of
second moment $1$; $r \ge 1$, $\varepsilon > 0$,
$\delta > 0$, <!-- value subgaussianEmbeddingDim c r (1/2) (\delta/4) -->
$\lvert s \rvert \ge 4 c^2 (r \log 9 + \log(2/(\delta/4)))/(C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/64$,
and <!-- value subgaussianRangeFinderFactor c --> <!-- value hansonWrightConstant -->
$$\log\frac{4}{\delta} \le \frac{1}{196}\cdot\frac{4\ell r\varepsilon^2}{c'^2(1 + 10c)}\,,\qquad
\log\frac{4}{\delta} \le \frac{1}{196}\cdot\frac{2\ell\sqrt{r}\,\varepsilon}{c'\sqrt{1 + 10c}}\,.$$
Then for every real positive semidefinite $\mathbf{A}$
$$\mathbb{P}\bigl[\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) >
(1 + \varepsilon)\operatorname{tr}\mathbf{A}\bigr] \le \delta\,;$$
the size is `subgaussianEmbeddingDim c r (1 / 2) (δ / 4)`, $C$ is `subgaussianJLConstant`, the
factor is `subgaussianRangeFinderFactor c` and $1/196$ is `hansonWrightConstant`. The lower half
is `Matrix.PosSemidef.measureReal_hutchpp_lt_one_sub_mul_trace_le_of_isSubgaussianVector`.
[MeyerMuscoMuscoWoodruff2021, Theorem 1]; there both halves together, with sign test matrices and
unspecified constants.
Result: hutchpp-relative-error -/
theorem _root_.Matrix.PosSemidef.measureReal_one_add_mul_trace_lt_hutchpp_le_of_isSubgaussianVector
    [Nonempty s] {A : Matrix n n ℝ} (hA : A.PosSemidef) {S : Ω → Matrix n s ℝ}
    {G : Ω → Matrix n t ℝ} {c c' : ℝ≥0} (hSind : iIndepFun (fun i ω => (S ω)ᴴ i) μ)
    (hSsub : ∀ i, IsSubgaussianVector (fun ω => (S ω)ᴴ i) c μ)
    (hSiso : ∀ i, IsIsotropic (fun ω => (S ω)ᴴ i) μ)
    (hGind : iIndepFun (fun p : n × t => fun ω => G ω p.1 p.2) μ)
    (hGsub : ∀ i j, HasSubgaussianMGF (fun ω => G ω i j) c' μ)
    (hGvar : ∀ i j, ∫ ω, G ω i j ^ 2 ∂μ = 1) (hSG : IndepFun S G μ) {r : ℕ} (hr : 0 < r)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hs : subgaussianEmbeddingDim c r (1 / 2) (δ / 4) ≤ Fintype.card s)
    (ht₁ : Real.log (4 / δ) ≤ hansonWrightConstant *
      (4 * Fintype.card t * r * ε ^ 2 / ((c' : ℝ) ^ 2 * subgaussianRangeFinderFactor c)))
    (ht₂ : Real.log (4 / δ) ≤ hansonWrightConstant *
      (2 * Fintype.card t * √(r : ℝ) * ε / ((c' : ℝ) * √(subgaussianRangeFinderFactor c)))) :
    μ.real {ω | (1 + ε) * A.trace < hutchpp A (S ω) (G ω)} ≤ δ := by
  sorry

/-- **$O(c^4(\sqrt{\log(1/\delta)}/\varepsilon + \log(1/\delta)))$ products suffice for Hutch++
to relative error $\varepsilon$ in the nuclear norm**: there are absolute constants
$C, \varepsilon_0 > 0$ such that if the sketch $\mathbf{S}^{\mathsf{H}}$ of the
$n \times \lvert s \rvert$ sketch test matrix $\mathbf{S}$, $\lvert s \rvert \ge 1$, has
independent, isotropic, sub-Gaussian rows with proxy $c$, the $n \times \lvert t \rvert$ residual
test matrix $\mathbf{G}$ is independent of $\mathbf{S}$ with independent entries that each satisfy
the sub-Gaussian moment generating function bound with variance proxy $c$ and have second moment
$1$, $0 < \varepsilon \le \varepsilon_0$, $0 < \delta \le 1/2$ and both
$\lvert s \rvert$ and $\lvert t \rvert$ are at least
$Cc^4(\sqrt{\log(1/\delta)}/\varepsilon + \log(1/\delta))$, then for every real square
$\mathbf{A}$
$$\mathbb{P}\bigl[\lvert \mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) -
\operatorname{tr}\mathbf{A} \rvert > \varepsilon\|\mathbf{A}\|_*\bigr] \le \delta\,,$$
with $m = 2\lvert s \rvert + \lvert t \rvert$ products in all. The asymptotic form of
`NLAlib.measureReal_abs_hutchpp_sub_trace_gt_le_of_isSubgaussianVector`, at
$r \asymp \lvert s \rvert/c^2$; the proxy stays in the threshold, and isotropy forces $c \ge 1$.
[MeyerMuscoMuscoWoodruff2021, Theorem 5 and Theorem 1]; there with sign test matrices ($c = 1$).
Asymptotic: NLAlib.measureReal_abs_hutchpp_sub_trace_gt_le_of_isSubgaussianVector
Result: hutchpp-relative-error -/
theorem exists_forall_measureReal_abs_hutchpp_sub_trace_gt_le_of_isSubgaussianVector :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω n s t : Type} [MeasurableSpace Ω] [Fintype n]
      [Fintype s] [Fintype t] [DecidableEq n] [Nonempty s] (μ : Measure Ω) (A : Matrix n n ℝ)
      (S : Ω → Matrix n s ℝ) (G : Ω → Matrix n t ℝ) (c : ℝ≥0) (ε δ : ℝ),
      iIndepFun (fun i ω => (S ω)ᴴ i) μ → (∀ i, IsSubgaussianVector (fun ω => (S ω)ᴴ i) c μ) →
      (∀ i, IsIsotropic (fun ω => (S ω)ᴴ i) μ) →
      iIndepFun (fun p : n × t => fun ω => G ω p.1 p.2) μ →
      (∀ i j, HasSubgaussianMGF (fun ω => G ω i j) c μ) → (∀ i j, ∫ ω, G ω i j ^ 2 ∂μ = 1) →
      IndepFun S G μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((c : ℝ) ^ 4 * (√(Real.log (1 / δ)) / ε + Real.log (1 / δ))) ≤ Fintype.card s →
      C * ((c : ℝ) ^ 4 * (√(Real.log (1 / δ)) / ε + Real.log (1 / δ))) ≤ Fintype.card t →
      μ.real {ω | ε * nuclearNorm A < |hutchpp A (S ω) (G ω) - A.trace|} ≤ δ := by
  -- SKELETON-NOTE: true by the inversion in the design note §3.4 (with `c ≥ 1` from isotropy
  -- when `n` is nonempty; `n` empty makes the event empty): `r = ⌊|s| / (B c²)⌋` for a large
  -- absolute `B`, `log(4/δ) ≤ 3 log(1/δ)` and `log(8/δ) ≤ 4 log(1/δ)` at `δ ≤ 1/2`. The cap
  -- `ε ≤ ε₀` is not needed by that argument (any `ε₀`, e.g. `1`); `[Nonempty s]` is needed
  -- (with `s`, `t` empty, `n` nonempty and `c = 0` the hypotheses hold and the event is sure).
  -- `C` is not fixed yet; the docstring should name it once the proof does.
  sorry

end NLAlib
