/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Probability.Distributions.ChiSquareTails
public import NLAlib.Probability.SubGaussianVector.Norm
public import NLAlib.Probability.Tail

/-!
# Weighted squares and images of a sub-Gaussian random vector

For a real sub-Gaussian vector $\mathbf{x}$ with proxy $c$, the upper tail of a weighted sum of
squares $\sum_i w_i \mathbf{x}_i^2$ and of the squared norm $\|\mathbf{A}\mathbf{x}\|^2$ of its
image under a fixed matrix $\mathbf{A}$: Hsu, Kakade and Zhang's tail, with Laurent and Massart's
constants,
$$\mathbb{P}\Bigl(\|\mathbf{A}\mathbf{x}\|^2 \ge c\,\bigl(\|\mathbf{A}\|_{\mathsf{F}}^2 +
  2 \|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\mathsf{F}} \sqrt{t} +
  2 \|\mathbf{A}\|_2^2\, t\bigr)\Bigr) \le e^{-t}\,.$$
The matrix may be over any `RCLike` field while $\mathbf{x}$ stays real; the bound has no field
factor (see the docstring of
`NLAlib.IsSubgaussianVector.measure_norm_mulVec_sq_ge_le`). The case $\mathbf{A} = \mathbf{I}$ is
`NLAlib.IsSubgaussianVector.measure_norm_sq_ge_le`.

Proofs. The diagonal form linearises $e^{\theta \sum_i w_i \mathbf{x}_i^2}$ with a standard
Gaussian vector at $\sqrt{\mathbf{w}} \odot \mathbf{g}$, applies the proxy, evaluates the weighted
$\chi^2$ transform (`NLAlib.integral_exp_sum_mul_sq_of_hasLaw_gaussianVector`), and bounds the
log-moment generating function by Laurent and Massart's
$-\tfrac12 \sum_i \log(1 - u_i) \le \tfrac12 \sum_i u_i + \sum_i u_i^2 / (4 (1 - \max_i u_i))$;
`NLAlib.measureReal_ge_le_exp_neg_of_mgf_le` inverts the resulting sub-gamma bound. The matrix form
stacks the real and imaginary parts of $\mathbf{A}$ into a real matrix and diagonalises its Gram
matrix (the spectral theorem over $\mathbb{R}$).

This file is part of the skeleton of Sketching stage S6 (`docs/design/Sketching-S6.md` §8,
item 2 (b)); its proofs are deferred. At the round's wrap-up it merges into
`NLAlib/Probability/SubGaussianVector/Norm.lean`, where
`NLAlib.IsSubgaussianVector.measure_norm_sq_ge_le` is reproved from the matrix form at
$\mathbf{A} = \mathbf{I}$ and keeps its name (CONTRIBUTING §5.2, rule 6), its private auxiliary
lemma goes, the result id `hsu-kakade-zhang` moves to the matrix form, and the module docstring's
sentence on complex versions in dimension $2n$ is replaced by the field remark of the matrix form.

## Main results

* `NLAlib.IsSubgaussianVector.measure_sum_mul_sq_ge_le`: weighted squares (the diagonal form).
* `NLAlib.IsSubgaussianVector.measure_norm_mulVec_sq_ge_le`: the Hsu–Kakade–Zhang tail.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {x : Ω → n → ℝ} {c : ℝ≥0}

namespace IsSubgaussianVector

/-- **Weighted squares of a sub-Gaussian vector**, the diagonal Hsu–Kakade–Zhang tail: for a real
sub-Gaussian vector $\mathbf{x}$ with proxy $c \ne 0$, weights $0 \le w_i \le b$ not all zero, and
$t \ge 0$,
$$\mu\Bigl(\sum_i w_i \mathbf{x}_i^2 \ge c\,\Bigl(\sum_i w_i +
  2 \sqrt{\textstyle\sum_i w_i^2}\, \sqrt{t} + 2 b t\Bigr)\Bigr) \le e^{-t}\,.$$
Hsu, Kakade and Zhang 2012, Theorem 2.1 for a diagonal matrix; for a standard Gaussian vector,
Laurent and Massart's weighted bound. The form Gaussian Hutchinson trace-estimator tails use.
$\mathbf{w} \ne \mathbf{0}$ and $c \ne 0$ are needed for the non-strict event: otherwise the
threshold is $0$ at $t = 0$ and $2 b t$ in general, and the event can be everything.
Proof: Gaussian linearisation at $\sqrt{\mathbf{w}} \odot \mathbf{g}$, the weighted $\chi^2$
transform, Laurent and Massart's log-moment bound, then
`NLAlib.measureReal_ge_le_exp_neg_of_mgf_le` at $v = 2 c^2 \sum_i w_i^2$ and $b' = 2 c b$; about
150 lines, moderate. -/
theorem measure_sum_mul_sq_ge_le (h : IsSubgaussianVector x c μ) (hc : c ≠ 0) {w : n → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw0 : w ≠ 0) {b : ℝ} (hwb : ∀ i, w i ≤ b) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | c * (∑ i, w i + 2 * √(∑ i, w i ^ 2) * √t + 2 * b * t) ≤
      ∑ i, w i * x ω i ^ 2} ≤ Real.exp (-t) := by
  sorry

/-- **The Hsu–Kakade–Zhang tail**: for a real sub-Gaussian vector $\mathbf{x}$ with proxy
$c \ne 0$, a nonzero matrix $\mathbf{A}$ over $\Bbbk$ acting on $\mathbf{x}$, and $t \ge 0$,
$$\mu\Bigl(\|\mathbf{A}\mathbf{x}\|^2 \ge c\,\bigl(\|\mathbf{A}\|_{\mathsf{F}}^2 +
  2 \|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\mathsf{F}} \sqrt{t} +
  2 \|\mathbf{A}\|_2^2\, t\bigr)\Bigr) \le e^{-t}\,.$$
Hsu, Kakade and Zhang 2012, Theorem 2.1 (there $\Bbbk = \mathbb{R}$; the real case is this one
through `RCLike.ofReal_real_eq_id`). There is no field factor because $\mathbf{x}$ is real: the
stacked real matrix $\mathbf{A}_r = \begin{bmatrix} \operatorname{Re}\mathbf{A} \\
\operatorname{Im}\mathbf{A} \end{bmatrix}$ has the same Frobenius norm, spectral norm at most
$\|\mathbf{A}\|_2$, $\|\mathbf{A}_r^{\mathsf{T}}\mathbf{A}_r\|_{\mathsf{F}} \le
\|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\mathsf{F}}$ (it is
$\operatorname{Re}(\mathbf{A}^{\mathsf{H}} \mathbf{A})$), and the same image norm on real
vectors. A complex $\mathbf{x}$ would double
$\|\mathbf{A}\|_{\mathsf{F}}^2$ (the realified operator is
$\begin{bmatrix} \operatorname{Re}\mathbf{A} & -\operatorname{Im}\mathbf{A} \\
\operatorname{Im}\mathbf{A} & \operatorname{Re}\mathbf{A} \end{bmatrix}$).
$\mathbf{A} \ne \mathbf{0}$ and $c \ne 0$ are needed for the non-strict event, as in
`NLAlib.IsSubgaussianVector.measure_sum_mul_sq_ge_le`.
Proof: the diagonal form at the eigenvalues of $\mathbf{A}_r^{\mathsf{T}}\mathbf{A}_r$
(the spectral theorem over $\mathbb{R}$; $\mathbf{V}^{\mathsf{T}}\mathbf{x}$ has proxy $c$ by
`NLAlib.IsSubgaussianVector.mulVec`), whose sum is $\|\mathbf{A}_r\|_{\mathsf{F}}^2$, whose squares
sum to $\|\mathbf{A}_r^{\mathsf{T}}\mathbf{A}_r\|_{\mathsf{F}}^2$, and which are at most
$\|\mathbf{A}\|_2^2$; then the three facts on the stacking. About 150 lines, moderate. -/
theorem measure_norm_mulVec_sq_ge_le {m : Type*} [Fintype m] {𝕜 : Type*} [RCLike 𝕜]
    (h : IsSubgaussianVector x c μ) (hc : c ≠ 0) {A : Matrix m n 𝕜} (hA : A ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | c * (frobNorm A ^ 2 + 2 * frobNorm (Aᴴ * A) * √t + 2 * specNorm A ^ 2 * t) ≤
      ‖WithLp.toLp 2 (A *ᵥ fun i => (x ω i : 𝕜))‖ ^ 2} ≤ Real.exp (-t) := by
  sorry

end IsSubgaussianVector

end NLAlib
