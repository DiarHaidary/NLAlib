/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.MeanInequalities

/-!
# The Paley–Zygmund inequality for finite weighted sums (scaffold)

Statement for a new `NLAlib/ForMathlib/Analysis/MeanInequalities.lean` (stage SHIFTED-QR, wave
W0, design note `docs/design/Eigensolvers-ShiftedQR.md` §3.3, id W1). Upstream candidate for
`Mathlib/Analysis/MeanInequalities.lean`, next to the weighted power-mean inequalities. The
measure form is `ProbabilityTheory.sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt` in
`NLAlib/ForMathlib/Probability/Moments/PaleyZygmund.lean`; the finite form keeps the matrix
files free of measure theory.

## Main results

* `Finset.sq_mul_sq_sum_le_sum_mul_sq_mul_sum_filter`.
-/

@[expose] public section

namespace Finset

/-- **The Paley–Zygmund inequality for finite weighted sums.** For a finite family of weights
$w_i \ge 0$ with $\sum_i w_i = 1$, values $x_i \ge 0$ and $0 \le t \le 1$,
$$(1 - t)^2\Bigl(\sum_i w_ix_i\Bigr)^2 \le \Bigl(\sum_i w_ix_i^2\Bigr)
\sum_{i \,:\, x_i > t\sum_j w_jx_j} w_i\,.$$
[PaleyZygmund1932, Lemma 19], in its discrete form.
Proof: split $\sum_i w_ix_i$ over $x_i \le t\,\mathbb{E}x$ (at most $t\,\mathbb{E}x$) and its
complement, which Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq` with the factors
$\sqrt{w_i}x_i$, $\sqrt{w_i}$) bounds by
$(\sum w_ix_i^2)^{1/2}(\sum_{\text{event}} w_i)^{1/2}$; square, using $(1 - t)\,\mathbb{E}x \ge 0$.
Alternatively apply the measure form to the discrete probability measure
$\sum_i w_i\delta_i$. M, about 35 lines. -/
theorem sq_mul_sq_sum_le_sum_mul_sq_mul_sum_filter {ι : Type*} (s : Finset ι) {w x : ι → ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (hx : ∀ i ∈ s, 0 ≤ x i) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) ^ 2 * (∑ i ∈ s, w i * x i) ^ 2 ≤
      (∑ i ∈ s, w i * x i ^ 2) *
        ∑ i ∈ s.filter (fun i => t * ∑ j ∈ s, w j * x j < x i), w i := by
  sorry

end Finset
