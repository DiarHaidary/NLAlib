/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Oblivious.EarlyTruncation
public import NLAlib.Sketching.Gaussian.HaarEmbedding

/-!
# Early truncation with a Haar test matrix, through injection and approximate multiplication

The Haar instance of `NLAlib.LowRank.Oblivious.EarlyTruncation`, for the family of
`NLAlib.Sketching.Gaussian.Haar`: for an $n \times \ell$ Haar frame $\mathbf{\Omega}$,
$\ell \le \lvert n\rvert$, the early-truncated randomized SVD
$\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$ reaches error
$(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ with
probability $1 - \delta$ at $\ell = O(k\log(1/\delta)/\varepsilon^2)$. The family's predicates are
about the normalised sketch $\sqrt{\lvert n\rvert/\ell}\,\mathbf{\Omega}^{\mathsf{H}}$: its OSI at
constant $1 - \varepsilon/6$ by JL and a net
(`NLAlib.isObliviousSubspaceInjection_of_hasLaw_haarFrame_of_jlDim_le`) and its JL moment at
$p = \max(2, \log(3/\delta))$ (`NLAlib.hasJLMoment_of_hasLaw_haarFrame_of_jlMomentDim_le`) for
the two multiplication tails; the conclusion is about the output the user computes from the raw
frame. Real throughout.

The Haar randomized SVD to relative error by this route is dominated by Tropp and Webber's bound
through the range transfer (`NLAlib.LowRank.Gaussian.RangeFinderTailHaar`) and is not stated.
Design: `docs/design/LowRank-S7.md` §3.5, D3; `docs/design/Sketching-Moments.md` §4.3.

## Main results

* `NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame`: the explicit
  tail, and its asymptotic form
  `exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] [DecidableEq l] {Q : Ω → Matrix n l ℝ}

/-- **Early-truncated randomized SVD with a Haar test matrix, tail**: for an $n \times \ell$ Haar
frame $\mathbf{\Omega}$, $\ell \le \lvert n\rvert$, $0 < \varepsilon \le 1$, $\delta > 0$, at
least <!-- value jlDim (2\varepsilon/15) (\delta/3/21^k) -->
$\ell \ge \log(2/(\delta/3/21^k))/((2\varepsilon/15)^2/4 - (2\varepsilon/15)^3/6)$ and at
least <!-- value jlMomentDim (\varepsilon/(6\sqrt{k})) (\delta/3) -->
$\ell \ge 128\max(2, \log(1/(\delta/3)))/(\varepsilon/(6\sqrt{k}))^2$,
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the sizes are `jlDim (2 * ε / 15) (δ / 3 / 21 ^ k)` (the OSI at
constant $1 - \varepsilon/6$ and failure $\delta/3$) and `jlMomentDim (ε / (6 * √k)) (δ / 3)`
(the JL moment for each multiplication tail, failure $\delta/3$). The route of
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`, through
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_mul_sq_gt_one_add_mul_le`. Asymptotic form:
`exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame`.
[CohenElderMuscoMuscoPersu2015, Theorem 12 and Lemma 3]; there for dense random sign matrices,
with unspecified constants; the Haar instance is not stated there.
Result: etrsvd -/
theorem measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame
    (A : Matrix m n ℝ) (hQ : HasLaw Q (haarFrame n l) μ) (hl : Fintype.card l ≤ Fintype.card n)
    {k : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hl₁ : jlDim (2 * ε / 15) (δ / 3 / 21 ^ k) ≤ Fintype.card l)
    (hl₂ : jlMomentDim (ε / (6 * √(k : ℝ))) (δ / 3) ≤ Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedRSVD A (Q ω) k) ^ 2} ≤ δ := by
  sorry

/-- **$O(k\log(1/\delta)/\varepsilon^2)$ Haar columns suffice for early truncation**: there are
absolute constants $C, \varepsilon_0 > 0$ such that for an $n \times \ell$ Haar frame
$\mathbf{\Omega}$, $\ell \le \lvert n\rvert$, $0 < \varepsilon \le \varepsilon_0$,
$0 < \delta \le 1/2$ and $\ell \ge Ck\log(1/\delta)/\varepsilon^2$,
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$ ($k = 0$ is trivial). The asymptotic form of
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame`, proved from it
with $\varepsilon_0 = 1$; the injection size $O((k + \log(1/\delta))/\varepsilon^2)$ is dominated
by the multiplication size for $k \ge 1$. [CohenElderMuscoMuscoPersu2015, Theorem 12 and
Lemma 3].
Asymptotic: NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame
Result: etrsvd -/
theorem exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [DecidableEq l] (μ : Measure Ω) (A : Matrix m n ℝ) (Q : Ω → Matrix n l ℝ)
      (k : ℕ) (ε δ : ℝ),
      HasLaw Q (haarFrame n l) μ → Fintype.card l ≤ Fintype.card n →
      0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((k : ℝ) * Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (Q ω) k) ^ 2} ≤ δ := by
  sorry

end NLAlib
