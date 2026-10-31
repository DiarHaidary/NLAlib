/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Oblivious.RangeFinder
public import NLAlib.Sketching.Sampling.RowSampling

/-!
# The randomized SVD with column sampling at the rank-$k$ leverage scores

The row-sampling instance of `NLAlib.LowRank.Oblivious.RangeFinder`, for the family of
`NLAlib.Sketching.Sampling.RowSampling`: the test matrix $\mathbf{\Omega}$ samples $\ell$
columns of $\mathbf{A}$ independently with probabilities $p_i > 0$, and its sketch
$\mathbf{\Omega}^{\mathsf{H}}$ has law `NLAlib.samplingSketch l p`. Sampling is not oblivious: the
statement takes the domination of the leverage scores of the one subspace the analysis needs,
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$
(`leverageScore (truncatedSVD A k)ᴴ i ≤ L * p i`), by the fixed-subspace injection route
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le` at constant $1/2$. Exact
leverage sampling at the head is $L = k$. Any `RCLike` field.

The factor is constant ($1 + 2t$ at failure probability $\delta + 1/t$) and there is no accuracy
parameter, so no asymptotic form; in $O(\cdot)$ form the size is the family's injection size,
`NLAlib.exists_forall_hasSubspaceInjection_of_hasLaw_samplingSketch`. Early truncation with
sampling is deferred (the probabilities would depend on the
tail). Nyström takes an OSI, which leverage sampling at one subspace is not, so it has no sampling
form here.

## Main results

* `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_samplingSketch`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq n] {X : Ω → Matrix n l 𝕜}

/-- **Column sampling at the rank-$k$ leverage scores**: if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ samples $\ell$ columns of $\mathbf{A}$ independently with
positive probabilities $p_i$ summing to $1$, the leverage scores of
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ satisfy $\tau_i \le Lp_i$,
$\ell$ nonempty, $\delta, t > 0$ and $\ell$ is at
least <!-- value samplingInjectionDim k L (1/2) \delta -->
$2 L \log(k/\delta)/(1/2)^2$ (`samplingInjectionDim k L (1 / 2) δ`), then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + 2t)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$. The size is at the target rank $k$, an upper bound on the
rank of the head. In $O(\cdot)$ form it is the family's injection size,
$O(L\log(k/\delta))$ (`NLAlib.exists_forall_hasSubspaceInjection_of_hasLaw_samplingSketch`); a
constant-factor result has no asymptotic form of its own. The without-replacement form is
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_samplingSketchWithoutReplacement`.
[CamanoEpperlyMeyerTropp2025, Theorem 2.2] with a fixed-subspace injection; the instance is not
stated there.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_samplingSketch [Nonempty l]
    (A : Matrix m n 𝕜) {p : n → ℝ≥0} (hX : HasLaw (fun ω => (X ω)ᴴ) (samplingSketch l p) μ)
    (hp : ∑ i, p i = 1) (hpos : ∀ i, 0 < p i) {k : ℕ} {L δ t : ℝ}
    (hdom : ∀ i, leverageScore (truncatedSVD A k)ᴴ i ≤ L * p i) (hδ : 0 < δ) (ht : 0 < t)
    (hl : samplingInjectionDim k L (1 / 2) δ ≤ Fintype.card l) :
    μ.real {ω | (1 + 2 * t) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t := by
  have : IsProbabilityMeasure μ :=
    hX.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketch hp)
  have hr : (truncatedSVD A k)ᴴ.rank ≤ k := by
    rw [Matrix.rank_conjTranspose]
    exact rank_truncatedSVD_le A k
  have hk : samplingInjectionDim (truncatedSVD A k)ᴴ.rank L (1 / 2) δ ≤ Fintype.card l := by
    rcases Nat.eq_zero_or_pos (truncatedSVD A k)ᴴ.rank with h0 | h0
    · rw [h0, samplingInjectionDim_def, Nat.cast_zero, zero_div, Real.log_zero, mul_zero,
        zero_div]
      exact Nat.cast_nonneg _
    · refine le_trans ?_ hl
      have hL : (0 : ℝ) ≤ L := (Nat.cast_nonneg _).trans (rank_le_of_leverageScore_le hp hdom)
      rw [samplingInjectionDim_def, samplingInjectionDim_def]
      have hrk : ((truncatedSVD A k)ᴴ.rank : ℝ) ≤ k := by exact_mod_cast hr
      have hlog : Real.log ((truncatedSVD A k)ᴴ.rank / δ) ≤ Real.log (k / δ) :=
        Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hrk hδ.le)
      gcongr
  have h := (hasSubspaceInjection_of_hasLaw_samplingSketch_of_samplingInjectionDim_le hX hp hdom
    (by norm_num) hδ hk).measureReal_frobNorm_sub_rsvd_sq_gt_le
    (isIsotropicSketch_of_hasLaw_samplingSketch hX hp hpos) (by norm_num) ht
  rwa [show (1 : ℝ) + t / (1 - 1 / 2) = 1 + 2 * t by ring] at h

end NLAlib
