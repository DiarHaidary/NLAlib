/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Oblivious.RangeFinder
public import NLAlib.Sketching.Sampling.WithoutReplacement

/-!
# The randomized SVD with uniform column sampling without replacement

The sampling-without-replacement instance of `NLAlib.LowRank.Oblivious.RangeFinder`, for the
family of `NLAlib.Sketching.Sampling.WithoutReplacement`: the test matrix $\mathbf{\Omega}$
samples $\ell \le n$ distinct columns of $\mathbf{A}$ uniformly, and its sketch
$\mathbf{\Omega}^{\mathsf{H}}$ has law `NLAlib.samplingSketchWithoutReplacement l n`. The
statement takes the coherence form of the leverage domination at the one subspace the analysis
needs, $\tau_i(\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}) \le L/n$, and runs the fixed-subspace
injection route `NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le` at constant
$1/2$. Any `RCLike` field.

The factor is constant and there is no accuracy parameter, so no asymptotic form; in $O(\cdot)$
form the size is the family's injection size,
`NLAlib.exists_forall_hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement`. Design:
`docs/design/LowRank-S7.md` §3.5, §8 item 10.

## Main results

* `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_samplingSketchWithoutReplacement`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq n] {X : Ω → Matrix n l 𝕜}

/-- **Uniform column sampling without replacement at the rank-$k$ coherence**: if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ samples $\ell \le n$ distinct columns of $\mathbf{A}$ uniformly,
the leverage scores of $\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ satisfy
$\tau_i \le L/n$, $\ell$ nonempty, $\delta, t > 0$ and $\ell$ is at
least <!-- value samplingInjectionDim k L (1/2) \delta -->
$2 L \log(k/\delta)/(1/2)^2$ (`samplingInjectionDim k L (1 / 2) δ`), then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + 2t)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$. In $O(\cdot)$ form the size is the family's injection
size, $O(L\log(k/\delta))$
(`NLAlib.exists_forall_hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement`); a
constant-factor result has no asymptotic form of its own. The with-replacement form, at any
positive probabilities, is `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_samplingSketch`.
[CamanoEpperlyMeyerTropp2025, Theorem 2.2] with a fixed-subspace injection; the instance is not
stated there.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_samplingSketchWithoutReplacement
    [Nonempty l] (A : Matrix m n 𝕜)
    (hX : HasLaw (fun ω => (X ω)ᴴ) (samplingSketchWithoutReplacement l n) μ)
    (hln : Fintype.card l ≤ Fintype.card n) {k : ℕ} {L δ t : ℝ}
    (hdom : ∀ i, leverageScore (truncatedSVD A k)ᴴ i ≤ L * (Fintype.card n : ℝ)⁻¹) (hδ : 0 < δ)
    (ht : 0 < t) (hl : samplingInjectionDim k L (1 / 2) δ ≤ Fintype.card l) :
    μ.real {ω | (1 + 2 * t) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t := by
  have : IsProbabilityMeasure μ :=
    hX.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketchWithoutReplacement hln)
  have hr : (truncatedSVD A k)ᴴ.rank ≤ k := by
    rw [Matrix.rank_conjTranspose]
    exact rank_truncatedSVD_le A k
  have hk : samplingInjectionDim (truncatedSVD A k)ᴴ.rank L (1 / 2) δ ≤ Fintype.card l := by
    rcases Nat.eq_zero_or_pos (truncatedSVD A k)ᴴ.rank with h0 | h0
    · rw [h0, samplingInjectionDim_def, Nat.cast_zero, zero_div, Real.log_zero, mul_zero,
        zero_div]
      exact Nat.cast_nonneg _
    · refine le_trans ?_ hl
      have hL : (0 : ℝ) ≤ L := (pos_of_leverageScore_le_mul_inv_card hdom h0).le
      rw [samplingInjectionDim_def, samplingInjectionDim_def]
      have hrk : ((truncatedSVD A k)ᴴ.rank : ℝ) ≤ k := by exact_mod_cast hr
      have hlog : Real.log ((truncatedSVD A k)ᴴ.rank / δ) ≤ Real.log (k / δ) :=
        Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hrk hδ.le)
      gcongr
  have h := HasSubspaceInjection.measureReal_frobNorm_sub_rsvd_sq_gt_le
    (hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement_of_samplingInjectionDim_le
      hX hdom (by norm_num) hδ hk)
    (isIsotropicSketch_of_hasLaw_samplingSketchWithoutReplacement hX hln) (by norm_num) ht
  rwa [show (1 : ℝ) + t / (1 - 1 / 2) = 1 + 2 * t by ring] at h

end NLAlib
