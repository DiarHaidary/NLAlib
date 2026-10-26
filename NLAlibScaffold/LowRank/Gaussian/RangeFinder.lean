/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RangeFinder

/-!
# The spectral residual of the Gaussian range finder at a comparison rank (research)

For a standard Gaussian $n \times \ell$ test matrix, $1 \le k$ and $4k \le \ell$, the second
spectral moment of the range-finder residual is $O(1/\ell)$ times the optimal Frobenius error:
$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_2^2 \le
(121/\ell)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$. The library proves it
as a private step of `NLAlib/LowRank/Gaussian/TruncatedGeneralizedNystrom.lean`; the upper bound
of `docs/design/research/TruncatedGN-Upper.md` (R1) needs it public. Joins
`NLAlib/LowRank/Gaussian/RangeFinder.lean`. Not for `main`. Proofs deferred.

## Main results

* `NLAlib.integral_specNorm_sub_rsvd_sq_le_div_of_hasLaw_gaussianMatrix` (R1).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] {X : Ω → Matrix n l ℝ}

/-- **The spectral residual of the range finder is $O(1/\ell)$ of the optimal Frobenius
error**: for a standard Gaussian test matrix $\mathbf{\Omega} \in \mathbb{R}^{n \times \ell}$,
$1 \le k$ and $4k \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_2^2 \le
\frac{121}{\ell}\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
No printed source; the comparison-rank argument of [HalkoMartinssonTropp2011, Theorem 10.6].
Proof: S, about 90 lines, copied. The private lemma integral_specNorm_sub_rsvd_sq_le_div of
`NLAlib/LowRank/Gaussian/TruncatedGeneralizedNystrom.lean` is this statement; copy it and its
three private helpers (residual_arith, div_le_three_of_half,
mul_gaussianPinvSpecNormBound_sq_le_of_half) as private lemmas here. They use
`integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound` at the comparison
rank $\lceil\ell/2\rceil$, `natCast_mul_singularValues_add_sq_le_frobNorm_sub_truncatedSVD_sq`,
`frobNorm_sub_truncatedSVD_sq` and `gaussianPinvSpecNormBound_def`. -/
theorem integral_specNorm_sub_rsvd_sq_le_div_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : 1 ≤ k) (hkl : 4 * k ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      121 / (Fintype.card l : ℝ) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  sorry

end NLAlib
