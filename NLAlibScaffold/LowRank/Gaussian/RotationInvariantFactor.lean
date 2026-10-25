/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RotationInvariantFactor

/-!
# The two-eigenvalue instance attains Epperly and Webber's factor (stage S10)

Epperly and Webber's Lemma 6.2 as a limit: on $\mathbf{D}_a = \operatorname{diag}(a\mathbf{I}_q,
b\mathbf{I}_{r-q})$ the expected trace error of Nyström tends, as $a \to \infty$,
to the factor <!-- value rotationInvariantFactor r \ell q -->
$(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))$ times $b(r - q)$, the bound that
`NLAlib.integral_nuclearNorm_fromBlocks_sub_nystrom_le_of_isLeftUnitarilyInvariant` proves at every
$a$. It joins `NLAlib/LowRank/Gaussian/RotationInvariantFactor.lean` (whose docstring reserves the
file for the matching lower bounds); its proof is deferred. Design:
`docs/design/LowRank-EstimatorLowerBounds.md` §3.3.

## Main results

* `NLAlib.tendsto_integral_nuclearNorm_fromBlocks_sub_nystrom_of_isLeftUnitarilyInvariant`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l : Type*} [Fintype l]

/-- **The two-eigenvalue instance attains the factor** (Epperly and Webber's Lemma 6.2): for
$\mathbf{Y}$ on $(s \oplus t) \times l$ with a left unitarily invariant law and full column rank
almost surely, $q = \lvert s\rvert$, $r = \lvert s\rvert + \lvert t\rvert$, $q + 2 \le \ell$,
$b \ge 0$ and $\mathbf{D}_a = \operatorname{diag}(a\mathbf{I}, b\mathbf{I})$,
so <!-- value rotationInvariantFactor r \ell q -->
$$\lim_{a \to \infty}\mathbb{E}\bigl\|\mathbf{D}_a - \mathsf{nystrom}(\mathbf{D}_a,
\mathbf{Y})\bigr\|_*
= \frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,b\,\lvert t\rvert\,.$$
With the upper bound at every $a$
(`NLAlib.integral_nuclearNorm_fromBlocks_sub_nystrom_le_of_isLeftUnitarilyInvariant`) this is the
sharpness of Epperly and Webber's factor on this instance. At $\ell = r$ both sides are $0$.
[EpperlyWebber2026, Lemma 6.2]; there over $\mathbb{R}$ and $\mathbb{C}$ with $a > b > 0$ and a zero
block, here real, $b \ge 0$, no zero block.
Proof: L, about 120 lines. Pass to the polar factor $\mathbf{\Psi}$, a Haar frame with the same
Nyström approximation (`hasLaw_polarFactor_of_isLeftUnitarilyInvariant`,
`Matrix.PosSemidef.nystrom_eq_of_range_eq`, as in the upper bound's proof). Dominated
convergence (`tendsto_integral_filter_of_dominated_convergence`): the dominator is the upper
bound's pointwise bound $b\|(\mathbf{W}\mathbf{\Psi})^{+}\|_{\mathsf{F}}^2 + b(\lvert t\rvert -
\ell)$
(`HasOrthonormalCols.nuclearNorm_fromBlocks_sub_nystrom_le`), integrable by
`integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame`, and it is also the pointwise limit.
For the limit, a.s. $\mathbf{\Psi}_1 = \mathbf{W}\mathbf{\Psi}$ ($q \times \ell$) has full row rank
(`ae_rank_mul_eq_min_of_hasLaw_haarFrame`). For $b > 0$ and $a > 0$ the error is exactly
$b(\lvert t\rvert - \ell) + ab\operatorname{Re}\operatorname{tr}\bigl(b\mathbf{I} +
(a-b)\mathbf{\Psi}_1\mathbf{\Psi}_1^{\mathsf{H}}\bigr)^{-1}$
(`HasOrthonormalCols.nuclearNorm_fromBlocks_sub_nystrom`); since $ab(b\mathbf{I} +
(a-b)\mathbf{K}\mathbf{K}^{\mathsf{H}})^{-1} = b\bigl((b/a)\mathbf{I} + (1 - b/a)
\mathbf{K}\mathbf{K}^{\mathsf{H}}\bigr)^{-1}$ and $\mathbf{K}\mathbf{K}^{\mathsf{H}}$
($\mathbf{K} = \mathbf{\Psi}_1$) is invertible, continuity of inversion gives the limit
$b(\lvert t\rvert - \ell) + b\operatorname{tr}(\mathbf{K}\mathbf{K}^{\mathsf{H}})^{-1} =
b(\lvert t\rvert - \ell) + b\|\mathbf{\Psi}_1^{+}\|_{\mathsf{F}}^2$, the dominator; no Schur
or QR form is needed. For $b = 0$ the error is $0$ for $a > 0$ (both sides vanish). The limit
value is the upper bound's computation. -/
theorem tendsto_integral_nuclearNorm_fromBlocks_sub_nystrom_of_isLeftUnitarilyInvariant
    {s t : Type*} [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    {ν' : Measure (Matrix (s ⊕ t) l ℝ)} [IsProbabilityMeasure ν'] [IsLeftUnitarilyInvariant ν']
    {Y : Ω → Matrix (s ⊕ t) l ℝ} (hY : HasLaw Y ν' μ)
    (hYr : ∀ᵐ ω ∂μ, Function.Injective (Y ω).mulVec) (hsl : Fintype.card s + 2 ≤ Fintype.card l)
    {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun a : ℝ => ∫ ω, nuclearNorm (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0
        (b • (1 : Matrix t t ℝ)) - nystrom (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0
          (b • (1 : Matrix t t ℝ))) (Y ω)) ∂μ) atTop
      (𝓝 (rotationInvariantFactor (Fintype.card s + Fintype.card t) (Fintype.card l)
        (Fintype.card s) * (b * Fintype.card t))) := by
  sorry

end NLAlib
