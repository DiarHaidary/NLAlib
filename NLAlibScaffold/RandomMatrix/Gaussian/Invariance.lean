/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Projector
public import NLAlib.Probability.Distributions.ChiSquare
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.ForMathlib.Probability.Independence.Basic

/-!
# Lower tails of projected Gaussian vectors (scaffold)

Statements for `NLAlib/RandomMatrix/Gaussian/Invariance.lean` (stage LB-C1, design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.4): the squared norm of the projection
of a standard Gaussian vector by an orthogonal projector of rank at least $r$ has the $\chi^2_r$
lower tail, also for a random projector independent of the vector ([Shamir2026, eq. (10)]).

## Main results

* `NLAlib.measureReal_norm_mulVec_sq_le_mul_le_of_hasLaw_gaussianVector`.
* `NLAlib.measureReal_norm_mulVec_sq_le_mul_le_of_hasLaw_gaussianVector_of_indepFun`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {g : Ω → n → ℝ}

/-- **Lower tail of a projected Gaussian vector**: let $\mathbf{g}$ be a standard Gaussian vector
and $\mathbf{P}$ an orthogonal projector of rank at least $r$. For $0 < \beta \le 1$,
$$\mathbb{P}\bigl[\|\mathbf{P}\mathbf{g}\|^2 \le \beta r\bigr] \le
\exp\Bigl(\frac{r}{2}(1 - \beta + \log\beta)\Bigr) \,.$$
[LaurentMassart2000, Lemma 1]; there for a $\chi^2_r$ variable, here for every rank at least $r$.
Proof: write $\mathbf{P} = \mathbf{Q}\mathbf{Q}^{\mathsf{H}}$ with $\mathbf{Q}$ a frame of its
range ($\rho = \operatorname{rank}\mathbf{P}$ columns), so $\|\mathbf{P}\mathbf{g}\| =
\|\mathbf{Q}^{\mathsf{H}}\mathbf{g}\|$ and $\mathbf{Q}^{\mathsf{H}}\mathbf{g}$ is standard Gaussian
on $\rho$ coordinates (`NLAlib.hasLaw_mulVec_of_hasLaw_gaussianVector`); apply
`NLAlib.measureReal_norm_sq_le_mul_card_le_of_hasLaw_gaussianVector` with
$\beta' = \beta r/\rho \le \beta$ and use that $\beta \mapsto 1 - \beta + \log\beta$ is
nonpositive and increasing on $(0, 1]$ (`Real.add_one_le_exp`, `Real.log_le_sub_one_of_pos`),
so $\rho(1 - \beta' + \log\beta') \le r(1 - \beta + \log\beta)$. The case $r = 0$ is trivial.
M, about 50 lines. -/
theorem measureReal_norm_mulVec_sq_le_mul_le_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) {P : Matrix n n ℝ} (hP : IsStarProjection P) {r : ℕ}
    (hr : r ≤ P.rank) {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1) :
    μ.real {ω | ‖WithLp.toLp 2 (P *ᵥ g ω)‖ ^ 2 ≤ β * r} ≤
      Real.exp (r / 2 * (1 - β + Real.log β)) := by
  sorry

/-- **Lower tail of a Gaussian vector projected by an independent projector**: let $\mathbf{g}$ be
a standard Gaussian vector and $\mathbf{P}$ a random orthogonal projector independent of
$\mathbf{g}$, of rank at least $r$ for every outcome. For $0 < \beta \le 1$,
$$\mathbb{P}\bigl[\|\mathbf{P}\mathbf{g}\|^2 \le \beta r\bigr] \le
\exp\Bigl(\frac{r}{2}(1 - \beta + \log\beta)\Bigr) \,.$$
[Shamir2026, eq. (10)]; there for $\mathbf{P}$ the projector away from the span of independent
Gaussian vectors.
Proof: freeze $\mathbf{P}$ with `ProbabilityTheory.IndepFun.measureReal_mem_le_add` ($G$ the
measurable set of projectors of rank at least $r$, so $\delta_2 = 0$); each section is
`NLAlib.measureReal_norm_mulVec_sq_le_mul_le_of_hasLaw_gaussianVector`. S, about 15 lines. -/
theorem measureReal_norm_mulVec_sq_le_mul_le_of_hasLaw_gaussianVector_of_indepFun
    (hg : HasLaw g (gaussianVector n) μ) {P : Ω → Matrix n n ℝ} (hPm : AEMeasurable P μ)
    (hgP : IndepFun g P μ) (hP : ∀ ω, IsStarProjection (P ω)) {r : ℕ}
    (hr : ∀ ω, r ≤ (P ω).rank) {β : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1) :
    μ.real {ω | ‖WithLp.toLp 2 (P ω *ᵥ g ω)‖ ^ 2 ≤ β * r} ≤
      Real.exp (r / 2 * (1 - β + Real.log β)) := by
  sorry

end NLAlib
