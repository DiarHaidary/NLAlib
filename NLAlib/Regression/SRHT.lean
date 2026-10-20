/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Regression.SketchAndPrecondition
public import NLAlib.Sketching.Structured.SRHT

/-!
# Regression with a subsampled randomized trigonometric transform

Sketch-and-precondition (`NLAlib.sketchAndPrecondition`) with an SRHT, built from a bounded
orthonormal transform $\mathbf{F}$ with coherence $\beta$, reaches relative squared residual
$1 + \tau$ from the sketch-and-solve start with
$O(\beta(\lvert n\rvert + 1 + \log(\lvert m\rvert/\delta))\log((\lvert n\rvert + 1)/\delta))$
rows and $O(\log(1/\tau))$ iterations, except with probability $\delta$, over any `RCLike` field.
This is Blendenpik's sketch, in exact arithmetic. The sketch embeds
$\operatorname{range}[\mathbf{A}\ \mathbf{y}]$, of dimension at most $\lvert n\rvert + 1$
(`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht_of_samplingEmbeddingDim_le`).
Design: `docs/design/Regression-SketchPrecondition.md` §5.

## Main results

* `NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_srht`: explicit
  sizes.
* [The sketch-and-solve start](https://nla-lib.org/explore/#d/NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_pinv_mulVec_sq_gt_le_of_hasLaw_srht):
  the same from $(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}$.
* [Asymptotic form](https://nla-lib.org/explore/#d/NLAlib.exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_srht):
  the asymptotic form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k m n : Type*} [Fintype k] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {S : Ω → Matrix k m 𝕜} {F : Matrix m m 𝕜} {β : ℝ}

/-- **SRHT sketch-and-precondition**: for a bounded orthonormal transform
$\mathbf{F} \in \Bbbk^{m \times m}$ with coherence $\beta$, an SRHT $\mathbf{S}$ built from it
(independent random signs and an independent uniform choice of $\lvert k\rvert$ distinct rows),
$\mathbf{A}$ of full column rank, $\mathbf{x}_0$ almost surely a minimizer of
$\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, $0 < \varepsilon \le 1/2$, $\delta > 0$ and
at least <!-- value samplingEmbeddingDim {(\lvert n \rvert + 1)} L \varepsilon (\delta/2) -->
$$3 L \log(2(\lvert n \rvert + 1)/(\delta/2))/\varepsilon^2$$
rows (`NLAlib.samplingEmbeddingDim (card n + 1) L ε (δ / 2)`) for the flattened
coherence <!-- value srhtRowBound {\lvert m \rvert} {(\lvert n \rvert + 1)} (\delta/2) -->
$$L = \beta\bigl((\lvert n \rvert + 1) +
2\sqrt{(\lvert n \rvert + 1) \log(\lvert m \rvert/(\delta/2))} +
2 \log(\lvert m \rvert/(\delta/2))\bigr),$$
$\beta$ times `NLAlib.srhtRowBound (card m) (card n + 1) (δ / 2)`, and
$16\varepsilon^{2q+1} \le \tau$,
$$\mathbb{P}\Bigl[(1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 <
\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
\mathbf{x}_0, q)\|^2\Bigr] \le \delta\,.$$
Squared residuals, and $\varepsilon$ is the squared-norm distortion of the embedding of
$\operatorname{range}[\mathbf{A}\ \mathbf{y}]$. [MartinssonTropp2020, §10.5], there unsquared,
after $j \sim \log(1/\varepsilon)$ steps and with no constants.
Asymptotic form:
`NLAlib.exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_srht`.
Result: sketch-and-precondition-ls -/
theorem measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_srht
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srht k F) μ) {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) (y : m → 𝕜) {x₀ : Ω → n → 𝕜}
    (hx₀ : ∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x₀ ω))
    {ε δ τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ : 0 < δ)
    (hk : samplingEmbeddingDim (Fintype.card n + 1)
      (β * srhtRowBound (Fintype.card m) (Fintype.card n + 1) (δ / 2)) ε (δ / 2) ≤
        Fintype.card k)
    {q : ℕ} (hq : 16 * ε ^ (2 * q + 1) ≤ τ) :
    μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A (S ω) y (x₀ ω) q)‖ ^ 2} ≤ δ := by
  sorry

/-- **SRHT sketch-and-precondition from the sketch-and-solve solution**, the algorithm as run:
for a bounded orthonormal transform $\mathbf{F} \in \Bbbk^{m \times m}$ with coherence $\beta$, an
SRHT $\mathbf{S}$ built from it (independent random signs and an independent uniform choice of
$\lvert k\rvert$ distinct rows), $\mathbf{A}$ of full column rank, the start
$\mathbf{x}_0 = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}$, $0 < \varepsilon \le 1/2$,
$\delta > 0$ and
at least <!-- value samplingEmbeddingDim {(\lvert n \rvert + 1)} L \varepsilon (\delta/2) -->
$$3 L \log(2(\lvert n \rvert + 1)/(\delta/2))/\varepsilon^2$$
rows (`NLAlib.samplingEmbeddingDim (card n + 1) L ε (δ / 2)`) for the flattened
coherence <!-- value srhtRowBound {\lvert m \rvert} {(\lvert n \rvert + 1)} (\delta/2) -->
$$L = \beta\bigl((\lvert n \rvert + 1) +
2\sqrt{(\lvert n \rvert + 1) \log(\lvert m \rvert/(\delta/2))} +
2 \log(\lvert m \rvert/(\delta/2))\bigr),$$
$\beta$ times `NLAlib.srhtRowBound (card m) (card n + 1) (δ / 2)`, and
$16\varepsilon^{2q+1} \le \tau$,
$$\mathbb{P}\Bigl[(1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 <
\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}, q)\|^2\Bigr] \le \delta\,.$$
Squared residuals. It fixes the start, not the sample size, so it has no asymptotic form.
[Epperly2024, Algorithm 1], there with the QR form of the start. -/
theorem measureReal_norm_sub_mulVec_sketchAndPrecondition_pinv_mulVec_sq_gt_le_of_hasLaw_srht
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srht k F) μ) {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) (y : m → 𝕜)
    {ε δ τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ : 0 < δ)
    (hk : samplingEmbeddingDim (Fintype.card n + 1)
      (β * srhtRowBound (Fintype.card m) (Fintype.card n + 1) (δ / 2)) ε (δ / 2) ≤
        Fintype.card k)
    {q : ℕ} (hq : 16 * ε ^ (2 * q + 1) ≤ τ) :
    μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A (S ω) y
        (pinv (S ω * A) *ᵥ (S ω *ᵥ y)) q)‖ ^ 2} ≤ δ := by
  sorry

/-- **SRHT sketch-and-precondition, asymptotic form**:
$O(\beta(\lvert n\rvert + 1 + \log(\lvert m\rvert/\delta))\log((\lvert n\rvert + 1)/\delta))$
rows and $O(\log(1/\tau))$ iterations suffice. There are absolute constants
$C, \varepsilon_0 > 0$ such that for a bounded orthonormal transform
$\mathbf{F} \in \Bbbk^{m \times m}$ with coherence $\beta$, an SRHT $\mathbf{S}$ built from it
(independent random signs and an independent uniform choice of $\lvert k\rvert$ distinct rows),
$\mathbf{A}$ of full column rank, $\mathbf{x}_0$ almost surely a minimizer of
$\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, $0 < \tau \le \varepsilon_0$,
$0 < \delta \le 1/2$,
$\lvert k\rvert \ge C\beta(\lvert n\rvert + 1 + \log(\lvert m\rvert/\delta))
\log((\lvert n\rvert + 1)/\delta)$ and $q \ge C\log(1/\tau)$,
$$\mathbb{P}\Bigl[(1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 <
\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
\mathbf{x}_0, q)\|^2\Bigr] \le \delta\,.$$
The constants come before every dimension and $\beta$; the $\log\lvert m\rvert$ of the flattening
stays in the threshold. Squared residuals. Proved from
`NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_srht` at distortion
$1/2$ with $C = 288$ and $\varepsilon_0 = 1/2$. [MartinssonTropp2020, §10.5], there unsquared.
Asymptotic:
NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_srht -/
theorem exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_srht :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 k m n : Type} [MeasurableSpace Ω] [RCLike 𝕜]
      [Fintype k] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (μ : Measure Ω)
      (S : Ω → Matrix k m 𝕜) (F : Matrix m m 𝕜) (β : ℝ) (A : Matrix m n 𝕜) (y : m → 𝕜)
      (x₀ : Ω → n → 𝕜) (τ δ : ℝ) (q : ℕ),
      IsBoundedOrthonormal F β → HasLaw S (srht k F) μ → Function.Injective A.mulVec →
      (∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x₀ ω)) →
      0 < τ → τ ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (β * (Fintype.card n + 1 + Real.log (Fintype.card m / δ)) *
        Real.log ((Fintype.card n + 1) / δ)) ≤ Fintype.card k →
      C * Real.log (1 / τ) ≤ q →
      μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
        ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A (S ω) y (x₀ ω) q)‖ ^ 2} ≤ δ := by
  sorry

end NLAlib
