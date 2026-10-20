/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Regression.SketchAndPrecondition
public import NLAlib.Sketching.Gaussian.SubGaussian

/-!
# Regression with a sub-Gaussian sketch

Sketch-and-precondition (`NLAlib.sketchAndPrecondition`) with the normalised sketch
$\lvert k\rvert^{-1/2}\mathbf{X}$, for $\mathbf{X}$ with independent, isotropic, sub-Gaussian rows
with proxy $c$, reaches relative squared residual $1 + \tau$ from the sketch-and-solve start with
$O(c^2(\lvert n\rvert + 1 + \log(1/\delta)))$ rows and $O(\log(1/\tau))$ iterations, except with
probability $\delta$. The sketch embeds $\operatorname{range}[\mathbf{A}\ \mathbf{y}]$, of
dimension at most $\lvert n\rvert + 1$
(`NLAlib.isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le`).
Design: `docs/design/Regression-SketchPrecondition.md` §5.

## Main results

* `NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_isSubgaussianVector`:
  explicit sizes.
* [The sketch-and-solve start](https://nla-lib.org/explore/#d/NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_pinv_mulVec_sq_gt_le_of_isSubgaussianVector):
  the same from $(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}$.
* [Asymptotic form](https://nla-lib.org/explore/#d/NLAlib.exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_isSubgaussianVector):
  the asymptotic form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k m n : Type*} [Fintype k]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {X : Ω → Matrix k m ℝ} {c : ℝ≥0}

-- A backticked declaration name in the docstring exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Sub-Gaussian sketch-and-precondition**: for a random $\mathbf{X} \in \mathbb{R}^{k \times m}$
with independent rows, each isotropic and sub-Gaussian with proxy $c$, the sketch
$\mathbf{S} = \lvert k\rvert^{-1/2}\mathbf{X}$, $\mathbf{A}$ of full column rank, $\mathbf{x}_0$
almost surely a minimizer of $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$,
$0 < \varepsilon \le 1/2$, $\varepsilon \le 2c$, $\delta > 0$,
at least <!-- value subgaussianEmbeddingDim c {(\lvert n \rvert + 1)} \varepsilon \delta -->
$$4 c^2 ((\lvert n \rvert + 1) \log 9 + \log(2/\delta))/(C \varepsilon^2)$$
rows (`subgaussianEmbeddingDim c (card n + 1) ε δ`,
with <!-- value subgaussianJLConstant -->$C = 1/64$ the constant `subgaussianJLConstant`) and
$16\varepsilon^{2q+1} \le \tau$,
$$\mathbb{P}\Bigl[(1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 <
\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
\mathbf{x}_0, q)\|^2\Bigr] \le \delta\,.$$
Squared residuals, and $\varepsilon$ is the squared-norm distortion of the embedding of
$\operatorname{range}[\mathbf{A}\ \mathbf{y}]$. [MartinssonTropp2020, §10.5], there unsquared,
after $j \sim \log(1/\varepsilon)$ steps and with no constants.
Asymptotic form:
`NLAlib.exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_isSubgaussianVector`.
Result: sketch-and-precondition-ls -/
theorem measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_isSubgaussianVector
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {A : Matrix m n ℝ}
    (hA : Function.Injective A.mulVec) (y : m → ℝ) {x₀ : Ω → n → ℝ}
    (hx₀ : ∀ᵐ ω ∂μ, IsLeastSquaresSolution ((√(Fintype.card k : ℝ))⁻¹ • X ω * A)
      ((√(Fintype.card k : ℝ))⁻¹ • X ω *ᵥ y) (x₀ ω))
    {ε δ τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hεc : ε ≤ 2 * c) (hδ : 0 < δ)
    (hk : subgaussianEmbeddingDim c (Fintype.card n + 1) ε δ ≤ Fintype.card k)
    {q : ℕ} (hq : 16 * ε ^ (2 * q + 1) ≤ τ) :
    μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A ((√(Fintype.card k : ℝ))⁻¹ • X ω) y
        (x₀ ω) q)‖ ^ 2} ≤ δ := by
  sorry

/-- **Sub-Gaussian sketch-and-precondition from the sketch-and-solve solution**, the algorithm as
run: for a random $\mathbf{X} \in \mathbb{R}^{k \times m}$ with independent rows, each isotropic
and sub-Gaussian with proxy $c$, the sketch $\mathbf{S} = \lvert k\rvert^{-1/2}\mathbf{X}$,
$\mathbf{A}$ of full column rank, the start
$\mathbf{x}_0 = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}$,
$0 < \varepsilon \le 1/2$, $\varepsilon \le 2c$, $\delta > 0$,
at least <!-- value subgaussianEmbeddingDim c {(\lvert n \rvert + 1)} \varepsilon \delta -->
$$4 c^2 ((\lvert n \rvert + 1) \log 9 + \log(2/\delta))/(C \varepsilon^2)$$
rows (`subgaussianEmbeddingDim c (card n + 1) ε δ`,
with <!-- value subgaussianJLConstant -->$C = 1/64$ the constant `subgaussianJLConstant`) and
$16\varepsilon^{2q+1} \le \tau$,
$$\mathbb{P}\Bigl[(1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 <
\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}, q)\|^2\Bigr] \le \delta\,.$$
Squared residuals. It fixes the start, not the sample size, so it has no asymptotic form.
[Epperly2024, Algorithm 1], there with the QR form of the start. -/
theorem
    measureReal_norm_sub_mulVec_sketchAndPrecondition_pinv_mulVec_sq_gt_le_of_isSubgaussianVector
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {A : Matrix m n ℝ}
    (hA : Function.Injective A.mulVec) (y : m → ℝ)
    {ε δ τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hεc : ε ≤ 2 * c) (hδ : 0 < δ)
    (hk : subgaussianEmbeddingDim c (Fintype.card n + 1) ε δ ≤ Fintype.card k)
    {q : ℕ} (hq : 16 * ε ^ (2 * q + 1) ≤ τ) :
    μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A ((√(Fintype.card k : ℝ))⁻¹ • X ω) y
        (pinv ((√(Fintype.card k : ℝ))⁻¹ • X ω * A) *ᵥ ((√(Fintype.card k : ℝ))⁻¹ • X ω *ᵥ y))
        q)‖ ^ 2} ≤ δ := by
  sorry

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Sub-Gaussian sketch-and-precondition, asymptotic form**:
$O(c^2(\lvert n\rvert + 1 + \log(1/\delta)))$ rows and $O(\log(1/\tau))$ iterations suffice.
There are absolute constants $C, \varepsilon_0 > 0$ such that for a random
$\mathbf{X} \in \mathbb{R}^{k \times m}$ with $k$ nonempty and independent rows, each isotropic and
sub-Gaussian with proxy $c$, the sketch $\mathbf{S} = \lvert k\rvert^{-1/2}\mathbf{X}$,
$\mathbf{A}$ of full column rank, $\mathbf{x}_0$ almost surely a minimizer of
$\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, $0 < \tau \le \varepsilon_0$,
$0 < \delta \le 1/2$, $\lvert k\rvert \ge Cc^2(\lvert n\rvert + 1 + \log(1/\delta))$ and
$q \ge C\log(1/\tau)$,
$$\mathbb{P}\Bigl[(1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 <
\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
\mathbf{x}_0, q)\|^2\Bigr] \le \delta\,.$$
The constants come before every dimension and the proxy. Squared residuals. Proved from
`NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_isSubgaussianVector` at
distortion $1/2$ with $C = 4608$ and $\varepsilon_0 = 1/2$; isotropy forces $c \ge 1$.
[MartinssonTropp2020, §10.5], there unsquared.
Asymptotic:
NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_isSubgaussianVector -/
theorem
    exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_isSubgaussianVector :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k m n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype m]
      [Fintype n] [DecidableEq m] [DecidableEq n] [Nonempty k] (μ : Measure Ω)
      (X : Ω → Matrix k m ℝ) (c : ℝ≥0) (A : Matrix m n ℝ) (y : m → ℝ) (x₀ : Ω → n → ℝ)
      (τ δ : ℝ) (q : ℕ),
      iIndepFun (fun i ω => X ω i) μ → (∀ i, IsSubgaussianVector (fun ω => X ω i) c μ) →
      (∀ i, IsIsotropic (fun ω => X ω i) μ) → Function.Injective A.mulVec →
      (∀ᵐ ω ∂μ, IsLeastSquaresSolution ((√(Fintype.card k : ℝ))⁻¹ • X ω * A)
        ((√(Fintype.card k : ℝ))⁻¹ • X ω *ᵥ y) (x₀ ω)) →
      0 < τ → τ ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((c : ℝ) ^ 2 * (Fintype.card n + 1 + Real.log (1 / δ))) ≤ Fintype.card k →
      C * Real.log (1 / τ) ≤ q →
      μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
        ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A ((√(Fintype.card k : ℝ))⁻¹ • X ω) y
          (x₀ ω) q)‖ ^ 2} ≤ δ := by
  sorry

end NLAlib
