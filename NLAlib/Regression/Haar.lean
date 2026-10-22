/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Basic
public import NLAlib.Regression.Oblivious
public import NLAlib.Regression.SketchAndPrecondition
public import NLAlib.Sketching.Gaussian.HaarEmbedding

/-!
# Regression with a Haar sketch

Sketch-and-precondition (`NLAlib.sketchAndPrecondition`) with the Haar sketch
$\mathbf{S} = \sqrt{\lvert m\rvert/\lvert k\rvert}\,\mathbf{Q}^{\mathsf{H}}$, $\mathbf{Q}$ an
$m \times k$ Haar frame, $\lvert k\rvert \le \lvert m\rvert$, reaches relative squared residual
$1 + \tau$ from the sketch-and-solve start with $O(\lvert n\rvert + 1 + \log(1/\delta))$ rows and
$O(\log(1/\tau))$ iterations, except with probability $\delta$: the sketch embeds
$\operatorname{range}[\mathbf{A}\ \mathbf{y}]$ with constants $1 \mp \varepsilon$ by JL and a net
(`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame_of_jlDim_le`). Sketch-and-solve with the
unnormalized sketch $\mathbf{Q}^{\mathsf{H}}$ reaches relative squared Frobenius residual error
with failure probability $\delta$ at $O((r + 1)\log(1/\delta)/\varepsilon)$ rows,
$r = \operatorname{rank}\mathbf{A}$, through a constant subspace injection and the Haar JL moment
at $p = \log(1/\delta)$; its expectation forms are in `NLAlib.Regression.SketchAndSolve`. Design:
`docs/design/Regression-SketchPrecondition.md` §7, `docs/design/Sketching-Moments.md` §4.3.

## Main results

* `NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_haarFrame`:
  explicit sizes;
  `measureReal_norm_sub_mulVec_sketchAndPrecondition_pinv_mulVec_sq_gt_le_of_hasLaw_haarFrame`,
  the same from $(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}$; the asymptotic form
  `exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_haarFrame`.
* `NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_haarFrame`: Haar
  sketch-and-solve with high probability, and its asymptotic form
  `exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_haarFrame`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k m n : Type*} [Fintype k]
  [Fintype m] [Fintype n] [DecidableEq k] [DecidableEq m] {Q : Ω → Matrix m k ℝ}

/-! ### Sketch-and-precondition -/

section SketchAndPrecondition

variable [DecidableEq n]

/-- **Haar sketch-and-precondition**: for an $m \times k$ Haar frame $\mathbf{Q}$,
$\lvert k\rvert \le \lvert m\rvert$, the sketch
$\mathbf{S} = \sqrt{\lvert m\rvert/\lvert k\rvert}\,\mathbf{Q}^{\mathsf{H}}$, $\mathbf{A}$ of full
column rank, $\mathbf{x}_0$ almost surely a minimizer of
$\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, $0 < \varepsilon \le 1/2$, $\delta > 0$, at
least <!-- value jlDim (4\varepsilon/5) (\delta/21^{\lvert n \rvert + 1}) -->
$$\log(2/(\delta/21^{\lvert n \rvert + 1}))/((4\varepsilon/5)^2/4 - (4\varepsilon/5)^3/6)$$
rows (`jlDim (4 * ε / 5) (δ / 21 ^ (card n + 1))`) and $16\varepsilon^{2q+1} \le \tau$,
$$\mathbb{P}\Bigl[(1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 <
\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
\mathbf{x}_0, q)\|^2\Bigr] \le \delta\,.$$
Squared residuals; $\varepsilon$ is the squared-norm distortion of the embedding of
$\operatorname{range}[\mathbf{A}\ \mathbf{y}]$, of dimension at most $\lvert n\rvert + 1$.
[MartinssonTropp2020, §10.5], there unsquared, after $j \sim \log(1/\varepsilon)$ steps and with
no constants. Asymptotic form:
`exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_haarFrame`.
Result: sketch-and-precondition-ls -/
theorem measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_haarFrame
    (hQ : HasLaw Q (haarFrame m k) μ) (hkm : Fintype.card k ≤ Fintype.card m)
    {A : Matrix m n ℝ} (hA : Function.Injective A.mulVec) (y : m → ℝ) {x₀ : Ω → n → ℝ}
    (hx₀ : ∀ᵐ ω ∂μ, IsLeastSquaresSolution
      (√(Fintype.card m / Fintype.card k : ℝ) • (Q ω)ᴴ * A)
      (√(Fintype.card m / Fintype.card k : ℝ) • (Q ω)ᴴ *ᵥ y) (x₀ ω))
    {ε δ τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ : 0 < δ)
    (hk : jlDim (4 * ε / 5) (δ / 21 ^ (Fintype.card n + 1)) ≤ Fintype.card k)
    {q : ℕ} (hq : 16 * ε ^ (2 * q + 1) ≤ τ) :
    μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A
        (√(Fintype.card m / Fintype.card k : ℝ) • (Q ω)ᴴ) y (x₀ ω) q)‖ ^ 2} ≤ δ := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  exact ((isObliviousSubspaceEmbedding_of_hasLaw_haarFrame_of_jlDim_le hQ hkm hε (by linarith) hδ
    hk).hasSubspaceEmbedding
      (U := Matrix.fromCols A (Matrix.replicateCol Unit y)) ((Matrix.rank_le_card_width _).trans_eq
      (by rw [Fintype.card_sum, Fintype.card_unit]))
    ).measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_one_sub_one_add hε hε1 hA
      (hx₀.mono fun ω h => by rwa [Matrix.smul_mulVec]) hq

/-- **Haar sketch-and-precondition from the sketch-and-solve solution**, the algorithm as run:
for an $m \times k$ Haar frame $\mathbf{Q}$, $\lvert k\rvert \le \lvert m\rvert$, the sketch
$\mathbf{S} = \sqrt{\lvert m\rvert/\lvert k\rvert}\,\mathbf{Q}^{\mathsf{H}}$, $\mathbf{A}$ of full
column rank, the start $\mathbf{x}_0 = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}$,
$0 < \varepsilon \le 1/2$, $\delta > 0$, at
least <!-- value jlDim (4\varepsilon/5) (\delta/21^{\lvert n \rvert + 1}) -->
$$\log(2/(\delta/21^{\lvert n \rvert + 1}))/((4\varepsilon/5)^2/4 - (4\varepsilon/5)^3/6)$$
rows (`jlDim (4 * ε / 5) (δ / 21 ^ (card n + 1))`) and $16\varepsilon^{2q+1} \le \tau$,
$$\mathbb{P}\Bigl[(1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 <
\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}, q)\|^2\Bigr] \le \delta\,.$$
Squared residuals. It fixes the start, not the sample size, so it has no asymptotic form.
[Epperly2024, Algorithm 1], there with the QR form of the start. -/
theorem
    measureReal_norm_sub_mulVec_sketchAndPrecondition_pinv_mulVec_sq_gt_le_of_hasLaw_haarFrame
    (hQ : HasLaw Q (haarFrame m k) μ) (hkm : Fintype.card k ≤ Fintype.card m)
    {A : Matrix m n ℝ} (hA : Function.Injective A.mulVec) (y : m → ℝ)
    {ε δ τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ : 0 < δ)
    (hk : jlDim (4 * ε / 5) (δ / 21 ^ (Fintype.card n + 1)) ≤ Fintype.card k)
    {q : ℕ} (hq : 16 * ε ^ (2 * q + 1) ≤ τ) :
    μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A
        (√(Fintype.card m / Fintype.card k : ℝ) • (Q ω)ᴴ) y
        (pinv (√(Fintype.card m / Fintype.card k : ℝ) • (Q ω)ᴴ * A) *ᵥ
          (√(Fintype.card m / Fintype.card k : ℝ) • (Q ω)ᴴ *ᵥ y)) q)‖ ^ 2} ≤ δ :=
  measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_haarFrame hQ hkm hA y
    (ae_of_all _ fun _ => isLeastSquaresSolution_pinv_mulVec _ _) hε hε1 hδ hk hq

/-- **Haar sketch-and-precondition, asymptotic form**:
$O(\lvert n\rvert + 1 + \log(1/\delta))$ rows and $O(\log(1/\tau))$ iterations suffice. There
are absolute constants $C, \varepsilon_0 > 0$ such that for an $m \times k$ Haar frame
$\mathbf{Q}$, $\lvert k\rvert \le \lvert m\rvert$, the sketch
$\mathbf{S} = \sqrt{\lvert m\rvert/\lvert k\rvert}\,\mathbf{Q}^{\mathsf{H}}$, $\mathbf{A}$ of full
column rank, $\mathbf{x}_0$ almost surely a minimizer of
$\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, $0 < \tau \le \varepsilon_0$,
$0 < \delta \le 1/2$, $\lvert k\rvert \ge C(\lvert n\rvert + 1 + \log(1/\delta))$ and
$q \ge C\log(1/\tau)$,
$$\mathbb{P}\Bigl[(1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 <
\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
\mathbf{x}_0, q)\|^2\Bigr] \le \delta\,.$$
The constants come before every dimension. Squared residuals. Proved from
`NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_haarFrame` at
distortion $1/2$. [MartinssonTropp2020, §10.5], there unsquared.
Asymptotic:
NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_haarFrame -/
theorem
    exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_haarFrame :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k m n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype m]
      [Fintype n] [DecidableEq k] [DecidableEq m] [DecidableEq n] (μ : Measure Ω)
      (Q : Ω → Matrix m k ℝ) (A : Matrix m n ℝ) (y : m → ℝ) (x₀ : Ω → n → ℝ) (τ δ : ℝ) (q : ℕ),
      HasLaw Q (haarFrame m k) μ → Fintype.card k ≤ Fintype.card m →
      Function.Injective A.mulVec →
      (∀ᵐ ω ∂μ, IsLeastSquaresSolution (√(Fintype.card m / Fintype.card k : ℝ) • (Q ω)ᴴ * A)
        (√(Fintype.card m / Fintype.card k : ℝ) • (Q ω)ᴴ *ᵥ y) (x₀ ω)) →
      0 < τ → τ ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (Fintype.card n + 1 + Real.log (1 / δ)) ≤ Fintype.card k →
      C * Real.log (1 / τ) ≤ q →
      μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
        ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A
          (√(Fintype.card m / Fintype.card k : ℝ) • (Q ω)ᴴ) y (x₀ ω) q)‖ ^ 2} ≤ δ := by
  sorry

end SketchAndPrecondition

/-! ### Sketch-and-solve with high probability -/

/-- **Haar sketch-and-solve, relative residual with high probability**: for an $m \times k$ Haar
frame $\mathbf{Q}$, $k$ nonempty, $\lvert k\rvert \le \lvert m\rvert$,
$r = \operatorname{rank}\mathbf{A}$, $0 < \varepsilon \le 4$ and $\delta > 0$,
if <!-- value jlDim (2/5) (\delta/2/21^r) -->
$$\lvert k\rvert \ge \log(2/(\delta/2/21^r))/((2/5)^2/4 - (2/5)^3/6)$$
and <!-- value jlMomentDim {\sqrt{\varepsilon/(4(r + 1))}} (\delta/2) -->
$$\lvert k\rvert \ge 128\max(2, \log(1/(\delta/2)))/\sqrt{\varepsilon/(4(r + 1))}^2\,,$$
then
$$\mathbb{P}\bigl[(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2<\|\mathbf{B}-\mathbf{A}\,
\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{Q}^{\mathsf{H}},\mathbf{B})\|_{\mathsf{F}}^2\bigr]
\le\delta\,.$$
The sizes are `jlDim (2 / 5) (δ / 2 / 21 ^ A.rank)` and
`jlMomentDim (√(ε / (4 * (A.rank + 1)))) (δ / 2)`; the sketch is unnormalized, the scaling
cancels in `NLAlib.sketchAndSolve`. The route: the OSI at constant $1/2$ and failure $\delta/2$
(`NLAlib.isObliviousSubspaceInjection_of_hasLaw_haarFrame_of_jlDim_le`), the JL moment
`NLAlib.hasJLMoment_of_hasLaw_haarFrame_of_jlMomentDim_le` at $\sqrt{\varepsilon/(4(r+1))}$ with
failure $\delta/2$, and `NLAlib.HasJLMoment.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le`.
Its expectation twin is
`NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_haarFrame`.
[Woodruff2014, proof of Theorem 23]; the injection-plus-multiplication route there, here with a
Haar sketch. Asymptotic form:
`NLAlib.exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_haarFrame`.
Result: sketch-and-solve-ls -/
theorem measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_haarFrame [Nonempty k]
    (hQ : HasLaw Q (haarFrame m k) μ) (hkm : Fintype.card k ≤ Fintype.card m)
    (A : Matrix m n ℝ) {r : Type*} [Fintype r] (B : Matrix m r ℝ) {ε δ : ℝ} (hε : 0 < ε)
    (hε4 : ε ≤ 4) (hδ : 0 < δ) (hk : jlDim (2 / 5) (δ / 2 / 21 ^ A.rank) ≤ Fintype.card k)
    (hk' : jlMomentDim (√(ε / (4 * ((A.rank : ℝ) + 1)))) (δ / 2) ≤ Fintype.card k) :
    μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
      frobNorm (B - A * sketchAndSolve A (Q ω)ᴴ B) ^ 2} ≤ δ := by
  sorry

/-- **Haar sketch-and-solve, asymptotic relative residual with high probability**:
$O((r+1)\log(1/\delta)/\varepsilon)$ rows suffice, with $r=\operatorname{rank}\mathbf{A}$: there
are absolute $C,\varepsilon_0>0$ such that for an $m \times k$ Haar frame $\mathbf{Q}$, $k$
nonempty, $\lvert k\rvert \le \lvert m\rvert$,
$\lvert k\rvert \ge C(r+1)\log(1/\delta)/\varepsilon$, $0<\varepsilon\le\varepsilon_0$ and
$0<\delta\le1/2$,
$$\mathbb{P}\bigl[(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2<\|\mathbf{B}-\mathbf{A}\,
\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{Q}^{\mathsf{H}},\mathbf{B})\|_{\mathsf{F}}^2\bigr]
\le\delta\,.$$
All constants precede dimensions and data. Proved from
`NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_haarFrame` with
$\varepsilon_0 = 1$. [Woodruff2014, proof of Theorem 23].
Asymptotic: NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_haarFrame
Result: sketch-and-solve-ls -/
theorem
    exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_haarFrame :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ {Ω k m n r : Type} [MeasurableSpace Ω] [Fintype k] [Fintype m] [Fintype n]
        [Fintype r] [DecidableEq k] [DecidableEq m] [Nonempty k] (μ : Measure Ω)
        (Q : Ω → Matrix m k ℝ) (A : Matrix m n ℝ) (B : Matrix m r ℝ) (ε δ : ℝ),
        HasLaw Q (haarFrame m k) μ → Fintype.card k ≤ Fintype.card m →
        0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
        C * (((A.rank : ℝ) + 1) * Real.log (1 / δ) / ε) ≤ Fintype.card k →
        μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
          frobNorm (B - A * sketchAndSolve A (Q ω)ᴴ B) ^ 2} ≤ δ := by
  sorry

end NLAlib
