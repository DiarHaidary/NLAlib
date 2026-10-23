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
  refine ⟨288, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro Ω k m n _ _ _ _ _ _ _ μ Q A y x₀ τ δ q hQ hkm hA hx₀ hτ hτ1 hδ hδ2 hk hq
  have h2 := Real.log_two_le_log_one_div hδ hδ2
  have hl2 := Real.log_two_gt_d9
  have hτl : 0 ≤ Real.log (1 / τ) := Real.log_nonneg (by rw [le_div_iff₀ hτ]; linarith)
  have h21 : (1 : ℝ) ≤ 21 ^ (Fintype.card n + 1) := one_le_pow₀ (by norm_num)
  have hl : Real.log (2 / (δ / 21 ^ (Fintype.card n + 1))) =
      Real.log 2 + ((Fintype.card n : ℝ) + 1) * Real.log 21 + Real.log (1 / δ) := by
    rw [show 2 / (δ / 21 ^ (Fintype.card n + 1)) = 2 * 21 ^ (Fintype.card n + 1) * (1 / δ) by
        field_simp, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hd21 : ((Fintype.card n : ℝ) + 1) * Real.log 21 ≤ ((Fintype.card n : ℝ) + 1) * (61 / 20) :=
    mul_le_mul_of_nonneg_left Real.log_twentyOne_le_sixtyOne_div_twenty (by positivity)
  refine measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_haarFrame hQ hkm hA
    y hx₀ (by norm_num : (0 : ℝ) < 1 / 2) le_rfl hδ ?_
    (Real.mul_pow_le_of_mul_log_le hτ hτ1 (by nlinarith))
  refine (jlDim_le (by norm_num) (by positivity)
    ((div_le_self hδ.le h21).trans (by linarith))).trans (le_trans ?_ hk)
  rw [hl, show (4 * (1 / 2) / 5 : ℝ) ^ 2 = 4 / 25 by norm_num, div_le_iff₀ (by norm_num)]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card n)]

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
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have hM : (0 : ℝ) < Fintype.card m := hK.trans_le (Nat.cast_le.2 hkm)
  let η := √(ε / (4 * ((A.rank : ℝ) + 1)))
  have hη : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hη1 : η ≤ 1 := by
    refine Real.sqrt_le_one.2 ((div_le_one (by positivity)).2 ?_)
    linarith [Nat.cast_nonneg (α := ℝ) A.rank]
  have hOSI := isObliviousSubspaceInjection_of_hasLaw_haarFrame_of_jlDim_le (d := A.rank) hQ hkm
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) (half_pos hδ)
    (by rwa [show (4 * (1 / 2) / 5 : ℝ) = 2 / 5 by norm_num])
  exact ((hasJLMoment_of_hasLaw_haarFrame_of_jlMomentDim_le hQ hkm hη hη1 (half_pos hδ) hk'
    ).measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_one_add_mul_le
    (hOSI.hasSubspaceInjection le_rfl)
    (continuous_id.matrix_conjTranspose.measurable.comp_aemeasurable hQ.aemeasurable)
    (Real.sqrt_pos.2 (by positivity)).ne' (by norm_num) hε (le_max_left _ _) (by positivity)
    B).trans (by linarith)

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
  refine ⟨3072, 1, by norm_num, one_pos, ?_⟩
  intro Ω k m n r _ _ _ _ _ _ _ _ μ Q A B ε δ hQ hkm hε hε1 hδ hδ2 hk
  have h2 := Real.log_two_le_log_one_div hδ hδ2
  have hl2 := Real.log_two_gt_d9
  have hlh : Real.log (1 / (δ / 2)) = Real.log 2 + Real.log (1 / δ) := by
    rw [show 1 / (δ / 2) = 2 * (1 / δ) by field_simp, Real.log_mul (by norm_num) (by positivity)]
  have hr : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
  have hrL : (0 : ℝ) ≤ ((A.rank : ℝ) + 1) * Real.log (1 / δ) := by
    have : 0 ≤ Real.log (1 / δ) := by linarith
    positivity
  have hε' : ((A.rank : ℝ) + 1) * Real.log (1 / δ) ≤
      ((A.rank : ℝ) + 1) * Real.log (1 / δ) / ε := le_div_self hrL hε hε1
  have h21 : (1 : ℝ) ≤ 21 ^ A.rank := one_le_pow₀ (by norm_num)
  have hl : Real.log (2 / (δ / 2 / 21 ^ A.rank)) =
      Real.log 2 + Real.log 2 + A.rank * Real.log 21 + Real.log (1 / δ) := by
    rw [show 2 / (δ / 2 / 21 ^ A.rank) = 2 * 2 * 21 ^ A.rank * (1 / δ) by field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hd21 : (A.rank : ℝ) * Real.log 21 ≤ A.rank * (61 / 20) :=
    mul_le_mul_of_nonneg_left Real.log_twentyOne_le_sixtyOne_div_twenty hr
  refine measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_haarFrame hQ hkm A B hε
    (by linarith) hδ ?_ ?_
  · refine (jlDim_le (by norm_num) (by positivity)
      ((div_le_self (by positivity) h21).trans (by linarith))).trans (le_trans ?_ hk)
    rw [hl, show ((2 : ℝ) / 5) ^ 2 = 4 / 25 by norm_num, div_le_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (A.rank : ℝ) + 1)]
  · refine (jlMomentDim_le (half_pos hδ) (by linarith)).trans (le_trans ?_ hk)
    rw [Real.sq_sqrt (by positivity), hlh]
    rw [show 384 * (Real.log 2 + Real.log (1 / δ)) / (ε / (4 * ((A.rank : ℝ) + 1))) =
      1536 * (((A.rank : ℝ) + 1) * (Real.log 2 + Real.log (1 / δ))) / ε by field_simp; ring,
      mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hε.le
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (A.rank : ℝ) + 1)]

end NLAlib
