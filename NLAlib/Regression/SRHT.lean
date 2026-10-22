/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Basic
public import NLAlib.Regression.Oblivious
public import NLAlib.Regression.SketchAndPrecondition
public import NLAlib.Sketching.Structured.SRHTMultiplication

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

Sketch-and-solve with a real SRHT reaches relative squared Frobenius residual error with failure
probability $\delta$ at $O(\beta(r + \log(\lvert m\rvert/\delta))\log(r/\delta) +
\beta^2(r + 1)/(\varepsilon\delta))$ rows, $r = \operatorname{rank}\mathbf{A}$: the SRHT OSI at
constant $1/2$ and its JL moment at $p = 2$ (`NLAlib.hasJLMoment_of_hasLaw_srht`) through
`NLAlib.HasJLMoment.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le`. Design:
`docs/design/Sketching-Moments.md` §3.4.

## Main results

* `NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_srht`: explicit
  sizes.
* [The sketch-and-solve start](https://nla-lib.org/explore/#d/NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_pinv_mulVec_sq_gt_le_of_hasLaw_srht):
  the same from $(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}$.
* [Asymptotic form](https://nla-lib.org/explore/#d/NLAlib.exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_srht):
  the asymptotic form.
* `NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_srht`: SRHT
  sketch-and-solve to relative error, and its asymptotic form
  `NLAlib.exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_srht`.
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
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  exact ((isObliviousSubspaceEmbedding_of_hasLaw_srht_of_samplingEmbeddingDim_le hF hS _ hε
    (by linarith) hδ hk).hasSubspaceEmbedding
      (U := Matrix.fromCols A (Matrix.replicateCol Unit y)) ((Matrix.rank_le_card_width _).trans_eq
      (by rw [Fintype.card_sum, Fintype.card_unit]))
    ).measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_one_sub_one_add hε hε1 hA hx₀ hq

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
  exact measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_srht hF hS hA y
    (ae_of_all _ fun ω => isLeastSquaresSolution_pinv_mulVec _ _) hε hε1 hδ hk hq

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
  refine ⟨288, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro Ω 𝕜 k m n _ _ _ _ _ _ _ μ S F β A y x₀ τ δ q hF hS hA hx₀ hτ hτ1 hδ hδ2 hk hq
  rcases isEmpty_or_nonempty m with hm | hm
  · refine (measureReal_mono (s₂ := ∅) (fun ω hω => ?_) (by simp)).trans
      (by rw [measureReal_empty]; exact hδ.le)
    simp only [Set.mem_ofPred_eq, Subsingleton.elim ((1 - rangeProjector A) *ᵥ y) 0,
      Subsingleton.elim (y - A *ᵥ sketchAndPrecondition A (S ω) y (x₀ ω) q) 0, WithLp.toLp_zero,
      norm_zero] at hω
    simp at hω
  have hτl : 0 ≤ Real.log (1 / τ) := Real.log_nonneg (by rw [le_div_iff₀ hτ]; linarith)
  refine measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_srht hF hS hA y hx₀
    (by norm_num : (0 : ℝ) < 1 / 2) le_rfl hδ ?_
    (Real.mul_pow_le_of_mul_log_le hτ hτ1 (by nlinarith))
  refine (samplingEmbeddingDim_le _ _ _ _).trans (le_trans ?_ hk)
  have hβ : 1 ≤ β := hF.one_le
  have hd1 : (1 : ℝ) ≤ (Fintype.card n : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card n)]
  have hN : (1 : ℝ) ≤ Fintype.card m := Nat.one_le_cast.2 Fintype.card_pos
  have h2N : Real.log 2 ≤ Real.log (Fintype.card m / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; nlinarith)
  have h2d : Real.log 2 ≤ Real.log (((Fintype.card n : ℝ) + 1) / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; nlinarith)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlN : Real.log (Fintype.card m / (δ / 2)) = Real.log 2 + Real.log (Fintype.card m / δ) := by
    rw [show (Fintype.card m : ℝ) / (δ / 2) = 2 * (Fintype.card m / δ) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hR : srhtRowBound (Fintype.card m) (Fintype.card n + 1) (δ / 2) ≤
      8 * ((Fintype.card n : ℝ) + 1 + Real.log (Fintype.card m / δ)) := by
    have h := srhtRowBound_le (Fintype.card m) (Fintype.card n + 1) (δ / 2)
    have ha := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (Fintype.card n + 1))
    have hb := Real.sq_sqrt (by linarith : 0 ≤ 2 * Real.log (Fintype.card m / (δ / 2)))
    push_cast at h ha
    nlinarith [sq_nonneg (√((Fintype.card n : ℝ) + 1) -
      √(2 * Real.log (Fintype.card m / (δ / 2))))]
  have hl : Real.log (2 * ((Fintype.card n : ℝ) + 1) / (δ / 2)) =
      2 * Real.log 2 + Real.log (((Fintype.card n : ℝ) + 1) / δ) := by
    rw [show 2 * ((Fintype.card n : ℝ) + 1) / (δ / 2) = 2 * 2 * (((Fintype.card n : ℝ) + 1) / δ) by
      ring, Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by norm_num)]
    ring
  push_cast
  rw [hl]
  have hB : 0 ≤ β * (8 * ((Fintype.card n : ℝ) + 1 + Real.log (Fintype.card m / δ))) :=
    mul_nonneg (by linarith) (by linarith)
  calc 3 * (β * srhtRowBound (Fintype.card m) (Fintype.card n + 1) (δ / 2)) *
        (2 * Real.log 2 + Real.log (((Fintype.card n : ℝ) + 1) / δ)) / (1 / 2) ^ 2
      ≤ 3 * (β * (8 * ((Fintype.card n : ℝ) + 1 + Real.log (Fintype.card m / δ)))) *
        (3 * Real.log (((Fintype.card n : ℝ) + 1) / δ)) / (1 / 2) ^ 2 := by
        gcongr ?_ / _
        exact mul_le_mul (by nlinarith [mul_le_mul_of_nonneg_left hR (by linarith : (0 : ℝ) ≤ β)])
          (by linarith) (by linarith) (by positivity)
    _ = _ := by ring

/-! ### Sketch-and-solve -/

omit [DecidableEq n] in
/-- **SRHT sketch-and-solve, relative residual with high probability**: for a real bounded
orthonormal $\mathbf{F} \in \mathbb{R}^{m \times m}$ with constant $\beta$, the SRHT $\mathbf{S}$
built from it (independent random signs and an independent uniform choice of $\lvert k\rvert$
distinct rows), $k$ nonempty, $\lvert k\rvert \le \lvert m\rvert$,
$r = \operatorname{rank}\mathbf{A}$, $\varepsilon, \delta > 0$, at
least <!-- value samplingInjectionDim r L (1/2) (\delta/4) -->
$$\lvert k\rvert \ge \frac{2L\log(r/(\delta/4))}{(1/2)^2}$$
rows, where the flattened coherence <!-- value srhtRowBound {\lvert m \rvert} r (\delta/4) -->
$$L = \beta\,\bigl(r + 2\sqrt{r \log(\lvert m \rvert/(\delta/4))} +
2 \log(\lvert m \rvert/(\delta/4))\bigr)$$
is $\beta$ times `NLAlib.srhtRowBound (card m) A.rank (δ / 4)` (the size is
`NLAlib.samplingInjectionDim A.rank L (1 / 2) (δ / 4)`, the OSI at constant $1/2$ and failure
$\delta/2$), and $\lvert k\rvert \ge 8(3\beta^2 - 1)(r + 1)/(\varepsilon\delta)$,
$$\mathbb{P}\bigl[(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2<\|\mathbf{B}-\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{S},
\mathbf{B})\|_{\mathsf{F}}^2\bigr]\le\delta\,.$$
The JL moment `NLAlib.hasJLMoment_of_hasLaw_srht` at $\sqrt{\varepsilon/(4(r+1))}$ with failure
$\delta/2$ and `NLAlib.HasJLMoment.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le`.
[Woodruff2014, Theorem 23], there for sparse embeddings; the injection-plus-multiplication route.
Asymptotic form:
`NLAlib.exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_srht`.
Result: sketch-and-solve-ls -/
theorem measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_srht [Nonempty k]
    {S : Ω → Matrix k m ℝ} {F : Matrix m m ℝ} (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srht k F) μ) (hkm : Fintype.card k ≤ Fintype.card m) (A : Matrix m n ℝ)
    {r : Type*} [Fintype r] (B : Matrix m r ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hk : samplingInjectionDim A.rank (β * srhtRowBound (Fintype.card m) A.rank (δ / 4)) (1 / 2)
      (δ / 4) ≤ Fintype.card k)
    (hk' : 8 * (3 * β ^ 2 - 1) * ((A.rank : ℝ) + 1) ≤ ε * δ * Fintype.card k) :
    μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
      frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2} ≤ δ := by
  sorry

/-- **SRHT sketch-and-solve, asymptotic relative residual with high probability**:
$O(\beta(r + \log(\lvert m\rvert/\delta))\log(r/\delta) + \beta^2(r+1)/(\varepsilon\delta))$ rows
suffice, with $r = \operatorname{rank}\mathbf{A}$: there are absolute $C, \varepsilon_0 > 0$ such
that for a real bounded orthonormal $\mathbf{F}$ with constant $\beta$, its SRHT $\mathbf{S}$ with
$k$ nonempty and $\lvert k\rvert \le \lvert m\rvert$ rows above that threshold times $C$,
$0 < \varepsilon \le \varepsilon_0$ and $0 < \delta \le 1/2$,
$$\mathbb{P}\bigl[(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2<\|\mathbf{B}-\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{S},
\mathbf{B})\|_{\mathsf{F}}^2\bigr]\le\delta\,.$$
The constants come before every dimension and before $\beta$. Proved from
`NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_srht` with
$\varepsilon_0 = 1$. [Woodruff2014, Theorem 23].
Asymptotic: NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_srht
Result: sketch-and-solve-ls -/
theorem exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_srht :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ {Ω k m n r : Type} [MeasurableSpace Ω] [Fintype k] [Fintype m] [Fintype n]
        [Fintype r] [DecidableEq m] [Nonempty k] (μ : Measure Ω) (S : Ω → Matrix k m ℝ)
        (F : Matrix m m ℝ) (β : ℝ) (A : Matrix m n ℝ) (B : Matrix m r ℝ) (ε δ : ℝ),
        IsBoundedOrthonormal F β → HasLaw S (srht k F) μ → Fintype.card k ≤ Fintype.card m →
        0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
        C * (β * (A.rank + Real.log (Fintype.card m / δ)) * Real.log (A.rank / δ) +
          β ^ 2 * ((A.rank : ℝ) + 1) / (ε * δ)) ≤ Fintype.card k →
        μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
          frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2} ≤ δ := by
  sorry

end NLAlib
