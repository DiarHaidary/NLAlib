/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Basic
public import NLAlib.Regression.Oblivious
public import NLAlib.Regression.SketchAndPrecondition
public import NLAlib.Sketching.Gaussian.Gaussian

/-!
# Regression with a Gaussian sketch

A standard Gaussian sketch gives relative squared Frobenius residual error with failure
probability $\delta$ at $O((r+1)/(\varepsilon\delta))$ rows through the second JL moment, and at
$O((r+1)\log(1/\delta)/\varepsilon)$ rows through the JL moment at $p = \log(1/\delta)$, where
$r=\operatorname{rank}\mathbf{A}$. The sketch is unnormalized: scaling cancels in
`NLAlib.sketchAndSolve`. The proof combines a constant subspace injection with the Gaussian's
second JL moment through `NLAlib.Regression.Oblivious`; it makes no optimal logarithmic-in-failure
claim. Expected-error bounds are in `NLAlib.Regression.SketchAndSolve`.

Sketch-and-precondition with the normalised Gaussian sketch $\lvert p\rvert^{-1/2}\mathbf{G}$
reaches relative squared residual $1 + \tau$ with $O(\lvert n\rvert + 1 + \log(1/\delta))$ rows
and $O(\log(1/\tau))$ iterations, from the sketch-and-solve start.

## Main results

* `NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix`:
  explicit sufficient sizes for relative residual error, and its $\log(1/\delta)$ twin
  [`…_of_jlMomentDim_le`](https://nla-lib.org/explore/#d/NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix_of_jlMomentDim_le).
* [Asymptotic form](https://nla-lib.org/explore/#d/NLAlib.exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix):
  the asymptotic form, including rank zero.
* `NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_gaussianMatrix`:
  Gaussian sketch-and-precondition, explicit sizes.
* [The sketch-and-solve start](https://nla-lib.org/explore/#d/NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_pinv_mulVec_sq_gt_le_of_hasLaw_gaussianMatrix):
  the same from $(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}$.
* [Asymptotic form](https://nla-lib.org/explore/#d/NLAlib.exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_gaussianMatrix):
  the asymptotic form of Gaussian sketch-and-precondition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {m n r p : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype p] [DecidableEq m]
  {G : Ω → Matrix p m ℝ}

/-- **Gaussian sketch-and-solve, relative residual with high probability**: for a standard
Gaussian $p\times m$ sketch $\mathbf{G}$, $r=\operatorname{rank}\mathbf{A}$ and
$\varepsilon,\delta>0$, if <!-- value gaussianInjectionDim r (1/2) (\delta/2) -->
$$p\ge\frac{4(\sqrt{r}+\sqrt{2\log(1/(\delta/2))})^2}{(1/2)^2}$$
and $p\ge16(r+1)/(\varepsilon\delta)$, then
$$\mathbb{P}\bigl[(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2<\|\mathbf{B}-\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{G},
\mathbf{B})\|_{\mathsf{F}}^2\bigr]\le\delta\,.$$
No full-rank assumption on $\mathbf{A}$ is needed; $\mathbf{B}$ may have several columns.
The first size is `NLAlib.gaussianInjectionDim A.rank (1 / 2) (δ / 2)`.
[Woodruff2014, proof of Theorem 23]; the injection-plus-multiplication route there, here with a
Gaussian sketch's second JL moment and a squared matrix residual. This is a sufficient
second-moment rate, rather than an optimal Gaussian failure dependence. Incomparable with its
$\log(1/\delta)$ twin
`measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix_of_jlMomentDim_le`
(rule 4): this one needs fewer rows at constant $\delta$, the twin for small $\delta$; the
asymptotic form
`exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix` is
proved from the twin.
Result: sketch-and-solve-ls -/
theorem measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix
    (hG : HasLaw G (gaussianMatrix p m) μ) (A : Matrix m n ℝ) (B : Matrix m r ℝ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hp : gaussianInjectionDim A.rank (1 / 2) (δ / 2) ≤ Fintype.card p)
    (hp' : 16 * ((A.rank : ℝ) + 1) ≤ ε * δ * Fintype.card p) :
    μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
      frobNorm (B - A * sketchAndSolve A (G ω) B) ^ 2} ≤ δ := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact measureReal_le_one.trans hδ1
  have hp0 : (0 : ℝ) < Fintype.card p := pos_of_mul_pos_right
    (lt_of_lt_of_le (by positivity) hp') (mul_nonneg hε.le hδ.le)
  have : Nonempty p := Fintype.card_pos_iff.1 (by exact_mod_cast hp0)
  let η := √(ε / (4 * ((A.rank : ℝ) + 1)))
  have hη : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hsq : η ^ 2 = ε / (4 * ((A.rank : ℝ) + 1)) := Real.sq_sqrt (by positivity)
  have hOSI := isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le
    (d := A.rank) hG (by norm_num) (by norm_num) (half_pos hδ) (by linarith) hp
  have hfail : 2 / (Fintype.card p * η ^ 2) ≤ δ / 2 := by
    rw [hsq]
    have e : 2 / (Fintype.card p * (ε / (4 * ((A.rank : ℝ) + 1)))) =
        8 * ((A.rank : ℝ) + 1) / (Fintype.card p * ε) := by field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  exact ((hasJLMoment_of_hasLaw_gaussianMatrix hG hη
    ).measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_one_add_mul_le
    (hOSI.hasSubspaceInjection le_rfl) hG.aemeasurable
    (inv_ne_zero (Real.sqrt_pos.2 hp0).ne') (by norm_num) hε (by norm_num) (by positivity)
    B).trans (by linarith)

/-- **Gaussian sketch-and-solve, relative residual with high probability**, $\log(1/\delta)$ size
form: for a standard Gaussian $p\times m$ sketch $\mathbf{G}$, $r=\operatorname{rank}\mathbf{A}$,
$0 < \varepsilon \le 4$, $\delta > 0$,
if <!-- value gaussianInjectionDim r (1/2) (\delta/2) -->
$$p\ge\frac{4(\sqrt{r}+\sqrt{2\log(1/(\delta/2))})^2}{(1/2)^2}$$
and <!-- value jlMomentDim {\sqrt{\varepsilon/(4(r + 1))}} (\delta/2) -->
$$p \ge 128\max(2, \log(1/(\delta/2)))/\sqrt{\varepsilon/(4(r + 1))}^2\,,$$
that is $p \ge 512(r + 1)\max(2, \log(2/\delta))/\varepsilon$, then
$$\mathbb{P}\bigl[(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2<\|\mathbf{B}-\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{G},
\mathbf{B})\|_{\mathsf{F}}^2\bigr]\le\delta\,.$$
The sizes are `NLAlib.gaussianInjectionDim A.rank (1 / 2) (δ / 2)` and
`NLAlib.jlMomentDim (√(ε / (4 * (A.rank + 1)))) (δ / 2)`: the JL moment at
$p = \max(2, \log(2/\delta))$ (`NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le`)
in place of the second moment, for which the JL budget $\sqrt{\varepsilon/(4(r+1))}$ must be at
most $1$, hence $\varepsilon \le 4$. Incomparable with
`NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix` (rule 4).
[Woodruff2014, proof of Theorem 23]; the injection-plus-multiplication route there, here with the
Gaussian JL moment at $p = \log(1/\delta)$. The product $(r + 1)\log(1/\delta)$ is what this route
gives; the optimal Gaussian rate needs more than JL moments. Asymptotic form:
`exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix`.
Result: sketch-and-solve-ls -/
theorem
    measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix_of_jlMomentDim_le
    (hG : HasLaw G (gaussianMatrix p m) μ) (A : Matrix m n ℝ) (B : Matrix m r ℝ)
    {ε δ : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 4) (hδ : 0 < δ)
    (hp : gaussianInjectionDim A.rank (1 / 2) (δ / 2) ≤ Fintype.card p)
    (hp' : jlMomentDim (√(ε / (4 * ((A.rank : ℝ) + 1)))) (δ / 2) ≤ Fintype.card p) :
    μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
      frobNorm (B - A * sketchAndSolve A (G ω) B) ^ 2} ≤ δ := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact measureReal_le_one.trans hδ1
  have hp0 : (0 : ℝ) < Fintype.card p :=
    (gaussianInjectionDim_pos A.rank (by norm_num) (half_pos hδ) (by linarith)).trans_le hp
  let η := √(ε / (4 * ((A.rank : ℝ) + 1)))
  have hη : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hη1 : η ≤ 1 := by
    refine Real.sqrt_le_one.2 ((div_le_one (by positivity)).2 ?_)
    linarith [Nat.cast_nonneg (α := ℝ) A.rank]
  have hOSI := isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le
    (d := A.rank) hG (by norm_num) (by norm_num) (half_pos hδ) (by linarith) hp
  exact ((hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le hG hη hη1 (half_pos hδ) hp'
    ).measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_one_add_mul_le
    (hOSI.hasSubspaceInjection le_rfl) hG.aemeasurable
    (inv_ne_zero (Real.sqrt_pos.2 hp0).ne') (by norm_num) hε (le_max_left _ _) (by positivity)
    B).trans (by linarith)

-- The explicit theorem's full name in the `Asymptotic:` tag exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Gaussian sketch-and-solve, asymptotic relative residual with high probability**:
$O((r+1)\log(1/\delta)/\varepsilon)$ rows suffice, with $r=\operatorname{rank}\mathbf{A}$:
there are absolute $C,\varepsilon_0>0$ such that a standard Gaussian $p\times m$ sketch with
$p\ge C(r+1)\log(1/\delta)/\varepsilon$, $0<\varepsilon\le\varepsilon_0$ and
$0<\delta\le1/2$ satisfies
$$\mathbb{P}\bigl[(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2<\|\mathbf{B}-\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{G},
\mathbf{B})\|_{\mathsf{F}}^2\bigr]\le\delta\,.$$
Rank zero and matrix right-hand sides are included; all constants precede dimensions and data.
Proved from
`measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix_of_jlMomentDim_le`
with $\varepsilon_0 = 1$. [Woodruff2014, proof of Theorem 23]; here the Gaussian JL-moment route,
without a claim of optimal failure dependence.
Asymptotic:
NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix_of_jlMomentDim_le
Result: sketch-and-solve-ls -/
theorem
    exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ {Ω m n r p : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
        [Fintype r] [Fintype p] [DecidableEq m] (μ : Measure Ω) (G : Ω → Matrix p m ℝ)
        (A : Matrix m n ℝ) (B : Matrix m r ℝ) (ε δ : ℝ),
        HasLaw G (gaussianMatrix p m) μ → 0 < ε → ε ≤ ε₀ →
        0 < δ → δ ≤ 1 / 2 →
        C * (((A.rank : ℝ) + 1) * Real.log (1 / δ) / ε) ≤ Fintype.card p →
        μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
          frobNorm (B - A * sketchAndSolve A (G ω) B) ^ 2} ≤ δ := by
  refine ⟨3072, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n r p _ _ _ _ _ _ μ G A B ε δ hG hε hε1 hδ hδ2 hp
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
  refine
    measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix_of_jlMomentDim_le
    hG A B hε (by linarith) hδ ?_ ?_
  · refine (gaussianInjectionDim_le _ _ (half_pos hδ) (by linarith)).trans (le_trans ?_ hp)
    rw [hlh, div_le_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (A.rank : ℝ) + 1)]
  · refine (jlMomentDim_le (half_pos hδ) (by linarith)).trans (le_trans ?_ hp)
    rw [Real.sq_sqrt (by positivity), hlh]
    rw [show 384 * (Real.log 2 + Real.log (1 / δ)) / (ε / (4 * ((A.rank : ℝ) + 1))) =
      1536 * (((A.rank : ℝ) + 1) * (Real.log 2 + Real.log (1 / δ))) / ε by field_simp; ring,
      mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hε.le
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (A.rank : ℝ) + 1)]

/-! ### Gaussian sketch-and-precondition -/

section SketchAndPrecondition

variable [DecidableEq n]

-- A backticked declaration name in the docstring exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Gaussian sketch-and-precondition**: for a standard Gaussian $\mathbf{G} \in \mathbb{R}^{p
\times m}$ (independent standard normal entries), the sketch
$\mathbf{S} = \lvert p\rvert^{-1/2}\mathbf{G}$, $\mathbf{A}$ of full column rank, $\mathbf{x}_0$
almost surely a minimizer of $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$,
$0 < \varepsilon \le 1/2$, $\delta > 0$,
at least <!-- value gaussianEmbeddingDim {\lvert n \rvert + 1} \varepsilon \delta -->
$9 (\sqrt{\lvert n \rvert + 1} + \sqrt{2 \log(2/\delta)})^2/\varepsilon^2$ rows
(`gaussianEmbeddingDim (card n + 1) ε δ`) and $16\varepsilon^{2q+1} \le \tau$,
$$\mathbb{P}\Bigl[(1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 <
\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
\mathbf{x}_0, q)\|^2\Bigr] \le \delta\,.$$
Squared residuals, and $\varepsilon$ is the squared-norm distortion of the embedding of
$\operatorname{range}[\mathbf{A}\ \mathbf{y}]$, which trades sketch size against iterations.
[MartinssonTropp2020, §10.5], there unsquared, after $j \sim \log(1/\varepsilon)$ steps and with
no constants.
Asymptotic form:
`NLAlib.exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_gaussianMatrix`.
Result: sketch-and-precondition-ls -/
theorem measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_gaussianMatrix
    (hG : HasLaw G (gaussianMatrix p m) μ) {A : Matrix m n ℝ} (hA : Function.Injective A.mulVec)
    (y : m → ℝ) {x₀ : Ω → n → ℝ}
    (hx₀ : ∀ᵐ ω ∂μ, IsLeastSquaresSolution ((√(Fintype.card p : ℝ))⁻¹ • G ω * A)
      ((√(Fintype.card p : ℝ))⁻¹ • G ω *ᵥ y) (x₀ ω))
    {ε δ τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ : 0 < δ)
    (hp : gaussianEmbeddingDim (Fintype.card n + 1) ε δ ≤ Fintype.card p)
    {q : ℕ} (hq : 16 * ε ^ (2 * q + 1) ≤ τ) :
    μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A ((√(Fintype.card p : ℝ))⁻¹ • G ω) y
        (x₀ ω) q)‖ ^ 2} ≤ δ := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hE := (isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix_of_gaussianEmbeddingDim_le hG hε
    (by linarith) hδ hp).hasSubspaceEmbedding
      (U := Matrix.fromCols A (Matrix.replicateCol Unit y)) ((Matrix.rank_le_card_width _).trans_eq
      (by rw [Fintype.card_sum, Fintype.card_unit]))
  exact hE.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_one_sub_one_add hε hε1 hA
    (hx₀.mono fun ω h => by rwa [Matrix.smul_mulVec]) hq

/-- **Gaussian sketch-and-precondition from the sketch-and-solve solution**, the algorithm as
run: for a standard Gaussian $\mathbf{G} \in \mathbb{R}^{p \times m}$ (independent standard
normal entries), the sketch $\mathbf{S} = \lvert p\rvert^{-1/2}\mathbf{G}$, $\mathbf{A}$ of full
column rank, the start $\mathbf{x}_0 = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}$,
$0 < \varepsilon \le 1/2$, $\delta > 0$,
at least <!-- value gaussianEmbeddingDim {\lvert n \rvert + 1} \varepsilon \delta -->
$9 (\sqrt{\lvert n \rvert + 1} + \sqrt{2 \log(2/\delta)})^2/\varepsilon^2$ rows
(`gaussianEmbeddingDim (card n + 1) ε δ`) and $16\varepsilon^{2q+1} \le \tau$,
$$\mathbb{P}\Bigl[(1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 <
\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}, q)\|^2\Bigr] \le \delta\,.$$
Squared residuals. It fixes the start, not the sample size, so it has no asymptotic form.
[Epperly2024, Algorithm 1], there with the QR form of the start. -/
theorem
    measureReal_norm_sub_mulVec_sketchAndPrecondition_pinv_mulVec_sq_gt_le_of_hasLaw_gaussianMatrix
    (hG : HasLaw G (gaussianMatrix p m) μ) {A : Matrix m n ℝ} (hA : Function.Injective A.mulVec)
    (y : m → ℝ) {ε δ τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ : 0 < δ)
    (hp : gaussianEmbeddingDim (Fintype.card n + 1) ε δ ≤ Fintype.card p)
    {q : ℕ} (hq : 16 * ε ^ (2 * q + 1) ≤ τ) :
    μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A ((√(Fintype.card p : ℝ))⁻¹ • G ω) y
        (pinv ((√(Fintype.card p : ℝ))⁻¹ • G ω * A) *ᵥ ((√(Fintype.card p : ℝ))⁻¹ • G ω *ᵥ y))
        q)‖ ^ 2} ≤ δ := by
  exact measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_gaussianMatrix hG hA y
    (ae_of_all _ fun ω => isLeastSquaresSolution_pinv_mulVec _ _) hε hε1 hδ hp hq

end SketchAndPrecondition

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Gaussian sketch-and-precondition, asymptotic form**: $O(\lvert n\rvert + 1 + \log(1/\delta))$
rows and $O(\log(1/\tau))$ iterations suffice. There are absolute constants
$C, \varepsilon_0 > 0$ such that for a standard Gaussian $\mathbf{G} \in \mathbb{R}^{p \times m}$
(independent standard normal entries), the sketch $\mathbf{S} = \lvert p\rvert^{-1/2}\mathbf{G}$,
$\mathbf{A}$ of full column rank, $\mathbf{x}_0$ almost surely a minimizer of
$\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, $0 < \tau \le \varepsilon_0$,
$0 < \delta \le 1/2$, $\lvert p\rvert \ge C(\lvert n\rvert + 1 + \log(1/\delta))$ and
$q \ge C\log(1/\tau)$,
$$\mathbb{P}\Bigl[(1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 <
\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
\mathbf{x}_0, q)\|^2\Bigr] \le \delta\,.$$
The constants come before every dimension. Squared residuals. Proved from
`NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_gaussianMatrix` at
distortion $1/2$ with $C = 288$ and $\varepsilon_0 = 1/2$. [MartinssonTropp2020, §10.5], there
unsquared.
Asymptotic:
NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_gaussianMatrix -/
theorem
    exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω p m n : Type} [MeasurableSpace Ω] [Fintype p] [Fintype m]
      [Fintype n] [DecidableEq m] [DecidableEq n] (μ : Measure Ω) (G : Ω → Matrix p m ℝ)
      (A : Matrix m n ℝ) (y : m → ℝ) (x₀ : Ω → n → ℝ) (τ δ : ℝ) (q : ℕ),
      HasLaw G (gaussianMatrix p m) μ → Function.Injective A.mulVec →
      (∀ᵐ ω ∂μ, IsLeastSquaresSolution ((√(Fintype.card p : ℝ))⁻¹ • G ω * A)
        ((√(Fintype.card p : ℝ))⁻¹ • G ω *ᵥ y) (x₀ ω)) →
      0 < τ → τ ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (Fintype.card n + 1 + Real.log (1 / δ)) ≤ Fintype.card p →
      C * Real.log (1 / τ) ≤ q →
      μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
        ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A ((√(Fintype.card p : ℝ))⁻¹ • G ω) y
          (x₀ ω) q)‖ ^ 2} ≤ δ := by
  refine ⟨288, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro Ω p m n _ _ _ _ _ _ μ G A y x₀ τ δ q hG hA hx₀ hτ hτ1 hδ hδ2 hp hq
  have hl1 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hl2 := Real.log_two_div_le_two_mul_log_one_div hδ hδ2
  have hτl : 0 ≤ Real.log (1 / τ) := Real.log_nonneg (by rw [le_div_iff₀ hτ]; linarith)
  refine measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_gaussianMatrix hG hA y
    hx₀ (by norm_num : (0 : ℝ) < 1 / 2) le_rfl hδ ?_
    (Real.mul_pow_le_of_mul_log_le hτ hτ1 (by nlinarith))
  refine (gaussianEmbeddingDim_le _ _ hδ (by linarith)).trans (le_trans ?_ hp)
  push_cast
  rw [div_le_iff₀ (by norm_num)]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card n)]

end NLAlib
