/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Regression.Oblivious
public import NLAlib.Sketching.Gaussian.Gaussian

/-!
# Gaussian sketch-and-solve with high probability

A standard Gaussian sketch gives relative squared Frobenius residual error with failure
probability $\delta$ at $O((r+1)/(\varepsilon\delta))$ rows, where
$r=\operatorname{rank}\mathbf{A}$. The sketch is unnormalized: scaling cancels in
`NLAlib.sketchAndSolve`. The proof combines a constant subspace injection with the Gaussian's
second JL moment through `NLAlib.Regression.Oblivious`; it makes no optimal logarithmic-in-failure
claim. Expected-error bounds are in `NLAlib.Regression.SketchAndSolve`.
Design: `docs/design/Regression-Rates.md`.

## Main results

* `NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix`:
  explicit sufficient sizes for relative residual error.
* [Asymptotic form](https://nla-lib.org/explore/#d/NLAlib.exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix):
  the asymptotic form, including rank zero.
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
second-moment rate, rather than an optimal Gaussian failure dependence.
Asymptotic form:
`exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix`.
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
  have h := (hasJLMoment_of_hasLaw_gaussianMatrix hG hη
    ).measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le
    (hOSI.hasSubspaceInjection (U := A) le_rfl)
    (hG.aemeasurable.const_smul ((√(Fintype.card p : ℝ))⁻¹)) (by norm_num) hη
    (by norm_num) (by positivity) B
  have hcoef : 1 + (A.rank : ℝ) * η ^ 2 / (1 - 1 / 2) ^ 2 ≤ 1 + ε := by
    rw [add_le_add_iff_left, div_le_iff₀ (by norm_num), hsq, ← mul_div_assoc,
      div_le_iff₀ (by positivity)]
    nlinarith
  have hfail : 2 / (Fintype.card p * η ^ 2) ≤ δ / 2 := by
    rw [hsq]
    have e : 2 / (Fintype.card p * (ε / (4 * ((A.rank : ℝ) + 1)))) =
        8 * ((A.rank : ℝ) + 1) / (Fintype.card p * ε) := by field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  have hnorm : (√(Fintype.card p : ℝ))⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 hp0))
  refine (measureReal_mono fun ω hω => ?_).trans (h.trans (by linarith))
  change (1 + (A.rank : ℝ) * η ^ 2 / (1 - 1 / 2) ^ 2) *
    frobNorm ((1 - rangeProjector A) * B) ^ 2 <
      frobNorm (B - A * sketchAndSolve A ((√(Fintype.card p : ℝ))⁻¹ • G ω) B) ^ 2
  rw [sketchAndSolve_smul_sketch A (G ω) B hnorm]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)) hω

/-- **Gaussian sketch-and-solve, asymptotic relative residual with high probability**:
$O((r+1)/(\varepsilon\delta))$ rows suffice, with $r=\operatorname{rank}\mathbf{A}$:
there are absolute $C,\varepsilon_0>0$ such that a standard Gaussian $p\times m$ sketch with
$p\ge C(r+1)/(\varepsilon\delta)$, $0<\varepsilon\le\varepsilon_0$ and
$0<\delta\le1/2$ satisfies
$$\mathbb{P}\bigl[(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2<\|\mathbf{B}-\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{G},
\mathbf{B})\|_{\mathsf{F}}^2\bigr]\le\delta\,.$$
Rank zero and matrix right-hand sides are included; all constants precede dimensions and data.
Proved from `NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix`
with $C=128$, $\varepsilon_0=1$. [Woodruff2014, proof of Theorem 23]; here the Gaussian
second-moment route, without a claim of optimal failure dependence.
Asymptotic:
NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix
Result: sketch-and-solve-ls -/
theorem
    exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ {Ω m n r p : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
        [Fintype r] [Fintype p] [DecidableEq m] (μ : Measure Ω) (G : Ω → Matrix p m ℝ)
        (A : Matrix m n ℝ) (B : Matrix m r ℝ) (ε δ : ℝ),
        HasLaw G (gaussianMatrix p m) μ → 0 < ε → ε ≤ ε₀ →
        0 < δ → δ ≤ 1 / 2 →
        C * (((A.rank : ℝ) + 1) / (ε * δ)) ≤ Fintype.card p →
        μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
          frobNorm (B - A * sketchAndSolve A (G ω) B) ^ 2} ≤ δ := by
  refine ⟨128, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n r p _ _ _ _ _ _ μ G A B ε δ hG hε hε1 hδ hδ2 hp
  have hsize : 128 * ((A.rank : ℝ) + 1) ≤ (Fintype.card p : ℝ) * (ε * δ) := by
    rwa [← mul_div_assoc, div_le_iff₀ (mul_pos hε hδ)] at hp
  refine measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix
    hG A B hε hδ ?_ ?_
  · refine (gaussianInjectionDim_le A.rank (1 / 2) (half_pos hδ) (by linarith)
      ).trans ?_
    have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 / (δ / 2) by positivity)
    have hδlog : δ * Real.log (1 / (δ / 2)) ≤ 2 - δ := by
      have e : δ * (1 / (δ / 2) - 1) = 2 - δ := by field_simp
      nlinarith
    have hbound : (32 * (A.rank : ℝ) + 64 * Real.log (1 / (δ / 2))) * δ ≤
        128 * ((A.rank : ℝ) + 1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) A.rank]
    have hεbound := mul_le_mul_of_nonneg_right hε1
      (show 0 ≤ 128 * ((A.rank : ℝ) + 1) by positivity)
    have hL : 0 ≤ 32 * (A.rank : ℝ) + 64 * Real.log (1 / (δ / 2)) := by
      have : 0 ≤ Real.log (1 / (δ / 2)) :=
        Real.log_nonneg (by rw [one_le_div (half_pos hδ)]; linarith)
      positivity
    have hεδ := mul_le_mul_of_nonneg_left hε1 (mul_nonneg hL hδ.le)
    norm_num only [one_div, inv_pow, inv_div, one_pow] at *
    nlinarith
  · have hnonneg : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
    nlinarith

end NLAlib
