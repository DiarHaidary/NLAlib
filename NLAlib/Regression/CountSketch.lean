/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Regression.Oblivious
public import NLAlib.Sketching.Sparse.CountSketchEmbedding

/-!
# Sketch-and-solve with a CountSketch

A CountSketch gives relative squared Frobenius residual error with failure probability $\delta$
at $O(((r+1)^2+(r+1)/\varepsilon)/\delta)$ rows, where $r=\operatorname{rank}\mathbf{A}$.
The statement works over any `RCLike` field and for a matrix right-hand side. It combines a
constant subspace injection with CountSketch's own approximate-multiplication tail through
`NLAlib.Regression.Oblivious`, preserving complex support. The sketch is unscaled, with one
random sign in each column. Design: `docs/design/Regression-Rates.md`.

## Main results

* `NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_countSketch`:
  explicit sufficient sizes for relative residual error.
* `NLAlib.exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_countSketch`:
  the asymptotic form, including rank zero.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {m n r p : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype p]
  [DecidableEq m] [DecidableEq p] {S : Ω → Matrix p m 𝕜}

/-- **CountSketch regression, relative residual with high probability**: for a CountSketch
$\mathbf{S}$ with $p$ rows, $r=\operatorname{rank}\mathbf{A}$ and $\varepsilon,\delta>0$,
if <!-- value countSketchEmbeddingDim r (1/2) (\delta/2) -->
$$p\ge\frac{r^2+r}{(\delta/2)(1/2)^2}$$
and $p\ge16(r+1)/(\varepsilon\delta)$, then
$$\mathbb{P}\bigl[(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2<\|\mathbf{B}-\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{S},
\mathbf{B})\|_{\mathsf{F}}^2\bigr]\le\delta\,.$$
Over any `RCLike` field, for any rank of $\mathbf{A}$ and a matrix right-hand side. The first
size is `NLAlib.countSketchEmbeddingDim A.rank (1 / 2) (δ / 2)`; the sketch is unscaled, with one
sign per column. [Woodruff2014, proof of Theorem 23]; there real vector regression and constant
success probability, here squared matrix residuals with a separate injection and multiplication
budget, and complex support from the direct CountSketch moment identity.
Asymptotic form:
`NLAlib.exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_countSketch`.
Result: sketch-and-solve-ls -/
theorem measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_countSketch
    (hS : HasLaw S (countSketch p m) μ) (A : Matrix m n 𝕜) (B : Matrix m r 𝕜)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hp : countSketchEmbeddingDim A.rank (1 / 2) (δ / 2) ≤ Fintype.card p)
    (hp' : 16 * ((A.rank : ℝ) + 1) ≤ ε * δ * Fintype.card p) :
    μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
      frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2} ≤ δ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  have hp0 : (0 : ℝ) < Fintype.card p := pos_of_mul_pos_right
    (lt_of_lt_of_le (by positivity) hp') (mul_nonneg hε.le hδ.le)
  have : Nonempty p := Fintype.card_pos_iff.1 (by exact_mod_cast hp0)
  let η := √(ε / (4 * ((A.rank : ℝ) + 1)))
  let C := (1 - rangeProjector A) * B
  have hη : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hsq : η ^ 2 = ε / (4 * ((A.rank : ℝ) + 1)) := Real.sq_sqrt (by positivity)
  have hfail : 2 / (Fintype.card p * η ^ 2) ≤ δ / 2 := by
    rw [hsq]
    have e : 2 / (Fintype.card p * (ε / (4 * ((A.rank : ℝ) + 1)))) =
        8 * ((A.rank : ℝ) + 1) / (Fintype.card p * ε) := by field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  have hPC : rangeProjector A * C = 0 := by
    dsimp [C]
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, rangeProjector_mul_rangeProjector,
      sub_self, Matrix.zero_mul]
  have hAMM : μ.real {ω | (1 / 2 : ℝ) * √ε * frobNorm C <
      frobNorm (rangeProjector A * (S ω)ᴴ * S ω * C)} ≤ 2 / (Fintype.card p * η ^ 2) := by
    by_cases hzero : rangeProjector A = 0 ∨ C = 0
    · have hz (ω) : rangeProjector A * (S ω)ᴴ * S ω * C = 0 := by
        rcases hzero with hP | hC
        · rw [hP, Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]
        · rw [hC, Matrix.mul_zero]
      refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) (by positivity)
      refine measure_mono_null (fun ω hω => ?_) measure_empty
      have hω' : (1 / 2 : ℝ) * √ε * frobNorm C <
          frobNorm (rangeProjector A * (S ω)ᴴ * S ω * C) := hω
      rw [hz, frobNorm_zero] at hω'
      exact not_lt_of_ge (by positivity) hω'
    rw [not_or] at hzero
    refine (measureReal_mono fun ω hω => ?_).trans
      (measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_countSketch hS hη hzero.1
        hzero.2)
    change η * frobNorm (rangeProjector A) * frobNorm C ≤
      frobNorm ((rangeProjector A)ᴴ * (S ω)ᴴ * S ω * C - (rangeProjector A)ᴴ * C)
    rw [conjTranspose_rangeProjector, hPC, sub_zero]
    have hth : η * frobNorm (rangeProjector A) ≤ (1 / 2 : ℝ) * √ε := by
      apply le_of_sq_le_sq ?_ (by positivity)
      rw [mul_pow, hsq, frobNorm_rangeProjector_sq, mul_pow, Real.sq_sqrt hε.le,
        div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    exact (mul_le_mul_of_nonneg_right hth (frobNorm_nonneg _)).trans hω.le
  have hOSI := isObliviousSubspaceInjection_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le
    hS A.rank (by norm_num) (half_pos hδ) hp
  have h := (hOSI.hasSubspaceInjection (U := A) le_rfl
    ).measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_one_add_mul_le
      (by norm_num) hε.le B (by simpa only [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num] using hAMM)
  exact h.trans (by linarith)

/-- **CountSketch regression, asymptotic relative residual with high probability**:
$O(((r+1)^2+(r+1)/\varepsilon)/\delta)$ rows suffice, where $r=\operatorname{rank}\mathbf{A}$:
there are absolute $C,\varepsilon_0>0$ such that a CountSketch with
$p\ge C((r+1)^2+(r+1)/\varepsilon)/\delta$, $0<\varepsilon\le\varepsilon_0$ and $\delta>0$
satisfies
$$\mathbb{P}\bigl[(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2<\|\mathbf{B}-\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{S},
\mathbf{B})\|_{\mathsf{F}}^2\bigr]\le\delta\,.$$
Over any `RCLike` field; rank zero and matrix right-hand sides are included. All constants precede
dimensions and data. Proved from
`NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_countSketch` with
$C=16$, $\varepsilon_0=1$. [Woodruff2014, proof of Theorem 23]; here explicit failure dependence,
squared matrix residuals, complex support and separate injection/multiplication sample budgets.
Asymptotic: NLAlib.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_countSketch
Result: sketch-and-solve-ls -/
theorem exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_countSketch :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ {Ω 𝕜 m n r p : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype m]
        [Fintype n] [Fintype r] [Fintype p] [DecidableEq m] [DecidableEq p]
        (μ : Measure Ω) (S : Ω → Matrix p m 𝕜) (A : Matrix m n 𝕜)
        (B : Matrix m r 𝕜) (ε δ : ℝ),
        HasLaw S (countSketch p m) μ → 0 < ε → ε ≤ ε₀ → 0 < δ →
        C * ((((A.rank : ℝ) + 1) ^ 2 + ((A.rank : ℝ) + 1) / ε) / δ) ≤
          Fintype.card p →
        μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
          frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2} ≤ δ := by
  refine ⟨16, 1, by norm_num, one_pos, ?_⟩
  intro Ω 𝕜 m n r p _ _ _ _ _ _ _ _ μ S A B ε δ hS hε _ hδ hp
  have hsize : 16 * (((A.rank : ℝ) + 1) ^ 2 + ((A.rank : ℝ) + 1) / ε) ≤
      (Fintype.card p : ℝ) * δ := by
    rwa [← mul_div_assoc, div_le_iff₀ hδ] at hp
  refine measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_countSketch
    hS A B hε hδ ?_ ?_
  · have e : countSketchEmbeddingDim A.rank (1 / 2) (δ / 2) =
        8 * ((A.rank : ℝ) ^ 2 + A.rank) / δ := by
      rw [countSketchEmbeddingDim_def]
      field_simp
      ring
    rw [e, div_le_iff₀ hδ]
    have hterm : 0 ≤ ((A.rank : ℝ) + 1) / ε := by positivity
    nlinarith [Nat.cast_nonneg (α := ℝ) A.rank]
  · have hterm : 16 * (((A.rank : ℝ) + 1) / ε) ≤ (Fintype.card p : ℝ) * δ := by
      nlinarith [sq_nonneg ((A.rank : ℝ) + 1)]
    rw [← mul_div_assoc, div_le_iff₀ hε] at hterm
    nlinarith

end NLAlib
