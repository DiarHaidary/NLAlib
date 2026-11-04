/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import NLAlib.Matrix.Perturbation.GramCutoff
public import NLAlib.RandomMatrix.Gaussian.Moments

/-!
# Gaussian integrability of cutoff Gram fields

A scalar test with positive compact support bounds the inverse on its active
region. The coordinate field, its product with the Gaussian coordinate, and its
actual derivative have integrable Frobenius majorants.

## Main results

* `NLAlib.integrable_mul_gramSoftMinGradient_single_gaussianMatrix`: the cutoff field.
* `NLAlib.integrable_apply_mul_gramSoftMinGradient_single_gaussianMatrix`: its coordinate product.
* `NLAlib.integrable_deriv_mul_gramSoftMinGradient_single_gaussianMatrix`: its derivative.
-/

@[expose] public section

open scoped Matrix ContDiff
open MeasureTheory ProbabilityTheory Set

namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private theorem measurable_gram : Measurable fun G : Matrix ι κ ℝ => G * Gᴴ :=
  measurable_id.matrix_mul (Measurable.matrix_conjTranspose (α := ℝ) measurable_id measurable_id)

private theorem measurable_inversePowerSoftMin_gram (n : ℕ) :
    Measurable fun G : Matrix ι κ ℝ => inversePowerSoftMin n (G * Gᴴ) :=
  ((measurable_gram.matrix_inv.matrix_pow n).matrix_trace).pow_const _

private theorem measurable_inversePowerSoftMinWeight {Ω : Type*} [MeasurableSpace Ω]
    {A : Ω → Matrix ι ι ℝ} (hA : Measurable A) (n : ℕ) :
    Measurable fun x => inversePowerSoftMinWeight n (A x) := by
  have hR := hA.matrix_inv
  exact ((hR.matrix_pow n).matrix_trace.pow_const _).matrix_smul (hR.matrix_pow (n + 1))

private theorem measurable_gramSoftMinGradient_single (n : ℕ) (i : ι) (j : κ) :
    Measurable fun G : Matrix ι κ ℝ => gramSoftMinGradient n 0 G i j := by
  unfold gramSoftMinGradient
  simp only [regularizedGram_zero]
  exact (Matrix.measurable_apply i j).comp
    ((measurable_inversePowerSoftMinWeight measurable_gram n).matrix_mul measurable_id
      |>.matrix_const_smul (2 : ℝ))

private theorem measurable_inversePowerSoftMinSecond {Ω : Type*} [MeasurableSpace Ω]
    {A B : Ω → Matrix ι ι ℝ} (hA : Measurable A) (hB : Measurable B) (n : ℕ) :
    Measurable fun x => inversePowerSoftMinSecond n (A x) (B x) := by
  have hR := hA.matrix_inv
  have hT := (hR.matrix_pow n).matrix_trace
  have hU := ((hR.matrix_pow (n + 1)).matrix_mul hB).matrix_trace
  have hK : Measurable fun x => inversePowerHessianKernel (A x)⁻¹ (B x) n := by
    unfold inversePowerHessianKernel
    exact Finset.measurable_fun_sum _ fun a _ =>
      ((((hR.matrix_pow (n - a + 1)).matrix_mul hB).matrix_mul
        (hR.matrix_pow (a + 1))).matrix_mul hB).matrix_trace
  exact ((measurable_const.mul (hT.pow_const _)).mul (hU.pow_const 2)).sub
    ((hT.pow_const _).mul hK)

omit [DecidableEq ι] in
private theorem integrable_frobNorm_sq_gaussianMatrix :
    Integrable (fun G : Matrix ι κ ℝ => frobNorm G ^ 2) (gaussianMatrix ι κ) := by
  have h := integrable_norm_sq_rpow_of_hasLaw_gaussianVector
    (hasLaw_uncurry_of_hasLaw_gaussianMatrix (HasLaw.id (μ := gaussianMatrix ι κ)))
    (s := 1) (by
      have hcard : 0 ≤ (Fintype.card (ι × κ) : ℝ) := Nat.cast_nonneg _
      linarith)
  simpa only [frobNorm_eq_norm_toLp_uncurry, Function.comp_apply, id_eq, Real.rpow_one] using h

omit [DecidableEq ι] in
private theorem integrable_of_abs_le_frobNorm_sq_gaussianMatrix
    {f : Matrix ι κ ℝ → ℝ} (hf : Measurable f) (a b : ℝ)
    (h : ∀ G, |f G| ≤ a + b * frobNorm G ^ 2) :
    Integrable f (gaussianMatrix ι κ) := by
  refine ((integrable_const a).add (integrable_frobNorm_sq_gaussianMatrix.const_mul b)).mono'
    hf.aestronglyMeasurable (ae_of_all _ fun G => ?_)
  simpa only [Real.norm_eq_abs, Pi.add_apply] using h G

/-- **Gaussian integrability of the cutoff Gram field.** For a positive inverse power,
a continuous compactly supported scalar test times an
unshifted Gram gradient entry is integrable under the standard Gaussian matrix law on a
nonempty row type.
No printed source. Original NLAlib atlas proof at
`77514ce42a0e437d837797a063ac161f41022730`.
Result: gram-cutoff-vector-field -/
theorem integrable_mul_gramSoftMinGradient_single_gaussianMatrix [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (ψ : ℝ → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (i : ι) (j : κ) :
    Integrable (fun G : Matrix ι κ ℝ =>
      ψ (inversePowerSoftMin n (G * Gᴴ)) * gramSoftMinGradient n 0 G i j)
      (gaussianMatrix ι κ) := by
  obtain ⟨P, hP⟩ := hψ.bounded_above_of_compact_support hψc
  have hP0 : 0 ≤ P := (norm_nonneg (ψ 0)).trans (hP 0)
  have hm := (hψ.measurable.comp (measurable_inversePowerSoftMin_gram n)).mul
    (measurable_gramSoftMinGradient_single n i j)
  refine integrable_of_abs_le_frobNorm_sq_gaussianMatrix hm (2 * P) (2 * P) fun G => ?_
  rw [abs_mul]
  have hbound := mul_le_mul (hP (inversePowerSoftMin n (G * Gᴴ)))
    (abs_gramSoftMinGradient_unshifted_single_le n hn G i j) (abs_nonneg _) hP0
  simp only [Real.norm_eq_abs] at hbound
  have hnorm : frobNorm G ≤ 1 + frobNorm G ^ 2 := by
    nlinarith [sq_nonneg (frobNorm G - 1)]
  calc
    _ ≤ P * (2 * frobNorm G) := hbound
    _ ≤ P * (2 * (1 + frobNorm G ^ 2)) := by gcongr
    _ = _ := by ring

/-- **Gaussian integrability of the cutoff Gram coordinate product.**
For a positive inverse power and a continuous compactly supported scalar test, the product
of an unshifted cutoff gradient entry with the corresponding matrix coordinate is integrable
under the standard Gaussian law on a nonempty row type.
No printed source. Original NLAlib atlas proof at
`77514ce42a0e437d837797a063ac161f41022730`.
Result: gram-cutoff-vector-field -/
theorem integrable_apply_mul_gramSoftMinGradient_single_gaussianMatrix [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (ψ : ℝ → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (i : ι) (j : κ) :
    Integrable (fun G : Matrix ι κ ℝ =>
      G i j * (ψ (inversePowerSoftMin n (G * Gᴴ)) * gramSoftMinGradient n 0 G i j))
      (gaussianMatrix ι κ) := by
  obtain ⟨P, hP⟩ := hψ.bounded_above_of_compact_support hψc
  have hP0 : 0 ≤ P := (norm_nonneg (ψ 0)).trans (hP 0)
  have hm := (Matrix.measurable_apply i j).mul
    ((hψ.measurable.comp (measurable_inversePowerSoftMin_gram n)).mul
      (measurable_gramSoftMinGradient_single n i j))
  refine integrable_of_abs_le_frobNorm_sq_gaussianMatrix hm 0 (2 * P) fun G => ?_
  simp only [abs_mul, zero_add]
  have hi : |G i j| ≤ frobNorm G := by
    simpa only [Real.norm_eq_abs] using norm_apply_le_frobNorm G i j
  have htest : |ψ (inversePowerSoftMin n (G * Gᴴ))| ≤ P := by
    simpa only [Real.norm_eq_abs] using hP (inversePowerSoftMin n (G * Gᴴ))
  calc
    _ ≤ frobNorm G * (P * (2 * frobNorm G)) := by
      have hG := frobNorm_nonneg G
      have hgrad := abs_gramSoftMinGradient_unshifted_single_le n hn G i j
      gcongr
    _ = _ := by ring

/-- **Gaussian integrability of the cutoff Gram field derivative.**
For a positive inverse power and a smooth compact test supported away from zero in the
positive half-line, the actual cutoff gradient derivative is integrable under the Gaussian
matrix law on a nonempty row type.
No printed source. Original NLAlib atlas proof at
`77514ce42a0e437d837797a063ac161f41022730`.
Result: gram-cutoff-vector-field -/
theorem integrable_deriv_mul_gramSoftMinGradient_single_gaussianMatrix
    [Nonempty ι] [DecidableEq κ] (n : ℕ) (hn : 0 < n)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioi 0) (i : ι) (j : κ) :
    Integrable (fun G : Matrix ι κ ℝ =>
      deriv ψ (inversePowerSoftMin n (G * Gᴴ)) * gramSoftMinGradient n 0 G i j ^ 2 +
        ψ (inversePowerSoftMin n (G * Gᴴ)) * gramSoftMinSecond n 0 G (Matrix.single i j 1))
      (gaussianMatrix ι κ) := by
  obtain ⟨a, ha, hlow⟩ := hψc.isCompact.exists_forall_le' continuous_id.continuousOn
    (fun x hx => hψs hx)
  obtain ⟨B, hB⟩ := hψc.isCompact.bddAbove
  let b := max a B
  have hb : 0 < b := ha.trans_le (le_max_left a B)
  obtain ⟨P, hP⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hderiv := hψ.continuous_deriv (by simp)
  obtain ⟨Q, hQ⟩ := hderiv.bounded_above_of_compact_support hψc.deriv
  have hP0 : 0 ≤ P := (norm_nonneg (ψ 0)).trans (hP 0)
  have hQ0 : 0 ≤ Q := (norm_nonneg (deriv ψ 0)).trans (hQ 0)
  let M : ℝ := 4 * b ^ (n + 1) * ((n : ℝ) + 1) * a⁻¹ ^ (n + 2)
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hD : Measurable fun G : Matrix ι κ ℝ => E * Gᴴ + G * Eᴴ :=
    (measurable_const.matrix_mul (Measurable.matrix_conjTranspose (α := ℝ)
      measurable_id measurable_id)).matrix_add
      (measurable_id.matrix_mul measurable_const)
  have hC : Measurable fun G : Matrix ι κ ℝ => gramSoftMinSecond n 0 G E := by
    simp only [gramSoftMinSecond, regularizedGram_zero,
      inversePowerSoftMinFirst]
    exact (measurable_inversePowerSoftMinSecond measurable_gram hD n).add
      (((measurable_inversePowerSoftMinWeight measurable_gram n).matrix_mul
        measurable_const).matrix_trace)
  have hFm := measurable_inversePowerSoftMin_gram (ι := ι) (κ := κ) n
  have hm := ((hderiv.measurable.comp hFm).mul
    ((measurable_gramSoftMinGradient_single n i j).pow_const 2)).add
    ((hψ.continuous.measurable.comp hFm).mul hC)
  refine integrable_of_abs_le_frobNorm_sq_gaussianMatrix hm (2 * P) (4 * Q + P * M) ?_
  intro G
  let F := inversePowerSoftMin n (G * Gᴴ)
  have hfirst : |deriv ψ F * gramSoftMinGradient n 0 G i j ^ 2| ≤ 4 * Q * frobNorm G ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (gramSoftMinGradient n 0 G i j))]
    have htest : |deriv ψ F| ≤ Q := by simpa only [Real.norm_eq_abs] using hQ F
    have hs := pow_le_pow_left₀ (abs_nonneg _)
      (abs_gramSoftMinGradient_unshifted_single_le n hn G i j) 2
    rw [sq_abs, mul_pow] at hs
    have hh := mul_le_mul htest hs (sq_nonneg _) hQ0
    norm_num at hh
    rw [mul_comm (4 : ℝ) Q, mul_assoc]
    exact hh
  have hsecond : |ψ F * gramSoftMinSecond n 0 G E| ≤ P * (2 + M * frobNorm G ^ 2) := by
    by_cases hz : ψ F = 0
    · rw [hz, zero_mul, abs_zero]
      positivity
    · have hmem : F ∈ tsupport ψ := subset_tsupport ψ hz
      have hupper : F ≤ b := (hB hmem).trans (le_max_right _ _)
      have hbound := abs_gramSoftMinSecond_unshifted_single_le_cutoff n hn G i j
        a b ha (hlow F hmem) hupper
      rw [abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hP F)
        hbound (abs_nonneg _) hP0
  change |deriv ψ F * gramSoftMinGradient n 0 G i j ^ 2 + ψ F * gramSoftMinSecond n 0 G E| ≤ _
  calc
    _ ≤ |deriv ψ F * gramSoftMinGradient n 0 G i j ^ 2| +
        |ψ F * gramSoftMinSecond n 0 G E| := abs_add_le _ _
    _ ≤ 4 * Q * frobNorm G ^ 2 + P * (2 + M * frobNorm G ^ 2) := add_le_add hfirst hsecond
    _ = _ := by ring

end NLAlib
