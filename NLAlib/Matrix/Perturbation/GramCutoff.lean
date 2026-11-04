/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Support
public import NLAlib.Matrix.Perturbation.GramSoftMin
public import NLAlib.Matrix.Perturbation.Continuity
public import NLAlib.Matrix.Pseudoinverse.NormBounds

/-!
# Coordinate calculus of a cutoff Gram field

A test supported away from zero makes the unshifted Gram gradient locally vanish at
deficient matrices. The derivative therefore extends there and obeys the same formula
as on the positive definite domain.

## Main results

* `NLAlib.hasDerivAt_mul_gramSoftMinGradient_single`: the global coordinate derivative.
* `NLAlib.abs_gramSoftMinSecond_unshifted_single_le_cutoff`: the active-region bound.
-/

@[expose] public section

open scoped Matrix Topology
open Matrix Set Filter

namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
private theorem inversePowerSoftMin_le_singularValues_last [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) :
    inversePowerSoftMin n (G * Gᴴ) ≤ singularValues (G * Gᴴ) (Fintype.card ι - 1) := by
  by_cases hpd : (G * Gᴴ).PosDef
  · have hk : Fintype.card ι - 1 + 1 = Fintype.card ι :=
      Nat.sub_add_cancel Fintype.card_pos
    have hi := Matrix.mulVec_injective_iff_isUnit.mpr hpd.isUnit
    have hinv := specNorm_inv_le_inv_inversePowerSoftMin n hn (G * Gᴴ) hpd
    rw [← pinv_of_isUnit hpd.isUnit, specNorm_pinv_of_injective hi hk] at hinv
    have hp := (singularValues_last_pos_iff_injective (G * Gᴴ) hk).mpr hi
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr hp) hinv
  · rw [inversePowerSoftMin_mul_conjTranspose_self_eq_zero_of_not_posDef n hn G hpd]
    exact singularValues_nonneg _ _

omit [DecidableEq ι] [DecidableEq κ] in
private theorem singularValues_gram_last_eq_zero [Nonempty ι] (G : Matrix ι κ ℝ)
    (hG : ¬(G * Gᴴ).PosDef) : singularValues (G * Gᴴ) (Fintype.card ι - 1) = 0 := by
  classical
  have hk : Fintype.card ι - 1 + 1 = Fintype.card ι := Nat.sub_add_cancel Fintype.card_pos
  refine le_antisymm (not_lt.mp ?_) (singularValues_nonneg _ _)
  intro h
  have hi := (singularValues_last_pos_iff_injective (G * Gᴴ) hk).mp h
  exact hG ((Matrix.posSemidef_self_mul_conjTranspose G).posDef_iff_isUnit.mpr
    (Matrix.mulVec_injective_iff_isUnit.mp hi))

omit [DecidableEq κ] in
private theorem inversePowerSoftMin_gram_nonneg (n : ℕ) (G : Matrix ι κ ℝ) :
    0 ≤ inversePowerSoftMin n (G * Gᴴ) :=
  Real.rpow_nonneg ((Matrix.posSemidef_self_mul_conjTranspose G).inv.pow n).trace_nonneg _

/-- **Coordinate derivative of a cutoff Gram field.** For a positive power and a real
matrix with nonempty row type, take a differentiable test whose closed support lies
in $(0,\infty)$. Along the coordinate line based at the matrix, the derivative of the
test times the unshifted gradient entry is the sum of the test derivative times the
squared gradient entry and the test times the second coordinate coefficient. The
formula holds at singular Gram matrices.
No printed source. Original NLAlib atlas proof at
`77514ce42a0e437d837797a063ac161f41022730`.
Result: gram-cutoff-vector-field -/
theorem hasDerivAt_mul_gramSoftMinGradient_single [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (ψ : ℝ → ℝ) (hψ : Differentiable ℝ ψ)
    (hψs : tsupport ψ ⊆ Ioi 0) (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    HasDerivAt (fun t : ℝ =>
      ψ (inversePowerSoftMin n ((G + t • Matrix.single i j 1) *
        (G + t • Matrix.single i j 1)ᴴ)) *
      gramSoftMinGradient n 0 (G + t • Matrix.single i j 1) i j)
      (deriv ψ (inversePowerSoftMin n (G * Gᴴ)) * gramSoftMinGradient n 0 G i j ^ 2 +
        ψ (inversePowerSoftMin n (G * Gᴴ)) *
          gramSoftMinSecond n 0 G (Matrix.single i j 1)) 0 := by
  by_cases hpd : (G * Gᴴ).PosDef
  · have hreg : (regularizedGram 0 (G + (0 : ℝ) • Matrix.single i j 1)).PosDef := by
      simpa only [regularizedGram_zero, zero_smul, add_zero] using hpd
    have hF := hasDerivAt_gramSoftMin_unshifted_single n hn G i j 0 hreg
    have hD := hasDerivAt_gramSoftMinGradient_unshifted_single_zero n hn G hpd i j
    convert! (((hψ (inversePowerSoftMin n ((G + (0 : ℝ) • Matrix.single i j 1) *
      (G + (0 : ℝ) • Matrix.single i j 1)ᴴ))).hasDerivAt.comp 0 hF).mul hD) using 1
    simp only [Function.comp_def, zero_smul, add_zero]
    ring
  · let E : Matrix ι κ ℝ := Matrix.single i j 1
    let H := fun t : ℝ => G + t • E
    let A := fun t : ℝ => H t * (H t)ᴴ
    let F := fun t : ℝ => inversePowerSoftMin n (A t)
    have hA : Continuous A := by
      have hH : Continuous H := continuous_const.add (continuous_id.smul continuous_const)
      exact hH.matrix_mul hH.matrix_conjTranspose
    have hs := (continuous_singularValues (Fintype.card ι - 1)).comp hA
    have hlim : Tendsto (fun t => singularValues (A t) (Fintype.card ι - 1))
        (𝓝 0) (𝓝 0) := by
      simpa only [A, H, Function.comp_def, zero_smul, add_zero,
        singularValues_gram_last_eq_zero G hpd] using hs.tendsto (0 : ℝ)
    have hFlim : Tendsto F (𝓝 0) (𝓝 0) := squeeze_zero
      (fun t => inversePowerSoftMin_gram_nonneg n (H t))
      (fun t => inversePowerSoftMin_le_singularValues_last n hn (H t)) hlim
    have hnot : 0 ∉ tsupport ψ := fun h => lt_irrefl (0 : ℝ) (hψs h)
    have hclosed : IsClosed (tsupport ψ) := isClosed_closure
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), F t ∉ tsupport ψ :=
      hFlim (hclosed.isOpen_compl.mem_nhds hnot)
    have hzero : (fun t : ℝ => ψ (F t) * gramSoftMinGradient n 0 (H t) i j) =ᶠ[𝓝 0]
        fun _ => 0 := by
      filter_upwards [hev] with t ht
      rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
    rw [inversePowerSoftMin_mul_conjTranspose_self_eq_zero_of_not_posDef n hn G hpd,
      image_eq_zero_of_notMem_tsupport hnot, deriv_of_notMem_tsupport hnot,
      zero_mul, zero_mul, zero_add]
    exact (hasDerivAt_const 0 (0 : ℝ)).congr_of_eventuallyEq hzero

private theorem abs_inversePowerSoftMinSecond_le_cutoff [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hB : B.IsHermitian)
    (a b : ℝ) (ha : 0 < a) (hlow : a ≤ inversePowerSoftMin n A)
    (hupp : inversePowerSoftMin n A ≤ b) :
    |inversePowerSoftMinSecond n A B| ≤
      b ^ (n + 1) * ((n : ℝ) + 1) * a⁻¹ ^ (n + 2) * frobNorm B ^ 2 := by
  have hb : 0 < b := ha.trans_le (hlow.trans hupp)
  have hc : Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) ≤ b ^ (n + 1) := by
    rw [trace_inv_pow_rpow_eq_inversePowerSoftMin_pow n hn A hA]
    exact pow_le_pow_left₀ (ha.le.trans hlow) hupp _
  have hinv : specNorm A⁻¹ ≤ a⁻¹ := by
    apply (specNorm_inv_le_inv_inversePowerSoftMin n hn A hA).trans
    simpa only [one_div] using one_div_le_one_div_of_le ha hlow
  have hpow := pow_le_pow_left₀ (specNorm_nonneg A⁻¹) hinv (n + 2)
  have hkernel :
      ((n : ℝ) + 1) * specNorm A⁻¹ ^ (n + 2) * frobNorm B ^ 2 ≤
      ((n : ℝ) + 1) * a⁻¹ ^ (n + 2) * frobNorm B ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
      (sq_nonneg _)
  have hk0 : 0 ≤ ((n : ℝ) + 1) * specNorm A⁻¹ ^ (n + 2) * frobNorm B ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (specNorm_nonneg A⁻¹) _))
      (sq_nonneg _)
  calc
    _ ≤ Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        (((n : ℝ) + 1) * specNorm A⁻¹ ^ (n + 2) * frobNorm B ^ 2) :=
      abs_inversePowerSoftMinSecond_le n A B hA hB
    _ ≤ b ^ (n + 1) * (((n : ℝ) + 1) * a⁻¹ ^ (n + 2) * frobNorm B ^ 2) :=
      mul_le_mul hc hkernel hk0 (pow_nonneg hb.le _)
    _ = _ := by ring

private theorem frobNorm_single_gram_direction_sq_le (G : Matrix ι κ ℝ)
    (i : ι) (j : κ) :
    let E : Matrix ι κ ℝ := Matrix.single i j 1
    frobNorm (E * Gᴴ + G * Eᴴ) ^ 2 ≤ 4 * frobNorm G ^ 2 := by
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  have hEsq : frobNorm E ^ 2 = 1 := by
    simp [E, frobNorm_sq_eq_sum_sq, Matrix.single, ite_and]
  have hE : frobNorm E = 1 := by
    nlinarith [frobNorm_nonneg E]
  have h1 : frobNorm (E * Gᴴ) ≤ frobNorm G := by
    simpa only [frobNorm_conjTranspose, hE, one_mul] using frobNorm_mul_le E Gᴴ
  have h2 : frobNorm (G * Eᴴ) ≤ frobNorm G := by
    simpa only [frobNorm_conjTranspose, hE, mul_one] using frobNorm_mul_le G Eᴴ
  have hnorm := (frobNorm_add_le (E * Gᴴ) (G * Eᴴ)).trans (add_le_add h1 h2)
  change frobNorm (E * Gᴴ + G * Eᴴ) ^ 2 ≤ _
  have hsq := pow_le_pow_left₀ (frobNorm_nonneg (E * Gᴴ + G * Eᴴ)) hnorm 2
  nlinarith

/-- On a positive interval containing the unshifted real Gram potential at a matrix with
nonempty row type, the second coordinate coefficient is bounded by an affine function of
the squared Frobenius norm. The lower endpoint forces the Gram matrix to be positive
definite for a positive inverse power. -/
theorem abs_gramSoftMinSecond_unshifted_single_le_cutoff [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) (i : ι) (j : κ)
    (a b : ℝ) (ha : 0 < a) (hlow : a ≤ inversePowerSoftMin n (G * Gᴴ))
    (hupp : inversePowerSoftMin n (G * Gᴴ) ≤ b) :
    |gramSoftMinSecond n 0 G (Matrix.single i j 1)| ≤
      2 + 4 * b ^ (n + 1) * ((n : ℝ) + 1) * a⁻¹ ^ (n + 2) * frobNorm G ^ 2 := by
  have hpd : (G * Gᴴ).PosDef := by
    by_contra hnot
    rw [inversePowerSoftMin_mul_conjTranspose_self_eq_zero_of_not_posDef n hn G hnot] at hlow
    linarith
  have hb : 0 < b := ha.trans_le (hlow.trans hupp)
  let E : Matrix ι κ ℝ := Matrix.single i j 1
  let A := G * Gᴴ
  let P := inversePowerSoftMinWeight n A
  have hP : P.PosSemidef := inversePowerSoftMinWeight_posSemidef n hpd.posSemidef
  have hPdiag (k : ι) : 0 ≤ P k k := hP.diag_nonneg
  have hPi : P i i ≤ 1 := by
    have hh : P i i ≤ Matrix.trace P := by
      simpa only [Matrix.trace, Matrix.diag] using
        Finset.single_le_sum (fun k _ => hPdiag k) (Finset.mem_univ i)
    exact hh.trans (trace_inversePowerSoftMinWeight_le_one n hn hpd)
  have hEE : E * Eᴴ = Matrix.single i i 1 := by
    simp only [E, Matrix.conjTranspose_single, star_trivial, Matrix.single_mul_single_same, one_mul]
  have hfirst : inversePowerSoftMinFirst n A ((2 : ℝ) • (E * Eᴴ)) = 2 * P i i := by
    rw [inversePowerSoftMinFirst, hEE, mul_smul_comm,
      Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_single]
    simp [P]
  have hfirstabs : |inversePowerSoftMinFirst n A ((2 : ℝ) • (E * Eᴴ))| ≤ 2 := by
    rw [hfirst, abs_of_nonneg (mul_nonneg (by norm_num) (hPdiag i))]
    linarith
  have hdir : (E * Gᴴ + G * Eᴴ).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose, add_comm]
  have hsecond := abs_inversePowerSoftMinSecond_le_cutoff n hn A (E * Gᴴ + G * Eᴴ)
    hpd hdir a b ha hlow hupp
  have hB := frobNorm_single_gram_direction_sq_le G i j
  have hc0 : 0 ≤ b ^ (n + 1) * ((n : ℝ) + 1) * a⁻¹ ^ (n + 2) := by positivity
  simp only [gramSoftMinSecond, regularizedGram_zero]
  change |inversePowerSoftMinSecond n A (E * Gᴴ + G * Eᴴ) +
    inversePowerSoftMinFirst n A ((2 : ℝ) • (E * Eᴴ))| ≤ _
  calc
    _ ≤ |inversePowerSoftMinSecond n A (E * Gᴴ + G * Eᴴ)| +
        |inversePowerSoftMinFirst n A ((2 : ℝ) • (E * Eᴴ))| := abs_add_le _ _
    _ ≤ b ^ (n + 1) * ((n : ℝ) + 1) * a⁻¹ ^ (n + 2) *
        frobNorm (E * Gᴴ + G * Eᴴ) ^ 2 + 2 := add_le_add hsecond hfirstabs
    _ ≤ b ^ (n + 1) * ((n : ℝ) + 1) * a⁻¹ ^ (n + 2) * (4 * frobNorm G ^ 2) + 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hB hc0) (le_refl _)
    _ = _ := by ring

omit [DecidableEq κ] in
/-- For positive inverse power and nonempty row type, each unshifted gradient entry of
a real Gram matrix has absolute value at most twice the Frobenius norm of the matrix. -/
theorem abs_gramSoftMinGradient_unshifted_single_le [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (G : Matrix ι κ ℝ) (i : ι) (j : κ) :
    |gramSoftMinGradient n 0 G i j| ≤ 2 * frobNorm G := by
  have hsoft : inversePowerSoftMin n (G * Gᴴ) ≤ frobNorm G ^ 2 := calc
    _ ≤ singularValues (G * Gᴴ) (Fintype.card ι - 1) :=
      inversePowerSoftMin_le_singularValues_last n hn G
    _ ≤ specNorm (G * Gᴴ) := singularValues_le_specNorm _ _
    _ = specNorm G ^ 2 := specNorm_mul_conjTranspose_self G
    _ ≤ frobNorm G ^ 2 := pow_le_pow_left₀ (specNorm_nonneg G) (specNorm_le_frobNorm G) 2
  have h := frobNorm_gramSoftMinGradient_sq_unshifted_le_of_pos n hn G
  have hD : frobNorm (gramSoftMinGradient n 0 G) ≤ 2 * frobNorm G := by
    have hh := mul_le_mul_of_nonneg_left hsoft (by norm_num : (0 : ℝ) ≤ 4)
    exact (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).mp (by nlinarith)
  have hentry : |gramSoftMinGradient n 0 G i j| ≤ frobNorm (gramSoftMinGradient n 0 G) := by
    simpa only [Real.norm_eq_abs] using norm_apply_le_frobNorm (gramSoftMinGradient n 0 G) i j
  exact hentry.trans hD

end NLAlib
