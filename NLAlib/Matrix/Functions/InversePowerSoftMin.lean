/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import NLAlib.ForMathlib.Analysis.Calculus.Deriv.Matrix
public import NLAlib.Matrix.Functions.TracePowers
public import NLAlib.Matrix.Norms.Compare

/-!
# The inverse-power spectral minimum

The reciprocal root of the inverse-power trace gives a smooth spectral approximation on the
positive definite domain. Its directional coefficients use finite products and traces.

## Main results

* `NLAlib.inversePowerSoftMin`: the potential.
* `NLAlib.hasDerivAt_inversePowerSoftMin`: its derivative along a matrix curve.
* `NLAlib.hasDerivAt_inversePowerSoftMinFirst`: the derivative of the first coefficient.
-/

@[expose] public section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic trace kernel of the second derivative of an inverse trace power. -/
noncomputable def inversePowerHessianKernel (R B : Matrix ι ι ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    Matrix.trace (R ^ (n - i + 1) * B * R ^ (i + 1) * B)

/-- The reciprocal $n$th root of the trace of the $n$th inverse power of a real matrix. -/
noncomputable def inversePowerSoftMin (n : ℕ) (A : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹)

/-- The trace-pairing weight for the first directional coefficient of the inverse-power
potential. -/
noncomputable def inversePowerSoftMinWeight (n : ℕ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) • A⁻¹ ^ (n + 1)

/-- The first directional coefficient of the inverse-power potential in direction $\mathbf{B}$. -/
noncomputable def inversePowerSoftMinFirst (n : ℕ) (A B : Matrix ι ι ℝ) : ℝ :=
  (inversePowerSoftMinWeight n A * B).trace

/-- The second directional coefficient of the inverse-power potential along a matrix
affine line. -/
noncomputable def inversePowerSoftMinSecond (n : ℕ) (A B : Matrix ι ι ℝ) : ℝ :=
  ((n : ℝ) + 1) * Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 2) *
      Matrix.trace (A⁻¹ ^ (n + 1) * B) ^ 2 -
    Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) * inversePowerHessianKernel A⁻¹ B n

private theorem hasDerivAt_matrix_inv {A : ℝ → Matrix ι ι ℝ}
    {A' : Matrix ι ι ℝ} {t : ℝ} (hA : HasDerivAt A A' t)
    (hunit : IsUnit (A t)) :
    HasDerivAt (fun x => (A x)⁻¹) (-(A t)⁻¹ * A' * (A t)⁻¹) t := by
  refine Matrix.hasDerivAt_iff_forall_apply.mpr fun i j => ?_
  simpa only [neg_mul] using Matrix.hasDerivAt_inv_apply
    (Matrix.hasDerivAt_iff_forall_apply.mp hA) ((A t).isUnit_iff_isUnit_det.mp hunit) i j

private theorem hasDerivAt_matrix_trace_inv_pow {A : ℝ → Matrix ι ι ℝ}
    {A' : Matrix ι ι ℝ} {t : ℝ} (hA : HasDerivAt A A' t)
    (hunit : IsUnit (A t)) (n : ℕ) :
    HasDerivAt (fun x => Matrix.trace ((A x)⁻¹ ^ n))
      (-(n : ℝ) * Matrix.trace ((A t)⁻¹ ^ (n + 1) * A')) t := by
  cases n with
  | zero =>
    simpa only [pow_zero, Nat.cast_zero, neg_zero, zero_mul] using
      hasDerivAt_const t (Matrix.trace (1 : Matrix ι ι ℝ))
  | succ n =>
    have h := Matrix.hasDerivAt_trace_pow_succ
      (Matrix.hasDerivAt_iff_forall_apply.mp (hasDerivAt_matrix_inv hA hunit)) n
    have htrace : Matrix.trace ((-(A t)⁻¹ * A' * (A t)⁻¹) * (A t)⁻¹ ^ n) =
        -Matrix.trace ((A t)⁻¹ ^ (n + 2) * A') := by
      simp only [neg_mul, Matrix.trace_neg]
      rw [Matrix.trace_mul_cycle ((A t)⁻¹ * A') (A t)⁻¹ ((A t)⁻¹ ^ n),
        ← Matrix.mul_assoc]
      rw [Matrix.trace_mul_cycle ((A t)⁻¹ ^ n * (A t)⁻¹) A' (A t)⁻¹,
        ← Matrix.mul_assoc, ← pow_succ', ← pow_succ]
    rw [htrace] at h
    simpa only [Nat.cast_succ, mul_neg, neg_mul] using h

private theorem trace_inv_power_derivative_sum (R B : Matrix ι ι ℝ) (n : ℕ) :
    Matrix.trace ((∑ i ∈ Finset.range (n + 1),
      R ^ ((n + 1).pred - i) * (-R * B * R) * R ^ i) * B) =
      -∑ i ∈ Finset.range (n + 1),
        Matrix.trace (R ^ (n - i + 1) * B * R ^ (i + 1) * B) := by
  simp only [Finset.sum_mul, Matrix.trace_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.pred_succ, neg_mul, mul_neg, Matrix.trace_neg]
  apply congrArg (fun M : Matrix ι ι ℝ => -Matrix.trace M)
  calc R ^ (n - i) * (R * B * R) * R ^ i * B
      = (R ^ (n - i) * R) * B * (R * R ^ i) * B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← pow_succ, ← pow_succ']

private theorem hasDerivAt_matrix_trace_inv_pow_mul {A D : ℝ → Matrix ι ι ℝ}
    {D' : Matrix ι ι ℝ} {t : ℝ} (hA : HasDerivAt A (D t) t)
    (hD : HasDerivAt D D' t) (hunit : IsUnit (A t)) (n : ℕ) :
    HasDerivAt (fun x => Matrix.trace ((A x)⁻¹ ^ (n + 1) * D x))
      ((-∑ i ∈ Finset.range (n + 1), Matrix.trace ((A t)⁻¹ ^ (n - i + 1) *
        D t * (A t)⁻¹ ^ (i + 1) * D t)) + Matrix.trace ((A t)⁻¹ ^ (n + 1) * D')) t := by
  have hpow := (hasDerivAt_matrix_inv hA hunit).fun_pow' (n + 1)
  let tr : Matrix ι ι ℝ →L[ℝ] ℝ := (Matrix.traceLinearMap ι ℝ ℝ).toContinuousLinearMap
  have htrace := (hasDerivAt_const t tr).clm_apply (hpow.mul hD)
  simp only [_root_.zero_apply, zero_add] at htrace
  convert! htrace using 1
  · simp only [tr, LinearMap.coe_toContinuousLinearMap']
    change _ = Matrix.trace (_ + _)
    rw [Matrix.trace_add, trace_inv_power_derivative_sum]

/-- Along an invertible differentiable matrix curve with positive inverse-power trace at the
base point, the inverse-power potential has derivative given by its first directional coefficient
when the power is positive. -/
theorem hasDerivAt_inversePowerSoftMin (n : ℕ) (hn : 0 < n)
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hunit : IsUnit (A t))
    (hT : 0 < Matrix.trace ((A t)⁻¹ ^ n)) :
    HasDerivAt (fun x => inversePowerSoftMin n (A x))
      (inversePowerSoftMinFirst n (A t) A') t := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := (hasDerivAt_matrix_trace_inv_pow hA hunit n).rpow_const
    (p := -(n : ℝ)⁻¹) (Or.inl hT.ne')
  convert! h using 1
  · unfold inversePowerSoftMinFirst inversePowerSoftMinWeight
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    field_simp

/-- Along an invertible twice differentiable matrix curve with positive inverse-power trace
at the base point, the first coefficient of the positive inverse-power potential has derivative
given by its second directional coefficient plus the trace pairing with the curve acceleration. -/
theorem hasDerivAt_inversePowerSoftMinFirst (n : ℕ) (hn : 0 < n)
    {A D : ℝ → Matrix ι ι ℝ} {D' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A (D t) t) (hD : HasDerivAt D D' t)
    (hunit : IsUnit (A t)) (hT : 0 < Matrix.trace ((A t)⁻¹ ^ n)) :
    HasDerivAt (fun x => inversePowerSoftMinFirst n (A x) (D x))
      (inversePowerSoftMinSecond n (A t) (D t) +
        inversePowerSoftMinFirst n (A t) D') t := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpower := (hasDerivAt_matrix_trace_inv_pow hA hunit n).rpow_const
    (p := -(n : ℝ)⁻¹ - 1) (Or.inl hT.ne')
  have hmul := hpower.mul (hasDerivAt_matrix_trace_inv_pow_mul hA hD hunit n)
  convert! hmul using 1
  · funext x
    simp only [inversePowerSoftMinFirst, inversePowerSoftMinWeight,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Pi.mul_apply]
  · unfold inversePowerSoftMinSecond inversePowerSoftMinFirst inversePowerSoftMinWeight
      inversePowerHessianKernel
    simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    have he : -(n : ℝ)⁻¹ - 1 - 1 = -(n : ℝ)⁻¹ - 2 := by ring
    rw [he]
    field_simp
    ring

private theorem trace_conjStarAlgAut {R : Type*} [CommRing R] [StarRing R]
    (U : Matrix.unitaryGroup ι R) (A : Matrix ι ι R) :
    Matrix.trace (Unitary.conjStarAlgAut R _ U A) = Matrix.trace A := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

private theorem trace_pow_eq_sum_eigenvalues {R : Matrix ι ι ℝ} (hR : R.IsHermitian) (n : ℕ) :
    Matrix.trace (R ^ n) = ∑ i, hR.eigenvalues i ^ n := by
  conv_lhs => rw [hR.spectral_theorem, ← map_pow]
  rw [trace_conjStarAlgAut,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

/-- The inverse-power weight of a positive semidefinite real matrix is positive semidefinite. -/
theorem inversePowerSoftMinWeight_posSemidef (n : ℕ) {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) : (inversePowerSoftMinWeight n A).PosSemidef := by
  exact (hA.inv.pow (n + 1)).smul (Real.rpow_nonneg
    (hA.inv.pow n).trace_nonneg _)

/-- For a positive definite real matrix of nonzero dimension and a positive power,
the inverse-power weight has trace at most one. -/
theorem trace_inversePowerSoftMinWeight_le_one [Nonempty ι] (n : ℕ) (hn : 0 < n)
    {A : Matrix ι ι ℝ} (hA : A.PosDef) : Matrix.trace (inversePowerSoftMinWeight n A) ≤ 1 := by
  set R := A⁻¹
  set T := Matrix.trace (R ^ n) with hTdef
  have hR : R.PosDef := hA.inv
  have hT : 0 < T := hR.trace_pow_pos n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let ev := hR.isHermitian.eigenvalues
  have hev : ∀ i, 0 ≤ ev i := fun i => (hR.eigenvalues_pos i).le
  have htrace (m : ℕ) : Matrix.trace (R ^ m) = ∑ i, ev i ^ m :=
    trace_pow_eq_sum_eigenvalues hR.isHermitian m
  have hroot (i : ι) : ev i ≤ T ^ (n : ℝ)⁻¹ := by
    have hsingle : ev i ^ n ≤ T := by
      rw [hTdef, htrace]
      exact Finset.single_le_sum (fun j _ => pow_nonneg (hev j) n) (Finset.mem_univ i)
    have h := Real.rpow_le_rpow (pow_nonneg (hev i) n) hsingle
      (inv_nonneg.mpr (Nat.cast_nonneg n))
    rw [← Real.rpow_natCast (ev i) n, Real.rpow_rpow_inv (hev i) hn0] at h
    exact h
  have hnext : Matrix.trace (R ^ (n + 1)) ≤ T * T ^ (n : ℝ)⁻¹ := by
    rw [htrace, hTdef, htrace, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [pow_succ]
    simpa only [hTdef, htrace] using
      mul_le_mul_of_nonneg_left (hroot i) (pow_nonneg (hev i) n)
  have heq : T ^ (-(n : ℝ)⁻¹ - 1) * (T * T ^ (n : ℝ)⁻¹) = 1 := by
    nth_rw 2 [← Real.rpow_one T]
    rw [← mul_assoc, ← Real.rpow_add hT, ← Real.rpow_add hT,
      show (-(n : ℝ)⁻¹ - 1) + 1 + (n : ℝ)⁻¹ = 0 by ring, Real.rpow_zero]
  unfold inversePowerSoftMinWeight
  rw [Matrix.trace_smul, smul_eq_mul]
  change T ^ (-(n : ℝ)⁻¹ - 1) * Matrix.trace (R ^ (n + 1)) ≤ 1
  exact (mul_le_mul_of_nonneg_left hnext (Real.rpow_nonneg hT.le _)).trans_eq heq

private theorem mul_trace_pow_mul_sq_le_trace_pow_mul_inversePowerHessianKernel
    {R B : Matrix ι ι ℝ} (hR : R.PosSemidef) (hB : B.IsHermitian) (n : ℕ) :
    ((n : ℝ) + 1) * Matrix.trace (R ^ (n + 1) * B) ^ 2 ≤
      Matrix.trace (R ^ n) * inversePowerHessianKernel R B n := by
  let U := star hR.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  let C := φ B
  let ev := hR.isHermitian.eigenvalues
  have hdiag : φ R = Matrix.diagonal ev := by
    dsimp only [φ, U, ev]
    simpa using hR.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hC : C.IsHermitian := hB.isSelfAdjoint.map φ |>.isHermitian
  have hev : ∀ i, 0 ≤ ev i := hR.eigenvalues_nonneg
  have hT : Matrix.trace (R ^ n) = ∑ i, ev i ^ n := by
    calc _ = Matrix.trace (φ (R ^ n)) := (trace_conjStarAlgAut U _).symm
      _ = _ := by
        simp only [map_pow, hdiag, Matrix.diagonal_pow, Matrix.trace_diagonal, Pi.pow_apply]
  have hL : Matrix.trace (R ^ (n + 1) * B) = ∑ i, ev i ^ (n + 1) * C i i := by
    calc _ = Matrix.trace (φ (R ^ (n + 1) * B)) := (trace_conjStarAlgAut U _).symm
      _ = _ := by simp only [map_mul, map_pow, hdiag, Matrix.diagonal_pow,
        Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Pi.pow_apply]; rfl
  have hterm (a : ℕ) : Matrix.trace (R ^ (n - a + 1) * B * R ^ (a + 1) * B) =
      ∑ i, ∑ j, C i j ^ 2 * ev j ^ (n - a + 1) * ev i ^ (a + 1) := by
    calc _ = Matrix.trace (φ (R ^ (n - a + 1) * B * R ^ (a + 1) * B)) :=
          (trace_conjStarAlgAut U _).symm
      _ = Matrix.trace ((Matrix.diagonal ev) ^ (n - a + 1) * C *
            (Matrix.diagonal ev) ^ (a + 1) * C) := by simp only [map_mul, map_pow, hdiag]; rfl
      _ = Matrix.trace (C * (Matrix.diagonal ev) ^ (n - a + 1) * C *
            (Matrix.diagonal ev) ^ (a + 1)) := by
          rw [Matrix.trace_mul_cycle]
          simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [Matrix.diagonal_pow, Matrix.diagonal_pow]
        have h := hC.re_trace_mul_diagonal_mul_mul_diagonal (ev ^ (n - a + 1)) (ev ^ (a + 1))
        simp only [RCLike.re_to_real, RCLike.ofReal_real_eq_id, id, Real.norm_eq_abs, sq_abs,
          mul_assoc] at h ⊢
        rw [h]
        simp only [Pi.pow_apply]
  let D : ℝ := ∑ i, ev i ^ (n + 2) * C i i ^ 2
  have hkernel : ((n : ℝ) + 1) * D ≤ inversePowerHessianKernel R B n := by
    calc _ = ∑ _a ∈ Finset.range (n + 1), D := by simp
      _ ≤ inversePowerHessianKernel R B n := by
        apply Finset.sum_le_sum
        intro a ha
        rw [hterm]
        apply Finset.sum_le_sum
        intro i _
        have hai : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have hdiagterm : ev i ^ (n + 2) * C i i ^ 2 =
            C i i ^ 2 * ev i ^ (n - a + 1) * ev i ^ (a + 1) := by
          rw [mul_assoc, ← pow_add, show n - a + 1 + (a + 1) = n + 2 by omega]
          ring
        rw [hdiagterm]
        exact Finset.single_le_sum (f := fun j =>
          C i j ^ 2 * ev j ^ (n - a + 1) * ev i ^ (a + 1))
          (fun j _ => mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (hev j) _))
            (pow_nonneg (hev i) _)) (Finset.mem_univ i)
  have hCS : Matrix.trace (R ^ (n + 1) * B) ^ 2 ≤ Matrix.trace (R ^ n) * D := by
    rw [hT, hL]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    · intro i _; exact pow_nonneg (hev i) _
    · intro i _; exact mul_nonneg (pow_nonneg (hev i) _) (sq_nonneg _)
    · intro i _
      have hpow : (ev i ^ (n + 1)) ^ 2 = ev i ^ n * ev i ^ (n + 2) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      rw [mul_pow, hpow]
      ring_nf
      exact le_refl _
  have hTnn : 0 ≤ Matrix.trace (R ^ n) := (hR.pow n).trace_nonneg
  calc ((n : ℝ) + 1) * Matrix.trace (R ^ (n + 1) * B) ^ 2
      ≤ ((n : ℝ) + 1) * (Matrix.trace (R ^ n) * D) := by gcongr
    _ = Matrix.trace (R ^ n) * (((n : ℝ) + 1) * D) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hkernel hTnn

/-- At a positive definite real matrix of nonzero dimension, the second inverse-power
coefficient is nonpositive in every symmetric direction. -/
theorem inversePowerSoftMinSecond_le_zero [Nonempty ι] (n : ℕ)
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.IsHermitian) :
    inversePowerSoftMinSecond n A B ≤ 0 := by
  have hT := hA.inv.trace_pow_pos n
  have hCS := mul_trace_pow_mul_sq_le_trace_pow_mul_inversePowerHessianKernel
    hA.inv.posSemidef hB n
  have he : -(n : ℝ)⁻¹ - 1 = (-(n : ℝ)⁻¹ - 2) + 1 := by ring
  unfold inversePowerSoftMinSecond
  rw [he, Real.rpow_add hT, Real.rpow_one]
  have hpos : 0 ≤ Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 2) := Real.rpow_nonneg hT.le _
  nlinarith [mul_le_mul_of_nonneg_left hCS hpos]

/-- At a positive definite real matrix of nonzero dimension, for a positive power $n$,
the scalar trace coefficient of the weight equals the potential to the power $n+1$. -/
theorem trace_inv_pow_rpow_eq_inversePowerSoftMin_pow [Nonempty ι] (n : ℕ) (hn : 0 < n)
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) = inversePowerSoftMin n A ^ (n + 1) := by
  have hT : 0 < Matrix.trace (A⁻¹ ^ n) := hA.inv.trace_pow_pos n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [inversePowerSoftMin, ← Real.rpow_natCast _ (n + 1), ← Real.rpow_mul hT.le]
  congr 1
  push_cast
  field_simp
  ring

/-- For a positive definite real matrix on a nonempty index type, the inverse spectral norm
is at most the reciprocal of the positive inverse-power potential. -/
theorem specNorm_inv_le_inv_inversePowerSoftMin [Nonempty ι]
    (n : ℕ) (hn : 0 < n) (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    specNorm A⁻¹ ≤ (inversePowerSoftMin n A)⁻¹ := by
  have hR := hA.inv.posSemidef
  have hb := hR.eigenvalue_nonneg 0
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hT := hA.inv.trace_pow_pos n
  have hsingle : eigenvalue A⁻¹ 0 ^ n ≤ Matrix.trace (A⁻¹ ^ n) := by
    have htrace := hR.isHermitian.re_trace_pow_eq_sum_range_eigenvalue_pow n
    simp only [RCLike.re_to_real] at htrace
    rw [htrace]
    exact Finset.single_le_sum (fun j _ => pow_nonneg (hR.eigenvalue_nonneg j) n)
      (Finset.mem_range.mpr Fintype.card_pos)
  have h := Real.rpow_le_rpow (pow_nonneg hb n) hsingle
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  rw [← Real.rpow_natCast _ n, Real.rpow_rpow_inv hb hn0] at h
  rw [hR.specNorm_eq_eigenvalue_zero, inversePowerSoftMin, Real.rpow_neg hT.le, inv_inv]
  exact h

private theorem abs_trace_pow_mul_mul_pow_mul_le (R B : Matrix ι ι ℝ) (p q : ℕ) :
    |Matrix.trace (R ^ p * B * R ^ q * B)| ≤
      specNorm R ^ (p + q) * frobNorm B ^ 2 := by
  cases isEmpty_or_nonempty ι with
  | inl hι => simp [Matrix.trace, Matrix.diag, frobNorm_sq_eq_sum]
  | inr hι =>
    have htrace : Matrix.trace (R ^ p * B * R ^ q * B) =
        frobInner (R ^ p * B)ᴴ (R ^ q * B) := by
      rw [frobInner_eq_re_trace, RCLike.re_to_real,
      Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
    have hp : specNorm (R ^ p) ≤ specNorm R ^ p := by
      exact specNorm_pow_le R p
    have hq : specNorm (R ^ q) ≤ specNorm R ^ q := by
      exact specNorm_pow_le R q
    have hfp : frobNorm (R ^ p * B) ≤ specNorm R ^ p * frobNorm B :=
      (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans
        (mul_le_mul_of_nonneg_right hp (frobNorm_nonneg B))
    have hfq : frobNorm (R ^ q * B) ≤ specNorm R ^ q * frobNorm B :=
      (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans
        (mul_le_mul_of_nonneg_right hq (frobNorm_nonneg B))
    rw [htrace]
    calc
      _ ≤ frobNorm (R ^ p * B) * frobNorm (R ^ q * B) := by
        simpa only [frobNorm_conjTranspose] using
          abs_frobInner_le (R ^ p * B)ᴴ (R ^ q * B)
      _ ≤ (specNorm R ^ p * frobNorm B) * (specNorm R ^ q * frobNorm B) :=
        mul_le_mul hfp hfq (frobNorm_nonneg _) (mul_nonneg
          (pow_nonneg (specNorm_nonneg R) _) (frobNorm_nonneg B))
      _ = _ := by rw [pow_add]; ring

private theorem abs_inversePowerHessianKernel_le (R B : Matrix ι ι ℝ) (n : ℕ) :
    |inversePowerHessianKernel R B n| ≤
      ((n : ℝ) + 1) * specNorm R ^ (n + 2) * frobNorm B ^ 2 := by
  unfold inversePowerHessianKernel
  calc
    _ ≤ ∑ a ∈ Finset.range (n + 1),
        |Matrix.trace (R ^ (n - a + 1) * B * R ^ (a + 1) * B)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.range (n + 1), specNorm R ^ (n + 2) * frobNorm B ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      simpa only [show n - a + 1 + (a + 1) = n + 2 by omega] using
        abs_trace_pow_mul_mul_pow_mul_le R B (n - a + 1) (a + 1)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]; ring

/-- At a positive definite real matrix of nonzero dimension, the absolute second
coefficient in a symmetric direction is bounded by the weighted trace kernel estimate. -/
theorem abs_inversePowerSoftMinSecond_le [Nonempty ι] (n : ℕ) (A B : Matrix ι ι ℝ)
    (hA : A.PosDef) (hB : B.IsHermitian) :
    |inversePowerSoftMinSecond n A B| ≤
      Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        (((n : ℝ) + 1) * specNorm A⁻¹ ^ (n + 2) * frobNorm B ^ 2) := by
  have hnonpos := inversePowerSoftMinSecond_le_zero n hA hB
  have hT := hA.inv.trace_pow_pos n
  have hsquare : 0 ≤ ((n : ℝ) + 1) *
      Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 2) *
      Matrix.trace (A⁻¹ ^ (n + 1) * B) ^ 2 := by positivity
  have hc : 0 ≤ Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) :=
    Real.rpow_nonneg hT.le _
  have hk := abs_inversePowerHessianKernel_le A⁻¹ B n
  rw [abs_of_nonpos hnonpos]
  unfold inversePowerSoftMinSecond
  calc
    _ ≤ Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        inversePowerHessianKernel A⁻¹ B n := by linarith
    _ ≤ Matrix.trace (A⁻¹ ^ n) ^ (-(n : ℝ)⁻¹ - 1) *
        |inversePowerHessianKernel A⁻¹ B n| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hc
    _ ≤ _ := mul_le_mul_of_nonneg_left hk hc

end NLAlib
