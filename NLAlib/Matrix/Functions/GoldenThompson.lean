/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Exponential
public import NLAlib.Matrix.Functions.Exponential

/-!
# The Golden–Thompson inequality

For Hermitian $\mathbf{H}$ and $\mathbf{K}$,
$\operatorname{tr} \exp(\mathbf{H} + \mathbf{K})
\le \operatorname{tr}(\exp(\mathbf{H})\exp(\mathbf{K}))$.
It replaces the scalar identity $e^{h + k} = e^h e^k$ in the Ahlswede–Winter approach to matrix
concentration.

The proof is the classical one: the Lie product formula
$(\exp(\mathbf{H}/n)\exp(\mathbf{K}/n))^n \to \exp(\mathbf{H} + \mathbf{K})$ along $n = 2^k$, and
the trace inequality
$\operatorname{tr} (\mathbf{A}\mathbf{B})^{2^k}
\le \operatorname{tr}(\mathbf{A}^{2^k}\mathbf{B}^{2^k})$
for positive semidefinite $\mathbf{A}$, $\mathbf{B}$. It works over any `RCLike` field and does
not use Lieb's theorem.

## Main results

* `NLAlib.tendsto_exp_smul_mul_exp_smul_pow`: the Lie product formula for matrices.
* `Matrix.PosSemidef.re_trace_mul_pow_two_pow_le`:
  $\operatorname{tr} (\mathbf{A}\mathbf{B})^m \le \operatorname{tr}(\mathbf{A}^m\mathbf{B}^m)$ for
  $m = 2^k$.
* `Matrix.IsHermitian.re_trace_exp_add_le`: the Golden–Thompson inequality.
* `Matrix.PosDef.re_trace_exp_add_cfc_log_le`: the form
  $\operatorname{tr} \exp(\mathbf{H} + \log(\mathbf{X}))
  \le \operatorname{tr}(\exp(\mathbf{H})\mathbf{X})$.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder Topology
open NormedSpace (exp)
open Filter

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- The trace of a product of two positive semidefinite matrices has nonnegative real part:
$\operatorname{Re} \operatorname{tr}(\mathbf{A}\mathbf{B}) \ge 0$. -/
theorem _root_.Matrix.PosSemidef.re_trace_mul_nonneg {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ RCLike.re (A * B).trace := by
  classical
  have hS : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint
  have h := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).re_trace_nonneg
  rwa [hS, Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self A hA.nonneg] at h

/-! ### Traces of powers of a product -/

/-- $\operatorname{Re} \operatorname{tr}(\mathbf{Y}^{\mathsf{H}}\mathbf{Z})
\le (\operatorname{Re} \operatorname{tr}(\mathbf{Y}^{\mathsf{H}}\mathbf{Y}) +
\operatorname{Re} \operatorname{tr}(\mathbf{Z}^{\mathsf{H}}\mathbf{Z})) / 2$. -/
private theorem re_trace_conjTranspose_mul_le (Y Z : Matrix n n 𝕜) :
    RCLike.re (Yᴴ * Z).trace ≤ (RCLike.re (Yᴴ * Y).trace + RCLike.re (Zᴴ * Z).trace) / 2 := by
  have h := (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (Y - Z)).trace_nonneg).1
  have hstar : RCLike.re (Zᴴ * Y).trace = RCLike.re (Yᴴ * Z).trace := by
    rw [← Matrix.conjTranspose_conjTranspose Y, ← Matrix.conjTranspose_mul,
      Matrix.trace_conjTranspose, Matrix.conjTranspose_conjTranspose, RCLike.star_def,
      RCLike.conj_re]
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.trace_sub, Matrix.trace_sub, map_sub, map_sub, map_sub, hstar] at h
  linarith

/-- The trace of a power of a product does not depend on the order of the factors. -/
private theorem trace_mul_pow_comm [DecidableEq n] (X Y : Matrix n n 𝕜) (k : ℕ) :
    ((X * Y) ^ k).trace = ((Y * X) ^ k).trace := by
  cases k with
  | zero => rw [pow_zero, pow_zero]
  | succ k =>
    have h : ∀ j : ℕ, (X * Y) ^ (j + 1) = X * (Y * X) ^ j * Y := fun j => by
      induction j with
      | zero => rw [pow_zero, zero_add, pow_one, Matrix.mul_one]
      | succ j ih =>
        rw [pow_succ, ih, pow_succ]
        simp only [Matrix.mul_assoc]
    rw [h, Matrix.trace_mul_cycle, ← pow_succ']

/-- For $m = 2^j$: $\operatorname{Re} \operatorname{tr} \mathbf{X}^{2m}
\le \operatorname{Re} \operatorname{tr} (\mathbf{X}^{\mathsf{H}}\mathbf{X})^m$ for every
$\mathbf{X}$, and $\operatorname{Re} \operatorname{tr} (\mathbf{A}\mathbf{B})^m
\le \operatorname{Re} \operatorname{tr}(\mathbf{A}^m\mathbf{B}^m)$ for positive semidefinite
$\mathbf{A}$, $\mathbf{B}$. The two are proved together by induction on $j$. -/
private theorem re_trace_pow_two_pow_le_aux [DecidableEq n] (j : ℕ) :
    (∀ X : Matrix n n 𝕜,
      RCLike.re (X ^ 2 ^ (j + 1)).trace ≤ RCLike.re ((Xᴴ * X) ^ 2 ^ j).trace) ∧
    ∀ A B : Matrix n n 𝕜, A.PosSemidef → B.PosSemidef →
      RCLike.re ((A * B) ^ 2 ^ j).trace ≤ RCLike.re (A ^ 2 ^ j * B ^ 2 ^ j).trace := by
  induction j with
  | zero =>
    refine ⟨fun X => ?_, fun A B _ _ => ?_⟩
    · have h := re_trace_conjTranspose_mul_le Xᴴ X
      rw [Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm X Xᴴ] at h
      rw [zero_add, pow_one, pow_zero, pow_one, pow_two]
      linarith
    · rw [pow_zero, pow_one, pow_one, pow_one]
  | succ j ih =>
    obtain ⟨ihS, ihT⟩ := ih
    refine ⟨fun X => ?_, fun A B hA hB => ?_⟩
    · have h1 := ihS (X ^ 2)
      have h2 : (((X ^ 2)ᴴ * X ^ 2) ^ 2 ^ j).trace = ((Xᴴ * X * (X * Xᴴ)) ^ 2 ^ j).trace := by
        rw [show (X ^ 2)ᴴ * X ^ 2 = Xᴴ * (Xᴴ * X * X) by
          rw [pow_two, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc], trace_mul_pow_comm, Matrix.mul_assoc (Xᴴ * X)]
      have h3 := ihT (Xᴴ * X) (X * Xᴴ) (Matrix.posSemidef_conjTranspose_mul_self X)
        (Matrix.posSemidef_self_mul_conjTranspose X)
      have h4 := re_trace_conjTranspose_mul_le ((Xᴴ * X) ^ 2 ^ j) ((X * Xᴴ) ^ 2 ^ j)
      rw [((Matrix.isHermitian_conjTranspose_mul_self X).pow _).eq,
        ((Matrix.isHermitian_mul_conjTranspose_self X).pow _).eq, ← pow_add, ← pow_add,
        ← two_mul, ← pow_succ', trace_mul_pow_comm X Xᴴ] at h4
      rw [← pow_mul, ← pow_succ', h2] at h1
      linarith
    · have h1 := ihS (A * B)
      have h2 : (((A * B)ᴴ * (A * B)) ^ 2 ^ j).trace = ((A ^ 2 * B ^ 2) ^ 2 ^ j).trace := by
        rw [show (A * B)ᴴ * (A * B) = B * (A ^ 2 * B) by
          rw [Matrix.conjTranspose_mul, hA.isHermitian.eq, hB.isHermitian.eq, pow_two]
          simp only [Matrix.mul_assoc], trace_mul_pow_comm, Matrix.mul_assoc, ← pow_two]
      have h3 := ihT (A ^ 2) (B ^ 2) (hA.pow 2) (hB.pow 2)
      rw [← pow_mul, ← pow_mul, ← pow_succ'] at h3
      rw [h2] at h1
      exact h1.trans h3

variable [DecidableEq n]

/-- For positive semidefinite $\mathbf{A}$, $\mathbf{B}$ and $m = 2^k$,
$\operatorname{Re} \operatorname{tr} (\mathbf{A}\mathbf{B})^m
\le \operatorname{Re} \operatorname{tr}(\mathbf{A}^m\mathbf{B}^m)$. With the Lie product formula
this gives the Golden–Thompson inequality.
[Bhatia1997, §IX.2]. -/
theorem _root_.Matrix.PosSemidef.re_trace_mul_pow_two_pow_le {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (k : ℕ) :
    RCLike.re ((A * B) ^ 2 ^ k).trace ≤ RCLike.re (A ^ 2 ^ k * B ^ 2 ^ k).trace :=
  (re_trace_pow_two_pow_le_aux k).2 A B hA hB

/-- Apply the Euler power limit to the product of two exponential curves. -/
private theorem tendsto_exp_smul_mul_exp_smul_pow_aux {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]
    [NormedAlgebra 𝕜 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (H K : 𝔸) :
    Tendsto (fun k : ℕ => (exp ((k : 𝕜)⁻¹ • H) * exp ((k : 𝕜)⁻¹ • K)) ^ k) atTop
      (𝓝 (exp (H + K))) := by
  have hd : HasDerivAt (fun t : 𝕜 => exp (t • H) * exp (t • K)) (H + K) 0 := by
    simpa only [Pi.mul_def, zero_smul, NormedSpace.exp_zero, one_mul, mul_one] using
      (hasDerivAt_exp_smul_const H (0 : 𝕜)).mul (hasDerivAt_exp_smul_const K (0 : 𝕜))
  exact hd.tendsto_pow_inv_nat (by simp)

/-- **The Lie product formula** for matrices:
$(\exp(\mathbf{H}/k)\exp(\mathbf{K}/k))^k \to \exp(\mathbf{H} + \mathbf{K})$ as $k \to \infty$,
for any two square matrices over an `RCLike` field.
[Bhatia1997, §IX.1].
Result: lie-product-formula -/
theorem tendsto_exp_smul_mul_exp_smul_pow (H K : Matrix n n 𝕜) :
    Tendsto (fun k : ℕ => (exp ((k : 𝕜)⁻¹ • H) * exp ((k : 𝕜)⁻¹ • K)) ^ k) atTop
      (𝓝 (exp (H + K))) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact tendsto_const_nhds.congr fun _ => Subsingleton.elim _ _
  open scoped Matrix.Norms.Operator in
  exact tendsto_exp_smul_mul_exp_smul_pow_aux (𝕜 := 𝕜) H K

/-- **The Golden–Thompson inequality.** For Hermitian $\mathbf{H}$ and $\mathbf{K}$,
$$\operatorname{Re} \operatorname{tr} \exp(\mathbf{H} + \mathbf{K})
  \le \operatorname{Re} \operatorname{tr}(\exp(\mathbf{H})\exp(\mathbf{K})) \,.$$
[Bhatia1997, §IX.3]; [Tropp2015, §3.1 notes].
Result: golden-thompson -/
theorem _root_.Matrix.IsHermitian.re_trace_exp_add_le {H K : Matrix n n 𝕜} (hH : H.IsHermitian)
    (hK : K.IsHermitian) :
    RCLike.re (exp (H + K)).trace ≤ RCLike.re (exp H * exp K).trace := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Matrix.trace_eq_zero_of_isEmpty, Matrix.trace_eq_zero_of_isEmpty]
  have hlim : Tendsto (fun k : ℕ => RCLike.re ((exp (((2 ^ k : ℕ) : 𝕜)⁻¹ • H) *
      exp (((2 ^ k : ℕ) : 𝕜)⁻¹ • K)) ^ 2 ^ k).trace) atTop
        (𝓝 (RCLike.re (exp (H + K)).trace)) :=
    ((RCLike.continuous_re.comp (continuous_id.matrix_trace)).tendsto _).comp
      ((tendsto_exp_smul_mul_exp_smul_pow H K).comp
        (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℕ) < 2)))
  refine le_of_tendsto' hlim fun k => ?_
  have hc : IsSelfAdjoint (((2 ^ k : ℕ) : 𝕜)⁻¹) := by
    rw [IsSelfAdjoint, star_inv₀, star_natCast]
  have hsmul : ∀ M : Matrix n n 𝕜, exp (((2 ^ k : ℕ) : 𝕜)⁻¹ • M) ^ 2 ^ k = exp M := fun M => by
    rw [← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (pow_pos two_pos k).ne'), one_smul]
  have h := (hH.smul hc).posDef_exp.posSemidef.re_trace_mul_pow_two_pow_le
    (hK.smul hc).posDef_exp.posSemidef k
  rwa [hsmul, hsmul] at h

/-- The Golden–Thompson inequality with a logarithm: for Hermitian $\mathbf{H}$ and positive
definite $\mathbf{X}$, $\operatorname{Re} \operatorname{tr} \exp(\mathbf{H} + \log(\mathbf{X}))
\le \operatorname{Re} \operatorname{tr}(\exp(\mathbf{H})\mathbf{X})$. -/
theorem _root_.Matrix.PosDef.re_trace_exp_add_cfc_log_le {H X : Matrix n n 𝕜}
    (hH : H.IsHermitian) (hX : X.PosDef) :
    RCLike.re (exp (H + cfc Real.log X)).trace ≤ RCLike.re (exp H * X).trace := by
  have h := Matrix.IsHermitian.re_trace_exp_add_le hH
    (cfc_predicate Real.log X : IsSelfAdjoint (cfc Real.log X))
  rwa [hX.exp_cfc_log] at h

end NLAlib
