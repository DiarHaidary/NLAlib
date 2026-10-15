/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import NLAlib.ForMathlib.LinearAlgebra.Matrix.Trace
public import NLAlib.Matrix.Functions.HermitianCalculus

/-!
# The exponential and the logarithm of a Hermitian matrix

The matrix exponential $\exp(\mathbf{A})$ is Mathlib's `NormedSpace.exp`; for a Hermitian matrix
it is the functional calculus `cfc Real.exp`. The logarithm $\log(\mathbf{A})$ of a positive
definite matrix is `cfc Real.log`. This file gives the bridge, the order facts
($\mathbf{I} + \mathbf{A} \preceq \exp(\mathbf{A})$, comparison of $\exp$ with polynomials on the
spectrum), the norm bound $\|\exp(\mathbf{A})\|_2 \le e^{\|\mathbf{A}\|_2}$, and the properties of
the trace exponential $\operatorname{tr} \exp(\mathbf{A})$ (in Lean the real part of the trace)
used by the matrix Laplace transform method: its expression through the eigenvalues, its bounds by
the largest eigenvalue, and its behaviour under shifts and unitary conjugation.

## Main results

* `Matrix.IsHermitian.exp_eq_cfc`: the bridge; `Matrix.IsHermitian.exp_cfc`:
  $\exp(f(\mathbf{A})) = (e^{f})(\mathbf{A})$.
* `Matrix.IsHermitian.posDef_exp`, `Matrix.IsHermitian.cfc_log_exp`, `Matrix.PosDef.exp_cfc_log`.
* `Matrix.IsHermitian.one_add_le_exp`.
* `NLAlib.specNorm_exp_le`: $\|\exp(\mathbf{A})\|_2 \le e^{\|\mathbf{A}\|_2}$ for every square
  matrix.
* `Matrix.IsHermitian.specNorm_exp`: $\|\exp(\mathbf{A})\|_2 = e^{\lambda_0(\mathbf{A})}$ for
  Hermitian $\mathbf{A}$, and `NLAlib.specNorm_exp_sum_le_prod`:
  $\|\exp(\sum_k \mathbf{A}_k)\|_2 \le \prod_k \|\exp(\mathbf{A}_k)\|_2$ for Hermitian
  $\mathbf{A}_k$.
* `Matrix.IsHermitian.re_trace_exp`:
  $\operatorname{tr} \exp(\mathbf{A}) = \sum_i e^{\lambda_i(\mathbf{A})}$;
  `Matrix.IsHermitian.re_trace_exp_nonneg`, `Matrix.IsHermitian.re_trace_exp_pos`: its sign.
* `Matrix.IsHermitian.exp_eigenvalue_zero_le_re_trace_exp`:
  $e^{\lambda_0(\mathbf{A})} \le \operatorname{tr} \exp(\mathbf{A})$.
* `Matrix.IsHermitian.re_trace_exp_le_card_mul_exp`:
  $\operatorname{tr} \exp(\mathbf{A}) \le \lvert n \rvert e^{\lambda_0(\mathbf{A})}$.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open NormedSpace (exp)

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### The bridge -/

/-- The exponential of a real number, seen in $\Bbbk$. -/
private theorem exp_ofReal (x : ℝ) : exp ((x : ℝ) : 𝕜) = ((Real.exp x : ℝ) : 𝕜) := by
  have h := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := 𝕜) x
  rw [RCLike.algebraMap_eq_ofReal] at h
  rw [← h, Real.exp_eq_exp_ℝ]

/-- The exponential of a real diagonal matrix. -/
private theorem exp_diagonal_ofReal (d : n → ℝ) :
    exp (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) =
      Matrix.diagonal fun i => ((Real.exp (d i) : ℝ) : 𝕜) := by
  rw [Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp]
  exact exp_ofReal (d i)

/-- The exponential commutes with unitary conjugation:
$\exp(\mathbf{U}\mathbf{A}\mathbf{U}^{\mathsf{H}})
= \mathbf{U}\exp(\mathbf{A})\mathbf{U}^{\mathsf{H}}$
for $\mathbf{U}$ with orthonormal columns and as many columns as rows.
Port of `NLAlib.matrixExp_unitary_conj`, there over $\mathbb{C}$. -/
theorem exp_mul_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r] {U : Matrix n r 𝕜}
    (hU : HasOrthonormalCols U) (hr : Fintype.card r = Fintype.card n) (A : Matrix r r 𝕜) :
    exp (U * A * Uᴴ) = U * exp A * Uᴴ := by
  have hUU : U * Uᴴ = 1 := hU.mul_conjTranspose_self_of_card_eq hr.symm
  let f : Matrix r r 𝕜 →+* Matrix n n 𝕜 :=
    { toFun := fun M => U * M * Uᴴ
      map_one' := by rw [Matrix.mul_one, hUU]
      map_mul' := fun M N => by simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]
      map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
      map_add' := fun M N => by rw [Matrix.mul_add, Matrix.add_mul] }
  have hf : Continuous f :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h : f (exp A) = exp (f A) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.map_exp f hf A
  exact h.symm

/-- The exponential of a unitary diagonalisation:
$\exp(\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}})
= \mathbf{U}\exp(\mathbf{D})\mathbf{U}^{\mathsf{H}}$
for a real diagonal $\mathbf{D}$ and $\mathbf{U}$ with orthonormal columns and as many columns as
rows; $\exp(\mathbf{D})$ is diagonal with entries $e^{\mathbf{D}_{i,i}}$. -/
theorem exp_mul_diagonal_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix n r 𝕜} (hU : HasOrthonormalCols U) (hr : Fintype.card r = Fintype.card n)
    (d : r → ℝ) :
    exp (U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) =
      U * Matrix.diagonal (fun i => ((Real.exp (d i) : ℝ) : 𝕜)) * Uᴴ := by
  rw [exp_mul_mul_conjTranspose hU hr, exp_diagonal_ofReal]

/-- **The exponential of a Hermitian matrix through the functional calculus.**
Port of `NLAlib.matrixExp_smul_eq_cfc`, at $s = 1$. -/
theorem _root_.Matrix.IsHermitian.exp_eq_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    exp A = cfc Real.exp A := by
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  rw [cfc_eq_mul_diagonal_mul_conjTranspose hU hr hAU Real.exp]
  conv_lhs => rw [hAU]
  exact exp_mul_diagonal_mul_conjTranspose hU hr _

/-- The exponential of a function of a Hermitian matrix is the function composed with the real
exponential: $\exp(f(\mathbf{B})) = (e^{f})(\mathbf{B})$, in terms of `cfc`. -/
theorem _root_.Matrix.IsHermitian.exp_cfc {B : Matrix n n 𝕜} (hB : B.IsHermitian) (f : ℝ → ℝ) :
    exp (cfc f B) = cfc (fun x => Real.exp (f x)) B := by
  have hH : (cfc f B).IsHermitian := cfc_predicate f B
  rw [hH.exp_eq_cfc]
  exact (cfc_comp' Real.exp f B ((B.finite_real_spectrum.image _).continuousOn _)
    (B.finite_real_spectrum.continuousOn _) hB).symm

/-- A scalar shift factors out of the exponential:
$\exp(\mathbf{A} + t\mathbf{I}) = e^t \exp(\mathbf{A})$ for real $t$. -/
theorem exp_add_real_smul_one (A : Matrix n n 𝕜) (t : ℝ) :
    exp (A + t • (1 : Matrix n n 𝕜)) = Real.exp t • exp A := by
  have hc : Commute A (t • (1 : Matrix n n 𝕜)) := (Commute.one_right A).smul_right t
  have ht : exp (t • (1 : Matrix n n 𝕜)) = Real.exp t • (1 : Matrix n n 𝕜) := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.real_smul_eq_coe_smul (K := 𝕜),
      Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal]
    exact exp_diagonal_ofReal fun _ => t
  rw [Matrix.exp_add_of_commute A _ hc, ht, Matrix.mul_smul, Matrix.mul_one]

/-- The exponential of a block diagonal matrix:
$\exp \begin{bmatrix} \mathbf{A} & \mathbf{0} \\ \mathbf{0} & \mathbf{B} \end{bmatrix}
= \begin{bmatrix} \exp(\mathbf{A}) & \mathbf{0} \\ \mathbf{0} & \exp(\mathbf{B}) \end{bmatrix}$. -/
theorem exp_fromBlocks_diagonal (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    exp (Matrix.fromBlocks A 0 0 B) = Matrix.fromBlocks (exp A) 0 0 (exp B) := by
  let f : Matrix m m 𝕜 × Matrix n n 𝕜 →+* Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
    { toFun := fun p => Matrix.fromBlocks p.1 0 0 p.2
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Matrix.fromBlocks_multiply, Matrix.mul_zero,
          Matrix.zero_mul, add_zero, zero_add]
      map_zero' := Matrix.fromBlocks_zero
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.fromBlocks_add, add_zero] }
  have hf : Continuous f :=
    Continuous.matrix_fromBlocks continuous_fst continuous_const continuous_const continuous_snd
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.map_exp f hf (A, B)
  open scoped Matrix.Norms.Operator in
  have h1 : exp (A, B) = (exp A, exp B) := Prod.ext (Prod.fst_exp _) (Prod.snd_exp _)
  exact h.symm.trans (congrArg f h1)

/-! ### Positivity and the logarithm -/

/-- **The exponential of a Hermitian matrix is positive definite.**
Port of `NLAlib.posDef_matrixExp_and_matrixLog_matrixExp`, first half. -/
theorem _root_.Matrix.IsHermitian.posDef_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (exp A).PosDef := by
  rw [hA.exp.posDef_iff_eigenvalue_pos]
  intro k hk
  rw [hA.exp_eq_cfc, hA.eigenvalue_cfc_of_monotoneOn (Real.exp_monotone.monotoneOn Set.univ)
    (Set.subset_univ _) hk]
  exact Real.exp_pos _

/-- The logarithm inverts the exponential on Hermitian matrices:
$\log(\exp(\mathbf{A})) = \mathbf{A}$.
Port of `NLAlib.posDef_matrixExp_and_matrixLog_matrixExp`, second half. -/
theorem _root_.Matrix.IsHermitian.cfc_log_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    cfc Real.log (exp A) = A := by
  have hsa : IsSelfAdjoint A := hA
  rw [hA.exp_eq_cfc, ← cfc_comp' Real.log Real.exp A
    ((A.finite_real_spectrum.image _).continuousOn _) (A.finite_real_spectrum.continuousOn _) hsa]
  conv_rhs => rw [← cfc_id' ℝ A hsa]
  exact cfc_congr fun x _ => Real.log_exp x

/-- The exponential inverts the logarithm on positive definite matrices:
$\exp(\log(\mathbf{A})) = \mathbf{A}$. -/
theorem _root_.Matrix.PosDef.exp_cfc_log {A : Matrix n n 𝕜} (hA : A.PosDef) :
    exp (cfc Real.log A) = A := by
  have hsa : IsSelfAdjoint A := hA.isHermitian
  have hL : (cfc Real.log A).IsHermitian := cfc_predicate Real.log A
  rw [hL.exp_eq_cfc, ← cfc_comp' Real.exp Real.log A
    ((A.finite_real_spectrum.image _).continuousOn _) (A.finite_real_spectrum.continuousOn _) hsa]
  conv_rhs => rw [← cfc_id' ℝ A hsa]
  exact cfc_congr fun x hx => Real.exp_log (hA.spectrum_subset_Ioi hx)

/-- Eigenvalues of the exponential: for Hermitian $\mathbf{A}$ and $k < \lvert n \rvert$,
$\lambda_k(\exp(\mathbf{A})) = e^{\lambda_k(\mathbf{A})}$. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {k : ℕ} (hk : k < Fintype.card n) : eigenvalue (exp A) k = Real.exp (eigenvalue A k) := by
  rw [hA.exp_eq_cfc]
  exact hA.eigenvalue_cfc_of_monotoneOn (Real.exp_monotone.monotoneOn Set.univ)
    (Set.subset_univ _) hk

/-! ### Order -/

/-- **The exponential lies above its tangent at zero**:
$\mathbf{I} + \mathbf{A} \preceq \exp(\mathbf{A})$ for Hermitian $\mathbf{A}$.
[Tropp2015, §2.1]. Port of `NLAlib.one_add_le_matrixExp_of_isHermitian`. -/
theorem _root_.Matrix.IsHermitian.one_add_le_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    1 + A ≤ exp A := by
  have hsa : IsSelfAdjoint A := hA
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ A) := fun g =>
    A.finite_real_spectrum.continuousOn g
  have h1 : cfc (fun x : ℝ => 1 + x) A = 1 + A := by
    rw [cfc_const_add 1 (fun x => x) A (hcont _) hsa, cfc_id' ℝ A hsa, map_one]
  rw [hA.exp_eq_cfc, ← h1]
  exact cfc_mono (fun x _ => by linarith [Real.add_one_le_exp x]) (hcont _) (hcont _)

/-- **The transfer rule for the exponential.** If $e^{\theta x} \le 1 + \theta x + c x^2$ for
every $x \in [a, b]$ and $a\mathbf{I} \preceq \mathbf{A} \preceq b\mathbf{I}$, then
$\exp(\theta\mathbf{A}) \preceq \mathbf{I} + \theta\mathbf{A} + c\mathbf{A}^2$.
[Tropp2015, §2.1 and §6.6].
Port of `NLAlib.matrixExp_smul_le_one_add_smul_add_smul_sq_of_spectrum_le`. -/
theorem exp_smul_le_one_add_smul_add_smul_sq {A : Matrix n n 𝕜} {a b θ c : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜))
    (h : ∀ x ∈ Set.Icc a b, Real.exp (θ * x) ≤ 1 + θ * x + c * x ^ 2) :
    exp (θ • A) ≤ 1 + θ • A + c • A ^ 2 := by
  have hA := isHermitian_of_le_smul_one h₂
  have hsa : IsSelfAdjoint A := hA
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ A) := fun g =>
    A.finite_real_spectrum.continuousOn g
  have hθA : θ • A = cfc (fun x : ℝ => θ * x) A := by
    rw [cfc_const_mul θ (fun x => x) A (hcont _), cfc_id' ℝ A hsa]
  have hH : (θ • A).IsHermitian := by
    rw [hθA]
    exact cfc_predicate _ A
  have hL : exp (θ • A) = cfc (fun x : ℝ => Real.exp (θ * x)) A := by
    rw [hH.exp_eq_cfc, hθA, ← cfc_comp' Real.exp (fun x => θ * x) A
      ((A.finite_real_spectrum.image _).continuousOn _) (hcont _) hsa]
  have hR : 1 + θ • A + c • A ^ 2 = cfc (fun x : ℝ => 1 + θ * x + c * x ^ 2) A := by
    rw [cfc_add A (fun x : ℝ => 1 + θ * x) (fun x : ℝ => c * x ^ 2) (hcont _) (hcont _),
      cfc_const_add 1 (fun x : ℝ => θ * x) A (hcont _) hsa,
      cfc_const_mul c (fun x : ℝ => x ^ 2) A (hcont _),
      cfc_pow (fun x : ℝ => x) 2 A (hcont _) hsa, cfc_id' ℝ A hsa, ← hθA, map_one]
  rw [hL, hR]
  exact cfc_le_cfc_of_forall_mem_Icc h₁ h₂ h

/-- **The logarithm lies below its tangent at one**:
$\log(\mathbf{I} + \mathbf{A}) \preceq \mathbf{A}$ for positive semidefinite $\mathbf{A}$. This
bounds matrix cumulant generating functions in the Bernstein and Bennett inequalities.
[Tropp2015, §6.6]. -/
theorem _root_.Matrix.PosSemidef.cfc_log_one_add_le {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    cfc Real.log (1 + A) ≤ A := by
  have hsa : IsSelfAdjoint A := hA.isHermitian
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ A) := fun g =>
    A.finite_real_spectrum.continuousOn g
  have h1 : 1 + A = cfc (fun x : ℝ => 1 + x) A := by
    rw [cfc_const_add 1 (fun x => x) A (hcont _) hsa, cfc_id' ℝ A hsa, map_one]
  rw [h1, ← cfc_comp' Real.log (fun x : ℝ => 1 + x) A
    ((A.finite_real_spectrum.image _).continuousOn _) (hcont _) hsa]
  conv_rhs => rw [← cfc_id' ℝ A hsa]
  refine cfc_mono (fun x hx => ?_) (hcont _) (hcont _)
  have hx0 : (0 : ℝ) ≤ x := hA.spectrum_subset_Ici hx
  linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)]

/-! ### The spectral norm -/

/-- The spectral norm of the exponential of any square matrix is at most the exponential of its
spectral norm: $\|\exp(\mathbf{A})\|_2 \le e^{\|\mathbf{A}\|_2}$, by the exponential series. -/
theorem specNorm_exp_le (A : Matrix n n 𝕜) : specNorm (exp A) ≤ Real.exp (specNorm A) := by
  rcases isEmpty_or_nonempty n with h | h
  · rw [Subsingleton.elim (exp A) 0, specNorm_zero]
    exact (Real.exp_pos _).le
  have hr : HasSum (fun k : ℕ => ((k.factorial : ℝ))⁻¹ • specNorm A ^ k)
      (Real.exp (specNorm A)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (specNorm A)
  open scoped Matrix.Norms.L2Operator in
  refine (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) A).norm_le_of_bounded hr fun k => ?_
  rw [norm_smul, norm_inv, RCLike.norm_natCast, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  cases k with
  | zero =>
    rw [pow_zero, pow_zero]
    exact specNorm_one_le
  | succ k => exact norm_pow_le' A k.succ_pos

/-- **The spectral norm of the exponential of a Hermitian matrix** is the exponential of its
largest eigenvalue: $\|\exp(\mathbf{A})\|_2 = e^{\lambda_0(\mathbf{A})}$, on a nonempty index type
(for a matrix of size zero the left side is $0$ and the right side $1$). -/
theorem _root_.Matrix.IsHermitian.specNorm_exp [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : specNorm (exp A) = Real.exp (eigenvalue A 0) := by
  rw [hA.posDef_exp.posSemidef.specNorm_eq_eigenvalue_zero, hA.eigenvalue_exp Fintype.card_pos]

/-- **The exponential of a sum of Hermitian matrices** is bounded in spectral norm by the product
of the norms of the exponentials: for a finite set $s$ of indices and Hermitian
$\mathbf{A}_k$, $k \in s$,
$$\Bigl\|\exp\Bigl(\sum_{k \in s} \mathbf{A}_k\Bigr)\Bigr\|_2
  \le \prod_{k \in s} \|\exp(\mathbf{A}_k)\|_2 \,.$$
The matrices need not commute: the largest eigenvalue is subadditive. Unlike the bound
$\prod_k e^{\|\mathbf{A}_k\|_2}$ from `NLAlib.specNorm_exp_le`, the right side is small when the
$\mathbf{A}_k$ are very negative, which is what the integrability of the matrix Laplace transform
bound needs.
Port of `NLAlib.norm_matrixExp_sum_le_prod`, there over $\mathbb{C}$ with the weaker factors
$1 + \|\exp(\mathbf{A}_k)\|$. -/
theorem specNorm_exp_sum_le_prod {ι : Type*} (s : Finset ι) {A : ι → Matrix n n 𝕜}
    (hA : ∀ k ∈ s, (A k).IsHermitian) :
    specNorm (exp (∑ k ∈ s, A k)) ≤ ∏ k ∈ s, specNorm (exp (A k)) := by
  rcases isEmpty_or_nonempty n with h | h
  · rw [Subsingleton.elim (exp (∑ k ∈ s, A k)) 0, specNorm_zero]
    exact Finset.prod_nonneg fun k _ => specNorm_nonneg _
  have hS : (∑ k ∈ s, A k).IsHermitian := isSelfAdjoint_sum s hA
  rw [hS.specNorm_exp, Finset.prod_congr rfl fun k hk => (hA k hk).specNorm_exp, ← Real.exp_sum,
    Real.exp_le_exp, ← hS.le_smul_one_iff, Finset.sum_smul]
  exact Finset.sum_le_sum fun k hk => (hA k hk).le_eigenvalue_zero_smul_one

/-! ### The trace exponential -/

/-- **The trace of the exponential** of a Hermitian matrix is the sum of the exponentials of its
eigenvalues: $\operatorname{Re} \operatorname{tr} \exp(\mathbf{A})
= \sum_{i < \lvert n \rvert} e^{\lambda_i(\mathbf{A})}$.
Port of `NLAlib.traceExp_smul_eq_sum`. -/
theorem _root_.Matrix.IsHermitian.re_trace_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.re (exp A).trace = ∑ i ∈ Finset.range (Fintype.card n), Real.exp (eigenvalue A i) := by
  rw [hA.exp_eq_cfc]
  exact hA.re_trace_cfc Real.exp

/-- The trace exponential of a Hermitian matrix of positive size is positive:
$\operatorname{Re} \operatorname{tr} \exp(\mathbf{A}) > 0$.
Port of `NLAlib.traceExp_pos_of_isHermitian`. -/
theorem _root_.Matrix.IsHermitian.re_trace_exp_pos [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : 0 < RCLike.re (exp A).trace := by
  rw [hA.re_trace_exp]
  exact Finset.sum_pos (fun i _ => Real.exp_pos _)
    (Finset.nonempty_range_iff.mpr Fintype.card_ne_zero)

/-- The trace exponential of a Hermitian matrix is nonnegative, for every size:
$\operatorname{Re} \operatorname{tr} \exp(\mathbf{A}) \ge 0$ (`0` for an empty index type;
`Matrix.IsHermitian.re_trace_exp_pos` for positive size). -/
theorem _root_.Matrix.IsHermitian.re_trace_exp_nonneg {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    0 ≤ RCLike.re (exp A).trace := by
  rw [hA.re_trace_exp]
  exact Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le

/-- **The largest eigenvalue is controlled by the trace exponential**: for Hermitian $\mathbf{A}$
of positive size,
$e^{\lambda_0(\mathbf{A})} \le \operatorname{Re} \operatorname{tr} \exp(\mathbf{A})$.
This is the first step of the matrix Laplace transform method.
[Tropp2015, Proposition 3.2.1].
Port of `NLAlib.exp_mul_lambdaMax_lambdaMin_le_traceExp_smul`. -/
theorem _root_.Matrix.IsHermitian.exp_eigenvalue_zero_le_re_trace_exp [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Real.exp (eigenvalue A 0) ≤ RCLike.re (exp A).trace := by
  rw [hA.exp_eq_cfc]
  exact hA.apply_eigenvalue_zero_le_re_trace_cfc fun x _ => (Real.exp_pos x).le

/-- The trace exponential is at most the dimension times the exponential of the largest
eigenvalue: $\operatorname{Re} \operatorname{tr} \exp(\mathbf{A})
\le \lvert n \rvert \, e^{\lambda_0(\mathbf{A})}$ for Hermitian $\mathbf{A}$.
Port of `NLAlib.traceExp_smul_le_mul_exp_mul_norm`, there with the norm. -/
theorem _root_.Matrix.IsHermitian.re_trace_exp_le_card_mul_exp {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    RCLike.re (exp A).trace ≤ Fintype.card n * Real.exp (eigenvalue A 0) := by
  rw [hA.re_trace_exp]
  have h := Finset.sum_le_card_nsmul (Finset.range (Fintype.card n))
    (fun i => Real.exp (eigenvalue A i)) (Real.exp (eigenvalue A 0)) fun i hi =>
      Real.exp_le_exp.mpr (hA.eigenvalue_le_eigenvalue (Nat.zero_le i) (Finset.mem_range.mp hi))
  rwa [Finset.card_range, nsmul_eq_mul] at h

/-- The trace exponential is invariant under unitary conjugation:
$\operatorname{Re} \operatorname{tr} \exp(\mathbf{U}\mathbf{A}\mathbf{U}^{\mathsf{H}})
= \operatorname{Re} \operatorname{tr} \exp(\mathbf{A})$ for $\mathbf{U}$ with orthonormal columns
and as many columns as rows.
Port of `NLAlib.traceExp_unitary_conj`. -/
theorem re_trace_exp_mul_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix n r 𝕜} (hU : HasOrthonormalCols U) (hr : Fintype.card r = Fintype.card n)
    (A : Matrix r r 𝕜) : RCLike.re (exp (U * A * Uᴴ)).trace = RCLike.re (exp A).trace := by
  rw [exp_mul_mul_conjTranspose hU hr, Matrix.trace_mul_cycle, hU.conjTranspose_mul_self,
    Matrix.one_mul]

/-- A scalar shift factors out of the trace exponential:
$\operatorname{Re} \operatorname{tr} \exp(\mathbf{A} + t\mathbf{I})
= e^t \operatorname{Re} \operatorname{tr} \exp(\mathbf{A})$.
Port of `NLAlib.traceExp_add_smul_one_eq_exp_mul`. -/
theorem re_trace_exp_add_real_smul_one (A : Matrix n n 𝕜) (t : ℝ) :
    RCLike.re (exp (A + t • (1 : Matrix n n 𝕜))).trace = Real.exp t * RCLike.re (exp A).trace := by
  rw [exp_add_real_smul_one, Matrix.trace_smul, RCLike.smul_re]

/-- The trace exponential of a block diagonal matrix with diagonal blocks $\mathbf{A}$,
$\mathbf{B}$ is the sum of the two trace exponentials.
Port of the block case used in `NLAlib.intrinsicDimension_fromBlocks`. -/
theorem re_trace_exp_fromBlocks_diagonal (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    RCLike.re (exp (Matrix.fromBlocks A 0 0 B)).trace =
      RCLike.re (exp A).trace + RCLike.re (exp B).trace := by
  rw [exp_fromBlocks_diagonal, Matrix.trace_fromBlocks, map_add]

/-- The trace exponential $\mathbf{A} \mapsto \operatorname{Re} \operatorname{tr} \exp(\mathbf{A})$
is continuous. Port of `NLAlib.continuous_traceExp`. -/
theorem continuous_re_trace_exp :
    Continuous fun A : Matrix n n 𝕜 => RCLike.re (exp A).trace := by
  have h : Continuous (exp : Matrix n n 𝕜 → Matrix n n 𝕜) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.exp_continuous
  exact RCLike.continuous_re.comp h.matrix_trace

end NLAlib
