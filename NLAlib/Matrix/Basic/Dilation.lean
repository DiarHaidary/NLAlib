/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The Hermitian dilation

`NLAlib.dilation A` is the Hermitian block matrix with $\mathbf{A}$ and $\mathbf{A}^{\mathsf{H}}$
off the diagonal. It carries statements about Hermitian matrices (eigenvalue perturbation, matrix
concentration) to rectangular matrices: its eigenvalues are plus and minus the singular values of
$\mathbf{A}$, and its spectral norm is that of $\mathbf{A}$. Those two facts are proved with the
spectral theory; this file has the algebra.

## Main definitions

* `NLAlib.dilation`:
  $\begin{bmatrix} \mathbf{0} & \mathbf{A} \\ \mathbf{A}^{\mathsf{H}} & \mathbf{0} \end{bmatrix}$.

## Main results

* `NLAlib.isHermitian_dilation`: the dilation is Hermitian.
* `NLAlib.dilation_mul_dilation`: the square is block diagonal with blocks
  $\mathbf{A}\mathbf{A}^{\mathsf{H}}$, $\mathbf{A}^{\mathsf{H}}\mathbf{A}$.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}

/-- The **Hermitian dilation** of a rectangular matrix $\mathbf{A}$: the block matrix
$\begin{bmatrix} \mathbf{0} & \mathbf{A} \\ \mathbf{A}^{\mathsf{H}} & \mathbf{0} \end{bmatrix}$,
with row and column index type `m ⊕ n`. [Tropp2015, §2.1.16]. -/
def dilation (A : Matrix m n 𝕜) : Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
  Matrix.fromBlocks 0 A Aᴴ 0

/-- The dilation of $\mathbf{A}$ unfolds to the block matrix
$\begin{bmatrix} \mathbf{0} & \mathbf{A} \\ \mathbf{A}^{\mathsf{H}} & \mathbf{0} \end{bmatrix}$
built with `Matrix.fromBlocks`. -/
theorem dilation_def (A : Matrix m n 𝕜) : dilation A = Matrix.fromBlocks 0 A Aᴴ 0 :=
  rfl

/-- The Hermitian dilation is Hermitian. -/
theorem isHermitian_dilation (A : Matrix m n 𝕜) : (dilation A).IsHermitian := by
  rw [Matrix.IsHermitian, dilation, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_conjTranspose]

/-- The Hermitian dilation equals its conjugate transpose. -/
@[simp]
theorem conjTranspose_dilation (A : Matrix m n 𝕜) : (dilation A)ᴴ = dilation A :=
  isHermitian_dilation A

/-- The dilation of the zero matrix is zero. -/
@[simp]
theorem dilation_zero : dilation (0 : Matrix m n 𝕜) = 0 := by
  rw [dilation, Matrix.conjTranspose_zero, Matrix.fromBlocks_zero]

/-- The dilation is additive. -/
theorem dilation_add (A B : Matrix m n 𝕜) : dilation (A + B) = dilation A + dilation B := by
  rw [dilation, dilation, dilation, Matrix.fromBlocks_add, Matrix.conjTranspose_add, add_zero,
    add_zero]

/-- The dilation commutes with negation. -/
theorem dilation_neg (A : Matrix m n 𝕜) : dilation (-A) = -dilation A := by
  rw [dilation, dilation, Matrix.fromBlocks_neg, Matrix.conjTranspose_neg, neg_zero, neg_zero]

/-- The dilation commutes with subtraction. -/
theorem dilation_sub (A B : Matrix m n 𝕜) : dilation (A - B) = dilation A - dilation B := by
  rw [sub_eq_add_neg, dilation_add, dilation_neg, sub_eq_add_neg]

/-- The dilation commutes with multiplication by a real scalar $c$, written with the real scalar
action (`RCLike.real_smul_eq_coe_smul` converts to and from the action of $c$ as an element of
$\Bbbk$). It is not $\Bbbk$-linear, because $\mathbf{A}^{\mathsf{H}}$ is conjugate-linear in
$\mathbf{A}$. -/
theorem dilation_smul_real (c : ℝ) (A : Matrix m n 𝕜) : dilation (c • A) = c • dilation A := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) c A,
    RCLike.real_smul_eq_coe_smul (K := 𝕜) c (dilation A), dilation, dilation,
    Matrix.fromBlocks_smul, Matrix.conjTranspose_smul, RCLike.star_def, RCLike.conj_ofReal,
    smul_zero, smul_zero]

/-- The dilation commutes with finite sums. -/
theorem dilation_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix m n 𝕜) :
    dilation (∑ i ∈ s, A i) = ∑ i ∈ s, dilation (A i) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, dilation_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, dilation_add, ih]

/-- The dilation is injective. -/
theorem dilation_injective : Function.Injective (dilation : Matrix m n 𝕜 → _) :=
  fun _ _ h => (Matrix.fromBlocks_inj.mp h).2.1

/-- The square of the dilation is block diagonal, with blocks $\mathbf{A}\mathbf{A}^{\mathsf{H}}$
and $\mathbf{A}^{\mathsf{H}}\mathbf{A}$.
[Tropp2015, (2.1.28)]. -/
theorem dilation_mul_dilation [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    dilation A * dilation A = Matrix.fromBlocks (A * Aᴴ) 0 0 (Aᴴ * A) := by
  rw [dilation, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

/-- The dilation acts on a pair $(\mathbf{y}, \mathbf{x})$ by
$(\mathbf{A}\mathbf{x}, \mathbf{A}^{\mathsf{H}}\mathbf{y})$. -/
theorem dilation_mulVec [Fintype m] [Fintype n] (A : Matrix m n 𝕜) (y : m → 𝕜) (x : n → 𝕜) :
    dilation A *ᵥ Sum.elim y x = Sum.elim (A *ᵥ x) (Aᴴ *ᵥ y) := by
  rw [dilation, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.zero_mulVec, Matrix.zero_mulVec, zero_add, add_zero]

end NLAlib
