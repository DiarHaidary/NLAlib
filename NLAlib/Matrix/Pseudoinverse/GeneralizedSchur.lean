/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.SchurComplement
public import NLAlib.Matrix.Pseudoinverse.Pinv

/-!
# The generalized Schur complement

For a Hermitian block matrix $\begin{bmatrix} \mathbf{A} & \mathbf{B} \\ \mathbf{B}^{\mathsf{H}} &
\mathbf{C} \end{bmatrix}$ whose leading block may be singular, the generalized Schur complement is
$\mathbf{C} - \mathbf{B}^{\mathsf{H}}\mathbf{A}^{+}\mathbf{B}$. It has no definition; its spelling
is `C - Bᴴ * pinv A * B`. The criteria here are the pseudoinverse forms of the statements in
`NLAlib.Matrix.Basic.SchurComplement`, which are stated with an arbitrary solution $\mathbf{X}$ of
$\mathbf{A}\mathbf{X} = \mathbf{B}$; here $\mathbf{X} = \mathbf{A}^{+}\mathbf{B}$.

## Main results

* `NLAlib.posSemidef_fromBlocks_iff_pinv`: Albert's criterion.
* `Matrix.PosSemidef.isLeast_re_quadForm_fromBlocks`: the generalized Schur complement is the
  partial minimum of the quadratic form. -/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m]

/-- `mul_pinv_mul_eq_of_range_le` in the association $\mathbf{A}\mathbf{X} = \mathbf{B}$ with
$\mathbf{X} = \mathbf{A}^{+}\mathbf{B}$, which the criteria of `NLAlib.Matrix.Basic.SchurComplement`
take. -/
private theorem mul_pinv_mul_eq_aux [Fintype n] {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    (h : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin) : A * (pinv A * B) = B := by
  rw [← Matrix.mul_assoc]
  exact mul_pinv_mul_eq_of_range_le h

/-- In a positive semidefinite block matrix $\begin{bmatrix} \mathbf{A} & \mathbf{B} \\
\mathbf{B}^{\mathsf{H}} & \mathbf{C} \end{bmatrix}$, $\mathbf{A}\mathbf{A}^{+}\mathbf{B} =
\mathbf{B}$.
-/
theorem _root_.Matrix.PosSemidef.mul_pinv_mul_eq_of_fromBlocks [Finite n] {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    A * pinv A * B = B := by
  have := Fintype.ofFinite n
  exact mul_pinv_mul_eq_of_range_le (Matrix.PosSemidef.range_le_of_fromBlocks h)

/-- For Hermitian $\mathbf{A}$, the solution $\mathbf{X} = \mathbf{A}^{+}\mathbf{B}$ gives
$\mathbf{X}^{\mathsf{H}}\mathbf{A}\mathbf{X} = \mathbf{B}^{\mathsf{H}}\mathbf{A}^{+}\mathbf{B}$. -/
private theorem conjTranspose_pinv_mul_mul_pinv_mul {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    (hA : A.IsHermitian) : (pinv A * B)ᴴ * A * (pinv A * B) = Bᴴ * pinv A * B := by
  rw [Matrix.conjTranspose_mul, hA.pinv.eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc (pinv A), ← Matrix.mul_assoc (pinv A),
    pinv_mul_mul_pinv]

/-- **Albert's criterion.** The block matrix $\begin{bmatrix} \mathbf{A} & \mathbf{B} \\
\mathbf{B}^{\mathsf{H}} & \mathbf{C} \end{bmatrix}$ is positive semidefinite exactly when
$\mathbf{A}$ is, the columns of $\mathbf{B}$ lie in the column space of $\mathbf{A}$, and the
generalized Schur complement $\mathbf{C} - \mathbf{B}^{\mathsf{H}}\mathbf{A}^{+}\mathbf{B}$ is
positive semidefinite.
[HornJohnson2013, Theorem 7.7.9].
Result: schur-complement-psd, albert-theorem -/
theorem posSemidef_fromBlocks_iff_pinv [Fintype n] {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔
      A.PosSemidef ∧ LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin ∧
        (C - Bᴴ * pinv A * B).PosSemidef := by
  constructor
  · intro h
    have hA : A.PosSemidef := h.submatrix (Sum.inl : m → m ⊕ n)
    have hr := Matrix.PosSemidef.range_le_of_fromBlocks h
    have hS := Matrix.PosSemidef.posSemidef_sub_conjTranspose_mul_mul_of_fromBlocks h
      (mul_pinv_mul_eq_aux hr)
    rw [conjTranspose_pinv_mul_mul_pinv_mul hA.isHermitian] at hS
    exact ⟨hA, hr, hS⟩
  · rintro ⟨hA, hr, hS⟩
    refine posSemidef_fromBlocks_iff_exists.mpr
      ⟨hA, pinv A * B, mul_pinv_mul_eq_aux hr, ?_⟩
    rwa [conjTranspose_pinv_mul_mul_pinv_mul hA.isHermitian]

/-- In a positive semidefinite block matrix $\begin{bmatrix} \mathbf{A} & \mathbf{B} \\
\mathbf{B}^{\mathsf{H}} & \mathbf{C} \end{bmatrix}$ the generalized Schur complement $\mathbf{C} -
\mathbf{B}^{\mathsf{H}}\mathbf{A}^{+}\mathbf{B}$ is positive semidefinite. -/
theorem _root_.Matrix.PosSemidef.posSemidef_sub_conjTranspose_mul_pinv_mul_of_fromBlocks [Finite n]
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) : (C - Bᴴ * pinv A * B).PosSemidef := by
  have := Fintype.ofFinite n
  exact (posSemidef_fromBlocks_iff_pinv.mp h).2.2

/-- **The generalized Schur complement as a partial minimum.** In a positive semidefinite block
matrix $\begin{bmatrix} \mathbf{A} & \mathbf{B} \\ \mathbf{B}^{\mathsf{H}} & \mathbf{C}
\end{bmatrix}$, the real part of the quadratic form of $\mathbf{C} -
\mathbf{B}^{\mathsf{H}}\mathbf{A}^{+}\mathbf{B}$ at $\mathbf{x}$ is the least value, over
$\mathbf{y}$, of the real part of the quadratic form of the block matrix at the stacked vector
$\begin{bmatrix} \mathbf{y} \\ \mathbf{x} \end{bmatrix}$.
[HornJohnson2013, §7.7].
Result: schur-complement-variational -/
theorem _root_.Matrix.PosSemidef.isLeast_re_quadForm_fromBlocks [Fintype n] {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) (x : n → 𝕜) :
    IsLeast
      (Set.range fun y : m → 𝕜 =>
        RCLike.re (quadForm (Matrix.fromBlocks A B Bᴴ C) (Sum.elim y x)))
      (RCLike.re (quadForm (C - Bᴴ * pinv A * B) x)) := by
  have hA : A.PosSemidef := h.submatrix (Sum.inl : m → m ⊕ n)
  have hX : A * (pinv A * B) = B :=
    mul_pinv_mul_eq_aux (Matrix.PosSemidef.range_le_of_fromBlocks h)
  have hS := conjTranspose_pinv_mul_mul_pinv_mul (B := B) hA.isHermitian
  constructor
  · refine ⟨-((pinv A * B) *ᵥ x), ?_⟩
    change RCLike.re (quadForm _ (Sum.elim (-((pinv A * B) *ᵥ x)) x)) = _
    rw [Matrix.IsHermitian.quadForm_fromBlocks_eq_add hA.isHermitian hX, neg_add_cancel,
      quadForm_zero_right,
      zero_add, hS]
  · rintro _ ⟨y, rfl⟩
    have hle := Matrix.PosSemidef.quadForm_sub_conjTranspose_mul_mul_le h hX y x
    rw [hS] at hle
    exact (RCLike.le_iff_re_im.mp hle).1

end NLAlib
