/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Orthonormal

/-!
# Selection matrices

`NLAlib.selectionMatrix s` is the matrix whose columns are the standard basis vectors
$\mathbf{e}_{s(j)}$. Multiplying by it on the right selects columns, and by its conjugate
transpose on the left selects rows. It exists so that column and row sampling can be passed to
statements that take a matrix (a sketch, a compression
$\mathbf{S}^{\mathsf{H}}\mathbf{A}\mathbf{S}$); where a selection is all that is needed, use
Mathlib's `Matrix.submatrix` directly.

## Main definitions

* `NLAlib.selectionMatrix`: the columns $s(j)$ of the identity matrix.

## Main results

* `NLAlib.mul_selectionMatrix`, `NLAlib.conjTranspose_selectionMatrix_mul`: the bridges to
  `Matrix.submatrix`.
* `NLAlib.hasOrthonormalCols_selectionMatrix`: an injective selection has orthonormal columns.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [DecidableEq n]

/-- The **selection matrix** of a map $s : p \to n$: column $j$ is the standard basis vector
$\mathbf{e}_{s(j)}$. The map $s$ need not be injective. -/
def selectionMatrix (s : p → n) : Matrix n p 𝕜 :=
  (1 : Matrix n n 𝕜).submatrix id s

/-- The selection matrix is a submatrix of the identity (`Matrix.submatrix`). -/
theorem selectionMatrix_eq_submatrix (s : p → n) :
    (selectionMatrix s : Matrix n p 𝕜) = (1 : Matrix n n 𝕜).submatrix id s :=
  rfl

/-- The entries of a selection matrix $\mathbf{S}$: $\mathbf{S}_{i,j} = 1$ if $i = s(j)$ and $0$
otherwise. Port of `NLAlib.transpose_selectionMatrix_apply`. -/
theorem selectionMatrix_apply (s : p → n) (i : n) (j : p) :
    (selectionMatrix s : Matrix n p 𝕜) i j = if i = s j then 1 else 0 := by
  rw [selectionMatrix, Matrix.submatrix_apply, Matrix.one_apply, id]

/-- Right multiplication by a selection matrix selects columns: column $j$ of
$\mathbf{A}\mathbf{S}$ is column $s(j)$ of $\mathbf{A}$.
Port of `NLAlib.mul_selectionMatrix`, there over $\mathbb{R}$ with `Fin`-indexed selections. -/
@[simp]
theorem mul_selectionMatrix [Fintype n] (A : Matrix m n 𝕜) (s : p → n) :
    A * selectionMatrix s = A.submatrix id s :=
  Matrix.mul_submatrix_one (Equiv.refl n) s A

/-- Left multiplication by the conjugate transpose of a selection matrix selects rows: row $j$
of $\mathbf{S}^{\mathsf{H}}\mathbf{A}$ is row $s(j)$ of $\mathbf{A}$.
Port of `NLAlib.transpose_selectionMatrix_mul`. -/
@[simp]
theorem conjTranspose_selectionMatrix_mul [Fintype n] (s : p → n) (A : Matrix n m 𝕜) :
    (selectionMatrix s : Matrix n p 𝕜)ᴴ * A = A.submatrix s id := by
  rw [selectionMatrix, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  exact Matrix.one_submatrix_mul s (Equiv.refl n) A

/-- A compression $\mathbf{S}^{\mathsf{H}}\mathbf{A}\mathbf{S}$ by a selection matrix is a
principal submatrix: its $(i, j)$ entry is $\mathbf{A}_{s(i),s(j)}$. -/
theorem conjTranspose_selectionMatrix_mul_mul_selectionMatrix [Fintype n] (s : p → n)
    (A : Matrix n n 𝕜) :
    (selectionMatrix s : Matrix n p 𝕜)ᴴ * A * selectionMatrix s = A.submatrix s s := by
  rw [conjTranspose_selectionMatrix_mul, mul_selectionMatrix, Matrix.submatrix_submatrix,
    Function.comp_id, Function.id_comp]

/-- Selecting columns of the two frames of a two-sided compression selects the corresponding
block: if $\mathbf{Q}_f$ has columns $f(i)$ of $\mathbf{Q}$ and $\mathbf{W}_g$ columns $g(j)$ of
$\mathbf{W}$, then $\mathbf{Q}_f^{\mathsf{H}}\mathbf{A}\mathbf{W}_g$ has $(i, j)$ entry
$(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{W})_{f(i),g(j)}$. With $\mathbf{Q} = \mathbf{W}$ and
$f = g$ this is a principal block of the compression
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$. -/
theorem conjTranspose_submatrix_mul_mul_submatrix {l q r s : Type*} [Fintype l] [Fintype m]
    (Q : Matrix m r 𝕜) (A : Matrix m l 𝕜) (W : Matrix l s 𝕜) (f : p → r) (g : q → s) :
    (Q.submatrix id f)ᴴ * A * W.submatrix id g = (Qᴴ * A * W).submatrix f g := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]

/-- A selection matrix acts on a vector by scattering its entries:
$\mathbf{S}\mathbf{x} = \sum_j \mathbf{x}_j \mathbf{e}_{s(j)}$, spelled as a sum of `Pi.single`. -/
theorem selectionMatrix_mulVec [Fintype p] (s : p → n) (x : p → 𝕜) :
    (selectionMatrix s : Matrix n p 𝕜) *ᵥ x = ∑ j, Pi.single (s j) (x j) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, selectionMatrix_apply, Finset.sum_apply, Pi.single_apply,
    ite_mul, one_mul, zero_mul]

/-- The conjugate transpose of a selection matrix acts on a vector by selecting entries:
$(\mathbf{S}^{\mathsf{H}}\mathbf{x})_j = \mathbf{x}_{s(j)}$. -/
@[simp]
theorem conjTranspose_selectionMatrix_mulVec [Fintype n] (s : p → n) (x : n → 𝕜) :
    (selectionMatrix s : Matrix n p 𝕜)ᴴ *ᵥ x = x ∘ s := by
  rw [selectionMatrix, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  exact (Matrix.submatrix_mulVec_equiv 1 x s (Equiv.refl n)).trans
    (congrArg (· ∘ s) (Matrix.one_mulVec x))

/-- The selection matrix of an injective map has orthonormal columns. -/
theorem hasOrthonormalCols_selectionMatrix [Fintype n] [DecidableEq p] {s : p → n}
    (hs : Function.Injective s) : HasOrthonormalCols (selectionMatrix s : Matrix n p 𝕜) :=
  hasOrthonormalCols_one.submatrix (Equiv.refl n) hs

/-- The selection matrix of the identity map is the identity matrix. -/
@[simp]
theorem selectionMatrix_id : (selectionMatrix (id : n → n) : Matrix n n 𝕜) = 1 :=
  Matrix.submatrix_id_id 1

end NLAlib
