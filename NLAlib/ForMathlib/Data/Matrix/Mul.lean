/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-!
# Bilinear forms as dot products of flattened matrices; products through leading columns

The bilinear form $\mathbf{x}^{\mathsf{T}}\mathbf{G}\mathbf{y}$ is the dot product of the
flattened matrix $(\mathbf{G}_{i,j})_{(i,j)}$ (`Function.uncurry G`) with the flattened outer
product $(\mathbf{x}_i \mathbf{y}_j)_{(i,j)}$, and dot products of flattened outer products factor.
Together they turn a bilinear form of a random matrix into a linear form of its entries (Gaussian
comparison for random matrices). A matrix whose columns from $k$ on vanish acts through its
first $k$ columns (the Krylov realisations past the grade). Powers of the two products
$\mathbf{C}\mathbf{D}$ and $\mathbf{D}\mathbf{C}$ of rectangular matrices intertwine (block
Krylov matrices). Upstream candidates for
`Mathlib.Data.Matrix.Mul`.

## Main results

* `Matrix.dotProduct_mulVec_eq_dotProduct_uncurry`: $\mathbf{x}^{\mathsf{T}}\mathbf{G}\mathbf{y}$
  as a dot product with `Function.uncurry G`.
* `Matrix.mulVec_eq_submatrix_castLE_mulVec`: a product through the leading $k$ columns.
* `Matrix.mul_pow_mul`: $(\mathbf{C}\mathbf{D})^j\mathbf{C} = \mathbf{C}(\mathbf{D}\mathbf{C})^j$.
* `dotProduct_mul_eq_mul_dotProduct`: the dot product of two flattened outer products is
  $(\mathbf{x}^{\mathsf{T}}\mathbf{x}') (\mathbf{y}^{\mathsf{T}}\mathbf{y}')$.
-/

@[expose] public section

open scoped Matrix

variable {R : Type*} [CommSemiring R] {m n : Type*} [Fintype m] [Fintype n]

/-- Dot products of flattened outer products factor:
$\sum_{(i,j)} (\mathbf{x}_i \mathbf{y}_j) (\mathbf{x}'_i \mathbf{y}'_j)
= (\mathbf{x}^{\mathsf{T}}\mathbf{x}') (\mathbf{y}^{\mathsf{T}}\mathbf{y}')$. -/
theorem dotProduct_mul_eq_mul_dotProduct (x x' : m → R) (y y' : n → R) :
    (fun p : m × n => x p.1 * y p.2) ⬝ᵥ (fun p => x' p.1 * y' p.2) = (x ⬝ᵥ x') * (y ⬝ᵥ y') := by
  simp only [dotProduct, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

namespace Matrix

/-- A bilinear form is a linear form of the entries:
$\mathbf{x}^{\mathsf{T}}\mathbf{G}\mathbf{y}$ is the dot product of the flattened outer product
$(\mathbf{x}_i \mathbf{y}_j)_{(i,j)}$ with the flattened matrix $(\mathbf{G}_{i,j})_{(i,j)}$
(`Function.uncurry G`): $\mathbf{x}^{\mathsf{T}}\mathbf{G}\mathbf{y}
= \sum_{(i,j)} \mathbf{x}_i \mathbf{y}_j \mathbf{G}_{i,j}$. -/
theorem dotProduct_mulVec_eq_dotProduct_uncurry (x : m → R) (G : Matrix m n R) (y : n → R) :
    x ⬝ᵥ (G *ᵥ y) = (fun p : m × n => x p.1 * y p.2) ⬝ᵥ Function.uncurry G := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change _ = _ * G i j
  ring

/-- A product through the leading columns: if the columns of
$\mathbf{Q} \in R^{m \times q}$ from $k \le q$ on vanish, then
$\mathbf{Q}\mathbf{y} = \mathbf{Q}_{:,<k}\,\mathbf{y}_{<k}$, the first $k$ columns of
$\mathbf{Q}$ applied to the first $k$ entries of $\mathbf{y}$. -/
theorem mulVec_eq_submatrix_castLE_mulVec {α : Type*} [NonUnitalNonAssocSemiring α] {l : Type*}
    {q k : ℕ} (h : k ≤ q) (Q : Matrix l (Fin q) α) (hQ : ∀ j : Fin q, k ≤ (j : ℕ) → Q.col j = 0)
    (y : Fin q → α) : Q *ᵥ y = Q.submatrix id (Fin.castLE h) *ᵥ (y ∘ Fin.castLE h) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq, Function.comp_apply]
  refine (Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _
    (fun j hj => ?_) fun j => rfl).symm
  have hkj : k ≤ (j : ℕ) := by
    by_contra hjk
    exact hj ⟨⟨j, not_le.mp hjk⟩, Fin.ext rfl⟩
  rw [show Q i j = Q.col j i from rfl, hQ j hkj, Pi.zero_apply, zero_mul]

/-- Powers of the two products of rectangular matrices intertwine:
$(\mathbf{C}\mathbf{D})^j\mathbf{C} = \mathbf{C}(\mathbf{D}\mathbf{C})^j$ for
$\mathbf{C} \in R^{m \times n}$ and $\mathbf{D} \in R^{n \times m}$. The rectangular form of
Mathlib's `mul_pow_mul`. -/
theorem mul_pow_mul {α : Type*} [Semiring α] [DecidableEq m] [DecidableEq n] (C : Matrix m n α)
    (D : Matrix n m α) (j : ℕ) : (C * D) ^ j * C = C * (D * C) ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
  | succ j ih => rw [pow_succ, Matrix.mul_assoc, Matrix.mul_assoc C D C, ← Matrix.mul_assoc, ih,
      Matrix.mul_assoc, ← pow_succ]

end Matrix
