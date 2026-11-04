/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Leading blocks of upper triangular products

An upper triangular right factor lets a product be restricted to the leading columns. In
particular, taking a leading square block commutes with multiplication and powers.
Upstream candidates for `Mathlib.LinearAlgebra.Matrix.Block`.

## Main results

* `Matrix.IsUpperTriangular.submatrix_castSucc_mul`.
* `Matrix.IsUpperTriangular.submatrix_castSucc_mul_castSucc`.
* `Matrix.IsUpperTriangular.submatrix_castSucc_pow`.
-/

@[expose] public section

namespace Matrix.IsUpperTriangular

variable {R p : Type*} [Semiring R] {m : ℕ}

/-- With an upper triangular right factor, the leading columns of a product use only the
leading columns of the left factor and the leading square block of the right factor. -/
theorem submatrix_castSucc_mul {X : Matrix (Fin (m + 1)) (Fin (m + 1)) R}
    (hX : X.IsUpperTriangular) (B : Matrix p (Fin (m + 1)) R) :
    (B * X).submatrix id Fin.castSucc =
      B.submatrix id Fin.castSucc * X.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [Matrix.submatrix_apply, id, Matrix.mul_apply]
  rw [Fin.sum_univ_castSucc,
    show X (Fin.last m) (Fin.castSucc j) = 0 from hX (Fin.castSucc_lt_last j), mul_zero, add_zero]

/-- The leading square block of a product with an upper triangular right factor is the product
of the leading square blocks. -/
theorem submatrix_castSucc_mul_castSucc {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) R}
    (hY : Y.IsUpperTriangular) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    (X * Y).submatrix Fin.castSucc Fin.castSucc =
      X.submatrix Fin.castSucc Fin.castSucc * Y.submatrix Fin.castSucc Fin.castSucc := by
  have h := hY.submatrix_castSucc_mul X
  ext i j
  have := congrFun (congrFun h (Fin.castSucc i)) j
  simpa only [Matrix.submatrix_apply, id, Matrix.mul_apply] using this

/-- Taking the leading square block of an upper triangular matrix commutes with powers. -/
theorem submatrix_castSucc_pow {X : Matrix (Fin (m + 1)) (Fin (m + 1)) R}
    (hX : X.IsUpperTriangular) (r : ℕ) :
    (X ^ r).submatrix Fin.castSucc Fin.castSucc =
      X.submatrix Fin.castSucc Fin.castSucc ^ r := by
  induction r with
  | zero => simp only [pow_zero, Matrix.submatrix_one _ (Fin.castSucc_injective m)]
  | succ r ih => rw [pow_succ, hX.submatrix_castSucc_mul_castSucc, ih, pow_succ]

end Matrix.IsUpperTriangular
