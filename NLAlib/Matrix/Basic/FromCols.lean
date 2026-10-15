/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.RCLike.Basic

/-!
# Column spaces of a column-partitioned matrix

The column space of `Matrix.fromCols A B`, the matrix
$\begin{bmatrix} \mathbf{A} & \mathbf{B} \end{bmatrix}$, contains that of $\mathbf{A}$, and the
column space of $\begin{bmatrix} \mathbf{A} & \mathbf{y} \end{bmatrix}$ contains $\mathbf{y}$.
These are the facts sketch-and-solve uses to pass from an embedding of
$\operatorname{range} \begin{bmatrix} \mathbf{A} & \mathbf{y} \end{bmatrix}$ to statements about
$\mathbf{A}$ and $\mathbf{y}$ (`docs/design/Sketching-S0.md` §3.3).

This file holds the Sketching round's S0 additions to the Matrix layer until the round's wrap-up
merges them into their owner.

## Main results

* `NLAlib.range_mulVecLin_le_range_fromCols_left`: $\operatorname{range} \mathbf{A} \le
  \operatorname{range} \begin{bmatrix} \mathbf{A} & \mathbf{B} \end{bmatrix}$.
* `NLAlib.mem_range_mulVecLin_fromCols_replicateCol`: $\mathbf{y} \in
  \operatorname{range} \begin{bmatrix} \mathbf{A} & \mathbf{y} \end{bmatrix}$.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n q r : Type*} [Fintype q] [Fintype r]

/-- The column space of $\mathbf{A}$ lies in the column space of `Matrix.fromCols A B`, the matrix
$\begin{bmatrix} \mathbf{A} & \mathbf{B} \end{bmatrix}$. Mathlib has `Matrix.fromCols_mulVec`
(the action of $\begin{bmatrix} \mathbf{A} & \mathbf{B} \end{bmatrix}$ on a split vector), no
range statement. -/
theorem range_mulVecLin_le_range_fromCols_left (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    LinearMap.range A.mulVecLin ≤ LinearMap.range (Matrix.fromCols A B).mulVecLin := by
  rintro _ ⟨v, rfl⟩
  refine ⟨Sum.elim v 0, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_zero,
    add_zero]

/-- The vector $\mathbf{y}$ lies in the column space of
$\begin{bmatrix} \mathbf{A} & \mathbf{y} \end{bmatrix}$, the matrix $\mathbf{A}$ with
$\mathbf{y}$ appended as one column. -/
theorem mem_range_mulVecLin_fromCols_replicateCol (A : Matrix n q 𝕜) (y : n → 𝕜) :
    y ∈ LinearMap.range (Matrix.fromCols A (Matrix.replicateCol Unit y)).mulVecLin := by
  refine ⟨Sum.elim 0 fun _ => 1, ?_⟩
  ext i
  simp [Matrix.mulVec, dotProduct]

end NLAlib
