/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Orthonormal
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Norms.Spectral

/-!
# Comparing the spectral and Frobenius norms

The inequalities between the spectral norm $\|\mathbf{A}\|_2$ and the Frobenius norm
$\|\mathbf{A}\|_{\mathsf{F}}$, the mixed bounds for products, and the
behaviour of both norms under factors with orthonormal columns.

Bounds that are linear in the norms are stated once, linearly; their squares follow by `gcongr`.

## Main results

* `NLAlib.specNorm_le_frobNorm`: $\|\mathbf{A}\|_2 \le \|\mathbf{A}\|_{\mathsf{F}}$.
* `NLAlib.frobNorm_mul_le_specNorm_mul_frobNorm`,
  `NLAlib.frobNorm_mul_le_frobNorm_mul_specNorm`: the mixed product bounds.
* `NLAlib.norm_toLp_map_abs_mulVec_abs_le`: $\lVert\,\lvert\mathbf{A}\rvert\lvert\mathbf{x}\rvert\,
  \rVert \le \sqrt{\lvert n \rvert}\,\|\mathbf{A}\|_2\lVert\mathbf{x}\rVert$.
* `NLAlib.HasOrthonormalCols.specNorm_mul_left`, `NLAlib.HasOrthonormalCols.frobNorm_mul_left`:
  both norms are invariant under left multiplication by a matrix with orthonormal columns, and
  under right multiplication by the conjugate transpose of one.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Spectral against Frobenius -/

/-- The spectral norm is at most the Frobenius norm:
$\|\mathbf{A}\|_2 \le \|\mathbf{A}\|_{\mathsf{F}}$.
[GolubVanLoan2013, (2.3.7)]. -/
theorem specNorm_le_frobNorm (A : Matrix m n 𝕜) : specNorm A ≤ frobNorm A := by
  exact (specNorm_le_iff (frobNorm_nonneg A)).2 (norm_toLp_mulVec_le_frobNorm_mul A)

/-- The Frobenius norm is at most $\sqrt{\lvert n \rvert}$ times the spectral norm, $n$ the column
index type, in squared form: $\|\mathbf{A}\|_{\mathsf{F}}^2 \le \lvert n \rvert \|\mathbf{A}\|_2^2$.
[GolubVanLoan2013, (2.3.7)]. -/
theorem frobNorm_sq_le_card_mul_specNorm_sq (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 ≤ Fintype.card n * specNorm A ^ 2 := by
  rw [frobNorm_sq_eq_sum_col, ← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun j _ => ?_
  gcongr
  exact norm_toLp_col_le_specNorm A j

/-- The Frobenius norm is at most $\sqrt{\lvert n \rvert}$ times the spectral norm, $n$ the column
index type: $\|\mathbf{A}\|_{\mathsf{F}} \le \sqrt{\lvert n \rvert} \, \|\mathbf{A}\|_2$.
[GolubVanLoan2013, (2.3.7)]. The squared form is `NLAlib.frobNorm_sq_le_card_mul_specNorm_sq`. -/
theorem frobNorm_le_sqrt_card_mul_specNorm (A : Matrix m n 𝕜) :
    frobNorm A ≤ √(Fintype.card n : ℝ) * specNorm A := by
  refine (sq_le_sq₀ (frobNorm_nonneg A) (by positivity)).1 ?_
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact frobNorm_sq_le_card_mul_specNorm_sq A

/-- **The entrywise product bound**: for a real $\mathbf{A}$ with $n$ columns, absolute values
taken entrywise, $\lVert\,\lvert\mathbf{A}\rvert\lvert\mathbf{x}\rvert\,\rVert \le
\|\mathbf{A}\|_{\mathsf{F}}\lVert\mathbf{x}\rVert \le \sqrt{\lvert n \rvert}\,
\|\mathbf{A}\|_2\lVert\mathbf{x}\rVert$; it turns a componentwise error bound
$\lvert\mathbf{e}\rvert \le c\lvert\mathbf{A}\rvert\lvert\mathbf{x}\rvert$ into a normwise one.
Cauchy–Schwarz by rows, then [GolubVanLoan2013, (2.3.7)]. -/
theorem norm_toLp_map_abs_mulVec_abs_le (A : Matrix m n ℝ) (x : n → ℝ) :
    ‖WithLp.toLp 2 (A.map abs *ᵥ fun j => |x j|)‖ ≤
      √(Fintype.card n : ℝ) * specNorm A * ‖WithLp.toLp 2 x‖ := by
  have hF : frobNorm (A.map abs) = frobNorm A := by
    simp [frobNorm]
  have hx : ‖WithLp.toLp 2 (fun j => |x j|)‖ = ‖WithLp.toLp 2 x‖ := by
    simp [EuclideanSpace.norm_eq]
  calc _ ≤ frobNorm (A.map abs) * ‖WithLp.toLp 2 (fun j => |x j|)‖ :=
        norm_toLp_mulVec_le_frobNorm_mul _ _
    _ = frobNorm A * ‖WithLp.toLp 2 x‖ := by rw [hF, hx]
    _ ≤ _ := by gcongr; exact frobNorm_le_sqrt_card_mul_specNorm A

/-- The squared Frobenius norm is at most the number of rows times the squared spectral norm,
$\|\mathbf{A}\|_{\mathsf{F}}^2 \le \lvert m \rvert \|\mathbf{A}\|_2^2$ with $m$ the row index type:
the row-count twin of `NLAlib.frobNorm_sq_le_card_mul_specNorm_sq`, which counts columns.
[GolubVanLoan2013, (2.3.7)]. -/
theorem frobNorm_sq_le_card_rows_mul_specNorm_sq (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 ≤ Fintype.card m * specNorm A ^ 2 := by
  have h := frobNorm_sq_le_card_mul_specNorm_sq Aᴴ
  rwa [frobNorm_conjTranspose, specNorm_conjTranspose] at h

/-- The mixed product bound with the spectral norm on the left factor:
$\|\mathbf{A}\mathbf{B}\|_{\mathsf{F}} \le \|\mathbf{A}\|_2 \|\mathbf{B}\|_{\mathsf{F}}$.
[HornJohnson2013, §5.6, Problem 20]. -/
theorem frobNorm_mul_le_specNorm_mul_frobNorm (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    frobNorm (A * B) ≤ specNorm A * frobNorm B := by
  refine (sq_le_sq₀ (by positivity) (by positivity)).1 ?_
  rw [mul_pow, frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [show (A * B).col j = A *ᵥ B.col j from rfl, ← mul_pow]
  gcongr
  exact norm_toLp_mulVec_le A (B.col j)

/-- The mixed product bound with the spectral norm on the right factor:
$\|\mathbf{A}\mathbf{B}\|_{\mathsf{F}} \le \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_2$. -/
theorem frobNorm_mul_le_frobNorm_mul_specNorm (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    frobNorm (A * B) ≤ frobNorm A * specNorm B := by
  have h := frobNorm_mul_le_specNorm_mul_frobNorm Bᴴ Aᴴ
  rwa [← Matrix.conjTranspose_mul, frobNorm_conjTranspose, specNorm_conjTranspose,
    frobNorm_conjTranspose, mul_comm] at h

/-- The Frobenius norm is submultiplicative:
$\|\mathbf{A}\mathbf{B}\|_{\mathsf{F}} \le \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_{\mathsf{F}}$.
-/
theorem frobNorm_mul_le (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    frobNorm (A * B) ≤ frobNorm A * frobNorm B := by
  refine (frobNorm_mul_le_specNorm_mul_frobNorm A B).trans ?_
  gcongr
  exact specNorm_le_frobNorm A

/-- The spectral norm is $1$-Lipschitz for the Frobenius norm:
$\lvert \|\mathbf{A}\|_2 - \|\mathbf{B}\|_2 \rvert \le \|\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}$. -/
theorem abs_specNorm_sub_specNorm_le_frobNorm (A B : Matrix m n 𝕜) :
    |specNorm A - specNorm B| ≤ frobNorm (A - B) := by
  exact (abs_specNorm_sub_specNorm_le A B).trans (specNorm_le_frobNorm (A - B))

/-- The Frobenius inner product is bounded by a Frobenius norm times a spectral-Frobenius
product:
$\lvert \langle \mathbf{A}\mathbf{B}, \mathbf{C} \rangle_{\mathsf{F}} \rvert
\le \|\mathbf{A}\|_2 \|\mathbf{B}\|_{\mathsf{F}} \|\mathbf{C}\|_{\mathsf{F}}$. -/
theorem abs_frobInner_mul_le (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) (C : Matrix l n 𝕜) :
    |frobInner (A * B) C| ≤ specNorm A * frobNorm B * frobNorm C := by
  refine (abs_frobInner_le (A * B) C).trans ?_
  gcongr
  exact frobNorm_mul_le_specNorm_mul_frobNorm A B

/-- The Frobenius inner product bound with the spectral norm on the right factor of the product:
$\lvert \langle \mathbf{A}\mathbf{B}, \mathbf{C} \rangle_{\mathsf{F}} \rvert
\le \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_2 \|\mathbf{C}\|_{\mathsf{F}}$. -/
theorem abs_frobInner_mul_le_frobNorm_mul_specNorm (A : Matrix l m 𝕜) (B : Matrix m n 𝕜)
    (C : Matrix l n 𝕜) : |frobInner (A * B) C| ≤ frobNorm A * specNorm B * frobNorm C := by
  refine (abs_frobInner_le (A * B) C).trans ?_
  gcongr
  exact frobNorm_mul_le_frobNorm_mul_specNorm A B

/-! ### Factors with orthonormal columns -/

namespace HasOrthonormalCols

variable [DecidableEq n]

/-- Left multiplication by a matrix with orthonormal columns preserves the spectral norm:
$\|\mathbf{Q}\mathbf{A}\|_2 = \|\mathbf{A}\|_2$. -/
theorem specNorm_mul_left {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix n p 𝕜) :
    specNorm (Q * A) = specNorm A := by
  have h (x : p → 𝕜) : ‖WithLp.toLp 2 ((Q * A) *ᵥ x)‖ = ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
    rw [← Matrix.mulVec_mulVec, hQ.norm_toLp_mulVec]
  refine le_antisymm ((specNorm_le_iff (specNorm_nonneg A)).2 fun x => ?_)
    ((specNorm_le_iff (specNorm_nonneg (Q * A))).2 fun x => ?_)
  · rw [h]
    exact norm_toLp_mulVec_le A x
  · rw [← h]
    exact norm_toLp_mulVec_le (Q * A) x

/-- Right multiplication by the conjugate transpose of a matrix with orthonormal columns
preserves the spectral norm: $\|\mathbf{A}\mathbf{Q}^{\mathsf{H}}\|_2 = \|\mathbf{A}\|_2$. -/
theorem specNorm_mul_conjTranspose_right {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix p n 𝕜) : specNorm (A * Qᴴ) = specNorm A := by
  rw [← specNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hQ.specNorm_mul_left, specNorm_conjTranspose]

/-- Left multiplication by a matrix with orthonormal columns preserves the Frobenius norm:
$\|\mathbf{Q}\mathbf{A}\|_{\mathsf{F}} = \|\mathbf{A}\|_{\mathsf{F}}$. -/
theorem frobNorm_mul_left {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix n p 𝕜) :
    frobNorm (Q * A) = frobNorm A := by
  refine (sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1 ?_
  rw [frobNorm_sq_eq_re_trace, frobNorm_sq_eq_re_trace, hQ.conjTranspose_mul_mul]

/-- Right multiplication by the conjugate transpose of a matrix with orthonormal columns
preserves the Frobenius norm: $\|\mathbf{A}\mathbf{Q}^{\mathsf{H}}\|_{\mathsf{F}}
= \|\mathbf{A}\|_{\mathsf{F}}$. -/
theorem frobNorm_mul_conjTranspose_right {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix p n 𝕜) : frobNorm (A * Qᴴ) = frobNorm A := by
  rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hQ.frobNorm_mul_left, frobNorm_conjTranspose]

/-- Left multiplication of both arguments by a matrix with orthonormal columns preserves the
Frobenius inner product. -/
theorem frobInner_mul_left {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A B : Matrix n p 𝕜) :
    frobInner (Q * A) (Q * B) = frobInner A B := by
  rw [frobInner, frobInner, hQ.conjTranspose_mul_mul]

/-- Right multiplication of both arguments by the conjugate transpose of a matrix with
orthonormal columns preserves the Frobenius inner product. -/
theorem frobInner_mul_conjTranspose_right {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A B : Matrix p n 𝕜) : frobInner (A * Qᴴ) (B * Qᴴ) = frobInner A B := by
  rw [← frobInner_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hQ.frobInner_mul_left, frobInner_conjTranspose]

/-- For $\mathbf{Q}$ with orthonormal columns, left multiplication by $\mathbf{Q}^{\mathsf{H}}$
does not increase the spectral norm: $\|\mathbf{Q}^{\mathsf{H}}\mathbf{A}\|_2 \le \|\mathbf{A}\|_2$.
-/
theorem specNorm_conjTranspose_mul_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m p 𝕜) : specNorm (Qᴴ * A) ≤ specNorm A := by
  refine (specNorm_le_iff (specNorm_nonneg A)).2 fun x => ?_
  rw [← Matrix.mulVec_mulVec]
  exact (hQ.norm_toLp_conjTranspose_mulVec_le (A *ᵥ x)).trans (norm_toLp_mulVec_le A x)

/-- For $\mathbf{Q}$ with orthonormal columns, left multiplication by $\mathbf{Q}^{\mathsf{H}}$
does not increase the Frobenius norm:
$\|\mathbf{Q}^{\mathsf{H}}\mathbf{A}\|_{\mathsf{F}} \le \|\mathbf{A}\|_{\mathsf{F}}$. -/
theorem frobNorm_conjTranspose_mul_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m p 𝕜) : frobNorm (Qᴴ * A) ≤ frobNorm A := by
  refine (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1 ?_
  rw [frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [show (Qᴴ * A).col j = Qᴴ *ᵥ A.col j from rfl]
  gcongr
  exact hQ.norm_toLp_conjTranspose_mulVec_le (A.col j)

/-- Right multiplication by a matrix with orthonormal columns does not increase the spectral
norm: $\|\mathbf{A}\mathbf{Q}\|_2 \le \|\mathbf{A}\|_2$. -/
theorem specNorm_mul_right_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p m 𝕜) :
    specNorm (A * Q) ≤ specNorm A := by
  refine (specNorm_le_iff (specNorm_nonneg A)).2 fun x => ?_
  rw [← Matrix.mulVec_mulVec, ← hQ.norm_toLp_mulVec x]
  exact norm_toLp_mulVec_le A (Q *ᵥ x)

/-- A compression does not increase the spectral norm:
$\|\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}\|_2 \le \|\mathbf{A}\|_2$ for $\mathbf{Q}$ with
orthonormal columns. -/
theorem specNorm_conjTranspose_mul_mul_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (A : Matrix m m 𝕜) : specNorm (Qᴴ * A * Q) ≤ specNorm A :=
  (hQ.specNorm_mul_right_le (Qᴴ * A)).trans (hQ.specNorm_conjTranspose_mul_le A)

/-- Right multiplication by a matrix with orthonormal columns does not increase the Frobenius
norm: $\|\mathbf{A}\mathbf{Q}\|_{\mathsf{F}} \le \|\mathbf{A}\|_{\mathsf{F}}$. -/
theorem frobNorm_mul_right_le {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p m 𝕜) :
    frobNorm (A * Q) ≤ frobNorm A := by
  have h := hQ.frobNorm_conjTranspose_mul_le Aᴴ
  rwa [← Matrix.conjTranspose_mul, frobNorm_conjTranspose, frobNorm_conjTranspose] at h

/-- Right multiplication by a matrix with orthonormal columns and as many rows as columns
preserves the spectral norm. The row and column index types may differ. -/
theorem specNorm_mul_right_of_card_eq {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (h : Fintype.card m = Fintype.card n) (A : Matrix p m 𝕜) :
    specNorm (A * Q) = specNorm A := by
  classical
  have h' := (hQ.conjTranspose_of_card_eq h).specNorm_mul_conjTranspose_right A
  rwa [Matrix.conjTranspose_conjTranspose] at h'

/-- Right multiplication by a matrix with orthonormal columns and as many rows as columns
preserves the Frobenius norm. The row and column index types may differ. -/
theorem frobNorm_mul_right_of_card_eq {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q)
    (h : Fintype.card m = Fintype.card n) (A : Matrix p m 𝕜) :
    frobNorm (A * Q) = frobNorm A := by
  classical
  have h' := (hQ.conjTranspose_of_card_eq h).frobNorm_mul_conjTranspose_right A
  rwa [Matrix.conjTranspose_conjTranspose] at h'

/-- Right multiplication by a unitary matrix preserves the spectral norm. -/
theorem specNorm_mul_right {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p n 𝕜) :
    specNorm (A * Q) = specNorm A :=
  hQ.specNorm_mul_right_of_card_eq rfl A

/-- Right multiplication by a unitary matrix preserves the Frobenius norm. -/
theorem frobNorm_mul_right {Q : Matrix n n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p n 𝕜) :
    frobNorm (A * Q) = frobNorm A :=
  hQ.frobNorm_mul_right_of_card_eq rfl A

/-- A matrix with orthonormal columns has spectral norm at most one. -/
theorem specNorm_le_one {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) : specNorm Q ≤ 1 := by
  rw [← Matrix.mul_one Q, hQ.specNorm_mul_left]
  exact specNorm_one_le

/-- A matrix with orthonormal columns, and at least one column, has spectral norm one. -/
theorem specNorm_eq_one [Nonempty n] {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    specNorm Q = 1 := by
  rw [← Matrix.mul_one Q, hQ.specNorm_mul_left, specNorm_one]

/-- The squared Frobenius norm of a matrix with orthonormal columns is its number of columns:
$\|\mathbf{Q}\|_{\mathsf{F}}^2 = \lvert n \rvert$. -/
theorem frobNorm_sq {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    frobNorm Q ^ 2 = Fintype.card n := by
  rw [← Matrix.mul_one Q, hQ.frobNorm_mul_left, frobNorm_one_sq]

end HasOrthonormalCols

end NLAlib
