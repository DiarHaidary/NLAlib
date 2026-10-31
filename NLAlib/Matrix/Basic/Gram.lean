/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Rank
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Gram matrices

The Gram matrix of $\mathbf{A}$ is $\mathbf{A}^{\mathsf{H}}\mathbf{A}$; it has no definition of
its own. Mathlib has its positive
semidefiniteness (`Matrix.posSemidef_conjTranspose_mul_self`), rank
(`Matrix.rank_conjTranspose_mul_self`) and kernel (`Matrix.ker_mulVecLin_conjTranspose_mul_self`).
This file adds the entries of $\mathbf{A}^{\mathsf{H}}\mathbf{B}$, of the Gram matrix and of a
compression $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ as pairings of columns, the
characterisations of invertibility, and two identities for a matrix scaled as a sketch: its action
on a vector row by row, and its Gram matrix.

"Full column rank" is spelled `Function.Injective A.mulVec` throughout the library, the
hypothesis of Mathlib's `Matrix.PosDef.conjTranspose_mul_self`. The equivalent forms
`IsUnit (Aᴴ * A)` and `A.rank = Fintype.card n` are reached through the lemmas here.

## Main results

* `NLAlib.conjTranspose_mul_apply`, `NLAlib.conjTranspose_mul_self_apply`,
  `NLAlib.conjTranspose_mul_mul_apply`: entries as pairings of columns.
* `NLAlib.isUnit_conjTranspose_mul_self_iff`: $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ is invertible iff
  $\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ is injective.
* `NLAlib.mulVec_injective_iff_rank_eq`: $\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ is injective iff
  $\operatorname{rank} \mathbf{A}$ is the number of columns.
* `NLAlib.posDef_conjTranspose_mul_self_iff`: $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ is positive
  definite iff $\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ is injective.
* `NLAlib.conjTranspose_mul_self_eq_gram`: the bridge to Mathlib's `Matrix.gram`.
* `NLAlib.dotProduct_mul_conjTranspose_inv_mulVec_nonneg`: the inverse Gram matrix of a real
  matrix is positive semidefinite, as a quadratic form.
* `NLAlib.norm_inv_sqrt_card_smul_mulVec_sq`,
  `NLAlib.conjTranspose_mul_self_sqrt_card_div_smul_conjTranspose_mul`: a matrix scaled as a sketch,
  on a vector and in its Gram matrix.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}

/-- An entry of $\mathbf{A}^{\mathsf{H}}\mathbf{B}$ is the pairing of a column of $\mathbf{A}$
with a column of $\mathbf{B}$:
$(\mathbf{A}^{\mathsf{H}}\mathbf{B})_{i,j} = \mathbf{a}_i^{\mathsf{H}}\mathbf{b}_j$, with
$\mathbf{a}_i$ column $i$ of $\mathbf{A}$ and $\mathbf{b}_j$ column $j$ of $\mathbf{B}$. -/
theorem conjTranspose_mul_apply {p : Type*} [Fintype m] (A : Matrix m n 𝕜) (B : Matrix m p 𝕜)
    (i : n) (j : p) : (Aᴴ * B) i j = star (A.col i) ⬝ᵥ B.col j := by
  simp only [Matrix.mul_apply, dotProduct, Matrix.conjTranspose_apply, Matrix.col_apply,
    Pi.star_apply]

/-- An entry of the Gram matrix is the pairing of two columns of $\mathbf{A}$:
$(\mathbf{A}^{\mathsf{H}}\mathbf{A})_{i,j} = \mathbf{a}_i^{\mathsf{H}}\mathbf{a}_j$, with
$\mathbf{a}_i$ column $i$ of $\mathbf{A}$. -/
theorem conjTranspose_mul_self_apply [Fintype m] (A : Matrix m n 𝕜) (i j : n) :
    (Aᴴ * A) i j = star (A.col i) ⬝ᵥ A.col j :=
  conjTranspose_mul_apply A A i j

/-- An entry of the compression $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ is the form of
$\mathbf{A}$ on two columns of $\mathbf{Q}$,
$(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})_{i,j} =
\mathbf{q}_i^{\mathsf{H}}\mathbf{A}\mathbf{q}_j$, with $\mathbf{q}_i$ column $i$ of $\mathbf{Q}$. -/
theorem conjTranspose_mul_mul_apply [Fintype m] (Q : Matrix m n 𝕜) (A : Matrix m m 𝕜)
    (i j : n) : (Qᴴ * A * Q) i j = star (Q.col i) ⬝ᵥ (A *ᵥ Q.col j) := by
  rw [Matrix.mul_assoc, conjTranspose_mul_apply]
  rfl

/-- $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ is Mathlib's `Matrix.gram` of the columns of $\mathbf{A}$
in `EuclideanSpace 𝕜 m`. -/
theorem conjTranspose_mul_self_eq_gram [Fintype m] (A : Matrix m n 𝕜) :
    Aᴴ * A = Matrix.gram 𝕜 fun j => WithLp.toLp 2 (A.col j) := by
  ext i j
  rw [Matrix.gram_apply, EuclideanSpace.inner_toLp_toLp, conjTranspose_mul_self_apply,
    dotProduct_comm]

/-- $\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ is injective exactly when the rank of $\mathbf{A}$
is its number of columns, $\operatorname{rank} \mathbf{A} = \lvert n \rvert$. -/
theorem mulVec_injective_iff_rank_eq [Fintype n] {A : Matrix m n 𝕜} :
    Function.Injective A.mulVec ↔ A.rank = Fintype.card n := by
  rw [Matrix.mulVec_injective_iff, linearIndependent_iff_card_eq_finrank_span,
    Matrix.rank_eq_finrank_span_cols, eq_comm, Set.finrank]

/-- The Gram matrix $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ is invertible exactly when $\mathbf{A}$ has
full column rank ($\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ injective).
[HornJohnson2013, Theorem 7.2.10]. -/
theorem isUnit_conjTranspose_mul_self_iff [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n 𝕜} : IsUnit (Aᴴ * A) ↔ Function.Injective A.mulVec := by
  rw [← Matrix.mulVec_injective_iff_isUnit, ← Matrix.coe_mulVecLin, ← Matrix.coe_mulVecLin,
    ← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_conjTranspose_mul_self]

/-- The Gram matrix $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ is positive definite exactly when
$\mathbf{A}$ has full column rank ($\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ injective).
The reverse direction is Mathlib's `Matrix.PosDef.conjTranspose_mul_self`. -/
theorem posDef_conjTranspose_mul_self_iff [Fintype m] [Fintype n] {A : Matrix m n 𝕜} :
    (Aᴴ * A).PosDef ↔ Function.Injective A.mulVec := by
  classical
  exact ⟨fun h => isUnit_conjTranspose_mul_self_iff.mp h.isUnit,
    Matrix.PosDef.conjTranspose_mul_self A⟩

/-- The Gram matrix $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ is invertible exactly when
$\operatorname{rank} \mathbf{A} = \lvert n \rvert$, the number of columns. -/
theorem isUnit_conjTranspose_mul_self_iff_rank [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n 𝕜} : IsUnit (Aᴴ * A) ↔ A.rank = Fintype.card n := by
  rw [isUnit_conjTranspose_mul_self_iff, mulVec_injective_iff_rank_eq]

/-- With full column rank, $(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{-1}\mathbf{A}^{\mathsf{H}}$ is a
left inverse of $\mathbf{A}$. -/
theorem inv_conjTranspose_mul_self_mul_conjTranspose_mul [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) : (Aᴴ * A)⁻¹ * Aᴴ * A = 1 := by
  rw [Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_conjTranspose_mul_self_iff.mpr hA))

/-- Two matrices with a common left factor of full column rank are equal when the products are:
$\mathbf{A}\mathbf{B} = \mathbf{A}\mathbf{C}$ iff $\mathbf{B} = \mathbf{C}$. -/
theorem mul_right_inj_of_mulVec_injective {p : Type*} [Fintype n] {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) {B C : Matrix n p 𝕜} : A * B = A * C ↔ B = C := by
  refine ⟨fun h => Matrix.ext_col fun j => hA ?_, fun h => by rw [h]⟩
  exact congrArg (fun M : Matrix m p 𝕜 => M.col j) h


/-- The quadratic form of the inverse Gram matrix $(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}$ of a
real matrix is nonnegative: $\mathbf{u}^{\mathsf{T}}(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}
\mathbf{u} \ge 0$ (Lean's inverse, $\mathbf{0}$ where $\mathbf{G}\mathbf{G}^{\mathsf{H}}$ is
singular). -/
theorem dotProduct_mul_conjTranspose_inv_mulVec_nonneg [Fintype m] [Fintype n] [DecidableEq m]
    (G : Matrix m n ℝ) (u : m → ℝ) : 0 ≤ u ⬝ᵥ ((G * Gᴴ)⁻¹ *ᵥ u) := by
  simpa only [star_trivial] using
    (Matrix.posSemidef_self_mul_conjTranspose G).inv.dotProduct_mulVec_nonneg u

/-! ### Scaled matrices -/

/-- A scaled matrix on a vector, row by row: for
$\mathbf{S} = \lvert k \rvert^{-1/2} \mathbf{A}$ with rows $\mathbf{A}_i$,
$$\|\mathbf{S}\mathbf{x}\|^2 = \frac{1}{\lvert k \rvert} \sum_i
\lvert \langle \mathbf{x}, \mathbf{A}_i \rangle \rvert^2 \,,$$
the average of the squared projections of $\mathbf{x}$ on the rows (with the bilinear pairing
`x ⬝ᵥ A i`). The identity behind every sketch with independent rows
(`NLAlib.isIsotropicSketch_smul_of_isIsotropic`, the Gaussian, sub-Gaussian and sign sketches). -/
theorem norm_inv_sqrt_card_smul_mulVec_sq {k : Type*} [Fintype k] [Fintype n] (A : Matrix k n 𝕜)
    (x : n → 𝕜) :
    ‖WithLp.toLp 2 (((√(Fintype.card k : ℝ))⁻¹ • A) *ᵥ x)‖ ^ 2 =
      (∑ i, ‖x ⬝ᵥ A i‖ ^ 2) / Fintype.card k := by
  rw [Matrix.smul_mulVec, EuclideanSpace.norm_toLp_inv_sqrt_card_smul_sq,
    EuclideanSpace.norm_sq_eq]
  simp only [Matrix.mulVec, dotProduct_comm (A _) x]

/-- The Gram matrix of a scaled conjugate transpose on $\mathbf{U}$: with
$\mathbf{S} = \sqrt{\lvert n \rvert / \lvert k \rvert} \, \mathbf{M}^{\mathsf{H}}$,
$(\mathbf{S}\mathbf{U})^{\mathsf{H}} (\mathbf{S}\mathbf{U}) = (\lvert n \rvert / \lvert k \rvert)
\, \mathbf{U}^{\mathsf{H}} (\mathbf{M}\mathbf{M}^{\mathsf{H}}) \mathbf{U}$. The Gram matrix of
the Haar sketch, for any $\mathbf{M}$ in place of the frame
(`NLAlib.Sketching.Gaussian.Haar`). -/
theorem conjTranspose_mul_self_sqrt_card_div_smul_conjTranspose_mul {k p : Type*} [Fintype k]
    [Fintype n] (M : Matrix n k 𝕜) (U : Matrix n p 𝕜) :
    (√(Fintype.card n / Fintype.card k : ℝ) • Mᴴ * U)ᴴ *
        (√(Fintype.card n / Fintype.card k : ℝ) • Mᴴ * U) =
      (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * (M * Mᴴ) * U) := by
  rw [Matrix.smul_mul, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt (by positivity), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

open scoped MatrixOrder in
/-- The Loewner lower bound $s^2\mathbf{I} \preceq \mathbf{M}^{\mathsf{H}}\mathbf{M}$ gives
$s^2\|\mathbf{v}\|^2 \le \|\mathbf{M}\mathbf{v}\|^2$. -/
theorem sq_mul_sum_sq_le_sum_sq_mulVec {m' b : Type*} [Fintype m'] [Fintype b]
    [DecidableEq b] (M : Matrix m' b ℝ) {s : ℝ} (hM : s ^ 2 • (1 : Matrix b b ℝ) ≤ Mᴴ * M)
    (v : b → ℝ) : s ^ 2 * ∑ c, v c ^ 2 ≤ ∑ i, (M *ᵥ v) i ^ 2 := by
  have h := (Matrix.le_iff.1 hM).dotProduct_mulVec_nonneg v
  have e : star v ⬝ᵥ ((Mᴴ * M - s ^ 2 • (1 : Matrix b b ℝ)) *ᵥ v) =
      ∑ i, (M *ᵥ v) i ^ 2 - s ^ 2 * ∑ c, v c ^ 2 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_sub, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, dotProduct_smul,
      star_trivial, smul_eq_mul]
    simp only [dotProduct, star_trivial, pow_two, Finset.mul_sum]
  linarith


end NLAlib
