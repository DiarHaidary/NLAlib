/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.FromCols
public import NLAlib.Sketching.Properties.SubspaceEmbedding
public import NLAlib.Matrix.Pseudoinverse.LeastSquares
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Pseudoinverse.NormBounds
public import NLAlib.Matrix.Factorizations.QR

/-!
# Sketched least squares

The deterministic consequences of a subspace embedding or injection for least squares. If `S` is
a subspace embedding with constants `a`, `b` for a subspace containing `range A` and `y`, every
minimizer `x` of the sketched problem `‖S A x - S y‖` has residual within `b / a` (squared) of the
optimal residual `(1 - rangeProjector A) *ᵥ y` (sketch-and-solve). If `S` embeds `range A` and
`S * A * M` has orthonormal columns (QR's `R⁻¹`, SVD's `V Σ⁻¹`), then `A * M` has condition
number at most `√(b / a)` (sketch-and-precondition).

The injection alone controls the error of the sketched solution against the sketched residual
(CEMT's Lemma 2.6), for a vector and for a matrix right-hand side, and gives the deterministic
half of CEMT's Lemma 2.1. These are what the tail bounds for oblivious subspace injections in
`NLAlib.Sketching.Properties.Injection` use. Design: `docs/design/Sketching-S0.md` §3.2.

## Main results

* `NLAlib.IsSubspaceEmbedding.norm_sub_mulVec_sq_le`: sketch-and-solve.
* `NLAlib.IsSubspaceEmbedding.conditionNumber_mul_sq_le`: sketch-and-precondition.
* `NLAlib.IsSubspaceInjection.norm_sub_mulVec_sq_le`: the sketch-and-solve error formula.
* `NLAlib.IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le`: its matrix form.
* `NLAlib.IsSubspaceInjection.frobNorm_mul_pinv_sq_le`: the deterministic half of CEMT
  Lemma 2.1.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {k l n p q r : Type*} [Fintype k] [Fintype l] [Fintype n]
  [Fintype p] [Fintype q] {S : Matrix k n 𝕜} {U : Matrix n p 𝕜}
  {A : Matrix n q 𝕜} {y : n → 𝕜} {x : q → 𝕜} {a b : ℝ}

/-! ### Sketch-and-solve -/

section LeastSquares

variable [DecidableEq n]

/-- **Sketch-and-solve.** If `S` is a subspace embedding with constants `a > 0`, `b` for a
subspace `range U` containing `range A` and `y`, every minimizer `x` of `‖S A x - S y‖` satisfies
`‖y - A x‖² ≤ (b / a) ‖(1 - P_A) y‖²`, the last being the optimal residual.
[Woodruff2014, proof of Theorem 21], there `(1 + ε) / (1 - ε)` in squared norms;
[MartinssonTropp2020, §10.3], there `‖A x̂ - b‖ ≤ (1 + ε) ‖A x⋆ - b‖`, unsquared (after Sarlós).
Here any constants and any subspace containing `range A` and `y`.
Result: sketch-and-solve-ls -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_sq_le (h : IsSubspaceEmbedding S U a b) (ha : 0 < a)
    (hA : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hy : y ∈ LinearMap.range U.mulVecLin) (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ^ 2 ≤
      b / a * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 := by
  sorry

/-- **Sketch-and-solve**, unsquared: `‖y - A x‖ ≤ √(b / a) ‖(1 - P_A) y‖`.
[MartinssonTropp2020, §10.3], unsquared there. -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_le (h : IsSubspaceEmbedding S U a b) (ha : 0 < a)
    (hA : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hy : y ∈ LinearMap.range U.mulVecLin) (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ≤ √(b / a) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ := by
  sorry

/-- **Sketch-and-solve** with an embedding of `range [A, y]`, the form in which the literature
states it. [Woodruff2014, proof of Theorem 21]. -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_sq_le_of_fromCols
    (h : IsSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y)) a b) (ha : 0 < a)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ^ 2 ≤
      b / a * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 := by
  sorry

end LeastSquares

/-! ### Sketch-and-precondition -/

/-- **Sketch-and-precondition**, lower half of the spectral equivalence: if `S` embeds `range A`
with upper constant `b > 0` and `S * A * M` has orthonormal columns, then
`b⁻¹ • 1 ≤ (A M)ᴴ (A M)`. Any such `M` (QR's `R⁻¹`, SVD's `V Σ⁻¹`, Cholesky-QR) qualifies. -/
theorem IsSubspaceEmbedding.inv_smul_one_le_conjTranspose_mul_self [DecidableEq r]
    {M : Matrix q r 𝕜} (h : IsSubspaceEmbedding S A a b) (hb : 0 < b)
    (hM : HasOrthonormalCols (S * A * M)) : b⁻¹ • (1 : Matrix r r 𝕜) ≤ (A * M)ᴴ * (A * M) := by
  sorry

/-- **Sketch-and-precondition**, upper half of the spectral equivalence: if `S` embeds `range A`
with lower constant `a > 0` and `S * A * M` has orthonormal columns, then
`(A M)ᴴ (A M) ≤ a⁻¹ • 1`. -/
theorem IsSubspaceEmbedding.conjTranspose_mul_self_le_inv_smul_one [DecidableEq r]
    {M : Matrix q r 𝕜} (h : IsSubspaceEmbedding S A a b) (ha : 0 < a)
    (hM : HasOrthonormalCols (S * A * M)) : (A * M)ᴴ * (A * M) ≤ a⁻¹ • (1 : Matrix r r 𝕜) := by
  sorry

/-- **Sketch-and-precondition**: if `S` embeds `range A` with constants `a > 0`, `b ≥ 0` and
`S * A * M` has orthonormal columns, the preconditioned matrix has `κ(A M)² ≤ b / a`.
For empty `r`, `κ(A M) = 0` and the bound is `hb`; for nonempty `r` the hypotheses force
`0 < b`. [MartinssonTropp2020, §10.5]; there for `M = R⁻¹` from a QR factorization of `S A`.
Result: sketch-and-precondition -/
theorem IsSubspaceEmbedding.conditionNumber_mul_sq_le [Fintype r] [DecidableEq r] {M : Matrix q r 𝕜}
    (h : IsSubspaceEmbedding S A a b) (ha : 0 < a) (hb : 0 ≤ b)
    (hM : HasOrthonormalCols (S * A * M)) : conditionNumber (A * M) ^ 2 ≤ b / a := by
  sorry

/-- **Sketch-and-precondition with QR**: for a thin QR factorization `S A = Q R` with `R`
invertible, `κ(A R⁻¹)² ≤ b / a`. [MartinssonTropp2020, §10.5]. -/
theorem IsSubspaceEmbedding.conditionNumber_mul_inv_sq_le_of_isQR [LinearOrder q]
    [DecidableEq q] {Q : Matrix k q 𝕜} {R : Matrix q q 𝕜} (h : IsSubspaceEmbedding S A a b)
    (ha : 0 < a) (hb : 0 ≤ b) (hQR : IsQR (S * A) Q R) (hR : IsUnit R) :
    conditionNumber (A * R⁻¹) ^ 2 ≤ b / a := by
  sorry

/-! ### The error formula, from the injection alone -/

section ErrorFormula

variable [DecidableEq n]

/-- The error of a sketched solution against the optimal fit, from the injection alone:
`‖A x - P_A y‖² ≤ ‖S (1 - P_A) y‖² / a` for every minimizer `x` of `‖S A x - S y‖`.
[CamanoEpperlyMeyerTropp2025, Lemma 2.6]; there an identity for the minimum-norm solution, here
a bound in norm for every minimizer. -/
theorem IsSubspaceInjection.norm_mulVec_sub_rangeProjector_mulVec_sq_le
    (h : IsSubspaceInjection S A a) (ha : 0 < a)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (A *ᵥ x - rangeProjector A *ᵥ y)‖ ^ 2 ≤
      ‖WithLp.toLp 2 (S *ᵥ ((1 - rangeProjector A) *ᵥ y))‖ ^ 2 / a := by
  sorry

/-- **Sketch-and-solve error formula**: for every minimizer `x` of `‖S A x - S y‖`,
`‖y - A x‖² ≤ ‖(1 - P_A) y‖² + ‖S (1 - P_A) y‖² / a`.
[CamanoEpperlyMeyerTropp2025, Lemma 2.6, proof of Theorem 2.7]; there an identity for the
minimum-norm solution, here a bound for every minimizer. -/
theorem IsSubspaceInjection.norm_sub_mulVec_sq_le (h : IsSubspaceInjection S A a) (ha : 0 < a)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ^ 2 ≤ ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 +
      ‖WithLp.toLp 2 (S *ᵥ ((1 - rangeProjector A) *ᵥ y))‖ ^ 2 / a := by
  sorry

/-- **Sketch-and-solve error formula, matrix right-hand side**, for the minimum-norm output
`pinv (S A) (S Y)`, as generalized Nyström uses it:
`‖Y - A (S A)† S Y‖_F² ≤ ‖(1 - P_A) Y‖_F² + ‖S (1 - P_A) Y‖_F² / a`.
[CamanoEpperlyMeyerTropp2025, Lemma 2.6, proof of Theorem 2.7]; there an identity. -/
theorem IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le [Fintype r]
    (h : IsSubspaceInjection S A a) (ha : 0 < a) (Y : Matrix n r 𝕜) :
    frobNorm (Y - A * (pinv (S * A) * (S * Y))) ^ 2 ≤
      frobNorm ((1 - rangeProjector A) * Y) ^ 2 +
        frobNorm (S * ((1 - rangeProjector A) * Y)) ^ 2 / a := by
  sorry

end ErrorFormula

/-- **Deterministic half of CEMT Lemma 2.1**: for `U` with orthonormal columns and a subspace
injection with constant `a > 0`, `‖X (S U)ᴴ†‖_F² ≤ ‖X‖_F² / a`. CEMT apply it at
`X = B (S Q⊥)ᴴ`. [CamanoEpperlyMeyerTropp2025, proof of Lemma 2.1]. -/
theorem IsSubspaceInjection.frobNorm_mul_pinv_sq_le [DecidableEq p]
    (h : IsSubspaceInjection S U a) (hU : HasOrthonormalCols U) (ha : 0 < a)
    (X : Matrix l k 𝕜) : frobNorm (X * pinv ((S * U)ᴴ)) ^ 2 ≤ frobNorm X ^ 2 / a := by
  sorry

end NLAlib
