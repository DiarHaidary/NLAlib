/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Spectral.SingularValues
public import NLAlib.Matrix.Norms.Compare
public import NLAlib.Matrix.Basic.Projector
public import NLAlib.ForMathlib.LinearAlgebra.Matrix.PosDef
public import NLAlib.ForMathlib.MeasureTheory.Matrix

/-!
# Subspace embeddings and subspace injections

A sketch `S : Matrix k n 𝕜` is a *subspace injection* for the column space of `U : Matrix n p 𝕜`
with constant `a` when `a ‖y‖² ≤ ‖S y‖²` for every `y ∈ range U`, and a *subspace embedding* with
constants `a`, `b` when moreover `‖S y‖² ≤ b ‖y‖²`. Both are stated in Loewner form on Gram
matrices, `a • (Uᴴ * U) ≤ (S * U)ᴴ * (S * U)` (and `≤ b • (Uᴴ * U)`), so they are about
`range U` for `U` of any shape and rank. The `ε` form of the literature is `a = 1 - ε`,
`b = 1 + ε`, written so. A one-sided upper statement is `IsSubspaceEmbedding S U 0 b`
(`NLAlib.isSubspaceInjection_of_nonpos` fills the lower half).

Degenerate cases: for empty `p` every predicate holds; for `k` empty or `S = 0` the injection holds
iff `a ≤ 0` or `U = 0`, the upper half iff `0 ≤ b` or `U = 0`; for `a ≤ 0` the injection is
vacuous. Design: `docs/design/Sketching-S0.md`.

## Main definitions

* `NLAlib.IsSubspaceInjection S U a`: the lower half.
* `NLAlib.IsSubspaceEmbedding S U a b`: both halves.

## Main results

* `NLAlib.isSubspaceInjection_iff_forall_mem_range`,
  `NLAlib.isSubspaceEmbedding_iff_forall_mem_range`: the vector forms.
* `NLAlib.HasOrthonormalCols.isSubspaceEmbedding_iff_specNorm_le`: the Gram-error form.
* `NLAlib.HasOrthonormalCols.isSubspaceInjection_iff_le_sq_singularValues`: the `σ_min` form.
* `NLAlib.IsSubspaceEmbedding.of_range_le`, `NLAlib.IsSubspaceEmbedding.mul_right`,
  `NLAlib.IsSubspaceEmbedding.smul`, `NLAlib.IsSubspaceEmbedding.mul`: subspaces, scaling and
  composition.
* `NLAlib.isClosed_setOf_isSubspaceEmbedding`, `NLAlib.measurableSet_setOf_isSubspaceEmbedding`.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {k l n p q : Type*} [Fintype k] [Fintype l] [Fintype n]
  {S : Matrix k n 𝕜} {U : Matrix n p 𝕜} {V : Matrix n q 𝕜}
  {a a' a₂ b b' b₂ ε : ℝ}

/-- **Subspace injection** for `range U` with constant `a`: `a • (Uᴴ * U) ≤ (S * U)ᴴ * (S * U)`,
that is `a ‖U x‖² ≤ ‖S U x‖²` for every `x` (`NLAlib.isSubspaceInjection_iff_forall_mem_range`).
Vacuous for `a ≤ 0`. [CamanoEpperlyMeyerTropp2025, Definition 1.2 (1.3)]; there `α ∈ (0, 1]` and
`U` with orthonormal columns, here any real `a` and any `U`.
Result: subspace-injection -/
def IsSubspaceInjection (S : Matrix k n 𝕜) (U : Matrix n p 𝕜) (a : ℝ) : Prop :=
  a • (Uᴴ * U) ≤ (S * U)ᴴ * (S * U)

/-- **Subspace embedding** for `range U` with lower constant `a` and upper constant `b`:
`a ‖y‖² ≤ ‖S y‖² ≤ b ‖y‖²` for `y ∈ range U`, in Loewner form on Gram matrices.
[Woodruff2014, Definition 1] (`1 ∓ ε`, squared norms); [CamanoEpperlyMeyerTropp2025,
Definition 1.1] (`α`, `β`); [MartinssonTropp2020, §8.1], with unsquared norms there.
Result: ose-def -/
structure IsSubspaceEmbedding (S : Matrix k n 𝕜) (U : Matrix n p 𝕜) (a b : ℝ) : Prop where
  /-- The lower half: `S` is a subspace injection with constant `a`. -/
  lower : IsSubspaceInjection S U a
  /-- The upper half: `‖S y‖² ≤ b ‖y‖²` on `range U`. -/
  upper : (S * U)ᴴ * (S * U) ≤ b • (Uᴴ * U)

/-! ### Vector, Gram-error and singular-value forms -/

/-- A subspace injection in vector form: `a ‖y‖² ≤ ‖S y‖²` for every `y` in the column space
of `U`. -/
theorem isSubspaceInjection_iff_forall_mem_range [Fintype p] :
    IsSubspaceInjection S U a ↔
    ∀ y ∈ LinearMap.range U.mulVecLin,
      a * ‖WithLp.toLp 2 y‖ ^ 2 ≤ ‖WithLp.toLp 2 (S *ᵥ y)‖ ^ 2 := by
  sorry

/-- A subspace embedding in vector form: `a ‖y‖² ≤ ‖S y‖² ≤ b ‖y‖²` for every `y` in the column
space of `U`. -/
theorem isSubspaceEmbedding_iff_forall_mem_range [Fintype p] :
    IsSubspaceEmbedding S U a b ↔
    ∀ y ∈ LinearMap.range U.mulVecLin,
      a * ‖WithLp.toLp 2 y‖ ^ 2 ≤ ‖WithLp.toLp 2 (S *ᵥ y)‖ ^ 2 ∧
        ‖WithLp.toLp 2 (S *ᵥ y)‖ ^ 2 ≤ b * ‖WithLp.toLp 2 y‖ ^ 2 := by
  sorry

/-- For `U` with orthonormal columns the injection is the Loewner bound
`a • 1 ≤ (S * U)ᴴ * (S * U)`. -/
theorem HasOrthonormalCols.isSubspaceInjection_iff [DecidableEq p] (hU : HasOrthonormalCols U) :
    IsSubspaceInjection S U a ↔ a • (1 : Matrix p p 𝕜) ≤ (S * U)ᴴ * (S * U) := by
  sorry

/-- For `U` with orthonormal columns and `0 ≤ ε`, the `ε`-embedding is the Gram-error bound
`‖(S U)ᴴ (S U) - 1‖ ≤ ε`. The hypothesis `0 ≤ ε` is needed only for empty `p`, where the left
side always holds and the right side says `0 ≤ ε`. -/
theorem HasOrthonormalCols.isSubspaceEmbedding_iff_specNorm_le [Fintype p] [DecidableEq p]
    (hU : HasOrthonormalCols U) (hε : 0 ≤ ε) :
    IsSubspaceEmbedding S U (1 - ε) (1 + ε) ↔ specNorm ((S * U)ᴴ * (S * U) - 1) ≤ ε := by
  sorry

/-- For `U` with orthonormal columns the injection is `a ≤ σ_min(S U)²`, the smallest singular
value being index `j` with `j + 1 = card p`. The upper half is
`NLAlib.specNorm_sq_le_iff_conjTranspose_mul_self_le` after `hU`. -/
theorem HasOrthonormalCols.isSubspaceInjection_iff_le_sq_singularValues [Fintype p] [DecidableEq p]
    (hU : HasOrthonormalCols U) {j : ℕ} (hj : j + 1 = Fintype.card p) :
    IsSubspaceInjection S U a ↔ a ≤ singularValues (S * U) j ^ 2 := by
  sorry

/-- An approximate-matrix-multiplication bound at `A = B = U` gives the embedding, since the
spectral norm is at most the Frobenius norm (`docs/PORT_SKETCHING.md` D7). -/
theorem HasOrthonormalCols.isSubspaceEmbedding_of_frobNorm_le [Fintype p] [DecidableEq p]
    (hU : HasOrthonormalCols U) (h : frobNorm (Uᴴ * Sᴴ * S * U - Uᴴ * U) ≤ ε) :
    IsSubspaceEmbedding S U (1 - ε) (1 + ε) := by
  sorry

/-! ### Monotonicity, subspaces, scaling and composition -/

/-- A subspace injection with constant `a` is one with any smaller constant. -/
theorem IsSubspaceInjection.mono (h : IsSubspaceInjection S U a) (ha : a' ≤ a) :
    IsSubspaceInjection S U a' := by
  sorry

/-- A subspace embedding with constants `a`, `b` is one with any `a' ≤ a` and `b ≤ b'`. -/
theorem IsSubspaceEmbedding.mono (h : IsSubspaceEmbedding S U a b) (ha : a' ≤ a) (hb : b ≤ b') :
    IsSubspaceEmbedding S U a' b' := by
  sorry

/-- A subspace injection for `range U` is one for every subspace `range V ≤ range U`. -/
theorem IsSubspaceInjection.of_range_le [Fintype p] [Fintype q] (h : IsSubspaceInjection S U a)
    (hVU : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    IsSubspaceInjection S V a := by
  sorry

/-- A subspace embedding for `range U` is one for every subspace `range V ≤ range U`. -/
theorem IsSubspaceEmbedding.of_range_le [Fintype p] [Fintype q] (h : IsSubspaceEmbedding S U a b)
    (hVU : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    IsSubspaceEmbedding S V a b := by
  sorry

/-- A subspace injection for `range U` is one for `range (U * C)`. -/
theorem IsSubspaceInjection.mul_right [Fintype p] (h : IsSubspaceInjection S U a)
    (C : Matrix p q 𝕜) :
    IsSubspaceInjection S (U * C) a := by
  sorry

/-- A subspace embedding for `range U` is one for `range (U * C)`. -/
theorem IsSubspaceEmbedding.mul_right [Fintype p] (h : IsSubspaceEmbedding S U a b)
    (C : Matrix p q 𝕜) :
    IsSubspaceEmbedding S (U * C) a b := by
  sorry

/-- Scaling the sketch by `c` scales the injection constant by `‖c‖²`. -/
theorem IsSubspaceInjection.smul (h : IsSubspaceInjection S U a) (c : 𝕜) :
    IsSubspaceInjection (c • S) U (‖c‖ ^ 2 * a) := by
  sorry

/-- Scaling the sketch by `c` scales both embedding constants by `‖c‖²`. -/
theorem IsSubspaceEmbedding.smul (h : IsSubspaceEmbedding S U a b) (c : 𝕜) :
    IsSubspaceEmbedding (c • S) U (‖c‖ ^ 2 * a) (‖c‖ ^ 2 * b) := by
  sorry

/-- Scaling the sketch by a real `c` scales the injection constant by `c ^ 2`: the form a
sketching family normalised by `(√k)⁻¹` uses. -/
theorem IsSubspaceInjection.smul_real (h : IsSubspaceInjection S U a) (c : ℝ) :
    IsSubspaceInjection (c • S) U (c ^ 2 * a) := by
  sorry

/-- Scaling the sketch by a real `c` scales both embedding constants by `c ^ 2`. -/
theorem IsSubspaceEmbedding.smul_real (h : IsSubspaceEmbedding S U a b) (c : ℝ) :
    IsSubspaceEmbedding (c • S) U (c ^ 2 * a) (c ^ 2 * b) := by
  sorry

/-- **Composition of subspace injections**: if `S` injects `range U` with constant `a` and `S₂`
injects `range (S * U)` with constant `a₂ ≥ 0`, then `S₂ * S` injects `range U` with `a₂ * a`. -/
theorem IsSubspaceInjection.mul {S₂ : Matrix l k 𝕜} (h₂ : IsSubspaceInjection S₂ (S * U) a₂)
    (h : IsSubspaceInjection S U a) (ha₂ : 0 ≤ a₂) : IsSubspaceInjection (S₂ * S) U (a₂ * a) := by
  sorry

/-- **Composition of subspace embeddings**: constants multiply, for nonnegative constants of the
outer sketch. -/
theorem IsSubspaceEmbedding.mul {S₂ : Matrix l k 𝕜} (h₂ : IsSubspaceEmbedding S₂ (S * U) a₂ b₂)
    (h : IsSubspaceEmbedding S U a b) (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂) :
    IsSubspaceEmbedding (S₂ * S) U (a₂ * a) (b₂ * b) := by
  sorry

/-- Every sketch is a subspace injection with a nonpositive constant. -/
theorem isSubspaceInjection_of_nonpos (S : Matrix k n 𝕜) (U : Matrix n p 𝕜) (ha : a ≤ 0) :
    IsSubspaceInjection S U a := by
  sorry

/-! ### Injectivity -/

/-- A subspace injection with a positive constant is injective on `range U`. -/
theorem IsSubspaceInjection.injOn [Fintype p] (h : IsSubspaceInjection S U a) (ha : 0 < a) :
    Set.InjOn S.mulVec (LinearMap.range U.mulVecLin) := by
  sorry

/-- A subspace injection with a positive constant preserves full column rank: `S * U` has full
column rank when `U` does. -/
theorem IsSubspaceInjection.injective_mulVec [Fintype p] (h : IsSubspaceInjection S U a)
    (ha : 0 < a) (hU : Function.Injective U.mulVec) : Function.Injective (S * U).mulVec := by
  sorry

/-! ### Closedness and measurability of the events -/

/-- The pairs `(S, U)` with `S` a subspace injection for `range U` form a closed set. -/
theorem isClosed_setOf_isSubspaceInjection (a : ℝ) :
    IsClosed {x : Matrix k n 𝕜 × Matrix n p 𝕜 | IsSubspaceInjection x.1 x.2 a} := by
  sorry

/-- The pairs `(S, U)` with `S` a subspace embedding for `range U` form a closed set. -/
theorem isClosed_setOf_isSubspaceEmbedding (a b : ℝ) :
    IsClosed {x : Matrix k n 𝕜 × Matrix n p 𝕜 | IsSubspaceEmbedding x.1 x.2 a b} := by
  sorry

/-- For fixed `U`, the sketches that are subspace injections for `range U` form a measurable
set. -/
theorem measurableSet_setOf_isSubspaceInjection (U : Matrix n p 𝕜) (a : ℝ) :
    MeasurableSet {S : Matrix k n 𝕜 | IsSubspaceInjection S U a} := by
  sorry

/-- For fixed `U`, the sketches that are subspace embeddings for `range U` form a measurable
set. -/
theorem measurableSet_setOf_isSubspaceEmbedding (U : Matrix n p 𝕜) (a b : ℝ) :
    MeasurableSet {S : Matrix k n 𝕜 | IsSubspaceEmbedding S U a b} := by
  sorry

end NLAlib
