/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Sketching.Properties.FixedSubspace
public import NLAlib.Sketching.Properties.Isotropic

/-!
# Oblivious subspace embeddings and injections

A random sketch `S : Ω → Matrix k n 𝕜` is an *oblivious subspace embedding* (OSE) for dimension
`d` when, for every fixed subspace of dimension at most `d`, it is a subspace embedding with
probability `1 - δ`; it is an *oblivious subspace injection* (OSI) when it is isotropic and the
lower half holds with probability `1 - δ` on every such subspace. Subspaces are column spaces of
square matrices `U : Matrix n n 𝕜` with `U.rank ≤ d`;
`NLAlib.IsObliviousSubspaceEmbedding.hasSubspaceEmbedding` applies the predicate to `U` of any
shape.

Every sketching family concludes one of these predicates, through the constructor from
orthonormal `U : Matrix n p 𝕜`; every consumer takes one. The predicates transfer to a random
subspace independent of the sketch, and compose over independent sketches.

Theorems that compare two events take `[IsFiniteMeasure μ]`. Design:
`docs/design/Sketching-S1.md` §3.3.

## Main definitions

* `NLAlib.IsObliviousSubspaceEmbedding S d a b δ μ`.
* `NLAlib.IsObliviousSubspaceInjection S d a δ μ`.

## Main results

* `NLAlib.IsObliviousSubspaceEmbedding.of_hasOrthonormalCols`: the constructor families use.
* `NLAlib.IsObliviousSubspaceEmbedding.isObliviousSubspaceInjection`: an isotropic OSE is an OSI.
* `NLAlib.IsObliviousSubspaceEmbedding.measure_not_isSubspaceEmbedding_le_of_indepFun`: transfer
  to an independent random subspace.
* `NLAlib.IsObliviousSubspaceEmbedding.mul`: composition of independent sketches.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k l n p q : Type*} [Fintype k] [Fintype l] [Fintype n] {S : Ω → Matrix k n 𝕜}
  {a a' a₂ b b' b₂ δ δ' δ₂ : ℝ} {d d' : ℕ}

/-- **Oblivious subspace embedding** for dimension `d`: for every `U : Matrix n n 𝕜` of rank at
most `d`, `S` is a subspace embedding for `range U` with constants `a`, `b` with probability
`1 - δ`. [Woodruff2014, Definition 2] (`1 ∓ ε`); [CamanoEpperlyMeyerTropp2025, Definition 1.1]
(`α`, `β`); there for subspaces of dimension exactly `d`, here at most `d`.
Result: ose-def -/
def IsObliviousSubspaceEmbedding (S : Ω → Matrix k n 𝕜) (d : ℕ) (a b δ : ℝ) (μ : Measure Ω) :
    Prop :=
  ∀ U : Matrix n n 𝕜, U.rank ≤ d → HasSubspaceEmbedding S U a b δ μ

/-- **Oblivious subspace injection** for dimension `d`: `S` is isotropic and, for every
`U : Matrix n n 𝕜` of rank at most `d`, a subspace injection for `range U` with constant `a` with
probability `1 - δ`. [CamanoEpperlyMeyerTropp2025, Definition 1.2]; there `δ = 1/20` and
`α ∈ (0, 1]`, here any `δ` and `a`.
Result: osi-def -/
structure IsObliviousSubspaceInjection [DecidableEq n] (S : Ω → Matrix k n 𝕜) (d : ℕ) (a δ : ℝ)
    (μ : Measure Ω) : Prop where
  /-- The sketch is isotropic. -/
  isotropic : IsIsotropicSketch S μ
  /-- The lower half holds with probability `1 - δ` on every subspace of dimension at most `d`. -/
  injection : ∀ U : Matrix n n 𝕜, U.rank ≤ d → HasSubspaceInjection S U a δ μ

/-- Being an OSE depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.isObliviousSubspaceEmbedding_iff
    {ν : Measure (Matrix k n 𝕜)} (hS : HasLaw S ν μ) :
    IsObliviousSubspaceEmbedding S d a b δ μ ↔ IsObliviousSubspaceEmbedding id d a b δ ν := by
  sorry

/-- Being an OSI depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.isObliviousSubspaceInjection_iff [DecidableEq n]
    {ν : Measure (Matrix k n 𝕜)} (hS : HasLaw S ν μ) :
    IsObliviousSubspaceInjection S d a δ μ ↔ IsObliviousSubspaceInjection id d a δ ν := by
  sorry

/-- An OSE applies to the column space of a matrix of any shape and rank at most `d`. -/
theorem IsObliviousSubspaceEmbedding.hasSubspaceEmbedding [Fintype p]
    (h : IsObliviousSubspaceEmbedding S d a b δ μ) {U : Matrix n p 𝕜} (hU : U.rank ≤ d) :
    HasSubspaceEmbedding S U a b δ μ := by
  sorry

/-- An OSI applies to the column space of a matrix of any shape and rank at most `d`. -/
theorem IsObliviousSubspaceInjection.hasSubspaceInjection [DecidableEq n] [Fintype p]
    (h : IsObliviousSubspaceInjection S d a δ μ) {U : Matrix n p 𝕜} (hU : U.rank ≤ d) :
    HasSubspaceInjection S U a δ μ := by
  sorry

/-- **The OSE constructor**: a sketch that is a random subspace embedding for every `U` with
orthonormal columns indexed by `p` is an OSE for dimension `card p`. The constructor every
sketching family uses. -/
theorem IsObliviousSubspaceEmbedding.of_hasOrthonormalCols [IsFiniteMeasure μ] [Fintype p]
    [DecidableEq p] (hp : Fintype.card p ≤ Fintype.card n)
    (h : ∀ U : Matrix n p 𝕜, HasOrthonormalCols U → HasSubspaceEmbedding S U a b δ μ) :
    IsObliviousSubspaceEmbedding S (Fintype.card p) a b δ μ := by
  sorry

/-- **The OSI constructor**: an isotropic sketch that is a random subspace injection for every
`U` with orthonormal columns indexed by `p` is an OSI for dimension `card p`. -/
theorem IsObliviousSubspaceInjection.of_hasOrthonormalCols [IsFiniteMeasure μ] [DecidableEq n]
    [Fintype p] [DecidableEq p] (hiso : IsIsotropicSketch S μ)
    (hp : Fintype.card p ≤ Fintype.card n)
    (h : ∀ U : Matrix n p 𝕜, HasOrthonormalCols U → HasSubspaceInjection S U a δ μ) :
    IsObliviousSubspaceInjection S (Fintype.card p) a δ μ := by
  sorry

/-- An isotropic OSE is an OSI with the same lower constant and failure probability. -/
theorem IsObliviousSubspaceEmbedding.isObliviousSubspaceInjection [IsFiniteMeasure μ]
    [DecidableEq n] (h : IsObliviousSubspaceEmbedding S d a b δ μ)
    (hiso : IsIsotropicSketch S μ) : IsObliviousSubspaceInjection S d a δ μ := by
  sorry

/-- An OSE is one for any smaller dimension, weaker constants and larger failure
probability. -/
theorem IsObliviousSubspaceEmbedding.mono [IsFiniteMeasure μ]
    (h : IsObliviousSubspaceEmbedding S d a b δ μ) (hd : d' ≤ d) (ha : a' ≤ a) (hb : b ≤ b')
    (hδ : δ ≤ δ') : IsObliviousSubspaceEmbedding S d' a' b' δ' μ := by
  sorry

/-- An OSI is one for any smaller dimension, smaller constant and larger failure
probability. -/
theorem IsObliviousSubspaceInjection.mono [IsFiniteMeasure μ] [DecidableEq n]
    (h : IsObliviousSubspaceInjection S d a δ μ) (hd : d' ≤ d) (ha : a' ≤ a) (hδ : δ ≤ δ') :
    IsObliviousSubspaceInjection S d' a' δ' μ := by
  sorry

/-! ### Transfer to an independent random subspace -/

/-- **Transfer of an OSE to an independent random subspace**: if `V` is independent of `S` and
has rank at most `d` almost surely, `S ω` fails to embed `range (V ω)` with probability at most
`δ`. Fubini on the closed set of `NLAlib.isClosed_setOf_isSubspaceEmbedding`. -/
theorem IsObliviousSubspaceEmbedding.measure_not_isSubspaceEmbedding_le_of_indepFun
    [IsProbabilityMeasure μ] [Fintype q] (h : IsObliviousSubspaceEmbedding S d a b δ μ)
    {V : Ω → Matrix n q 𝕜} (hind : IndepFun S V μ) (hS : AEMeasurable S μ)
    (hV : AEMeasurable V μ) (hrank : ∀ᵐ ω ∂μ, (V ω).rank ≤ d) :
    μ.real {ω | ¬ IsSubspaceEmbedding (S ω) (V ω) a b} ≤ δ := by
  sorry

/-- **Transfer of an OSI to an independent random subspace**: if `V` is independent of `S` and
has rank at most `d` almost surely, `S ω` fails to inject `range (V ω)` with probability at most
`δ`. -/
theorem IsObliviousSubspaceInjection.measure_not_isSubspaceInjection_le_of_indepFun
    [IsProbabilityMeasure μ] [DecidableEq n] [Fintype q]
    (h : IsObliviousSubspaceInjection S d a δ μ) {V : Ω → Matrix n q 𝕜} (hind : IndepFun S V μ)
    (hS : AEMeasurable S μ) (hV : AEMeasurable V μ) (hrank : ∀ᵐ ω ∂μ, (V ω).rank ≤ d) :
    μ.real {ω | ¬ IsSubspaceInjection (S ω) (V ω) a} ≤ δ := by
  sorry

/-! ### Composition -/

/-- **Composition of OSEs**: for independent OSEs `S₂` and `S` for the same dimension, `S₂ * S`
is an OSE with multiplied constants and failure probability `δ₂ + δ`. -/
theorem IsObliviousSubspaceEmbedding.mul [IsProbabilityMeasure μ] {S₂ : Ω → Matrix l k 𝕜}
    (h₂ : IsObliviousSubspaceEmbedding S₂ d a₂ b₂ δ₂ μ)
    (h : IsObliviousSubspaceEmbedding S d a b δ μ) (hind : IndepFun S₂ S μ)
    (hS₂ : AEMeasurable S₂ μ) (hS : AEMeasurable S μ) (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂) :
    IsObliviousSubspaceEmbedding (fun ω => S₂ ω * S ω) d (a₂ * a) (b₂ * b) (δ₂ + δ) μ := by
  sorry

/-- **Composition of OSIs**: for independent OSIs `S₂` and `S` for the same dimension, `S₂ * S`
is an OSI with constant `a₂ * a` and failure probability `δ₂ + δ`. -/
theorem IsObliviousSubspaceInjection.mul [IsProbabilityMeasure μ] [DecidableEq n]
    [DecidableEq k] {S₂ : Ω → Matrix l k 𝕜} (h₂ : IsObliviousSubspaceInjection S₂ d a₂ δ₂ μ)
    (h : IsObliviousSubspaceInjection S d a δ μ) (hind : IndepFun S₂ S μ)
    (hS₂ : AEMeasurable S₂ μ) (hS : AEMeasurable S μ) (ha₂ : 0 ≤ a₂) :
    IsObliviousSubspaceInjection (fun ω => S₂ ω * S ω) d (a₂ * a) (δ₂ + δ) μ := by
  sorry

end NLAlib
