/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Law
public import NLAlib.Sketching.Properties.SubspaceEmbedding

/-!
# Random sketches of a fixed subspace

For a random sketch `S : Ω → Matrix k n 𝕜` and a fixed `U : Matrix n p 𝕜`,
`NLAlib.HasSubspaceInjection S U a δ μ` and `NLAlib.HasSubspaceEmbedding S U a b δ μ` say that
`S ω` fails to be a subspace injection (embedding) for `range U` with probability at most `δ`:
`μ.real {ω | ¬ IsSubspaceInjection (S ω) U a} ≤ δ`. They are the conclusions of the
fixed-subspace theorems (leverage-score sampling, a sketch of `[A, y]` in a solver) and the
hypotheses of the oblivious constructors. Tails of the Gram error (matrix Chernoff) and of the
smallest singular value convert to them here.

Theorems that compare two events take `[IsFiniteMeasure μ]`, since `μ.real` of a set of infinite
measure is `0`. Design: `docs/design/Sketching-S1.md` §3.2.

## Main definitions

* `NLAlib.HasSubspaceInjection`, `NLAlib.HasSubspaceEmbedding`.

## Main results

* `NLAlib.HasSubspaceInjection.hasSubspaceEmbedding`: joining the two halves.
* `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_measureReal_le`: from a Gram-error tail.
* `NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_measureReal_le`: from a `σ_min` tail.
* `NLAlib.HasSubspaceEmbedding.of_range_le`: passing to a smaller subspace.
* `ProbabilityTheory.HasLaw.hasSubspaceEmbedding_iff`: the predicates depend only on the law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n p q : Type*} [Fintype k] [Fintype n] {S : Ω → Matrix k n 𝕜}
  {U : Matrix n p 𝕜} {a a' b b' δ δ' ε : ℝ}

/-- `S` is a **subspace injection for `range U` with probability `1 - δ`**: the event that `S ω`
is not a subspace injection with constant `a` has probability at most `δ`. -/
def HasSubspaceInjection (S : Ω → Matrix k n 𝕜) (U : Matrix n p 𝕜) (a δ : ℝ) (μ : Measure Ω) :
    Prop :=
  μ.real {ω | ¬ IsSubspaceInjection (S ω) U a} ≤ δ

/-- `S` is a **subspace embedding for `range U` with probability `1 - δ`**: the event that `S ω`
is not a subspace embedding with constants `a`, `b` has probability at most `δ`. -/
def HasSubspaceEmbedding (S : Ω → Matrix k n 𝕜) (U : Matrix n p 𝕜) (a b δ : ℝ)
    (μ : Measure Ω) : Prop :=
  μ.real {ω | ¬ IsSubspaceEmbedding (S ω) U a b} ≤ δ

/-- `HasSubspaceInjection` depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.hasSubspaceInjection_iff {ν : Measure (Matrix k n 𝕜)}
    (hS : HasLaw S ν μ) : HasSubspaceInjection S U a δ μ ↔ HasSubspaceInjection id U a δ ν := by
  sorry

/-- `HasSubspaceEmbedding` depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.hasSubspaceEmbedding_iff {ν : Measure (Matrix k n 𝕜)}
    (hS : HasLaw S ν μ) :
    HasSubspaceEmbedding S U a b δ μ ↔ HasSubspaceEmbedding id U a b δ ν := by
  sorry

/-- A random subspace embedding is a random subspace injection with the same lower constant
and failure probability. -/
theorem HasSubspaceEmbedding.hasSubspaceInjection [IsFiniteMeasure μ]
    (h : HasSubspaceEmbedding S U a b δ μ) : HasSubspaceInjection S U a δ μ := by
  sorry

/-- **Joining the halves**: a random subspace injection whose upper half fails with probability
at most `δ'` is a random subspace embedding with failure probability `δ + δ'` (union bound). -/
theorem HasSubspaceInjection.hasSubspaceEmbedding (h : HasSubspaceInjection S U a δ μ)
    (hb : μ.real {ω | ¬ (S ω * U)ᴴ * (S ω * U) ≤ b • (Uᴴ * U)} ≤ δ') :
    HasSubspaceEmbedding S U a b (δ + δ') μ := by
  sorry

/-- **From a Gram-error tail**: for `U` with orthonormal columns, a tail
`P(ε ≤ ‖(S U)ᴴ (S U) - 1‖) ≤ δ` gives a random `ε`-embedding with failure probability `δ`. The
form matrix Chernoff and matrix Bernstein bounds produce. -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_of_measureReal_le [IsFiniteMeasure μ]
    [Fintype p] [DecidableEq p] (hU : HasOrthonormalCols U)
    (h : μ.real {ω | ε ≤ specNorm ((S ω * U)ᴴ * (S ω * U) - 1)} ≤ δ) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε) δ μ := by
  sorry

/-- **From a smallest-singular-value tail**: for `U` with orthonormal columns, a tail
`P(σ_min(S U)² ≤ a) ≤ δ` gives a random subspace injection with constant `a`; the smallest
singular value is index `j` with `j + 1 = card p`. -/
theorem HasOrthonormalCols.hasSubspaceInjection_of_measureReal_le [IsFiniteMeasure μ]
    [Fintype p] [DecidableEq p] (hU : HasOrthonormalCols U) {j : ℕ} (hj : j + 1 = Fintype.card p)
    (h : μ.real {ω | singularValues (S ω * U) j ^ 2 ≤ a} ≤ δ) :
    HasSubspaceInjection S U a δ μ := by
  sorry

/-- A random subspace injection is one with any smaller constant and any larger failure
probability. -/
theorem HasSubspaceInjection.mono [IsFiniteMeasure μ] (h : HasSubspaceInjection S U a δ μ)
    (ha : a' ≤ a) (hδ : δ ≤ δ') : HasSubspaceInjection S U a' δ' μ := by
  sorry

/-- A random subspace embedding is one with any weaker constants and any larger failure
probability. -/
theorem HasSubspaceEmbedding.mono [IsFiniteMeasure μ] (h : HasSubspaceEmbedding S U a b δ μ)
    (ha : a' ≤ a) (hb : b ≤ b') (hδ : δ ≤ δ') : HasSubspaceEmbedding S U a' b' δ' μ := by
  sorry

/-- A random subspace injection for `range U` is one for every subspace `range V ≤ range U`. -/
theorem HasSubspaceInjection.of_range_le [IsFiniteMeasure μ] [Fintype p] [Fintype q]
    (h : HasSubspaceInjection S U a δ μ) {V : Matrix n q 𝕜}
    (hVU : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    HasSubspaceInjection S V a δ μ := by
  sorry

/-- A random subspace embedding for `range U` is one for every subspace `range V ≤ range U`. -/
theorem HasSubspaceEmbedding.of_range_le [IsFiniteMeasure μ] [Fintype p] [Fintype q]
    (h : HasSubspaceEmbedding S U a b δ μ) {V : Matrix n q 𝕜}
    (hVU : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    HasSubspaceEmbedding S V a b δ μ := by
  sorry

end NLAlib
