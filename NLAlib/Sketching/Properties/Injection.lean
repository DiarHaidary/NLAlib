/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Tail
public import NLAlib.Sketching.Properties.LeastSquares
public import NLAlib.Sketching.Properties.Oblivious

/-!
# Tail bounds from a subspace injection

The two probabilistic consequences of an oblivious subspace injection in
[CamanoEpperlyMeyerTropp2025]: *OSIs respect orthogonality* (their Lemma 2.1), the step behind
the randomized range finder, Nyström and generalized Nyström bounds; and *sketch-and-solve with an
OSI* (their Theorem 2.7), for a vector and for a matrix right-hand side. Each is stated for a
random subspace injection of a fixed subspace together with isotropy, and again for an OSI.

Each event is the negation of the guarantee (`{c < X}` for `X ≤ c`), so the degenerate cases
`B Zᴴ = 0`, `(1 - P_A) y = 0` need no hypothesis. The proofs combine the deterministic bounds of
`NLAlib.Sketching.Properties.LeastSquares` with Markov's inequality for
`E ‖S M‖_F² = ‖M‖_F²`. Design: `docs/design/Sketching-S1.md` §3.4.

## Main results

* `NLAlib.HasSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le`,
  `NLAlib.IsObliviousSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le`: CEMT Lemma 2.1.
* `NLAlib.HasSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le`: sketch-and-solve, CEMT
  Theorem 2.7.
* `NLAlib.HasSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le`: its matrix form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k l n p q r : Type*} [Fintype k] [Fintype l] [Fintype n] [Fintype p] [Fintype q] [Fintype r]
  [DecidableEq n] {S : Ω → Matrix k n 𝕜} {Q : Matrix n p 𝕜} {A : Matrix n q 𝕜} {a δ t : ℝ}
  {d : ℕ}

/-! ### OSIs respect orthogonality -/

/-- **OSIs respect orthogonality**: if `S` is isotropic and a subspace injection for `range Q`
with constant `a > 0` and failure probability `δ`, `Q` with orthonormal columns, then
`‖B (S Z)ᴴ (S Q)ᴴ†‖_F² ≤ t ‖B Zᴴ‖_F² / a` except with probability `δ + 1 / t`.
[CamanoEpperlyMeyerTropp2025, Lemma 2.1]; there `Qᴴ Z = 0` (unused here), `Z` with orthonormal
columns and `t = 20`. -/
theorem HasSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le [IsFiniteMeasure μ]
    [DecidableEq p] (h : HasSubspaceInjection S Q a δ μ) (hiso : IsIsotropicSketch S μ)
    (hQ : HasOrthonormalCols Q) (ha : 0 < a) (ht : 0 < t) (B : Matrix l r 𝕜)
    (Z : Matrix n r 𝕜) :
    μ.real {ω | t * frobNorm (B * Zᴴ) ^ 2 / a <
      frobNorm (B * (S ω * Z)ᴴ * pinv ((S ω * Q)ᴴ)) ^ 2} ≤ δ + 1 / t := by
  sorry

/-- **OSIs respect orthogonality**, in CEMT's form: for an OSI for dimension `d ≥ card p`, `Q`
and `Z` with orthonormal columns, `‖B (S Z)ᴴ (S Q)ᴴ†‖_F² ≤ t ‖B‖_F² / a` except with probability
`δ + 1 / t`. [CamanoEpperlyMeyerTropp2025, Lemma 2.1]; there `Qᴴ Z = 0` (unused here) and
`t = 20`. -/
theorem IsObliviousSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le [IsFiniteMeasure μ]
    [DecidableEq p] [DecidableEq r] (h : IsObliviousSubspaceInjection S d a δ μ)
    (hQ : HasOrthonormalCols Q) (hpd : Fintype.card p ≤ d) {Z : Matrix n r 𝕜}
    (hZ : HasOrthonormalCols Z) (ha : 0 < a) (ht : 0 < t) (B : Matrix l r 𝕜) :
    μ.real {ω | t * frobNorm B ^ 2 / a <
      frobNorm (B * (S ω * Z)ᴴ * pinv ((S ω * Q)ᴴ)) ^ 2} ≤ δ + 1 / t := by
  sorry

/-! ### Sketch-and-solve with an injection -/

/-- **Sketch-and-solve with an OSI**: if `S` is isotropic and a subspace injection for
`range A` with constant `a > 0` and failure probability `δ`, every (almost surely) minimizer
`x ω` of `‖S A x - S y‖` satisfies `‖y - A x‖² ≤ (1 + t / a) ‖(1 - P_A) y‖²` except with
probability `δ + 1 / t`. [CamanoEpperlyMeyerTropp2025, Theorem 2.7]; there for an OSI, the
minimum-norm solution and a fixed `t`, here a tail in `t` for every minimizer.
Result: sketch-and-solve-ls -/
theorem HasSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le [IsFiniteMeasure μ]
    (h : HasSubspaceInjection S A a δ μ) (hiso : IsIsotropicSketch S μ) (ha : 0 < a)
    (ht : 0 < t) (y : n → 𝕜) {x : Ω → q → 𝕜}
    (hx : ∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x ω)) :
    μ.real {ω | (1 + t / a) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ x ω)‖ ^ 2} ≤ δ + 1 / t := by
  sorry

/-- **Sketch-and-solve with an OSI, matrix right-hand side**, for the minimum-norm output
`pinv (S A) (S Y)`: `‖Y - A (S A)† S Y‖_F² ≤ (1 + t / a) ‖(1 - P_A) Y‖_F²` except with
probability `δ + 1 / t`. [CamanoEpperlyMeyerTropp2025, Theorem 2.7]; there a vector
right-hand side. -/
theorem HasSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le [IsFiniteMeasure μ]
    (h : HasSubspaceInjection S A a δ μ) (hiso : IsIsotropicSketch S μ) (ha : 0 < a)
    (ht : 0 < t) (Y : Matrix n r 𝕜) :
    μ.real {ω | (1 + t / a) * frobNorm ((1 - rangeProjector A) * Y) ^ 2 <
      frobNorm (Y - A * (pinv (S ω * A) * (S ω * Y))) ^ 2} ≤ δ + 1 / t := by
  sorry

/-- **Sketch-and-solve with an OSI** for dimension `d ≥ rank A`.
[CamanoEpperlyMeyerTropp2025, Theorem 2.7]. -/
theorem IsObliviousSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le [IsFiniteMeasure μ]
    (h : IsObliviousSubspaceInjection S d a δ μ) (hA : A.rank ≤ d) (ha : 0 < a) (ht : 0 < t)
    (y : n → 𝕜) {x : Ω → q → 𝕜}
    (hx : ∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x ω)) :
    μ.real {ω | (1 + t / a) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ x ω)‖ ^ 2} ≤ δ + 1 / t := by
  sorry

/-- **Sketch-and-solve with an OSI, matrix right-hand side**, for dimension `d ≥ rank A`.
[CamanoEpperlyMeyerTropp2025, Theorem 2.7]; there a vector right-hand side. -/
theorem IsObliviousSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le
    [IsFiniteMeasure μ] (h : IsObliviousSubspaceInjection S d a δ μ) (hA : A.rank ≤ d)
    (ha : 0 < a) (ht : 0 < t) (Y : Matrix n r 𝕜) :
    μ.real {ω | (1 + t / a) * frobNorm ((1 - rangeProjector A) * Y) ^ 2 <
      frobNorm (Y - A * (pinv (S ω * A) * (S ω * Y))) ^ 2} ≤ δ + 1 / t := by
  sorry

end NLAlib
