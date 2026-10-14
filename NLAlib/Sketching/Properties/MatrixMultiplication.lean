/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Sketching.Properties.JohnsonLindenstrauss
public import NLAlib.Sketching.Properties.Oblivious

/-!
# Approximate matrix multiplication from the JL moment property

A real sketch with the JL moment property, exponent `p ≥ 2`, approximates every product `Aᴴ B`:
`E ‖Aᴴ Sᴴ S B - Aᴴ B‖_F^p ≤ (ε ‖A‖_F ‖B‖_F)^p δ`. At `A = B = U` with orthonormal columns this is
a Gram-error bound, so the sketch is a random subspace embedding for every fixed subspace with
distortion `ε · dim`, hence an oblivious subspace embedding.

Over `ℝ` only, with constant `1`: Woodruff's statement has `3 ε`, and `1` is optimal (the
deterministic sketch with `Sᴴ S = (1 + ε) • 1`, at `A = B` a unit vector, attains it). Over `ℂ`
the hypothesis gives only `√2 ε`, and this is sharp: for `Sᴴ S - 1 = c (ξ₁ σx + ξ₂ σy)` with
Rademacher `ξ` and Pauli matrices `σx`, `σy`, `c ≤ 1/√2`, one has `E (x* E x)² ≤ c² ‖x‖⁴` for
every `x` but `E |e₁* E e₂|² = 2 c²`. A `𝕜` form with `√2 ε` is added when a complex consumer
appears. Design: `docs/design/Sketching-S1.md` §3.6, §7 Q2.

## Main results

* `NLAlib.HasJLMoment.integral_frobNorm_conjTranspose_mul_sub_rpow_le`: approximate matrix
  multiplication in `L^p`.
* `NLAlib.HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le`: its tail.
* `NLAlib.HasJLMoment.hasSubspaceEmbedding`, `NLAlib.HasJLMoment.isObliviousSubspaceEmbedding`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k n q r : Type*} [Fintype k]
  [Fintype n] [Fintype q] [Fintype r] {S : Ω → Matrix k n ℝ} {ε δ p : ℝ}

/-- The `p`-th power of the approximate-matrix-multiplication error is integrable. -/
theorem HasJLMoment.integrable_frobNorm_conjTranspose_mul_sub_rpow (h : HasJLMoment S ε δ p μ)
    (hp : 2 ≤ p) (hS : AEMeasurable S μ) (A : Matrix n q ℝ) (B : Matrix n r ℝ) :
    Integrable (fun ω => frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ p) μ := by
  sorry

/-- **Approximate matrix multiplication from the JL moment property**: for a real sketch with
the `(ε, δ, p)` JL moment property, `p ≥ 2`,
`E ‖Aᴴ Sᴴ S B - Aᴴ B‖_F^p ≤ (ε ‖A‖_F ‖B‖_F)^p δ`. [Woodruff2014, Theorem 13]; Woodruff has
`3 ε`; the constant `1` here is optimal (`Sᴴ S = (1 + ε) • 1` attains it). Over `ℝ` only: over
`ℂ` the hypothesis gives only `√2 ε`, sharply, as `Sᴴ S - 1 = c (ξ₁ σx + ξ₂ σy)` shows
(Rademacher `ξ`, Pauli `σx`, `σy`, `c ≤ 1/√2`: `E (x* E x)² ≤ c² ‖x‖⁴`, `E |e₁* E e₂|² = 2 c²`).
Result: amm-ose -/
theorem HasJLMoment.integral_frobNorm_conjTranspose_mul_sub_rpow_le (h : HasJLMoment S ε δ p μ)
    (hε : 0 ≤ ε) (hp : 2 ≤ p) (hS : AEMeasurable S μ) (A : Matrix n q ℝ) (B : Matrix n r ℝ) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ p ∂μ ≤
      (ε * frobNorm A * frobNorm B) ^ p * δ := by
  sorry

/-- **Approximate matrix multiplication, tail form**: for nonzero `A`, `B`,
`P(ε ‖A‖_F ‖B‖_F ≤ ‖Aᴴ Sᴴ S B - Aᴴ B‖_F) ≤ δ`. [Woodruff2014, Theorem 13]; there `3 ε`. -/
theorem HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le (h : HasJLMoment S ε δ p μ)
    (hε : 0 < ε) (hp : 2 ≤ p) (hS : AEMeasurable S μ) {A : Matrix n q ℝ} {B : Matrix n r ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    μ.real {ω | ε * frobNorm A * frobNorm B ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      δ := by
  sorry

/-- **The JL moment property gives subspace embeddings**: for `U` with orthonormal columns, a
real sketch with the `(ε, δ, p)` JL moment property, `p ≥ 2`, is a random subspace embedding for
`range U` with distortion `ε · card q` and failure probability `δ`. [Woodruff2014, proof of
Theorem 9] (Theorems 13 and 14). -/
theorem HasJLMoment.hasSubspaceEmbedding [DecidableEq q] (h : HasJLMoment S ε δ p μ)
    (hε : 0 < ε) (hp : 2 ≤ p) (hS : AEMeasurable S μ) (hδ : 0 ≤ δ) {U : Matrix n q ℝ}
    (hU : HasOrthonormalCols U) :
    HasSubspaceEmbedding S U (1 - ε * Fintype.card q) (1 + ε * Fintype.card q) δ μ := by
  sorry

/-- **The JL moment property gives an OSE**: a real sketch with the `(ε, δ, p)` JL moment
property, `p ≥ 2`, is an OSE for every dimension `d` with distortion `ε d` and failure
probability `δ`; no `d ≤ card n` is needed. [Woodruff2014, proof of Theorem 9] (Theorems 13
and 14). -/
theorem HasJLMoment.isObliviousSubspaceEmbedding (h : HasJLMoment S ε δ p μ) (hε : 0 < ε)
    (hp : 2 ≤ p) (hS : AEMeasurable S μ) (hδ : 0 ≤ δ) (d : ℕ) :
    IsObliviousSubspaceEmbedding S d (1 - ε * d) (1 + ε * d) δ μ := by
  sorry

end NLAlib
