/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.Probability.Law
public import NLAlib.Probability.Tail

/-!
# The Johnson–Lindenstrauss property

A random sketch `S : Ω → Matrix k n 𝕜` has the *distributional Johnson–Lindenstrauss property*
with distortion `ε` and failure probability `δ` when, for every unit vector `x`,
`P(ε ≤ |‖S x‖² - 1|) ≤ δ`; it has the *JL moment property* with exponent `p` when
`E |‖S x‖² - 1|^p ≤ ε^p δ` for unit `x`. The moment property implies the tail property
(Markov), and both scale to every nonzero vector; the tail property gives the
Johnson–Lindenstrauss lemma for finitely many points by a union bound over pairs. The moment
property also gives approximate matrix multiplication
(`NLAlib.Sketching.Properties.MatrixMultiplication`).

Both are stated with the non-strict threshold event `{ε ≤ X}`. Design:
`docs/design/Sketching-S1.md` §3.5.

## Main definitions

* `NLAlib.HasJLProperty S ε δ μ`, `NLAlib.HasJLMoment S ε δ p μ`.

## Main results

* `NLAlib.HasJLProperty.measure_exists_abs_norm_mulVec_sq_sub_ge_le`: the JL lemma.
* `NLAlib.HasJLMoment.hasJLProperty`: moments give tails.
* `NLAlib.HasJLMoment.integral_abs_norm_mulVec_sq_sub_rpow_le`: the moment bound for every `x`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n : Type*} [Fintype k] [Fintype n] {S : Ω → Matrix k n 𝕜} {ε ε' δ δ' p : ℝ}

/-- **Distributional Johnson–Lindenstrauss property** on unit vectors: for every unit `x`,
`P(ε ≤ |‖S x‖² - 1|) ≤ δ`. [Woodruff2014, proof of Lemma 18]; [MartinssonTropp2020, §8.6]. -/
def HasJLProperty (S : Ω → Matrix k n 𝕜) (ε δ : ℝ) (μ : Measure Ω) : Prop :=
  ∀ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 →
    μ.real {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1|} ≤ δ

/-- **JL moment property** with exponent `p : ℝ`: for every unit `x`,
`E |‖S x‖² - 1|^p ≤ ε^p δ`. Junk for `ε < 0` (real powers of negative numbers).
[Woodruff2014, Definition 12]. -/
structure HasJLMoment (S : Ω → Matrix k n 𝕜) (ε δ p : ℝ) (μ : Measure Ω) : Prop where
  /-- The `p`-th moment of the distortion is finite at every unit vector. -/
  integrable : ∀ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 →
    Integrable (fun ω => |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1| ^ p) μ
  /-- The `p`-th moment of the distortion is at most `ε^p δ` at every unit vector. -/
  integral_le : ∀ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 →
    ∫ ω, |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1| ^ p ∂μ ≤ ε ^ p * δ

/-- The JL property depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.hasJLProperty_iff {ν : Measure (Matrix k n 𝕜)}
    (hS : HasLaw S ν μ) : HasJLProperty S ε δ μ ↔ HasJLProperty id ε δ ν := by
  sorry

/-- The JL moment property depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.hasJLMoment_iff {ν : Measure (Matrix k n 𝕜)}
    (hS : HasLaw S ν μ) : HasJLMoment S ε δ p μ ↔ HasJLMoment id ε δ p ν := by
  sorry

/-- The JL property holds with any larger distortion and failure probability. -/
theorem HasJLProperty.mono [IsFiniteMeasure μ] (h : HasJLProperty S ε δ μ) (hε : ε ≤ ε')
    (hδ : δ ≤ δ') : HasJLProperty S ε' δ' μ := by
  sorry

/-- The JL moment property holds with any larger distortion and failure probability, for
`0 ≤ ε`, `0 ≤ p`, `0 ≤ δ`. -/
theorem HasJLMoment.mono (h : HasJLMoment S ε δ p μ) (hε : ε ≤ ε') (hδ : δ ≤ δ') (hε0 : 0 ≤ ε)
    (hp : 0 ≤ p) (hδ0 : 0 ≤ δ) : HasJLMoment S ε' δ' p μ := by
  sorry

/-- The JL property at a nonzero vector `x`: `P(ε ‖x‖² ≤ |‖S x‖² - ‖x‖²|) ≤ δ`. -/
theorem HasJLProperty.measure_abs_norm_mulVec_sq_sub_ge_le (h : HasJLProperty S ε δ μ)
    {x : n → 𝕜} (hx : x ≠ 0) :
    μ.real {ω | ε * ‖WithLp.toLp 2 x‖ ^ 2 ≤
      |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2|} ≤ δ := by
  sorry

/-- **Johnson–Lindenstrauss lemma**: for finitely many points `x i`, the probability that some
pairwise difference has its squared norm distorted by a factor `ε` or more is at most
`(card ι).choose 2 * δ` (union over unordered pairs). [Woodruff2014, Definition 3]; there
inner products on a finite set, here squared norms of differences.
Result: jl-lemma -/
theorem HasJLProperty.measure_exists_abs_norm_mulVec_sq_sub_ge_le (h : HasJLProperty S ε δ μ)
    (hδ : 0 ≤ δ) {ι : Type*} [Fintype ι] (x : ι → n → 𝕜) :
    μ.real {ω | ∃ i j, x i ≠ x j ∧ ε * ‖WithLp.toLp 2 (x i - x j)‖ ^ 2 ≤
      |‖WithLp.toLp 2 (S ω *ᵥ (x i - x j))‖ ^ 2 - ‖WithLp.toLp 2 (x i - x j)‖ ^ 2|} ≤
      (Fintype.card ι).choose 2 * δ := by
  sorry

/-- **Moments give tails**: the JL moment property implies the JL property with the same
`ε` and `δ` (Markov's inequality in `L^p`). [Woodruff2014, §2.2]. -/
theorem HasJLMoment.hasJLProperty (h : HasJLMoment S ε δ p μ) (hε : 0 < ε) (hp : 0 < p) :
    HasJLProperty S ε δ μ := by
  sorry

/-- The `p`-th moment of the distortion at any vector is integrable. -/
theorem HasJLMoment.integrable_abs_norm_mulVec_sq_sub_rpow (h : HasJLMoment S ε δ p μ)
    (hp : 0 < p) (x : n → 𝕜) :
    Integrable (fun ω => |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2| ^ p) μ := by
  sorry

/-- The JL moment bound at any vector: `E |‖S x‖² - ‖x‖²|^p ≤ ε^p δ ‖x‖^(2p)`. -/
theorem HasJLMoment.integral_abs_norm_mulVec_sq_sub_rpow_le (h : HasJLMoment S ε δ p μ)
    (hp : 0 < p) (x : n → 𝕜) :
    ∫ ω, |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2| ^ p ∂μ ≤
      ε ^ p * δ * ‖WithLp.toLp 2 x‖ ^ (2 * p) := by
  sorry

end NLAlib
