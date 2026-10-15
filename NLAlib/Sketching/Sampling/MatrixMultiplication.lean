/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.MatrixConcentration.Variance
public import NLAlib.Probability.Tail
public import NLAlib.Sketching.Sampling.RowSampling

/-!
# Approximate matrix multiplication by row sampling

For `A : Matrix n q 𝕜`, `B : Matrix n r 𝕜` and the row-sampling sketch `S` with law
`NLAlib.samplingSketch k p`, the sampled product `Aᴴ Sᴴ S B` is the average of `card k` i.i.d.
rank-one atoms `(card k · p ι)⁻¹ (A ι)ᴴ B ι` (`NLAlib.conjTranspose_samplingSketchMatrix_mul_mul`).
It is unbiased when every zero weight sits on a row where `A` or `B` vanishes, its squared
Frobenius error has the exact mean `(∑ i, ‖A i‖² ‖B i‖² / p i - ‖Aᴴ B‖_F²) / k`, and under the
domination `‖A i‖ ‖B i‖ ≤ L p i` that mean is at most `L ‖A‖_F ‖B‖_F / k`; Markov's inequality
gives the tail. The error and its event are those of the JL-moment form
(`NLAlib.HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le`), here over `𝕜`.

Degenerate cases: for empty `k`, `S = 0` and the sampled product is `0`, hence `[Nonempty k]` on
every mean and tail; the integrability statements need neither it nor `∑ i, p i = 1`. A zero
weight with `A i ≠ 0` and `B i ≠ 0` biases the estimator, which the support hypothesis excludes and
the domination hypothesis implies. Design: `docs/design/Sketching-S4.md` §3.3, §8.

This file is a skeleton of Sketching stage S4: the statements are final; the proofs of the
integrability statements, unbiasedness, the exact second moment and the domination bound are
deferred (`sorry`), and the two tails are proved from the domination bound.

## Main results

* `NLAlib.integral_conjTranspose_mul_mul_of_hasLaw_samplingSketch`: unbiasedness.
* `NLAlib.integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch`: the exact second
  moment.
* `NLAlib.integral_frobNorm_conjTranspose_mul_sub_sq_le_of_hasLaw_samplingSketch`: the
  domination bound.
* `NLAlib.measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch`,
  `NLAlib.measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch_of_ne_zero`:
  tails.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n q r : Type*} [Fintype k] [Fintype n] [Fintype q] [Fintype r] [DecidableEq n]
  {S : Ω → Matrix k n 𝕜} {p : n → ℝ≥0} {A : Matrix n q 𝕜} {B : Matrix n r 𝕜} {L ε t : ℝ}

/-! ### The sampled product -/

/-- The sampled product `Aᴴ Sᴴ S B` of a row-sampling sketch is integrable, for any weights and
any number of samples: the sketch takes finitely many values. -/
theorem integrable_conjTranspose_mul_mul_of_hasLaw_samplingSketch [DecidableEq r]
    (hS : HasLaw S (samplingSketch k p) μ) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    Integrable (fun ω => Aᴴ * (S ω)ᴴ * S ω * B) μ := by
  sorry

/-- **Row sampling is unbiased for matrix products**: `E [Aᴴ Sᴴ S B] = Aᴴ B` when every zero
weight sits on a row where `A` or `B` vanishes (in particular when every weight is positive).
[MartinssonTropp2020, §7.1] (the sampled estimator, positive weights). -/
theorem integral_conjTranspose_mul_mul_of_hasLaw_samplingSketch [Nonempty k] [DecidableEq r]
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hsupport : ∀ i, p i = 0 → A i = 0 ∨ B i = 0) :
    ∫ ω, Aᴴ * (S ω)ᴴ * S ω * B ∂μ = Aᴴ * B := by
  sorry

/-! ### The Frobenius error -/

/-- The squared Frobenius error of the sampled product is integrable, for any weights and any
number of samples. -/
theorem integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch
    (hS : HasLaw S (samplingSketch k p) μ) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    Integrable (fun ω => frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2) μ := by
  sorry

/-- **Approximate matrix multiplication by sampling, exact second moment**:
`E ‖Aᴴ Sᴴ S B - Aᴴ B‖_F² = (∑ i, ‖A i‖² ‖B i‖² / p i - ‖Aᴴ B‖_F²) / k` when every zero weight sits
on a row where `A` or `B` vanishes (there the term is `0 / 0 = 0`). [MartinssonTropp2020, §7.1]
(the estimator); Drineas, Kannan and Mahoney 2006, Lemma 4 (the identity, citation to confirm).
Result: amm-sampling -/
theorem integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch [Nonempty k]
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hsupport : ∀ i, p i = 0 → A i = 0 ∨ B i = 0) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ =
      (∑ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2 / p i -
        frobNorm (Aᴴ * B) ^ 2) / Fintype.card k := by
  sorry

/-- **Approximate matrix multiplication by sampling, domination form**: if
`‖A i‖ ‖B i‖ ≤ L p i` for every row, `E ‖Aᴴ Sᴴ S B - Aᴴ B‖_F² ≤ L ‖A‖_F ‖B‖_F / k`. Zero weights
are allowed. At the optimal weights `p i ∝ ‖A i‖ ‖B i‖` (`L = ∑ i, ‖A i‖ ‖B i‖`) this is
`‖A‖_F² ‖B‖_F² / k` by Cauchy–Schwarz, and `β`-approximations of them are `L = W/β`.
[MartinssonTropp2020, §7.1]; Drineas, Kannan and Mahoney 2006, Lemma 4 (there the bound
`‖A‖_F² ‖B‖_F² / (β k)`, citation to confirm).
Result: amm-sampling -/
theorem integral_frobNorm_conjTranspose_mul_sub_sq_le_of_hasLaw_samplingSketch [Nonempty k]
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hdom : ∀ i, ‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖ ≤ L * p i) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ ≤
      L * frobNorm A * frobNorm B / Fintype.card k := by
  sorry

/-- **The tail of approximate matrix multiplication by sampling**: under the domination
`‖A i‖ ‖B i‖ ≤ L p i`, the Frobenius error exceeds `t > 0` with probability at most
`L ‖A‖_F ‖B‖_F / (k t²)` (Markov on the square). [MartinssonTropp2020, §7.1]. -/
theorem measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch [Nonempty k]
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hdom : ∀ i, ‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖ ≤ L * p i) (ht : 0 < t) :
    μ.real {ω | t ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      L * frobNorm A * frobNorm B / (Fintype.card k * t ^ 2) := by
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketch hp)
  calc μ.real {ω | t ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)}
      ≤ μ.real {ω | t ^ 2 ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2} :=
        measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω => pow_le_pow_left₀ ht.le hω 2)
    _ ≤ (∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ) / t ^ 2 :=
        measureReal_ge_le_integral_div (ae_of_all _ fun ω => sq_nonneg _)
          (integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch hS A B)
          (by positivity)
    _ ≤ (L * frobNorm A * frobNorm B / Fintype.card k) / t ^ 2 :=
        div_le_div_of_nonneg_right
          (integral_frobNorm_conjTranspose_mul_sub_sq_le_of_hasLaw_samplingSketch hS hp hdom)
          (by positivity)
    _ = _ := by rw [div_div]

/-- **The relative tail of approximate matrix multiplication by sampling**: under the domination
`‖A i‖ ‖B i‖ ≤ L p i`, the Frobenius error exceeds `ε ‖A‖_F ‖B‖_F` with probability at most
`L / (k ε² ‖A‖_F ‖B‖_F)`, for `ε > 0` and nonzero `A`, `B`: the event of the JL-moment form
`NLAlib.HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le`, the instance
`t = ε ‖A‖_F ‖B‖_F` of
`NLAlib.measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch`.
[MartinssonTropp2020, §7.1]. -/
theorem measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch_of_ne_zero
    [Nonempty k] (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hdom : ∀ i, ‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖ ≤ L * p i) (hε : 0 < ε)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    μ.real {ω | ε * frobNorm A * frobNorm B ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      L / (Fintype.card k * ε ^ 2 * frobNorm A * frobNorm B) := by
  have hA' : 0 < frobNorm A :=
    (frobNorm_nonneg A).lt_of_ne (Ne.symm (frobNorm_eq_zero_iff.not.2 hA))
  have hB' : 0 < frobNorm B :=
    (frobNorm_nonneg B).lt_of_ne (Ne.symm (frobNorm_eq_zero_iff.not.2 hB))
  have hK : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine (measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch hS hp hdom
    (t := ε * frobNorm A * frobNorm B) (by positivity)).trans (le_of_eq ?_)
  field_simp

end NLAlib
