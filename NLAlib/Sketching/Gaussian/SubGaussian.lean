/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.IndependentRows
public import NLAlib.Probability.SubGaussian.SquareSum
public import NLAlib.RandomMatrix.SubGaussian.ExtremeSingularValues
public import NLAlib.Sketching.Properties.Isotropic
public import NLAlib.Sketching.Properties.JohnsonLindenstraussNet

/-!
# Sub-Gaussian sketches

The sub-Gaussian sketch is `S = (√k)⁻¹ • X` for a random `X : Matrix k n ℝ` (`k = card k` rows)
whose rows are independent, isotropic and sub-Gaussian with proxy `c` (the three hypotheses of
`NLAlib/RandomMatrix/SubGaussian/ExtremeSingularValues.lean`, suffix `_of_isSubgaussianVector`,
always in the order `hind`, `hsub`, `hiso`). It is written out in each statement,
`fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω`; there is no named sketch law. Its isotropy is
`NLAlib.isIsotropicSketch_smul_of_isIsotropic` (no independence needed), so it gets no isotropy
statement here.

It has the distributional Johnson–Lindenstrauss property with Vershynin's two-regime tail
`2 exp (-C k min (ε²/c², ε/c))`, `C = subgaussianJLConstant` (Bernstein's inequality on the
centred squares `⟨Xᵢ, x⟩² - 1`), and, for rows with proxy `1` and fourth directional moments at
most `3`, the tail `2 exp (-k (ε²/4 - ε³/6))` of Dasgupta and Gupta (Achlioptas's argument;
incomparable, CONTRIBUTING §5.2 rule 4). It has the JL moment property at `p = 2`, and is an
oblivious subspace embedding and injection through JL plus a net
(`NLAlib.HasJLProperty.isObliviousSubspaceEmbedding` at `ε / 2`); that route dominates the
rows theorem's Gram sandwich in every regime (`docs/design/Sketching-S3.md` §7 Q1). Matrices with
independent sub-Gaussian entries of unit variance reach the rows hypotheses through
`NLAlib.iIndepFun_row_of_iIndepFun_entry`; only their JL tail is stated. The sample sizes are
named quantities with nonnegativity, monotonicity and an explicit comparison.

Degenerate cases: for empty `k`, `S = 0`, the JL bounds are `2` and the OSE bounds `2 · 9^d`, all
true, but `S` is not isotropic, hence `[Nonempty k]` on the OSI and the moment. With rows and
columns present the hypotheses force `1 ≤ c`; for `c = 0`, `ε / 0 = 0` and the bound is `2`. No
`0 ≤ ε` on the Bernstein tails: for `ε < 0` the bound exceeds `2`. For `ε = 1` the lower JL event
is `{S x = 0}`, which need not be null (for signs, probability `2^{-k}` at `x = (1, 1)/√2`); for
`ε > 1` it is empty, and the lower OSE constant `1 - ε ≤ 0` is vacuous
(`NLAlib.isSubspaceInjection_of_nonpos`). Design: `docs/design/Sketching-S3.md` §3.3, §8.

This file is a skeleton of Sketching stage S3; every proof is deferred.

## Main definitions

* `NLAlib.subgaussianJLConstant`: the constant `C` of the sub-Gaussian JL tail.
* `NLAlib.subgaussianJLDim`, `NLAlib.subgaussianEmbeddingDim`: sample sizes.

## Main results

* `NLAlib.hasJLProperty_of_isSubgaussianVector`: sub-Gaussian distributional JL.
* `NLAlib.hasJLProperty_of_isSubgaussianVector_of_integral_pow_four_le`: the Dasgupta–Gupta
  tail for proxy `1` and Gaussian fourth moments.
* `NLAlib.hasJLMoment_of_isSubgaussianVector`: the JL moment property at `p = 2`.
* `NLAlib.isObliviousSubspaceEmbedding_of_isSubgaussianVector`,
  `NLAlib.isObliviousSubspaceInjection_of_isSubgaussianVector`.
* `NLAlib.hasJLProperty_of_iIndepFun_entry`: JL for independent sub-Gaussian entries.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal

namespace NLAlib

/-! ### The constant and the sample sizes -/

/-- The constant `C` of the sub-Gaussian JL tail `2 exp (-C k min (ε²/c², ε/c))`. Unspecified in
[Vershynin2018, Exercise 5.3.3, Theorem 2.8.1 (2020 draft)]; the prototype had `1/(256 e²)`, for
`ε < 1` only. The value proved is `1/64`: the proof reaches `min (ε²/(64 c²)) (ε/(8 c))` (the
centred square's parameters `(32 c², 4 c)` and Bernstein's inequality), whose linear part is `8`
times this one's and is given up for Vershynin's shape. Larger is better; consumers use only
`subgaussianJLConstant_pos` and `le_subgaussianJLConstant`. -/
noncomputable irreducible_def subgaussianJLConstant : ℝ := 1 / 64

/-- The sub-Gaussian JL constant is positive. -/
theorem subgaussianJLConstant_pos : 0 < subgaussianJLConstant := by
  sorry

/-- An explicit lower bound on `subgaussianJLConstant`. -/
theorem le_subgaussianJLConstant : 1 / 64 ≤ subgaussianJLConstant := by
  sorry

/-- The **sub-Gaussian JL dimension** `c² log (2/δ) / (C ε²)`, `C = subgaussianJLConstant`: for
`0 < ε ≤ c`, at least this many rows give the JL property with failure `δ`
(`NLAlib.hasJLProperty_of_isSubgaussianVector_of_subgaussianJLDim_le`). Junk: for `δ > 2` the
logarithm is negative, and the value is `0` at `ε = 0`. -/
noncomputable irreducible_def subgaussianJLDim (c ε δ : ℝ) : ℝ :=
  c ^ 2 * Real.log (2 / δ) / (subgaussianJLConstant * ε ^ 2)

/-- The **sub-Gaussian embedding dimension** `4 c² (d log 9 + log (2/δ)) / (C ε²)`,
`C = subgaussianJLConstant`: for `0 < ε ≤ 2c`, at least this many rows give an oblivious
`1 ∓ ε` embedding for dimension `d` with failure `δ`
(`NLAlib.isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le`).
Junk: the value is `0` at `ε = 0`, and negative for `δ > 2 · 9 ^ d`. -/
noncomputable irreducible_def subgaussianEmbeddingDim (c : ℝ) (d : ℕ) (ε δ : ℝ) : ℝ :=
  4 * c ^ 2 * (d * Real.log 9 + Real.log (2 / δ)) / (subgaussianJLConstant * ε ^ 2)

section Sizes

variable {c c' ε ε' δ δ' : ℝ} {d d' : ℕ}

/-- The sub-Gaussian JL dimension is nonnegative for `0 < δ ≤ 2`. -/
theorem subgaussianJLDim_nonneg (c ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    0 ≤ subgaussianJLDim c ε δ := by
  sorry

/-- The sub-Gaussian JL dimension is monotone in `0 ≤ c` and antitone in `ε > 0` and `δ > 0`
(for `δ ≤ 2`). -/
theorem subgaussianJLDim_mono (hc : 0 ≤ c) (hcc' : c ≤ c') (hε : 0 < ε) (hεε' : ε ≤ ε')
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') (hδ2 : δ ≤ 2) :
    subgaussianJLDim c ε' δ' ≤ subgaussianJLDim c' ε δ := by
  sorry

/-- An explicit upper bound on the sub-Gaussian JL dimension: `64 c² log (2/δ) / ε²`. -/
theorem subgaussianJLDim_le (c ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    subgaussianJLDim c ε δ ≤ 64 * c ^ 2 * Real.log (2 / δ) / ε ^ 2 := by
  sorry

/-- The sub-Gaussian embedding dimension is nonnegative for `0 < δ ≤ 2`. -/
theorem subgaussianEmbeddingDim_nonneg (c : ℝ) (d : ℕ) (ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    0 ≤ subgaussianEmbeddingDim c d ε δ := by
  sorry

/-- The sub-Gaussian embedding dimension is monotone in `0 ≤ c` and in `d`, and antitone in
`ε > 0` and `δ > 0` (for `δ ≤ 2`). -/
theorem subgaussianEmbeddingDim_mono (hc : 0 ≤ c) (hcc' : c ≤ c') (hd : d ≤ d') (hε : 0 < ε)
    (hεε' : ε ≤ ε') (hδ : 0 < δ) (hδδ' : δ ≤ δ') (hδ2 : δ ≤ 2) :
    subgaussianEmbeddingDim c d ε' δ' ≤ subgaussianEmbeddingDim c' d' ε δ := by
  sorry

/-- An explicit upper bound on the sub-Gaussian embedding dimension,
`576 c² (d + log (2/δ)) / ε²` (`256 log 9 ≤ 576`): [Woodruff2014, Theorem 6]'s
`Θ ((d + log (1/δ))/ε²)` with an explicit constant. -/
theorem subgaussianEmbeddingDim_le (c : ℝ) (d : ℕ) (ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    subgaussianEmbeddingDim c d ε δ ≤ 576 * c ^ 2 * (d + Real.log (2 / δ)) / ε ^ 2 := by
  sorry

end Sizes

/-! ### Independent isotropic sub-Gaussian rows -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k n : Type*} [Fintype k]
  [Fintype n] {X : Ω → Matrix k n ℝ} {c : ℝ≥0} {ε δ : ℝ} {d : ℕ}

section Rows

variable [DecidableEq n]

/-- **Sub-Gaussian distributional JL**: for `X` with independent, isotropic, sub-Gaussian rows
with proxy `c`, the sketch `(√k)⁻¹ • X` has the JL property at every `ε` with failure
`2 exp (-C k min (ε²/c², ε/c))`, `C = subgaussianJLConstant`. [Vershynin2018, Exercise 5.3.3
(2020 draft)], there with an unspecified constant. Replaces the prototype's
`measure_lt_abs_mulVec_sq_sub_le_of_independent_isotropic_rows` (constant `1/(256 e²)`, `ε < 1`,
`K ≥ 1` assumed). For proxy `1` and fourth directional moments at most `3`,
`NLAlib.hasJLProperty_of_isSubgaussianVector_of_integral_pow_four_le` is better for
`ε ≲ 1.43` and this one beyond.
Result: jl-subgaussian -/
theorem hasJLProperty_of_isSubgaussianVector (hind : iIndepFun (fun i ω => X ω i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε
      (2 * Real.exp (-(subgaussianJLConstant * Fintype.card k *
        min (ε ^ 2 / (c : ℝ) ^ 2) (ε / c)))) μ := by
  sorry

/-- **Dasgupta–Gupta tail for rows with Gaussian fourth moments**: for `X` with independent,
isotropic rows, sub-Gaussian with proxy `1`, with `E ⟨Xᵢ, x⟩⁴ ≤ 3 ‖x‖⁴`, and `0 ≤ ε`, the
sketch `(√k)⁻¹ • X` has the JL property with failure `2 exp (-k (ε²/4 - ε³/6))`, the Gaussian
sketch's (`NLAlib.hasJLProperty_of_hasLaw_gaussianMatrix`). From
`NLAlib.measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun` at `Yᵢ = ⟨Xᵢ, x⟩`.
[Woodruff2014, §2.1, after Theorem 6] attributes this to Achlioptas for signs; constants of
[Achlioptas2003, Theorem 1.1], locator to confirm (`docs/PORT_SKETCHING.md` §7.2). Incomparable
with `NLAlib.hasJLProperty_of_isSubgaussianVector` at `c = 1` (CONTRIBUTING §5.2 rule 4): this
one is better for `ε ≲ 1.43` (sixteen times the exponent at small `ε`), that one beyond, and
needs no fourth-moment hypothesis.
Result: jl-subgaussian -/
theorem hasJLProperty_of_isSubgaussianVector_of_integral_pow_four_le
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) 1 μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ)
    (h4 : ∀ i (x : n → ℝ), ∫ ω, (x ⬝ᵥ X ω i) ^ 4 ∂μ ≤ 3 * ‖WithLp.toLp 2 x‖ ^ 4) (hε : 0 ≤ ε) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε
      (2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6)))) μ := by
  sorry

/-- **Sub-Gaussian JL moment** at `p = 2`: `E (‖S x‖² - 1)² = (E ⟨Xᵢ, x⟩⁴ - 1)/k` on average over
the rows, and `E ⟨Xᵢ, x⟩⁴ ≤ 16 c²` (`HasSubgaussianMGF.integral_abs_rpow_le` at `p = 4`), so the
JL moment property holds with `δ = (16 c² - 1)/(k ε²)`. [Woodruff2014, Definition 12] for the
property; the constant is the closed form of the sub-Gaussian fourth moment bound. -/
theorem hasJLMoment_of_isSubgaussianVector [Nonempty k] (hind : iIndepFun (fun i ω => X ω i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (hε : 0 < ε) :
    HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε
      ((16 * (c : ℝ) ^ 2 - 1) / (Fintype.card k * ε ^ 2)) 2 μ := by
  sorry

/-- **Sub-Gaussian OSE**: for `X` with independent, isotropic, sub-Gaussian rows with proxy `c`,
`(√k)⁻¹ • X` is an oblivious `1 ∓ ε` subspace embedding for dimension `d` with failure
`2 · 9^d exp (-C k min (ε²/(4c²), ε/(2c)))`, `C = subgaussianJLConstant`: JL plus a net at `ε/2`
(`NLAlib.HasJLProperty.isObliviousSubspaceEmbedding`). [Vershynin2018, Theorem 4.6.1, (4.22)
(2020 draft)], there for the singular values, `K² max (δ, δ²)` with an unspecified constant; it
dominates the rows theorem's Gram sandwich in every regime (`docs/design/Sketching-S3.md` §7 Q1).
Result: subgaussian-ose -/
theorem isObliviousSubspaceEmbedding_of_isSubgaussianVector (hind : iIndepFun (fun i ω => X ω i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (d : ℕ) :
    IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) (1 + ε)
      (2 * 9 ^ d * Real.exp (-(subgaussianJLConstant * Fintype.card k *
        min (ε ^ 2 / (4 * (c : ℝ) ^ 2)) (ε / (2 * c))))) μ := by
  sorry

/-- **Sub-Gaussian OSI**: the lower half of
`NLAlib.isObliviousSubspaceEmbedding_of_isSubgaussianVector`, with the sketch's isotropy
(`NLAlib.isIsotropicSketch_smul_of_isIsotropic`). [Vershynin2018, Theorem 4.6.1 (2020 draft)];
[CamanoEpperlyMeyerTropp2025, Definition 1.2] for the notion. -/
theorem isObliviousSubspaceInjection_of_isSubgaussianVector [Nonempty k]
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (d : ℕ) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε)
      (2 * 9 ^ d * Real.exp (-(subgaussianJLConstant * Fintype.card k *
        min (ε ^ 2 / (4 * (c : ℝ) ^ 2)) (ε / (2 * c))))) μ := by
  sorry

/-- **Sub-Gaussian JL, sample-size form**: for `0 < ε ≤ c`, `0 < δ` and at least
`subgaussianJLDim c ε δ` rows, the JL property holds with failure `δ` (for `ε ≤ c` the `min` of
the tail is its quadratic part). [Vershynin2018, Exercise 5.3.3 (2020 draft)]. -/
theorem hasJLProperty_of_isSubgaussianVector_of_subgaussianJLDim_le
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (hε : 0 < ε) (hεc : ε ≤ c) (hδ : 0 < δ)
    (hk : subgaussianJLDim c ε δ ≤ Fintype.card k) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε δ μ := by
  sorry

/-- **Sub-Gaussian OSE, sample-size form**: for `0 < ε ≤ 2c`, `0 < δ` and at least
`subgaussianEmbeddingDim c d ε δ` rows, `(√k)⁻¹ • X` is an oblivious `1 ∓ ε` subspace embedding
for dimension `d` with failure `δ`. [Vershynin2018, Theorem 4.6.1 (2020 draft)];
[Woodruff2014, Theorem 6]. -/
theorem isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (hε : 0 < ε) (hεc : ε ≤ 2 * c) (hδ : 0 < δ)
    (hk : subgaussianEmbeddingDim c d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) (1 + ε) δ
      μ := by
  sorry

/-- **Sub-Gaussian OSI, sample-size form**: the injection twin of
`NLAlib.isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le`. -/
theorem isObliviousSubspaceInjection_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le
    [Nonempty k] (hind : iIndepFun (fun i ω => X ω i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (hε : 0 < ε) (hεc : ε ≤ 2 * c) (hδ : 0 < δ)
    (hk : subgaussianEmbeddingDim c d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) δ μ := by
  sorry

end Rows

/-! ### Independent sub-Gaussian entries -/

/-- **Sub-Gaussian JL for independent entries**: for `X` with independent entries, each
sub-Gaussian with proxy `c` and of unit variance, `(√k)⁻¹ • X` has the JL property with failure
`2 exp (-C k min (ε²/c², ε/c))`, `C = subgaussianJLConstant`. The mean is `0` by
`HasSubgaussianMGF.integral_eq_zero` (the prototype's `hmean` is dropped). The rows hypotheses
follow by `NLAlib.iIndepFun_row_of_iIndepFun_entry`, `IsSubgaussianVector.of_iIndepFun` and
`IsIsotropic.of_iIndepFun`; the other rows theorems apply to entries through the same three
steps. [Vershynin2018, Exercise 5.3.3 (2020 draft)]. Replaces the prototype's
`…_of_independent_subgaussian_entries`.
Result: jl-subgaussian -/
theorem hasJLProperty_of_iIndepFun_entry
    (hind : iIndepFun (fun p : k × n => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε
      (2 * Real.exp (-(subgaussianJLConstant * Fintype.card k *
        min (ε ^ 2 / (c : ℝ) ^ 2) (ε / c)))) μ := by
  sorry

end NLAlib
