/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.Rademacher
public import NLAlib.Probability.QuadraticForm.Moments
public import NLAlib.Sketching.Gaussian.Gaussian
public import NLAlib.Sketching.Gaussian.SubGaussian

/-!
# Rademacher sketches

The sign sketch is `S = (√k)⁻¹ • X` for `X : Matrix k n ℝ` with independent random signs,
`HasLaw X (rademacherMatrix k n) μ`, where `rademacherMatrix k n` is the law of independent rows,
each a `rademacherVector n`. It is written out in each statement,
`fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω`, as for the Gaussian sketch.

It is an isotropic sketch, has the distributional Johnson–Lindenstrauss property with the
Gaussian sketch's exponent `ε²/4 - ε³/6` (Dasgupta and Gupta's; Achlioptas's argument, through
`NLAlib.hasJLProperty_of_isSubgaussianVector_of_integral_pow_four_le`, since
`E ⟨ξ, x⟩⁴ = 3 ‖x‖⁴ - 2 ∑ xⱼ⁴ ≤ 3 ‖x‖⁴`), the exact JL second moment `2 (‖x‖⁴ - ∑ xⱼ⁴)/k`, at
most the Gaussian's `2 ‖x‖⁴/k`, and is an oblivious subspace embedding and injection through JL
plus a net at `ε / 2`. The sample sizes are the Gaussian sketch's `NLAlib.jlDim`: `jlDim ε δ`
for JL and `jlDim (ε/2) (δ/9^d)` for the OSE and OSI. For `ε ≳ 1.43` the sub-Gaussian rows
theorem at `c = 1` (`NLAlib.hasJLProperty_of_isSubgaussianVector` with
`NLAlib.isSubgaussianVector_of_hasLaw_rademacherVector`) is better; it is not restated here.

Degenerate cases: for empty `k`, `S = 0`, which is not isotropic, hence `[Nonempty k]` on
isotropy, the OSI and the moments; the JL bound is `2` for `k = 0` and at least `2` for
`ε ≥ 3/2`. For `ε = 1` the lower JL event `{S x = 0}` has positive probability (`2^{-k}` at
`x = (1, 1)/√2`), and the proof covers it. Design: `docs/design/Sketching-S3.md` §3.3, §8.

This file is a skeleton of Sketching stage S3; every proof is deferred.

## Main definitions

* `NLAlib.rademacherMatrix k n`.

## Main results

* `NLAlib.isIsotropicSketch_of_hasLaw_rademacherMatrix`.
* `NLAlib.hasJLProperty_of_hasLaw_rademacherMatrix`: distributional JL.
* `NLAlib.integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_rademacherMatrix`: the exact second
  moment of the distortion.
* `NLAlib.hasJLMoment_of_hasLaw_rademacherMatrix`: the JL moment property at `p = 2`.
* `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix`,
  `NLAlib.isObliviousSubspaceInjection_of_hasLaw_rademacherMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

/-- The law of a matrix with independent random signs: independent rows, each a
`rademacherVector n`. -/
noncomputable abbrev rademacherMatrix (k n : Type*) [Fintype k] [Fintype n] :
    Measure (Matrix k n ℝ) :=
  Measure.pi fun _ : k => rademacherVector n

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k n : Type*} [Fintype k]
  [Fintype n] {X : Ω → Matrix k n ℝ} {ε δ : ℝ} {d : ℕ}

instance isProbabilityMeasure_rademacherMatrix : IsProbabilityMeasure (rademacherMatrix k n) :=
  sorry

/-- **The sign sketch is isotropic**: `E [Sᴴ S] = 1`, from the isotropy of each row
(`NLAlib.isIsotropic_of_hasLaw_rademacherVector`). [CamanoEpperlyMeyerTropp2025, Definition 1.2]
for the notion. -/
theorem isIsotropicSketch_of_hasLaw_rademacherMatrix [DecidableEq n] [Nonempty k]
    (hX : HasLaw X (rademacherMatrix k n) μ) :
    IsIsotropicSketch (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) μ := by
  sorry

/-- **Sign-sketch distributional JL** with Gaussian constants: for `0 ≤ ε`,
`P(ε ≤ |‖S x‖² - 1|) ≤ 2 exp (-k (ε²/4 - ε³/6))` at every unit `x`, the bound of
`NLAlib.hasJLProperty_of_hasLaw_gaussianMatrix`. From
`NLAlib.hasJLProperty_of_isSubgaussianVector_of_integral_pow_four_le`, with
`E ⟨ξ, x⟩⁴ = Var (⟨ξ, x⟩²) + ‖x‖⁴ = 3 ‖x‖⁴ - 2 ∑ xⱼ⁴`
(`NLAlib.variance_quadForm_of_hasLaw_rademacherVector` at `vecMulVec x x`).
[Woodruff2014, §2.1, after Theorem 6]; constants of [Achlioptas2003, Theorem 1.1], locator to
confirm (`docs/PORT_SKETCHING.md` §7.2). For `ε ≳ 1.43`,
`NLAlib.hasJLProperty_of_isSubgaussianVector` at `c = 1` is better.
Result: jl-rademacher -/
theorem hasJLProperty_of_hasLaw_rademacherMatrix (hX : HasLaw X (rademacherMatrix k n) μ)
    (hε : 0 ≤ ε) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε
      (2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6)))) μ := by
  sorry

/-- The squared distortion of the sign sketch is integrable. -/
theorem integrable_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_rademacherMatrix
    (hX : HasLaw X (rademacherMatrix k n) μ) (x : n → ℝ) :
    Integrable (fun ω => (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • X ω *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2) μ := by
  sorry

/-- **Exact second moment of the sign-sketch distortion**:
`E (‖S x‖² - ‖x‖²)² = 2 (‖x‖⁴ - ∑ xⱼ⁴)/k`, at most the Gaussian sketch's `2 ‖x‖⁴/k`
(`NLAlib.integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_gaussianMatrix`). By independence of
the rows and `NLAlib.variance_quadForm_of_hasLaw_rademacherVector` at `vecMulVec x x`
(`‖x xᵀ‖_F² = ‖x‖⁴`). -/
theorem integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_rademacherMatrix [Nonempty k]
    (hX : HasLaw X (rademacherMatrix k n) μ) (x : n → ℝ) :
    ∫ ω, (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • X ω *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 ∂μ =
        2 / Fintype.card k * (‖WithLp.toLp 2 x‖ ^ 4 - ∑ j, x j ^ 4) := by
  sorry

/-- **Sign-sketch JL moment** at `p = 2`, with `δ = 2/(k ε²)`, the Gaussian sketch's
(`NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix`). [Woodruff2014, Definition 12] for the
property. -/
theorem hasJLMoment_of_hasLaw_rademacherMatrix [Nonempty k] (hX : HasLaw X (rademacherMatrix k n) μ)
    (hε : 0 < ε) :
    HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε
      (2 / (Fintype.card k * ε ^ 2)) 2 μ := by
  sorry

/-- **Sign-sketch OSE**: for `0 ≤ ε`, `(√k)⁻¹ • X` is an oblivious `1 ∓ ε` subspace embedding for
dimension `d` with failure `2 · 9^d exp (-k (ε²/16 - ε³/48))`: JL plus a net at `ε/2`
(`NLAlib.HasJLProperty.isObliviousSubspaceEmbedding`). [Woodruff2014, §2.1, Theorem 6], there
with `O(ε)` and unspecified constants.
Result: rademacher-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix
    (hX : HasLaw X (rademacherMatrix k n) μ) (d : ℕ) (hε : 0 ≤ ε) :
    IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) (1 + ε)
      (2 * 9 ^ d * Real.exp (-(Fintype.card k * (ε ^ 2 / 16 - ε ^ 3 / 48)))) μ := by
  sorry

/-- **Sign-sketch OSI**: the lower half of
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix`, with the sketch's isotropy.
[CamanoEpperlyMeyerTropp2025, Definition 1.2] for the notion. -/
theorem isObliviousSubspaceInjection_of_hasLaw_rademacherMatrix [DecidableEq n] [Nonempty k]
    (hX : HasLaw X (rademacherMatrix k n) μ) (d : ℕ) (hε : 0 ≤ ε) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε)
      (2 * 9 ^ d * Real.exp (-(Fintype.card k * (ε ^ 2 / 16 - ε ^ 3 / 48)))) μ := by
  sorry

/-- **Sign-sketch JL, sample-size form**: for `0 < ε < 3/2`, `0 < δ` and at least `jlDim ε δ`
rows, the JL property holds with failure `δ`; the Gaussian sketch's size
(`NLAlib.hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le`). -/
theorem hasJLProperty_of_hasLaw_rademacherMatrix_of_jlDim_le
    (hX : HasLaw X (rademacherMatrix k n) μ) (hε : 0 < ε) (hε1 : ε < 3 / 2) (hδ : 0 < δ)
    (hk : jlDim ε δ ≤ Fintype.card k) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) ε δ μ := by
  sorry

/-- **Sign-sketch OSE, sample-size form**: for `0 < ε < 3`, `0 < δ` and at least
`jlDim (ε/2) (δ/9^d)` rows, `(√k)⁻¹ • X` is an oblivious `1 ∓ ε` subspace embedding for
dimension `d` with failure `δ`. -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix_of_jlDim_le
    (hX : HasLaw X (rademacherMatrix k n) μ) (hε : 0 < ε) (hε3 : ε < 3) (hδ : 0 < δ)
    (hk : jlDim (ε / 2) (δ / 9 ^ d) ≤ Fintype.card k) :
    IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) (1 + ε) δ
      μ := by
  sorry

/-- **Sign-sketch OSI, sample-size form**: the injection twin of
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix_of_jlDim_le`. -/
theorem isObliviousSubspaceInjection_of_hasLaw_rademacherMatrix_of_jlDim_le [DecidableEq n]
    [Nonempty k] (hX : HasLaw X (rademacherMatrix k n) μ) (hε : 0 < ε) (hε3 : ε < 3)
    (hδ : 0 < δ) (hk : jlDim (ε / 2) (δ / 9 ^ d) ≤ Fintype.card k) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) d (1 - ε) δ μ := by
  sorry

end NLAlib
