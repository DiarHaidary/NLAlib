/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.ChiSquareTails
public import NLAlib.RandomMatrix.Haar.Uniqueness

/-!
# Projections of a uniform unit vector

For `u` uniform on the unit sphere of `ℝⁿ` and `V : Matrix n k ℝ` with orthonormal columns,
`‖Vᴴ u‖²` is the squared length of the projection of `u` onto a fixed `k`-dimensional subspace.
Its law does not depend on `V`, and it is the law of `‖Qᴴ x‖²` for an `n × k` Haar frame `Q` and a
fixed unit `x`: this is the Haar sketch's Johnson–Lindenstrauss variable. This file gives the
law, the Chernoff tails of Dasgupta and Gupta (2003) around the mean `k / n`, on either side, and
the exact fourth moment `E ‖Vᴴ u‖⁴ = k (k + 2) / (n (n + 2))`.

There is no sphere-invariance lemma in the library: the tails go through `u = g / ‖g‖` for a
standard Gaussian `g` (`NLAlib.hasLaw_inv_norm_smul_of_hasLaw_gaussianVector`), the orthogonal
`W = [V, V⊥]ᴴ` from `NLAlib.HasOrthonormalCols.exists_fromCols` and
`NLAlib.hasLaw_mulVec_of_hasLaw_gaussianVector`, which reduce `‖Vᴴ u‖² ≤ c` to the event
`0 ≤ ∑ θᵢ gᵢ²` with two weights, and Chernoff's bound with
`NLAlib.integral_exp_sum_mul_sq_of_hasLaw_gaussianVector`. The fourth moment uses invariance
alone: `∑ uᵢ² = 1` and a `45°` rotation give `E u₁⁴ = 3 E u₁² u₂²` when `card n ≥ 2`; for
`card n = 1`, `u = ±1`.

This file is a skeleton of Sketching stage S2 (`docs/design/Sketching-S2.md` §3.2, §8); at the
wrap-up it merges into a Haar owner file.

## Main results

* `NLAlib.hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame`: `Qᴴ x` has the law of `Vᴴ u`.
* `NLAlib.measureReal_mul_div_le_norm_conjTranspose_mulVec_sq_le_of_hasLaw_uniformSphereVector`,
  `NLAlib.measureReal_norm_conjTranspose_mulVec_sq_le_mul_div_le_of_hasLaw_uniformSphereVector`:
  the two Chernoff tails.
* The relative deviation (in namespace `NLAlib`):
  `measureReal_abs_div_mul_norm_conjTranspose_mulVec_sq_sub_one_ge_le_of_hasLaw_uniformSphereVector`
* `NLAlib.integral_norm_conjTranspose_mulVec_pow_four_of_hasLaw_uniformSphereVector`: the fourth
  moment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k : Type*} [Fintype n]
  [Fintype k] [DecidableEq k] {u : Ω → n → ℝ} {V : Matrix n k ℝ} {ε β : ℝ}

/-- **A Haar frame applied to a fixed unit vector**: for an `n × k` Haar frame `Q` and a unit
`x`, `Qᴴ x` has the law of `Vᴴ u` for `u` uniform on the sphere and any `V` with orthonormal
columns (`hV` gives `card k ≤ card n`). By left invariance
(`NLAlib.HasOrthonormalCols.exists_mul_eq` sends `x` to a coordinate vector), `Q ~ P V` for a
square Haar frame `P`
(`NLAlib.hasLaw_mul_const_of_hasLaw_haarFrame`), and a column of `Pᴴ`
(`NLAlib.hasLaw_col_of_hasLaw_haarFrame`). -/
theorem hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame {Q : Ω → Matrix n k ℝ}
    (hQ : HasLaw Q (haarFrame n k) μ) (hV : HasOrthonormalCols V) {x : n → ℝ}
    (hx : ‖WithLp.toLp 2 x‖ = 1) :
    HasLaw (fun ω => (Q ω)ᴴ *ᵥ x) ((uniformSphereVector n).map (Vᴴ *ᵥ ·)) μ := by
  sorry

/-- **Projection of a uniform unit vector, upper tail**:
`P(β k / n ≤ ‖Vᴴ u‖²) ≤ exp ((k/2)(1 - β + log β))` for `β ≥ 1`. The exponent of Dasgupta and
Gupta (2003); [Vershynin2018, Lemma 5.3.2 (2020 draft)] has the fact with an unspecified
constant `c`. The `χ²_k` tail `NLAlib.measureReal_mul_card_le_norm_sq_le_of_hasLaw_gaussianVector`
is the limit `n → ∞`. -/
theorem measureReal_mul_div_le_norm_conjTranspose_mulVec_sq_le_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) (hβ : 1 ≤ β) :
    μ.real {ω | β * (Fintype.card k / Fintype.card n) ≤ ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2} ≤
      Real.exp (Fintype.card k / 2 * (1 - β + Real.log β)) := by
  sorry

/-- **Projection of a uniform unit vector, lower tail**:
`P(‖Vᴴ u‖² ≤ β k / n) ≤ exp ((k/2)(1 - β + log β))` for `0 < β ≤ 1`. The exponent of Dasgupta and
Gupta (2003); [Vershynin2018, Lemma 5.3.2 (2020 draft)] has the fact with an unspecified
constant `c`. -/
theorem measureReal_norm_conjTranspose_mulVec_sq_le_mul_div_le_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) (hβ0 : 0 < β)
    (hβ : β ≤ 1) :
    μ.real {ω | ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2 ≤ β * (Fintype.card k / Fintype.card n)} ≤
      Real.exp (Fintype.card k / 2 * (1 - β + Real.log β)) := by
  sorry

/-- **Projection of a uniform unit vector, relative deviation**:
`P(ε ≤ |(n/k) ‖Vᴴ u‖² - 1|) ≤ 2 exp (-k (ε²/4 - ε³/6))` for `ε ≥ 0`, from the two tails as for
`χ²_k` (`NLAlib.measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector`). At
least `2` for empty `k` and for `ε ≥ 3/2`. [Vershynin2018, Lemma 5.3.2 (2020 draft)], there with
an unspecified constant `c`; the exponent of Dasgupta and Gupta (2003). -/
theorem
measureReal_abs_div_mul_norm_conjTranspose_mulVec_sq_sub_one_ge_le_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |(Fintype.card n / Fintype.card k : ℝ) *
      ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2 - 1|} ≤
      2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
  sorry

omit [DecidableEq k] in
/-- The fourth power of the projected length of a uniform unit vector is integrable (it is at
most `specNorm V ^ 4`), for every fixed `V`. -/
theorem integrable_norm_conjTranspose_mulVec_pow_four_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (V : Matrix n k ℝ) :
    Integrable (fun ω => ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 4) μ := by
  sorry

/-- **The fourth moment of a projected uniform unit vector**:
`E ‖Vᴴ u‖⁴ = k (k + 2) / (n (n + 2))`, from invariance alone (`docs/design/Sketching-S2.md` §7
Q5): `∑ uᵢ² = 1` and a `45°` rotation give `E u₁⁴ = 3 E u₁² u₂²` and
`n (n + 2) E u₁² u₂² = 1` when `card n ≥ 2`; for `card n = 1`, `u = ±1`. No radius–direction
independence. -/
theorem integral_norm_conjTranspose_mulVec_pow_four_of_hasLaw_uniformSphereVector [Nonempty n]
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) :
    ∫ ω, ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 4 ∂μ =
      Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2)) := by
  sorry

end NLAlib
