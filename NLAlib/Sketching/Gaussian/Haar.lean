/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Haar.Moments
public import NLAlib.RandomMatrix.Haar.Sphere
public import NLAlib.RandomMatrix.Haar.Transfer
public import NLAlib.Sketching.Gaussian.Gaussian

/-!
# Haar sketches

The Haar sketch is `S = √(n/k) • Qᴴ` for an `n × k` Haar frame `Q`, `card k ≤ card n`: `k`
orthonormal rows, scaled. It is written out in each statement,
`fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ`, with the hypothesis
`HasLaw Q (haarFrame n k) μ`; there is no named sketch law (`docs/design/Sketching-S2.md` §7 Q1).

It is exactly isotropic, like a Gaussian sketch, and unlike it has a deterministic norm
`specNorm S = √(n/k)`. Its upper half is deterministic: `(S U)ᴴ (S U) ≤ (n/k) • Uᴴ U` almost
surely, and at `k = n` the sketch is orthogonal, an exact embedding. Its Gram matrix on `U` has the
law of `(n/k) Uᴴ P_G U` for the range projector `P_G` of an `n × k` Gaussian (the transfer of
`NLAlib/RandomMatrix/Haar/Transfer.lean`); the inverse-Gram identity
`Uᴴ P_G U = (Gᴴ U)ᴴ (Gᴴ G)⁻¹ (Gᴴ U)` and Gordon's tails then give the lower constant
`a_H = (1 - (√p + t)/√k)² / (1 + (√k + s)/√n)²`, with a tail in `t` for the subspace and one in
`s` for the frame, and the upper constant `b_H = (1 + (√p + t)/√k)² / (1 - (√k + s)/√n)²` for
`s < √n - √k`. Both are lossy near `k = n`; there the complement route is sharp: with `c` the
codimension (`card k + c = card n`), `Q ~ P V₁` and `Q⊥ := P V₂` for a square Haar frame `P`,
`Uᴴ Q Qᴴ U = 1 - Uᴴ Q⊥ Q⊥ᴴ U`, and the inverse-Gram step on the `n × c` Gaussian behind `Q⊥` gives
`a = (n/k)(1 - (√c + √p + t)² / (√n - √c - s)²)`, which tends to `1` as `c / n → 0`.

The JL tails are the projection tails of a uniform unit vector
(`NLAlib/RandomMatrix/Haar/Sphere.lean`), with the Gaussian's constants; the JL variance is
`2 (n - k) / (k (n + 2))`, below the Gaussian's `2 / k` and `0` at `k = n`.

Degenerate cases: for empty `k`, `√(n/0) = 0` and `S = 0`, hence `[Nonempty k]` on isotropy, the
OSI and the moments. Design: `docs/design/Sketching-S2.md` §3.4, §8.

## Main results

* `NLAlib.isIsotropicSketch_of_hasLaw_haarFrame`, `NLAlib.ae_specNorm_eq_of_hasLaw_haarFrame`.
* `NLAlib.hasLaw_conjTranspose_mul_self_mul_of_hasLaw_haarFrame`: the Gaussian transfer.
* `NLAlib.ae_conjTranspose_mul_self_mul_le_smul_of_hasLaw_haarFrame`: the upper half.
* `NLAlib.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_eq`: exact at `k = n`.
* `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame`,
  `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt`,
  `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_add_eq`: three
  incomparable fixed-subspace embeddings.
* `NLAlib.isObliviousSubspaceInjection_of_hasLaw_haarFrame`,
  `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame`.
* `NLAlib.hasJLProperty_of_hasLaw_haarFrame`, `NLAlib.hasJLMoment_of_hasLaw_haarFrame`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k n p : Type*} [Fintype k]
  [Fintype n] [Fintype p] [DecidableEq k] {Q : Ω → Matrix n k ℝ} {U : Matrix n p ℝ}
  {t s ε δ : ℝ}

/-! ### Isotropy, norm and the Gaussian transfer -/

/-- **A Haar sketch is isotropic**: `E [Sᴴ S] = (n/k) E [Q Qᴴ] = 1`
(`NLAlib.integral_mul_conjTranspose_of_hasLaw_haarFrame`), exactly, as for a Gaussian sketch.
[MartinssonTropp2020, §8.9]. -/
theorem isIsotropicSketch_of_hasLaw_haarFrame [DecidableEq n] [Nonempty k]
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) :
    IsIsotropicSketch (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) μ := by
  sorry

/-- **The norm of a Haar sketch is deterministic**: `specNorm S = √(n/k)` almost surely, since
`Q` has orthonormal columns (`NLAlib.HasOrthonormalCols.specNorm_eq_one`); for empty `k` both
sides are `0`. [MartinssonTropp2020, §8.9]. -/
theorem ae_specNorm_eq_of_hasLaw_haarFrame (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) :
    ∀ᵐ ω ∂μ, specNorm (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) =
      √(Fintype.card n / Fintype.card k : ℝ) := by
  sorry

omit [Fintype p] in
/-- **Gaussian transfer of the Haar Gram matrix**: `(S U)ᴴ (S U)` has the law of
`(n/k) Uᴴ P_G U`, `P_G` the range projector of an `n × k` standard Gaussian, for every `U`; `Q Qᴴ`
is the range projector of `Q` almost surely (`NLAlib.HasOrthonormalCols.rangeProjector_eq`), and
`NLAlib.hasLaw_rangeProjector_mul_of_hasLaw_haarFrame` at `A = 1` transfers it. -/
theorem hasLaw_conjTranspose_mul_self_mul_of_hasLaw_haarFrame (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (U : Matrix n p ℝ) :
    HasLaw (fun ω => (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U)ᴴ *
        (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U))
      ((gaussianMatrix n k).map fun G =>
        (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * rangeProjector G * U)) μ := by
  sorry

/-! ### Deterministic halves -/

omit [Fintype p] in
/-- **The upper half of a Haar sketch is deterministic**: `(S U)ᴴ (S U) ≤ (n/k) • (Uᴴ U)` almost
surely, for every `U`, every shape, with no parameter: `Q Qᴴ ≤ 1` because `specNorm Q ≤ 1`
(`NLAlib.ae_specNorm_le_one_of_hasLaw_haarFrame`,
`NLAlib.specNorm_sq_le_iff_conjTranspose_mul_self_le`). -/
theorem ae_conjTranspose_mul_self_mul_le_smul_of_hasLaw_haarFrame
    (hQ : HasLaw Q (haarFrame n k) μ) (U : Matrix n p ℝ) :
    ∀ᵐ ω ∂μ, (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U)ᴴ *
        (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U) ≤
      (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * U) := by
  sorry

omit [Fintype p] in
/-- **A square Haar sketch is an exact embedding**: for `card k = card n`, `S = Qᴴ` is orthogonal
almost surely, so it is a subspace embedding for every `range U` with constants `1`, `1` and
failure probability `0`. -/
theorem hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_eq (hQ : HasLaw Q (haarFrame n k) μ)
    (hkn : Fintype.card k = Fintype.card n) (U : Matrix n p ℝ) :
    HasSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U 1 1 0 μ := by
  sorry

/-! ### A fixed subspace -/

variable [DecidableEq p]

/-- **Haar subspace injection**: for `U` with orthonormal columns, the Haar sketch is a subspace
injection for `range U` with constant `a_H = (1 - (√p + t)/√k)² / (1 + (√k + s)/√n)²` outside
probability `e^{-t²/2} + e^{-s²/2}`, for `0 ≤ t ≤ √k - √p` and `s ≥ 0`. By the transfer and
`Uᴴ P_G U = (Gᴴ U)ᴴ (Gᴴ G)⁻¹ (Gᴴ U)` with `Gᴴ U` a `k × p` Gaussian: Gordon's lower tail for
`Gᴴ U` (`t`), the upper tail of `‖G‖` (`s`), a union bound (no independence needed). Lossy near
`k = n` (`a_H ≈ (1 - √(p/n))² / 4` there);
`NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame_of_card_add_eq` is better
when the codimension is small, this one when `k ≤ n/2` (rule 4). -/
theorem HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame (hU : HasOrthonormalCols U)
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (ht : 0 ≤ t)
    (htk : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card p : ℝ)) (hs : 0 ≤ s) :
    HasSubspaceInjection (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U
      ((1 - (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 + (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ := by
  sorry

/-- **Haar subspace embedding, deterministic upper half**: for `U` with orthonormal columns, the
lower constant `a_H` of `NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame` and
the upper constant `n/k`, outside probability `e^{-t²/2} + e^{-s²/2}`, for `0 ≤ t ≤ √k - √p`
and `s ≥ 0`; no condition on `s` and `k < n` not needed. The upper half is
`NLAlib.ae_conjTranspose_mul_self_mul_le_smul_of_hasLaw_haarFrame`. Its upper constant is exact
at `k = n` and incomparable with the `b_H` of
`NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt`, which
is better for `k` small against `n` (rule 4).
Result: haar-sketch-ose -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame (hU : HasOrthonormalCols U)
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (ht : 0 ≤ t)
    (htk : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card p : ℝ)) (hs : 0 ≤ s) :
    HasSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U
      ((1 - (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 + (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      (Fintype.card n / Fintype.card k : ℝ)
      (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ := by
  sorry

/-- **Haar subspace embedding, Gaussian upper half**: for `U` with orthonormal columns, constants
`a_H` and `b_H = (1 + (√p + t)/√k)² / (1 - (√k + s)/√n)²` outside probability
`2 e^{-t²/2} + 2 e^{-s²/2}`, for `0 ≤ t ≤ √k - √p` and `0 ≤ s < √n - √k`; four tails, two for
`Gᴴ U` and two for `G`, with `NLAlib.Matrix.PosDef.inv_le_inv_of_le` on `Gᴴ G`. Better than the
upper constant `n/k` of `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame` for
`k` small against `n`, worse near `k = n` (rule 4).
Result: haar-sketch-ose -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt
    (hU : HasOrthonormalCols U) (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (ht : 0 ≤ t)
    (htk : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card p : ℝ)) (hs : 0 ≤ s)
    (hsk : s < √(Fintype.card n : ℝ) - √(Fintype.card k : ℝ)) :
    HasSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U
      ((1 - (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 + (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      ((1 + (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 - (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      (2 * Real.exp (-t ^ 2 / 2) + 2 * Real.exp (-s ^ 2 / 2)) μ := by
  sorry

/-- **Haar subspace injection near `k = n`**: with `c` the codimension, `card k + c = card n`,
and `U` with orthonormal columns, the Haar sketch is a subspace injection for `range U` with
constant `(n/k)(1 - (√c + √p + t)² / (√n - √c - s)²)` outside probability
`e^{-t²/2} + e^{-s²/2}`, for `t ≥ 0` and `0 ≤ s < √n - √c`. The complement route:
`Q ~ P V₁` and `Q⊥ := P V₂` for a square Haar frame `P` and the selection matrices of a split of
its columns (`NLAlib.hasLaw_mul_const_of_hasLaw_haarFrame`), `Uᴴ Q Qᴴ U = 1 - Uᴴ Q⊥ Q⊥ᴴ U`, and
the inverse-Gram step on the `n × c` Gaussian behind `Q⊥`. The constant tends to `1` as
`c / n → 0` and is vacuous for `k ≤ n/2`; incomparable with the `a_H` of
`NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame` (rule 4). -/
theorem HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame_of_card_add_eq
    (hU : HasOrthonormalCols U) (hQ : HasLaw Q (haarFrame n k) μ) {c : ℕ}
    (hc : Fintype.card k + c = Fintype.card n) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hsc : s < √(Fintype.card n : ℝ) - √(c : ℝ)) :
    HasSubspaceInjection (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U
      ((Fintype.card n / Fintype.card k : ℝ) *
        (1 - (√(c : ℝ) + √(Fintype.card p : ℝ) + t) ^ 2 /
          (√(Fintype.card n : ℝ) - √(c : ℝ) - s) ^ 2))
      (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ := by
  sorry

/-- **Haar subspace embedding near `k = n`**: the lower constant of
`NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame_of_card_add_eq` and the
deterministic upper constant `n/k`, outside probability `e^{-t²/2} + e^{-s²/2}`, for `t ≥ 0`
and `0 ≤ s < √n - √c`, `c` the codimension. Both constants tend to `1` as `c / n → 0`.
Result: haar-sketch-ose -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_add_eq
    (hU : HasOrthonormalCols U) (hQ : HasLaw Q (haarFrame n k) μ) {c : ℕ}
    (hc : Fintype.card k + c = Fintype.card n) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hsc : s < √(Fintype.card n : ℝ) - √(c : ℝ)) :
    HasSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U
      ((Fintype.card n / Fintype.card k : ℝ) *
        (1 - (√(c : ℝ) + √(Fintype.card p : ℝ) + t) ^ 2 /
          (√(Fintype.card n : ℝ) - √(c : ℝ) - s) ^ 2))
      (Fintype.card n / Fintype.card k : ℝ)
      (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ := by
  sorry

/-! ### Oblivious forms -/

/-- **The Haar OSI**: the Haar sketch is an oblivious subspace injection for dimension `d` with
constant `(1 - (√d + t)/√k)² / (1 + (√k + s)/√n)²` and failure probability
`e^{-t²/2} + e^{-s²/2}`, for `0 ≤ t ≤ √k - √d` and `s ≥ 0`.
Result: haar-sketch-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_haarFrame [DecidableEq n] [Nonempty k]
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (d : ℕ)
    (ht : 0 ≤ t) (htd : t ≤ √(Fintype.card k : ℝ) - √(d : ℝ)) (hs : 0 ≤ s) :
    IsObliviousSubspaceInjection (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) d
      ((1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 + (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ := by
  sorry

/-- **The Haar OSE, deterministic upper half**: an oblivious subspace embedding for dimension
`d` with constants `(1 - (√d + t)/√k)² / (1 + (√k + s)/√n)²` and `n/k`, failure probability
`e^{-t²/2} + e^{-s²/2}`, for `0 ≤ t ≤ √k - √d` and `s ≥ 0`. Incomparable with
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt` (rule 4).
Result: haar-sketch-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_haarFrame (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (d : ℕ) (ht : 0 ≤ t)
    (htd : t ≤ √(Fintype.card k : ℝ) - √(d : ℝ)) (hs : 0 ≤ s) :
    IsObliviousSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) d
      ((1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 + (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      (Fintype.card n / Fintype.card k : ℝ)
      (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ := by
  sorry

/-- **The Haar OSE, Gaussian upper half**: an oblivious subspace embedding for dimension `d`
with constants `(1 ∓ (√d + t)/√k)² / (1 ± (√k + s)/√n)²` and failure probability
`2 e^{-t²/2} + 2 e^{-s²/2}`, for `0 ≤ t ≤ √k - √d` and `0 ≤ s < √n - √k`. Better than
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame` for `k` small against `n` (rule 4).
Result: haar-sketch-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (d : ℕ)
    (ht : 0 ≤ t) (htd : t ≤ √(Fintype.card k : ℝ) - √(d : ℝ)) (hs : 0 ≤ s)
    (hsk : s < √(Fintype.card n : ℝ) - √(Fintype.card k : ℝ)) :
    IsObliviousSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) d
      ((1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 + (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      ((1 + (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 - (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      (2 * Real.exp (-t ^ 2 / 2) + 2 * Real.exp (-s ^ 2 / 2)) μ := by
  sorry

/-! ### Johnson–Lindenstrauss -/

/-- **Distributional Johnson–Lindenstrauss for a Haar sketch**, with the Gaussian's constants:
`P(ε ≤ |‖S x‖² - 1|) ≤ 2 exp (-k (ε²/4 - ε³/6))` for every unit `x` and `ε ≥ 0`;
`‖S x‖² = (n/k) ‖Vᴴ u‖²` for `u` uniform on the sphere
(`NLAlib.hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame`) and the relative-deviation tail of
`NLAlib/RandomMatrix/Haar/Sphere.lean`. [Vershynin2018, Lemma 5.3.2 (2020 draft)], there with
an unspecified constant `c`; the exponent of Dasgupta and Gupta (2003). -/
theorem hasJLProperty_of_hasLaw_haarFrame (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (hε : 0 ≤ ε) :
    HasJLProperty (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) ε
      (2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6)))) μ := by
  sorry

/-- The squared distortion `(‖S x‖² - ‖x‖²)²` of a Haar sketch is integrable (it is bounded). -/
theorem integrable_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_haarFrame
    (hQ : HasLaw Q (haarFrame n k) μ) (x : n → ℝ) :
    Integrable (fun ω => (‖WithLp.toLp 2
      ((√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2) μ := by
  sorry

/-- **The JL variance of a Haar sketch**: `E (‖S x‖² - ‖x‖²)² = 2 (n - k) / (k (n + 2)) ‖x‖⁴`
exactly, below the Gaussian's `2 / k` and `0` at `k = n`; from `E ‖Vᴴ u‖² = k / n` and the
fourth moment `NLAlib.integral_norm_conjTranspose_mulVec_pow_four_of_hasLaw_uniformSphereVector`.
-/
theorem integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_haarFrame [Nonempty k]
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (x : n → ℝ) :
    ∫ ω, (‖WithLp.toLp 2 ((√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 ∂μ =
      2 * ((Fintype.card n : ℝ) - Fintype.card k) / (Fintype.card k * (Fintype.card n + 2)) *
        ‖WithLp.toLp 2 x‖ ^ 4 := by
  sorry

/-- **The JL moment property of a Haar sketch** at `p = 2`, with
`δ = 2 (n - k) / (k (n + 2) ε²)`, from the exact variance. [Woodruff2014, Definition 12], the
property there. -/
theorem hasJLMoment_of_hasLaw_haarFrame [Nonempty k] (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (hε : 0 < ε) :
    HasJLMoment (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) ε
      (2 * ((Fintype.card n : ℝ) - Fintype.card k) /
        (Fintype.card k * (Fintype.card n + 2) * ε ^ 2)) 2 μ := by
  sorry

/-- **Haar distributional JL, sample-size form**: `k ≥ jlDim ε δ` rows give the JL property with
distortion `ε` and failure probability `δ`, for `0 < ε < 3/2` and `δ > 0`. -/
theorem hasJLProperty_of_hasLaw_haarFrame_of_jlDim_le (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (hε : 0 < ε) (hε1 : ε < 3 / 2) (hδ : 0 < δ)
    (hk' : jlDim ε δ ≤ Fintype.card k) :
    HasJLProperty (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) ε δ μ := by
  sorry

end NLAlib
