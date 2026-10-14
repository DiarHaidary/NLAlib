/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.ChiSquareMoments
public import NLAlib.Probability.Distributions.ChiSquareTails
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlib.Sketching.Properties.JohnsonLindenstrauss
public import NLAlib.Sketching.Properties.Oblivious

/-!
# Gaussian sketches

The Gaussian sketch is `S = (√k)⁻¹ • G` for a standard Gaussian `G : Matrix k n ℝ` (`k = card k`
rows). It is written out in each statement, `fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω`, with the
hypothesis `HasLaw G (gaussianMatrix k n) μ`; there is no named sketch law
(`docs/design/Sketching-S2.md` §7 Q1).

It is an isotropic sketch, a random subspace injection and embedding for a fixed `U` with
orthonormal columns (Gordon's extreme singular values, one tail `e^{-t²/2}` per side), an
oblivious subspace injection and embedding, and has the distributional Johnson–Lindenstrauss
property with Dasgupta and Gupta's exponent `ε²/4 - ε³/6`, and the exact JL second moment
`2 / k`. The sample sizes are named quantities (CONTRIBUTING §5.2, rule 2), each with its
nonnegativity, monotonicity and an explicit comparison; the "`k ≥ …` suffices" forms are
corollaries of the tails.

Degenerate cases: for empty `k`, `(√0)⁻¹ = 0` and `S = 0`, which is not isotropic, hence
`[Nonempty k]` on isotropy, the OSI and the moments; the hypothesis `t ≤ √k - √p` then forces `p`
empty. The JL bound is `2` for `k = 0` and at least `2` for `ε ≥ 3/2`. Design:
`docs/design/Sketching-S2.md` §3.3, §8.

## Main definitions

* `NLAlib.gaussianEmbeddingDim`, `NLAlib.gaussianInjectionDim`, `NLAlib.jlDim`: sample sizes.

## Main results

* `NLAlib.isIsotropicSketch_of_hasLaw_gaussianMatrix`.
* `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_gaussianMatrix`: the fixed-subspace
  embedding, `(1 ∓ (√p + t)/√k)²` outside `2 e^{-t²/2}`.
* `NLAlib.isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix`,
  `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix`.
* `NLAlib.hasJLProperty_of_hasLaw_gaussianMatrix`: distributional JL.
* `NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix`: the JL moment property at `p = 2`.
* `NLAlib.exists_forall_abs_norm_mulVec_sq_sub_le_of_jlDim_le`: the Johnson–Lindenstrauss lemma.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k n p ι : Type*} [Fintype k]
  [Fintype n] [Fintype p] {G : Ω → Matrix k n ℝ} {U : Matrix n p ℝ} {d d' : ℕ}
  {t ε ε' δ δ' : ℝ}

/-! ### Sample sizes -/

/-- The **Gaussian embedding dimension** `9 (√d + √(2 log (2/δ)))² / ε²`: a Gaussian sketch with
at least this many rows is an oblivious subspace embedding for dimension `d` with constants
`1 ∓ ε` and failure probability `δ`, for `0 < ε ≤ 1`
(`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix_of_gaussianEmbeddingDim_le`). The
value the proof reaches (`t = √(2 log (2/δ))` and `(√d + t)/√k ≤ ε/3`); [Woodruff2014, Theorem 6]
has `Θ((d + log (1/δ))/ε²)` with no constant. Consumers use `gaussianEmbeddingDim_le`, the
prototype's `18 (d + 2 log (2/δ))/ε²`. Junk values: `0` at `ε = 0`; for `δ ≥ 2` the logarithm is
at most `0` and its square root is `0`. -/
noncomputable irreducible_def gaussianEmbeddingDim (d : ℕ) (ε δ : ℝ) : ℝ :=
  9 * (√(d : ℝ) + √(2 * Real.log (2 / δ))) ^ 2 / ε ^ 2

/-- The Gaussian embedding dimension is nonnegative. -/
theorem gaussianEmbeddingDim_nonneg (d : ℕ) (ε δ : ℝ) : 0 ≤ gaussianEmbeddingDim d ε δ := by
  sorry

/-- The Gaussian embedding dimension is monotone in the dimension `d` and antitone in the
distortion `ε > 0` and the failure probability `δ > 0`. -/
theorem gaussianEmbeddingDim_mono (hd : d ≤ d') (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ)
    (hδδ' : δ ≤ δ') : gaussianEmbeddingDim d ε' δ' ≤ gaussianEmbeddingDim d' ε δ := by
  sorry

/-- The explicit comparison `gaussianEmbeddingDim d ε δ ≤ 18 (d + 2 log (2/δ)) / ε²` for
`0 < δ ≤ 2`, the constant of the prototype's
`one_sub_le_measure_isSubspaceEmbedding_gaussianMatrix`. -/
theorem gaussianEmbeddingDim_le (d : ℕ) (ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    gaussianEmbeddingDim d ε δ ≤ 18 * (d + 2 * Real.log (2 / δ)) / ε ^ 2 := by
  sorry

/-- The **Gaussian injection dimension** `4 (√d + √(2 log (1/δ)))² / ε²`: a Gaussian sketch with
at least this many rows is an oblivious subspace injection for dimension `d` with constant
`1 - ε` and failure probability `δ`, for `0 < ε ≤ 2` and `0 < δ < 1`
(`NLAlib.isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le`). The
value the proof reaches (`t = √(2 log (1/δ))` and `(√d + t)/√k ≤ ε/2`); one tail, against the
embedding's two. Consumers use `gaussianInjectionDim_le`. Junk values: `0` at `ε = 0`; for
`δ ≥ 1` the logarithm is at most `0` and its square root is `0`. -/
noncomputable irreducible_def gaussianInjectionDim (d : ℕ) (ε δ : ℝ) : ℝ :=
  4 * (√(d : ℝ) + √(2 * Real.log (1 / δ))) ^ 2 / ε ^ 2

/-- The Gaussian injection dimension is positive for `ε ≠ 0` and `0 < δ < 1`; a sketch with at
least this many rows has a row. -/
theorem gaussianInjectionDim_pos (d : ℕ) (hε : ε ≠ 0) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < gaussianInjectionDim d ε δ := by
  sorry

/-- The Gaussian injection dimension is monotone in the dimension `d` and antitone in the
distortion `ε > 0` and the failure probability `δ > 0`. -/
theorem gaussianInjectionDim_mono (hd : d ≤ d') (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ)
    (hδδ' : δ ≤ δ') : gaussianInjectionDim d ε' δ' ≤ gaussianInjectionDim d' ε δ := by
  sorry

/-- The explicit comparison `gaussianInjectionDim d ε δ ≤ 8 (d + 2 log (1/δ)) / ε²` for
`0 < δ ≤ 1`. -/
theorem gaussianInjectionDim_le (d : ℕ) (ε : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    gaussianInjectionDim d ε δ ≤ 8 * (d + 2 * Real.log (1 / δ)) / ε ^ 2 := by
  sorry

/-- The **Johnson–Lindenstrauss dimension** `log (2/δ) / (ε²/4 - ε³/6)`: a Gaussian or Haar
sketch with at least this many rows has the distributional JL property with distortion `ε` and
failure probability `δ`, for `0 < ε < 3/2`
(`NLAlib.hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le`). The value the proof reaches, from
Dasgupta and Gupta's exponent. Consumers use `jlDim_le`, `12 log (2/δ) / ε²` for `ε ≤ 1`. Junk
values: for `ε ≥ 3/2` the denominator is at most `0`, and the value is `0` at `ε = 3/2` and of
the sign of `-log (2/δ)` beyond; for `δ ≥ 2` the logarithm is at most `0`. -/
noncomputable irreducible_def jlDim (ε δ : ℝ) : ℝ :=
  Real.log (2 / δ) / (ε ^ 2 / 4 - ε ^ 3 / 6)

/-- The Johnson–Lindenstrauss dimension is positive for `0 < ε < 3/2` and `0 < δ < 2`. -/
theorem jlDim_pos (hε : 0 < ε) (hε1 : ε < 3 / 2) (hδ : 0 < δ) (hδ2 : δ < 2) : 0 < jlDim ε δ := by
  sorry

/-- The Johnson–Lindenstrauss dimension is antitone in the distortion on `(0, 1]` and in the
failure probability, for `0 < δ ≤ 2`. -/
theorem jlDim_mono (hε : 0 < ε) (hεε' : ε ≤ ε') (hε'1 : ε' ≤ 1) (hδ : 0 < δ) (hδδ' : δ ≤ δ')
    (hδ2 : δ ≤ 2) : jlDim ε' δ' ≤ jlDim ε δ := by
  sorry

/-- The explicit comparison `jlDim ε δ ≤ 12 log (2/δ) / ε²` for `ε ≤ 1` and `0 < δ ≤ 2`
(`ε²/4 - ε³/6 ≥ ε²/12`). -/
theorem jlDim_le (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    jlDim ε δ ≤ 12 * Real.log (2 / δ) / ε ^ 2 := by
  sorry

/-! ### Isotropy -/

/-- **A Gaussian sketch is isotropic**: `E [Sᴴ S] = 1` for `S = (√k)⁻¹ • G`, `k` nonempty. Its
rows are isotropic (`NLAlib.hasLaw_col_of_hasLaw_gaussianMatrix` on `Gᴴ`) and
`NLAlib.isIsotropicSketch_smul_of_isIsotropic` scales them. -/
theorem isIsotropicSketch_of_hasLaw_gaussianMatrix [DecidableEq n] [Nonempty k]
    (hG : HasLaw G (gaussianMatrix k n) μ) :
    IsIsotropicSketch (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) μ := by
  sorry

/-! ### A fixed subspace -/

variable [DecidableEq p]

/-- **Gaussian subspace injection**: for `U` with orthonormal columns, `S = (√k)⁻¹ • G` satisfies
`(1 - (√p + t)/√k)² • 1 ≤ (S U)ᴴ (S U)` outside probability `e^{-t²/2}`, for
`0 ≤ t ≤ √k - √p`. `G U` is a `k × p` Gaussian and Gordon's lower tail
(`NLAlib.measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix`)
applies. [MartinssonTropp2020, §8.7.2], there `1 - (1 + √p)/√k - t/√k` for our `t`, with
unsquared singular values; one-sided here, so one tail. -/
theorem HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_gaussianMatrix
    (hU : HasOrthonormalCols U) (hG : HasLaw G (gaussianMatrix k n) μ) (ht : 0 ≤ t)
    (htk : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card p : ℝ)) :
    HasSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) U
      ((1 - (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2)
      (Real.exp (-t ^ 2 / 2)) μ := by
  sorry

/-- **Gaussian subspace embedding**: for `U` with orthonormal columns, `S = (√k)⁻¹ • G` is a
subspace embedding for `range U` with constants `(1 ∓ (√p + t)/√k)²` outside probability
`2 e^{-t²/2}`, for `0 ≤ t ≤ √k - √p`; Gordon's Gram sandwich for the `k × p` Gaussian `G U`.
[Woodruff2014, Theorem 6] (`k = Θ((p + log (1/δ))/ε²)`, no constant);
[MartinssonTropp2020, §8.7.2], there `1 ∓ (1 + √p)/√k ∓ t/√k` for our `t`.
Result: gaussian-ose -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_gaussianMatrix
    (hU : HasOrthonormalCols U) (hG : HasLaw G (gaussianMatrix k n) μ) (ht : 0 ≤ t)
    (htk : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card p : ℝ)) :
    HasSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) U
      ((1 - (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2)
      ((1 + (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2)
      (2 * Real.exp (-t ^ 2 / 2)) μ := by
  sorry

/-- **The upper half alone**: for `U` with orthonormal columns,
`(S U)ᴴ (S U) ≤ (1 + (√p + t)/√k)² • 1` outside probability `e^{-t²/2}`, for every `t ≥ 0`; no
condition relating `t`, `k` and `p`, and one tail. The lower constant `0` is vacuous. -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_zero_of_hasLaw_gaussianMatrix
    (hU : HasOrthonormalCols U) (hG : HasLaw G (gaussianMatrix k n) μ) (ht : 0 ≤ t) :
    HasSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) U 0
      ((1 + (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2)
      (Real.exp (-t ^ 2 / 2)) μ := by
  sorry

/-! ### Oblivious forms -/

/-- **The Gaussian OSI**: `S = (√k)⁻¹ • G` is an oblivious subspace injection for dimension `d`
with constant `(1 - (√d + t)/√k)²` and failure probability `e^{-t²/2}`, for
`0 ≤ t ≤ √k - √d`; for `d > card n` the proof works at `min d (card n)` and weakens.
[CamanoEpperlyMeyerTropp2025, Definition 1.6, §1.5.0], who cite [MartinssonTropp2020, §8.7.2]
for it; the one-sided tail gives the better failure probability.
Result: gaussian-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix [DecidableEq n] [Nonempty k]
    (hG : HasLaw G (gaussianMatrix k n) μ) (d : ℕ) (ht : 0 ≤ t)
    (htd : t ≤ √(Fintype.card k : ℝ) - √(d : ℝ)) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) d
      ((1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2) (Real.exp (-t ^ 2 / 2)) μ := by
  sorry

/-- **The Gaussian OSE**: `S = (√k)⁻¹ • G` is an oblivious subspace embedding for dimension `d`
with constants `(1 ∓ (√d + t)/√k)²` and failure probability `2 e^{-t²/2}`, for
`0 ≤ t ≤ √k - √d`. [Woodruff2014, Theorem 6]; [MartinssonTropp2020, §8.7.2].
Result: gaussian-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix
    (hG : HasLaw G (gaussianMatrix k n) μ) (d : ℕ) (ht : 0 ≤ t)
    (htd : t ≤ √(Fintype.card k : ℝ) - √(d : ℝ)) :
    IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) d
      ((1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2)
      ((1 + (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2) (2 * Real.exp (-t ^ 2 / 2)) μ := by
  sorry

/-! ### Johnson–Lindenstrauss -/

/-- **Distributional Johnson–Lindenstrauss for a Gaussian sketch**: for every unit `x`,
`P(ε ≤ |‖S x‖² - 1|) ≤ 2 exp (-k (ε²/4 - ε³/6))`, every `ε ≥ 0`; `‖S x‖² = ‖G x‖²/k` is
`χ²_k / k` (`NLAlib.measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector`).
[Woodruff2014, Lemma 18] (there `ε² k / 16`); [MartinssonTropp2020, §8.6]; the exponent of
Dasgupta and Gupta (`docs/PORT_SKETCHING.md` D12). No `ε < 1`: the bound is at least `2` for
`ε ≥ 3/2`. Replaces the prototype's `jl_distributional`.
Result: jl-distributional -/
theorem hasJLProperty_of_hasLaw_gaussianMatrix (hG : HasLaw G (gaussianMatrix k n) μ)
    (hε : 0 ≤ ε) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε
      (2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6)))) μ := by
  sorry

/-- The squared distortion `(‖S x‖² - ‖x‖²)²` of a Gaussian sketch is integrable. -/
theorem integrable_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_gaussianMatrix
    (hG : HasLaw G (gaussianMatrix k n) μ) (x : n → ℝ) :
    Integrable (fun ω => (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • G ω *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2) μ := by
  sorry

/-- **The JL variance of a Gaussian sketch**: `E (‖S x‖² - ‖x‖²)² = 2 ‖x‖⁴ / k` exactly, from
`Var χ²_k = 2k` (`NLAlib.integral_norm_sq_rpow_of_hasLaw_gaussianVector` at `s = 1, 2`). -/
theorem integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_gaussianMatrix [Nonempty k]
    (hG : HasLaw G (gaussianMatrix k n) μ) (x : n → ℝ) :
    ∫ ω, (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • G ω *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 ∂μ = 2 / Fintype.card k * ‖WithLp.toLp 2 x‖ ^ 4 := by
  sorry

/-- **The JL moment property of a Gaussian sketch** at `p = 2`, with `δ = 2 / (k ε²)`, from the
exact variance. [Woodruff2014, Definition 12], the property there; the input of approximate
matrix multiplication at `p = 2`. -/
theorem hasJLMoment_of_hasLaw_gaussianMatrix [Nonempty k] (hG : HasLaw G (gaussianMatrix k n) μ)
    (hε : 0 < ε) :
    HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε
      (2 / (Fintype.card k * ε ^ 2)) 2 μ := by
  sorry

/-! ### Sample-size corollaries -/

/-- **Gaussian OSE, sample-size form**: `k ≥ gaussianEmbeddingDim d ε δ` rows give an oblivious
subspace embedding for dimension `d` with constants `1 ∓ ε` and failure probability `δ`, for
`0 < ε ≤ 1` and `δ > 0` (for `δ ≥ 2` it is trivial). [Woodruff2014, Theorem 6]. Replaces the
prototype's `one_sub_le_measure_isSubspaceEmbedding_gaussianMatrix`
(`k ≥ 18 (d + 2 log (2/δ)) / ε²`, now `gaussianEmbeddingDim_le`). -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix_of_gaussianEmbeddingDim_le
    (hG : HasLaw G (gaussianMatrix k n) μ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : gaussianEmbeddingDim d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) d (1 - ε) (1 + ε) δ
      μ := by
  sorry

/-- **Gaussian OSI, sample-size form**: `k ≥ gaussianInjectionDim d ε δ` rows give an oblivious
subspace injection for dimension `d` with constant `1 - ε` and failure probability `δ`, for
`0 < ε ≤ 2` and `0 < δ < 1`; `k` is nonempty because the dimension is positive. -/
theorem isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le
    [DecidableEq n] (hG : HasLaw G (gaussianMatrix k n) μ) (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hk : gaussianInjectionDim d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) d (1 - ε) δ μ := by
  sorry

/-- **Gaussian distributional JL, sample-size form**: `k ≥ jlDim ε δ` rows give the JL property
with distortion `ε` and failure probability `δ`, for `0 < ε < 3/2` and `δ > 0`. Replaces the
prototype's `jl_lemma_prob_le_of_log_le`. -/
theorem hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le (hG : HasLaw G (gaussianMatrix k n) μ)
    (hε : 0 < ε) (hε1 : ε < 3 / 2) (hδ : 0 < δ) (hk : jlDim ε δ ≤ Fintype.card k) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε δ μ := by
  sorry

/-- **The Johnson–Lindenstrauss lemma**, existence form: for points `x i` in `ℝⁿ`, `N = card ι`,
and `k ≥ jlDim ε (1 / (N choose 2 + 1))`, some `S : Matrix k n ℝ` distorts every squared
distance `‖x i - x j‖²` by a factor within `1 ± ε`, for `0 < ε < 3/2`. A scaled Gaussian works
with positive probability (the union bound over pairs, failure `< 1`). [Woodruff2014, Theorem 4],
in squared-norm form; [MartinssonTropp2020, §8.6]. Replaces the prototype's `jl_lemma_exists`.
Result: jl-lemma -/
theorem exists_forall_abs_norm_mulVec_sq_sub_le_of_jlDim_le [Fintype ι] (x : ι → n → ℝ)
    (hε : 0 < ε) (hε1 : ε < 3 / 2)
    (hk : jlDim ε (1 / (((Fintype.card ι).choose 2 : ℕ) + 1 : ℝ)) ≤ Fintype.card k) :
    ∃ S : Matrix k n ℝ, ∀ i j, |‖WithLp.toLp 2 (S *ᵥ (x i - x j))‖ ^ 2 -
      ‖WithLp.toLp 2 (x i - x j)‖ ^ 2| ≤ ε * ‖WithLp.toLp 2 (x i - x j)‖ ^ 2 := by
  sorry

end NLAlib
