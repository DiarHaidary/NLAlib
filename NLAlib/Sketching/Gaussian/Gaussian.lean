/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.ChiSquareMoments
public import NLAlib.Probability.Distributions.ChiSquareTails
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlib.RandomMatrix.Gaussian.Invariance
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

/-! ### Proof-local arithmetic -/

private theorem norm_inv_sqrt_smul_sq {m : Type*} [Fintype m] {N : ℝ} (hN : 0 ≤ N)
    (v : m → ℝ) : ‖WithLp.toLp 2 ((√N)⁻¹ • v)‖ ^ 2 = ‖WithLp.toLp 2 v‖ ^ 2 / N := by
  rw [WithLp.toLp_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt hN, inv_mul_eq_div]

private theorem norm_sketch_sq (A : Matrix k n ℝ) (r : ℝ) (u : n → ℝ) :
    ‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • A *ᵥ (r • u))‖ ^ 2 =
      r ^ 2 * (‖WithLp.toLp 2 (A *ᵥ u)‖ ^ 2 / Fintype.card k) := by
  rw [norm_inv_sqrt_smul_sq (Nat.cast_nonneg _), Matrix.mulVec_smul, WithLp.toLp_smul,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_div_assoc]

private theorem norm_smul_unit {r : ℝ} (hr : 0 ≤ r) {u : n → ℝ} (hu : ‖WithLp.toLp 2 u‖ = 1) :
    ‖WithLp.toLp 2 (r • u)‖ = r := by
  rw [WithLp.toLp_smul, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_nonneg hr]

private theorem exists_eq_smul_unit {x : n → ℝ} (hx : x ≠ 0) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ u : n → ℝ, ‖WithLp.toLp 2 u‖ = 1 ∧ x = r • u := by
  have hc0 : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])
  refine ⟨‖WithLp.toLp 2 x‖, hc0.le, ‖WithLp.toLp 2 x‖⁻¹ • x, ?_, ?_⟩
  · rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc0,
      inv_mul_cancel₀ hc0.ne']
  · rw [smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]

private theorem one_sub_div_sq {s b c : ℝ} (hs : 0 < s) :
    s⁻¹ ^ 2 * (s - b - c) ^ 2 = (1 - (b + c) / s) ^ 2 := by
  field_simp
  ring

private theorem one_add_div_sq {s b c : ℝ} (hs : 0 < s) :
    s⁻¹ ^ 2 * (s + b + c) ^ 2 ≤ (1 + (b + c) / s) ^ 2 := by
  apply le_of_eq
  field_simp
  ring

/-- `‖X‖²` and `‖X‖⁴` of a standard Gaussian vector are integrable. -/
private theorem integrable_chiSq {X : Ω → k → ℝ} (hX : HasLaw X (gaussianVector k) μ) :
    Integrable (fun ω => ‖WithLp.toLp 2 (X ω)‖ ^ 2) μ ∧
      Integrable (fun ω => (‖WithLp.toLp 2 (X ω)‖ ^ 2) ^ 2) μ := by
  have hk : (0 : ℝ) ≤ Fintype.card k := Nat.cast_nonneg _
  have h1 := integrable_norm_sq_rpow_of_hasLaw_gaussianVector hX (s := 1) (by linarith)
  have h2 := integrable_norm_sq_rpow_of_hasLaw_gaussianVector hX (s := 2) (by linarith)
  simp only [Real.rpow_one, Real.rpow_two] at h1 h2
  exact ⟨h1, h2⟩

/-- `E ‖X‖² = k` and `E ‖X‖⁴ = k (k + 2)` for a standard Gaussian vector. -/
private theorem integral_chiSq [Nonempty k] {X : Ω → k → ℝ}
    (hX : HasLaw X (gaussianVector k) μ) :
    ∫ ω, ‖WithLp.toLp 2 (X ω)‖ ^ 2 ∂μ = Fintype.card k ∧
      ∫ ω, (‖WithLp.toLp 2 (X ω)‖ ^ 2) ^ 2 ∂μ = Fintype.card k * (Fintype.card k + 2) := by
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have h1 := integral_norm_sq_rpow_of_hasLaw_gaussianVector hX (s := 1) (by linarith)
  have h2 := integral_norm_sq_rpow_of_hasLaw_gaussianVector hX (s := 2) (by linarith)
  simp only [Real.rpow_one, Real.rpow_two] at h1 h2
  have hΓ : Real.Gamma ((Fintype.card k : ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hΓ1 : Real.Gamma ((Fintype.card k : ℝ) / 2 + 1) =
      (Fintype.card k : ℝ) / 2 * Real.Gamma ((Fintype.card k : ℝ) / 2) :=
    Real.Gamma_add_one (by positivity)
  have hΓ2 : Real.Gamma ((Fintype.card k : ℝ) / 2 + 2) =
      ((Fintype.card k : ℝ) / 2 + 1) * Real.Gamma ((Fintype.card k : ℝ) / 2 + 1) := by
    rw [show (Fintype.card k : ℝ) / 2 + 2 = (Fintype.card k : ℝ) / 2 + 1 + 1 by ring]
    exact Real.Gamma_add_one (by positivity)
  refine ⟨?_, ?_⟩
  · rw [h1, hΓ1]
    field_simp
  · rw [h2, hΓ2, hΓ1]
    field_simp

/-- The parameter `t = √(2 log a)` of the sample-size corollaries: `e^{-t²/2} = 1/a`. -/
private theorem exists_sqrt_two_mul_log {a : ℝ} (ha : 1 ≤ a) :
    ∃ t : ℝ, 0 ≤ t ∧ √(2 * Real.log a) = t ∧ Real.exp (-t ^ 2 / 2) = a⁻¹ := by
  have hL : 0 ≤ Real.log a := Real.log_nonneg ha
  refine ⟨_, Real.sqrt_nonneg _, rfl, ?_⟩
  rw [Real.sq_sqrt (by positivity), show -(2 * Real.log a) / 2 = -Real.log a by ring,
    Real.exp_neg, Real.exp_log (by linarith)]

/-- From `c² (√d + t)² / ε² ≤ k`: the ratio `(√d + t)/√k` is at most `ε / c`, and
`t ≤ √k - √d` when `ε ≤ c`. -/
private theorem div_sqrt_le_of_mul_sq_div_le {c : ℝ} (hc : 0 < c) (hε : 0 < ε) (ht : 0 ≤ t)
    (hεc : ε ≤ c) (hk : c ^ 2 * (√(d : ℝ) + t) ^ 2 / ε ^ 2 ≤ Fintype.card k) :
    0 ≤ (√(d : ℝ) + t) / √(Fintype.card k : ℝ) ∧
      (√(d : ℝ) + t) / √(Fintype.card k : ℝ) ≤ ε / c ∧
      t ≤ √(Fintype.card k : ℝ) - √(d : ℝ) := by
  have hsk2 : √(Fintype.card k : ℝ) ^ 2 = Fintype.card k := Real.sq_sqrt (Nat.cast_nonneg _)
  have hsk0 : 0 ≤ √(Fintype.card k : ℝ) := Real.sqrt_nonneg _
  have hA : 0 ≤ √(d : ℝ) + t := by positivity
  rw [div_le_iff₀ (by positivity), ← hsk2] at hk
  have h2 : c * (√(d : ℝ) + t) ≤ ε * √(Fintype.card k : ℝ) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 (by
      rw [mul_pow, mul_pow]; linarith)
  refine ⟨by positivity, ?_, ?_⟩
  · rcases hsk0.eq_or_lt with h0 | h0
    · rw [← h0, div_zero]; positivity
    · rw [div_le_div_iff₀ h0 hc]; linarith
  · have : ε * √(Fintype.card k : ℝ) ≤ c * √(Fintype.card k : ℝ) :=
      mul_le_mul_of_nonneg_right hεc hsk0
    nlinarith

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
  rw [gaussianEmbeddingDim_def]
  positivity

/-- The Gaussian embedding dimension is monotone in the dimension `d` and antitone in the
distortion `ε > 0` and the failure probability `δ > 0`. -/
theorem gaussianEmbeddingDim_mono (hd : d ≤ d') (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ)
    (hδδ' : δ ≤ δ') : gaussianEmbeddingDim d ε' δ' ≤ gaussianEmbeddingDim d' ε δ := by
  rw [gaussianEmbeddingDim_def, gaussianEmbeddingDim_def]
  have hd' : (d : ℝ) ≤ d' := by exact_mod_cast hd
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  gcongr

/-- The explicit comparison `gaussianEmbeddingDim d ε δ ≤ 18 (d + 2 log (2/δ)) / ε²` for
`0 < δ ≤ 2`, the constant of the prototype's
`one_sub_le_measure_isSubspaceEmbedding_gaussianMatrix`. -/
theorem gaussianEmbeddingDim_le (d : ℕ) (ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    gaussianEmbeddingDim d ε δ ≤ 18 * (d + 2 * Real.log (2 / δ)) / ε ^ 2 := by
  rw [gaussianEmbeddingDim_def]
  have hL : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have h1 := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have h2 := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.log (2 / δ))
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
  nlinarith [sq_nonneg (√(d : ℝ) - √(2 * Real.log (2 / δ)))]

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
  rw [gaussianInjectionDim_def]
  have hL : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have h1 : 0 < √(2 * Real.log (1 / δ)) := Real.sqrt_pos.2 (by linarith)
  have h2 : 0 < √(d : ℝ) + √(2 * Real.log (1 / δ)) := by positivity
  positivity

/-- The Gaussian injection dimension is monotone in the dimension `d` and antitone in the
distortion `ε > 0` and the failure probability `δ > 0`. -/
theorem gaussianInjectionDim_mono (hd : d ≤ d') (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ)
    (hδδ' : δ ≤ δ') : gaussianInjectionDim d ε' δ' ≤ gaussianInjectionDim d' ε δ := by
  rw [gaussianInjectionDim_def, gaussianInjectionDim_def]
  have hd' : (d : ℝ) ≤ d' := by exact_mod_cast hd
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  gcongr

/-- The explicit comparison `gaussianInjectionDim d ε δ ≤ 8 (d + 2 log (1/δ)) / ε²` for
`0 < δ ≤ 1`. -/
theorem gaussianInjectionDim_le (d : ℕ) (ε : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    gaussianInjectionDim d ε δ ≤ 8 * (d + 2 * Real.log (1 / δ)) / ε ^ 2 := by
  rw [gaussianInjectionDim_def]
  have hL : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have h1 := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have h2 := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.log (1 / δ))
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
  nlinarith [sq_nonneg (√(d : ℝ) - √(2 * Real.log (1 / δ)))]

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
  rw [jlDim_def]
  refine div_pos (Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)) ?_
  have : 0 < ε ^ 2 := by positivity
  nlinarith

/-- The Johnson–Lindenstrauss dimension is antitone in the distortion on `(0, 1]` and in the
failure probability, for `0 < δ ≤ 2`. -/
theorem jlDim_mono (hε : 0 < ε) (hεε' : ε ≤ ε') (hε'1 : ε' ≤ 1) (hδ : 0 < δ) (hδδ' : δ ≤ δ')
    (hδ2 : δ ≤ 2) : jlDim ε' δ' ≤ jlDim ε δ := by
  rw [jlDim_def, jlDim_def]
  have hε' : 0 < ε' := hε.trans_le hεε'
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  have hL : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hLL : Real.log (2 / δ') ≤ Real.log (2 / δ) := by gcongr
  have hf : 0 < ε ^ 2 / 4 - ε ^ 3 / 6 := by
    have : 0 < ε ^ 2 := by positivity
    nlinarith
  have hff : ε ^ 2 / 4 - ε ^ 3 / 6 ≤ ε' ^ 2 / 4 - ε' ^ 3 / 6 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hεε') (sub_nonneg.2 hε'1), mul_pos hε hε',
      mul_nonneg (sub_nonneg.2 hεε') (mul_nonneg (sub_nonneg.2 hε'1) hε.le),
      mul_nonneg (sub_nonneg.2 hεε') (mul_nonneg (sub_nonneg.2 hε'1) hε'.le),
      mul_nonneg (sub_nonneg.2 hεε') (mul_nonneg (sub_nonneg.2 (hεε'.trans hε'1)) hε.le)]
  exact (div_le_div_of_nonneg_right hLL (hf.le.trans hff)).trans
    (div_le_div_of_nonneg_left hL hf hff)

/-- The explicit comparison `jlDim ε δ ≤ 12 log (2/δ) / ε²` for `ε ≤ 1` and `0 < δ ≤ 2`
(`ε²/4 - ε³/6 ≥ ε²/12`). -/
theorem jlDim_le (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    jlDim ε δ ≤ 12 * Real.log (2 / δ) / ε ^ 2 := by
  rw [jlDim_def]
  have hL : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  rcases eq_or_ne ε 0 with rfl | hε0
  · simp
  have he2 : 0 < ε ^ 2 := by positivity
  have hf : ε ^ 2 / 12 ≤ ε ^ 2 / 4 - ε ^ 3 / 6 := by
    nlinarith [mul_nonneg he2.le (sub_nonneg.2 hε1)]
  calc Real.log (2 / δ) / (ε ^ 2 / 4 - ε ^ 3 / 6) ≤ Real.log (2 / δ) / (ε ^ 2 / 12) :=
        div_le_div_of_nonneg_left hL (by positivity) hf
    _ = 12 * Real.log (2 / δ) / ε ^ 2 := by field_simp

/-! ### Isotropy -/

/-- **A Gaussian sketch is isotropic**: `E [Sᴴ S] = 1` for `S = (√k)⁻¹ • G`, `k` nonempty. Its
rows are isotropic (`NLAlib.hasLaw_col_of_hasLaw_gaussianMatrix` on `Gᴴ`) and
`NLAlib.isIsotropicSketch_smul_of_isIsotropic` scales them. -/
theorem isIsotropicSketch_of_hasLaw_gaussianMatrix [DecidableEq n] [Nonempty k]
    (hG : HasLaw G (gaussianMatrix k n) μ) :
    IsIsotropicSketch (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) μ := by
  exact isIsotropicSketch_smul_of_isIsotropic fun i =>
    isIsotropic_of_hasLaw_gaussianVector (hG.eval i)

/-! ### A fixed subspace -/

variable [DecidableEq p]

/-- The upper half for a fixed `U` with orthonormal columns, in Loewner form. -/
private theorem measureReal_not_upper_le (hU : HasOrthonormalCols U)
    (hG : HasLaw G (gaussianMatrix k n) μ) (ht : 0 ≤ t) :
    μ.real {ω | ¬ IsSubspaceEmbedding ((√(Fintype.card k : ℝ))⁻¹ • G ω) U 0
      ((1 + (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2)} ≤
      Real.exp (-t ^ 2 / 2) := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have h := measureReal_not_conjTranspose_mul_self_le_smul_one_le_of_hasLaw_gaussianMatrix
    (hasLaw_mul_const_of_hasLaw_gaussianMatrix hG hU) ht
  refine (measureReal_mono (fun ω hω => ?_)).trans h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hup
  apply hω
  have hE : IsSubspaceEmbedding (G ω) U 0
      ((√(Fintype.card k : ℝ) + √(Fintype.card p : ℝ) + t) ^ 2) :=
    ⟨isSubspaceInjection_of_nonpos _ _ le_rfl, by rwa [hU.conjTranspose_mul_self]⟩
  have h' := hE.smul_real (√(Fintype.card k : ℝ))⁻¹
  rw [mul_zero] at h'
  refine h'.mono le_rfl ?_
  rcases (Real.sqrt_nonneg (Fintype.card k : ℝ)).eq_or_lt with h0 | h0
  · rw [← h0, inv_zero, zero_pow two_ne_zero, zero_mul]
    positivity
  · exact one_add_div_sq h0

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
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have h := measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix
    (hasLaw_mul_const_of_hasLaw_gaussianMatrix hG hU) ht htk
  unfold HasSubspaceInjection
  rcases Nat.eq_zero_or_pos (Fintype.card k) with hk | hk
  · have hp : √(Fintype.card p : ℝ) = 0 := by
      rw [hk, Nat.cast_zero, Real.sqrt_zero] at htk
      linarith [Real.sqrt_nonneg (Fintype.card p : ℝ)]
    have : IsEmpty p := by
      rw [← Fintype.card_eq_zero_iff]
      exact_mod_cast (Real.sqrt_eq_zero (Nat.cast_nonneg _)).1 hp
    have he (ω : Ω) : IsSubspaceInjection ((√(Fintype.card k : ℝ))⁻¹ • G ω) U
        ((1 - (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2) :=
      le_of_eq (Subsingleton.elim _ _)
    simp only [he, not_true_eq_false, Set.ofPred_false, measureReal_empty]
    positivity
  have hs : 0 < √(Fintype.card k : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hk)
  refine (measureReal_mono (fun ω hω => ?_)).trans h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hlow
  apply hω
  have h' := ((hU.isSubspaceInjection_iff (S := G ω)).2 hlow).smul_real (√(Fintype.card k : ℝ))⁻¹
  rwa [one_sub_div_sq hs] at h'

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
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have h1 := hU.hasSubspaceInjection_of_hasLaw_gaussianMatrix hG ht htk
  have h2 := measureReal_not_upper_le hU hG ht
  rw [two_mul]
  refine h1.hasSubspaceEmbedding ((measureReal_mono (fun ω hω => ?_)).trans h2)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact fun h' => hω h'.upper

/-- **The upper half alone**: for `U` with orthonormal columns,
`(S U)ᴴ (S U) ≤ (1 + (√p + t)/√k)² • 1` outside probability `e^{-t²/2}`, for every `t ≥ 0`; no
condition relating `t`, `k` and `p`, and one tail. The lower constant `0` is vacuous. -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_zero_of_hasLaw_gaussianMatrix
    (hU : HasOrthonormalCols U) (hG : HasLaw G (gaussianMatrix k n) μ) (ht : 0 ≤ t) :
    HasSubspaceEmbedding (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) U 0
      ((1 + (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2)
      (Real.exp (-t ^ 2 / 2)) μ := by
  exact measureReal_not_upper_le hU hG ht

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
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hs : 0 < √(Fintype.card k : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have hm : √((min d (Fintype.card n) : ℕ) : ℝ) ≤ √(d : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast min_le_left _ _)
  have h := IsObliviousSubspaceInjection.of_hasOrthonormalCols (p := Fin (min d (Fintype.card n)))
    (isIsotropicSketch_of_hasLaw_gaussianMatrix hG) (by simp only [Fintype.card_fin]; omega)
    fun U hU => hU.hasSubspaceInjection_of_hasLaw_gaussianMatrix hG ht
      (by simp only [Fintype.card_fin]; linarith)
  refine ⟨h.isotropic, fun U hU => ?_⟩
  have hU' : U.rank ≤ Fintype.card (Fin (min d (Fintype.card n))) := by
    rw [Fintype.card_fin]
    exact le_min hU U.rank_le_card_width
  refine (h.injection U hU').mono ?_ le_rfl
  rw [Fintype.card_fin]
  have h0 : 0 ≤ 1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ) := by
    rw [sub_nonneg, div_le_one hs]
    linarith
  have h1 : (√((min d (Fintype.card n) : ℕ) : ℝ) + t) / √(Fintype.card k : ℝ) ≤
      (√(d : ℝ) + t) / √(Fintype.card k : ℝ) := by gcongr
  exact pow_le_pow_left₀ h0 (by linarith) 2

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
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hm : √((min d (Fintype.card n) : ℕ) : ℝ) ≤ √(d : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast min_le_left _ _)
  have h := IsObliviousSubspaceEmbedding.of_hasOrthonormalCols (p := Fin (min d (Fintype.card n)))
    (by simp only [Fintype.card_fin]; omega)
    fun U hU => hU.hasSubspaceEmbedding_of_hasLaw_gaussianMatrix hG ht
      (by simp only [Fintype.card_fin]; linarith)
  intro U hU
  have hU' : U.rank ≤ Fintype.card (Fin (min d (Fintype.card n))) := by
    rw [Fintype.card_fin]
    exact le_min hU U.rank_le_card_width
  refine (h U hU').mono ?_ ?_ le_rfl
  · rw [Fintype.card_fin]
    rcases (Real.sqrt_nonneg (Fintype.card k : ℝ)).eq_or_lt with h0 | hs
    · rw [← h0, div_zero, div_zero]
    have h0 : 0 ≤ 1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ) := by
      rw [sub_nonneg, div_le_one hs]
      linarith
    have h1 : (√((min d (Fintype.card n) : ℕ) : ℝ) + t) / √(Fintype.card k : ℝ) ≤
        (√(d : ℝ) + t) / √(Fintype.card k : ℝ) := by gcongr
    exact pow_le_pow_left₀ h0 (by linarith) 2
  · rw [Fintype.card_fin]
    gcongr

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
  intro x hx
  have h := measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector
    (hasLaw_mulVec_of_hasLaw_gaussianMatrix hG hx) hε
  simp only [Matrix.smul_mulVec, norm_inv_sqrt_smul_sq (Nat.cast_nonneg _)]
  exact h

/-- The squared distortion `(‖S x‖² - ‖x‖²)²` of a Gaussian sketch is integrable. -/
theorem integrable_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_gaussianMatrix
    (hG : HasLaw G (gaussianMatrix k n) μ) (x : n → ℝ) :
    Integrable (fun ω => (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • G ω *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2) μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Matrix.mulVec_zero, smul_zero, WithLp.toLp_zero, norm_zero]
    exact integrable_const _
  obtain ⟨r, hr, u, hu, rfl⟩ := exists_eq_smul_unit hx
  obtain ⟨h1, h2⟩ := integrable_chiSq (hasLaw_mulVec_of_hasLaw_gaussianMatrix hG hu)
  simp only [norm_sketch_sq, norm_smul_unit hr hu]
  have e : ∀ y : ℝ, (r ^ 2 * (y / Fintype.card k) - r ^ 2) ^ 2 =
      r ^ 4 / Fintype.card k ^ 2 * y ^ 2 - 2 * r ^ 4 / Fintype.card k * y + r ^ 4 := by
    intro y
    ring
  simp only [e]
  exact ((h2.const_mul _).sub (h1.const_mul _)).add (integrable_const _)

/-- **The JL variance of a Gaussian sketch**: `E (‖S x‖² - ‖x‖²)² = 2 ‖x‖⁴ / k` exactly, from
`Var χ²_k = 2k` (`NLAlib.integral_norm_sq_rpow_of_hasLaw_gaussianVector` at `s = 1, 2`). -/
theorem integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_gaussianMatrix [Nonempty k]
    (hG : HasLaw G (gaussianMatrix k n) μ) (x : n → ℝ) :
    ∫ ω, (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • G ω *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 ∂μ = 2 / Fintype.card k * ‖WithLp.toLp 2 x‖ ^ 4 := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Matrix.mulVec_zero, smul_zero, WithLp.toLp_zero, norm_zero]
    simp
  obtain ⟨r, hr, u, hu, rfl⟩ := exists_eq_smul_unit hx
  have hGu := hasLaw_mulVec_of_hasLaw_gaussianMatrix hG hu
  obtain ⟨h1, h2⟩ := integrable_chiSq hGu
  obtain ⟨e1, e2⟩ := integral_chiSq hGu
  simp only [norm_sketch_sq, norm_smul_unit hr hu]
  have e : ∀ y : ℝ, (r ^ 2 * (y / Fintype.card k) - r ^ 2) ^ 2 =
      r ^ 4 / Fintype.card k ^ 2 * y ^ 2 - 2 * r ^ 4 / Fintype.card k * y + r ^ 4 := by
    intro y
    ring
  simp only [e]
  have hA : Integrable (fun ω => r ^ 4 / Fintype.card k ^ 2 *
      (‖WithLp.toLp 2 (G ω *ᵥ u)‖ ^ 2) ^ 2) μ := h2.const_mul _
  have hB : Integrable (fun ω => 2 * r ^ 4 / Fintype.card k *
      ‖WithLp.toLp 2 (G ω *ᵥ u)‖ ^ 2) μ := h1.const_mul _
  have hAB : Integrable (fun ω => r ^ 4 / Fintype.card k ^ 2 *
      (‖WithLp.toLp 2 (G ω *ᵥ u)‖ ^ 2) ^ 2 - 2 * r ^ 4 / Fintype.card k *
      ‖WithLp.toLp 2 (G ω *ᵥ u)‖ ^ 2) μ := hA.sub hB
  rw [integral_add hAB (integrable_const _), integral_sub hA hB, integral_const_mul,
    integral_const_mul, e1, e2, integral_const, probReal_univ, one_smul]
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  field_simp
  ring

/-- **The JL moment property of a Gaussian sketch** at `p = 2`, with `δ = 2 / (k ε²)`, from the
exact variance. [Woodruff2014, Definition 12], the property there; the input of approximate
matrix multiplication at `p = 2`. -/
theorem hasJLMoment_of_hasLaw_gaussianMatrix [Nonempty k] (hG : HasLaw G (gaussianMatrix k n) μ)
    (hε : 0 < ε) :
    HasJLMoment (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε
      (2 / (Fintype.card k * ε ^ 2)) 2 μ := by
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have e (x : n → ℝ) (hx : ‖WithLp.toLp 2 x‖ = 1) :
      (fun ω => |‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • G ω *ᵥ x)‖ ^ 2 - 1| ^ (2 : ℝ)) =
      fun ω => (‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • G ω *ᵥ x)‖ ^ 2 -
        ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 := by
    funext ω
    rw [hx, one_pow, Real.rpow_two, sq_abs]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · simp only [Matrix.smul_mulVec]
    rw [e x hx]
    exact integrable_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_gaussianMatrix hG x
  · simp only [Matrix.smul_mulVec]
    rw [e x hx, integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_gaussianMatrix hG x, hx,
      Real.rpow_two]
    apply le_of_eq
    field_simp

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
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  rcases le_or_gt 2 δ with hδ2 | hδ2
  · exact fun U _ => measureReal_le_one.trans (by linarith)
  have hL : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  obtain ⟨t, ht0, hteq, htδ⟩ := exists_sqrt_two_mul_log
    (by rw [le_div_iff₀ hδ]; linarith : 1 ≤ 2 / δ)
  rw [gaussianEmbeddingDim_def, hteq] at hk
  have hδeq : 2 * Real.exp (-t ^ 2 / 2) = δ := by rw [htδ]; field_simp
  obtain ⟨hx0, hx, htd⟩ := div_sqrt_le_of_mul_sq_div_le (c := 3) (by norm_num) hε ht0
    (by linarith) (by rw [show (3 : ℝ) ^ 2 = 9 by norm_num]; exact hk)
  refine (isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix hG d ht0 htd).mono le_rfl ?_ ?_
    hδeq.le
  · nlinarith
  · nlinarith

/-- **Gaussian OSI, sample-size form**: `k ≥ gaussianInjectionDim d ε δ` rows give an oblivious
subspace injection for dimension `d` with constant `1 - ε` and failure probability `δ`, for
`0 < ε ≤ 2` and `0 < δ < 1`; `k` is nonempty because the dimension is positive. -/
theorem isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le
    [DecidableEq n] (hG : HasLaw G (gaussianMatrix k n) μ) (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hk : gaussianInjectionDim d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceInjection (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) d (1 - ε) δ μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hk0 : 0 < Fintype.card k := by
    exact_mod_cast (gaussianInjectionDim_pos d hε.ne' hδ hδ1).trans_le hk
  have : Nonempty k := Fintype.card_pos_iff.1 hk0
  have hL : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  obtain ⟨t, ht0, hteq, htδ⟩ := exists_sqrt_two_mul_log
    (by rw [le_div_iff₀ hδ]; linarith : 1 ≤ 1 / δ)
  rw [gaussianInjectionDim_def, hteq] at hk
  have hδeq : Real.exp (-t ^ 2 / 2) = δ := by rw [htδ]; field_simp
  obtain ⟨hx0, hx, htd⟩ := div_sqrt_le_of_mul_sq_div_le (c := 2) (by norm_num) hε ht0
    hε2 (by rw [show (2 : ℝ) ^ 2 = 4 by norm_num]; exact hk)
  refine (isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix hG d ht0 htd).mono le_rfl ?_
    hδeq.le
  nlinarith

/-- **Gaussian distributional JL, sample-size form**: `k ≥ jlDim ε δ` rows give the JL property
with distortion `ε` and failure probability `δ`, for `0 < ε < 3/2` and `δ > 0`. Replaces the
prototype's `jl_lemma_prob_le_of_log_le`. -/
theorem hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le (hG : HasLaw G (gaussianMatrix k n) μ)
    (hε : 0 < ε) (hε1 : ε < 3 / 2) (hδ : 0 < δ) (hk : jlDim ε δ ≤ Fintype.card k) :
    HasJLProperty (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) ε δ μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  rcases le_or_gt 2 δ with hδ2 | hδ2
  · exact fun x _ => measureReal_le_one.trans (by linarith)
  have hf : 0 < ε ^ 2 / 4 - ε ^ 3 / 6 := by
    have : 0 < ε ^ 2 := by positivity
    nlinarith
  rw [jlDim_def, div_le_iff₀ hf] at hk
  refine (hasJLProperty_of_hasLaw_gaussianMatrix hG hε.le).mono le_rfl ?_
  calc 2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6))) ≤
        2 * Real.exp (-Real.log (2 / δ)) := by gcongr
    _ = δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp

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
  have hδ : (0 : ℝ) < 1 / (((Fintype.card ι).choose 2 : ℕ) + 1 : ℝ) := by positivity
  have hJL := hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le
    (HasLaw.id (μ := gaussianMatrix k n)) hε hε1 hδ hk
  have hm := hJL.measure_exists_abs_norm_mulVec_sq_sub_ge_le hδ.le x
  by_contra hcon
  push Not at hcon
  have huniv : {ω : Matrix k n ℝ | ∃ i j, x i ≠ x j ∧ ε * ‖WithLp.toLp 2 (x i - x j)‖ ^ 2 ≤
      |‖WithLp.toLp 2 (((√(Fintype.card k : ℝ))⁻¹ • id ω) *ᵥ (x i - x j))‖ ^ 2 -
        ‖WithLp.toLp 2 (x i - x j)‖ ^ 2|} = Set.univ := by
    refine Set.eq_univ_of_forall fun ω => ?_
    obtain ⟨i, j, hij⟩ := hcon ((√(Fintype.card k : ℝ))⁻¹ • ω)
    refine ⟨i, j, fun h => ?_, hij.le⟩
    rw [h, sub_self] at hij
    simp at hij
  rw [huniv, probReal_univ, mul_one_div, le_div_iff₀ (by positivity)] at hm
  linarith

end NLAlib
