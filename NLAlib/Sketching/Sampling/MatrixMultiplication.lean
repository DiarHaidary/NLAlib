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

Proofs. Every expectation is transported to `card k` i.i.d. indices
(`NLAlib.samplingSketch_eq_map`), where the sampled product is a sum of i.i.d. atoms whose weighted
mean is `Aᴴ B / card k`; unbiasedness is linearity, the exact second moment is the additivity of
the Frobenius variance over independent centred summands
(`NLAlib.integral_sum_mul_sum_of_iIndepFun` under the trace), the domination bound is the identity
with `w² / p ≤ L w` and Cauchy–Schwarz, and the tails are Markov's inequality on the square.

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

/-! ### Reduction to i.i.d. indices -/

variable (k) in
/-- The rank-one atom of row `i`, `(card k · p i)⁻¹ (A i)ᴴ B i`; the zero matrix where
`p i = 0`. -/
private noncomputable def ammAtom (p : n → ℝ≥0) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) (i : n) :
    Matrix q r 𝕜 :=
  ((Fintype.card k : ℝ) * p i)⁻¹ • Matrix.vecMulVec (star (A i)) (B i)

omit [Fintype q] [Fintype r] in
/-- The sampled product as a sum of atoms. -/
private theorem conjTranspose_mul_samplingSketchMatrix_mul_mul (p : n → ℝ≥0) (ι : k → n)
    (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    Aᴴ * (samplingSketchMatrix p ι : Matrix k n 𝕜)ᴴ * samplingSketchMatrix p ι * B =
      ∑ j, ammAtom k p A B (ι j) := by
  rw [Matrix.mul_assoc (Aᴴ * _), ← Matrix.conjTranspose_mul]
  exact conjTranspose_samplingSketchMatrix_mul_mul p ι A B

omit [Fintype q] [Fintype r] [DecidableEq n] in
/-- The weighted atoms average to `Aᴴ B / card k` when every zero weight sits on a row where
`A` or `B` vanishes. -/
private theorem sum_smul_ammAtom (hsupport : ∀ i, p i = 0 → A i = 0 ∨ B i = 0) :
    ∑ i, (p i : ℝ) • ammAtom k p A B i = (Fintype.card k : ℝ)⁻¹ • (Aᴴ * B) := by
  rw [Matrix.conjTranspose_mul_eq_sum_vecMulVec, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ammAtom, smul_smul]
  by_cases hi : p i = 0
  · rcases hsupport i hi with h | h <;> ext <;> simp [h, Matrix.vecMulVec_apply]
  · have hi' : (p i : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hi
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hi', mul_one]

omit [Fintype n] [DecidableEq n] in
/-- The weighted squared Frobenius norm of an atom. -/
private theorem mul_frobNorm_ammAtom_sq (i : n) :
    (p i : ℝ) * frobNorm (ammAtom k p A B i) ^ 2 =
      ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2 / p i /
        (Fintype.card k : ℝ) ^ 2 := by
  have hstar : ‖WithLp.toLp 2 (star (A i))‖ = ‖WithLp.toLp 2 (A i)‖ := by
    simp only [EuclideanSpace.norm_eq, Pi.star_apply, norm_star]
  rw [ammAtom, frobNorm_real_smul, frobNorm_vecMulVec, hstar,
    abs_of_nonneg (by positivity)]
  by_cases hi : (p i : ℝ) = 0
  · simp [hi]
  · field_simp

/-- An expectation of a continuous function of the sketch is an expectation over i.i.d.
indices. -/
private theorem integral_comp_of_hasLaw_samplingSketch [MeasurableSpace n]
    [MeasurableSingletonClass n] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hS : HasLaw S (samplingSketch k p) μ) {F : Matrix k n 𝕜 → E} (hF : Continuous F) :
    ∫ ω, F (S ω) ∂μ =
      ∫ ι, F (samplingSketchMatrix p ι) ∂(Measure.pi fun _ : k => samplingMeasure p) := by
  have h := hS.integral_comp hF.aestronglyMeasurable
  rw [samplingSketch_eq_map, integral_map (measurable_of_finite _).aemeasurable
    hF.aestronglyMeasurable] at h
  exact h

/-- A continuous function of the sketch is integrable. -/
private theorem integrable_comp_of_hasLaw_samplingSketch {E : Type*} [NormedAddCommGroup E]
    (hS : HasLaw S (samplingSketch k p) μ) {F : Matrix k n 𝕜 → E} (hF : Continuous F) :
    Integrable (fun ω => F (S ω)) μ := by
  let _ : MeasurableSpace n := ⊤
  have hF' : AEStronglyMeasurable F (samplingSketch k p) := hF.aestronglyMeasurable
  rw [hS.integrable_comp_iff hF', samplingSketch_eq_map,
    integrable_map_measure (by rwa [samplingSketch_eq_map] at hF')
      (measurable_of_finite _).aemeasurable]
  exact .of_finite

omit [DecidableEq n] in
/-- The expectation of a function of one i.i.d. index is the weighted sum. -/
private theorem integral_comp_eval_pi_samplingMeasure [MeasurableSpace n]
    [MeasurableSingletonClass n] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (hp : ∑ i, p i = 1) (G : n → E) (j : k) :
    ∫ ι, G (ι j) ∂(Measure.pi fun _ : k => samplingMeasure p) = ∑ i, (p i : ℝ) • G i := by
  have := isProbabilityMeasure_samplingMeasure p hp
  rw [← integral_samplingMeasure]
  exact (HasLaw.id.eval j).integral_comp (StronglyMeasurable.of_discrete).aestronglyMeasurable

omit [DecidableEq n] in
/-- **The Frobenius variance of an i.i.d. sum**: for `card k` i.i.d. indices and `Z` centred
under the weights, `E ‖∑ j, Z (ι j)‖_F² = card k · ∑ i, p i ‖Z i‖_F²`. -/
private theorem integral_frobNorm_sum_sq_pi [MeasurableSpace n] [MeasurableSingletonClass n]
    (hp : ∑ i, p i = 1) (Z : n → Matrix q r 𝕜) (hZ : ∑ i, (p i : ℝ) • Z i = 0) :
    ∫ ι, frobNorm (∑ j, Z (ι j)) ^ 2 ∂(Measure.pi fun _ : k => samplingMeasure p) =
      Fintype.card k * ∑ i, (p i : ℝ) * frobNorm (Z i) ^ 2 := by
  classical
  have := isProbabilityMeasure_samplingMeasure p hp
  have hind : iIndepFun (fun j (ι : k → n) => ι j) (Measure.pi fun _ : k => samplingMeasure p) :=
    iIndepFun_pi (X := fun _ => id) fun _ => measurable_id.aemeasurable
  have hZ' : ∑ i, (p i : ℝ) • (Z i)ᴴ = 0 := by
    have h := congrArg Matrix.conjTranspose hZ
    simpa only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
      Matrix.conjTranspose_zero] using h
  have hf : Measurable fun i : n => (Z i)ᴴ := measurable_of_finite _
  have hg : Measurable Z := measurable_of_finite _
  have hmf (j : k) : MemLp (fun ι : k → n => (Z (ι j))ᴴ) 2
      (Measure.pi fun _ : k => samplingMeasure p) := .of_discrete
  have hmg (j : k) : MemLp (fun ι : k → n => Z (ι j)) 2
      (Measure.pi fun _ : k => samplingMeasure p) := .of_discrete
  have h0 (j : k) : ∫ ι, (Z (ι j))ᴴ ∂(Measure.pi fun _ : k => samplingMeasure p) = 0 := by
    rw [integral_comp_eval_pi_samplingMeasure hp (fun i => (Z i)ᴴ) j, hZ']
  have key := integral_sum_mul_sum_of_iIndepFun hind hf hg hmf hmg h0
  calc ∫ ι, frobNorm (∑ j, Z (ι j)) ^ 2 ∂(Measure.pi fun _ : k => samplingMeasure p)
      = ∫ ι, RCLike.re ((∑ j, Z (ι j))ᴴ * ∑ j, Z (ι j)).trace
          ∂(Measure.pi fun _ : k => samplingMeasure p) := by
        simp only [frobNorm_sq_eq_re_trace]
    _ = RCLike.re (∫ ι, (∑ j, Z (ι j))ᴴ * ∑ j, Z (ι j)
          ∂(Measure.pi fun _ : k => samplingMeasure p)).trace := by
        rw [integral_re .of_finite, Matrix.integral_trace .of_finite]
    _ = ∑ j : k, ∑ i, (p i : ℝ) * frobNorm (Z i) ^ 2 := by
        simp only [Matrix.conjTranspose_sum]
        rw [key, Matrix.trace_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_comp_eval_pi_samplingMeasure hp (fun i => (Z i)ᴴ * Z i) j,
          Matrix.trace_sum, map_sum]
        simp only [Matrix.trace_smul, RCLike.smul_re, frobNorm_sq_eq_re_trace]
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### The sampled product -/

/-- The sampled product `Aᴴ Sᴴ S B` of a row-sampling sketch is integrable, for any weights and
any number of samples: the sketch takes finitely many values. -/
theorem integrable_conjTranspose_mul_mul_of_hasLaw_samplingSketch [DecidableEq r]
    (hS : HasLaw S (samplingSketch k p) μ) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    Integrable (fun ω => Aᴴ * (S ω)ᴴ * S ω * B) μ :=
  integrable_comp_of_hasLaw_samplingSketch hS (F := fun M => Aᴴ * Mᴴ * M * B) (by fun_prop)

/-- **Row sampling is unbiased for matrix products**: `E [Aᴴ Sᴴ S B] = Aᴴ B` when every zero
weight sits on a row where `A` or `B` vanishes (in particular when every weight is positive).
[MartinssonTropp2020, §7.1] (the sampled estimator, positive weights). -/
theorem integral_conjTranspose_mul_mul_of_hasLaw_samplingSketch [Nonempty k] [DecidableEq r]
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hsupport : ∀ i, p i = 0 → A i = 0 ∨ B i = 0) :
    ∫ ω, Aᴴ * (S ω)ᴴ * S ω * B ∂μ = Aᴴ * B := by
  let _ : MeasurableSpace n := ⊤
  have := isProbabilityMeasure_samplingMeasure p hp
  have hK : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [integral_comp_of_hasLaw_samplingSketch hS (F := fun M => Aᴴ * Mᴴ * M * B) (by fun_prop)]
  simp only [conjTranspose_mul_samplingSketchMatrix_mul_mul]
  rw [integral_finsetSum _ fun j _ => .of_finite]
  simp only [integral_comp_eval_pi_samplingMeasure hp (ammAtom k p A B), sum_smul_ammAtom hsupport,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hK, one_smul]

/-! ### The Frobenius error -/

/-- The squared Frobenius error of the sampled product is integrable, for any weights and any
number of samples. -/
theorem integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch
    (hS : HasLaw S (samplingSketch k p) μ) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    Integrable (fun ω => frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2) μ :=
  integrable_comp_of_hasLaw_samplingSketch hS
    (F := fun M => frobNorm (Aᴴ * Mᴴ * M * B - Aᴴ * B) ^ 2)
    ((continuous_frobNorm.comp (by fun_prop)).pow 2)

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
  let _ : MeasurableSpace n := ⊤
  set K : ℝ := (Fintype.card k : ℝ) with hKdef
  have hK : K ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  set c : Matrix q r 𝕜 := K⁻¹ • (Aᴴ * B) with hc
  have hsum (ι : k → n) : Aᴴ * (samplingSketchMatrix p ι : Matrix k n 𝕜)ᴴ *
      samplingSketchMatrix p ι * B - Aᴴ * B = ∑ j, (ammAtom k p A B (ι j) - c) := by
    rw [conjTranspose_mul_samplingSketchMatrix_mul_mul, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, hc, smul_smul, ← hKdef, mul_inv_cancel₀ hK,
      one_smul]
  have hZ : ∑ i, (p i : ℝ) • (ammAtom k p A B i - c) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib, sum_smul_ammAtom hsupport, ← Finset.sum_smul,
      ← NNReal.coe_sum, hp, NNReal.coe_one, one_smul, hc]
    exact sub_self _
  rw [integral_comp_of_hasLaw_samplingSketch hS
    (F := fun M => frobNorm (Aᴴ * Mᴴ * M * B - Aᴴ * B) ^ 2)
    ((continuous_frobNorm.comp (by fun_prop)).pow 2)]
  simp only [hsum]
  rw [integral_frobNorm_sum_sq_pi hp _ hZ]
  have hvar : ∑ i, (p i : ℝ) * frobNorm (ammAtom k p A B i - c) ^ 2 =
      ∑ i, (p i : ℝ) * frobNorm (ammAtom k p A B i) ^ 2 - frobNorm c ^ 2 := by
    have hin : ∑ i, (p i : ℝ) * frobInner (ammAtom k p A B i) c = frobNorm c ^ 2 := by
      simp only [← frobInner_smul_left, ← frobInner_sum_left]
      rw [sum_smul_ammAtom hsupport, ← hc, frobInner_self]
    have hp' : ∑ i, (p i : ℝ) = 1 := by rw [← NNReal.coe_sum, hp, NNReal.coe_one]
    simp only [frobNorm_sub_sq, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hp', one_mul]
    have h2 : ∑ i, (p i : ℝ) * (2 * frobInner (ammAtom k p A B i) c) = 2 * frobNorm c ^ 2 := by
      rw [← hin, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2]
    ring
  rw [hvar]
  simp only [mul_frobNorm_ammAtom_sq, ← Finset.sum_div]
  rw [hc, frobNorm_real_smul, abs_of_nonneg (by positivity)]
  field_simp
  rw [hKdef]
  ring

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
  set w : n → ℝ := fun i => ‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖ with hw
  have hw0 (i : n) : 0 ≤ w i := by positivity
  have hp' : ∑ i, (p i : ℝ) = 1 := by rw [← NNReal.coe_sum, hp, NNReal.coe_one]
  have hL : 0 ≤ L := by
    have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hw0 i).trans (hdom i)
    rwa [Finset.sum_const_zero, ← Finset.mul_sum, hp', mul_one] at h
  have hsupport (i : n) (hi : p i = 0) : A i = 0 ∨ B i = 0 := by
    have h : w i = 0 := le_antisymm (by simpa [hi] using hdom i) (hw0 i)
    rcases mul_eq_zero.1 h with h | h
    · exact .inl (by simpa using h)
    · exact .inr (by simpa using h)
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  rw [integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch hS hp hsupport]
  refine div_le_div_of_nonneg_right ?_ hK.le
  have hterm (i : n) : ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2 / p i ≤ L * w i := by
    rw [← mul_pow]
    change w i ^ 2 / _ ≤ _
    rcases (p i).coe_nonneg.eq_or_lt with h0 | h0
    · rw [← h0, div_zero]
      exact mul_nonneg hL (hw0 i)
    · rw [div_le_iff₀ h0]
      calc w i ^ 2 = w i * w i := sq _
        _ ≤ w i * (L * p i) := mul_le_mul_of_nonneg_left (hdom i) (hw0 i)
        _ = L * w i * p i := by ring
  have hcs : ∑ i, w i ≤ frobNorm A * frobNorm B := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖WithLp.toLp 2 (A i)‖)
      (fun i => ‖WithLp.toLp 2 (B i)‖)
    have hA : frobNorm A ^ 2 = ∑ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 := frobNorm_sq_eq_sum_row A
    have hB : frobNorm B ^ 2 = ∑ i, ‖WithLp.toLp 2 (B i)‖ ^ 2 := frobNorm_sq_eq_sum_row B
    rwa [← hA, ← hB,
      Real.sqrt_sq (frobNorm_nonneg _), Real.sqrt_sq (frobNorm_nonneg _)] at h
  calc ∑ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2 / p i - frobNorm (Aᴴ * B) ^ 2
      ≤ ∑ i, L * w i := by
        have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
        nlinarith [sq_nonneg (frobNorm (Aᴴ * B))]
    _ = L * ∑ i, w i := by rw [Finset.mul_sum]
    _ ≤ L * (frobNorm A * frobNorm B) := mul_le_mul_of_nonneg_left hcs hL
    _ = L * frobNorm A * frobNorm B := by ring

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
