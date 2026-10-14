/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.SchattenPowers
public import NLAlib.Probability.Tail
public import NLAlib.Sketching.Properties.Oblivious

/-!
# Trace moments of the Gram error

For a random sketch `S` and `U` with orthonormal columns, the Gram error is
`E = (S U)ᴴ (S U) - 1`. A bound `E [re tr E^{2q}] ≤ B` on its even trace moments,
`NLAlib.HasGramTraceMoment S U q B μ`, gives `P(ε ≤ ‖E‖) ≤ B / ε^{2q}` by Markov's inequality,
since `‖E‖^{2q} ≤ re tr E^{2q}`, hence a random subspace embedding, and, for every orthonormal
`U` at once, an oblivious subspace embedding. This is the moment method of the sparse
embeddings and of the Gaussian and sign sketches at `q = 1`.

At `q = 0` the hypothesis is `card p · μ univ ≤ B` and the consequences still hold. Design:
`docs/design/Sketching-S1.md` §3.7.

## Main definitions

* `NLAlib.HasGramTraceMoment S U q B μ`.

## Main results

* `NLAlib.HasGramTraceMoment.measure_specNorm_ge_le`: the Markov step.
* `NLAlib.HasGramTraceMoment.hasSubspaceEmbedding`.
* `NLAlib.isObliviousSubspaceEmbedding_of_hasGramTraceMoment`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n p : Type*} [Fintype k] [Fintype n] [Fintype p] [DecidableEq p] {S : Ω → Matrix k n 𝕜}
  {U : Matrix n p 𝕜} {q : ℕ} {B B' ε : ℝ}

/-- **Trace-moment bound on the Gram error**: `re tr E^{2q}` is integrable and
`E [re tr E^{2q}] ≤ B` for `E = (S U)ᴴ (S U) - 1`. Used for `U` with orthonormal columns, where
`E` is the Gram error of the embedding. -/
structure HasGramTraceMoment (S : Ω → Matrix k n 𝕜) (U : Matrix n p 𝕜) (q : ℕ) (B : ℝ)
    (μ : Measure Ω) : Prop where
  /-- The trace moment is integrable. -/
  integrable : Integrable (fun ω => RCLike.re (((S ω * U)ᴴ * (S ω * U) - 1) ^ (2 * q)).trace) μ
  /-- The trace moment is at most `B`. -/
  integral_le : ∫ ω, RCLike.re (((S ω * U)ᴴ * (S ω * U) - 1) ^ (2 * q)).trace ∂μ ≤ B

/-- The trace-moment bound depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.hasGramTraceMoment_iff {ν : Measure (Matrix k n 𝕜)}
    (hS : HasLaw S ν μ) : HasGramTraceMoment S U q B μ ↔ HasGramTraceMoment id U q B ν := by
  have hc : Continuous fun A : Matrix k n 𝕜 =>
      RCLike.re (((A * U)ᴴ * (A * U) - 1) ^ (2 * q)).trace := by
    fun_prop
  have hm := hc.aestronglyMeasurable (μ := ν)
  have hint : ∫ ω, RCLike.re (((S ω * U)ᴴ * (S ω * U) - 1) ^ (2 * q)).trace ∂μ =
      ∫ A, RCLike.re (((A * U)ᴴ * (A * U) - 1) ^ (2 * q)).trace ∂ν := hS.integral_comp hm
  constructor
  · intro h
    exact ⟨(hS.integrable_comp_iff hm).1 h.integrable, hint.symm.trans_le h.integral_le⟩
  · intro h
    exact ⟨(hS.integrable_comp_iff hm).2 h.integrable, hint.trans_le h.integral_le⟩

/-- A trace-moment bound holds with any larger bound. -/
theorem HasGramTraceMoment.mono (h : HasGramTraceMoment S U q B μ) (hB : B ≤ B') :
    HasGramTraceMoment S U q B' μ := by
  exact ⟨h.integrable, h.integral_le.trans hB⟩

/-- **Trace-moment Markov step**: `P(ε ≤ ‖(S U)ᴴ (S U) - 1‖) ≤ B / ε^{2q}`, from
`‖E‖^{2q} ≤ re tr E^{2q}`. [Woodruff2014, proof of Theorem 9]. -/
theorem HasGramTraceMoment.measure_specNorm_ge_le [IsFiniteMeasure μ]
    (h : HasGramTraceMoment S U q B μ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ specNorm ((S ω * U)ᴴ * (S ω * U) - 1)} ≤ B / ε ^ (2 * q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hB := h.integral_le
    simp only [mul_zero, pow_zero, Matrix.trace_one, RCLike.natCast_re, integral_const,
      smul_eq_mul] at hB
    rw [mul_zero, pow_zero, div_one]
    rcases isEmpty_or_nonempty p with hp | hp
    · have he : {ω | ε ≤ specNorm ((S ω * U)ᴴ * (S ω * U) - 1)} = ∅ :=
        Set.eq_empty_of_forall_notMem fun ω hω => by
          have h0 : (S ω * U)ᴴ * (S ω * U) - 1 = 0 := Subsingleton.elim _ _
          simp only [Set.mem_ofPred_eq, h0, specNorm_zero] at hω
          exact absurd hω (not_le.2 hε)
      rw [he, measureReal_empty]
      simpa only [Fintype.card_eq_zero, Nat.cast_zero, mul_zero] using hB
    · have h1 : (1 : ℝ) ≤ Fintype.card p := Nat.one_le_cast.2 Fintype.card_pos
      exact (measureReal_mono (Set.subset_univ _)).trans
        ((le_mul_of_one_le_right measureReal_nonneg h1).trans hB)
  have hpow (ω : Ω) : specNorm ((S ω * U)ᴴ * (S ω * U) - 1) ^ (2 * q) ≤
      RCLike.re (((S ω * U)ᴴ * (S ω * U) - 1) ^ (2 * q)).trace := by
    have hH : ((S ω * U)ᴴ * (S ω * U) - 1).IsHermitian :=
      (Matrix.isHermitian_conjTranspose_mul_self _).sub Matrix.isHermitian_one
    have h' := specNorm_pow_le_re_trace_pow ((S ω * U)ᴴ * (S ω * U) - 1) hq.ne'
    rwa [hH.eq, ← sq, ← pow_mul] at h'
  have hεq : 0 < ε ^ (2 * q) := pow_pos hε _
  calc μ.real {ω | ε ≤ specNorm ((S ω * U)ᴴ * (S ω * U) - 1)} ≤
        μ.real {ω | ε ^ (2 * q) ≤ RCLike.re (((S ω * U)ᴴ * (S ω * U) - 1) ^ (2 * q)).trace} :=
        measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω =>
          (pow_le_pow_left₀ hε.le hω _).trans (hpow ω))
    _ ≤ (∫ ω, RCLike.re (((S ω * U)ᴴ * (S ω * U) - 1) ^ (2 * q)).trace ∂μ) / ε ^ (2 * q) :=
        measureReal_ge_le_integral_div (ae_of_all _ fun ω =>
          (pow_nonneg (specNorm_nonneg _) _).trans (hpow ω)) h.integrable hεq
    _ ≤ B / ε ^ (2 * q) := div_le_div_of_nonneg_right h.integral_le hεq.le

/-- A trace-moment bound for `U` with orthonormal columns makes `S` a random `ε`-embedding of
`range U` with failure probability `B / ε^{2q}`. -/
theorem HasGramTraceMoment.hasSubspaceEmbedding [IsFiniteMeasure μ]
    (h : HasGramTraceMoment S U q B μ) (hU : HasOrthonormalCols U) (hε : 0 < ε) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε) (B / ε ^ (2 * q)) μ := by
  exact hU.hasSubspaceEmbedding_of_measureReal_le (h.measure_specNorm_ge_le hε)

/-- **OSE from trace moments**: a trace-moment bound for every `U : Matrix n p 𝕜` with
orthonormal columns makes `S` an OSE for dimension `card p` with distortion `ε` and failure
probability `B / ε^{2q}`. [Woodruff2014, proof of Theorem 9]. -/
theorem isObliviousSubspaceEmbedding_of_hasGramTraceMoment [IsFiniteMeasure μ]
    (hp : Fintype.card p ≤ Fintype.card n)
    (h : ∀ U : Matrix n p 𝕜, HasOrthonormalCols U → HasGramTraceMoment S U q B μ) (hε : 0 < ε) :
    IsObliviousSubspaceEmbedding S (Fintype.card p) (1 - ε) (1 + ε) (B / ε ^ (2 * q)) μ := by
  exact IsObliviousSubspaceEmbedding.of_hasOrthonormalCols hp fun U hU =>
    (h U hU).hasSubspaceEmbedding hU hε

end NLAlib
