/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Basic.Selection
public import NLAlib.Probability.Distributions.Sampling
public import NLAlib.Probability.Law
public import NLAlib.Probability.MatrixConcentration.ChernoffSum
public import NLAlib.Sketching.Properties.FixedSubspace
public import NLAlib.Sketching.Properties.Isotropic
public import NLAlib.Sketching.Sampling.Leverage

/-!
# Row sampling

For weights `p : n → ℝ≥0` and indices `ι : k → n`, the row-sampling sketch
`NLAlib.samplingSketchMatrix p ι : Matrix k n 𝕜` has row `j` equal to
`(√(card k · p (ι j)))⁻¹ e_{ι j}ᴴ`; its law `NLAlib.samplingSketch k p` is the pushforward of
`card k` i.i.d. indices with law `NLAlib.samplingMeasure p`. The measurable space on the row index
`n` is fixed to `⊤` inside the definition, so no statement carries an instance on `n`;
`NLAlib.samplingSketch_eq_sum_smul_dirac` gives the law as a finite mixture of Diracs and
`NLAlib.samplingSketch_eq_map` recovers the pushforward under any measurable space on `n` with
measurable singletons.

For a fixed `U : Matrix n r 𝕜` of any shape and rank and weights dominating its leverage scores,
`∀ i, leverageScore U i ≤ L * p i`, the sketch is a random subspace injection with failure
probability `U.rank · e^{-ε² k/(2L)}` and a random subspace embedding with constants `1 ∓ ε` and
failure probability `2 U.rank · e^{-ε² k/(3L)}` for `0 ≤ ε ≤ 1` (matrix Chernoff). Exact leverage
sampling is `L = U.rank`, uniform sampling `L = coherence U`. The sample sizes are named quantities
(CONTRIBUTING §5.2, rule 2); the "`k ≥ …` suffices" forms are corollaries of the tails.

Degenerate cases. Rank zero (`U = 0`): every failure event is empty and every bound is `0`. Empty
`k`: `S = 0`, the bound `U.rank · e^0` is at least `1` when `U ≠ 0`, and the upper half holds
surely; the sketch is not isotropic, hence `[Nonempty k]` on isotropy. A zero weight `p i = 0`
gives a zero sketch row (junk `(√0)⁻¹ = 0`), and the domination hypothesis then forces row `i` of
`U` to vanish (`NLAlib.leverageScore_eq_zero_iff`). `L ≤ 0` forces rank zero, so no `0 < L` is
assumed. For `ε ≥ 1` the injection is vacuous (`NLAlib.isSubspaceInjection_of_nonpos`). The two
corollaries at the leverage-score distribution and at uniform weights take no `∑ i, p i = 1`: when
their weights fail it (`U = 0`, or `n` empty) the law is the zero measure for nonempty `k`, so
`HasLaw` forces `μ = 0`, and for empty `k` the law is `dirac 0`, a probability measure; in both
subcases `U.rank = 0` and every embedding event is full. Design: `docs/design/Sketching-S4.md`
§3.2, §8.

This file is a skeleton of Sketching stage S4: the statements are final; the proofs of isotropy
and of the two matrix Chernoff halves are deferred (`sorry`), and every other theorem is proved,
from those three where it needs them.

## Main definitions

* `NLAlib.samplingSketchMatrix`: the sketch built from given indices.
* `NLAlib.samplingSketch`: its law for i.i.d. indices.
* `NLAlib.samplingSize`, `NLAlib.samplingInjectionSize`: sample sizes.

## Main results

* `NLAlib.samplingSketch_eq_sum_smul_dirac`, `NLAlib.samplingSketch_eq_map`,
  `NLAlib.hasLaw_samplingSketchMatrix`: the law as a mixture, as a pushforward, and the bridge
  from a user's own indices.
* `NLAlib.conjTranspose_samplingSketchMatrix_mul_mul`: the sketched cross-Gram matrix as an
  average of rank-one atoms.
* `NLAlib.isIsotropicSketch_of_hasLaw_samplingSketch`: isotropy for positive weights.
* `NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketch`,
  `NLAlib.hasSubspaceEmbedding_zero_of_hasLaw_samplingSketch`: the two halves.
* `NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch`: row sampling under leverage
  domination.
* `NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch_leverageScoreDistribution`,
  `NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch_const_inv_card`: exact leverage and
  uniform sampling.
* `NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch_of_samplingSize_le`,
  `NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketch_of_samplingInjectionSize_le`: sample
  sizes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal ENNReal Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n q r : Type*} [Fintype k] [Fintype n] [Fintype q] [Fintype r] [DecidableEq n]
  {S : Ω → Matrix k n 𝕜} {U : Matrix n r 𝕜} {p : n → ℝ≥0} {L ε δ : ℝ}

/-! ### The sketch and its law -/

/-- The **row-sampling sketch** with weights `p` and indices `ι : k → n`: row `j` is
`(√(card k · p (ι j)))⁻¹ e_{ι j}ᴴ`. Junk value: a zero row where `p (ι j) = 0`. Its law for i.i.d.
indices is `NLAlib.samplingSketch`. [Woodruff2014, Definition 16] (there `D Ωᵀ`);
[MartinssonTropp2020, §9.6.3]. -/
noncomputable def samplingSketchMatrix (p : n → ℝ≥0) (ι : k → n) : Matrix k n 𝕜 :=
  Matrix.of fun j i => if ι j = i then (((√((Fintype.card k : ℝ) * p i))⁻¹ : ℝ) : 𝕜) else 0

variable (k) in
/-- The **law of the row-sampling sketch**: the pushforward by `NLAlib.samplingSketchMatrix p` of
`card k` i.i.d. indices with law `NLAlib.samplingMeasure p`. The measurable space on `n` is `⊤`
inside the definition; `NLAlib.samplingSketch_eq_map` restates it under any measurable space on
`n` with measurable singletons, and `NLAlib.samplingSketch_eq_sum_smul_dirac` as a finite mixture
of Diracs. A probability measure when `∑ i, p i = 1` or `k` is empty. [Woodruff2014,
Definition 16]; [MartinssonTropp2020, §9.6.3]. -/
noncomputable def samplingSketch (p : n → ℝ≥0) : Measure (Matrix k n 𝕜) :=
  letI : MeasurableSpace n := ⊤
  (Measure.pi fun _ : k => samplingMeasure p).map (samplingSketchMatrix p)

omit [DecidableEq n] in
/-- The product of `card k` copies of `samplingMeasure p`, as a finite mixture of Diracs. -/
private theorem pi_samplingMeasure_eq_sum [DecidableEq k] [MeasurableSpace n]
    [MeasurableSingletonClass n] (p : n → ℝ≥0) :
    Measure.pi (fun _ : k => samplingMeasure p) =
      ∑ ι : k → n, (∏ j, (p (ι j) : ℝ≥0∞)) • Measure.dirac ι := by
  refine Measure.ext_of_singleton fun ι => ?_
  rw [← Set.univ_pi_singleton, Measure.pi_pi]
  classical
  simp only [samplingMeasure_singleton, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul, Set.univ_pi_singleton,
    Measure.dirac_apply' _ (measurableSet_singleton ι), Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- The pushforward of `card k` i.i.d. indices by the sketch, as a finite mixture of Diracs,
under any measurable space on `n` with measurable singletons. -/
private theorem map_pi_samplingMeasure_eq_sum [DecidableEq k] [MeasurableSpace n]
    [MeasurableSingletonClass n] (p : n → ℝ≥0) :
    (Measure.pi fun _ : k => samplingMeasure p).map (samplingSketchMatrix (𝕜 := 𝕜) p) =
      ∑ ι : k → n, (∏ j, (p (ι j) : ℝ≥0∞)) • Measure.dirac (samplingSketchMatrix p ι) := by
  have hf : Measurable (samplingSketchMatrix (𝕜 := 𝕜) (k := k) p) := measurable_of_finite _
  ext s hs
  rw [Measure.map_apply hf hs, pi_samplingMeasure_eq_sum]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (hf hs), Measure.dirac_apply' _ hs]
  rfl

/-- The law of the row-sampling sketch as a finite mixture of Diracs, one atom per index map
`ι : k → n` with mass `∏ j, p (ι j)`. -/
theorem samplingSketch_eq_sum_smul_dirac [DecidableEq k] (p : n → ℝ≥0) :
    samplingSketch (𝕜 := 𝕜) k p =
      ∑ ι : k → n, (∏ j, (p (ι j) : ℝ≥0∞)) • Measure.dirac (samplingSketchMatrix p ι) := by
  let _ : MeasurableSpace n := ⊤
  exact map_pi_samplingMeasure_eq_sum p

/-- The law of the row-sampling sketch is a finite measure, for any weights. -/
instance isFiniteMeasure_samplingSketch (p : n → ℝ≥0) :
    IsFiniteMeasure (samplingSketch (𝕜 := 𝕜) k p) := by
  unfold samplingSketch
  infer_instance

/-- The law of the row-sampling sketch is a probability measure for weights summing to one. -/
theorem isProbabilityMeasure_samplingSketch (hp : ∑ i, p i = 1) :
    IsProbabilityMeasure (samplingSketch (𝕜 := 𝕜) k p) := by
  let _ : MeasurableSpace n := ⊤
  have : IsProbabilityMeasure (samplingMeasure p) := isProbabilityMeasure_samplingMeasure p hp
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- The law of the row-sampling sketch is the pushforward of i.i.d. indices under any measurable
space on `n` with measurable singletons. -/
theorem samplingSketch_eq_map [MeasurableSpace n] [MeasurableSingletonClass n] (p : n → ℝ≥0) :
    samplingSketch (𝕜 := 𝕜) k p =
      (Measure.pi fun _ : k => samplingMeasure p).map (samplingSketchMatrix p) := by
  classical
  rw [samplingSketch_eq_sum_smul_dirac, map_pi_samplingMeasure_eq_sum]

/-- **From the user's own indices**: if `ι` is a vector of `card k` i.i.d. indices with law
`NLAlib.samplingMeasure p`, the sketch built from it has law `NLAlib.samplingSketch k p`. -/
theorem hasLaw_samplingSketchMatrix [MeasurableSpace n] [MeasurableSingletonClass n]
    {ι : Ω → k → n} (hι : HasLaw ι (Measure.pi fun _ : k => samplingMeasure p) μ) :
    HasLaw (fun ω => (samplingSketchMatrix p (ι ω) : Matrix k n 𝕜)) (samplingSketch k p) μ := by
  rw [samplingSketch_eq_map]
  have hY : HasLaw (samplingSketchMatrix (𝕜 := 𝕜) p)
      ((Measure.pi fun _ : k => samplingMeasure p).map (samplingSketchMatrix p))
      (Measure.pi fun _ : k => samplingMeasure p) :=
    ⟨(measurable_of_finite _).aemeasurable, rfl⟩
  exact hY.comp hι

/-! ### Deterministic identities -/

omit [Fintype n] in
/-- The row-sampling sketch is a diagonal scaling of the transposed selection matrix. -/
theorem samplingSketchMatrix_eq_diagonal_mul [DecidableEq k] (p : n → ℝ≥0) (ι : k → n) :
    (samplingSketchMatrix p ι : Matrix k n 𝕜) =
      Matrix.diagonal (fun j => (((√((Fintype.card k : ℝ) * p (ι j)))⁻¹ : ℝ) : 𝕜)) *
        (selectionMatrix ι)ᴴ := by
  ext j i
  rw [Matrix.diagonal_mul, Matrix.conjTranspose_apply, selectionMatrix_apply]
  simp only [samplingSketchMatrix, Matrix.of_apply]
  by_cases h : ι j = i
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- Row `j` of a sampled matrix is the scaled row `ι j`. -/
private theorem samplingSketchMatrix_mul_apply {q' : Type*} (p : n → ℝ≥0) (ι : k → n)
    (C : Matrix n q' 𝕜) (j : k) :
    (samplingSketchMatrix p ι * C : Matrix k q' 𝕜) j =
      ((((√((Fintype.card k : ℝ) * p (ι j)))⁻¹ : ℝ) : 𝕜)) • C (ι j) := by
  ext a
  simp [Matrix.mul_apply, samplingSketchMatrix, ite_mul, Finset.sum_ite_eq]

omit [Fintype q] [Fintype r] in
/-- **The Gram-atoms identity**: the sketched cross-Gram matrix `(S A)ᴴ (S B)` is the sum over
the samples `j` of the rank-one atoms `(card k · p (ι j))⁻¹ (A (ι j))ᴴ B (ι j)`, the zero matrix
where `p (ι j) = 0`. -/
theorem conjTranspose_samplingSketchMatrix_mul_mul (p : n → ℝ≥0) (ι : k → n)
    (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    (samplingSketchMatrix p ι * A)ᴴ * (samplingSketchMatrix p ι * B) =
      ∑ j, ((Fintype.card k : ℝ) * p (ι j))⁻¹ • Matrix.vecMulVec (star (A (ι j))) (B (ι j)) := by
  ext a b
  rw [Matrix.mul_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hx : 0 ≤ (Fintype.card k : ℝ) * p (ι j) := by positivity
  have hc : (√((Fintype.card k : ℝ) * p (ι j)))⁻¹ * (√((Fintype.card k : ℝ) * p (ι j)))⁻¹ =
      ((Fintype.card k : ℝ) * p (ι j))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hx]
  rw [Matrix.conjTranspose_apply, samplingSketchMatrix_mul_apply, samplingSketchMatrix_mul_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, RCLike.real_smul_eq_coe_mul, ← hc]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', RCLike.star_def, RCLike.conj_ofReal,
    Pi.star_apply, RCLike.ofReal_mul]
  ring

/-! ### Isotropy -/

/-- **Row sampling with positive weights is isotropic.** With zero weights the second moment is
`E [Sᴴ S] = diagonal (fun i => if p i = 0 then 0 else 1) ≤ 1`, which is not isotropy; mixing in
uniform weights, `p = (ℓ/d + 1/n)/2` for the leverage scores `ℓ` of `U` and `d = U.rank`,
restores isotropy at the price of a factor `2` in the domination constant (`ℓᵢ ≤ 2 d pᵢ`). A
weakening of the fixed-subspace injection tails of `NLAlib.Sketching.Properties.Injection` to
`∫ (S ω)ᴴ * S ω ∂μ ≤ 1` (sub-isotropy) would admit zero weights; it is open work for an S1 interface
review (`docs/design/Sketching-S4.md` §8, item 10). [MartinssonTropp2020, §9.6.3]. -/
theorem isIsotropicSketch_of_hasLaw_samplingSketch [Nonempty k]
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1) (hpos : ∀ i, 0 < p i) :
    IsIsotropicSketch S μ := by
  sorry

/-! ### Subspace injection and embedding for a fixed subspace -/

omit [DecidableEq n] in
/-- Under leverage domination with weights summing to one, the rank is at most the domination
constant. -/
private theorem rank_le_of_leverageScore_le (hp : ∑ i, p i = 1)
    (hdom : ∀ i, leverageScore U i ≤ L * p i) : (U.rank : ℝ) ≤ L := by
  calc (U.rank : ℝ) = ∑ i, leverageScore U i := (sum_leverageScore U).symm
    _ ≤ ∑ i, L * p i := Finset.sum_le_sum fun i _ => hdom i
    _ = L := by rw [← Finset.mul_sum, ← NNReal.coe_sum, hp, NNReal.coe_one, mul_one]

omit [DecidableEq n] [Fintype r] in
/-- Every sketch is a subspace embedding for the zero matrix. -/
private theorem measureReal_not_isSubspaceEmbedding_zero (a b : ℝ) :
    μ.real {ω | ¬ IsSubspaceEmbedding (S ω) (0 : Matrix n r 𝕜) a b} = 0 := by
  have h : {ω | ¬ IsSubspaceEmbedding (S ω) (0 : Matrix n r 𝕜) a b} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun ω hω => hω ⟨?_, ?_⟩ <;>
      simp [IsSubspaceInjection]
  rw [h, measureReal_empty]

/-- **The lower half of row sampling**: under leverage domination with constant `L`, the
row-sampling sketch is a subspace injection for `range U` with constant `1 - ε` outside
probability `U.rank · e^{-ε² k/(2L)}`, for every `ε ≥ 0` (vacuous for `ε ≥ 1`). Matrix Chernoff's
lower tail with `R = L / card k`. [Tropp2015, Theorem 5.1.1, (5.1.5), weakened after (5.1.8)];
there `ε ∈ [0, 1)` and the source form `(e^{-ε}/(1 - ε)^{1 - ε})^{k/L}`. -/
theorem hasSubspaceInjection_of_hasLaw_samplingSketch (hS : HasLaw S (samplingSketch k p) μ)
    (hp : ∑ i, p i = 1) (hdom : ∀ i, leverageScore U i ≤ L * p i) (hε : 0 ≤ ε) :
    HasSubspaceInjection S U (1 - ε)
      (U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (2 * L))) μ := by
  sorry

/-- **The upper half of row sampling**: under leverage domination with constant `L`, the
row-sampling sketch satisfies `(S U)ᴴ (S U) ≤ (1 + ε) Uᴴ U` outside probability
`U.rank · e^{-ε² k/(3L)}`, for `0 ≤ ε ≤ 1`; the lower constant `0` holds surely. Matrix Chernoff's
upper tail with `R = L / card k`. [Tropp2015, Theorem 5.1.1, (5.1.6)], with
`ε - (1 + ε) log (1 + ε) ≤ -ε²/3` on `[0, 1]`; there the source form for every `ε ≥ 0`. -/
theorem hasSubspaceEmbedding_zero_of_hasLaw_samplingSketch (hS : HasLaw S (samplingSketch k p) μ)
    (hp : ∑ i, p i = 1) (hdom : ∀ i, leverageScore U i ≤ L * p i) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U 0 (1 + ε)
      (U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L))) μ := by
  sorry

/-- **Row sampling under leverage domination**: if `leverageScore U i ≤ L · p i` for every row,
the row-sampling sketch with `k` samples is a subspace embedding for `range U` with constants
`1 ∓ ε` outside probability `2 U.rank · e^{-ε² k/(3L)}`, for `0 ≤ ε ≤ 1` and any `U`.
[Woodruff2014, Theorem 17] (there `U` with orthonormal columns, `p` a `β`-approximation of the
leverage-score distribution and `s > 144 d log (2d/δ)/(β ε²)` through a Bernstein bound, Fact 1;
here matrix Chernoff, `L = d/β`, any shape and rank); [MartinssonTropp2020, §9.6.3];
[Tropp2015, Theorem 5.1.1].
Result: leverage-sampling-ose -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketch (hS : HasLaw S (samplingSketch k p) μ)
    (hp : ∑ i, p i = 1) (hdom : ∀ i, leverageScore U i ≤ L * p i) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε)
      (2 * U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L))) μ := by
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketch hp)
  have hL : 0 ≤ L := (Nat.cast_nonneg _).trans (rank_le_of_leverageScore_le hp hdom)
  have hlow := hasSubspaceInjection_of_hasLaw_samplingSketch hS hp hdom hε
  have hb : μ.real {ω | ¬ (S ω * U)ᴴ * (S ω * U) ≤ (1 + ε) • (Uᴴ * U)} ≤
      U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L)) :=
    (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω h' => hω h'.upper)).trans
      (hasSubspaceEmbedding_zero_of_hasLaw_samplingSketch hS hp hdom hε hε1)
  refine (hlow.hasSubspaceEmbedding hb).mono le_rfl le_rfl ?_
  have hexp : Real.exp (-ε ^ 2 * Fintype.card k / (2 * L)) ≤
      Real.exp (-ε ^ 2 * Fintype.card k / (3 * L)) := by
    rw [Real.exp_le_exp]
    rcases hL.eq_or_lt with h0 | h0
    · simp [← h0]
    · rw [neg_mul, neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg (α := ℝ) U.rank)
  linarith

/-- **Exact leverage-score sampling**: sampling rows by the leverage-score distribution of `U`
gives a subspace embedding with constants `1 ∓ ε` outside probability
`2 U.rank · e^{-ε² k/(3 U.rank)}`, for `0 ≤ ε ≤ 1`; the domination constant is `L = U.rank`. No
normalisation hypothesis: for `U = 0` the bound is `0` and every embedding event is full.
[MartinssonTropp2020, §9.6.3]; [Woodruff2014, Theorem 17] (`β = 1`).
Result: leverage-sampling-ose -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketch_leverageScoreDistribution
    (hS : HasLaw S (samplingSketch k (leverageScoreDistribution U)) μ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε)
      (2 * U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * U.rank))) μ := by
  rcases eq_or_ne U 0 with hU | hU
  · subst hU
    rw [HasSubspaceEmbedding, measureReal_not_isSubspaceEmbedding_zero, Matrix.rank_zero,
      Nat.cast_zero, mul_zero, zero_mul]
  · exact hasSubspaceEmbedding_of_hasLaw_samplingSketch hS (sum_leverageScoreDistribution hU)
      (leverageScore_le_rank_mul_leverageScoreDistribution U) hε hε1

/-- **Uniform row sampling**: sampling rows uniformly gives a subspace embedding with constants
`1 ∓ ε` outside probability `2 U.rank · e^{-ε² k/(3 coherence U)}`, for `0 ≤ ε ≤ 1`; the
domination constant is `L = coherence U`. No normalisation hypothesis: for empty `n` the bound is
`0` and every embedding event is full. [MartinssonTropp2020, §9.6.2] (there the sample size
`2 ε⁻² μ log (2d/δ)` for coherence `μ`, through matrix Chernoff). -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketch_const_inv_card
    (hS : HasLaw S (samplingSketch k fun _ : n => (Fintype.card n : ℝ≥0)⁻¹) μ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε)
      (2 * U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * coherence U))) μ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hU : U = 0 := Matrix.ext fun i => isEmptyElim i
    subst hU
    rw [HasSubspaceEmbedding, measureReal_not_isSubspaceEmbedding_zero, Matrix.rank_zero,
      Nat.cast_zero, mul_zero, zero_mul]
  · have hc : (Fintype.card n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    refine hasSubspaceEmbedding_of_hasLaw_samplingSketch hS ?_ (fun i => ?_) hε hε1
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hc]
    · rw [NNReal.coe_inv, NNReal.coe_natCast]
      exact leverageScore_le_coherence_mul_inv U i

/-! ### Sample sizes -/

/-- The **row-sampling size** `3 L log (2d/δ) / ε²`: with at least this many samples, row
sampling under leverage domination with constant `L` is a subspace embedding with constants
`1 ∓ ε` and failure probability `δ` for a subspace of dimension `d`, for `0 < ε ≤ 1`
(`NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch_of_samplingSize_le`). The value the proof
reaches, inverting `2 d e^{-ε² k/(3L)} ≤ δ`; [Woodruff2014, Theorem 17] has
`144 d log (2d/δ)/(β ε²)`, which at `L = d/β` is `48` times larger. Consumers use
`NLAlib.samplingSize_le`. Junk values: `0` at `ε = 0`; at most `0` for `δ ≥ 2d`, where the tail
bound is at least `1`. -/
noncomputable irreducible_def samplingSize (d : ℕ) (L ε δ : ℝ) : ℝ :=
  3 * L * Real.log (2 * d / δ) / ε ^ 2

/-- The row-sampling size is nonnegative for `0 ≤ L` and `0 < δ ≤ 2d`. -/
theorem samplingSize_nonneg {d : ℕ} (hL : 0 ≤ L) (hδ : 0 < δ) (hδd : δ ≤ 2 * d) :
    0 ≤ samplingSize d L ε δ := by
  rw [samplingSize_def]
  have hlog : 0 ≤ Real.log (2 * d / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hlog) (sq_nonneg ε)

/-- The row-sampling size is monotone in the dimension `d` and in the domination constant
`L ≥ 0`, and antitone in the distortion `ε > 0` and the failure probability `δ > 0`, as long as
the larger side is in its nontrivial range `δ ≤ 2 d'`. -/
theorem samplingSize_mono {d d' : ℕ} {L' ε' δ' : ℝ} (hd : d ≤ d') (hL : 0 ≤ L) (hLL' : L ≤ L')
    (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ) (hδδ' : δ ≤ δ') (hδd : δ ≤ 2 * d') :
    samplingSize d L ε' δ' ≤ samplingSize d' L' ε δ := by
  have hR := samplingSize_nonneg (ε := ε) (hL.trans hLL') hδ hδd
  rw [samplingSize_def] at hR ⊢
  rw [samplingSize_def]
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  rcases le_or_gt (Real.log (2 * d / δ')) 0 with h0 | h0
  · exact (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hL) h0) (sq_nonneg ε')).trans hR
  · have hpos : 0 < 2 * (d : ℝ) / δ' := by
      refine lt_of_le_of_ne (by positivity) fun h => ?_
      rw [← h, Real.log_zero] at h0
      exact lt_irrefl _ h0
    have hdd : (d : ℝ) ≤ d' := by exact_mod_cast hd
    have hlog : Real.log (2 * d / δ') ≤ Real.log (2 * d' / δ) :=
      Real.log_le_log hpos (div_le_div₀ (by positivity) (by linarith) hδ hδδ')
    exact div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) (hL.trans hLL')) (h0.le.trans hlog))
      (mul_le_mul (by linarith) hlog h0.le (mul_nonneg (by norm_num) (hL.trans hLL')))
      (by positivity) (pow_le_pow_left₀ hε.le hεε' 2)

/-- The explicit comparison `samplingSize d L ε δ ≤ 3 L log (2d/δ) / ε²`, the value the proof
reaches; an improved definition keeps it true. -/
theorem samplingSize_le (d : ℕ) (L ε δ : ℝ) :
    samplingSize d L ε δ ≤ 3 * L * Real.log (2 * d / δ) / ε ^ 2 := by
  rw [samplingSize_def]

/-- The **row-sampling injection size** `2 L log (d/δ) / ε²`: with at least this many samples,
row sampling under leverage domination with constant `L` is a subspace injection with constant
`1 - ε` and failure probability `δ` for a subspace of dimension `d`, for `ε > 0`
(`NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketch_of_samplingInjectionSize_le`). The value
the proof reaches, inverting `d e^{-ε² k/(2L)} ≤ δ`; one tail, against the embedding's two.
Consumers use `NLAlib.samplingInjectionSize_le`. Junk values: `0` at `ε = 0`; at most `0` for
`δ ≥ d`, where the tail bound is at least `1`. -/
noncomputable irreducible_def samplingInjectionSize (d : ℕ) (L ε δ : ℝ) : ℝ :=
  2 * L * Real.log (d / δ) / ε ^ 2

/-- The row-sampling injection size is nonnegative for `0 ≤ L` and `0 < δ ≤ d`. -/
theorem samplingInjectionSize_nonneg {d : ℕ} (hL : 0 ≤ L) (hδ : 0 < δ) (hδd : δ ≤ d) :
    0 ≤ samplingInjectionSize d L ε δ := by
  rw [samplingInjectionSize_def]
  have hlog : 0 ≤ Real.log (d / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hlog) (sq_nonneg ε)

/-- The row-sampling injection size is monotone in the dimension `d` and in the domination
constant `L ≥ 0`, and antitone in the distortion `ε > 0` and the failure probability `δ > 0`, as
long as the larger side is in its nontrivial range `δ ≤ d'`. -/
theorem samplingInjectionSize_mono {d d' : ℕ} {L' ε' δ' : ℝ} (hd : d ≤ d') (hL : 0 ≤ L)
    (hLL' : L ≤ L') (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ) (hδδ' : δ ≤ δ') (hδd : δ ≤ d') :
    samplingInjectionSize d L ε' δ' ≤ samplingInjectionSize d' L' ε δ := by
  have hR := samplingInjectionSize_nonneg (ε := ε) (hL.trans hLL') hδ hδd
  rw [samplingInjectionSize_def] at hR ⊢
  rw [samplingInjectionSize_def]
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  rcases le_or_gt (Real.log (d / δ')) 0 with h0 | h0
  · exact (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hL) h0) (sq_nonneg ε')).trans hR
  · have hpos : 0 < (d : ℝ) / δ' := by
      refine lt_of_le_of_ne (by positivity) fun h => ?_
      rw [← h, Real.log_zero] at h0
      exact lt_irrefl _ h0
    have hdd : (d : ℝ) ≤ d' := by exact_mod_cast hd
    have hlog : Real.log (d / δ') ≤ Real.log (d' / δ) :=
      Real.log_le_log hpos (div_le_div₀ (by positivity) hdd hδ hδδ')
    exact div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) (hL.trans hLL')) (h0.le.trans hlog))
      (mul_le_mul (by linarith) hlog h0.le (mul_nonneg (by norm_num) (hL.trans hLL')))
      (by positivity) (pow_le_pow_left₀ hε.le hεε' 2)

/-- The explicit comparison `samplingInjectionSize d L ε δ ≤ 2 L log (d/δ) / ε²`, the value the
proof reaches; an improved definition keeps it true. -/
theorem samplingInjectionSize_le (d : ℕ) (L ε δ : ℝ) :
    samplingInjectionSize d L ε δ ≤ 2 * L * Real.log (d / δ) / ε ^ 2 := by
  rw [samplingInjectionSize_def]

/-- **Row sampling, sample-size form**: with at least `NLAlib.samplingSize U.rank L ε δ` samples,
row sampling under leverage domination is a subspace embedding for `range U` with constants
`1 ∓ ε` and failure probability `δ`, for `0 < ε ≤ 1` and `δ > 0`. [Woodruff2014, Theorem 17]
(constant `144/β` there, `3` here at `L = d/β`); [MartinssonTropp2020, §9.6.3].
Result: leverage-sampling-ose -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketch_of_samplingSize_le
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hdom : ∀ i, leverageScore U i ≤ L * p i) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : samplingSize U.rank L ε δ ≤ Fintype.card k) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε) δ μ := by
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketch hp)
  refine (hasSubspaceEmbedding_of_hasLaw_samplingSketch hS hp hdom hε.le hε1).mono le_rfl le_rfl ?_
  rcases Nat.eq_zero_or_pos U.rank with hd | hd
  · rw [hd, Nat.cast_zero, mul_zero, zero_mul]
    exact hδ.le
  have hd' : (0 : ℝ) < U.rank := Nat.cast_pos.2 hd
  have hL : 0 < L := hd'.trans_le (rank_le_of_leverageScore_le hp hdom)
  rw [samplingSize_def, div_le_iff₀ (by positivity)] at hk
  have hlog : Real.log (2 * U.rank / δ) ≤ ε ^ 2 * Fintype.card k / (3 * L) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [Real.log_le_iff_le_exp (by positivity), div_le_iff₀ hδ] at hlog
  rw [neg_mul, neg_div, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

/-- **The lower half, sample-size form**: with at least
`NLAlib.samplingInjectionSize U.rank L ε δ` samples, row sampling under leverage domination is a
subspace injection for `range U` with constant `1 - ε` and failure probability `δ`, for `ε > 0`
and `δ > 0`. -/
theorem hasSubspaceInjection_of_hasLaw_samplingSketch_of_samplingInjectionSize_le
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hdom : ∀ i, leverageScore U i ≤ L * p i) (hε : 0 < ε) (hδ : 0 < δ)
    (hk : samplingInjectionSize U.rank L ε δ ≤ Fintype.card k) :
    HasSubspaceInjection S U (1 - ε) δ μ := by
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketch hp)
  refine (hasSubspaceInjection_of_hasLaw_samplingSketch hS hp hdom hε.le).mono le_rfl ?_
  rcases Nat.eq_zero_or_pos U.rank with hd | hd
  · rw [hd, Nat.cast_zero, zero_mul]
    exact hδ.le
  have hd' : (0 : ℝ) < U.rank := Nat.cast_pos.2 hd
  have hL : 0 < L := hd'.trans_le (rank_le_of_leverageScore_le hp hdom)
  rw [samplingInjectionSize_def, div_le_iff₀ (by positivity)] at hk
  have hlog : Real.log (U.rank / δ) ≤ ε ^ 2 * Fintype.card k / (2 * L) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [Real.log_le_iff_le_exp (by positivity), div_le_iff₀ hδ] at hlog
  rw [neg_mul, neg_div, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

end NLAlib
