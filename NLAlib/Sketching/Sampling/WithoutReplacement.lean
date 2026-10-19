/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.MatrixConcentration.ChernoffWithoutReplacement
public import NLAlib.Sketching.Properties.FixedSubspace
public import NLAlib.Sketching.Properties.Isotropic
public import NLAlib.Sketching.Sampling.RowSampling

/-!
# Row sampling without replacement

Sampling $\lvert k \rvert$ rows of an $n$-row matrix without replacement, in order, is a uniformly
random injection $\iota : k \to n$ (`uniformOn {ι : k → n | Function.Injective ι}`), and the
sketch is `NLAlib.samplingSketchMatrix` at uniform weights: row $j$ is
$\sqrt{\lvert n \rvert / \lvert k \rvert}\, \mathbf{e}_{\iota(j)}^{\mathsf{H}}$, so the sketch is
$\sqrt{\lvert n \rvert / \lvert k \rvert}\, \mathbf{P}^{\mathsf{H}}$ for the selection matrix
$\mathbf{P}$ of $\iota$. Its law `NLAlib.samplingSketchWithoutReplacement k n` is the pushforward
of the uniform injection; the measurable space on the row index `n` is fixed to `⊤` inside the
definition, so no statement carries an instance on `n`, and
`NLAlib.samplingSketchWithoutReplacement_eq_map` recovers the pushforward under any measurable space
on `n` with measurable singletons.

For a fixed $\mathbf{U} : n \times r$ of any shape and rank whose leverage scores are dominated by
uniform weights, $\ell_i(\mathbf{U}) \le L / \lvert n \rvert$, the sketch is a random subspace
injection with failure probability $d\, e^{-\varepsilon^2 k / (2L)}$ and a random subspace embedding
with constants $1 \mp \varepsilon$ and failure probability $2 d\, e^{-\varepsilon^2 k / (3L)}$ for
$0 \le \varepsilon \le 1$, $d = \operatorname{rank}\mathbf{U}$: the bounds of uniform sampling with
replacement (`NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch_const_inv_card`), here from the
matrix Chernoff inequalities without replacement
(`NLAlib.Probability.MatrixConcentration.ChernoffWithoutReplacement`). With $L$ the coherence of
$\mathbf{U}$ the domination always holds. The sample sizes are those of sampling with
replacement: <!-- value samplingEmbeddingDim d L \varepsilon \delta -->
$\lvert k \rvert \ge 3 L \log(2d/\delta)/\varepsilon^2$ for the embedding
(`NLAlib.samplingEmbeddingDim`) and <!-- value samplingInjectionDim d L \varepsilon \delta -->
$\lvert k \rvert \ge 2 L \log(d/\delta)/\varepsilon^2$ for the injection
(`NLAlib.samplingInjectionDim`).

Degenerate cases. For $\lvert n \rvert < \lvert k \rvert$ there is no injection and the law is the
zero measure, so `HasLaw` forces $\mu = 0$ and every tail holds; no $\lvert k \rvert \le
\lvert n \rvert$ is assumed on the tails. For empty `k` the law is a Dirac mass at $\mathbf{0}$, the
bound $d \cdot e^0$ is at least $1$ when $\mathbf{U} \ne \mathbf{0}$, and the sketch is not
isotropic, hence `[Nonempty k]` on isotropy. Rank zero: every failure event is empty. $L \le 0$
forces rank zero, so no $0 < L$ is assumed. For $\varepsilon \ge 1$ the injection is vacuous.
The tails rest on Hoeffding's comparison of sampling without and with replacement
(`NLAlib.Probability.ConvexOrder`). Design: `docs/design/Sketching-S5.md` §3.4, §8.

## Main definitions

* `NLAlib.samplingSketchWithoutReplacement`: the law of the sketch.

## Main results

* `NLAlib.samplingSketchWithoutReplacement_eq_sum_smul_dirac`,
  `NLAlib.samplingSketchWithoutReplacement_eq_map`,
  `NLAlib.hasLaw_samplingSketchMatrix_of_hasLaw_uniformOn_injective`: the law as a mixture, as a
  pushforward, and the bridge from a user's own injection.
* `NLAlib.isIsotropicSketch_of_hasLaw_samplingSketchWithoutReplacement`: isotropy.
* `NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement`,
  `NLAlib.hasSubspaceEmbedding_zero_of_hasLaw_samplingSketchWithoutReplacement`: the two halves.
* `NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement`: row sampling without
  replacement under leverage domination;
  `NLAlib.hasSubspaceEmbedding_coherence_of_hasLaw_samplingSketchWithoutReplacement` at the
  coherence.
* `hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement_of_samplingEmbeddingDim_le`
  and its lower-half twin
  `hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement_of_samplingInjectionDim_le`:
  sample sizes.
* `NLAlib.exists_forall_hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement`,
  `NLAlib.exists_forall_hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement`: the
  asymptotic forms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal ENNReal Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n r : Type*} [Fintype k] [Fintype n] [Fintype r] [DecidableEq n]
  {S : Ω → Matrix k n 𝕜} {U : Matrix n r 𝕜} {L ε δ : ℝ}

/-! ### The law -/

variable (k n) in
/-- The **law of the row-sampling sketch without replacement**: the pushforward by
`NLAlib.samplingSketchMatrix` at uniform weights $1 / \lvert n \rvert$ of a uniformly random
injection $\iota : k \to n$. Row $j$ of the sketch is
$\sqrt{\lvert n \rvert / \lvert k \rvert}\, \mathbf{e}_{\iota(j)}^{\mathsf{H}}$, so the sketch is
$\sqrt{\lvert n \rvert / \lvert k \rvert}\, \mathbf{P}^{\mathsf{H}}$ for the selection matrix
$\mathbf{P}$ of $\iota$. The measurable space on `n` is `⊤` inside the definition;
`NLAlib.samplingSketchWithoutReplacement_eq_map` restates it under any measurable space on `n` with
measurable singletons, and `NLAlib.samplingSketchWithoutReplacement_eq_sum_smul_dirac` as a finite
mixture of Diracs. Junk value: the zero measure when $\lvert n \rvert < \lvert k \rvert$.
[HalkoMartinssonTropp2011, §4.6] (the restriction $\mathbf{R}$ of the SRFT);
[MartinssonTropp2020, §9.6.2] (mentioned there, not analysed). -/
noncomputable def samplingSketchWithoutReplacement : Measure (Matrix k n 𝕜) :=
  let _ : MeasurableSpace n := ⊤
  (uniformOn {ι : k → n | Function.Injective ι}).map
    (samplingSketchMatrix fun _ => (Fintype.card n : ℝ≥0)⁻¹)

/-- The law of the row-sampling sketch without replacement is a finite measure. -/
instance isFiniteMeasure_samplingSketchWithoutReplacement :
    IsFiniteMeasure (samplingSketchWithoutReplacement (𝕜 := 𝕜) k n) := by
  unfold samplingSketchWithoutReplacement
  infer_instance

/-- The law of the row-sampling sketch without replacement is a probability measure when
$\lvert k \rvert \le \lvert n \rvert$. -/
theorem isProbabilityMeasure_samplingSketchWithoutReplacement
    (hk : Fintype.card k ≤ Fintype.card n) :
    IsProbabilityMeasure (samplingSketchWithoutReplacement (𝕜 := 𝕜) k n) := by
  let _ : MeasurableSpace n := ⊤
  have := isProbabilityMeasure_uniformOn_injective (k := k) (n := n) hk
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

omit [Fintype k] [Fintype n] [Fintype r] [DecidableEq n] in
/-- The pushforward of the uniform injection by any map, evaluated on a measurable set, by
counting, under any measurable space on `n` with measurable singletons. -/
private theorem map_uniformOn_injective_apply [Finite k] [Finite n] [MeasurableSpace n]
    [MeasurableSingletonClass n]
    (F : (k → n) → Matrix k n 𝕜) {s : Set (Matrix k n 𝕜)} (hs : MeasurableSet s) :
    (uniformOn {ι : k → n | Function.Injective ι}).map F s =
      ({ι : k → n | Function.Injective ι}.encard : ℝ≥0∞)⁻¹ *
        ({ι : k → n | Function.Injective ι} ∩ F ⁻¹' s).encard := by
  rw [Measure.map_apply (measurable_of_countable F) hs, uniformOn,
    cond_apply (Set.toFinite _).measurableSet, Measure.count_apply (Set.toFinite _).measurableSet,
    Measure.count_apply (Set.toFinite _).measurableSet]

omit [Fintype k] [Fintype n] [Fintype r] [DecidableEq n] in
/-- The uniform law on injections as a finite mixture of Diracs, under any measurable space on `n`
with measurable singletons. -/
private theorem uniformOn_injective_eq_sum [Fintype k] [Fintype n] [MeasurableSpace n]
    [MeasurableSingletonClass n] :
    uniformOn {ι : k → n | Function.Injective ι} =
      ∑ e : k ↪ n, ((Fintype.card n).descFactorial (Fintype.card k) : ℝ≥0∞)⁻¹ •
        Measure.dirac (⇑e : k → n) := by
  refine Measure.ext_of_singleton fun f => ?_
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton f)]
  by_cases hf : Function.Injective f
  · rw [uniformOn_injective_singleton hf, Finset.sum_eq_single (⟨f, hf⟩ : k ↪ n)]
    · rw [Function.Embedding.coeFn_mk, Set.indicator_of_mem (Set.mem_singleton f), Pi.one_apply,
        mul_one]
    · intro e _ he
      have hne : (⇑e : k → n) ∉ ({f} : Set (k → n)) := fun h =>
        he (DFunLike.coe_injective (Set.mem_singleton_iff.1 h))
      rw [Set.indicator_of_notMem hne, mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  · have h0 : uniformOn {ι : k → n | Function.Injective ι} {f} = 0 := by
      rw [uniformOn, cond_apply (Set.toFinite _).measurableSet,
        Set.inter_singleton_eq_empty.2 hf, measure_empty, mul_zero]
    rw [h0]
    refine (Finset.sum_eq_zero fun e _ => ?_).symm
    have hne : (⇑e : k → n) ∉ ({f} : Set (k → n)) := fun h =>
      hf (by rw [← Set.mem_singleton_iff.1 h]; exact e.injective)
    rw [Set.indicator_of_notMem hne, mul_zero]

/-- The law of the row-sampling sketch without replacement as a finite mixture of Diracs, one
atom per injection $e : k \hookrightarrow n$ with mass $1 / (\lvert n \rvert)_{\lvert k \rvert}$
(the falling factorial). -/
theorem samplingSketchWithoutReplacement_eq_sum_smul_dirac :
    samplingSketchWithoutReplacement (𝕜 := 𝕜) k n =
      ∑ e : k ↪ n, ((Fintype.card n).descFactorial (Fintype.card k) : ℝ≥0∞)⁻¹ •
        Measure.dirac (samplingSketchMatrix (fun _ => (Fintype.card n : ℝ≥0)⁻¹) e) := by
  let _ : MeasurableSpace n := ⊤
  have hF : Measurable (samplingSketchMatrix (𝕜 := 𝕜) (k := k)
      fun _ : n => (Fintype.card n : ℝ≥0)⁻¹) := measurable_of_countable _
  ext s hs
  rw [show samplingSketchWithoutReplacement (𝕜 := 𝕜) k n =
      (uniformOn {ι : k → n | Function.Injective ι}).map
        (samplingSketchMatrix fun _ => (Fintype.card n : ℝ≥0)⁻¹) from rfl,
    Measure.map_apply hF hs, uniformOn_injective_eq_sum]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (hF hs), Measure.dirac_apply' _ hs]
  rfl

/-- The law of the row-sampling sketch without replacement is the pushforward of a uniform
injection under any measurable space on `n` with measurable singletons. -/
theorem samplingSketchWithoutReplacement_eq_map [MeasurableSpace n] [MeasurableSingletonClass n] :
    samplingSketchWithoutReplacement (𝕜 := 𝕜) k n =
      (uniformOn {ι : k → n | Function.Injective ι}).map
        (samplingSketchMatrix fun _ => (Fintype.card n : ℝ≥0)⁻¹) := by
  ext s hs
  rw [map_uniformOn_injective_apply _ hs]
  let _ : MeasurableSpace n := ⊤
  exact map_uniformOn_injective_apply _ hs

/-- **From the user's own injection**: if $\iota$ is a uniformly random injection $k \to n$, the
sketch built from it at uniform weights has law `NLAlib.samplingSketchWithoutReplacement k n`. -/
theorem hasLaw_samplingSketchMatrix_of_hasLaw_uniformOn_injective [MeasurableSpace n]
    [MeasurableSingletonClass n] {ι : Ω → k → n}
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) :
    HasLaw (fun ω => (samplingSketchMatrix (fun _ => (Fintype.card n : ℝ≥0)⁻¹) (ι ω) :
      Matrix k n 𝕜)) (samplingSketchWithoutReplacement k n) μ := by
  rw [samplingSketchWithoutReplacement_eq_map]
  have hY : HasLaw (samplingSketchMatrix (𝕜 := 𝕜) fun _ => (Fintype.card n : ℝ≥0)⁻¹)
      ((uniformOn {f : k → n | Function.Injective f}).map
        (samplingSketchMatrix fun _ => (Fintype.card n : ℝ≥0)⁻¹))
      (uniformOn {f : k → n | Function.Injective f}) :=
    ⟨(measurable_of_countable _).aemeasurable, rfl⟩
  exact hY.comp hι

/-! ### Isotropy -/

/-- **Row sampling without replacement is isotropic**:
$\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \mathbf{I}$ for nonempty `k` and
$\lvert k \rvert \le \lvert n \rvert$, since each draw is uniform
(`NLAlib.map_eval_uniformOn_injective`) and the rows carry the scale
$\sqrt{\lvert n \rvert / \lvert k \rvert}$. [MartinssonTropp2020, §9.6.2] (with replacement). -/
theorem isIsotropicSketch_of_hasLaw_samplingSketchWithoutReplacement [Nonempty k]
    (hS : HasLaw S (samplingSketchWithoutReplacement k n) μ)
    (hk : Fintype.card k ≤ Fintype.card n) : IsIsotropicSketch S μ := by
  let _ : MeasurableSpace n := ⊤
  have := isProbabilityMeasure_uniformOn_injective (k := k) (n := n) hk
  have hk0 : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hn0 : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Fintype.card_pos.trans_le hk))
  have hB := hasLaw_samplingSketchMatrix_of_hasLaw_uniformOn_injective (𝕜 := 𝕜)
    (HasLaw.id (μ := uniformOn {ι : k → n | Function.Injective ι}))
  refine hS.isIsotropicSketch_iff.2 (hB.isIsotropicSketch_iff.1 ⟨fun i j => MemLp.of_discrete, ?_⟩)
  set c : ℝ := ((Fintype.card k : ℝ) * ((Fintype.card n : ℝ≥0)⁻¹ : ℝ≥0))⁻¹ with hc
  set G : n → Matrix n n 𝕜 := fun i =>
    c • Matrix.vecMulVec (star ((1 : Matrix n n 𝕜) i)) ((1 : Matrix n n 𝕜) i) with hG
  have e (ι : k → n) : (samplingSketchMatrix (fun _ => (Fintype.card n : ℝ≥0)⁻¹) ι :
      Matrix k n 𝕜)ᴴ * samplingSketchMatrix (fun _ => (Fintype.card n : ℝ≥0)⁻¹) ι =
      ∑ j, G (ι j) := by
    have h := conjTranspose_samplingSketchMatrix_mul_mul (fun _ => (Fintype.card n : ℝ≥0)⁻¹) ι
      (1 : Matrix n n 𝕜) (1 : Matrix n n 𝕜)
    rwa [Matrix.mul_one] at h
  have hj (j : k) : ∫ ι : k → n, G (ι j) ∂uniformOn {ι : k → n | Function.Injective ι} =
      (Fintype.card n : ℝ)⁻¹ • ∑ i, G i := by
    rw [← integral_map (φ := fun ι : k → n => ι j) (measurable_of_countable _).aemeasurable
      .of_discrete, map_eval_uniformOn_injective hk j, ← samplingMeasure_const_inv_card,
      integral_samplingMeasure, Finset.smul_sum]
    simp only [NNReal.coe_inv, NNReal.coe_natCast]
  have hsum : ∑ i, G i = c • (1 : Matrix n n 𝕜) := by
    rw [hG, ← Finset.smul_sum, ← Matrix.conjTranspose_mul_eq_sum_vecMulVec,
      Matrix.conjTranspose_one, Matrix.mul_one]
  simp only [id, e]
  rw [integral_finsetSum _ fun j _ => Integrable.of_finite, Finset.sum_congr rfl fun j _ => hj j,
    hsum, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul,
    hc, NNReal.coe_inv, NNReal.coe_natCast]
  convert one_smul ℝ (1 : Matrix n n 𝕜) using 2
  field_simp

/-! ### Subspace injection and embedding for a fixed subspace -/

/-- With fewer members than samples, the probability space of the sketch is zero. -/
private theorem eq_zero_of_hasLaw_samplingSketchWithoutReplacement
    (hS : HasLaw S (samplingSketchWithoutReplacement k n) μ)
    (hk : Fintype.card n < Fintype.card k) : μ = 0 := by
  have h := hS.map_eq
  have h0 : samplingSketchWithoutReplacement (𝕜 := 𝕜) k n = 0 := by
    let _ : MeasurableSpace n := ⊤
    rw [samplingSketchWithoutReplacement_eq_map, uniformOn_injective_of_card_lt hk,
      Measure.map_zero]
  rw [h0] at h
  exact (Measure.map_eq_zero_iff hS.aemeasurable).1 h

section Primitive

variable [MeasurableSpace n] [MeasurableSingletonClass n] {d : ℕ} {Q : Matrix n (Fin d) 𝕜}

open scoped ComplexOrder in
omit [DecidableEq n] [MeasurableSpace n] [MeasurableSingletonClass n] in
/-- The population of Chernoff atoms of the sketched Gram matrix of `Q` at uniform weights:
positive semidefinite, at most `L / card k`, with mean `Qᴴ Q = 1`. -/
private theorem atoms_of_hasOrthonormalCols [Nonempty k] (hk : Fintype.card k ≤ Fintype.card n)
    (hQ : HasOrthonormalCols Q) (hL : 0 ≤ L)
    (hdomQ : ∀ i, ‖WithLp.toLp 2 (Q i)‖ ^ 2 ≤ L * ((Fintype.card n : ℝ≥0)⁻¹ : ℝ≥0)) :
    let X : n → Matrix (Fin d) (Fin d) 𝕜 := fun i =>
      ((Fintype.card k : ℝ) * ((Fintype.card n : ℝ≥0)⁻¹ : ℝ≥0))⁻¹ •
        Matrix.vecMulVec (star (Q i)) (Q i)
    (∀ i, (X i).PosSemidef) ∧ (∀ i, X i ≤ (L / Fintype.card k) • (1 : Matrix (Fin d) (Fin d) 𝕜)) ∧
      ((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i = 1 := by
  intro X
  have hk0 : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hn0 : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Fintype.card_pos.trans_le hk))
  refine ⟨fun i => (Matrix.posSemidef_vecMulVec_star_self _).smul (by positivity),
    fun i => inv_mul_smul_vecMulVec_star_self_le (Nat.cast_nonneg _) hL (hdomQ i), ?_⟩
  simp only [X]
  rw [← Finset.smul_sum, ← Matrix.conjTranspose_mul_eq_sum_vecMulVec, hQ.conjTranspose_mul_self,
    smul_smul, NNReal.coe_inv, NNReal.coe_natCast]
  convert one_smul ℝ (1 : Matrix (Fin d) (Fin d) 𝕜) using 2
  field_simp

/-- The lower Chernoff tail on the primitive space, for `Q` with orthonormal columns. -/
private theorem hasSubspaceInjection_uniformOn_injective [Nonempty k] [Nonempty (Fin d)]
    (hk : Fintype.card k ≤ Fintype.card n) (hQ : HasOrthonormalCols Q) (hL : 0 < L)
    (hdomQ : ∀ i, ‖WithLp.toLp 2 (Q i)‖ ^ 2 ≤ L * ((Fintype.card n : ℝ≥0)⁻¹ : ℝ≥0))
    (hε : 0 ≤ ε) :
    HasSubspaceInjection (samplingSketchMatrix (𝕜 := 𝕜) fun _ => (Fintype.card n : ℝ≥0)⁻¹) Q
      (1 - ε) (d * Real.exp (-ε ^ 2 * Fintype.card k / (2 * L)))
      (uniformOn {ι : k → n | Function.Injective ι}) := by
  have := isProbabilityMeasure_uniformOn_injective (k := k) (n := n) hk
  rcases le_or_gt 1 ε with h1 | h1
  · have he : {ι : k → n | ¬ IsSubspaceInjection
        (samplingSketchMatrix (𝕜 := 𝕜) (fun _ => (Fintype.card n : ℝ≥0)⁻¹) ι) Q (1 - ε)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ι hι =>
        hι (isSubspaceInjection_of_nonpos _ _ (by linarith))
    rw [HasSubspaceInjection, he, measureReal_empty]
    positivity
  obtain ⟨hpsd, hle, hV⟩ := atoms_of_hasOrthonormalCols (k := k) hk hQ hL.le hdomQ
  have hk' : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨j₀, hj₀⟩ : ∃ j, j + 1 = Fintype.card (Fin d) :=
    ⟨Fintype.card (Fin d) - 1, Nat.sub_add_cancel Fintype.card_pos⟩
  have hC := measureReal_eigenvalue_sum_le_le_card_mul_exp_of_hasLaw_uniformOn_injective
    (HasLaw.id (μ := uniformOn {ι : k → n | Function.Injective ι})) (div_pos hL hk') hpsd hle hj₀
    hε h1
  rw [hV, eigenvalue_one (by omega)] at hC
  refine hQ.hasSubspaceInjection_of_measureReal_le hj₀
    ((measureReal_mono (Set.ofPred_subset_ofPred.2 fun ι hι => ?_)).trans (hC.trans_eq ?_))
  · rw [singularValues_sq, conjTranspose_samplingSketchMatrix_mul_mul] at hι
    rw [mul_one]
    exact hι
  · rw [Fintype.card_fin]
    congr 2
    field_simp

/-- The upper Chernoff tail on the primitive space, for `Q` with orthonormal columns. -/
private theorem hasSubspaceEmbedding_zero_uniformOn_injective [Nonempty k] [Nonempty (Fin d)]
    (hk : Fintype.card k ≤ Fintype.card n) (hQ : HasOrthonormalCols Q) (hL : 0 < L)
    (hdomQ : ∀ i, ‖WithLp.toLp 2 (Q i)‖ ^ 2 ≤ L * ((Fintype.card n : ℝ≥0)⁻¹ : ℝ≥0))
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding (samplingSketchMatrix (𝕜 := 𝕜) fun _ => (Fintype.card n : ℝ≥0)⁻¹) Q
      0 (1 + ε) (d * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L)))
      (uniformOn {ι : k → n | Function.Injective ι}) := by
  have := isProbabilityMeasure_uniformOn_injective (k := k) (n := n) hk
  obtain ⟨hpsd, hle, hV⟩ := atoms_of_hasOrthonormalCols (k := k) hk hQ hL.le hdomQ
  have hk' : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have hC := measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp_of_hasLaw_uniformOn_injective
    (HasLaw.id (μ := uniformOn {ι : k → n | Function.Injective ι})) (div_pos hL hk') hpsd hle hε hε1
  rw [hV, eigenvalue_one Fintype.card_pos] at hC
  refine hQ.hasSubspaceEmbedding_zero_of_measureReal_le
    ((measureReal_mono (Set.ofPred_subset_ofPred.2 fun ι hι => ?_)).trans (hC.trans_eq ?_))
  · rw [singularValues_sq, conjTranspose_samplingSketchMatrix_mul_mul] at hι
    rw [mul_one]
    exact hι
  · rw [Fintype.card_fin]
    congr 2
    field_simp

end Primitive

/-- **The lower half of row sampling without replacement**: if the leverage scores of
$\mathbf{U}$ satisfy $\ell_i(\mathbf{U}) \le L / \lvert n \rvert$, the sketch is a subspace
injection for $\operatorname{range}\mathbf{U}$ with constant $1 - \varepsilon$ outside probability
$\operatorname{rank}\mathbf{U} \cdot e^{-\varepsilon^2 k / (2L)}$, for every $\varepsilon \ge 0$
(vacuous for $\varepsilon \ge 1$). Matrix Chernoff's lower tail without replacement with
$R = L / \lvert k \rvert$. [Tropp2011a] (sampling without replacement); [Tropp2015, Theorem 5.1.1,
(5.1.5), weakened after (5.1.8)] (the i.i.d. form, the same bound). -/
theorem hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement
    (hS : HasLaw S (samplingSketchWithoutReplacement k n) μ)
    (hdom : ∀ i, leverageScore U i ≤ L * (Fintype.card n : ℝ)⁻¹) (hε : 0 ≤ ε) :
    HasSubspaceInjection S U (1 - ε)
      (U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (2 * L))) μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  rcases Nat.eq_zero_or_pos U.rank with hd | hd
  · rw [hd, Nat.cast_zero, zero_mul]
    exact (hasSubspaceEmbedding_of_rank_eq_zero (b := 0) hd le_rfl).hasSubspaceInjection
  have hL : 0 < L := pos_of_leverageScore_le_mul_inv_card hdom hd
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [HasSubspaceInjection, eq_zero_of_hasLaw_samplingSketchWithoutReplacement hS hk,
      measureReal_zero_apply]
    positivity
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketchWithoutReplacement hk)
  rcases isEmpty_or_nonempty k with hk0 | hk0
  · refine measureReal_le_one.trans ?_
    rw [Fintype.card_eq_zero, Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one]
    exact_mod_cast hd
  obtain ⟨Q, hQ, hUQ, hdomQ⟩ := exists_hasOrthonormalCols_of_leverageScore_le
    (p := fun _ => (Fintype.card n : ℝ≥0)⁻¹) (leverageScore_le_mul_const_inv_card hdom)
  have : Nonempty (Fin U.rank) := ⟨⟨0, hd⟩⟩
  let _ : MeasurableSpace n := ⊤
  have h := hasSubspaceInjection_uniformOn_injective (k := k) hk hQ hL hdomQ hε
  have hB := hasLaw_samplingSketchMatrix_of_hasLaw_uniformOn_injective (𝕜 := 𝕜)
    (HasLaw.id (μ := uniformOn {ι : k → n | Function.Injective ι}))
  exact (hS.hasSubspaceInjection_iff.2 (hB.hasSubspaceInjection_iff.1 h)).of_range_le hUQ

/-- **The upper half of row sampling without replacement**: under the domination
$\ell_i(\mathbf{U}) \le L / \lvert n \rvert$, the sketch satisfies
$(\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U}
\preceq (1 + \varepsilon)\, \mathbf{U}^{\mathsf{H}}\mathbf{U}$ outside probability
$\operatorname{rank}\mathbf{U} \cdot e^{-\varepsilon^2 k / (3L)}$, for
$0 \le \varepsilon \le 1$; the lower constant $0$ holds surely. [Tropp2011a];
[Tropp2015, Theorem 5.1.1, (5.1.6)] (the i.i.d. form), with
$\varepsilon - (1 + \varepsilon) \log (1 + \varepsilon) \le -\varepsilon^2/3$ on $[0, 1]$. -/
theorem hasSubspaceEmbedding_zero_of_hasLaw_samplingSketchWithoutReplacement
    (hS : HasLaw S (samplingSketchWithoutReplacement k n) μ)
    (hdom : ∀ i, leverageScore U i ≤ L * (Fintype.card n : ℝ)⁻¹) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U 0 (1 + ε)
      (U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L))) μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  rcases Nat.eq_zero_or_pos U.rank with hd | hd
  · rw [hd, Nat.cast_zero, zero_mul]
    exact hasSubspaceEmbedding_of_rank_eq_zero hd le_rfl
  have hL : 0 < L := pos_of_leverageScore_le_mul_inv_card hdom hd
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [HasSubspaceEmbedding, eq_zero_of_hasLaw_samplingSketchWithoutReplacement hS hk,
      measureReal_zero_apply]
    positivity
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketchWithoutReplacement hk)
  rcases isEmpty_or_nonempty k with hk0 | hk0
  · refine measureReal_le_one.trans ?_
    rw [Fintype.card_eq_zero, Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one]
    exact_mod_cast hd
  obtain ⟨Q, hQ, hUQ, hdomQ⟩ := exists_hasOrthonormalCols_of_leverageScore_le
    (p := fun _ => (Fintype.card n : ℝ≥0)⁻¹) (leverageScore_le_mul_const_inv_card hdom)
  have : Nonempty (Fin U.rank) := ⟨⟨0, hd⟩⟩
  let _ : MeasurableSpace n := ⊤
  have h := hasSubspaceEmbedding_zero_uniformOn_injective (k := k) hk hQ hL hdomQ hε hε1
  have hB := hasLaw_samplingSketchMatrix_of_hasLaw_uniformOn_injective (𝕜 := 𝕜)
    (HasLaw.id (μ := uniformOn {ι : k → n | Function.Injective ι}))
  exact (hS.hasSubspaceEmbedding_iff.2 (hB.hasSubspaceEmbedding_iff.1 h)).of_range_le hUQ

/-- **Row sampling without replacement**: if the leverage scores of $\mathbf{U}$ (any shape and
rank) satisfy $\ell_i(\mathbf{U}) \le L / \lvert n \rvert$, the row-sampling sketch without
replacement with $k$ samples is a subspace embedding for $\operatorname{range}\mathbf{U}$ with
constants $1 \mp \varepsilon$ outside probability
$2 \operatorname{rank}\mathbf{U} \cdot e^{-\varepsilon^2 k / (3L)}$, for
$0 \le \varepsilon \le 1$. Sampling without replacement is never worse than with replacement
(`NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch` at uniform weights has the same bound).
[Tropp2011a] (the sampling step of the SRHT, there for orthonormal columns and
$L = \lvert n \rvert \max_i \ell_i$); [Tropp2015, Theorem 5.1.1] (the i.i.d. form).
Result: sampling-without-replacement-ose -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement
    (hS : HasLaw S (samplingSketchWithoutReplacement k n) μ)
    (hdom : ∀ i, leverageScore U i ≤ L * (Fintype.card n : ℝ)⁻¹) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε)
      (2 * U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L))) μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  rcases Nat.eq_zero_or_pos U.rank with hd | hd
  · exact hasSubspaceEmbedding_of_rank_eq_zero hd (by positivity)
  have hL : 0 < L := pos_of_leverageScore_le_mul_inv_card hdom hd
  have hlow := hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement hS hdom hε
  have hb : μ.real {ω | ¬ (S ω * U)ᴴ * (S ω * U) ≤ (1 + ε) • (Uᴴ * U)} ≤
      U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L)) :=
    (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω h' => hω h'.upper)).trans
      (hasSubspaceEmbedding_zero_of_hasLaw_samplingSketchWithoutReplacement hS hdom hε hε1)
  refine (hlow.hasSubspaceEmbedding hb).mono le_rfl le_rfl ?_
  have hexp : Real.exp (-ε ^ 2 * Fintype.card k / (2 * L)) ≤
      Real.exp (-ε ^ 2 * Fintype.card k / (3 * L)) := by
    rw [Real.exp_le_exp, neg_mul, neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg (α := ℝ) U.rank)
  linarith

/-- **Uniform row sampling without replacement at the coherence**: with $L$ the coherence of
$\mathbf{U}$ the domination always holds, and the sketch is a subspace embedding with constants
$1 \mp \varepsilon$ outside probability
$2 \operatorname{rank}\mathbf{U} \cdot e^{-\varepsilon^2 k / (3 \operatorname{coh}\mathbf{U})}$,
for $0 \le \varepsilon \le 1$. [MartinssonTropp2020, §9.6.2] (with replacement); [Tropp2011a]. -/
theorem hasSubspaceEmbedding_coherence_of_hasLaw_samplingSketchWithoutReplacement
    (hS : HasLaw S (samplingSketchWithoutReplacement k n) μ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε)
      (2 * U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * coherence U))) μ :=
  hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement hS
    (leverageScore_le_coherence_mul_inv U) hε hε1

/-! ### Sample sizes -/

/-- **Row sampling without replacement, sample-size form**: row sampling without
replacement under the domination $\ell_i(\mathbf{U}) \le L / \lvert n \rvert$ is a subspace
embedding for $\operatorname{range}\mathbf{U}$ with constants $1 \mp \varepsilon$ and failure
probability $\delta$, for $0 < \varepsilon \le 1$, $\delta > 0$
and <!-- value samplingEmbeddingDim \operatorname{rank}\mathbf{U} L \varepsilon \delta -->
$\lvert k \rvert \ge 3 L \log(2\operatorname{rank}\mathbf{U}/\delta)/\varepsilon^2$ samples
(`NLAlib.samplingEmbeddingDim U.rank L ε δ`), the size of sampling with replacement.
[Tropp2011a]. Asymptotic form:
`NLAlib.exists_forall_hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement`.
Result: sampling-without-replacement-ose -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement_of_samplingEmbeddingDim_le
    (hS : HasLaw S (samplingSketchWithoutReplacement k n) μ)
    (hdom : ∀ i, leverageScore U i ≤ L * (Fintype.card n : ℝ)⁻¹) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hk : samplingEmbeddingDim U.rank L ε δ ≤ Fintype.card k) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε) δ μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  refine (hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement hS hdom hε.le
    hε1).mono le_rfl le_rfl ?_
  rcases Nat.eq_zero_or_pos U.rank with hd | hd
  · rw [hd, Nat.cast_zero, mul_zero, zero_mul]
    exact hδ.le
  exact two_mul_mul_exp_le_of_samplingEmbeddingDim_le (pos_of_leverageScore_le_mul_inv_card hdom hd)
    hε
    hδ hk

/-- **Row sampling without replacement, asymptotic form**: with
$d = \operatorname{rank}\mathbf{U}$, $O(L \log(d/\delta)/\varepsilon^2)$ samples suffice for row
sampling without replacement under the domination $\ell_i(\mathbf{U}) \le L / \lvert n \rvert$ to
be a subspace embedding for $\operatorname{range}\mathbf{U}$ with constants $1 \mp \varepsilon$
and failure probability $\delta$, for $\varepsilon$ and $\delta$ below absolute constants; the
constants come before every dimension and before $L$ (the coherence parameter), which stays in the
threshold. Proved from
`NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement_of_samplingEmbeddingDim_le`
with $C = 6$, $\varepsilon_0 = 1$ and $\delta \le 1/2$.
Asymptotic:
NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement_of_samplingEmbeddingDim_le -/
theorem exists_forall_hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 k n r : Type} [MeasurableSpace Ω] [RCLike 𝕜]
      [Fintype k] [Fintype n] [Fintype r] [DecidableEq n] (μ : Measure Ω) (S : Ω → Matrix k n 𝕜)
      (U : Matrix n r 𝕜) (L ε δ : ℝ),
      HasLaw S (samplingSketchWithoutReplacement k n) μ →
      (∀ i, leverageScore U i ≤ L * (Fintype.card n : ℝ)⁻¹) →
      0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (L * Real.log (U.rank / δ) / ε ^ 2) ≤ Fintype.card k →
      HasSubspaceEmbedding S U (1 - ε) (1 + ε) δ μ := by
  refine ⟨6, 1, by norm_num, one_pos, ?_⟩
  intro Ω 𝕜 k n r _ _ _ _ _ _ μ S U L ε δ hS hdom hε hε1 hδ hδ2 hk
  refine hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement_of_samplingEmbeddingDim_le
    hS
    hdom hε hε1 hδ ((samplingEmbeddingDim_le _ L ε δ).trans (le_trans ?_ hk))
  rcases Nat.eq_zero_or_pos U.rank with hd | hd
  · simp [hd]
  have hL : 0 < L := pos_of_leverageScore_le_mul_inv_card hdom hd
  have hl2 : Real.log (2 * U.rank / δ) ≤ 2 * Real.log (U.rank / δ) := by
    have h2 : Real.log 2 ≤ Real.log (U.rank / δ) :=
      Real.log_le_log (by norm_num) (by
        rw [le_div_iff₀ hδ]; nlinarith [(Nat.one_le_cast (α := ℝ)).2 hd])
    rw [mul_div_assoc, Real.log_mul (by norm_num) (by positivity)]
    linarith
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right
    (by nlinarith [mul_le_mul_of_nonneg_left hl2 hL.le]) (sq_nonneg ε)

/-- **The lower half without replacement, sample-size form**: row sampling without
replacement under the domination $\ell_i(\mathbf{U}) \le L / \lvert n \rvert$ is a subspace
injection for $\operatorname{range}\mathbf{U}$ with constant $1 - \varepsilon$ and failure
probability $\delta$, for $\varepsilon > 0$, $\delta > 0$
and <!-- value samplingInjectionDim \operatorname{rank}\mathbf{U} L \varepsilon \delta -->
$\lvert k \rvert \ge 2 L \log(\operatorname{rank}\mathbf{U}/\delta)/\varepsilon^2$ samples
(`NLAlib.samplingInjectionDim U.rank L ε δ`). Asymptotic form:
`NLAlib.exists_forall_hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement`.
Result: sampling-without-replacement-osi -/
theorem hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement_of_samplingInjectionDim_le
    (hS : HasLaw S (samplingSketchWithoutReplacement k n) μ)
    (hdom : ∀ i, leverageScore U i ≤ L * (Fintype.card n : ℝ)⁻¹) (hε : 0 < ε) (hδ : 0 < δ)
    (hk : samplingInjectionDim U.rank L ε δ ≤ Fintype.card k) :
    HasSubspaceInjection S U (1 - ε) δ μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  refine (hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement hS hdom hε.le).mono
    le_rfl ?_
  rcases Nat.eq_zero_or_pos U.rank with hd | hd
  · rw [hd, Nat.cast_zero, zero_mul]
    exact hδ.le
  exact mul_exp_le_of_samplingInjectionDim_le (pos_of_leverageScore_le_mul_inv_card hdom hd) hε
    hδ hk

/-- **The lower half without replacement, asymptotic form**: with
$d = \operatorname{rank}\mathbf{U}$, $O(L \log(d/\delta)/\varepsilon^2)$ samples suffice for row
sampling without replacement under the domination $\ell_i(\mathbf{U}) \le L / \lvert n \rvert$ to
be a subspace injection for $\operatorname{range}\mathbf{U}$ with constant $1 - \varepsilon$ and
failure probability $\delta$, for $\varepsilon$ below an absolute constant; the constants come
before every dimension and before $L$, which stays in the threshold. Proved from
`NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement_of_samplingInjectionDim_le`
with $C = 2$ and $\varepsilon_0 = 1$.
Asymptotic:
NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement_of_samplingInjectionDim_le
-/
theorem exists_forall_hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 k n r : Type} [MeasurableSpace Ω] [RCLike 𝕜]
      [Fintype k] [Fintype n] [Fintype r] [DecidableEq n] (μ : Measure Ω) (S : Ω → Matrix k n 𝕜)
      (U : Matrix n r 𝕜) (L ε δ : ℝ),
      HasLaw S (samplingSketchWithoutReplacement k n) μ →
      (∀ i, leverageScore U i ≤ L * (Fintype.card n : ℝ)⁻¹) →
      0 < ε → ε ≤ ε₀ → 0 < δ → C * (L * Real.log (U.rank / δ) / ε ^ 2) ≤ Fintype.card k →
      HasSubspaceInjection S U (1 - ε) δ μ := by
  refine ⟨2, 1, by norm_num, one_pos, ?_⟩
  intro Ω 𝕜 k n r _ _ _ _ _ _ μ S U L ε δ hS hdom hε _ hδ hk
  refine hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement_of_samplingInjectionDim_le
    hS hdom hε hδ ((samplingInjectionDim_le _ L ε δ).trans (le_of_eq_of_le ?_ hk))
  ring

end NLAlib
