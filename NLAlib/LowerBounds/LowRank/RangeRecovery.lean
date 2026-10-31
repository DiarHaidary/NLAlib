/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.QueryModel.DeferredDecision
public import NLAlib.LowerBounds.QueryModel.Yao
public import NLAlib.RandomMatrix.Gaussian.Rank

/-!
# Exact range recovery needs as many queries as the rank

For $\mathbf{A} = \mathbf{X}\mathbf{X}^{\mathsf{H}}$ with $\mathbf{X}$ a standard Gaussian
$d \times k$ matrix, an algorithm that makes fewer than $k$ adaptive products with $\mathbf{A}$
outputs, with probability one, a matrix whose range does not contain the range of $\mathbf{A}$,
unless that output has full rank $d$. In particular no algorithm with fewer than $k$ queries
outputs a rank-$k$ projector $\mathbf{P}$ with $\mathbf{A}(\mathbf{I} - \mathbf{P}) = \mathbf{0}$
with positive probability, for any $k < d$. This is the first end-to-end theorem of the query
model: Yao's principle, the Gram simulation
and the adaptive Gaussian deferred decision. Since $\mathbf{A}$ is Hermitian, products with
$\mathbf{A}^{\mathsf{H}}$ are products with $\mathbf{A}$, so the bound counts all products.

## Main results

* `NLAlib.QueryAlgorithm.IsMeasurable.measure_queryAt_notMem_span_and_mulVec_mem_span_eq_zero`:
  one query at a time, a new direction is almost surely not collapsed by $\mathbf{X}^{\mathsf{H}}$.
* `NLAlib.QueryAlgorithm.IsMeasurable.ae_rank_conjTranspose_mul_leftQueryMatrix_gramSimulation`:
  the left responses of the Gram simulation are in general position.
* `NLAlib.QueryAlgorithm.IsMeasurable.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix`:
  deterministic algorithms; the theorem of the same name in the namespace
  `NLAlib.QueryAlgorithm.IsMeasurableFamily` is the randomized form (`Result:` id
  range-recovery-k-queries).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

namespace QueryAlgorithm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {d k : Type*} [Fintype d]
  [Fintype k] {q : ℕ}

/-- Two families span the same space when each member of one is zero or a member of the
other, and each member of the other is a member of the first. -/
private theorem span_range_eq_of_forall {V ι ι' : Type*} [AddCommGroup V] [Module ℝ V]
    (f : ι → V) (a : ι' → V) (h₁ : ∀ j, f j = 0 ∨ ∃ l, f j = a l) (h₂ : ∀ l, ∃ j, f j = a l) :
    Submodule.span ℝ (Set.range f) = Submodule.span ℝ (Set.range a) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨j, rfl⟩
    rcases h₁ j with h | ⟨l, h⟩
    · rw [h]
      exact zero_mem _
    · rw [h]
      exact Submodule.subset_span ⟨l, rfl⟩
  · rintro _ ⟨l, rfl⟩
    obtain ⟨j, h⟩ := h₂ l
    rw [← h]
    exact Submodule.subset_span ⟨j, rfl⟩

/-- Every query of the Gram simulation is a left query $(\mathbf{0}, \mathbf{x}_l)$ or a right
query $(\mathbf{Y}^{\mathsf{H}}\mathbf{x}_l, \mathbf{0})$. -/
private theorem queries_transcript_gramSimulation {β : Type*}
    (alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β) (Y : Matrix d k ℝ) (j : Fin (2 * q)) :
    ∃ l : Fin q, (alg.gramSimulation k).queries
        ((alg.gramSimulation k).transcript (twoSidedMulVec Y)) j =
      (0, alg.queryAt (Y * Yᴴ).mulVec l) ∨
    (alg.gramSimulation k).queries ((alg.gramSimulation k).transcript (twoSidedMulVec Y)) j =
      (Yᴴ *ᵥ alg.queryAt (Y * Yᴴ).mulVec l, 0) := by
  rw [← queryAt_eq_queries_transcript]
  obtain ⟨l, hl | hl⟩ := Nat.even_or_odd' (j : ℕ)
  · exact ⟨⟨l, by omega⟩, Or.inl (by rw [hl, queryAt_gramSimulation_two_mul])⟩
  · exact ⟨⟨l, by omega⟩, Or.inr (by rw [hl, queryAt_gramSimulation_two_mul_add_one])⟩

/-- The left query span of the Gram simulation is the span of the queries $\mathbf{x}_l$. -/
private theorem range_leftQueryMatrix_gramSimulation {β : Type*}
    (alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β) (Y : Matrix d k ℝ) :
    LinearMap.range ((alg.gramSimulation k).leftQueryMatrix
        ((alg.gramSimulation k).transcript (twoSidedMulVec Y))).mulVecLin =
      Submodule.span ℝ (Set.range fun l : Fin q => alg.queryAt (Y * Yᴴ).mulVec l) := by
  rw [Matrix.range_mulVecLin]
  refine span_range_eq_of_forall _ _ (fun j => ?_) (fun l => ⟨⟨2 * l, by omega⟩, ?_⟩)
  · obtain ⟨l, h | h⟩ := queries_transcript_gramSimulation alg Y j
    · exact Or.inr ⟨l, funext fun r => by simp [Matrix.col, leftQueryMatrix, h]⟩
    · exact Or.inl (funext fun r => by simp [Matrix.col, leftQueryMatrix, h])
  · funext r
    simp [Matrix.col, leftQueryMatrix, ← queryAt_eq_queries_transcript,
      queryAt_gramSimulation_two_mul]

/-- The right query span of the Gram simulation is the span of the
$\mathbf{Y}^{\mathsf{H}}\mathbf{x}_l$. -/
private theorem range_rightQueryMatrix_gramSimulation {β : Type*}
    (alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β) (Y : Matrix d k ℝ) :
    LinearMap.range ((alg.gramSimulation k).rightQueryMatrix
        ((alg.gramSimulation k).transcript (twoSidedMulVec Y))).mulVecLin =
      Submodule.span ℝ (Set.range fun l : Fin q => Yᴴ *ᵥ alg.queryAt (Y * Yᴴ).mulVec l) := by
  rw [Matrix.range_mulVecLin]
  refine span_range_eq_of_forall _ _ (fun j => ?_) (fun l => ⟨⟨2 * l + 1, by omega⟩, ?_⟩)
  · obtain ⟨l, h | h⟩ := queries_transcript_gramSimulation alg Y j
    · exact Or.inl (funext fun r => by simp [Matrix.col, rightQueryMatrix, h])
    · exact Or.inr ⟨l, funext fun r => by simp [Matrix.col, rightQueryMatrix, h]⟩
  · funext r
    simp [Matrix.col, rightQueryMatrix, ← queryAt_eq_queries_transcript,
      queryAt_gramSimulation_two_mul_add_one]

/-- The next query $\mathbf{x}_q$ as a function of the Gram simulation transcript. -/
private theorem queryAt_eq_query_transcript_gramSimulation {β : Type*}
    (alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β) (Y : Matrix d k ℝ) :
    alg.queryAt (Y * Yᴴ).mulVec q = alg.query q fun l : Fin q =>
      ((alg.gramSimulation k).transcript (twoSidedMulVec Y) ⟨2 * l + 1, by omega⟩).1 := by
  rw [queryAt, ← gramDecode_history_gramSimulation]
  rfl

/-- The bad event of one step, in terms of the complement projectors of the query spans. -/
private theorem notMem_span_and_mem_span_iff [DecidableEq d] [DecidableEq k] {β : Type*}
    (alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β) (Y : Matrix d k ℝ) :
    (alg.queryAt (Y * Yᴴ).mulVec q ∉
        Submodule.span ℝ (Set.range fun l : Fin q => alg.queryAt (Y * Yᴴ).mulVec l) ∧
      Yᴴ *ᵥ alg.queryAt (Y * Yᴴ).mulVec q ∈
        Submodule.span ℝ (Set.range fun l : Fin q => Yᴴ *ᵥ alg.queryAt (Y * Yᴴ).mulVec l)) ↔
    ((1 - rangeProjector ((alg.gramSimulation k).leftQueryMatrix
          ((alg.gramSimulation k).transcript (twoSidedMulVec Y)))) *ᵥ
        alg.queryAt (Y * Yᴴ).mulVec q ≠ 0 ∧
      (1 - rangeProjector ((alg.gramSimulation k).rightQueryMatrix
          ((alg.gramSimulation k).transcript (twoSidedMulVec Y)))) *ᵥ
        (Yᴴ *ᵥ alg.queryAt (Y * Yᴴ).mulVec q) = 0) := by
  rw [← range_leftQueryMatrix_gramSimulation, ← range_rightQueryMatrix_gramSimulation,
    ← rangeProjector_mulVec_eq_self_iff, ← rangeProjector_mulVec_eq_self_iff, Matrix.sub_mulVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, sub_ne_zero, sub_eq_zero, ne_comm,
    eq_comm (a := Yᴴ *ᵥ _)]

/-- After resampling, the unrevealed part of $\mathbf{Y}^{\mathsf{H}}\mathbf{x}$ comes from
$\mathbf{Y}'$ only. -/
private theorem mulVec_conjTranspose_resample_gramSimulation [DecidableEq d] [DecidableEq k]
    {β : Type*} (alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β) (Y Y' : Matrix d k ℝ) (x : d → ℝ) :
    (1 - rangeProjector ((alg.gramSimulation k).rightQueryMatrix
          ((alg.gramSimulation k).transcript (twoSidedMulVec Y)))) *ᵥ
        (((alg.gramSimulation k).resample Y Y')ᴴ *ᵥ x) =
      (1 - rangeProjector ((alg.gramSimulation k).rightQueryMatrix
          ((alg.gramSimulation k).transcript (twoSidedMulVec Y)))) *ᵥ (Y'ᴴ *ᵥ
        ((1 - rangeProjector ((alg.gramSimulation k).leftQueryMatrix
          ((alg.gramSimulation k).transcript (twoSidedMulVec Y)))) *ᵥ x)) := by
  set U := (alg.gramSimulation k).leftQueryMatrix
    ((alg.gramSimulation k).transcript (twoSidedMulVec Y)) with hU
  set W := (alg.gramSimulation k).rightQueryMatrix
    ((alg.gramSimulation k).transcript (twoSidedMulVec Y)) with hW
  have h0 : ∀ v, (1 - rangeProjector W) *ᵥ (Yᴴ *ᵥ (rangeProjector U *ᵥ v)) = 0 := by
    intro v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero, eq_comm,
      rangeProjector_mulVec_eq_self_iff, hW, range_rightQueryMatrix_gramSimulation]
    have hv : rangeProjector U *ᵥ v ∈ LinearMap.range U.mulVecLin :=
      (range_rangeProjector U).le ⟨v, rfl⟩
    rw [hU, range_leftQueryMatrix_gramSimulation] at hv
    have := Submodule.mem_map_of_mem (f := Yᴴ.mulVecLin) hv
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this
  have hE : (1 - rangeProjector U)ᴴ = 1 - rangeProjector U := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, conjTranspose_rangeProjector]
  have hF : (1 - rangeProjector W)ᴴ = 1 - rangeProjector W := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, conjTranspose_rangeProjector]
  have hFF : (1 - rangeProjector W) * (1 - rangeProjector W) = 1 - rangeProjector W := by
    simp [Matrix.sub_mul, Matrix.mul_sub]
  have key : (1 - rangeProjector W) * ((alg.gramSimulation k).resample Y Y')ᴴ =
      (1 - rangeProjector W) * Yᴴ * rangeProjector U +
        (1 - rangeProjector W) * Y'ᴴ * (1 - rangeProjector U) := by
    simp only [resample, ← hU, ← hW, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, hE, hF]
    rw [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc _ _ (Yᴴ * _),
      ← Matrix.mul_assoc _ _ (Y'ᴴ * _), hFF]
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [Matrix.mulVec_mulVec, key, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    h0, zero_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

omit [Fintype d] in
/-- With `q < card k` the right query span of the Gram simulation is a proper subspace. -/
private theorem one_sub_rangeProjector_rightQueryMatrix_gramSimulation_ne_zero [DecidableEq k]
    {β : Type*} (alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β) (hq : q < Fintype.card k)
    (τ : Fin (2 * q) → (d → ℝ) × (k → ℝ)) :
    1 - rangeProjector ((alg.gramSimulation k).rightQueryMatrix τ) ≠ 0 := by
  intro h
  have h1 := rank_rangeProjector ((alg.gramSimulation k).rightQueryMatrix τ)
  rw [← sub_eq_zero.1 h, Matrix.rank_one] at h1
  have := rank_rightQueryMatrix_gramSimulation_le alg τ
  omega

/-- For fixed $\mathbf{v} \ne \mathbf{0}$ and $\mathbf{F} \ne \mathbf{0}$, a Gaussian
$\mathbf{X}'$ has $\mathbf{F}\mathbf{X}'^{\mathsf{H}}\mathbf{v} = \mathbf{0}$ with probability
zero. -/
private theorem measure_ne_zero_and_mulVec_conjTranspose_mulVec_eq_zero {X' : Ω → Matrix d k ℝ}
    (hX' : HasLaw X' (gaussianMatrix d k) μ) {F : Matrix k k ℝ} (hF : F ≠ 0) (v : d → ℝ) :
    μ {ω | v ≠ 0 ∧ F *ᵥ ((X' ω)ᴴ *ᵥ v) = 0} = 0 := by
  rcases eq_or_ne v 0 with hv | hv
  · exact measure_mono_null (fun ω hω => absurd hv hω.1) measure_empty
  refine measure_mono_null (fun ω hω => ?_) (measure_mul_mul_eq_eq_zero_of_hasLaw_gaussianMatrix
    hX' (N := Matrix.replicateRow (Fin 1) v) (F := Fᵀ) ?_ (Matrix.transpose_eq_zero.not.2 hF) 0)
  · have h : Matrix.replicateRow (Fin 1) v * X' ω * Fᵀ =
        (Matrix.replicateCol (Fin 1) (F *ᵥ ((X' ω)ᴴ *ᵥ v)))ᵀ := by
      rw [Matrix.replicateCol_mulVec, Matrix.replicateCol_mulVec, Matrix.transpose_mul,
        Matrix.transpose_mul, Matrix.transpose_replicateCol,
        Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
        Matrix.mul_assoc]
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [h, hω.2]
    rfl
  · rw [← Matrix.transpose_replicateCol, Ne, Matrix.transpose_eq_zero, Matrix.replicateCol_eq_zero]
    exact hv

/-- **One step of general position**: for a measurable algorithm making adaptive queries
$\mathbf{x}_0, \mathbf{x}_1, \dots$ to $\mathbf{X}\mathbf{X}^{\mathsf{H}}$, with $\mathbf{X}$ a
standard Gaussian $d \times k$ matrix, and $i < q$, $i < k$: almost surely, either
$\mathbf{x}_i$ lies in the span of $\mathbf{x}_0, \dots, \mathbf{x}_{i-1}$, or
$\mathbf{X}^{\mathsf{H}}\mathbf{x}_i$ does not lie in the span of
$\mathbf{X}^{\mathsf{H}}\mathbf{x}_0, \dots, \mathbf{X}^{\mathsf{H}}\mathbf{x}_{i-1}$.
[ZhangEtAl2026, proof of Lemma 4.2]; there inside the block decomposition of Lemma 4.1. -/
theorem IsMeasurable.measure_queryAt_notMem_span_and_mulVec_mem_span_eq_zero {β : Type*}
    [MeasurableSpace β] {alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β} (halg : alg.IsMeasurable)
    {X : Ω → Matrix d k ℝ} (hX : HasLaw X (gaussianMatrix d k) μ) {i : ℕ} (hi : i < q)
    (hik : i < Fintype.card k) :
    μ {ω | alg.queryAt (X ω * (X ω)ᴴ).mulVec i ∉
        Submodule.span ℝ (Set.range fun l : Fin i => alg.queryAt (X ω * (X ω)ᴴ).mulVec l) ∧
      (X ω)ᴴ *ᵥ alg.queryAt (X ω * (X ω)ᴴ).mulVec i ∈
        Submodule.span ℝ
          (Set.range fun l : Fin i => (X ω)ᴴ *ᵥ alg.queryAt (X ω * (X ω)ᴴ).mulVec l)} = 0 := by
  classical
  have := hX.isProbabilityMeasure
  set T := (alg.truncate i).gramSimulation k
  have hT : T.IsMeasurable := (halg.truncate hi.le).gramSimulation
  -- the transcript, the query `x_i` and the two projectors, as functions of the transcript
  set τ : Matrix d k ℝ → Fin (2 * i) → (d → ℝ) × (k → ℝ) :=
    fun Y => T.transcript (twoSidedMulVec Y)
  set x : (Fin (2 * i) → (d → ℝ) × (k → ℝ)) → d → ℝ :=
    fun t => alg.query i fun l : Fin i => (t ⟨2 * l + 1, by omega⟩).1
  set E := fun t : Fin (2 * i) → (d → ℝ) × (k → ℝ) => 1 - rangeProjector (T.leftQueryMatrix t)
  set F := fun t : Fin (2 * i) → (d → ℝ) × (k → ℝ) => 1 - rangeProjector (T.rightQueryMatrix t)
  have hτ : Measurable τ := hT.measurable_transcript
    (Measurable.twoSidedMulVec measurable_fst measurable_snd)
  have hx : Measurable x := (halg.measurable_query i hi).comp
    (measurable_pi_lambda _ fun l => measurable_fst.comp (measurable_pi_apply _))
  have hE : Measurable E :=
    measurable_const.sub (measurable_rangeProjector.comp hT.measurable_leftQueryMatrix)
  have hF : Measurable F :=
    measurable_const.sub (measurable_rangeProjector.comp hT.measurable_rightQueryMatrix)
  set B := {p : (Fin (2 * i) → (d → ℝ) × (k → ℝ)) × Matrix d k ℝ |
    E p.1 *ᵥ x p.1 ≠ 0 ∧ F p.1 *ᵥ ((p.2)ᴴ *ᵥ x p.1) = 0}
  have hstar : Measurable fun Y : Matrix d k ℝ => Yᴴ :=
    Measurable.matrix_conjTranspose continuous_star.measurable measurable_id
  have hB : MeasurableSet B :=
    ((hE.comp measurable_fst).matrix_mulVec (hx.comp measurable_fst)
      (measurableSet_singleton 0).compl).inter ((hF.comp measurable_fst).matrix_mulVec
        ((hstar.comp measurable_snd).matrix_mulVec (hx.comp measurable_fst))
        (measurableSet_singleton 0))
  have hB' : MeasurableSet {Y | (τ Y, Y) ∈ B} := (hτ.prodMk measurable_id) hB
  have hev : {ω | alg.queryAt (X ω * (X ω)ᴴ).mulVec i ∉
        Submodule.span ℝ (Set.range fun l : Fin i => alg.queryAt (X ω * (X ω)ᴴ).mulVec l) ∧
      (X ω)ᴴ *ᵥ alg.queryAt (X ω * (X ω)ᴴ).mulVec i ∈ Submodule.span ℝ
        (Set.range fun l : Fin i => (X ω)ᴴ *ᵥ alg.queryAt (X ω * (X ω)ᴴ).mulVec l)} =
      X ⁻¹' {Y | (τ Y, Y) ∈ B} := by
    ext ω
    have h := notMem_span_and_mem_span_iff (alg.truncate i) (X ω)
    have hxi : x (τ (X ω)) = alg.queryAt (X ω * (X ω)ᴴ).mulVec i :=
      (queryAt_eq_query_transcript_gramSimulation (alg.truncate i) (X ω)).symm.trans (by
        rw [queryAt, queryAt, history_truncate]; rfl)
    simp only [queryAt, history_truncate] at h
    change _ ↔ E (τ (X ω)) *ᵥ x (τ (X ω)) ≠ 0 ∧ F (τ (X ω)) *ᵥ ((X ω)ᴴ *ᵥ x (τ (X ω))) = 0
    rwa [hxi]
  -- extend by an independent Gaussian matrix
  set μ' := μ.prod (gaussianMatrix d k)
  have hX₁ : HasLaw (fun p : Ω × Matrix d k ℝ => X p.1) (gaussianMatrix d k) μ' :=
    hX.comp measurePreserving_fst.hasLaw
  have hX₂ : HasLaw Prod.snd (gaussianMatrix d k) μ' := measurePreserving_snd.hasLaw
  have hind : IndepFun (fun p : Ω × Matrix d k ℝ => X p.1) Prod.snd μ' :=
    indepFun_prod₀ hX.aemeasurable aemeasurable_id
  have hid := hT.identDistrib_resample_of_hasLaw_gaussianMatrix hX₁ hX₂ hind
  set S := {p : Matrix d k ℝ × (Fin (2 * i) → (d → ℝ) × (k → ℝ)) |
    E p.2 *ᵥ x p.2 ≠ 0 ∧ F p.2 *ᵥ ((p.1)ᴴ *ᵥ (E p.2 *ᵥ x p.2)) = 0}
  have hEx := (hE.comp (measurable_snd (α := Matrix d k ℝ))).matrix_mulVec (hx.comp measurable_snd)
  have hS : MeasurableSet S := (hEx (measurableSet_singleton 0).compl).inter
    ((hF.comp measurable_snd).matrix_mulVec ((hstar.comp measurable_fst).matrix_mulVec hEx)
      (measurableSet_singleton 0))
  have hsec := (hind.symm.comp measurable_id hτ).measureReal_mem_le_add hX₂.aemeasurable
    (hτ.comp_aemeasurable hX₁.aemeasurable) hS MeasurableSet.univ le_rfl
    (fun t _ => ?_) (δ₂ := 0) (by simp)
  · have hres : (fun p : Ω × Matrix d k ℝ => (T.transcript (twoSidedMulVec (X p.1)),
        T.resample (X p.1) p.2)) ⁻¹' B = {p | (p.2, τ (X p.1)) ∈ S} := by
      ext p
      exact and_congr_right fun _ => iff_of_eq (congrArg (· = 0)
        (mulVec_conjTranspose_resample_gramSimulation (alg.truncate i) _ _ _))
    rw [hev, ← Measure.map_apply_of_aemeasurable hX.aemeasurable hB', hX.map_eq, ← hX₁.map_eq,
      Measure.map_apply_of_aemeasurable hX₁.aemeasurable hB']
    change μ' ((fun p : Ω × Matrix d k ℝ => (T.transcript (twoSidedMulVec (X p.1)), X p.1)) ⁻¹'
      B) = 0
    rw [hid.measure_mem_eq hB, hres]
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1
      (le_antisymm (hsec.trans_eq (add_zero 0)) measureReal_nonneg)
  · exact ((measureReal_eq_zero_iff (measure_ne_top _ _)).2
      (measure_ne_zero_and_mulVec_conjTranspose_mulVec_eq_zero hX₂
        (one_sub_rangeProjector_rightQueryMatrix_gramSimulation_ne_zero (alg.truncate i) hik t)
        (E t *ᵥ x t))).le

/-- Matrices whose columns lie in each other's column spans have the same rank. -/
private lemma rank_eq_of_col_mem_span {m n p : Type*} [Fintype n] [Fintype p]
    {M : Matrix m n ℝ} {N : Matrix m p ℝ}
    (h₁ : ∀ j, M.col j ∈ Submodule.span ℝ (Set.range N.col))
    (h₂ : ∀ l, N.col l ∈ Submodule.span ℝ (Set.range M.col)) : M.rank = N.rank := by
  have hspan : Submodule.span ℝ (Set.range M.col) = Submodule.span ℝ (Set.range N.col) :=
    le_antisymm (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h₁ j))
      (Submodule.span_le.2 (by rintro _ ⟨l, rfl⟩; exact h₂ l))
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols, hspan]

/-- Columns of a product are the products of the columns. -/
private lemma col_mul_eq_mulVec_col {k d n : Type*} [Fintype d] (B : Matrix k d ℝ)
    (N : Matrix d n ℝ) (j : n) : (B * N).col j = B *ᵥ N.col j := by
  funext r
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]

/-- A product by a fixed matrix maps the column span into the column span of the product. -/
private lemma mulVec_mem_span_col_mul {k d n : Type*} [Fintype d] (B : Matrix k d ℝ)
    {U : Matrix d n ℝ} {v : d → ℝ} (hv : v ∈ Submodule.span ℝ (Set.range U.col)) :
    B *ᵥ v ∈ Submodule.span ℝ (Set.range (B * U).col) := by
  have hle : Submodule.span ℝ (Set.range U.col) ≤
      (Submodule.span ℝ (Set.range (B * U).col)).comap B.mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_comap.2 (Submodule.subset_span ⟨j, (col_mul_eq_mulVec_col B U j).symm⟩)
  exact Submodule.mem_comap.1 (hle hv)

/-- Algebraic core of `IsMeasurable.ae_rank_conjTranspose_mul_leftQueryMatrix_gramSimulation`:
if each query $\mathbf{x}_i$ ($i < q$) lies in the span of the earlier ones or has
$\mathbf{X}^{\mathsf{H}}\mathbf{x}_i$ outside the span of theirs, the left query matrix of the
Gram simulation is in general position. -/
private lemma rank_conjTranspose_mul_leftQueryMatrix_gramSimulation_of_good {β : Type*}
    {alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β} (Y : Matrix d k ℝ)
    (hgood : ∀ i < q,
      alg.queryAt (Y * Yᴴ).mulVec i ∈
          Submodule.span ℝ (Set.range fun l : Fin i => alg.queryAt (Y * Yᴴ).mulVec l) ∨
        Yᴴ *ᵥ alg.queryAt (Y * Yᴴ).mulVec i ∉
          Submodule.span ℝ (Set.range fun l : Fin i => Yᴴ *ᵥ alg.queryAt (Y * Yᴴ).mulVec l)) :
    (Yᴴ * (alg.gramSimulation k).leftQueryMatrix
        ((alg.gramSimulation k).transcript (twoSidedMulVec Y))).rank =
      ((alg.gramSimulation k).leftQueryMatrix
        ((alg.gramSimulation k).transcript (twoSidedMulVec Y))).rank := by
  set L := (alg.gramSimulation k).leftQueryMatrix
    ((alg.gramSimulation k).transcript (twoSidedMulVec Y)) with hL
  set U := (Matrix.of fun (r : d) (j : Fin q) => alg.queryAt (Y * Yᴴ).mulVec j r) with hU
  -- induction: the rank of `Yᴴ * U_i` is that of `U_i`, for the first `i ≤ q` queries
  have hind : ∀ i : ℕ, i ≤ q →
      (Yᴴ * Matrix.of fun (r : d) (j : Fin i) => alg.queryAt (Y * Yᴴ).mulVec j r).rank =
        (Matrix.of fun (r : d) (j : Fin i) => alg.queryAt (Y * Yᴴ).mulVec j r).rank := by
    intro i
    induction i with
    | zero =>
      intro _
      have h1 := Matrix.rank_le_card_width
        (Yᴴ * Matrix.of fun (r : d) (j : Fin 0) => alg.queryAt (Y * Yᴴ).mulVec j r)
      have h2 := Matrix.rank_le_card_width
        (Matrix.of fun (r : d) (j : Fin 0) => alg.queryAt (Y * Yᴴ).mulVec j r)
      simp only [Fintype.card_fin] at h1 h2
      omega
    | succ i ih =>
      intro hi
      have hsnoc : (Matrix.of fun (r : d) (j : Fin (i + 1)) => alg.queryAt (Y * Yᴴ).mulVec j r) =
          Matrix.of fun r => Fin.snoc (α := fun _ => ℝ)
            ((Matrix.of fun (r : d) (j : Fin i) => alg.queryAt (Y * Yᴴ).mulVec j r) r)
            (alg.queryAt (Y * Yᴴ).mulVec i r) := by
        ext r j
        refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
      rw [hsnoc]
      exact Matrix.rank_mul_of_snoc_eq_rank_of_snoc Yᴴ _ (fun r => alg.queryAt (Y * Yᴴ).mulVec i r)
        (ih (by omega)) (hgood i (by omega))
  -- the even columns of `L` are the queries, the odd ones are zero
  have hEven : ∀ (j : Fin (2 * q)) (i : ℕ) (hi : i < q), (j : ℕ) = 2 * i →
      L.col j = alg.queryAt (Y * Yᴴ).mulVec i := by
    rintro ⟨j, hj⟩ i hi hji
    simp only at hji
    subst hji
    funext r
    change ((alg.gramSimulation k).queries _ ⟨2 * i, hj⟩).2 r = _
    rw [← QueryAlgorithm.queryAt_eq_queries_transcript, queryAt_gramSimulation_two_mul]
  have hOdd : ∀ (j : Fin (2 * q)), (j : ℕ) % 2 = 1 → L.col j = 0 := by
    rintro ⟨j, hj⟩ hodd
    funext r
    simp [hL, Matrix.col, QueryAlgorithm.leftQueryMatrix, QueryAlgorithm.queries,
      QueryAlgorithm.gramSimulation, hodd]
  have hLmem : ∀ j : Fin (2 * q), L.col j ∈ Submodule.span ℝ (Set.range U.col) := by
    intro j
    have := j.isLt
    by_cases hj : (j : ℕ) % 2 = 0
    · have hi : (j : ℕ) / 2 < q := by omega
      rw [hEven j _ hi (by omega)]
      exact Submodule.subset_span ⟨⟨(j : ℕ) / 2, hi⟩, rfl⟩
    · rw [hOdd j (by omega)]
      exact Submodule.zero_mem _
  have hULmem : ∀ l : Fin q, U.col l ∈ Submodule.span ℝ (Set.range L.col) := by
    intro l
    have h2l : 2 * (l : ℕ) < 2 * q := by have := l.isLt; omega
    have hc : U.col l = L.col ⟨2 * l, h2l⟩ := (hEven ⟨2 * l, h2l⟩ l l.isLt rfl).symm
    rw [hc]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hA : (Yᴴ * L).rank = (Yᴴ * U).rank :=
    rank_eq_of_col_mem_span
      (fun j => by rw [col_mul_eq_mulVec_col]; exact mulVec_mem_span_col_mul Yᴴ (hLmem j))
      (fun l => by rw [col_mul_eq_mulVec_col]; exact mulVec_mem_span_col_mul Yᴴ (hULmem l))
  have hB : L.rank = U.rank := rank_eq_of_col_mem_span hLmem hULmem
  exact hA.trans ((hind q le_rfl).trans hB.symm)

/-- **The left queries of the Gram simulation are in general position**: for a measurable
algorithm making $q \le k$ queries to $\mathbf{X}\mathbf{X}^{\mathsf{H}}$, with $\mathbf{X}$ a
standard Gaussian $d \times k$ matrix, let $\mathbf{U}$ be the $d \times 2q$ left query matrix of
its Gram simulation (columns $\mathbf{x}_i$ and zeros). Almost surely
$\operatorname{rank}(\mathbf{X}^{\mathsf{H}}\mathbf{U}) = \operatorname{rank}\mathbf{U}$: no
nonzero combination of the queries is annihilated by $\mathbf{X}^{\mathsf{H}}$.
[ZhangEtAl2026, proof of Lemma 4.2]; there inside the block decomposition of Lemma 4.1. -/
theorem IsMeasurable.ae_rank_conjTranspose_mul_leftQueryMatrix_gramSimulation
    {β : Type*} [MeasurableSpace β] {alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β}
    (halg : alg.IsMeasurable) {X : Ω → Matrix d k ℝ} (hX : HasLaw X (gaussianMatrix d k) μ)
    (hq : q ≤ Fintype.card k) :
    ∀ᵐ ω ∂μ, ((X ω)ᴴ * (alg.gramSimulation k).leftQueryMatrix
        ((alg.gramSimulation k).transcript (twoSidedMulVec (X ω)))).rank =
      ((alg.gramSimulation k).leftQueryMatrix
        ((alg.gramSimulation k).transcript (twoSidedMulVec (X ω)))).rank := by
  have hbad : ∀ᵐ ω ∂μ, ∀ i < q,
      alg.queryAt (X ω * (X ω)ᴴ).mulVec i ∈
          Submodule.span ℝ (Set.range fun l : Fin i => alg.queryAt (X ω * (X ω)ᴴ).mulVec l) ∨
        (X ω)ᴴ *ᵥ alg.queryAt (X ω * (X ω)ᴴ).mulVec i ∉
          Submodule.span ℝ
            (Set.range fun l : Fin i => (X ω)ᴴ *ᵥ alg.queryAt (X ω * (X ω)ᴴ).mulVec l) := by
    refine ae_all_iff.2 fun i => ?_
    by_cases hi : i < q
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1
        (IsMeasurable.measure_queryAt_notMem_span_and_mulVec_mem_span_eq_zero halg hX hi
          (lt_of_lt_of_le hi hq))] with ω hω
      intro _
      simpa only [Set.mem_ofPred_eq, not_and_or, not_not] using hω
    · exact ae_of_all _ fun ω h => absurd h hi
  filter_upwards [hbad] with ω hω
  exact rank_conjTranspose_mul_leftQueryMatrix_gramSimulation_of_good (X ω) hω

/-- A left factor that preserves the rank of $\mathbf{U}$ is injective on its range:
$\mathbf{B}\mathbf{U}\mathbf{C} = \mathbf{0}$ forces $\mathbf{U}\mathbf{C} = \mathbf{0}$. -/
private theorem mul_eq_zero_of_rank_mul_eq {m r s : Type*} [Fintype r]
    {B : Matrix m d ℝ} {U : Matrix d r ℝ} (hU : (B * U).rank = U.rank) {C : Matrix r s ℝ}
    (h : B * U * C = 0) : U * C = 0 := by
  have hker : LinearMap.ker (B * U).mulVecLin = LinearMap.ker U.mulVecLin := by
    refine (Submodule.eq_of_le_of_finrank_eq (fun v hv => ?_) ?_).symm
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
      rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    · have h1 := LinearMap.finrank_range_add_finrank_ker (B * U).mulVecLin
      have h2 := LinearMap.finrank_range_add_finrank_ker U.mulVecLin
      rw [Matrix.rank, Matrix.rank] at hU
      omega
  ext i j
  have hc : (fun l => C l j) ∈ LinearMap.ker U.mulVecLin := by
    rw [← hker, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext a
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (congrFun h a) j
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hc i

/-- The fiber of the range event for a fixed $\mathbf{Y}$ in general position: with
$\mathbf{E} = \mathbf{I} - \mathbf{P}_{\mathbf{U}}$, $\mathbf{F} \ne \mathbf{0}$ and
$\mathbf{Z} = \mathbf{Y} - \mathbf{E}\mathbf{Y}\mathbf{F} + \mathbf{E}\mathbf{Y}'\mathbf{F}$,
a Gaussian $\mathbf{Y}'$ puts the range of $\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ inside the range
of a fixed $\mathbf{V}$ of rank below $d$ with probability zero. -/
private theorem measure_rangeProjector_mul_resample_eq_zero [DecidableEq d] {r : Type*}
    [Fintype r] {p : Type*} [Fintype p] {U : Matrix d r ℝ} {V : Matrix d p ℝ}
    {Y : Matrix d k ℝ} {F : Matrix k k ℝ} {Z : Matrix d k ℝ → Matrix d k ℝ}
    (hV : V.rank < Fintype.card d) (hF : F ≠ 0) (hU : (Yᴴ * U).rank = U.rank)
    (hZ : ∀ Y', Z Y' = Y - (1 - rangeProjector U) * Y * F + (1 - rangeProjector U) * Y' * F) :
    gaussianMatrix d k {Y' | rangeProjector V * (Z Y' * (Z Y')ᴴ) = Z Y' * (Z Y')ᴴ} = 0 := by
  set E := 1 - rangeProjector U with hE
  set N := 1 - rangeProjector V with hN_def
  have hN : N ≠ 0 := by
    intro h
    have := rank_one_sub_rangeProjector_add_rank V
    rw [← hN_def, h, Matrix.rank_zero] at this
    omega
  have hsub : {Y' | rangeProjector V * (Z Y' * (Z Y')ᴴ) = Z Y' * (Z Y')ᴴ} ⊆
      {Y' | N * E * Y' * F = -(N * (Y - E * Y * F))} := by
    intro Y' hY'
    have hNZZ : N * (Z Y' * (Z Y')ᴴ) = 0 := by
      rw [hN_def, one_sub_rangeProjector_mul, hY', sub_self]
    have h0 : N * Z Y' = 0 := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (by
      rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc N, hNZZ,
        Matrix.zero_mul, Matrix.trace_zero])
    rw [hZ, Matrix.mul_add] at h0
    rw [Set.mem_ofPred_eq, eq_neg_iff_add_eq_zero, add_comm, ← h0]
    simp only [Matrix.mul_assoc]
  by_cases hNE : N * E = 0
  · refine measure_mono_null (fun Y' hY' => ?_) measure_empty
    have hNY : N * Y = 0 := by
      have h := hsub hY'
      rw [Set.mem_ofPred_eq, hNE, Matrix.zero_mul, Matrix.zero_mul, Matrix.mul_sub,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, hNE, Matrix.zero_mul, Matrix.zero_mul, sub_zero,
        eq_comm, neg_eq_zero] at h
      exact h
    have hNP : N * rangeProjector U = N := by
      rw [hE, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hNE
      exact hNE.symm
    have hYU : Yᴴ * U * (pinv U * Nᴴ) = 0 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc U, mul_pinv, ← conjTranspose_rangeProjector,
        ← Matrix.conjTranspose_mul, hNP, ← Matrix.conjTranspose_mul, hNY,
        Matrix.conjTranspose_zero]
    have hUC := mul_eq_zero_of_rank_mul_eq hU hYU
    rw [← Matrix.mul_assoc, mul_pinv, ← conjTranspose_rangeProjector, ← Matrix.conjTranspose_mul,
      hNP, Matrix.conjTranspose_eq_zero] at hUC
    exact (hN hUC).elim
  · exact measure_mono_null hsub
      (measure_mul_mul_eq_eq_zero_of_hasLaw_gaussianMatrix HasLaw.id hNE hF _)

/-- **Exact range recovery needs $k$ queries, deterministic algorithms**: let $\mathbf{X}$ be a
standard Gaussian $d \times k$ matrix and $\mathbf{A} = \mathbf{X}\mathbf{X}^{\mathsf{H}}$. A
measurable deterministic algorithm making $q < k$ adaptive queries $\mathbf{x} \mapsto
\mathbf{A}\mathbf{x}$ and outputting $\mathbf{V} \in \mathbb{R}^{d \times p}$ satisfies
$$\mathbb{P}\bigl[\operatorname{range}\mathbf{A} \subseteq \operatorname{range}\mathbf{V}
\text{ and } \operatorname{rank}\mathbf{V} < d\bigr] = 0\,.$$
For an output rank-$k$ projector $\mathbf{P}$ ($k < d$) the event is
$\mathbf{A}(\mathbf{I} - \mathbf{P}) = \mathbf{0}$.
[ZhangEtAl2026, Lemma 4.2]; there for rank-$k$ projector outputs and success probability bounded
below, here any output with rank below $d$, success probability zero, $k \ge d$ allowed (then
$\operatorname{range}\mathbf{A} = \mathbb{R}^d$ almost surely and the event is impossible). -/
theorem IsMeasurable.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix {p : Type*}
    [Fintype p] {alg : QueryAlgorithm (d → ℝ) (d → ℝ) q (Matrix d p ℝ)}
    (halg : alg.IsMeasurable) {X : Ω → Matrix d k ℝ} (hX : HasLaw X (gaussianMatrix d k) μ)
    (hq : q < Fintype.card k) :
    μ {ω | LinearMap.range (X ω * (X ω)ᴴ).mulVecLin ≤
        LinearMap.range (alg.run (X ω * (X ω)ᴴ).mulVec).mulVecLin ∧
      (alg.run (X ω * (X ω)ᴴ).mulVec).rank < Fintype.card d} = 0 := by
  classical
  set G := alg.gramSimulation k
  set γ := gaussianMatrix d k
  have hG : G.IsMeasurable := halg.gramSimulation
  have hτ : Measurable fun Y : Matrix d k ℝ => G.transcript (twoSidedMulVec Y) :=
    hG.measurable_transcript (Measurable.twoSidedMulVec measurable_fst measurable_snd)
  set B : Set ((Fin (2 * q) → (d → ℝ) × (k → ℝ)) × Matrix d k ℝ) :=
    {t | rangeProjector (G.output t.1) * (t.2 * t.2ᴴ) = t.2 * t.2ᴴ ∧
      (G.output t.1).rank < Fintype.card d} with hB_def
  have hB : MeasurableSet B := by
    have hout : Measurable fun t : (Fin (2 * q) → (d → ℝ) × (k → ℝ)) × Matrix d k ℝ =>
        G.output t.1 := hG.measurable_output.comp measurable_fst
    have hYY : Measurable fun t : (Fin (2 * q) → (d → ℝ) × (k → ℝ)) × Matrix d k ℝ =>
        t.2 * t.2ᴴ :=
      (continuous_id.matrix_mul continuous_id.matrix_conjTranspose).measurable.comp measurable_snd
    exact (measurableSet_eq_fun ((measurable_rangeProjector.comp hout).matrix_mul hYY) hYY).inter
      (measurableSet_lt (measurable_rank.comp hout) measurable_const)
  have hτY : Measurable fun Y : Matrix d k ℝ => (G.transcript (twoSidedMulVec Y), Y) :=
    hτ.prodMk measurable_id
  have hset : {ω | LinearMap.range (X ω * (X ω)ᴴ).mulVecLin ≤
        LinearMap.range (alg.run (X ω * (X ω)ᴴ).mulVec).mulVecLin ∧
      (alg.run (X ω * (X ω)ᴴ).mulVec).rank < Fintype.card d} =
      X ⁻¹' ((fun Y => (G.transcript (twoSidedMulVec Y), Y)) ⁻¹' B) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hB_def, rangeProjector_mul_eq_self_iff,
      ← run_gramSimulation]
    rfl
  rw [hset, ← Measure.map_apply_of_aemeasurable hX.aemeasurable (hτY hB), hX.map_eq]
  have h1 : HasLaw (Prod.fst : _ → Matrix d k ℝ) γ (γ.prod γ) := measurePreserving_fst.hasLaw
  have hid := hG.identDistrib_resample_of_hasLaw_gaussianMatrix h1 measurePreserving_snd.hasLaw
    (indepFun_prod measurable_id measurable_id)
  rw [← h1.map_eq, Measure.map_apply measurable_fst (hτY hB)]
  have := hid.measure_mem_eq hB
  simp only [Set.preimage, Set.mem_ofPred_eq] at this ⊢
  have hτ1 : Measurable fun x : Matrix d k ℝ × Matrix d k ℝ =>
      G.transcript (twoSidedMulVec x.1) := hτ.comp measurable_fst
  have hres : Measurable fun x : Matrix d k ℝ × Matrix d k ℝ => G.resample x.1 x.2 :=
    hG.measurable_resample
  rw [this, Measure.prod_apply (show MeasurableSet {x : Matrix d k ℝ × Matrix d k ℝ |
    (G.transcript (twoSidedMulVec x.1), G.resample x.1 x.2) ∈ B} from hτ1.prodMk hres hB)]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [halg.ae_rank_conjTranspose_mul_leftQueryMatrix_gramSimulation HasLaw.id hq.le]
    with Y hY
  set τ := G.transcript (twoSidedMulVec Y)
  by_cases hV : (G.output τ).rank < Fintype.card d
  · have hF := one_sub_rangeProjector_rightQueryMatrix_gramSimulation_ne_zero alg hq τ
    have hY2 : (Yᴴ * G.leftQueryMatrix τ).rank = (G.leftQueryMatrix τ).rank := hY
    have hZ : ∀ Y', G.resample Y Y' = Y - (1 - rangeProjector (G.leftQueryMatrix τ)) * Y *
        (1 - rangeProjector (G.rightQueryMatrix τ)) + (1 - rangeProjector (G.leftQueryMatrix τ)) *
        Y' * (1 - rangeProjector (G.rightQueryMatrix τ)) := fun _ => rfl
    have h0 := measure_rangeProjector_mul_resample_eq_zero hV hF hY2 hZ
    exact measure_mono_null (fun Y' hY' => hY'.1) h0
  · exact measure_mono_null (fun Y' hY' => (hV hY'.2).elim) measure_empty

/-- **Exact range recovery needs $k$ queries**: let $\mathbf{X}$ be a standard Gaussian
$d \times k$ matrix and $\mathbf{A} = \mathbf{X}\mathbf{X}^{\mathsf{H}}$. A randomized algorithm
(a measurable family of algorithms indexed by a seed $s$ independent of $\mathbf{X}$) making
$q < k$ adaptive queries $\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$ and outputting
$\mathbf{V} \in \mathbb{R}^{d \times p}$ satisfies
$$\mathbb{P}\bigl[\operatorname{range}\mathbf{A} \subseteq \operatorname{range}\mathbf{V}
\text{ and } \operatorname{rank}\mathbf{V} < d\bigr] = 0\,.$$
So exact recovery of the range of a rank-$k$ positive semidefinite matrix by a rank-$k$ projector
($k < d$) needs at least $k$ matrix–vector products, for every success probability $> 0$.
[ZhangEtAl2026, Lemma 4.2]; there for rank-$k$ projector outputs.
Result: range-recovery-k-queries -/
theorem IsMeasurableFamily.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix
    {S p : Type*} [MeasurableSpace S] [Fintype p]
    {alg : S → QueryAlgorithm (d → ℝ) (d → ℝ) q (Matrix d p ℝ)} (halg : IsMeasurableFamily alg)
    {s : Ω → S} (hs : AEMeasurable s μ) {X : Ω → Matrix d k ℝ}
    (hX : HasLaw X (gaussianMatrix d k) μ) (hsX : IndepFun s X μ) (hq : q < Fintype.card k) :
    μ {ω | LinearMap.range (X ω * (X ω)ᴴ).mulVecLin ≤
        LinearMap.range ((alg (s ω)).run (X ω * (X ω)ᴴ).mulVec).mulVecLin ∧
      ((alg (s ω)).run (X ω * (X ω)ᴴ).mulVec).rank < Fintype.card d} = 0 := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  set B : Set (Matrix d k ℝ × Matrix d p ℝ) :=
    {x | rangeProjector x.2 * (x.1 * x.1ᴴ) = x.1 * x.1ᴴ ∧ x.2.rank < Fintype.card d} with hBdef
  have hAm : Measurable fun x : Matrix d k ℝ × Matrix d p ℝ => x.1 * x.1ᴴ :=
    measurable_fst.matrix_mul ((continuous_id.matrix_conjTranspose).measurable.comp measurable_fst)
  have hB : MeasurableSet B := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_eq_fun
        ((measurable_rangeProjector.comp measurable_snd).matrix_mul hAm) hAm
    · exact measurableSet_lt (measurable_rank.comp measurable_snd) measurable_const
  have hO : Measurable (Function.uncurry fun (Y : Matrix d k ℝ) (v : d → ℝ) =>
      (Y * Yᴴ).mulVec v) :=
    (measurable_fst.matrix_mul
      ((continuous_id.matrix_conjTranspose).measurable.comp measurable_fst)).matrix_mulVec
      measurable_snd
  have hfam := IsMeasurableFamily.measureReal_run_mem_le_of_indepFun halg hO hs hX.aemeasurable
    hsX hB (δ := 0) fun a ha => by
      have h0 := IsMeasurable.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix ha hX hq
      have hset : {ω | (X ω, a.run ((fun (Y : Matrix d k ℝ) (v : d → ℝ) =>
          (Y * Yᴴ).mulVec v) (X ω))) ∈ B} = {ω | LinearMap.range (X ω * (X ω)ᴴ).mulVecLin ≤
          LinearMap.range (a.run (X ω * (X ω)ᴴ).mulVec).mulVecLin ∧
          (a.run (X ω * (X ω)ᴴ).mulVec).rank < Fintype.card d} := by
        ext ω
        simp only [hBdef, Set.mem_ofPred_eq, rangeProjector_mul_eq_self_iff]
      rw [hset, measureReal_def, h0]
      simp
  rw [← measureReal_eq_zero_iff (measure_ne_top _ _)]
  refine le_antisymm ?_ measureReal_nonneg
  convert hfam using 2
  · rfl
  · ext ω
    simp only [hBdef, Set.mem_ofPred_eq, rangeProjector_mul_eq_self_iff]

end QueryAlgorithm

end NLAlib
