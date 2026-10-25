/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Probability.QueryModel.Yao
public import NLAlibScaffold.RandomMatrix.DeferredDecision
public import NLAlibScaffold.RandomMatrix.Gaussian.Rank

/-!
# Exact range recovery needs as many queries as the rank

For $\mathbf{A} = \mathbf{X}\mathbf{X}^{\mathsf{H}}$ with $\mathbf{X}$ a standard Gaussian
$d \times k$ matrix, an algorithm that makes fewer than $k$ adaptive products with $\mathbf{A}$
outputs, with probability one, a matrix whose range does not contain the range of $\mathbf{A}$,
unless that output has full rank $d$. In particular no algorithm with fewer than $k$ queries
outputs a rank-$k$ projector $\mathbf{P}$ with $\mathbf{A}(\mathbf{I} - \mathbf{P}) = \mathbf{0}$
with positive probability, for any $k < d$. This is the first end-to-end theorem of the query
model (`docs/design/Probability-MatvecQueryModel.md`, §3.6): Yao's principle, the Gram simulation
and the adaptive Gaussian deferred decision. Since $\mathbf{A}$ is Hermitian, products with
$\mathbf{A}^{\mathsf{H}}$ are products with $\mathbf{A}$, so the bound counts all products.

## Main results

* `NLAlib.rank_mul_of_snoc_eq_rank_of_snoc`: the rank step of general position.

In the `NLAlib.QueryAlgorithm` namespace:

* `IsMeasurable.measure_queryAt_notMem_span_and_mulVec_mem_span_eq_zero`: one query at a time,
  a new direction is almost surely not collapsed by $\mathbf{X}^{\mathsf{H}}$.
* `IsMeasurable.ae_rank_conjTranspose_mul_leftQueryMatrix_gramSimulation`: the left
  responses of the Gram simulation are in general position.
* `IsMeasurable.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix`: deterministic
  algorithms.
* `IsMeasurableFamily.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix`: randomized
  algorithms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

private lemma finrank_sup_span_singleton_of_notMem {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] {p : Submodule K V} [FiniteDimensional K p] {v : V}
    (hv : v ∉ p) : Module.finrank K ↥(p ⊔ K ∙ v) = Module.finrank K p + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ p.zero_mem)
  have hinf : p ⊓ K ∙ v = ⊥ :=
    (Submodule.disjoint_span_singleton' hv0).mpr hv |>.eq_bot
  have := Submodule.finrank_sup_add_finrank_inf_eq p (K ∙ v)
  rw [hinf, finrank_bot, finrank_span_singleton hv0] at this
  omega

/-- **Rank step of general position**: let $\mathbf{B} \in \Bbbk^{k \times d}$ preserve the rank
of $\mathbf{U} \in \Bbbk^{d \times i}$, $\operatorname{rank}(\mathbf{B}\mathbf{U}) =
\operatorname{rank}\mathbf{U}$, and append a column $\mathbf{x}$. If $\mathbf{x}$ lies in the
column span of $\mathbf{U}$, or $\mathbf{B}\mathbf{x}$ does not lie in the column span of
$\mathbf{B}\mathbf{U}$, then $\mathbf{B}$ preserves the rank of $[\mathbf{U}\;\mathbf{x}]$.
Proof: M, about 40 lines. `Matrix.rank_eq_finrank_span_cols` on all four matrices; the columns of
`Matrix.of fun r => Fin.snoc (U r) (x r)` are those of $\mathbf{U}$ and $\mathbf{x}$
(`Fin.snoc_castSucc`, `Fin.snoc_last`, `Fin.lastCases`), so its column span is
`span (range Uᵀ) ⊔ span {x}` (`Submodule.span_insert`, `Set.range` of a `Fin.snoc`), and
likewise for $\mathbf{B}[\mathbf{U}\;\mathbf{x}] = [\mathbf{B}\mathbf{U}\;\mathbf{B}\mathbf{x}]$
(`Matrix.mul_apply`, `Matrix.mulVec`). First case: both spans are unchanged
(`Submodule.span_insert_eq_span`; $\mathbf{B}\mathbf{x}$ is in the image span by linearity,
`Submodule.span_image` with `Matrix.mulVecLin`). Second case: then $\mathbf{x}$ is not in the span
of $\mathbf{U}$ either (else $\mathbf{B}\mathbf{x}$ would be in the image), and both finranks
grow by one (`Submodule.span_insert` and a `finrank` count for adding a vector outside a
subspace, e.g. through `Submodule.finrank_add_eq_of_isCompl` or
`finrank_sup_add_finrank_inf_eq`). -/
theorem rank_mul_of_snoc_eq_rank_of_snoc {𝕜 : Type*} [Field 𝕜] {d k : Type*} [Fintype d] {i : ℕ}
    (B : Matrix k d 𝕜) (U : Matrix d (Fin i) 𝕜) (x : d → 𝕜)
    (hU : (B * U).rank = U.rank)
    (hx : x ∈ Submodule.span 𝕜 (Set.range Uᵀ) ∨ B *ᵥ x ∉ Submodule.span 𝕜 (Set.range (B * U)ᵀ)) :
    (B * Matrix.of fun r => Fin.snoc (α := fun _ => 𝕜) (U r) (x r)).rank =
      (Matrix.of fun r => Fin.snoc (α := fun _ => 𝕜) (U r) (x r)).rank := by
  set M : Matrix d (Fin (i + 1)) 𝕜 := Matrix.of fun r => Fin.snoc (α := fun _ => 𝕜) (U r) (x r)
  have hcolBU : Set.range (B * U).col = Matrix.mulVecLin B '' Set.range U.col := by
    rw [← Set.range_comp]
    congr 1
  have hMcol : M.col = Fin.snoc U.col x := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [Fin.snoc_last]; funext r; simp [M]
    · rw [Fin.snoc_castSucc]; funext r; simp [M]
  have hcolM : Set.range M.col = insert x (Set.range U.col) := by
    rw [hMcol, Fin.range_snoc]
  have hcolBM : Set.range (B * M).col = insert (B *ᵥ x) (Set.range (B * U).col) := by
    have : (B * M).col = Fin.snoc (B * U).col (B *ᵥ x) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last]; funext r; simp [M, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      · rw [Fin.snoc_castSucc]; funext r; simp [M, Matrix.mul_apply]
    rw [this, Fin.range_snoc]
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols] at hU ⊢
  rw [hcolBM, hcolM, Submodule.span_insert, Submodule.span_insert]
  change x ∈ Submodule.span 𝕜 (Set.range U.col) ∨
    B *ᵥ x ∉ Submodule.span 𝕜 (Set.range (B * U).col) at hx
  rw [hcolBU, Submodule.span_image] at hU hx ⊢
  have hW : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range U.col)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  generalize Submodule.span 𝕜 (Set.range U.col) = W at hU hx hW ⊢
  have hBx : B *ᵥ x = B.mulVecLin x := rfl
  rw [hBx] at hx ⊢
  rcases em (x ∈ W) with h | h
  · rw [sup_eq_right.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr h),
      sup_eq_right.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr
        (Submodule.mem_map_of_mem h)), hU]
  · have h' : B.mulVecLin x ∉ W.map B.mulVecLin := hx.resolve_left h
    rw [sup_comm, finrank_sup_span_singleton_of_notMem h',
      sup_comm, finrank_sup_span_singleton_of_notMem h, hU]

namespace QueryAlgorithm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {d k : Type*} [Fintype d]
  [Fintype k] {q : ℕ}

private theorem queryAt_gramSimulation_two_mul {β : Type*}
    (alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β) (Y : Matrix d k ℝ) (l : ℕ) :
    (alg.gramSimulation k).queryAt (twoSidedMulVec Y) (2 * l) =
      (0, alg.queryAt (Y * Yᴴ).mulVec l) := by
  have h := history_gramSimulation alg Y l
  rw [queryAt]
  generalize (alg.gramSimulation k).history (twoSidedMulVec Y) (2 * l) = H at h ⊢
  dsimp only [gramSimulation]
  rw [dif_pos (by omega)]
  have key : ∀ (n : ℕ) (hn : n = l) (f : Fin n → d → ℝ),
      alg.query n f = alg.query l fun m => f (Fin.cast hn.symm m) := by
    rintro n rfl f; rfl
  refine Prod.ext rfl ((key _ (by omega) _).trans ?_)
  exact congrArg (alg.query l) h

private theorem queryAt_gramSimulation_two_mul_add_one {β : Type*}
    (alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β) (Y : Matrix d k ℝ) (l : ℕ) :
    (alg.gramSimulation k).queryAt (twoSidedMulVec Y) (2 * l + 1) =
      (Yᴴ *ᵥ alg.queryAt (Y * Yᴴ).mulVec l, 0) := by
  have h := history_apply (alg.gramSimulation k) (twoSidedMulVec Y) (2 * l + 1) ⟨2 * l, by omega⟩
  rw [queryAt_gramSimulation_two_mul] at h
  rw [queryAt]
  generalize (alg.gramSimulation k).history (twoSidedMulVec Y) (2 * l + 1) = H at h ⊢
  dsimp only [gramSimulation]
  rw [dif_neg (by omega)]
  refine Prod.ext ?_ rfl
  change (H ⟨2 * l, by omega⟩).2 = _
  rw [h]
  rfl

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

private theorem queryAt_eq_query_transcript_gramSimulation {β : Type*}
    (alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β) (Y : Matrix d k ℝ) :
    alg.queryAt (Y * Yᴴ).mulVec q = alg.query q fun l : Fin q =>
      ((alg.gramSimulation k).transcript (twoSidedMulVec Y) ⟨2 * l + 1, by omega⟩).1 := by
  rw [queryAt, ← history_gramSimulation]
  rfl

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
private theorem one_sub_rangeProjector_rightQueryMatrix_gramSimulation_ne_zero [DecidableEq k]
    {β : Type*} (alg : QueryAlgorithm (d → ℝ) (d → ℝ) q β) (hq : q < Fintype.card k)
    (τ : Fin (2 * q) → (d → ℝ) × (k → ℝ)) :
    1 - rangeProjector ((alg.gramSimulation k).rightQueryMatrix τ) ≠ 0 := by
  intro h
  have h1 := rank_rangeProjector ((alg.gramSimulation k).rightQueryMatrix τ)
  rw [← sub_eq_zero.1 h, Matrix.rank_one] at h1
  have := rank_rightQueryMatrix_gramSimulation_le alg τ
  omega

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
[ZhangEtAl2026, proof of Lemma 4.2]; there inside the block decomposition of Lemma 4.1.
Proof: L, about 70 lines. Let $T$ be the Gram simulation truncated to its first `2 * i` rounds,
`(alg.gramSimulation k).truncate (2 * i)` (measurable: `QueryAlgorithm.IsMeasurable.truncate` of
`QueryAlgorithm.IsMeasurable.gramSimulation`, `2 * i ≤ 2 * q`), with transcript
`(alg.gramSimulation k).history (twoSidedMulVec X) (2 * i)`
(`QueryAlgorithm.transcript_truncate`). By
`QueryAlgorithm.history_gramSimulation` and `QueryAlgorithm.history_apply`, the queries
$\mathbf{x}_l$ ($l \le i$) are functions of that transcript, the left query matrix of $T$ has
columns $\mathbf{x}_l$ and zeros, and its right query matrix has columns
$\mathbf{X}^{\mathsf{H}}\mathbf{x}_l$ (second components of the even responses) and zeros; so with
$\mathbf{E}$, $\mathbf{F}$ as in `QueryAlgorithm.resample` for $T$, the first condition is
$\mathbf{E}\mathbf{x}_i \ne \mathbf{0}$ and the second
$\mathbf{F}\mathbf{X}^{\mathsf{H}}\mathbf{x}_i = \mathbf{0}$ (`rangeProjector`, range of the
complement projector). Extend $\Omega$ by an independent Gaussian $\mathbf{X}'$ (`Measure.prod`
with `gaussianMatrix d k`). By
`QueryAlgorithm.IsMeasurable.identDistrib_resample_of_hasLaw_gaussianMatrix` for $T$, the event has
the probability of the same event for $\widetilde{\mathbf{X}} = \mathbf{X} -
\mathbf{E}\mathbf{X}\mathbf{F} + \mathbf{E}\mathbf{X}'\mathbf{F}$ with the transcript of
$\mathbf{X}$, and $\mathbf{F}\widetilde{\mathbf{X}}^{\mathsf{H}}\mathbf{x}_i
= \mathbf{F}\mathbf{X}'^{\mathsf{H}}\mathbf{E}\mathbf{x}_i$ ($\mathbf{F}\mathbf{X}^{\mathsf{H}}
(\mathbf{I} - \mathbf{E})\mathbf{x}_i = \mathbf{0}$ since $(\mathbf{I} - \mathbf{E})\mathbf{x}_i$
is in the left query span). Freeze the transcript
(`ProbabilityTheory.IndepFun.measureReal_mem_le_add` with $\delta_1 = \delta_2 = 0$, the
transcript of $\mathbf{X}$ independent of $\mathbf{X}'$): for a fixed transcript with
$\mathbf{E}\mathbf{x}_i \ne \mathbf{0}$, the event
$(\mathbf{E}\mathbf{x}_i)^{\mathsf{H}}\mathbf{X}'\mathbf{F} = \mathbf{0}$ has probability zero
by `NLAlib.measure_mul_mul_eq_eq_zero_of_hasLaw_gaussianMatrix` (row matrix
$\mathbf{N} = (\mathbf{E}\mathbf{x}_i)^{\mathsf{H}} \ne \mathbf{0}$, and $\mathbf{F} \ne
\mathbf{0}$ because the range of the right query matrix of $T$ is the span of the
$\mathbf{X}^{\mathsf{H}}\mathbf{x}_l$, $l < i$, of finrank at most $i < k$
(`finrank_span_le_card`; the width of that matrix is `2 * i`, so `Matrix.rank_le_width` does not
suffice)). Split off the identification of the event with the $\mathbf{E}$, $\mathbf{F}$
form as a private lemma. -/
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
    (Continuous.measurable (by unfold Function.uncurry twoSidedMulVec; fun_prop))
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
    (indepFun_prod (μ := μ) (ν := gaussianMatrix d k) measurable_id measurable_id).comp₀
      measurable_fst.aemeasurable measurable_snd.aemeasurable
      (by change AEMeasurable X (μ'.map Prod.fst); rw [measurePreserving_fst.map_eq]
          exact hX.aemeasurable) measurable_id.aemeasurable
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

/-- Congruence of `query` in its index, along an equality of indices. -/
private lemma query_congr_index {Q R β : Type*} {q : ℕ} (alg : QueryAlgorithm Q R q β) {m n : ℕ}
    (hmn : m = n) (F : Fin m → R) (G : Fin n → R)
    (hFG : ∀ l : Fin m, F l = G (Fin.cast hmn l)) : alg.query m F = alg.query n G := by
  subst hmn
  exact congrArg (alg.query _) (funext fun l => hFG l)

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
      exact rank_mul_of_snoc_eq_rank_of_snoc Yᴴ _ (fun r => alg.queryAt (Y * Yᴴ).mulVec i r)
        (ih (by omega)) (hgood i (by omega))
  -- the even columns of `L` are the queries, the odd ones are zero
  have hEven : ∀ (j : Fin (2 * q)) (i : ℕ) (hi : i < q), (j : ℕ) = 2 * i →
      L.col j = alg.queryAt (Y * Yᴴ).mulVec i := by
    rintro ⟨j, hj⟩ i hi hji
    simp only at hji
    subst hji
    funext r
    have hsnd : ∀ h : Fin (2 * i) → (d → ℝ) × (k → ℝ),
        ((alg.gramSimulation k).query (2 * i) h).2 =
          alg.query i (fun l => (h ⟨2 * l + 1, by have := l.isLt; omega⟩).1) := by
      intro h
      have hdec : 2 * i % 2 = 0 := Nat.mul_mod_right 2 i
      dsimp only [QueryAlgorithm.gramSimulation]
      rw [dif_pos hdec]
      exact query_congr_index alg (by omega) _ _ (fun l => rfl)
    change ((alg.gramSimulation k).queries _ ⟨2 * i, hj⟩).2 r = _
    rw [← QueryAlgorithm.queryAt_eq_queries_transcript]
    change ((alg.gramSimulation k).query (2 * i) _).2 r = _
    rw [hsnd, QueryAlgorithm.history_gramSimulation]
    rfl
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
[ZhangEtAl2026, proof of Lemma 4.2]; there inside the block decomposition of Lemma 4.1.
Proof: M, about 50 lines. Almost surely the events of
`QueryAlgorithm.IsMeasurable.measure_queryAt_notMem_span_and_mulVec_mem_span_eq_zero` fail for
every `i < q` (`ae_all_iff` over `Fin q`, `measure_eq_zero_iff_ae_notMem`; `i < k` from `hq`). On
that set, with $\mathbf{U}_i$ = `Matrix.of fun r (l : Fin i) => alg.queryAt (X * Xᴴ).mulVec l r`,
show $\operatorname{rank}(\mathbf{X}^{\mathsf{H}}\mathbf{U}_i) = \operatorname{rank}\mathbf{U}_i$
for `i ≤ q` by induction: `i = 0` both sides are `0` (`Matrix.rank_le_width`); the step is
`NLAlib.rank_mul_of_snoc_eq_rank_of_snoc` with `B = Xᴴ` ($\mathbf{U}_{i+1}$ is the `Fin.snoc` of
$\mathbf{U}_i$ and
$\mathbf{x}_i$, `Matrix.ext`, `Fin.lastCases`), whose hypothesis is the negation of the bad event
(`not_and_or`, `not_not`; the column spans are `Set.range` of the queries, `Matrix.mul_apply`).
Finally the left query matrix of the simulation has the columns of $\mathbf{U}_q$ (at the even
indices, by `QueryAlgorithm.history_gramSimulation` and
`QueryAlgorithm.queryAt_eq_queries_transcript`) and zero columns, and $\mathbf{X}^{\mathsf{H}}$
times it the columns of $\mathbf{X}^{\mathsf{H}}\mathbf{U}_q$ and zeros, so both column spans
agree (`Matrix.rank_eq_finrank_span_cols`, `Submodule.span_insert_zero`-type rewriting) and the
ranks transfer. -/
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
$\operatorname{range}\mathbf{A} = \mathbb{R}^d$ almost surely and the event is impossible).
Proof: L, about 70 lines. By `QueryAlgorithm.run_gramSimulation` the output is that of
`alg.gramSimulation k` on `twoSidedMulVec X` (measurable by
`QueryAlgorithm.IsMeasurable.gramSimulation`), and
$\operatorname{range}\mathbf{A} = \operatorname{range}\mathbf{X}$ over $\mathbb{R}$. Extend
$\Omega$ by an independent Gaussian $\mathbf{X}'$ (`Measure.prod`); by
`QueryAlgorithm.IsMeasurable.identDistrib_resample_of_hasLaw_gaussianMatrix` and
`QueryAlgorithm.transcript_resample` the event has the probability of the same event for
$\widetilde{\mathbf{X}} = \mathbf{X} - \mathbf{E}\mathbf{X}\mathbf{F} +
\mathbf{E}\mathbf{X}'\mathbf{F}$ with the same output $\mathbf{V}$ (the event is measurable:
$\operatorname{range}\mathbf{A} \subseteq \operatorname{range}\mathbf{V}$ iff
$(\mathbf{I} - \mathbf{P}_{\mathbf{V}})\mathbf{A} = \mathbf{0}$, `measurable_rangeProjector`,
`measurable_rank`). Condition on $\mathbf{X}$ (`ProbabilityTheory.IndepFun.measureReal_mem_le_add`
with the good set of
`QueryAlgorithm.IsMeasurable.ae_rank_conjTranspose_mul_leftQueryMatrix_gramSimulation`).
For fixed $\mathbf{X}$ in the good set, with $\mathbf{N} = \mathbf{I} - \mathbf{P}_{\mathbf{V}}
\ne \mathbf{0}$ (rank below $d$), the event is
$\mathbf{N}\mathbf{E}\mathbf{X}'\mathbf{F}
= -\mathbf{N}(\mathbf{X} - \mathbf{E}\mathbf{X}\mathbf{F})$.
$\mathbf{F} \ne \mathbf{0}$ by `QueryAlgorithm.rank_rightQueryMatrix_gramSimulation_le` and
$q < k$. If $\mathbf{N}\mathbf{E} \ne \mathbf{0}$ the probability is zero
(`NLAlib.measure_mul_mul_eq_eq_zero_of_hasLaw_gaussianMatrix`). If
$\mathbf{N}\mathbf{E} = \mathbf{0}$ the rows of $\mathbf{N}$ lie in the span of the left
queries and the event says $\mathbf{N}\mathbf{X} = \mathbf{0}$, which contradicts the good set: a
nonzero row $\mathbf{n} = \mathbf{U}\mathbf{c}$ with $\mathbf{X}^{\mathsf{H}}\mathbf{U}\mathbf{c}
= \mathbf{0}$ forces $\operatorname{rank}(\mathbf{X}^{\mathsf{H}}\mathbf{U}) <
\operatorname{rank}\mathbf{U}$ (`Matrix.rank_mul_le`, rank–nullity). Split the case analysis
into a private lemma. -/
theorem IsMeasurable.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix {p : Type*}
    [Fintype p] {alg : QueryAlgorithm (d → ℝ) (d → ℝ) q (Matrix d p ℝ)}
    (halg : alg.IsMeasurable) {X : Ω → Matrix d k ℝ} (hX : HasLaw X (gaussianMatrix d k) μ)
    (hq : q < Fintype.card k) :
    μ {ω | LinearMap.range (X ω * (X ω)ᴴ).mulVecLin ≤
        LinearMap.range (alg.run (X ω * (X ω)ᴴ).mulVec).mulVecLin ∧
      (alg.run (X ω * (X ω)ᴴ).mulVec).rank < Fintype.card d} = 0 := by
  sorry

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
Proof: S, about 15 lines. `QueryAlgorithm.IsMeasurableFamily.measureReal_run_mem_le_of_indepFun`
with $\delta = 0$, oracle `fun X => (X * Xᴴ).mulVec` (measurable: `Measurable.matrix_mulVec`,
`Continuous.matrix_mul`), and $B$ the measurable set
$\{(\mathbf{X}, \mathbf{V}) \mid
(\mathbf{I} - \mathbf{P}_{\mathbf{V}})\mathbf{X}\mathbf{X}^{\mathsf{H}} = \mathbf{0} \wedge
\operatorname{rank}\mathbf{V} < d\}$ (`measurable_rangeProjector`,
`measurable_rank`; it equals the event, `range_le_iff_exists_mul` or the projector form);
each deterministic case is
`QueryAlgorithm.IsMeasurable.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix`
(`measureReal_eq_zero_iff`). Back to `μ` with `measureReal_eq_zero_iff`.
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
        simp only [hBdef, Set.mem_setOf_eq, rangeProjector_mul_eq_self_iff]
      rw [hset, measureReal_def, h0]
      simp
  rw [← measureReal_eq_zero_iff (measure_ne_top _ _)]
  refine le_antisymm ?_ measureReal_nonneg
  convert hfam using 2
  · rfl
  · ext ω
    simp only [hBdef, Set.mem_setOf_eq, rangeProjector_mul_eq_self_iff]

end QueryAlgorithm

end NLAlib
