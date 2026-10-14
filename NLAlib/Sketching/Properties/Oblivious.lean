/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Sketching.Properties.FixedSubspace
public import NLAlib.Sketching.Properties.Isotropic

/-!
# Oblivious subspace embeddings and injections

A random sketch `S : Ω → Matrix k n 𝕜` is an *oblivious subspace embedding* (OSE) for dimension
`d` when, for every fixed subspace of dimension at most `d`, it is a subspace embedding with
probability `1 - δ`; it is an *oblivious subspace injection* (OSI) when it is isotropic and the
lower half holds with probability `1 - δ` on every such subspace. Subspaces are column spaces of
square matrices `U : Matrix n n 𝕜` with `U.rank ≤ d`;
`NLAlib.IsObliviousSubspaceEmbedding.hasSubspaceEmbedding` applies the predicate to `U` of any
shape.

Every sketching family concludes one of these predicates, through the constructor from
orthonormal `U : Matrix n p 𝕜`; every consumer takes one. The predicates transfer to a random
subspace independent of the sketch, and compose over independent sketches.

Theorems that compare two events take `[IsFiniteMeasure μ]`. Design:
`docs/design/Sketching-S1.md` §3.3.

## Main definitions

* `NLAlib.IsObliviousSubspaceEmbedding S d a b δ μ`.
* `NLAlib.IsObliviousSubspaceInjection S d a δ μ`.

## Main results

* `NLAlib.IsObliviousSubspaceEmbedding.of_hasOrthonormalCols`: the constructor families use.
* `NLAlib.IsObliviousSubspaceEmbedding.isObliviousSubspaceInjection`: an isotropic OSE is an OSI.
* `NLAlib.IsObliviousSubspaceEmbedding.measure_not_isSubspaceEmbedding_le_of_indepFun`: transfer
  to an independent random subspace.
* `NLAlib.IsObliviousSubspaceEmbedding.mul`: composition of independent sketches.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k l n p q : Type*} [Fintype k] [Fintype l] [Fintype n] {S : Ω → Matrix k n 𝕜}
  {a a' a₂ b b' b₂ δ δ' δ₂ : ℝ} {d d' : ℕ}

/-- **Oblivious subspace embedding** for dimension `d`: for every `U : Matrix n n 𝕜` of rank at
most `d`, `S` is a subspace embedding for `range U` with constants `a`, `b` with probability
`1 - δ`. [Woodruff2014, Definition 2] (`1 ∓ ε`); [CamanoEpperlyMeyerTropp2025, Definition 1.1]
(`α`, `β`); there for subspaces of dimension exactly `d`, here at most `d`.
Result: ose-def -/
def IsObliviousSubspaceEmbedding (S : Ω → Matrix k n 𝕜) (d : ℕ) (a b δ : ℝ) (μ : Measure Ω) :
    Prop :=
  ∀ U : Matrix n n 𝕜, U.rank ≤ d → HasSubspaceEmbedding S U a b δ μ

/-- **Oblivious subspace injection** for dimension `d`: `S` is isotropic and, for every
`U : Matrix n n 𝕜` of rank at most `d`, a subspace injection for `range U` with constant `a` with
probability `1 - δ`. [CamanoEpperlyMeyerTropp2025, Definition 1.2]; there `δ = 1/20` and
`α ∈ (0, 1]`, here any `δ` and `a`.
Result: osi-def -/
structure IsObliviousSubspaceInjection [DecidableEq n] (S : Ω → Matrix k n 𝕜) (d : ℕ) (a δ : ℝ)
    (μ : Measure Ω) : Prop where
  /-- The sketch is isotropic. -/
  isotropic : IsIsotropicSketch S μ
  /-- The lower half holds with probability `1 - δ` on every subspace of dimension at most `d`. -/
  injection : ∀ U : Matrix n n 𝕜, U.rank ≤ d → HasSubspaceInjection S U a δ μ

/-- Being an OSE depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.isObliviousSubspaceEmbedding_iff
    {ν : Measure (Matrix k n 𝕜)} (hS : HasLaw S ν μ) :
    IsObliviousSubspaceEmbedding S d a b δ μ ↔ IsObliviousSubspaceEmbedding id d a b δ ν := by
  exact forall₂_congr fun U _ => hS.hasSubspaceEmbedding_iff

/-- Being an OSI depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.isObliviousSubspaceInjection_iff [DecidableEq n]
    {ν : Measure (Matrix k n 𝕜)} (hS : HasLaw S ν μ) :
    IsObliviousSubspaceInjection S d a δ μ ↔ IsObliviousSubspaceInjection id d a δ ν := by
  constructor
  · intro h
    exact ⟨hS.isIsotropicSketch_iff.1 h.isotropic,
      fun U hU => hS.hasSubspaceInjection_iff.1 (h.injection U hU)⟩
  · intro h
    exact ⟨hS.isIsotropicSketch_iff.2 h.isotropic,
      fun U hU => hS.hasSubspaceInjection_iff.2 (h.injection U hU)⟩

/-- An OSE applies to the column space of a matrix of any shape and rank at most `d`. -/
theorem IsObliviousSubspaceEmbedding.hasSubspaceEmbedding [Fintype p]
    (h : IsObliviousSubspaceEmbedding S d a b δ μ) {U : Matrix n p 𝕜} (hU : U.rank ≤ d) :
    HasSubspaceEmbedding S U a b δ μ := by
  have hr := range_mulVecLin_rangeProjector U
  have e : {ω | ¬ IsSubspaceEmbedding (S ω) U a b} =
      {ω | ¬ IsSubspaceEmbedding (S ω) (rangeProjector U) a b} :=
    Set.ext fun ω => not_congr ⟨fun h' => h'.of_range_le hr.le, fun h' => h'.of_range_le hr.ge⟩
  unfold HasSubspaceEmbedding
  rw [e]
  exact h _ (by rwa [rank_rangeProjector])

/-- An OSI applies to the column space of a matrix of any shape and rank at most `d`. -/
theorem IsObliviousSubspaceInjection.hasSubspaceInjection [DecidableEq n] [Fintype p]
    (h : IsObliviousSubspaceInjection S d a δ μ) {U : Matrix n p 𝕜} (hU : U.rank ≤ d) :
    HasSubspaceInjection S U a δ μ := by
  have hr := range_mulVecLin_rangeProjector U
  have e : {ω | ¬ IsSubspaceInjection (S ω) U a} =
      {ω | ¬ IsSubspaceInjection (S ω) (rangeProjector U) a} :=
    Set.ext fun ω => not_congr ⟨fun h' => h'.of_range_le hr.le, fun h' => h'.of_range_le hr.ge⟩
  unfold HasSubspaceInjection
  rw [e]
  exact h.injection _ (by rwa [rank_rangeProjector])

/-- **The OSE constructor**: a sketch that is a random subspace embedding for every `U` with
orthonormal columns indexed by `p` is an OSE for dimension `card p`. The constructor every
sketching family uses. -/
theorem IsObliviousSubspaceEmbedding.of_hasOrthonormalCols [IsFiniteMeasure μ] [Fintype p]
    [DecidableEq p] (hp : Fintype.card p ≤ Fintype.card n)
    (h : ∀ U : Matrix n p 𝕜, HasOrthonormalCols U → HasSubspaceEmbedding S U a b δ μ) :
    IsObliviousSubspaceEmbedding S (Fintype.card p) a b δ μ := by
  intro U hU
  obtain ⟨Q, hQ, hUQ⟩ := exists_hasOrthonormalCols_range_le U hU hp
  exact (h Q hQ).of_range_le hUQ

/-- **The OSI constructor**: an isotropic sketch that is a random subspace injection for every
`U` with orthonormal columns indexed by `p` is an OSI for dimension `card p`. -/
theorem IsObliviousSubspaceInjection.of_hasOrthonormalCols [IsFiniteMeasure μ] [DecidableEq n]
    [Fintype p] [DecidableEq p] (hiso : IsIsotropicSketch S μ)
    (hp : Fintype.card p ≤ Fintype.card n)
    (h : ∀ U : Matrix n p 𝕜, HasOrthonormalCols U → HasSubspaceInjection S U a δ μ) :
    IsObliviousSubspaceInjection S (Fintype.card p) a δ μ := by
  refine ⟨hiso, fun U hU => ?_⟩
  obtain ⟨Q, hQ, hUQ⟩ := exists_hasOrthonormalCols_range_le U hU hp
  exact (h Q hQ).of_range_le hUQ

/-- An isotropic OSE is an OSI with the same lower constant and failure probability. -/
theorem IsObliviousSubspaceEmbedding.isObliviousSubspaceInjection [IsFiniteMeasure μ]
    [DecidableEq n] (h : IsObliviousSubspaceEmbedding S d a b δ μ)
    (hiso : IsIsotropicSketch S μ) : IsObliviousSubspaceInjection S d a δ μ := by
  exact ⟨hiso, fun U hU => (h U hU).hasSubspaceInjection⟩

/-- An OSE is one for any smaller dimension, weaker constants and larger failure
probability. -/
theorem IsObliviousSubspaceEmbedding.mono [IsFiniteMeasure μ]
    (h : IsObliviousSubspaceEmbedding S d a b δ μ) (hd : d' ≤ d) (ha : a' ≤ a) (hb : b ≤ b')
    (hδ : δ ≤ δ') : IsObliviousSubspaceEmbedding S d' a' b' δ' μ := by
  exact fun U hU => (h U (hU.trans hd)).mono ha hb hδ

/-- An OSI is one for any smaller dimension, smaller constant and larger failure
probability. -/
theorem IsObliviousSubspaceInjection.mono [IsFiniteMeasure μ] [DecidableEq n]
    (h : IsObliviousSubspaceInjection S d a δ μ) (hd : d' ≤ d) (ha : a' ≤ a) (hδ : δ ≤ δ') :
    IsObliviousSubspaceInjection S d' a' δ' μ := by
  exact ⟨h.isotropic, fun U hU => (h.injection U (hU.trans hd)).mono ha hδ⟩

/-! ### Transfer to an independent random subspace -/

omit [Fintype k] [Fintype l] [Fintype n] in
/-- The Fubini step of the transfer lemmas: a closed property `P` of the pair `(S, B)` that fails
with probability at most `δ` for every fixed `B` of rank at most `d` fails with probability at
most `δ` at an independent random `V` of rank at most `d`. -/
private theorem measureReal_not_le_of_indepFun [Finite k] [Finite n] [IsProbabilityMeasure μ]
    [Fintype q]
    {P : Matrix k n 𝕜 → Matrix n q 𝕜 → Prop}
    (hP : IsClosed {x : Matrix k n 𝕜 × Matrix n q 𝕜 | P x.1 x.2}) {V : Ω → Matrix n q 𝕜}
    (hind : IndepFun S V μ) (hS : AEMeasurable S μ) (hV : AEMeasurable V μ)
    (hrank : ∀ᵐ ω ∂μ, (V ω).rank ≤ d) (hδ : 0 ≤ δ)
    (hfix : ∀ B : Matrix n q 𝕜, B.rank ≤ d → μ.real {ω | ¬ P (S ω) B} ≤ δ) :
    μ.real {ω | ¬ P (S ω) (V ω)} ≤ δ := by
  have hE : MeasurableSet {x : Matrix k n 𝕜 × Matrix n q 𝕜 | ¬ P x.1 x.2} :=
    hP.isOpen_compl.measurableSet
  have hslice (B : Matrix n q 𝕜) : MeasurableSet {A : Matrix k n 𝕜 | ¬ P A B} :=
    (hP.preimage (continuous_id.prodMk continuous_const)).isOpen_compl.measurableSet
  have hmeas : μ {ω | ¬ P (S ω) (V ω)} = ∫⁻ ω, μ {ω' | ¬ P (S ω') (V ω)} ∂μ := by
    have h1 : μ {ω | ¬ P (S ω) (V ω)} =
        (μ.map fun ω => (S ω, V ω)) {x | ¬ P x.1 x.2} := by
      rw [Measure.map_apply_of_aemeasurable (hS.prodMk hV) hE]
      rfl
    rw [h1, (indepFun_iff_map_prod_eq_prod_map_map hS hV).1 hind, Measure.prod_apply_symm hE,
      lintegral_map' (measurable_measure_prodMk_right hE).aemeasurable hV]
    exact lintegral_congr fun ω => Measure.map_apply_of_aemeasurable hS (hslice (V ω))
  have hle : μ {ω | ¬ P (S ω) (V ω)} ≤ ENNReal.ofReal δ := by
    rw [hmeas]
    calc ∫⁻ ω, μ {ω' | ¬ P (S ω') (V ω)} ∂μ ≤ ∫⁻ _, ENNReal.ofReal δ ∂μ := by
          refine lintegral_mono_ae (hrank.mono fun ω hω => ?_)
          rw [← ofReal_measureReal]
          exact ENNReal.ofReal_le_ofReal (hfix _ hω)
      _ = ENNReal.ofReal δ := by rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.toReal_le_of_le_ofReal hδ hle

/-- **Transfer of an OSE to an independent random subspace**: if `V` is independent of `S` and
has rank at most `d` almost surely, `S ω` fails to embed `range (V ω)` with probability at most
`δ`. Fubini on the closed set of `NLAlib.isClosed_setOf_isSubspaceEmbedding`. -/
theorem IsObliviousSubspaceEmbedding.measure_not_isSubspaceEmbedding_le_of_indepFun
    [IsProbabilityMeasure μ] [Fintype q] (h : IsObliviousSubspaceEmbedding S d a b δ μ)
    {V : Ω → Matrix n q 𝕜} (hind : IndepFun S V μ) (hS : AEMeasurable S μ)
    (hV : AEMeasurable V μ) (hrank : ∀ᵐ ω ∂μ, (V ω).rank ≤ d) :
    μ.real {ω | ¬ IsSubspaceEmbedding (S ω) (V ω) a b} ≤ δ := by
  have hδ : 0 ≤ δ := measureReal_nonneg.trans (h 0 (by simp))
  exact measureReal_not_le_of_indepFun (P := fun A B => IsSubspaceEmbedding A B a b)
    (isClosed_setOf_isSubspaceEmbedding a b) hind hS hV hrank hδ
    fun B hB => h.hasSubspaceEmbedding hB

/-- **Transfer of an OSI to an independent random subspace**: if `V` is independent of `S` and
has rank at most `d` almost surely, `S ω` fails to inject `range (V ω)` with probability at most
`δ`. -/
theorem IsObliviousSubspaceInjection.measure_not_isSubspaceInjection_le_of_indepFun
    [IsProbabilityMeasure μ] [DecidableEq n] [Fintype q]
    (h : IsObliviousSubspaceInjection S d a δ μ) {V : Ω → Matrix n q 𝕜} (hind : IndepFun S V μ)
    (hS : AEMeasurable S μ) (hV : AEMeasurable V μ) (hrank : ∀ᵐ ω ∂μ, (V ω).rank ≤ d) :
    μ.real {ω | ¬ IsSubspaceInjection (S ω) (V ω) a} ≤ δ := by
  have hδ : 0 ≤ δ := measureReal_nonneg.trans (h.injection 0 (by simp))
  exact measureReal_not_le_of_indepFun (P := fun A B => IsSubspaceInjection A B a)
    (isClosed_setOf_isSubspaceInjection a) hind hS hV hrank hδ
    fun B hB => h.hasSubspaceInjection hB

/-! ### Composition -/

/-- **Composition of OSEs**: for independent OSEs `S₂` and `S` for the same dimension, `S₂ * S`
is an OSE with multiplied constants and failure probability `δ₂ + δ`. -/
theorem IsObliviousSubspaceEmbedding.mul [IsProbabilityMeasure μ] {S₂ : Ω → Matrix l k 𝕜}
    (h₂ : IsObliviousSubspaceEmbedding S₂ d a₂ b₂ δ₂ μ)
    (h : IsObliviousSubspaceEmbedding S d a b δ μ) (hind : IndepFun S₂ S μ)
    (hS₂ : AEMeasurable S₂ μ) (hS : AEMeasurable S μ) (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂) :
    IsObliviousSubspaceEmbedding (fun ω => S₂ ω * S ω) d (a₂ * a) (b₂ * b) (δ₂ + δ) μ := by
  intro U hU
  have hc : Continuous fun A : Matrix k n 𝕜 => A * U := continuous_id.matrix_mul continuous_const
  have hindU : IndepFun S₂ (fun ω => S ω * U) μ := hind.comp measurable_id hc.measurable
  have h₁ := h₂.measure_not_isSubspaceEmbedding_le_of_indepFun hindU hS₂
    (hc.measurable.comp_aemeasurable hS)
    (ae_of_all _ fun ω => (Matrix.rank_mul_le_right _ _).trans hU)
  have h₀ := h U hU
  unfold HasSubspaceEmbedding at h₀ ⊢
  refine (measureReal_mono (s₂ := {ω | ¬ IsSubspaceEmbedding (S₂ ω) (S ω * U) a₂ b₂} ∪
    {ω | ¬ IsSubspaceEmbedding (S ω) U a b}) fun ω hω => ?_).trans
    ((measureReal_union_le _ _).trans (add_le_add h₁ h₀))
  simp only [Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  exact hω (hcon.1.mul hcon.2 ha₂ hb₂)

/-- **Composition of OSIs**: for independent OSIs `S₂` and `S` for the same dimension, `S₂ * S`
is an OSI with constant `a₂ * a` and failure probability `δ₂ + δ`. -/
theorem IsObliviousSubspaceInjection.mul [IsProbabilityMeasure μ] [DecidableEq n]
    [DecidableEq k] {S₂ : Ω → Matrix l k 𝕜} (h₂ : IsObliviousSubspaceInjection S₂ d a₂ δ₂ μ)
    (h : IsObliviousSubspaceInjection S d a δ μ) (hind : IndepFun S₂ S μ)
    (hS₂ : AEMeasurable S₂ μ) (hS : AEMeasurable S μ) (ha₂ : 0 ≤ a₂) :
    IsObliviousSubspaceInjection (fun ω => S₂ ω * S ω) d (a₂ * a) (δ₂ + δ) μ := by
  refine ⟨h₂.isotropic.mul h.isotropic hind, fun U hU => ?_⟩
  have hc : Continuous fun A : Matrix k n 𝕜 => A * U := continuous_id.matrix_mul continuous_const
  have hindU : IndepFun S₂ (fun ω => S ω * U) μ := hind.comp measurable_id hc.measurable
  have h₁ := h₂.measure_not_isSubspaceInjection_le_of_indepFun hindU hS₂
    (hc.measurable.comp_aemeasurable hS)
    (ae_of_all _ fun ω => (Matrix.rank_mul_le_right _ _).trans hU)
  have h₀ := h.injection U hU
  unfold HasSubspaceInjection at h₀ ⊢
  refine (measureReal_mono (s₂ := {ω | ¬ IsSubspaceInjection (S₂ ω) (S ω * U) a₂} ∪
    {ω | ¬ IsSubspaceInjection (S ω) U a}) fun ω hω => ?_).trans
    ((measureReal_union_le _ _).trans (add_le_add h₁ h₀))
  simp only [Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  exact hω (hcon.1.mul hcon.2 ha₂)

end NLAlib
