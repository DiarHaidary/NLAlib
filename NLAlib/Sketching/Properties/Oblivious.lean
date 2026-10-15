/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Perturbation.Continuity
public import NLAlib.Sketching.Properties.FixedSubspace
public import NLAlib.Sketching.Properties.Isotropic

/-!
# Oblivious subspace embeddings and injections

A random sketch $\mathbf{S}$ with values in $\Bbbk^{k \times n}$ is an *oblivious subspace
embedding* (OSE) for dimension $d$ when, for every fixed subspace of dimension at most $d$, it is
a subspace embedding with probability $1 - \delta$; it is an *oblivious subspace injection* (OSI)
when it is isotropic and the lower half holds with probability $1 - \delta$ on every such
subspace. Subspaces are column spaces of square matrices $\mathbf{U} \in \Bbbk^{n \times n}$ with
$\operatorname{rank}\mathbf{U} \le d$; `NLAlib.IsObliviousSubspaceEmbedding.hasSubspaceEmbedding`
applies the predicate to $\mathbf{U}$ of any shape.

Every sketching family concludes one of these predicates, through the constructor from
$\mathbf{U} \in \Bbbk^{n \times p}$ with orthonormal columns; every consumer takes one. The
predicates transfer to a random subspace independent of the sketch, and compose over independent
sketches.

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

/-- **Oblivious subspace embedding** for dimension $d$: for every
$\mathbf{U} \in \Bbbk^{n \times n}$ of rank at most $d$, $\mathbf{S}$ is a subspace embedding for
$\operatorname{range}\mathbf{U}$ with constants $a$, $b$ with probability $1 - \delta$.
[Woodruff2014, Definition 2], there $1 \mp \varepsilon$; [CamanoEpperlyMeyerTropp2025,
Definition 1.1], there $\alpha$, $\beta$; both for subspaces of dimension exactly $d$, here at
most $d$.
Result: ose-def -/
def IsObliviousSubspaceEmbedding (S : Ω → Matrix k n 𝕜) (d : ℕ) (a b δ : ℝ) (μ : Measure Ω) :
    Prop :=
  ∀ U : Matrix n n 𝕜, U.rank ≤ d → HasSubspaceEmbedding S U a b δ μ

/-- **Oblivious subspace injection** for dimension $d$: $\mathbf{S}$ is isotropic and, for every
$\mathbf{U} \in \Bbbk^{n \times n}$ of rank at most $d$, a subspace injection for
$\operatorname{range}\mathbf{U}$ with constant $a$ with probability $1 - \delta$.
[CamanoEpperlyMeyerTropp2025, Definition 1.2]; there $\delta = 1/20$ and $\alpha \in (0, 1]$,
here any $\delta$ and $a$.
Result: osi-def -/
structure IsObliviousSubspaceInjection [DecidableEq n] (S : Ω → Matrix k n 𝕜) (d : ℕ) (a δ : ℝ)
    (μ : Measure Ω) : Prop where
  /-- The sketch is isotropic. -/
  isotropic : IsIsotropicSketch S μ
  /-- The lower half holds with probability $1 - \delta$ on every subspace of dimension at most
  $d$. -/
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

/-- An OSE applies to the column space of a matrix of any shape and rank at most $d$. -/
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

/-- An OSI applies to the column space of a matrix of any shape and rank at most $d$. -/
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

/-- **The OSE constructor**: for $\lvert p \rvert \le \lvert n \rvert$, a sketch that is a random
subspace embedding for every $\mathbf{U}$ with orthonormal columns indexed by $p$ is an OSE for
dimension $\lvert p \rvert$. The constructor every sketching family uses. -/
theorem IsObliviousSubspaceEmbedding.of_hasOrthonormalCols [IsFiniteMeasure μ] [Fintype p]
    [DecidableEq p] (hp : Fintype.card p ≤ Fintype.card n)
    (h : ∀ U : Matrix n p 𝕜, HasOrthonormalCols U → HasSubspaceEmbedding S U a b δ μ) :
    IsObliviousSubspaceEmbedding S (Fintype.card p) a b δ μ := by
  intro U hU
  obtain ⟨Q, hQ, hUQ⟩ := exists_hasOrthonormalCols_range_le U hU hp
  exact (h Q hQ).of_range_le hUQ

/-- **The OSI constructor**: for $\lvert p \rvert \le \lvert n \rvert$, an isotropic sketch that is
a random subspace injection for every $\mathbf{U}$ with orthonormal columns indexed by $p$ is an
OSI for dimension $\lvert p \rvert$. -/
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

/-- **Transfer of an OSE to an independent random subspace**: if $\mathbf{V}$ is independent of
$\mathbf{S}$ and has rank at most $d$ almost surely, $\mathbf{S}(\omega)$ fails to embed
$\operatorname{range}\mathbf{V}(\omega)$ with probability at most $\delta$. Fubini on the closed
set of `NLAlib.isClosed_setOf_isSubspaceEmbedding`: the sections bound
`ProbabilityTheory.IndepFun.measureReal_mem_le_add` with the good set of rank at most $d$. -/
theorem IsObliviousSubspaceEmbedding.measure_not_isSubspaceEmbedding_le_of_indepFun
    [IsProbabilityMeasure μ] [Fintype q] (h : IsObliviousSubspaceEmbedding S d a b δ μ)
    {V : Ω → Matrix n q 𝕜} (hind : IndepFun S V μ) (hS : AEMeasurable S μ)
    (hV : AEMeasurable V μ) (hrank : ∀ᵐ ω ∂μ, (V ω).rank ≤ d) :
    μ.real {ω | ¬ IsSubspaceEmbedding (S ω) (V ω) a b} ≤ δ := by
  have hδ : 0 ≤ δ := measureReal_nonneg.trans (h 0 (by simp))
  have h' := hind.measureReal_mem_le_add hS hV
    (isClosed_setOf_isSubspaceEmbedding a b).isOpen_compl.measurableSet
    (isClosed_setOf_rank_le d).measurableSet hδ (fun B hB => h.hasSubspaceEmbedding hB)
    (δ₂ := 0) ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 (ae_iff.1 hrank)).le
  rwa [add_zero] at h'

/-- **Transfer of an OSI to an independent random subspace**: if $\mathbf{V}$ is independent of
$\mathbf{S}$ and has rank at most $d$ almost surely, $\mathbf{S}(\omega)$ fails to inject
$\operatorname{range}\mathbf{V}(\omega)$ with probability at most $\delta$. -/
theorem IsObliviousSubspaceInjection.measure_not_isSubspaceInjection_le_of_indepFun
    [IsProbabilityMeasure μ] [DecidableEq n] [Fintype q]
    (h : IsObliviousSubspaceInjection S d a δ μ) {V : Ω → Matrix n q 𝕜} (hind : IndepFun S V μ)
    (hS : AEMeasurable S μ) (hV : AEMeasurable V μ) (hrank : ∀ᵐ ω ∂μ, (V ω).rank ≤ d) :
    μ.real {ω | ¬ IsSubspaceInjection (S ω) (V ω) a} ≤ δ := by
  have hδ : 0 ≤ δ := measureReal_nonneg.trans (h.injection 0 (by simp))
  have h' := hind.measureReal_mem_le_add hS hV
    (isClosed_setOf_isSubspaceInjection a).isOpen_compl.measurableSet
    (isClosed_setOf_rank_le d).measurableSet hδ (fun B hB => h.hasSubspaceInjection hB)
    (δ₂ := 0) ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 (ae_iff.1 hrank)).le
  rwa [add_zero] at h'

/-! ### Composition -/

/-- **Composition of OSEs**: for independent OSEs $\mathbf{S}_2$ and $\mathbf{S}$ for the same
dimension, the constants $a_2, b_2$ of $\mathbf{S}_2$ nonnegative, $\mathbf{S}_2\mathbf{S}$ is an
OSE with constants $a_2 a$, $b_2 b$ and failure probability $\delta_2 + \delta$. -/
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

/-- **Composition of OSIs**: for independent OSIs $\mathbf{S}_2$ and $\mathbf{S}$ for the same
dimension, the constant $a_2$ of $\mathbf{S}_2$ nonnegative, $\mathbf{S}_2\mathbf{S}$ is an OSI
with constant $a_2 a$ and failure probability $\delta_2 + \delta$. -/
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
