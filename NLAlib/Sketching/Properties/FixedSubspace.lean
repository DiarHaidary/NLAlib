/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Law
public import NLAlib.Sketching.Properties.SubspaceEmbedding

/-!
# Random sketches of a fixed subspace

For a random sketch $\mathbf{S}$ with values in $\Bbbk^{k \times n}$ and a fixed
$\mathbf{U} \in \Bbbk^{n \times p}$, `NLAlib.HasSubspaceInjection S U a δ μ` and
`NLAlib.HasSubspaceEmbedding S U a b δ μ` say that $\mathbf{S}(\omega)$ fails to be a subspace
injection (embedding) for $\operatorname{range}\mathbf{U}$ with probability at most $\delta$:
$\mu\{\omega : \mathbf{S}(\omega) \text{ is not a subspace injection with constant } a\}
\le \delta$.
They are the conclusions of the fixed-subspace theorems (leverage-score sampling, a sketch of
$[\mathbf{A}, \mathbf{y}]$ in a solver) and the hypotheses of the oblivious constructors. Tails of
the Gram error (matrix Chernoff) and of the smallest singular value convert to them here.

Theorems that compare two events take `[IsFiniteMeasure μ]`, since `μ.real` of a set of infinite
measure is $0$. Design: `docs/design/Sketching-S1.md` §3.2.

## Main definitions

* `NLAlib.HasSubspaceInjection`, `NLAlib.HasSubspaceEmbedding`.

## Main results

* `NLAlib.HasSubspaceInjection.hasSubspaceEmbedding`: joining the two halves.
* `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_measureReal_le`: from a Gram-error tail.
* `NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_measureReal_le`: from a $\sigma_{\min}$
  tail.
* `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_zero_of_measureReal_le`: the upper half from a
  $\sigma_{\max}$ tail.
* `NLAlib.HasSubspaceEmbedding.of_range_le`: passing to a smaller subspace.
* `ProbabilityTheory.HasLaw.hasSubspaceEmbedding_iff`: the predicates depend only on the law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n p q : Type*} [Fintype k] [Fintype n] {S : Ω → Matrix k n 𝕜}
  {U : Matrix n p 𝕜} {a a' b b' δ δ' ε : ℝ}

/-- $\mathbf{S}$ is a **subspace injection for $\operatorname{range}\mathbf{U}$ with probability
$1 - \delta$**: the event that $\mathbf{S}(\omega)$ is not a subspace injection with constant $a$
has probability at most $\delta$. -/
def HasSubspaceInjection (S : Ω → Matrix k n 𝕜) (U : Matrix n p 𝕜) (a δ : ℝ) (μ : Measure Ω) :
    Prop :=
  μ.real {ω | ¬ IsSubspaceInjection (S ω) U a} ≤ δ

/-- $\mathbf{S}$ is a **subspace embedding for $\operatorname{range}\mathbf{U}$ with probability
$1 - \delta$**: the event that $\mathbf{S}(\omega)$ is not a subspace embedding with constants $a$,
$b$ has probability at most $\delta$. -/
def HasSubspaceEmbedding (S : Ω → Matrix k n 𝕜) (U : Matrix n p 𝕜) (a b δ : ℝ)
    (μ : Measure Ω) : Prop :=
  μ.real {ω | ¬ IsSubspaceEmbedding (S ω) U a b} ≤ δ

/-- `HasSubspaceInjection` depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.hasSubspaceInjection_iff {ν : Measure (Matrix k n 𝕜)}
    (hS : HasLaw S ν μ) : HasSubspaceInjection S U a δ μ ↔ HasSubspaceInjection id U a δ ν := by
  unfold HasSubspaceInjection
  rw [hS.measureReal_eq (p := fun A => ¬ IsSubspaceInjection A U a)
    (measurableSet_setOf_isSubspaceInjection U a).compl]
  rfl

/-- `HasSubspaceEmbedding` depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.hasSubspaceEmbedding_iff {ν : Measure (Matrix k n 𝕜)}
    (hS : HasLaw S ν μ) :
    HasSubspaceEmbedding S U a b δ μ ↔ HasSubspaceEmbedding id U a b δ ν := by
  unfold HasSubspaceEmbedding
  rw [hS.measureReal_eq (p := fun A => ¬ IsSubspaceEmbedding A U a b)
    (measurableSet_setOf_isSubspaceEmbedding U a b).compl]
  rfl

/-- A random subspace embedding is a random subspace injection with the same lower constant
and failure probability. -/
theorem HasSubspaceEmbedding.hasSubspaceInjection [IsFiniteMeasure μ]
    (h : HasSubspaceEmbedding S U a b δ μ) : HasSubspaceInjection S U a δ μ := by
  exact (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω h' => hω h'.lower)).trans h

/-- **Joining the halves**: a random subspace injection whose upper half fails with probability
at most $\delta'$ is a random subspace embedding with failure probability $\delta + \delta'$
(union bound). -/
theorem HasSubspaceInjection.hasSubspaceEmbedding (h : HasSubspaceInjection S U a δ μ)
    (hb : μ.real {ω | ¬ (S ω * U)ᴴ * (S ω * U) ≤ b • (Uᴴ * U)} ≤ δ') :
    HasSubspaceEmbedding S U a b (δ + δ') μ := by
  have e : {ω | ¬ IsSubspaceEmbedding (S ω) U a b} =
      {ω | ¬ IsSubspaceInjection (S ω) U a} ∪ {ω | ¬ (S ω * U)ᴴ * (S ω * U) ≤ b • (Uᴴ * U)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    exact ⟨fun hω => not_and_or.1 fun h' => hω ⟨h'.1, h'.2⟩,
      fun hω h' => hω.elim (· h'.lower) (· h'.upper)⟩
  unfold HasSubspaceEmbedding
  rw [e]
  exact (measureReal_union_le _ _).trans (add_le_add h hb)

/-- **From a Gram-error tail**: for $\mathbf{U}$ with orthonormal columns, a tail
$\mathbb{P}(\varepsilon \le \|(\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U} -
\mathbf{I}\|_2) \le \delta$ gives a random $\varepsilon$-embedding with failure probability
$\delta$. The form matrix Chernoff and matrix Bernstein bounds produce. -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_of_measureReal_le [IsFiniteMeasure μ]
    [Fintype p] [DecidableEq p] (hU : HasOrthonormalCols U)
    (h : μ.real {ω | ε ≤ specNorm ((S ω * U)ᴴ * (S ω * U) - 1)} ≤ δ) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε) δ μ := by
  refine (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω => ?_)).trans h
  by_contra hlt
  rw [not_le] at hlt
  exact hω ((hU.isSubspaceEmbedding_iff_specNorm_le
    ((specNorm_nonneg _).trans hlt.le)).2 hlt.le)

/-- **From a smallest-singular-value tail**: for $\mathbf{U}$ with orthonormal columns, a tail
$\mathbb{P}(\sigma_{\min}(\mathbf{S}\mathbf{U})^2 \le a) \le \delta$ gives a random subspace
injection with constant $a$; the smallest singular value is index $j$ with
$j + 1 = \lvert p \rvert$. -/
theorem HasOrthonormalCols.hasSubspaceInjection_of_measureReal_le [IsFiniteMeasure μ]
    [Fintype p] [DecidableEq p] (hU : HasOrthonormalCols U) {j : ℕ} (hj : j + 1 = Fintype.card p)
    (h : μ.real {ω | singularValues (S ω * U) j ^ 2 ≤ a} ≤ δ) :
    HasSubspaceInjection S U a δ μ := by
  refine (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω => ?_)).trans h
  rw [hU.isSubspaceInjection_iff_le_sq_singularValues hj, not_le] at hω
  exact hω.le

/-- **From a largest-singular-value tail**: for $\mathbf{U}$ with orthonormal columns, a tail
$\mathbb{P}(b \le \sigma_0(\mathbf{S}\mathbf{U})^2) \le \delta$ gives the upper half
$(\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U}
\preceq b\,\mathbf{U}^{\mathsf{H}}\mathbf{U}$ with failure probability $\delta$, the lower
constant $0$ holding surely. The form matrix Chernoff's upper tail produces. No nonemptiness of
`p` is needed: for empty `p` the failure event is empty. -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_zero_of_measureReal_le [IsFiniteMeasure μ]
    [Fintype p] [DecidableEq p] (hU : HasOrthonormalCols U)
    (h : μ.real {ω | b ≤ singularValues (S ω * U) 0 ^ 2} ≤ δ) :
    HasSubspaceEmbedding S U 0 b δ μ := by
  refine (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω => ?_)).trans h
  by_contra hlt
  refine hω ⟨isSubspaceInjection_of_nonpos _ _ le_rfl, ?_⟩
  rw [hU.conjTranspose_mul_self]
  refine (conjTranspose_mul_self_le_specNorm_sq_smul_one _).trans (smul_one_le_smul_one ?_)
  rw [← singularValues_zero_eq_specNorm]
  exact (not_le.1 hlt).le

/-- A random subspace injection is one with any smaller constant and any larger failure
probability. -/
theorem HasSubspaceInjection.mono [IsFiniteMeasure μ] (h : HasSubspaceInjection S U a δ μ)
    (ha : a' ≤ a) (hδ : δ ≤ δ') : HasSubspaceInjection S U a' δ' μ := by
  exact (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω h' => hω (h'.mono ha))).trans
    (h.trans hδ)

/-- A random subspace embedding is one with any weaker constants and any larger failure
probability. -/
theorem HasSubspaceEmbedding.mono [IsFiniteMeasure μ] (h : HasSubspaceEmbedding S U a b δ μ)
    (ha : a' ≤ a) (hb : b ≤ b') (hδ : δ ≤ δ') : HasSubspaceEmbedding S U a' b' δ' μ := by
  exact (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω h' => hω (h'.mono ha hb))).trans
    (h.trans hδ)

/-- A random subspace injection for $\operatorname{range}\mathbf{U}$ is one for every subspace
$\operatorname{range}\mathbf{V} \subseteq \operatorname{range}\mathbf{U}$. -/
theorem HasSubspaceInjection.of_range_le [IsFiniteMeasure μ] [Fintype p] [Fintype q]
    (h : HasSubspaceInjection S U a δ μ) {V : Matrix n q 𝕜}
    (hVU : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    HasSubspaceInjection S V a δ μ := by
  exact (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω h' =>
    hω (h'.of_range_le hVU))).trans h

/-- A random subspace embedding for $\operatorname{range}\mathbf{U}$ is one for every subspace
$\operatorname{range}\mathbf{V} \subseteq \operatorname{range}\mathbf{U}$. -/
theorem HasSubspaceEmbedding.of_range_le [IsFiniteMeasure μ] [Fintype p] [Fintype q]
    (h : HasSubspaceEmbedding S U a b δ μ) {V : Matrix n q 𝕜}
    (hVU : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    HasSubspaceEmbedding S V a b δ μ := by
  exact (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω h' =>
    hω (h'.of_range_le hVU))).trans h

end NLAlib
