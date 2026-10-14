/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Haar.Basic

/-!
# Transfer between Gaussian and Haar test matrices

For a fixed $\mathbf{A}$ and a Haar frame $\mathbf{Q}$, the range projector of
$\mathbf{A}\mathbf{Q}$ has the law of the range projector of $\mathbf{A}\mathbf{G}$ for a standard
Gaussian $\mathbf{G}$ of the same shape: `polarFactor G` is $\mathbf{G}\mathbf{T}$ with
$\mathbf{T}$ invertible on the range, so $\mathbf{A}\mathbf{G}$ and $\mathbf{A}$ (`polarFactor G`)
have the same column space. Every
statistic of the column space of a sketch is a function of its range projector, so every
range-finder statement proved for a Gaussian test matrix (expectations, tails, ranks) holds
verbatim for a Haar test matrix, in every shape and rank.

## Main results

* `NLAlib.hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`: the law of
  $\mathbf{P}_{\mathbf{A}\mathbf{Q}}$.
* `NLAlib.integral_comp_rangeProjector_mul_of_hasLaw_haarFrame`: the expectation form, with values
  in any real Banach space.
* `NLAlib.ae_rank_mul_eq_min_of_hasLaw_haarFrame`:
  $\operatorname{rank}(\mathbf{A}\mathbf{Q}) = \min(\operatorname{rank} \mathbf{A},
  \lvert k \rvert)$ almost surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k : Type*} [Fintype n]
  [Fintype k] {X : Ω → Matrix n k ℝ}

/-- The range projector of $\mathbf{A}\mathbf{Q}$ is measurable in $\mathbf{Q}$. -/
private theorem measurable_rangeProjector_mul {m : Type*} [Fintype m] (A : Matrix m n ℝ) :
    Measurable fun Q : Matrix n k ℝ => rangeProjector (A * Q) :=
  measurable_rangeProjector.comp (measurable_const.matrix_mul measurable_id)

/-- **Transfer between Gaussian and Haar test matrices**: the range projector
$\mathbf{P}_{\mathbf{A}\mathbf{Q}}$ for a Haar frame $\mathbf{Q}$ has the law of
$\mathbf{P}_{\mathbf{A}\mathbf{G}}$ for a standard Gaussian $\mathbf{G}$. Every shape and rank; no
$\lvert k \rvert \le \lvert n \rvert$ is needed. A statistic of
$\operatorname{range}(\mathbf{A}\mathbf{Q})$ is a measurable function of the projector, so it
transfers by `HasLaw.comp`; this covers the residual $(\mathbf{I} - \mathbf{P})\mathbf{A}$ of the
range finder, the power-iteration range finder (take
$(\mathbf{A}\mathbf{A}^{\mathsf{H}})^q \mathbf{A}$ for $\mathbf{A}$) and the Nyström approximation
of a positive semidefinite $\mathbf{A}$ (take $\mathbf{A}^{1/2}$, `CFC.sqrt A`, for $\mathbf{A}$).
[HalkoMartinssonTropp2011, §4, §10], where the range finder is analysed for Gaussian test
matrices.
Result: gaussian-haar-range-transfer -/
theorem hasLaw_rangeProjector_mul_of_hasLaw_haarFrame [DecidableEq k] {m : Type*} [Fintype m]
    (A : Matrix m n ℝ) (hX : HasLaw X (haarFrame n k) μ) :
    HasLaw (fun ω => rangeProjector (A * X ω))
      ((gaussianMatrix n k).map fun G => rangeProjector (A * G)) μ := by
  have hm := measurable_rangeProjector_mul (k := k) A
  refine HasLaw.fun_comp (Y := fun Q => rangeProjector (A * Q)) ⟨hm.aemeasurable, ?_⟩ hX
  rw [haarFrame, Measure.map_map hm measurable_polarFactor]
  congr 1
  funext G
  exact rangeProjector_mul_polarFactor A G

/-- **Expectations transfer between Gaussian and Haar test matrices**: for any strongly
measurable statistic $f$ of the range projector, with values in any real Banach space,
$\mathbb{E} f(\mathbf{P}_{\mathbf{A}\mathbf{Q}}) = \mathbb{E} f(\mathbf{P}_{\mathbf{A}\mathbf{G}})$
for a Haar frame $\mathbf{Q}$ and a standard Gaussian $\mathbf{G}$ on any two probability spaces. No
integrability hypothesis: both sides integrate `f` against one law. This is the form a range-finder
consumer applies, including to the power-iteration and Nyström sketches
(`hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`). -/
theorem integral_comp_rangeProjector_mul_of_hasLaw_haarFrame [DecidableEq k] {m : Type*}
    [Fintype m] (A : Matrix m n ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Matrix m m ℝ → E} (hf : StronglyMeasurable f) (hX : HasLaw X (haarFrame n k) μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} {G : Ω' → Matrix n k ℝ}
    (hG : HasLaw G (gaussianMatrix n k) μ') :
    ∫ ω, f (rangeProjector (A * X ω)) ∂μ = ∫ ω', f (rangeProjector (A * G ω')) ∂μ' := by
  have hm := measurable_rangeProjector_mul (k := k) A
  have hG' : HasLaw (fun ω' => rangeProjector (A * G ω'))
      ((gaussianMatrix n k).map fun G => rangeProjector (A * G)) μ' :=
    HasLaw.fun_comp (Y := fun Q => rangeProjector (A * Q)) ⟨hm.aemeasurable, rfl⟩ hG
  exact ((hasLaw_rangeProjector_mul_of_hasLaw_haarFrame A hX).integral_comp
    hf.aestronglyMeasurable).trans (hG'.integral_comp hf.aestronglyMeasurable).symm

/-- **The rank of a Haar sketch**:
$\operatorname{rank}(\mathbf{A}\mathbf{Q}) = \min(\operatorname{rank} \mathbf{A}, \lvert k \rvert)$
almost surely, for an $n \times k$ Haar frame $\mathbf{Q}$, in every shape. The Haar twin of
`ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`. -/
theorem ae_rank_mul_eq_min_of_hasLaw_haarFrame [DecidableEq k] {m : Type*} [Finite m]
    (A : Matrix m n ℝ) (hX : HasLaw X (haarFrame n k) μ) :
    ∀ᵐ ω ∂μ, (A * X ω).rank = min A.rank (Fintype.card k) := by
  have := Fintype.ofFinite m
  have hP := hasLaw_rangeProjector_mul_of_hasLaw_haarFrame A hX
  have hs : MeasurableSet {P : Matrix m m ℝ | P.rank = min A.rank (Fintype.card k)} :=
    measurable_rank (measurableSet_singleton _)
  have hm := measurable_rangeProjector_mul (k := k) A
  have hG : ∀ᵐ P ∂(gaussianMatrix n k).map fun G => rangeProjector (A * G),
      P.rank = min A.rank (Fintype.card k) := by
    refine (ae_map_iff hm.aemeasurable hs).2 ?_
    filter_upwards [ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix A
      (HasLaw.id (μ := gaussianMatrix n k))] with G hG
    rw [rank_rangeProjector]
    exact hG
  rw [← hP.map_eq] at hG
  filter_upwards [ae_of_ae_map hP.aemeasurable hG] with ω hω
  rwa [rank_rangeProjector] at hω

end NLAlib
