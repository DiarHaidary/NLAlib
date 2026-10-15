/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Haar.Uniqueness

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
* `NLAlib.hasLaw_rangeProjector_mul_of_isLeftUnitarilyInvariant`,
  `NLAlib.ae_rank_mul_eq_min_of_isLeftUnitarilyInvariant`: the same for every full-rank test
  matrix with a left unitarily invariant law.
* `NLAlib.integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant`,
  `NLAlib.measureReal_eq_measureReal_gaussianMatrix_of_isLeftUnitarilyInvariant`: expectations
  and tails of statistics of the range projector, in the form a range-finder consumer applies.
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

/-! ### Rotation-invariant test matrices -/

/-- **Every full-rank rotation-invariant test matrix has the Gaussian law of the range**: if the
law $\nu$ of $\mathbf{X}$ is a left unitarily invariant probability measure and $\mathbf{X}$ has
full column rank almost surely, then $\mathbf{P}_{\mathbf{A}\mathbf{X}}$ has the law of
$\mathbf{P}_{\mathbf{A}\mathbf{G}}$ for a standard Gaussian $\mathbf{G}$ of the same shape.
The polar factor of $\mathbf{X}$ is a Haar frame
(`NLAlib.hasLaw_polarFactor_of_isLeftUnitarilyInvariant`) with the same range sketch, and
`NLAlib.hasLaw_rangeProjector_mul_of_hasLaw_haarFrame` applies. The hypothesis class is the
full-rank rotation-invariant embedding of [EpperlyWebber2026, p. 2]; it is unsatisfiable for
$\lvert k \rvert > \lvert n \rvert$, where the Haar frame is handled directly.
Result: gaussian-haar-range-transfer -/
theorem hasLaw_rangeProjector_mul_of_isLeftUnitarilyInvariant [DecidableEq n] {m : Type*}
    [Fintype m] {ν : Measure (Matrix n k ℝ)} [IsProbabilityMeasure ν]
    [IsLeftUnitarilyInvariant ν] (A : Matrix m n ℝ) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) :
    HasLaw (fun ω => rangeProjector (A * X ω))
      ((gaussianMatrix n k).map fun G => rangeProjector (A * G)) μ := by
  classical
  have h := hasLaw_rangeProjector_mul_of_hasLaw_haarFrame A
    (hasLaw_polarFactor_of_isLeftUnitarilyInvariant hX hXr)
  simp only [rangeProjector_mul_polarFactor] at h
  exact h

/-- **The rank of a rotation-invariant sketch**:
$\operatorname{rank}(\mathbf{A}\mathbf{X}) = \min(\operatorname{rank} \mathbf{A}, \lvert k \rvert)$
almost surely, for $\mathbf{X}$ with a left unitarily invariant law and full column rank almost
surely. The rotation-invariant twin of `ae_rank_mul_eq_min_of_hasLaw_haarFrame`, through the
polar factor, whose sketch has the same range. -/
theorem ae_rank_mul_eq_min_of_isLeftUnitarilyInvariant [DecidableEq n] {m : Type*} [Finite m]
    {ν : Measure (Matrix n k ℝ)} [IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]
    (A : Matrix m n ℝ) (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) :
    ∀ᵐ ω ∂μ, (A * X ω).rank = min A.rank (Fintype.card k) := by
  classical
  have := Fintype.ofFinite m
  filter_upwards [ae_rank_mul_eq_min_of_hasLaw_haarFrame A
    (hasLaw_polarFactor_of_isLeftUnitarilyInvariant hX hXr)] with ω hω
  rw [← hω, ← rank_rangeProjector, ← rank_rangeProjector (A * polarFactor (X ω)),
    rangeProjector_mul_polarFactor]

/-- **Expectations transfer from a rotation-invariant test matrix to the Gaussian**: if the law of
$\mathbf{X}$ is a left unitarily invariant probability measure and $\mathbf{X}$ has full column
rank almost surely, then for every $f$ that factors through the range projector,
$f(\mathbf{Y}) = g(\mathbf{P}_{\mathbf{A}\mathbf{Y}})$ with $g$ measurable,
$\mathbb{E} f(\mathbf{X}) = \mathbb{E} f(\mathbf{G})$ for a standard Gaussian $\mathbf{G}$ of the
same shape. No integrability hypothesis: both sides integrate $g$ against one law. -/
theorem integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant [DecidableEq n]
    {m : Type*} [Fintype m] {ν : Measure (Matrix n k ℝ)} [IsProbabilityMeasure ν]
    [IsLeftUnitarilyInvariant ν] (A : Matrix m n ℝ) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {f : Matrix n k ℝ → ℝ}
    {g : Matrix m m ℝ → ℝ} (hg : Measurable g) (hfg : ∀ Y, f Y = g (rangeProjector (A * Y))) :
    ∫ ω, f (X ω) ∂μ = ∫ G, f G ∂(gaussianMatrix n k) := by
  classical
  have h := integral_comp_rangeProjector_mul_of_hasLaw_haarFrame A hg.stronglyMeasurable
    (hasLaw_polarFactor_of_isLeftUnitarilyInvariant hX hXr) (HasLaw.id (μ := gaussianMatrix n k))
  simp only [rangeProjector_mul_polarFactor, id] at h
  simp only [hfg]
  exact h

/-- **Tails transfer from a rotation-invariant test matrix to the Gaussian**: with the hypotheses
of `NLAlib.integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant`, for every $f$ that
factors measurably through the range projector and every $c$,
$\mathbb{P}\{f(\mathbf{X}) > c\} = \mathbb{P}\{f(\mathbf{G}) > c\}$ for a standard Gaussian
$\mathbf{G}$ of the same shape. -/
theorem measureReal_eq_measureReal_gaussianMatrix_of_isLeftUnitarilyInvariant [DecidableEq n]
    {m : Type*} [Fintype m] {ν : Measure (Matrix n k ℝ)} [IsProbabilityMeasure ν]
    [IsLeftUnitarilyInvariant ν] (A : Matrix m n ℝ) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {f : Matrix n k ℝ → ℝ}
    {g : Matrix m m ℝ → ℝ} (hg : Measurable g) (hfg : ∀ Y, f Y = g (rangeProjector (A * Y)))
    (c : ℝ) :
    μ.real {ω | ¬ f (X ω) ≤ c} = (gaussianMatrix n k).real {G | ¬ f G ≤ c} := by
  have hs : MeasurableSet {P : Matrix m m ℝ | ¬ g P ≤ c} :=
    (measurableSet_le hg measurable_const).compl
  have hG : HasLaw (fun G : Matrix n k ℝ => rangeProjector (A * G))
      ((gaussianMatrix n k).map fun G => rangeProjector (A * G)) (gaussianMatrix n k) :=
    ⟨(measurable_rangeProjector_mul A).aemeasurable, rfl⟩
  simp only [hfg]
  rw [(hasLaw_rangeProjector_mul_of_isLeftUnitarilyInvariant A hX hXr).measureReal_eq hs,
    hG.measureReal_eq hs]

end NLAlib
