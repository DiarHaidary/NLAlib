/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.PolarFrames
public import NLAlib.Probability.MatrixIntegral
public import NLAlib.RandomMatrix.Gaussian.Invariance

/-!
# Unitarily invariant laws of random matrices

A law $\nu$ on $n \times k$ matrices is **left unitarily invariant** when $\mathbf{U}\mathbf{Q}$
has law $\nu$ for $\mathbf{Q} \sim \nu$ and every unitary (over $\mathbb{R}$, orthogonal)
$\mathbf{U}$, and **right unitarily invariant** when $\mathbf{Q}\mathbf{V}$ does for every unitary
$\mathbf{V}$. These are the hypotheses of the characterization of the Haar frame
(`NLAlib/RandomMatrix/Haar/Uniqueness.lean`) and of the oblivious-embedding arguments for Gaussian
and Haar sketches. The standard Gaussian matrix is invariant on both sides.

Consequences proved here from invariance alone: a left invariant random matrix has mean zero, and
$\mathbb{E}[\mathbf{X}\mathbf{B}\mathbf{X}^{\mathsf{H}}]$ is a multiple of the identity,
$(\mathbb{E} \operatorname{tr}(\mathbf{X}\mathbf{B}\mathbf{X}^{\mathsf{H}}) / \lvert n \rvert) \,
\mathbf{I}$.

The classes are stated with `HasOrthonormalCols`, not with Mathlib's `SMulInvariantMeasure` of
`Matrix.unitaryGroup` (which would need a global action on rectangular matrices):
`docs/design/Mathlib-deviations.md` entry 14. The bridge to the bundled group is
`isLeftUnitarilyInvariant_iff`.

## Main results

* `NLAlib.IsLeftUnitarilyInvariant`, `NLAlib.IsRightUnitarilyInvariant`, with the bridges
  `NLAlib.isLeftUnitarilyInvariant_iff`, `NLAlib.isRightUnitarilyInvariant_iff`.
* `NLAlib.hasLaw_const_mul_of_isLeftUnitarilyInvariant`,
  `NLAlib.hasLaw_mul_const_of_isRightUnitarilyInvariant`: the `HasLaw` form consumers use.
* `NLAlib.isLeftUnitarilyInvariant_gaussianMatrix`,
  `NLAlib.isRightUnitarilyInvariant_gaussianMatrix`.
* `NLAlib.integral_eq_zero_of_isLeftUnitarilyInvariant`.
* `NLAlib.integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant`:
  $\mathbb{E}[\mathbf{X}\mathbf{B}\mathbf{X}^{\mathsf{H}}]$ is scalar.
* `NLAlib.hasLaw_prodMk_conjTranspose_mul_of_isLeftUnitarilyInvariant`: rotating one of two
  orthogonal blocks keeps their joint law.
* `NLAlib.integral_conjTranspose_mul_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant`: the
  coupled conjugation average is scalar.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n k : Type*} [Fintype n] [Fintype k]

/-! ### The interfaces -/

/-- A law on $n \times k$ matrices is **left unitarily invariant** when $\mathbf{U}\mathbf{Q}$ has
the law of $\mathbf{Q}$ for every unitary (over $\mathbb{R}$, orthogonal) $\mathbf{U}$. Mirrors
Mathlib's `Measure.IsMulLeftInvariant`, with the unitary given as a matrix with orthonormal columns
(`docs/design/Mathlib-deviations.md` entry 14; bridge `isLeftUnitarilyInvariant_iff`). Consumers use
`hasLaw_const_mul_of_isLeftUnitarilyInvariant`. -/
class IsLeftUnitarilyInvariant [DecidableEq n] (ν : Measure (Matrix n k 𝕜)) : Prop where
  /-- Left multiplication by a unitary preserves the law. -/
  map_mul_left_eq_self : ∀ U : Matrix n n 𝕜, HasOrthonormalCols U → ν.map (U * ·) = ν

/-- A law on $n \times k$ matrices is **right unitarily invariant** when $\mathbf{Q}\mathbf{V}$ has
the law of $\mathbf{Q}$ for every unitary (over $\mathbb{R}$, orthogonal) $\mathbf{V}$. Mirrors
Mathlib's `Measure.IsMulRightInvariant` (`docs/design/Mathlib-deviations.md` entry 14; bridge
`isRightUnitarilyInvariant_iff`). Consumers use `hasLaw_mul_const_of_isRightUnitarilyInvariant`. -/
class IsRightUnitarilyInvariant [DecidableEq k] (ν : Measure (Matrix n k 𝕜)) : Prop where
  /-- Right multiplication by a unitary preserves the law. -/
  map_mul_right_eq_self : ∀ V : Matrix k k 𝕜, HasOrthonormalCols V → ν.map (· * V) = ν

omit [Fintype k] in
/-- Bridge to Mathlib's unitary group: left unitary invariance is invariance under left
multiplication by every element of `Matrix.unitaryGroup n 𝕜`. -/
theorem isLeftUnitarilyInvariant_iff [DecidableEq n] {ν : Measure (Matrix n k 𝕜)} :
    IsLeftUnitarilyInvariant ν ↔
      ∀ U : Matrix.unitaryGroup n 𝕜, ν.map ((U : Matrix n n 𝕜) * ·) = ν :=
  ⟨fun h U => h.map_mul_left_eq_self U (hasOrthonormalCols_iff_mem_unitaryGroup.mpr U.2),
    fun h => ⟨fun U hU => h ⟨U, hasOrthonormalCols_iff_mem_unitaryGroup.mp hU⟩⟩⟩

omit [Fintype n] in
/-- Bridge to Mathlib's unitary group: right unitary invariance is invariance under right
multiplication by every element of `Matrix.unitaryGroup k 𝕜`. -/
theorem isRightUnitarilyInvariant_iff [DecidableEq k] {ν : Measure (Matrix n k 𝕜)} :
    IsRightUnitarilyInvariant ν ↔
      ∀ V : Matrix.unitaryGroup k 𝕜, ν.map (· * (V : Matrix k k 𝕜)) = ν :=
  ⟨fun h V => h.map_mul_right_eq_self V (hasOrthonormalCols_iff_mem_unitaryGroup.mpr V.2),
    fun h => ⟨fun V hV => h ⟨V, hasOrthonormalCols_iff_mem_unitaryGroup.mp hV⟩⟩⟩

omit [Fintype k] in
/-- A random matrix whose law is left unitarily invariant keeps its law under left multiplication
by a fixed unitary. -/
theorem hasLaw_const_mul_of_isLeftUnitarilyInvariant [DecidableEq n] {ν : Measure (Matrix n k 𝕜)}
    [IsLeftUnitarilyInvariant ν] {X : Ω → Matrix n k 𝕜} (hX : HasLaw X ν μ) {U : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) : HasLaw (fun ω => U * X ω) ν μ :=
  HasLaw.fun_comp (Y := (U * ·)) ⟨(measurable_const.matrix_mul measurable_id).aemeasurable,
    IsLeftUnitarilyInvariant.map_mul_left_eq_self U hU⟩ hX

omit [Fintype n] in
/-- A random matrix whose law is right unitarily invariant keeps its law under right
multiplication by a fixed unitary. -/
theorem hasLaw_mul_const_of_isRightUnitarilyInvariant [DecidableEq k] {ν : Measure (Matrix n k 𝕜)}
    [IsRightUnitarilyInvariant ν] {X : Ω → Matrix n k 𝕜} (hX : HasLaw X ν μ) {V : Matrix k k 𝕜}
    (hV : HasOrthonormalCols V) : HasLaw (fun ω => X ω * V) ν μ :=
  HasLaw.fun_comp (Y := (· * V)) ⟨(measurable_id.matrix_mul measurable_const).aemeasurable,
    IsRightUnitarilyInvariant.map_mul_right_eq_self V hV⟩ hX

/-! ### Gaussian matrices -/

/-- The standard Gaussian matrix is left orthogonally invariant. -/
instance isLeftUnitarilyInvariant_gaussianMatrix [DecidableEq n] :
    IsLeftUnitarilyInvariant (gaussianMatrix n k) :=
  ⟨fun _ hU => (hasLaw_const_mul_of_hasLaw_gaussianMatrix HasLaw.id hU.conjTranspose).map_eq⟩

/-- The standard Gaussian matrix is right orthogonally invariant. -/
instance isRightUnitarilyInvariant_gaussianMatrix [DecidableEq k] :
    IsRightUnitarilyInvariant (gaussianMatrix n k) :=
  ⟨fun _ hV => (hasLaw_mul_const_of_hasLaw_gaussianMatrix HasLaw.id hV).map_eq⟩

/-! ### Moments from invariance -/

/-- A left unitarily invariant random matrix has mean zero (take $\mathbf{U} = -\mathbf{I}$).
No integrability is needed: $\int (-\mathbf{X}) = -\int \mathbf{X}$ holds for the Bochner integral
in every case. -/
theorem integral_eq_zero_of_isLeftUnitarilyInvariant [DecidableEq n] [DecidableEq k]
    {ν : Measure (Matrix n k 𝕜)} [IsLeftUnitarilyInvariant ν] {X : Ω → Matrix n k 𝕜}
    (hX : HasLaw X ν μ) : ∫ ω, X ω ∂μ = 0 := by
  have hneg : HasOrthonormalCols (-1 : Matrix n n 𝕜) := by
    rw [hasOrthonormalCols_iff, Matrix.conjTranspose_neg, Matrix.conjTranspose_one,
      neg_mul_neg, Matrix.one_mul]
  have hX' : ∫ ω, (-1 : Matrix n n 𝕜) * X ω ∂μ = -∫ ω, X ω ∂μ := by
    simp only [Matrix.neg_mul, Matrix.one_mul]
    exact integral_neg _
  have h : ∫ ω, X ω ∂μ = -∫ ω, X ω ∂μ :=
    hX.integral_eq.trans
      ((hasLaw_const_mul_of_isLeftUnitarilyInvariant hX hneg).integral_eq.symm.trans hX')
  ext i j
  have hij := congrFun₂ h i j
  rw [Matrix.neg_apply] at hij
  rw [Matrix.zero_apply]
  linear_combination hij / 2

/-- **$\mathbb{E}[\mathbf{X}\mathbf{B}\mathbf{X}^{\mathsf{H}}]$ is scalar** for a left unitarily
invariant $n \times k$ random matrix $\mathbf{X}$ with $\mathbf{X}\mathbf{B}\mathbf{X}^{\mathsf{H}}$
integrable: it commutes with every unitary, so
$$\mathbb{E}[\mathbf{X}\mathbf{B}\mathbf{X}^{\mathsf{H}}]
= \frac{\mathbb{E} \operatorname{tr}(\mathbf{X}\mathbf{B}\mathbf{X}^{\mathsf{H}})}{\lvert n \rvert}
  \, \mathbf{I} \,.$$
The integrability hypothesis is needed: without it the left side is $\mathbf{0}$ while the trace
may still be integrable. Applied to the Gaussian it gives
$\mathbb{E}[\mathbf{G}\mathbf{B}\mathbf{G}^{\mathsf{T}}] = (\operatorname{tr} \mathbf{B}) \,
\mathbf{I}$; to the Haar frame, its second moments. [Meckes2019, Ch. 2] for Haar
measure on the orthogonal group; here any left invariant law, over any `RCLike` field. -/
theorem integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant [DecidableEq n]
    {ν : Measure (Matrix n k 𝕜)} [IsLeftUnitarilyInvariant ν] {X : Ω → Matrix n k 𝕜}
    (hX : HasLaw X ν μ) (B : Matrix k k 𝕜) (hint : Integrable (fun ω => X ω * B * (X ω)ᴴ) μ) :
    ∫ ω, X ω * B * (X ω)ᴴ ∂μ =
      ((∫ ω, (X ω * B * (X ω)ᴴ).trace ∂μ) / Fintype.card n) • (1 : Matrix n n 𝕜) := by
  have hm : Measurable fun Q : Matrix n k 𝕜 => Q * B * Qᴴ :=
    ((measurable_id.matrix_mul measurable_const).matrix_mul
      (Measurable.matrix_conjTranspose continuous_star.measurable measurable_id))
  have hf : AEStronglyMeasurable (fun Q : Matrix n k 𝕜 => Q * B * Qᴴ) ν :=
    hm.aestronglyMeasurable
  have key : ∀ U : Matrix n n 𝕜, HasOrthonormalCols U →
      U * (∫ ω, X ω * B * (X ω)ᴴ ∂μ) * Uᴴ = ∫ ω, X ω * B * (X ω)ᴴ ∂μ := by
    intro U hU
    have h1 := hX.integral_comp hf
    have h2 := (hasLaw_const_mul_of_isLeftUnitarilyInvariant hX hU).integral_comp hf
    have h3 : ∫ ω, U * X ω * B * (U * X ω)ᴴ ∂μ = U * (∫ ω, X ω * B * (X ω)ᴴ ∂μ) * Uᴴ := by
      have h4 : ∀ ω, U * X ω * B * (U * X ω)ᴴ = U * (X ω * B * (X ω)ᴴ) * Uᴴ := fun ω => by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      simp only [h4]
      rw [Matrix.integral_mul_const (hint.const_mul U), Matrix.integral_const_mul U hint]
    rw [← h3]
    exact h2.trans h1.symm
  refine (eq_smul_one_of_forall_mul_mul_conjTranspose_eq key).trans ?_
  rw [Matrix.integral_trace hint]

/-! ### Coupled invariance of two blocks -/

/-- The block-diagonal rotation $\mathbf{I} + \mathbf{V}_2(\mathbf{U} - \mathbf{I})
\mathbf{V}_2^{\mathsf{H}}$ of a frame $\mathbf{V}_2$ by a unitary $\mathbf{U}$ is unitary. -/
theorem HasOrthonormalCols.hasOrthonormalCols_one_add_mul_sub_one_mul_conjTranspose [DecidableEq n]
    {t : Type*} [Fintype t] [DecidableEq t] {V₂ : Matrix n t 𝕜} (hV₂ : HasOrthonormalCols V₂)
    {U : Matrix t t 𝕜} (hU : HasOrthonormalCols U) :
    HasOrthonormalCols (1 + V₂ * (U - 1) * V₂ᴴ) := by
  rw [hasOrthonormalCols_iff]
  have hM : (Uᴴ - 1) + (U - 1) + (Uᴴ - 1) * (U - 1) = 0 := by
    rw [sub_mul, mul_sub, mul_sub, hU.conjTranspose_mul_self, Matrix.mul_one, Matrix.one_mul,
      Matrix.one_mul]
    abel
  have hV := hV₂.conjTranspose_mul_self
  calc (1 + V₂ * (U - 1) * V₂ᴴ)ᴴ * (1 + V₂ * (U - 1) * V₂ᴴ)
      = 1 + V₂ * ((Uᴴ - 1) + (U - 1) + (Uᴴ - 1) * (V₂ᴴ * V₂) * (U - 1)) * V₂ᴴ := by
        simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, Matrix.add_mul,
          Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
        abel
    _ = 1 := by rw [hV, Matrix.mul_one, hM, Matrix.mul_zero, Matrix.zero_mul, add_zero]

omit [Fintype k] in
/-- **Rotating one block keeps the joint law**: for $\mathbf{X}$ with a left unitarily invariant
law, frames $\mathbf{V}_1$ ($n \times s$, any matrix) and $\mathbf{V}_2$ ($n \times t$, orthonormal
columns) with $\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$, and every unitary
$\mathbf{U}$ on $t$, the pair
$(\mathbf{V}_1^{\mathsf{H}}\mathbf{X}, \mathbf{U}\mathbf{V}_2^{\mathsf{H}}\mathbf{X})$ has the law
of $(\mathbf{V}_1^{\mathsf{H}}\mathbf{X}, \mathbf{V}_2^{\mathsf{H}}\mathbf{X})$. The rotation
$\mathbf{I} + \mathbf{V}_2(\mathbf{U} - \mathbf{I})\mathbf{V}_2^{\mathsf{H}}$ is unitary and fixes
the first block.
[EpperlyWebber2026, proofs of Theorem 2.1 and Proposition 5.7]; there for a random orthonormal
matrix and complementary frames. -/
theorem hasLaw_prodMk_conjTranspose_mul_of_isLeftUnitarilyInvariant [DecidableEq n]
    {s t : Type*} [Fintype t] [DecidableEq t] {ν : Measure (Matrix n k 𝕜)}
    [IsLeftUnitarilyInvariant ν] {X : Ω → Matrix n k 𝕜} (hX : HasLaw X ν μ)
    {V₁ : Matrix n s 𝕜} {V₂ : Matrix n t 𝕜} (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0)
    {U : Matrix t t 𝕜} (hU : HasOrthonormalCols U) :
    HasLaw (fun ω => (V₁ᴴ * X ω, U * (V₂ᴴ * X ω))) (ν.map fun x => (V₁ᴴ * x, V₂ᴴ * x)) μ := by
  set R := 1 + V₂ * (U - 1) * V₂ᴴ
  have hR : HasOrthonormalCols R :=
    hV₂.hasOrthonormalCols_one_add_mul_sub_one_mul_conjTranspose hU
  have h1 : V₁ᴴ * R = V₁ᴴ := by
    simp only [R, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, h₁₂, Matrix.zero_mul,
      add_zero]
  have h2 : V₂ᴴ * R = U * V₂ᴴ := by
    simp only [R, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hV₂.conjTranspose_mul_self,
      Matrix.one_mul, Matrix.sub_mul]
    abel
  have hg : Measurable fun x : Matrix n k 𝕜 => (V₁ᴴ * x, V₂ᴴ * x) :=
    (measurable_const.matrix_mul measurable_id).prodMk (measurable_const.matrix_mul measurable_id)
  have h := HasLaw.fun_comp (Y := fun x : Matrix n k 𝕜 => (V₁ᴴ * x, V₂ᴴ * x))
    ⟨hg.aemeasurable, rfl⟩ (hasLaw_const_mul_of_isLeftUnitarilyInvariant hX hR)
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [← Matrix.mul_assoc, h1, h2]

/-- **The coupled conjugation average**: for a random $\mathbf{X} \in \Bbbk^{n \times k}$ whose
law $\nu$ is left unitarily invariant (`IsLeftUnitarilyInvariant ν`), any
$\mathbf{V}_1 \in \Bbbk^{n \times s}$, any $\mathbf{V}_2 \in \Bbbk^{n \times t}$ with orthonormal
columns and $\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$, and measurable
$F : \Bbbk^{s \times k} \to \Bbbk^{k \times k}$, if
$\mathbf{Z} = \mathbf{V}_2^{\mathsf{H}}\mathbf{X}\,F(\mathbf{V}_1^{\mathsf{H}}\mathbf{X})\,
(\mathbf{V}_2^{\mathsf{H}}\mathbf{X})^{\mathsf{H}}$ is integrable then
$$\mathbb{E}\mathbf{Z} =
\frac{\mathbb{E}\operatorname{tr}\mathbf{Z}}{\lvert t\rvert}\,\mathbf{I}\,,$$
although the middle factor depends on $\mathbf{X}$. The case of a fixed middle factor is
`NLAlib.integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant`.
[EpperlyWebber2026, proof of Proposition 5.7]; there for a random orthonormal matrix. -/
theorem integral_conjTranspose_mul_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant
    [DecidableEq n] {s t : Type*} [Fintype t] [DecidableEq t]
    {ν : Measure (Matrix n k 𝕜)} [IsLeftUnitarilyInvariant ν] {X : Ω → Matrix n k 𝕜}
    (hX : HasLaw X ν μ) {V₁ : Matrix n s 𝕜} {V₂ : Matrix n t 𝕜} (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) {F : Matrix s k 𝕜 → Matrix k k 𝕜} (hF : Measurable F)
    (hint : Integrable (fun ω => V₂ᴴ * X ω * F (V₁ᴴ * X ω) * (V₂ᴴ * X ω)ᴴ) μ) :
    ∫ ω, V₂ᴴ * X ω * F (V₁ᴴ * X ω) * (V₂ᴴ * X ω)ᴴ ∂μ =
      ((∫ ω, (V₂ᴴ * X ω * F (V₁ᴴ * X ω) * (V₂ᴴ * X ω)ᴴ).trace ∂μ) / Fintype.card t) •
        (1 : Matrix t t 𝕜) := by
  set g := fun x : Matrix n k 𝕜 => (V₁ᴴ * x, V₂ᴴ * x)
  have hg : Measurable g :=
    (measurable_const.matrix_mul measurable_id).prodMk (measurable_const.matrix_mul measurable_id)
  set h := fun y : Matrix s k 𝕜 × Matrix t k 𝕜 => y.2 * F y.1 * y.2ᴴ
  have hh : Measurable h :=
    (measurable_snd.matrix_mul (hF.comp measurable_fst)).matrix_mul
      (Measurable.matrix_conjTranspose continuous_star.measurable measurable_snd)
  have h0 : HasLaw (fun ω => (V₁ᴴ * X ω, V₂ᴴ * X ω)) (ν.map g) μ :=
    HasLaw.fun_comp (Y := g) ⟨hg.aemeasurable, rfl⟩ hX
  have key : ∀ U : Matrix t t 𝕜, HasOrthonormalCols U →
      U * (∫ ω, V₂ᴴ * X ω * F (V₁ᴴ * X ω) * (V₂ᴴ * X ω)ᴴ ∂μ) * Uᴴ =
        ∫ ω, V₂ᴴ * X ω * F (V₁ᴴ * X ω) * (V₂ᴴ * X ω)ᴴ ∂μ := by
    intro U hU
    have hU' := hasLaw_prodMk_conjTranspose_mul_of_isLeftUnitarilyInvariant hX hV₂ h₁₂ hU
    have e1 := hU'.integral_comp hh.aestronglyMeasurable
    have e2 := h0.integral_comp hh.aestronglyMeasurable
    have e3 : ∫ ω, h (V₁ᴴ * X ω, U * (V₂ᴴ * X ω)) ∂μ =
        U * (∫ ω, V₂ᴴ * X ω * F (V₁ᴴ * X ω) * (V₂ᴴ * X ω)ᴴ ∂μ) * Uᴴ := by
      have e4 : ∀ ω, h (V₁ᴴ * X ω, U * (V₂ᴴ * X ω)) =
          U * (V₂ᴴ * X ω * F (V₁ᴴ * X ω) * (V₂ᴴ * X ω)ᴴ) * Uᴴ := fun ω => by
        simp only [h, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      simp only [e4]
      rw [Matrix.integral_mul_const (hint.const_mul U), Matrix.integral_const_mul U hint]
    rw [← e3]
    exact e1.trans e2.symm
  refine (eq_smul_one_of_forall_mul_mul_conjTranspose_eq key).trans ?_
  rw [Matrix.integral_trace hint]

end NLAlib
