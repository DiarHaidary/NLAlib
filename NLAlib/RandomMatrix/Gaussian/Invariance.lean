/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Probability.IdentDistrib
public import NLAlib.Matrix.Basic.Orthonormal
public import NLAlib.Matrix.Basic.Selection
public import NLAlib.Matrix.Structured.Kronecker
public import NLAlib.RandomMatrix.Gaussian.Basic

/-!
# Orthogonal invariance of Gaussian matrices

A standard Gaussian matrix $\mathbf{G}$ keeps its law under multiplication by matrices with
orthonormal rows on the left and orthonormal columns on the right: $\mathbf{U}\mathbf{G}\mathbf{V}$
is a standard Gaussian matrix when $\mathbf{U}\mathbf{U}^{\mathsf{H}} = \mathbf{I}$ and
$\mathbf{V}^{\mathsf{H}}\mathbf{V} = \mathbf{I}$. Special cases: $\mathbf{U}\mathbf{G}$,
$\mathbf{G}\mathbf{V}$, the conjugate transpose $\mathbf{G}^{\mathsf{H}}$, submatrices on injective
index maps, and $\mathbf{G}\mathbf{x}$ for a unit vector $\mathbf{x}$. Blocks
$\mathbf{V}_1^{\mathsf{H}}\mathbf{G}$ and $\mathbf{V}_2^{\mathsf{H}}\mathbf{G}$ along orthogonal
frames are independent, which is how the randomized range finder splits a Gaussian test matrix.

For fixed nested orthogonal projectors $\mathbf{E}_2 \preceq \mathbf{E}_1$ and
$\mathbf{F}_2 \preceq \mathbf{F}_1$, the block $\mathbf{E}_2\mathbf{X}\mathbf{F}_2$ of a standard
Gaussian matrix is independent of the rest of $\mathbf{E}_1\mathbf{X}\mathbf{F}_1$ and may be
replaced by the same block of an independent copy. This is one step of the adaptive
deferred-decision induction (`NLAlib/LowerBounds/QueryModel/DeferredDecision.lean`).

## Main results

* `NLAlib.hasLaw_mulVec_of_hasLaw_gaussianVector`: $\mathbf{A}\mathbf{g}$ is a standard Gaussian
  vector when $\mathbf{A}$ has orthonormal rows; every result below reduces to it.
* `NLAlib.hasLaw_mul_mul_of_hasLaw_gaussianMatrix`: two-sided invariance.
* `NLAlib.hasLaw_const_mul_of_hasLaw_gaussianMatrix`,
  `NLAlib.hasLaw_mul_const_of_hasLaw_gaussianMatrix`,
  `NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix`.
* `NLAlib.hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`,
  `NLAlib.hasLaw_submatrix_of_hasLaw_gaussianMatrix`.
* `NLAlib.hasLaw_mulVec_of_hasLaw_gaussianMatrix`: $\mathbf{G}\mathbf{x}$ for a unit vector
  $\mathbf{x}$.
* `NLAlib.indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix`: independence of orthogonal blocks.
* `NLAlib.identDistrib_mul_mul_of_hasLaw_gaussianMatrix`: resampling a nested block.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

section Vector

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private theorem inner_toLp_mulVec (A : Matrix κ ι ℝ) (x : ι → ℝ) (t : EuclideanSpace ℝ κ) :
    inner ℝ (WithLp.toLp 2 (A *ᵥ x)) t =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 (Aᴴ *ᵥ t.ofLp)) := by
  rw [← WithLp.toLp_ofLp 2 t, EuclideanSpace.inner_toLp_toLp, EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

private theorem map_mulVec_gaussianVector [DecidableEq κ] {A : Matrix κ ι ℝ}
    (hA : HasOrthonormalCols Aᴴ) : (gaussianVector ι).map (A *ᵥ ·) = gaussianVector κ := by
  have hc : Continuous fun x : ι → ℝ => A *ᵥ x := continuous_const.matrix_mulVec continuous_id
  have key : ((gaussianVector ι).map (A *ᵥ ·)).map (WithLp.toLp 2) =
      (gaussianVector κ).map (WithLp.toLp 2) := by
    rw [map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) hc.measurable]
    refine Measure.ext_of_charFun (funext fun t => ?_)
    have h : charFun ((gaussianVector ι).map (WithLp.toLp 2 ∘ (A *ᵥ ·))) t =
        charFun ((gaussianVector ι).map (WithLp.toLp 2)) (WithLp.toLp 2 (Aᴴ *ᵥ t.ofLp)) := by
      rw [charFun_apply, charFun_apply,
        integral_map ((PiLp.continuous_toLp 2 _).comp hc).aemeasurable (by fun_prop),
        integral_map (by fun_prop) (by fun_prop)]
      simp only [Function.comp_apply, inner_toLp_mulVec]
    rw [h, map_pi_eq_stdGaussian, charFun_stdGaussian, charFun_stdGaussian,
      hA.norm_toLp_mulVec, WithLp.toLp_ofLp]
  have h := congrArg (Measure.map WithLp.ofLp) key
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa only [Function.comp_def, WithLp.ofLp_toLp, Measure.map_id'] using h

/-- Coisometric images of a standard Gaussian vector: if $\mathbf{A}$ has orthonormal rows
($\mathbf{A}\mathbf{A}^{\mathsf{H}} = \mathbf{I}$), then $\mathbf{A}\mathbf{y}$ is a standard
Gaussian vector whenever $\mathbf{y}$ is. For a square $\mathbf{A}$ this is the orthogonal
invariance of the standard Gaussian law; for a wide $\mathbf{A}$ it says that orthonormal linear
forms of a standard Gaussian vector are independent standard Gaussians. -/
theorem hasLaw_mulVec_of_hasLaw_gaussianVector [DecidableEq κ] {y : Ω → ι → ℝ}
    (hy : HasLaw y (gaussianVector ι) μ) {A : Matrix κ ι ℝ} (hA : HasOrthonormalCols Aᴴ) :
    HasLaw (fun ω => A *ᵥ y ω) (gaussianVector κ) μ := by
  have hc : Continuous fun x : ι → ℝ => A *ᵥ x := continuous_const.matrix_mulVec continuous_id
  exact HasLaw.fun_comp (Y := (A *ᵥ ·)) ⟨hc.measurable.aemeasurable, map_mulVec_gaussianVector hA⟩
    hy

end Vector

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  {X : Ω → Matrix m n ℝ}

/-- Orthogonal invariance: for $\mathbf{U}$ with orthonormal rows and $\mathbf{V}$ with
orthonormal columns, $\mathbf{U}\mathbf{G}\mathbf{V}$ is a standard Gaussian matrix. -/
theorem hasLaw_mul_mul_of_hasLaw_gaussianMatrix [DecidableEq p] [DecidableEq q]
    (hX : HasLaw X (gaussianMatrix m n) μ) {U : Matrix p m ℝ} (hU : HasOrthonormalCols Uᴴ)
    {V : Matrix n q ℝ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => U * X ω * V) (gaussianMatrix p q) μ := by
  have hUV : HasOrthonormalCols (U ⊗ₖ Vᵀ)ᴴ := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_eq_transpose_of_trivial Vᵀ,
      Matrix.transpose_transpose]
    exact hU.kronecker hV
  refine hasLaw_gaussianMatrix_of_hasLaw_uncurry ?_
  simp only [uncurry_mul_mul]
  exact hasLaw_mulVec_of_hasLaw_gaussianVector (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX) hUV

/-- $\mathbf{U}\mathbf{G}$ is a standard Gaussian matrix when $\mathbf{U}$ has orthonormal rows. -/
theorem hasLaw_const_mul_of_hasLaw_gaussianMatrix [DecidableEq p]
    (hX : HasLaw X (gaussianMatrix m n) μ) {U : Matrix p m ℝ} (hU : HasOrthonormalCols Uᴴ) :
    HasLaw (fun ω => U * X ω) (gaussianMatrix p n) μ := by
  classical
  simpa only [Matrix.mul_one] using
    hasLaw_mul_mul_of_hasLaw_gaussianMatrix hX hU (hasOrthonormalCols_one (n := n))

/-- $\mathbf{V}^{\mathsf{H}}\mathbf{G}$ is a standard Gaussian matrix when $\mathbf{V}$ has
orthonormal columns: the form in which a block of a Gaussian test matrix appears,
$\mathbf{G}_1 = \mathbf{V}_1^{\mathsf{H}}\mathbf{G}$ for a frame $\mathbf{V}_1$. -/
theorem hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix [DecidableEq p]
    (hX : HasLaw X (gaussianMatrix m n) μ) {V : Matrix m p ℝ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => Vᴴ * X ω) (gaussianMatrix p n) μ :=
  hasLaw_const_mul_of_hasLaw_gaussianMatrix hX (by rwa [Matrix.conjTranspose_conjTranspose])

/-- $\mathbf{G}\mathbf{V}$ is a standard Gaussian matrix when $\mathbf{V}$ has orthonormal
columns. -/
theorem hasLaw_mul_const_of_hasLaw_gaussianMatrix [DecidableEq q]
    (hX : HasLaw X (gaussianMatrix m n) μ) {V : Matrix n q ℝ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => X ω * V) (gaussianMatrix m q) μ := by
  classical
  have h1 : HasOrthonormalCols (1 : Matrix m m ℝ)ᴴ := by
    rw [Matrix.conjTranspose_one]
    exact hasOrthonormalCols_one
  simpa only [Matrix.one_mul] using hasLaw_mul_mul_of_hasLaw_gaussianMatrix hX h1 hV

/-- The conjugate transpose (over $\mathbb{R}$, the transpose) of a Gaussian matrix is
Gaussian. -/
theorem hasLaw_conjTranspose_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    HasLaw (fun ω => (X ω)ᴴ) (gaussianMatrix n m) μ := by
  have := hX.isProbabilityMeasure
  have h : HasLaw (fun ω j i => X ω i j) (Measure.pi fun _ : n => gaussianVector m) μ :=
    hasLaw_pi_iff.2 ⟨iIndepFun_col_of_hasLaw_gaussianMatrix hX,
      hasLaw_col_of_hasLaw_gaussianMatrix hX⟩
  have hfun : (fun ω => (X ω)ᴴ) = fun ω => Matrix.of fun j i => X ω i j := by
    funext ω
    ext j i
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.of_apply]
  rw [hfun]
  exact h

/-- A submatrix of a Gaussian matrix on injective row and column maps is Gaussian. -/
theorem hasLaw_submatrix_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    {r : p → m} (hr : Function.Injective r) {s : q → n} (hs : Function.Injective s) :
    HasLaw (fun ω => (X ω).submatrix r s) (gaussianMatrix p q) μ := by
  classical
  have hr' : HasOrthonormalCols (selectionMatrix r : Matrix m p ℝ)ᴴᴴ := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hasOrthonormalCols_selectionMatrix hr
  simpa only [conjTranspose_selectionMatrix_mul, mul_selectionMatrix, Matrix.submatrix_submatrix,
    Function.comp_id, Function.id_comp] using
    hasLaw_mul_mul_of_hasLaw_gaussianMatrix hX hr' (hasOrthonormalCols_selectionMatrix hs)

/-- $\mathbf{G}\mathbf{x}$ is a standard Gaussian vector for a unit vector $\mathbf{x}$
($\|\mathbf{x}\| = 1$). -/
theorem hasLaw_mulVec_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    {x : n → ℝ} (hx : ‖WithLp.toLp 2 x‖ = 1) :
    HasLaw (fun ω => X ω *ᵥ x) (gaussianVector m) μ := by
  have hV : HasOrthonormalCols (Matrix.replicateCol Unit x) := by
    rw [hasOrthonormalCols_iff]
    ext a b
    obtain rfl : a = b := Subsingleton.elim a b
    rw [Matrix.one_apply_eq, Matrix.conjTranspose_replicateCol,
      Matrix.replicateRow_mul_replicateCol_apply, star_trivial,
      ← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hx, one_pow]
  exact hasLaw_col_of_hasLaw_gaussianMatrix (hasLaw_mul_const_of_hasLaw_gaussianMatrix hX hV) ()

omit [Fintype p] [Fintype q] in
/-- Independence of orthogonal blocks: for frames (matrices with orthonormal columns)
$\mathbf{V}_1$ and $\mathbf{V}_2$ with $\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$, the
blocks $\mathbf{V}_1^{\mathsf{H}}\mathbf{G}$ and $\mathbf{V}_2^{\mathsf{H}}\mathbf{G}$ are
independent (and each is a standard Gaussian matrix, by
`hasLaw_const_mul_of_hasLaw_gaussianMatrix`). -/
theorem indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix [Finite p] [Finite q]
    [DecidableEq p] [DecidableEq q] (hX : HasLaw X (gaussianMatrix m n) μ) {V₁ : Matrix m p ℝ}
    {V₂ : Matrix m q ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) :
    IndepFun (fun ω => V₁ᴴ * X ω) (fun ω => V₂ᴴ * X ω) μ := by
  have := hX.isProbabilityMeasure
  have := Fintype.ofFinite p
  have := Fintype.ofFinite q
  have hrows {V : Matrix m p ℝ} (hV : HasOrthonormalCols V) : HasOrthonormalCols Vᴴᴴ := by
    rwa [Matrix.conjTranspose_conjTranspose]
  have hW : HasOrthonormalCols (Matrix.fromCols V₁ V₂)ᴴᴴ := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hasOrthonormalCols_fromCols_iff.2 ⟨hV₁, hV₂, h₁₂⟩
  have hP := (measurePreserving_sumPiEquivProdPi
    (fun _ : p ⊕ q => gaussianVector n)).fun_comp_hasLaw
    (hasLaw_const_mul_of_hasLaw_gaussianMatrix hX hW)
  have hfun : ∀ ω, MeasurableEquiv.sumPiEquivProdPi (fun _ : p ⊕ q => n → ℝ)
      ((Matrix.fromCols V₁ V₂)ᴴ * X ω) = (V₁ᴴ * X ω, V₂ᴴ * X ω) := by
    intro ω
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul]
    rfl
  refine (indepFun_iff_hasLaw_prodMk_prod (hasLaw_const_mul_of_hasLaw_gaussianMatrix hX
    (hrows hV₁)) (hasLaw_const_mul_of_hasLaw_gaussianMatrix hX ?_)).2 ?_
  · rwa [Matrix.conjTranspose_conjTranspose]
  · simp only [hfun] at hP
    exact hP

end NLAlib


open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n]

/-- **Resampling a block of a Gaussian matrix**: let $\mathbf{X}$, $\mathbf{X}'$ be independent
standard Gaussian $m \times n$ matrices, $\mathbf{E}_2$, $\mathbf{F}_1$, $\mathbf{F}_2$ orthogonal
projectors and $\mathbf{E}_1$ a matrix with $\mathbf{E}_1\mathbf{E}_2 = \mathbf{E}_2$ and
$\mathbf{F}_1\mathbf{F}_2 = \mathbf{F}_2$ (for an orthogonal projector $\mathbf{E}_1$ this is
$\mathbf{E}_2 \preceq \mathbf{E}_1$; likewise $\mathbf{F}_2 \preceq \mathbf{F}_1$). Then
$\mathbf{E}_1\mathbf{X}\mathbf{F}_1$ has the law of
$$\mathbf{E}_1\mathbf{X}\mathbf{F}_1 - \mathbf{E}_2\mathbf{X}\mathbf{F}_2 +
\mathbf{E}_2\mathbf{X}'\mathbf{F}_2\,.$$
[ZhangEtAl2026, proof of Lemma 4.1]; there one query at a time with orthonormal frames and
entries $\mathcal{N}(0, 1/d)$; here unit variance and any nested projectors. -/
theorem identDistrib_mul_mul_of_hasLaw_gaussianMatrix {X X' : Ω → Matrix m n ℝ}
    (hX : HasLaw X (gaussianMatrix m n) μ) (hX' : HasLaw X' (gaussianMatrix m n) μ)
    (hXX' : IndepFun X X' μ) {E₁ E₂ : Matrix m m ℝ} {F₁ F₂ : Matrix n n ℝ}
    (hE₂ : IsStarProjection E₂) (hF₁ : IsStarProjection F₁) (hF₂ : IsStarProjection F₂)
    (hE : E₁ * E₂ = E₂) (hF : F₁ * F₂ = F₂) :
    IdentDistrib (fun ω => E₁ * X ω * F₁)
      (fun ω => E₁ * X ω * F₁ - E₂ * X ω * F₂ + E₂ * X' ω * F₂) μ μ := by
  classical
  have := hX.isProbabilityMeasure
  set P : Matrix (m × n) (m × n) ℝ := Matrix.kronecker E₂ F₂ᵀ with hPdef
  have hPH : Pᴴ = P := by
    have hF₂T : F₂ᵀ = F₂ := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.star_eq_conjTranspose,
        hF₂.isSelfAdjoint.star_eq]
    rw [hPdef, hF₂T, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, hE₂.isSelfAdjoint.star_eq,
      hF₂.isSelfAdjoint.star_eq]
  have hPP : P * P = P := by
    rw [hPdef, Matrix.kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul,
      hE₂.isIdempotentElem.eq, hF₂.isIdempotentElem.eq]
  have hA : HasOrthonormalCols (Matrix.fromCols (1 - P) P)ᴴ := by
    rw [hasOrthonormalCols_iff, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, hPP]
    abel
  -- the stacked pair `(X, X')`, flattened, is a standard Gaussian vector; swapping its
  -- `E₂ ⬝ F₂` blocks is the coisometry `[1 - P, P]`, so `Y = X - E₂XF₂ + E₂X'F₂` is Gaussian
  have hz : HasLaw (fun ω => (MeasurableEquiv.sumPiEquivProdPi fun _ : (m × n) ⊕ (m × n) => ℝ).symm
      (Function.uncurry (X ω), Function.uncurry (X' ω))) (gaussianVector ((m × n) ⊕ (m × n))) μ :=
    (measurePreserving_sumPiEquivProdPi fun _ : (m × n) ⊕ (m × n) => gaussianReal 0 1).symm
      |>.fun_comp_hasLaw <| (indepFun_iff_hasLaw_prodMk_prod
        (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX)
        (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX')).1 (hXX'.comp
        (MeasurableEquiv.curry m n ℝ).symm.measurable
        (MeasurableEquiv.curry m n ℝ).symm.measurable)
  have hY : HasLaw (fun ω => X ω - E₂ * X ω * F₂ + E₂ * X' ω * F₂) (gaussianMatrix m n) μ := by
    refine hasLaw_gaussianMatrix_of_hasLaw_uncurry ?_
    convert hasLaw_mulVec_of_hasLaw_gaussianVector hz hA using 2 with ω
    change _ = (1 - P).fromCols P *ᵥ Sum.elim (Function.uncurry (X ω)) (Function.uncurry (X' ω))
    rw [Matrix.fromCols_mulVec_sumElim, Matrix.sub_mulVec, Matrix.one_mulVec, hPdef,
      Matrix.kronecker, ← uncurry_mul_mul, ← uncurry_mul_mul]
    rfl
  have hF' : F₂ * F₁ = F₂ := by
    have h := congrArg star hF
    rwa [star_mul, hF₁.isSelfAdjoint.star_eq, hF₂.isSelfAdjoint.star_eq] at h
  have hfun : (fun ω => E₁ * X ω * F₁ - E₂ * X ω * F₂ + E₂ * X' ω * F₂) =
      (fun M => E₁ * M * F₁) ∘ fun ω => X ω - E₂ * X ω * F₂ + E₂ * X' ω * F₂ := by
    funext ω
    simp only [Function.comp_apply, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add,
      Matrix.mul_sub, ← Matrix.mul_assoc, hE]
    simp only [Matrix.mul_assoc, hF']
  rw [hfun]
  exact (hX.identDistrib hY).comp
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable

end NLAlib
