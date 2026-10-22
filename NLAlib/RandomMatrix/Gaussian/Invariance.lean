/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
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

/-- **Coisometric images of a standard Gaussian vector**: if $\mathbf{A}$ has orthonormal rows
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

omit [Fintype p] [Fintype q] in
private theorem hasOrthonormalCols_conjTranspose_kronecker [DecidableEq p] [DecidableEq q]
    {U : Matrix p m ℝ} (hU : HasOrthonormalCols Uᴴ) {V : Matrix n q ℝ}
    (hV : HasOrthonormalCols V) : HasOrthonormalCols (U ⊗ₖ Vᵀ)ᴴ := by
  have h₁ : U * Uᴴ = 1 := by
    simpa only [hasOrthonormalCols_iff, Matrix.conjTranspose_conjTranspose] using hU
  have h₂ : Vᵀ * (Vᵀ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
      ← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hV
  rw [hasOrthonormalCols_iff, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, h₁, h₂, Matrix.one_kronecker_one]

/-- **Orthogonal invariance**: for $\mathbf{U}$ with orthonormal rows and $\mathbf{V}$ with
orthonormal columns, $\mathbf{U}\mathbf{G}\mathbf{V}$ is a standard Gaussian matrix. -/
theorem hasLaw_mul_mul_of_hasLaw_gaussianMatrix [DecidableEq p] [DecidableEq q]
    (hX : HasLaw X (gaussianMatrix m n) μ) {U : Matrix p m ℝ} (hU : HasOrthonormalCols Uᴴ)
    {V : Matrix n q ℝ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => U * X ω * V) (gaussianMatrix p q) μ := by
  refine hasLaw_gaussianMatrix_of_hasLaw_uncurry ?_
  simp only [uncurry_mul_mul]
  exact hasLaw_mulVec_of_hasLaw_gaussianVector (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX)
    (hasOrthonormalCols_conjTranspose_kronecker hU hV)

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
/-- **Independence of orthogonal blocks**: for frames (matrices with orthonormal columns)
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
