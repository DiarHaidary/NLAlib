/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import NLAlib.ForMathlib.Analysis.CStarAlgebra.Matrix
public import NLAlib.ForMathlib.LinearAlgebra.Matrix.PosDef

/-!
# Integrals of matrix-valued functions

The expectation $\mathbb{E}\mathbf{X}$ of a random matrix `X : Ω → Matrix m n 𝕜` is Mathlib's
Bochner integral `∫ ω, X ω ∂μ`, which needs a normed-space structure on matrices: the operator
norm of `open scoped Matrix.Norms.L2Operator`, with the real normed-space instance of
`NLAlib/ForMathlib/Analysis/CStarAlgebra/Matrix.lean` (`docs/design/Mathlib-deviations.md`
entry 13). The value of the integral does not depend on the norm, and the statements here mention
none: integrability and the integral are entrywise, and the integral commutes with the conjugate
transpose, reindexing, submatrices, the trace and products with fixed matrices. An almost surely
Hermitian (positive semidefinite) random matrix has a Hermitian (positive semidefinite) mean, with
no integrability hypothesis, because a non-integrable function integrates to $\mathbf{0}$. Loewner
monotonicity is Mathlib's `MeasureTheory.integral_mono_ae`, through
`Matrix.instOrderClosedTopology` (`NLAlib/ForMathlib/LinearAlgebra/Matrix/PosDef.lean`). Upstream
candidates for a file `Mathlib.MeasureTheory.SpecificCodomains.Matrix`, next to Mathlib's
`Mathlib.MeasureTheory.SpecificCodomains.Pi`.

## Main results

* `Matrix.integrable_iff`, `Matrix.memLp_iff`, `Matrix.integral_apply`: entrywise.
* `Matrix.integral_conjTranspose`, `Matrix.integral_reindex`, `Matrix.integral_submatrix`,
  `Matrix.integral_trace`, `Matrix.integral_const_mul`, `Matrix.integral_mul_const`.
* `Matrix.isHermitian_integral`, `Matrix.posSemidef_integral`, `Matrix.posDef_integral`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace Matrix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {l m n k : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype k] [DecidableEq n]

section Entrywise

variable {X : Ω → Matrix m n 𝕜}

/-- Matrices as functions of two indices, a real continuous linear equivalence. -/
private noncomputable def toPi : Matrix m n 𝕜 ≃L[ℝ] (m → n → 𝕜) :=
  (Matrix.ofLinearEquiv ℝ).symm.toContinuousLinearEquiv

/-- A random matrix is integrable exactly when its entries are. -/
theorem integrable_iff :
    Integrable X μ ↔ ∀ i j, Integrable (fun ω => X ω i j) μ := by
  rw [← toPi.integrable_comp_iff]
  simp only [integrable_pi_iff]
  rfl

/-- A random matrix is in $L^p$ exactly when its entries are. -/
theorem memLp_iff {p : ℝ≥0∞} :
    MemLp X p μ ↔ ∀ i j, MemLp (fun ω => X ω i j) p μ := by
  have h : MemLp X p μ ↔ MemLp (fun ω => toPi (X ω)) p μ :=
    ⟨fun h => (toPi (m := m) (n := n) (𝕜 := 𝕜)).toContinuousLinearMap.comp_memLp' h, fun h => by
      simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply] using
        (toPi (m := m) (n := n) (𝕜 := 𝕜)).symm.toContinuousLinearMap.comp_memLp' h⟩
  rw [h]
  simp only [memLp_pi_iff]
  rfl

/-- The entries of the mean of a random matrix are the means of its entries:
$(\mathbb{E}\mathbf{X})_{i,j} = \mathbb{E}\mathbf{X}_{i,j}$. Integrability of the entries is
needed: if one entry is not integrable, the integral is $\mathbf{0}$ while the other entries may
have nonzero means. -/
theorem integral_apply (hX : ∀ i j, Integrable (fun ω => X ω i j) μ) (i : m)
    (j : n) : (∫ ω, X ω ∂μ) i j = ∫ ω, X ω i j ∂μ := by
  exact ((Matrix.entryLinearMap ℝ 𝕜 i j).toContinuousLinearMap.integral_comp_comm
    (Matrix.integrable_iff.mpr hX)).symm

end Entrywise

section Linear

variable {X : Ω → Matrix m n 𝕜}

/-- The conjugate transpose as a real linear equivalence. -/
private def conjTransposeLinearEquivReal : Matrix m n 𝕜 ≃ₗ[ℝ] Matrix n m 𝕜 where
  toFun := Matrix.conjTranspose
  invFun := Matrix.conjTranspose
  map_add' := Matrix.conjTranspose_add
  map_smul' r A := by simp only [Matrix.conjTranspose_smul, star_trivial, RingHom.id_apply]
  left_inv := Matrix.conjTranspose_conjTranspose
  right_inv := Matrix.conjTranspose_conjTranspose

variable [DecidableEq m] in
/-- The conjugate transpose commutes with the integral,
$\mathbb{E}[\mathbf{X}^{\mathsf{H}}] = (\mathbb{E}\mathbf{X})^{\mathsf{H}}$; no integrability is
needed, since the conjugate transpose is a real-linear isometric equivalence. -/
theorem integral_conjTranspose (X : Ω → Matrix m n 𝕜) :
    ∫ ω, (X ω)ᴴ ∂μ = (∫ ω, X ω ∂μ)ᴴ := by
  exact (conjTransposeLinearEquivReal (m := m) (n := n) (𝕜 := 𝕜)).toContinuousLinearEquiv
    |>.integral_comp_comm X

/-- Reindexing commutes with the integral; no integrability is needed. -/
theorem integral_reindex {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq n']
    (e : m ≃ m') (f : n ≃ n') (X : Ω → Matrix m n 𝕜) :
    ∫ ω, Matrix.reindex e f (X ω) ∂μ = Matrix.reindex e f (∫ ω, X ω ∂μ) := by
  exact (Matrix.reindexLinearEquiv ℝ 𝕜 e f).toContinuousLinearEquiv.integral_comp_comm X

variable [DecidableEq k] in
/-- A submatrix of the mean is the mean of the submatrix. -/
theorem integral_submatrix (hX : Integrable X μ) (r : l → m) (c : k → n) :
    ∫ ω, (X ω).submatrix r c ∂μ = (∫ ω, X ω ∂μ).submatrix r c := by
  let L : Matrix m n 𝕜 →ₗ[ℝ] Matrix l k 𝕜 :=
    { toFun := fun A => A.submatrix r c
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact L.toContinuousLinearMap.integral_comp_comm hX

/-- The trace commutes with the integral: for integrable $\mathbf{X}$,
$\mathbb{E}\operatorname{tr}\mathbf{X} = \operatorname{tr}\mathbb{E}\mathbf{X}$. -/
theorem integral_trace {X : Ω → Matrix n n 𝕜} (hX : Integrable X μ) :
    ∫ ω, (X ω).trace ∂μ = (∫ ω, X ω ∂μ).trace := by
  exact (Matrix.traceLinearMap n ℝ 𝕜).toContinuousLinearMap.integral_comp_comm hX

/-- A fixed left factor comes out of the integral: for integrable $\mathbf{X}$,
$\mathbb{E}[\mathbf{A}\mathbf{X}] = \mathbf{A}\, \mathbb{E}\mathbf{X}$. Integrability is needed:
$\mathbf{A}\mathbf{X}$ may be integrable when $\mathbf{X}$ is not. -/
theorem integral_const_mul (A : Matrix l m 𝕜) (hX : Integrable X μ) :
    ∫ ω, A * X ω ∂μ = A * ∫ ω, X ω ∂μ := by
  let L : Matrix m n 𝕜 →ₗ[ℝ] Matrix l n 𝕜 :=
    { toFun := fun B => A * B
      map_add' := Matrix.mul_add A
      map_smul' := fun r B => Matrix.mul_smul A r B }
  exact L.toContinuousLinearMap.integral_comp_comm hX

variable [DecidableEq k] in
/-- A fixed right factor comes out of the integral: for integrable $\mathbf{X}$,
$\mathbb{E}[\mathbf{X}\mathbf{B}] = (\mathbb{E}\mathbf{X})\, \mathbf{B}$. -/
theorem integral_mul_const (hX : Integrable X μ) (B : Matrix n k 𝕜) :
    ∫ ω, X ω * B ∂μ = (∫ ω, X ω ∂μ) * B := by
  let L : Matrix m n 𝕜 →ₗ[ℝ] Matrix m k 𝕜 :=
    { toFun := fun A => A * B
      map_add' := fun A A' => Matrix.add_mul A A' B
      map_smul' := fun r A => Matrix.smul_mul r A B }
  exact L.toContinuousLinearMap.integral_comp_comm hX

end Linear

section Order

variable {X : Ω → Matrix n n 𝕜}

/-- An almost surely Hermitian random matrix has a Hermitian mean. No integrability is needed:
a non-integrable function integrates to $\mathbf{0}$. -/
theorem isHermitian_integral (h : ∀ᵐ ω ∂μ, (X ω).IsHermitian) :
    (∫ ω, X ω ∂μ).IsHermitian := by
  rw [Matrix.IsHermitian, ← Matrix.integral_conjTranspose]
  exact integral_congr_ae (h.mono fun _ hω => hω.eq)

/-- An almost surely positive semidefinite random matrix has a positive semidefinite mean. No
integrability is needed. -/
theorem posSemidef_integral (h : ∀ᵐ ω ∂μ, (X ω).PosSemidef) :
    (∫ ω, X ω ∂μ).PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp (integral_nonneg_of_ae (h.mono fun _ hω => hω.nonneg))

/-- The pairing $\mathbf{z}^{\mathsf{H}}\mathbf{A}\mathbf{z}$ at a fixed vector, as a real linear
map of the matrix. -/
private def dotProductMulVecLinearMap (z : n → 𝕜) : Matrix n n 𝕜 →ₗ[ℝ] 𝕜 where
  toFun A := star z ⬝ᵥ (A *ᵥ z)
  map_add' A A' := by rw [Matrix.add_mulVec, dotProduct_add]
  map_smul' r A := by
    rw [RingHom.id_apply, Matrix.smul_mulVec, dotProduct_smul]

/-- An integrable, almost surely positive definite random matrix has a positive definite mean,
for a nonzero measure. -/
theorem posDef_integral [NeZero μ] (hX : Integrable X μ)
    (h : ∀ᵐ ω ∂μ, (X ω).PosDef) : (∫ ω, X ω ∂μ).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨Matrix.isHermitian_integral (h.mono fun _ hω => hω.isHermitian), fun z hz => ?_⟩
  let L := (dotProductMulVecLinearMap (𝕜 := 𝕜) z).toContinuousLinearMap
  have hq : ∀ᵐ ω ∂μ, 0 < star z ⬝ᵥ (X ω *ᵥ z) := h.mono fun _ hω => hω.dotProduct_mulVec_pos hz
  have hre : ∀ᵐ ω ∂μ, 0 < RCLike.re (star z ⬝ᵥ (X ω *ᵥ z)) :=
    hq.mono fun _ hω => (RCLike.pos_iff.mp hω).1
  have hint : Integrable (fun ω => star z ⬝ᵥ (X ω *ᵥ z)) μ := L.integrable_comp hX
  have hL : star z ⬝ᵥ ((∫ ω, X ω ∂μ) *ᵥ z) = ∫ ω, star z ⬝ᵥ (X ω *ᵥ z) ∂μ :=
    (L.integral_comp_comm hX).symm
  rw [hL, RCLike.pos_iff]
  refine ⟨?_, ?_⟩
  · rw [← integral_re hint]
    refine (integral_pos_iff_support_of_nonneg_ae (hre.mono fun _ h => h.le) hint.re).mpr ?_
    have hs : Function.support (fun ω => RCLike.re (star z ⬝ᵥ (X ω *ᵥ z))) =ᵐ[μ] Set.univ := by
      filter_upwards [hre] with ω hω
      exact propext (iff_true_intro hω.ne')
    rw [measure_congr hs]
    exact Measure.measure_univ_pos.mpr (NeZero.ne μ)
  · rw [← integral_im hint, integral_eq_zero_of_ae (hq.mono fun _ hω => ?_)]
    exact (RCLike.pos_iff.mp hω).2

end Order

end Matrix
