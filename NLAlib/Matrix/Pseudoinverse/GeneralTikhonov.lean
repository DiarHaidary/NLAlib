/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.GeneralizedSVD
public import NLAlib.Matrix.Pseudoinverse.RegularizedLeastSquares
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Generalized singular filters for Tikhonov regularization

The normalized GSVD gives a regularized solution for every data and penalty pair, including
a common kernel. Its vanishing-parameter endpoint minimizes the penalty among least-squares
solutions, while its diverging-parameter endpoint solves least squares on the penalty kernel.
The endpoint variational meanings are proved in the companion `GeneralTikhonovLimits` module.
Proof material adapted from `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`, `NLAlib/Matrix/Basic/GeneralTikhonov*.lean`.

## Main results

* `NLAlib.IsGSVD.isMinOn_tikhonovObjective`: the generalized singular filter minimizes.
* `NLAlib.IsGSVD.gsvdTikhonovFilter_eq`: agreement with the canonical solution when unique.
* `NLAlib.IsGSVD.tendsto_gsvdTikhonovFilter_zero`: the vanishing-parameter endpoint.
* `NLAlib.tendsto_gsvdTikhonovFilter_atTop`: the diverging-parameter endpoint.
-/

@[expose] public section

open Filter Topology
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}
  [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

/-- The GSVD-coordinate Tikhonov solution
$\mathbf{X}\operatorname{diag}((c_i^2+\beta s_i^2)^{-1})\mathbf{X}^{\mathsf{H}}
\mathbf{A}^{\mathsf{H}}\mathbf{b}$. Division by zero is zero. With normalized GSVD
coordinates and positive parameter it minimizes the general-penalty objective. With a common
kernel this chosen solution need not be the minimum Euclidean norm solution. -/
noncomputable def gsvdTikhonovFilter (A : Matrix m n 𝕜) (X : Matrix n n 𝕜)
    (c s : n → ℝ) (b : m → 𝕜) (β : ℝ) : n → 𝕜 :=
  X *ᵥ (fun i => (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜))

/-- The GSVD-coordinate least-squares solution on the penalty kernel: retain coordinates
with $s_i=0$ and divide their data coefficient by $c_i^2$. Division by zero is zero;
without a GSVD hypothesis the definition is only this total coordinate expression. -/
noncomputable def gsvdPenaltyKernelSolution (A : Matrix m n 𝕜) (X : Matrix n n 𝕜)
    (c s : n → ℝ) (b : m → 𝕜) : n → 𝕜 :=
  X *ᵥ (fun i => if s i = 0 then (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / (c i : 𝕜) ^ 2 else 0)

namespace IsGSVD

variable {A : Matrix m n 𝕜} {L : Matrix p n 𝕜}
  {X : Matrix n n 𝕜} {c s : n → ℝ}

private theorem normal_congruence (h : IsGSVD A L X c s) (β : ℝ) :
    Xᴴ * (Aᴴ * A + β • (Lᴴ * L)) * X =
      Matrix.diagonal (fun i => ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜)) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    h.conjTranspose_mul_mul_left, h.conjTranspose_mul_mul_right]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [RCLike.real_smul_eq_coe_mul, map_add, map_mul, map_pow]
  · simp [hij]

private theorem coefficient_eq_zero (h : IsGSVD A L X c s) (b : m → 𝕜)
    (i : n) (hi : c i = 0) : (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i = 0 := by
  have hc := h.col_mul_eq_zero i hi
  rw [Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul]
  change ∑ j, star ((A * X) j i) * b j = 0
  simp only [show ∀ j, (A * X) j i = 0 from fun j => congrFun hc j,
    star_zero, zero_mul, Finset.sum_const_zero]

/-- The generalized singular filter solves the regularized normal equation for every
positive parameter, including deficient stacked rank. Inactive coordinates have zero data
coefficient, so the total division causes no extra assumption. -/
theorem mulVec_gsvdTikhonovFilter (h : IsGSVD A L X c s) (b : m → 𝕜)
    {β : ℝ} (hβ : 0 < β) :
    (Aᴴ * A + β • (Lᴴ * L)) *ᵥ gsvdTikhonovFilter A X c s b β = Aᴴ *ᵥ b := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_conjTranspose X).mpr h.isUnit)
  rw [gsvdTikhonovFilter, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h.normal_congruence]
  ext i
  rw [Matrix.mulVec_diagonal]
  by_cases hi : c i ^ 2 + β * s i ^ 2 = 0
  · have hc : c i = 0 := by nlinarith [sq_nonneg (c i), sq_nonneg (s i)]
    rw [h.coefficient_eq_zero b i hc, zero_div, mul_zero]
  · have hcast : ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast hi
    exact mul_div_cancel₀ _ hcast

/-- **The generalized Tikhonov filter minimizes.** For normalized generalized singular
coordinates of real or complex rectangular data and penalty matrices and $\beta>0$, the
coordinate filter minimizes $\|\mathbf{b}-\mathbf{A}\mathbf{x}\|^2+
\beta\|\mathbf{L}\mathbf{x}\|^2$. Common kernels and empty dimensions are included.
Derived here from the normalized GSVD and augmented normal equations; no printed source
for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem isMinOn_tikhonovObjective (h : IsGSVD A L X c s) (b : m → 𝕜)
    {β : ℝ} (hβ : 0 < β) :
    IsMinOn (tikhonovObjective A L b β) Set.univ (gsvdTikhonovFilter A X c s b β) := by
  rw [isMinOn_tikhonovObjective_iff_normal_equations A L b hβ.le]
  exact h.mulVec_gsvdTikhonovFilter b hβ

/-- **The unique generalized Tikhonov solution.** For normalized generalized singular
coordinates, positive parameter, and trivial common kernel of data and penalty matrices,
the GSVD filter equals the canonical regularized inverse applied to the data. The common
kernel condition is essential because the GSVD coordinates need not be orthonormal.
Derived here from the affine minimizer description; no printed source for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem gsvdTikhonovFilter_eq (h : IsGSVD A L X c s)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker L.mulVecLin = ⊥)
    (b : m → 𝕜) {β : ℝ} (hβ : 0 < β) :
    gsvdTikhonovFilter A X c s b β = tikhonovInverse A L β *ᵥ b := by
  obtain ⟨v, hv, he⟩ := (isMinOn_tikhonovObjective_iff_exists A L b hβ).mp
    (h.isMinOn_tikhonovObjective b hβ)
  rw [hker, Submodule.mem_bot] at hv
  simpa only [hv, add_zero] using he

/-- **The zero-parameter GSVD limit.** For normalized generalized singular coordinates,
the positive-parameter filter converges to its value at zero. This keeps nonzero data
coordinates and sets the remaining ones to zero. The result includes common kernels and
empty dimensions; this endpoint need not equal the data pseudoinverse solution.
Derived here by finite coordinate limits; no printed source for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem tendsto_gsvdTikhonovFilter_zero (h : IsGSVD A L X c s) (b : m → 𝕜) :
    Tendsto (fun β : ℝ => gsvdTikhonovFilter A X c s b β)
      (𝓝[>] 0) (𝓝 (gsvdTikhonovFilter A X c s b 0)) := by
  have hcoord : Tendsto (fun β : ℝ => fun i =>
      (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜)) (𝓝[>] 0)
      (𝓝 (fun i => (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / (c i : 𝕜) ^ 2)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    by_cases hi : c i = 0
    · simp only [h.coefficient_eq_zero b i hi, zero_div]
      exact tendsto_const_nhds
    · have hc : ContinuousAt (fun β : ℝ =>
          (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜)) 0 := by
        apply continuousAt_const.div
        · fun_prop
        · simpa using (pow_ne_zero 2 (show (c i : 𝕜) ≠ 0 by exact_mod_cast hi))
      simpa using! hc.tendsto.mono_left inf_le_left
  have hc : Continuous (fun y : n → 𝕜 => X *ᵥ y) := by fun_prop
  simpa [gsvdTikhonovFilter, Function.comp_def] using! hc.continuousAt.tendsto.comp hcoord

end IsGSVD

omit [DecidableEq n] in
/-- **The infinite-parameter GSVD limit.** For any finite real or complex coordinate
matrix and real coordinate weights, the filter converges as the parameter tends to infinity
to the expression retaining exactly the zero-penalty coordinates. No GSVD hypothesis is
needed for this coordinate limit. Derived here by finite coordinate limits;
no printed source for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem tendsto_gsvdTikhonovFilter_atTop (A : Matrix m n 𝕜) (X : Matrix n n 𝕜)
    (c s : n → ℝ) (b : m → 𝕜) :
    Tendsto (fun β : ℝ => gsvdTikhonovFilter A X c s b β)
      atTop (𝓝 (gsvdPenaltyKernelSolution A X c s b)) := by
  have hcoord : Tendsto (fun β : ℝ => fun i =>
      (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜)) atTop
      (𝓝 (fun i => if s i = 0 then (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / (c i : 𝕜) ^ 2 else 0)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    by_cases hi : s i = 0
    · simp [hi]
    · have hw : Tendsto (fun β : ℝ => c i ^ 2 + β * s i ^ 2) atTop atTop := by
        apply tendsto_const_nhds.add_atTop
        exact tendsto_id.atTop_mul_const (sq_pos_of_ne_zero hi)
      have hinv := tendsto_inv_atTop_zero.comp hw
      have hcast : Tendsto (fun β : ℝ => (((c i ^ 2 + β * s i ^ 2)⁻¹ : ℝ) : 𝕜))
          atTop (𝓝 0) := by
        simpa only [RCLike.ofReal_zero, Function.comp_def] using
          RCLike.continuous_ofReal.continuousAt.tendsto.comp hinv
      simpa [hi, div_eq_mul_inv] using tendsto_const_nhds.mul hcast
  have hc : Continuous (fun y : n → 𝕜 => X *ᵥ y) := by fun_prop
  exact hc.continuousAt.tendsto.comp hcoord

end NLAlib
