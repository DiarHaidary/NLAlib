/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.GeneralTikhonov
public import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Variational endpoints of general Tikhonov regularization

The vanishing-parameter GSVD filter minimizes the penalty among all least-squares solutions.
The diverging-parameter endpoint minimizes the residual on the penalty kernel. Both meanings
include common kernels; a trivial common kernel makes either endpoint unique.

Proof material adapted from `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib/Matrix/Basic/GeneralTikhonovEndpoints.lean` and
`NLAlib/ForMathlib/Analysis/PenaltyLimits.lean`, using the native least-squares interfaces.

## Main results

* `NLAlib.IsGSVD.isLeastSquaresSolution_gsvdTikhonovFilter_zero`: the limiting data fit.
* `NLAlib.IsGSVD.isMinOn_norm_mulVec_gsvdTikhonovFilter_zero`: its least penalty.
* `NLAlib.IsGSVD.mulVec_gsvdPenaltyKernelSolution`: feasibility of the infinite endpoint.
* `NLAlib.IsGSVD.isMinOn_norm_sub_mulVec_gsvdPenaltyKernelSolution`: constrained optimality.
* `NLAlib.IsGSVD.eq_gsvdTikhonovFilter_zero_of_isMinOn`: uniqueness at zero.
* `NLAlib.IsGSVD.eq_gsvdPenaltyKernelSolution_of_isMinOn`: uniqueness at infinity.
-/

@[expose] public section

open Filter Topology
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}
  [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]
  {A : Matrix m n 𝕜} {L : Matrix p n 𝕜}
  {X : Matrix n n 𝕜} {c s : n → ℝ}

private theorem IsGSVD.zero_endpoint (h : IsGSVD A L X c s) (b : m → 𝕜) :
    IsLeastSquaresSolution A b (gsvdTikhonovFilter A X c s b 0) ∧
      IsMinOn (fun x => ‖WithLp.toLp 2 (L *ᵥ x)‖)
        {x | IsLeastSquaresSolution A b x} (gsvdTikhonovFilter A X c s b 0) := by
  let f := fun x : n → 𝕜 => ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ^ 2
  let g := fun x : n → 𝕜 => ‖WithLp.toLp 2 (L *ᵥ x)‖ ^ 2
  let x := gsvdTikhonovFilter A X c s b
  have hf : Continuous f := by fun_prop
  have hg : Continuous g := by fun_prop
  have hfx := hf.continuousAt.tendsto.comp (h.tendsto_gsvdTikhonovFilter_zero b)
  have hgx := hg.continuousAt.tendsto.comp (h.tendsto_gsvdTikhonovFilter_zero b)
  have hβ : Tendsto (fun β : ℝ => β) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hmin (β : ℝ) (hβ : 0 < β) (z : n → 𝕜) :
      f (x β) + β * g (x β) ≤ f z + β * g z :=
    h.isMinOn_tikhonovObjective b hβ (Set.mem_univ z)
  have hfirst (z : n → 𝕜) : f (x 0) ≤ f z := by
    have hl : Tendsto (fun β => f (x β) + β * g (x β)) (𝓝[>] (0 : ℝ))
        (𝓝 (f (x 0))) := by simpa using hfx.add (hβ.mul hgx)
    have hr : Tendsto (fun β : ℝ => f z + β * g z) (𝓝[>] (0 : ℝ))
        (𝓝 (f z)) := by simpa using tendsto_const_nhds.add (hβ.mul tendsto_const_nhds)
    apply le_of_tendsto_of_tendsto hl hr
    filter_upwards [self_mem_nhdsWithin] with β hβ
    exact hmin β hβ z
  refine ⟨fun z => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hfirst z), ?_⟩
  intro z hz
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply le_of_tendsto hgx
  filter_upwards [self_mem_nhdsWithin] with β hβ
  change g (x β) ≤ g z
  have hz' : f z ≤ f (x β) := pow_le_pow_left₀ (norm_nonneg _) (hz (x β)) 2
  have hh := hmin β hβ z
  exact (mul_le_mul_iff_right₀ hβ).mp (by linarith)

/-- **The general Tikhonov limit is a least-squares solution.** For normalized GSVD
coordinates of arbitrary real or complex data and penalty matrices, the zero-parameter
endpoint minimizes the data residual. Common kernels and empty dimensions are included.
Derived here by taking limits in the regularized minimizing inequality; no printed source
for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem IsGSVD.isLeastSquaresSolution_gsvdTikhonovFilter_zero
    (h : IsGSVD A L X c s) (b : m → 𝕜) :
    IsLeastSquaresSolution A b (gsvdTikhonovFilter A X c s b 0) :=
  (h.zero_endpoint b).1

/-- **The least-penalty least-squares endpoint.** For normalized GSVD coordinates of
arbitrary real or complex data and penalty matrices, the zero-parameter endpoint has the
smallest penalty norm among all least-squares solutions. It need not equal the data
pseudoinverse solution. Common kernels and empty dimensions are allowed.
Derived here from the regularized minimizing inequality; no printed source for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem IsGSVD.isMinOn_norm_mulVec_gsvdTikhonovFilter_zero
    (h : IsGSVD A L X c s) (b : m → 𝕜) :
    IsMinOn (fun x => ‖WithLp.toLp 2 (L *ᵥ x)‖)
      {x | IsLeastSquaresSolution A b x} (gsvdTikhonovFilter A X c s b 0) :=
  (h.zero_endpoint b).2

private theorem IsGSVD.infinity_endpoint (h : IsGSVD A L X c s) (b : m → 𝕜) :
    L *ᵥ gsvdPenaltyKernelSolution A X c s b = 0 ∧
      IsMinOn (fun x => ‖WithLp.toLp 2 (b - A *ᵥ x)‖)
        (LinearMap.ker L.mulVecLin) (gsvdPenaltyKernelSolution A X c s b) := by
  let f := fun x : n → 𝕜 => ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ^ 2
  let g := fun x : n → 𝕜 => ‖WithLp.toLp 2 (L *ᵥ x)‖ ^ 2
  let x := gsvdTikhonovFilter A X c s b
  let xInf := gsvdPenaltyKernelSolution A X c s b
  have hf : Continuous f := by fun_prop
  have hg : Continuous g := by fun_prop
  have hfx := hf.continuousAt.tendsto.comp (tendsto_gsvdTikhonovFilter_atTop A X c s b)
  have hgx := hg.continuousAt.tendsto.comp (tendsto_gsvdTikhonovFilter_atTop A X c s b)
  have hmin (β : ℝ) (hβ : 0 < β) (z : n → 𝕜) :
      f (x β) + β * g (x β) ≤ f z + β * g z :=
    h.isMinOn_tikhonovObjective b hβ (Set.mem_univ z)
  have hbound : ∀ᶠ β : ℝ in atTop, g (x β) ≤ f 0 / β := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    apply (le_div_iff₀ hβ).mpr
    have hh := hmin β hβ 0
    have hgz : g 0 = 0 := by simp [g]
    rw [hgz, mul_zero, add_zero] at hh
    nlinarith [show 0 ≤ f (x β) from sq_nonneg _]
  have hzero : g xInf = 0 := le_antisymm
    (le_of_tendsto_of_tendsto hgx (tendsto_id.const_div_atTop (f 0)) hbound)
    (sq_nonneg _)
  refine ⟨?_, ?_⟩
  · simpa only [g, sq_eq_zero_iff, norm_eq_zero, WithLp.toLp_eq_zero] using hzero
  · intro z hz
    change L *ᵥ z = 0 at hz
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    apply le_of_tendsto hfx
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
    change f (x β) ≤ f z
    have hh := hmin β hβ z
    have hgz : g z = 0 := by simp [g, hz]
    rw [hgz, mul_zero, add_zero] at hh
    linarith [mul_nonneg hβ.le (show 0 ≤ g (x β) from sq_nonneg _)]

/-- **The infinite Tikhonov endpoint lies in the penalty kernel.** For normalized GSVD
coordinates of arbitrary real or complex matrices, the infinite-parameter endpoint has zero
penalty. This includes common kernels and empty dimensions.
Derived here by comparison with the zero vector and passage to the limit; no printed source
for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem IsGSVD.mulVec_gsvdPenaltyKernelSolution (h : IsGSVD A L X c s) (b : m → 𝕜) :
    L *ᵥ gsvdPenaltyKernelSolution A X c s b = 0 :=
  (h.infinity_endpoint b).1

/-- **Least squares on the penalty kernel.** For normalized GSVD coordinates of arbitrary
real or complex data and penalty matrices, the infinite-parameter endpoint minimizes the
data residual over the entire penalty kernel. Common kernels and empty dimensions are allowed.
Derived here by taking limits in the regularized minimizing inequality; no printed source
for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem IsGSVD.isMinOn_norm_sub_mulVec_gsvdPenaltyKernelSolution
    (h : IsGSVD A L X c s) (b : m → 𝕜) :
    IsMinOn (fun x => ‖WithLp.toLp 2 (b - A *ᵥ x)‖)
      (LinearMap.ker L.mulVecLin) (gsvdPenaltyKernelSolution A X c s b) :=
  (h.infinity_endpoint b).2

omit [Fintype p] [DecidableEq n] in
private theorem mulVec_eq_of_norm_midpoint_le (A : Matrix m n 𝕜) (b : m → 𝕜)
    {x y : n → 𝕜}
    (hn : ‖WithLp.toLp 2 (b - A *ᵥ x)‖ = ‖WithLp.toLp 2 (b - A *ᵥ y)‖)
    (hm : ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ≤
      ‖WithLp.toLp 2 (b - A *ᵥ ((1 / 2 : ℝ) • (x + y)))‖) : A *ᵥ x = A *ᵥ y := by
  have he : WithLp.toLp 2 (b - A *ᵥ ((1 / 2 : ℝ) • (x + y))) =
      (1 / 2 : ℝ) • (WithLp.toLp 2 (b - A *ᵥ x) + WithLp.toLp 2 (b - A *ᵥ y)) := by
    rw [← WithLp.toLp_add, ← WithLp.toLp_smul]
    congr 1
    rw [Matrix.mulVec_smul, Matrix.mulVec_add]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, RCLike.real_smul_eq_coe_mul,
      RCLike.ofReal_div, RCLike.ofReal_one, RCLike.ofReal_ofNat]
    ring
  rw [he] at hm
  have hres : WithLp.toLp 2 (b - A *ᵥ x) = WithLp.toLp 2 (b - A *ᵥ y) := by
    by_contra hne
    exact (not_lt_of_ge hm) ((norm_midpoint_lt_iff hn).mpr hne)
  exact sub_right_inj.mp (congrArg WithLp.ofLp hres)

/-- **Uniqueness of the least-penalty endpoint.** For normalized GSVD coordinates and
trivial common kernel of the data and penalty matrices, every least-squares solution with
smallest penalty is the zero-parameter endpoint. Either matrix may be rank deficient.
Derived here using strict convexity of the Euclidean norm; no printed source for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem IsGSVD.eq_gsvdTikhonovFilter_zero_of_isMinOn (h : IsGSVD A L X c s)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker L.mulVecLin = ⊥)
    (b : m → 𝕜) {x : n → 𝕜} (hx : IsLeastSquaresSolution A b x)
    (hmin : IsMinOn (fun y => ‖WithLp.toLp 2 (L *ᵥ y)‖)
      {y | IsLeastSquaresSolution A b y} x) :
    x = gsvdTikhonovFilter A X c s b 0 := by
  let y := gsvdTikhonovFilter A X c s b 0
  obtain ⟨hy, hymin⟩ := h.zero_endpoint b
  have hA : A *ᵥ x = A *ᵥ y := hx.mulVec_eq hy
  have hmid : IsLeastSquaresSolution A b ((1 / 2 : ℝ) • (x + y)) := by
    rw [isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec]
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, hx.mulVec_eq_rangeProjector_mulVec,
      hy.mulVec_eq_rangeProjector_mulVec, ← two_smul ℝ, smul_smul]
    norm_num
  have hn : ‖WithLp.toLp 2 (L *ᵥ x)‖ = ‖WithLp.toLp 2 (L *ᵥ y)‖ :=
    le_antisymm (hmin hy) (hymin hx)
  have hm : ‖WithLp.toLp 2 (L *ᵥ x)‖ ≤
      ‖WithLp.toLp 2 (L *ᵥ ((1 / 2 : ℝ) • (x + y)))‖ := hmin hmid
  have hL : L *ᵥ x = L *ᵥ y := mulVec_eq_of_norm_midpoint_le L 0
    (by simpa only [zero_sub, WithLp.toLp_neg, norm_neg] using hn)
    (by simpa only [zero_sub, WithLp.toLp_neg, norm_neg] using hm)
  have hz : x - y ∈ LinearMap.ker A.mulVecLin ⊓ LinearMap.ker L.mulVecLin := by
    constructor <;> change _ *ᵥ (x - y) = 0
    · rw [Matrix.mulVec_sub, hA, sub_self]
    · rw [Matrix.mulVec_sub, hL, sub_self]
  rw [hker, Submodule.mem_bot] at hz
  exact sub_eq_zero.mp hz

/-- **Uniqueness on the penalty kernel.** For normalized GSVD coordinates and trivial
common kernel, every best data fit on the penalty kernel is the infinite-parameter endpoint.
Neither matrix individually needs full column rank; empty dimensions are included.
Derived here using strict convexity of the Euclidean norm; no printed source for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem IsGSVD.eq_gsvdPenaltyKernelSolution_of_isMinOn (h : IsGSVD A L X c s)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker L.mulVecLin = ⊥)
    (b : m → 𝕜) {x : n → 𝕜} (hx : L *ᵥ x = 0)
    (hmin : IsMinOn (fun y => ‖WithLp.toLp 2 (b - A *ᵥ y)‖)
      (LinearMap.ker L.mulVecLin) x) :
    x = gsvdPenaltyKernelSolution A X c s b := by
  let y := gsvdPenaltyKernelSolution A X c s b
  obtain ⟨hy, hymin⟩ := h.infinity_endpoint b
  have hmid : (1 / 2 : ℝ) • (x + y) ∈ LinearMap.ker L.mulVecLin := by
    change L *ᵥ ((1 / 2 : ℝ) • (x + y)) = 0
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, hx, hy, add_zero, smul_zero]
  have hA : A *ᵥ x = A *ᵥ y := mulVec_eq_of_norm_midpoint_le A b
    (le_antisymm (hmin hy) (hymin hx)) (hmin hmid)
  have hz : x - y ∈ LinearMap.ker A.mulVecLin ⊓ LinearMap.ker L.mulVecLin := by
    constructor <;> change _ *ᵥ (x - y) = 0
    · rw [Matrix.mulVec_sub, hA, sub_self]
    · rw [Matrix.mulVec_sub, hx, hy, sub_self]
  rw [hker, Submodule.mem_bot] at hz
  exact sub_eq_zero.mp hz

end NLAlib
