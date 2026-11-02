/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.Richardson
public import NLAlib.Matrix.Spectral.PowerBounds

/-!
# Landweber iteration and spectral filtering

Landweber is preconditioned Richardson iteration with preconditioner
$\eta\mathbf{A}^{\mathsf{H}}$. The finite filter is valid for every step size and rank.
When $0 < \eta$ and $\eta\|\mathbf{A}\|_2^2 < 2$, the iterates converge to the minimum-norm
least-squares solution plus the initial component in the kernel of $\mathbf{A}$. This form
includes zero matrices and empty dimensions. The zero start converges to the pseudoinverse
solution.

## Main results

* `NLAlib.IsSVD.richardsonIterate_smul_conjTranspose_zero`: the finite spectral filter.
* `NLAlib.tendsto_richardsonIterate_smul_conjTranspose`: convergence from an arbitrary start.
* `NLAlib.tendsto_richardsonIterate_smul_conjTranspose_zero`: the minimum-norm limit.
-/

@[expose] public section

open Filter
open scoped Matrix Topology

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n r : Type*}
  [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- The exact error of Landweber iteration about the minimum-norm least-squares solution.
For every matrix, step size and starting vector,
$$\mathbf{A}^{+}\mathbf{b} -
\mathsf{richardsonIterate}(\mathbf{A},\eta\mathbf{A}^{\mathsf{H}},\mathbf{b},\mathbf{x}_0,q)
= (\mathbf{I}-\eta\mathbf{A}^{\mathsf{H}}\mathbf{A})^q
(\mathbf{A}^{+}\mathbf{b}-\mathbf{x}_0)\,.$$
This is the existing Richardson error identity at the pseudoinverse fixed point. -/
theorem sub_richardsonIterate_smul_conjTranspose_eq [DecidableEq n] (A : Matrix m n 𝕜) (b : m → 𝕜)
    (η : ℝ) (x₀ : n → 𝕜) (q : ℕ) :
    pinv A *ᵥ b - richardsonIterate A (η • Aᴴ) b x₀ q =
      (1 - η • (Aᴴ * A)) ^ q *ᵥ (pinv A *ᵥ b - x₀) := by
  have hfix : (η • Aᴴ) *ᵥ (b - A *ᵥ (pinv A *ᵥ b)) = 0 := by
    rw [Matrix.smul_mulVec,
      isLeastSquaresSolution_iff_conjTranspose_mulVec_sub_eq_zero.mp
        (isLeastSquaresSolution_pinv_mulVec A b), smul_zero]
  simpa only [Matrix.smul_mul] using sub_richardsonIterate_eq hfix x₀ q

/-- **The finite Landweber spectral filter.** For any SVD of $\mathbf{A}$, zero initialization
gives, for every real step size $\eta$ and every $q\ge0$,
$$\mathsf{richardsonIterate}(\mathbf{A},\eta\mathbf{A}^{\mathsf{H}},\mathbf{b},\mathbf{0},q)
=\mathbf{V}\operatorname{diag}\!\left(
\frac{1-(1-\eta\boldsymbol{\sigma}_i^2)^q}{\boldsymbol{\sigma}_i}\right)
\mathbf{U}^{\mathsf{H}}\mathbf{b}\,.$$
The filter is zero at zero singular values, using the total inverse; no rank or stability
assumption is needed. [FesslerNadakuditi2024, §§9.2–9.2.3].
Result: landweber-spectral-filter -/
theorem IsSVD.richardsonIterate_smul_conjTranspose_zero
    {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ} {V : Matrix n r 𝕜}
    (h : IsSVD A U σ V) (b : m → 𝕜) (η : ℝ) (q : ℕ) :
    richardsonIterate A (η • Aᴴ) b 0 q =
      (V * Matrix.diagonal (fun i =>
        (((1 - (1 - η * σ i ^ 2) ^ q) / σ i : ℝ) : 𝕜)) * Uᴴ) *ᵥ b := by
  classical
  have he := sub_richardsonIterate_smul_conjTranspose_eq A b η 0 q
  have hP : (1 - V * Vᴴ) * NLAlib.pinv A = 0 := by
    rw [h.pinv_eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    have hz : (1 - V * Vᴴ) * V = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
        h.hasOrthonormalCols_right.conjTranspose_mul_self, Matrix.mul_one, sub_self]
    rw [hz, Matrix.zero_mul, Matrix.zero_mul]
  rw [h.one_sub_smul_conjTranspose_mul_self_pow, sub_zero, Matrix.add_mulVec,
    Matrix.mulVec_mulVec, hP, Matrix.zero_mulVec, zero_add] at he
  have hdiff : NLAlib.pinv A -
      V * Matrix.diagonal (fun i => (((1 - η * σ i ^ 2) ^ q : ℝ) : 𝕜)) * Vᴴ * NLAlib.pinv A =
      V * Matrix.diagonal (fun i =>
        (((1 - (1 - η * σ i ^ 2) ^ q) / σ i : ℝ) : 𝕜)) * Uᴴ := by
    rw [h.pinv_eq]
    have hc : (V * Matrix.diagonal (fun i => (((1 - η * σ i ^ 2) ^ q : ℝ) : 𝕜)) * Vᴴ) *
        (V * Matrix.diagonal (fun i => (((σ i)⁻¹ : ℝ) : 𝕜)) * Uᴴ) =
        V * (Matrix.diagonal (fun i => (((1 - η * σ i ^ 2) ^ q : ℝ) : 𝕜)) *
          Matrix.diagonal (fun i => (((σ i)⁻¹ : ℝ) : 𝕜))) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᴴ V, h.hasOrthonormalCols_right.conjTranspose_mul_self,
        Matrix.one_mul]
    rw [hc, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_sub]
    congr 2
    funext i
    simp only [div_eq_mul_inv, sub_mul, one_mul, RCLike.ofReal_sub, RCLike.ofReal_mul]
  rw [← hdiff, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
  linear_combination -he

/-- **Landweber convergence from any start.** For every matrix and right-hand side, when
$0<\eta$ and $\eta\|\mathbf{A}\|_2^2<2$,
$$\mathsf{richardsonIterate}(\mathbf{A},\eta\mathbf{A}^{\mathsf{H}},\mathbf{b},\mathbf{x}_0,q)
\longrightarrow \mathbf{A}^{+}\mathbf{b}+
(\mathbf{I}-\mathbf{P}_{\mathbf{A}^{\mathsf{H}}})\mathbf{x}_0\,.$$
For nonzero $\mathbf{A}$ the step-size condition is exactly $0<\eta<2/\|\mathbf{A}\|_2^2$.
The initial kernel component is preserved; for the zero matrix the limit is the start itself.
[FesslerNadakuditi2024, §§9.2–9.2.3]; the full-column-rank source statement is extended here
to arbitrary rank by retaining the unchanged kernel component.
Result: landweber-spectral-filter -/
theorem tendsto_richardsonIterate_smul_conjTranspose [DecidableEq n] (A : Matrix m n 𝕜)
    (b : m → 𝕜) {η : ℝ} (hη : 0 < η) (hstep : η * specNorm A ^ 2 < 2)
    (x₀ : n → 𝕜) :
    Tendsto (fun q => (WithLp.toLp 2
      (richardsonIterate A (η • Aᴴ) b x₀ q) : EuclideanSpace 𝕜 n)) atTop
      (𝓝 (WithLp.toLp 2 (pinv A *ᵥ b + (1 - rangeProjector Aᴴ) *ᵥ x₀))) := by
  have hc : Continuous (fun M : Matrix n n 𝕜 => (WithLp.toLp 2
      (pinv A *ᵥ b - M *ᵥ (pinv A *ᵥ b - x₀)) : EuclideanSpace 𝕜 n)) := by fun_prop
  have ht := hc.continuousAt.tendsto.comp
    (tendsto_one_sub_smul_conjTranspose_mul_self_pow A hη hstep)
  have hkill : (1 - rangeProjector Aᴴ) * pinv A = 0 := by
    rw [← pinv_mul, Matrix.sub_mul, Matrix.one_mul, pinv_mul_mul_pinv, sub_self]
  have hz : (1 - rangeProjector Aᴴ) *ᵥ (pinv A *ᵥ b - x₀) =
      -((1 - rangeProjector Aᴴ) *ᵥ x₀) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hkill, Matrix.zero_mulVec, zero_sub]
  rw [hz, sub_neg_eq_add] at ht
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro q
  apply congrArg (fun v : n → 𝕜 => (WithLp.toLp 2 v : EuclideanSpace 𝕜 n))
  have he := sub_richardsonIterate_smul_conjTranspose_eq A b η x₀ q
  linear_combination he

/-- **The minimum-norm Landweber limit.** For every matrix and right-hand side, zero-start
Landweber with $0<\eta$ and $\eta\|\mathbf{A}\|_2^2<2$ converges to the minimum-norm
least-squares solution:
$$\mathsf{richardsonIterate}(\mathbf{A},\eta\mathbf{A}^{\mathsf{H}},\mathbf{b},\mathbf{0},q)
\longrightarrow\mathbf{A}^{+}\mathbf{b}\,.$$
Rank-deficient and zero matrices and empty dimensions are included.
[FesslerNadakuditi2024, §§9.2–9.2.3].
Result: landweber-spectral-filter -/
theorem tendsto_richardsonIterate_smul_conjTranspose_zero (A : Matrix m n 𝕜)
    (b : m → 𝕜) {η : ℝ} (hη : 0 < η) (hstep : η * specNorm A ^ 2 < 2) :
    Tendsto (fun q => (WithLp.toLp 2
      (richardsonIterate A (η • Aᴴ) b 0 q) : EuclideanSpace 𝕜 n)) atTop
      (𝓝 (WithLp.toLp 2 (pinv A *ᵥ b))) := by
  classical
  simpa only [Matrix.mulVec_zero, add_zero] using
    tendsto_richardsonIterate_smul_conjTranspose A b hη hstep 0

/-- A zero forward matrix leaves every Landweber iterate equal to its start:
$\mathsf{richardsonIterate}(\mathbf{0},\eta\mathbf{0}^{\mathsf{H}},\mathbf{b},
\mathbf{x}_0,q)=\mathbf{x}_0$ for every real step size. -/
theorem richardsonIterate_zero_smul_conjTranspose (b : m → 𝕜) (η : ℝ) (x₀ : n → 𝕜)
    (q : ℕ) : richardsonIterate (0 : Matrix m n 𝕜) (η • (0 : Matrix m n 𝕜)ᴴ) b x₀ q = x₀ := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [richardsonIterate_succ, ih, Matrix.conjTranspose_zero, smul_zero, Matrix.zero_mulVec,
      add_zero]

end NLAlib
