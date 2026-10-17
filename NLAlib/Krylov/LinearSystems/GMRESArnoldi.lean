/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.GMRES
public import NLAlib.Krylov.Processes.ArnoldiRecurrence

/-!
# GMRES through the Arnoldi process

For every square $\mathbf{A}$ and every $q$, the GMRES iterate is
$\mathbf{x}_0 + \|\mathbf{r}_0\|\,\mathbf{Q}_q\underline{\mathbf{H}}_q^{+}\mathbf{e}_0$, with
$\mathbf{Q}_q$ the Arnoldi basis of $\mathcal{K}_q(\mathbf{A}, \mathbf{r}_0)$ and
$\underline{\mathbf{H}}_q = \mathbf{Q}_{q+1}^{\mathsf{H}}\mathbf{A}\mathbf{Q}_q$ the
$(q + 1) \times q$ Hessenberg matrix: the small least-squares problem
$\min_{\mathbf{y}}\|\|\mathbf{r}_0\|\mathbf{e}_0 - \underline{\mathbf{H}}_q\mathbf{y}\|$, whose
minimum-norm solution the pseudoinverse names. The same holds with the basis and Hessenberg matrix
computed by the Arnoldi process. No grade hypothesis: past the grade the canonical basis has zero
columns, $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{Q}$ still holds, and
`pinv_mul_of_conjTranspose_mul_self_mul_eq` applies.

## Main results

* `NLAlib.gmresIterate_eq_arnoldiMatrix`: the canonical Arnoldi basis yields GMRES.
* `NLAlib.gmresIterate_eq_mgsArnoldiMatrix`: the Arnoldi process yields GMRES.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Arnoldi basis yields GMRES**, for every $\mathbf{A}$ and $q$:
$\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_0 +
\|\mathbf{r}_0\|\,\mathbf{Q}_q\underline{\mathbf{H}}_q^{+}\mathbf{e}_0$, with no grade
hypothesis. [SaadSchultz1986]; [Saad2003, Proposition 6.18]; locators to verify.
Result: gmres-arnoldi -/
theorem gmresIterate_eq_arnoldiMatrix (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    gmresIterate A b x₀ q = x₀ + (‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ : 𝕜) •
      (arnoldiMatrix A (b - A *ᵥ x₀) q *ᵥ
        (pinv ((arnoldiMatrix A (b - A *ᵥ x₀) (q + 1))ᴴ * A * arnoldiMatrix A (b - A *ᵥ x₀) q)
          *ᵥ Pi.single 0 1)) := by
  have hQ := gramSchmidtQ_mul_conjTranspose_gramSchmidtQ_mul_self
    (krylovMatrix A (b - A *ᵥ x₀) q)
  have hQ' := gramSchmidtQ_mul_conjTranspose_gramSchmidtQ_mul_self
    (krylovMatrix A (b - A *ᵥ x₀) (q + 1))
  rw [← arnoldiMatrix] at hQ hQ'
  have hQ'' : (arnoldiMatrix A (b - A *ᵥ x₀) (q + 1))ᴴ * arnoldiMatrix A (b - A *ᵥ x₀) (q + 1) *
      (arnoldiMatrix A (b - A *ᵥ x₀) (q + 1))ᴴ = (arnoldiMatrix A (b - A *ᵥ x₀) (q + 1))ᴴ := by
    have h := congrArg Matrix.conjTranspose hQ'
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      at h
  rw [gmresIterate, minResidualInverse, ← gramSchmidtQ_mul_conjTranspose, ← arnoldiMatrix,
    ← Matrix.mul_assoc A, mul_arnoldiMatrix,
    Matrix.mul_assoc (arnoldiMatrix A (b - A *ᵥ x₀) (q + 1)),
    pinv_mul_of_conjTranspose_mul_self_mul_eq (by simp only [← Matrix.mul_assoc, hQ'']),
    pinv_mul_conjTranspose_of_mul_conjTranspose_mul_self_eq (by simp only [Matrix.mul_assoc, hQ]),
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, conjTranspose_arnoldiMatrix_mulVec_self,
    Matrix.mulVec_smul, Matrix.mulVec_smul]

/-- **The Arnoldi process yields GMRES**, for every $\mathbf{A}$ and $q$, with the basis and the
Hessenberg matrix computed by `arnoldiState`. -/
theorem gmresIterate_eq_mgsArnoldiMatrix (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    gmresIterate A b x₀ q = x₀ + (‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ : 𝕜) •
      (mgsArnoldiMatrix A (b - A *ᵥ x₀) q *ᵥ
        (pinv (mgsArnoldiHessenberg A (b - A *ᵥ x₀) q) *ᵥ Pi.single 0 1)) := by
  rw [mgsArnoldiMatrix_eq_arnoldiMatrix, mgsArnoldiHessenberg_eq, gmresIterate_eq_arnoldiMatrix]

end NLAlib
