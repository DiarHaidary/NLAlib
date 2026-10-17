/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CG
public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# Conjugate gradients through the Lanczos basis

For every $\mathbf{A}$ and every $q$, the CG iterate is
$\mathbf{x}_0 + \|\mathbf{r}_0\|\,\mathbf{Q}\mathbf{T}^{+}\mathbf{e}_0$ with $\mathbf{Q}$ the
canonical (Lanczos) basis of $\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{r}_0)$ and
$\mathbf{T} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$, tridiagonal for Hermitian $\mathbf{A}$;
for Hermitian $\mathbf{A}$ the Lanczos recurrence computes $\mathbf{Q}$ and $\mathbf{T}$. No
hypothesis on the grade is needed: the small system is solved by the pseudoinverse of
$\mathbf{T}$, which below the grade is $\mathbf{T}^{-1}$ (for positive definite $\mathbf{A}$) and
past it is $\operatorname{diag}(\mathbf{T}_\nu^{-1}, \mathbf{0})$, matching the zero columns of
the canonical basis, so the iterate is unchanged once the grade is reached.

## Main results

* `NLAlib.galerkinInverse_krylovMatrix_eq_arnoldiMatrix`: the Galerkin inverse in the canonical
  basis, every $q$.
* `NLAlib.cgIterate_eq_arnoldiMatrix`: the Lanczos basis yields CG.
* `Matrix.IsHermitian.cgIterate_eq_lanczosMatrix`: the Lanczos recurrence yields CG.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Galerkin inverse in the canonical basis**, for every $\mathbf{A}$ and $q$:
$\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{K}_q) =
\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{+}\mathbf{Q}^{\mathsf{H}}$ with
$\mathbf{Q}$ = `arnoldiMatrix A b q`, also past the grade, where $\mathbf{Q}$ has zero columns. -/
theorem galerkinInverse_krylovMatrix_eq_arnoldiMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    galerkinInverse A (krylovMatrix A b q) =
      arnoldiMatrix A b q * pinv ((arnoldiMatrix A b q)ᴴ * A * arnoldiMatrix A b q) *
        (arnoldiMatrix A b q)ᴴ := by
  have hQ := gramSchmidtQ_mul_conjTranspose_gramSchmidtQ_mul_self (krylovMatrix A b q)
  rw [← arnoldiMatrix] at hQ
  have hQ' : (arnoldiMatrix A b q)ᴴ * arnoldiMatrix A b q * (arnoldiMatrix A b q)ᴴ =
      (arnoldiMatrix A b q)ᴴ := by
    have h := congrArg Matrix.conjTranspose hQ
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      at h
  rw [galerkinInverse, ← gramSchmidtQ_mul_conjTranspose, ← arnoldiMatrix,
    show arnoldiMatrix A b q * (arnoldiMatrix A b q)ᴴ * A *
        (arnoldiMatrix A b q * (arnoldiMatrix A b q)ᴴ) =
      arnoldiMatrix A b q * (((arnoldiMatrix A b q)ᴴ * A * arnoldiMatrix A b q) *
        (arnoldiMatrix A b q)ᴴ) by simp only [Matrix.mul_assoc],
    pinv_mul_of_conjTranspose_mul_self_mul_eq (by simp only [← Matrix.mul_assoc, hQ']),
    pinv_mul_conjTranspose_of_mul_conjTranspose_mul_self_eq (by simp only [Matrix.mul_assoc, hQ]),
    Matrix.mul_assoc]

/-- **The Lanczos basis yields CG**, for every $\mathbf{A}$ and every $q$, with no grade
hypothesis: with $\mathbf{Q}$ the canonical basis of $\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{r}_0)$
and $\mathbf{T} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$,
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q + 1) =
\mathbf{x}_0 + \|\mathbf{r}_0\|\,\mathbf{Q}\mathbf{T}^{+}\mathbf{e}_0$. For positive definite
$\mathbf{A}$ and $q + 1 \le \nu$, $\mathbf{T}^{+} = \mathbf{T}^{-1}$ (`pinv_of_isUnit`).
[Saad2003, §6.7.1]. -/
theorem cgIterate_eq_arnoldiMatrix (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    cgIterate A b x₀ (q + 1) = x₀ + (‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ : 𝕜) •
      (arnoldiMatrix A (b - A *ᵥ x₀) (q + 1) *ᵥ
        (pinv ((arnoldiMatrix A (b - A *ᵥ x₀) (q + 1))ᴴ * A *
          arnoldiMatrix A (b - A *ᵥ x₀) (q + 1)) *ᵥ Pi.single 0 1)) := by
  rw [cgIterate, galerkinInverse_krylovMatrix_eq_arnoldiMatrix, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, conjTranspose_arnoldiMatrix_mulVec_self, Matrix.mulVec_smul,
    Matrix.mulVec_smul]

/-- **The Lanczos recurrence yields CG**: for Hermitian $\mathbf{A}$ and every $q$,
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q + 1) =
\mathbf{x}_0 + \|\mathbf{r}_0\|\,\mathbf{Q}\mathbf{T}^{+}\mathbf{e}_0$ with $\mathbf{Q}$ and
$\mathbf{T}$ computed by $q + 1$ steps of the recurrence from $\mathbf{r}_0$; past the grade the
recurrence has frozen at zero and the iterate is unchanged. [Saad2003, §6.7.1]. -/
theorem _root_.Matrix.IsHermitian.cgIterate_eq_lanczosMatrix {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b x₀ : n → 𝕜) (q : ℕ) :
    cgIterate A b x₀ (q + 1) = x₀ + (‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ : 𝕜) •
      (lanczosMatrix A (b - A *ᵥ x₀) (q + 1) *ᵥ
        (pinv (lanczosTridiagonal A (b - A *ᵥ x₀) (q + 1)) *ᵥ Pi.single 0 1)) := by
  rw [hA.lanczosMatrix_eq_arnoldiMatrix, hA.lanczosTridiagonal_eq, cgIterate_eq_arnoldiMatrix]

end NLAlib
