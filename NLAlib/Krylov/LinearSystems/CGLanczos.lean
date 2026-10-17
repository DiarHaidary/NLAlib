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

For positive definite $\mathbf{A}$ and $q \le \nu$, the CG iterate is
$\|\mathbf{b}\|\,\mathbf{Q}\mathbf{T}^{-1}\mathbf{e}_0$ with $\mathbf{Q}$ the Lanczos basis and
$\mathbf{T} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ tridiagonal: the Lanczos basis yields CG,
and so do the basis and tridiagonal matrix computed by the Lanczos recurrence. The grade
hypothesis is needed: past the grade $\mathbf{T}$ is singular, its inverse is $\mathbf{0}$, and
the right side is $\mathbf{0}$.

## Main results

* `Matrix.PosDef.cgIterate_eq_arnoldiMatrix`: the Lanczos basis yields CG.
* `Matrix.PosDef.cgIterate_eq_lanczosMatrix`: the Lanczos recurrence yields CG.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Lanczos basis yields CG**: for positive definite $\mathbf{A}$ and $q + 1 \le \nu$, with
$\mathbf{Q}$ the canonical basis of $\mathcal{K}_{q+1}$ and
$\mathbf{T} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ (tridiagonal),
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q + 1) =
\|\mathbf{b}\|\,\mathbf{Q}\mathbf{T}^{-1}\mathbf{e}_0$. [Saad2003, §6.7.1]. -/
theorem _root_.Matrix.PosDef.cgIterate_eq_arnoldiMatrix {A : Matrix n n 𝕜} (hA : A.PosDef)
    {b : n → 𝕜} {q : ℕ} (h : q + 1 ≤ krylovGrade A b) :
    cgIterate A b (q + 1) = (‖WithLp.toLp 2 b‖ : 𝕜) • (arnoldiMatrix A b (q + 1) *ᵥ
      (((arnoldiMatrix A b (q + 1))ᴴ * A * arnoldiMatrix A b (q + 1))⁻¹ *ᵥ Pi.single 0 1)) := by
  rw [hA.cgIterate_eq (hasOrthonormalCols_arnoldiMatrix_iff.mpr h) (range_arnoldiMatrix A b _),
    conjTranspose_arnoldiMatrix_mulVec_self, Matrix.mulVec_smul, Matrix.mulVec_smul]

/-- **The Lanczos recurrence yields CG**: for positive definite $\mathbf{A}$ and $q + 1 \le \nu$,
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q + 1) =
\|\mathbf{b}\|\,\mathbf{Q}\mathbf{T}^{-1}\mathbf{e}_0$ with $\mathbf{Q}$ and $\mathbf{T}$ computed
by $q + 1$ steps of the recurrence. [Saad2003, §6.7.1]. -/
theorem _root_.Matrix.PosDef.cgIterate_eq_lanczosMatrix {A : Matrix n n 𝕜} (hA : A.PosDef)
    {b : n → 𝕜} {q : ℕ} (h : q + 1 ≤ krylovGrade A b) :
    cgIterate A b (q + 1) = (‖WithLp.toLp 2 b‖ : 𝕜) • (lanczosMatrix A b (q + 1) *ᵥ
      ((lanczosTridiagonal A b (q + 1))⁻¹ *ᵥ Pi.single 0 1)) := by
  rw [hA.isHermitian.lanczosMatrix_eq_arnoldiMatrix, hA.isHermitian.lanczosTridiagonal_eq,
    hA.cgIterate_eq_arnoldiMatrix h]

end NLAlib
