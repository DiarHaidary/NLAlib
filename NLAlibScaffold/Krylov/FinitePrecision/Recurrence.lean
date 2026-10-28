/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.LocalErrors
public import NLAlib.Matrix.Factorizations.Hessenberg
public import NLAlib.Matrix.Norms.Compare

/-!
# The perturbed Lanczos recurrence and Ritz residuals

The matrix form of the local error bounds of a run `L : NLAlib.LanczosRun n k`: with the computed
basis $\mathbf{V}_k = [\mathbf{v}_1, \dots, \mathbf{v}_k]$ (`L.basis`, column $j$ is
$\mathbf{v}_{j+1}$), the computed tridiagonal matrix $\mathbf{T}_k$ (`L.tridiagonal`, entries
indexed from $0$ as `NLAlib.lanczosTridiagonal`) and the residual matrix $\mathbf{F}_k$ of the
recurrence,
$$\mathbf{H}\mathbf{V}_k = \mathbf{V}_k\mathbf{T}_k
+ \beta_k\mathbf{v}_{k+1}\mathbf{e}_k^{\mathsf{T}} + \mathbf{F}_k,
\qquad \|\mathbf{F}_k\|_{\mathsf{F}} \le 6k^{3/2}\varepsilon\|\mathbf{H}\|_2 \,,$$
and its consequence for a Ritz pair $(\theta, \mathbf{V}_k\mathbf{y})$: the residual is the
scalar estimate $\beta_k\lvert y_k\rvert$ up to $O(\varepsilon\|\mathbf{H}\|_2)$.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `eq:governing`, `eq:ritz-residual-identity`, `eq:ritz-residual-bound`.

## Main definitions

* `NLAlib.LanczosRun.basis`, `NLAlib.LanczosRun.tridiagonal`, `NLAlib.LanczosRun.residual`,
  `NLAlib.LanczosRun.lastIndex`.

## Main results

* `NLAlib.LanczosRun.H_mul_basis`: the perturbed recurrence.
* `NLAlib.LanczosRun.frobNorm_residual_le`, `NLAlib.LanczosRun.specNorm_residual_le`: its residual.
* `NLAlib.LanczosRun.H_mulVec_basis_mulVec_sub_smul`: the Ritz residual identity.
* `NLAlib.LanczosRun.norm_H_mulVec_basis_mulVec_sub_smul_le`: the Ritz residual bound.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- The **computed Lanczos basis** $\mathbf{V}_k$: column $j$ is $\mathbf{v}_{j+1}$. -/
def basis : Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun i j => L.v ((j : ℕ) + 1) i

/-- The **computed tridiagonal matrix** $\mathbf{T}_k$, indexed from $0$:
$\alpha_{i+1}$ at $(i, i)$, and $\beta_i$ at $(i, i - 1)$ and $(i - 1, i)$. -/
def tridiagonal : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if i = j then L.α ((i : ℕ) + 1)
    else if (i : ℕ) = j + 1 then L.β i
    else if (j : ℕ) = i + 1 then L.β j
    else 0

/-- The **residual matrix** $\mathbf{F}_k$ of the recurrence: column $j$ is
`NLAlib.LanczosRun.recurrenceError L j`. -/
noncomputable def residual : Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun i j => L.recurrenceError j i

/-- The index $k - 1$ of the last column, as an element of `Fin k` (a run has $k \ge 1$). -/
def lastIndex : Fin k :=
  ⟨k - 1, Nat.sub_one_lt_of_lt L.k_pos⟩

/-- The computed tridiagonal matrix is symmetric. -/
theorem transpose_tridiagonal : L.tridiagonalᵀ = L.tridiagonal := by
  sorry

/-- The computed tridiagonal matrix is tridiagonal. -/
theorem isTridiagonal_tridiagonal : IsTridiagonal L.tridiagonal := by
  sorry

/-- **The perturbed Lanczos recurrence**: the computed basis satisfies
$$\mathbf{H}\mathbf{V}_k = \mathbf{V}_k\mathbf{T}_k
+ (\beta_k\mathbf{v}_{k+1})\mathbf{e}_{k-1}^{\mathsf{T}} + \mathbf{F}_k$$
($\mathbf{e}_{k-1}$ the last coordinate vector, indexed from $0$), an identity of the
definitions. No printed source; the maintainer's draft, `eq:governing`, writes it as
$\mathbf{V}_{k+1}\underline{\mathbf{T}}_k + \mathbf{F}_k$.
Proof: column by column, `NLAlib.LanczosRun.recurrenceError` and the conventions
$\mathbf{v}_0 = \mathbf{0}$, $\beta_0 = 0$; easy. -/
theorem H_mul_basis :
    L.H * L.basis = L.basis * L.tridiagonal +
      Matrix.vecMulVec (L.β k • L.v (k + 1)) (Pi.single L.lastIndex 1) + L.residual := by
  sorry

/-- **The residual of the perturbed recurrence is small**:
$\|\mathbf{F}_k\|_{\mathsf{F}} \le 6k\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, proof of `cor:gram-commutator`, uses
$\|\mathbf{F}_k\| \le \sqrt{k}\max_j\|\mathbf{f}_j\|$ (its formalization: $700k^2$).
Proof: `NLAlib.frobNorm_sq_eq_sum_col` and `NLAlib.LanczosRun.norm_recurrenceError_le`; easy. -/
theorem frobNorm_residual_le :
    frobNorm L.residual ≤ 6 * k * Real.sqrt k * L.ε * specNorm L.H := by
  sorry

/-- **The residual of the perturbed recurrence is small** in the spectral norm:
$\|\mathbf{F}_k\|_2 \le 6k\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, proof of `cor:gram-commutator`.
Proof: `NLAlib.specNorm_le_frobNorm` and `NLAlib.LanczosRun.frobNorm_residual_le`; easy. -/
theorem specNorm_residual_le :
    specNorm L.residual ≤ 6 * k * Real.sqrt k * L.ε * specNorm L.H := by
  sorry

/-- **The Ritz residual identity**: for an eigenpair $\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$
of the computed tridiagonal matrix, the Ritz vector $\mathbf{x} = \mathbf{V}_k\mathbf{y}$
satisfies
$$(\mathbf{H} - \theta\mathbf{I})\mathbf{x} = y_{k-1}\,(\beta_k\mathbf{v}_{k+1})
+ \mathbf{F}_k\mathbf{y}$$
($y_{k-1}$ the last entry, indexed from $0$). No printed source; the maintainer's draft,
`eq:ritz-residual-identity`.
Proof: apply `NLAlib.LanczosRun.H_mul_basis` to $\mathbf{y}$; easy. -/
theorem H_mulVec_basis_mulVec_sub_smul {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) :
    L.H *ᵥ (L.basis *ᵥ y) - θ • (L.basis *ᵥ y) =
      y L.lastIndex • (L.β k • L.v (k + 1)) + L.residual *ᵥ y := by
  sorry

/-- **The Ritz residual bound for finite-precision Lanczos**: for a unit eigenpair
$\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$, $\|\mathbf{y}\| = 1$, of the computed tridiagonal
matrix, the Ritz vector $\mathbf{x} = \mathbf{V}_k\mathbf{y}$ satisfies
$$\|\mathbf{H}\mathbf{x} - \theta\mathbf{x}\|
\le \sqrt{1 + \varepsilon}\,\beta_k\lvert y_{k-1}\rvert
+ 6k\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2 \,.$$
No printed source; the maintainer's draft, `eq:ritz-residual-bound`, with
$\|\mathbf{F}_k\|$ for the last term and both sides divided by $\|\mathbf{x}\|$.
Proof: `NLAlib.LanczosRun.H_mulVec_basis_mulVec_sub_smul`, the near-unit length of
$\mathbf{v}_{k+1}$ when $\beta_k \neq 0$ and `NLAlib.LanczosRun.specNorm_residual_le`; easy.
Result: lanczos-ritz-residual -/
theorem norm_H_mulVec_basis_mulVec_sub_smul_le {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    ‖WithLp.toLp 2 (L.H *ᵥ (L.basis *ᵥ y) - θ • (L.basis *ᵥ y))‖ ≤
      Real.sqrt (1 + L.ε) * L.β k * |y L.lastIndex| +
        6 * k * Real.sqrt k * L.ε * specNorm L.H := by
  sorry

end LanczosRun

end NLAlib
