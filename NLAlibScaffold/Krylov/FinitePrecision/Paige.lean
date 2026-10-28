/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.Recurrence

/-!
# Paige's loss-of-orthogonality bound

For a run `L : NLAlib.LanczosRun n k`, split the Gram matrix of the computed basis as
$\mathbf{V}_k^{\mathsf{T}}\mathbf{V}_k = \mathbf{I} + \mathbf{R}_k^{\mathsf{T}} + \mathbf{\Gamma}
+ \mathbf{R}_k$ with $\mathbf{R}_k$ strictly upper triangular and $\mathbf{\Gamma}$ diagonal. The
**Gram commutator**
$\mathbf{M}_k = \mathbf{T}_k\mathbf{R}_k - \mathbf{R}_k\mathbf{T}_k
- (\mathbf{V}_k^{\mathsf{T}}\beta_k\mathbf{v}_{k+1})\mathbf{e}_k^{\mathsf{T}}$ is upper triangular
and of size $O(k^2\varepsilon\|\mathbf{H}\|_2)$, although $\mathbf{R}_k$ itself need not be small.
In the quadratic form of an eigenvector of $\mathbf{T}_k$ the commutator vanishes, which gives
Paige's bound: a Ritz vector loses orthogonality to $\mathbf{v}_{k+1}$ only when its scalar
residual estimate $\beta_k\lvert y_k\rvert$ is small, that is, only after it has converged.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `eq:M-def`, `cor:gram-commutator`, `lem:gram-commutator`, `thm:paige`;
[Paige1980, (3.11)–(3.13)] for the bound under Paige's rounding model.

## Main definitions

* `NLAlib.LanczosRun.gramStrictUpper`, `NLAlib.LanczosRun.normSqDefect`: the strict upper
  triangle $\mathbf{R}_k$ and the diagonal defects $\mathbf{\Gamma}$ of the Gram matrix.
* `NLAlib.LanczosRun.gramCommutator`: the Gram commutator $\mathbf{M}_k$.

## Main results

* `NLAlib.LanczosRun.isUpperTriangular_gramCommutator`,
  `NLAlib.LanczosRun.gramCommutator_sub_transpose`,
  `NLAlib.LanczosRun.specNorm_gramCommutator_le`: the Gram commutator.
* `NLAlib.LanczosRun.abs_basis_mulVec_dotProduct_mul_abs_le`: Paige's bound.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- The **strict upper triangle of the Gram matrix** of the computed basis:
$(\mathbf{R}_k)_{i,j} = \mathbf{v}_{i+1}^{\mathsf{T}}\mathbf{v}_{j+1}$ for $i < j$, and $0$
otherwise. -/
def gramStrictUpper : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => if i < j then L.v ((i : ℕ) + 1) ⬝ᵥ L.v ((j : ℕ) + 1) else 0

/-- The **diagonal defects** of the Gram matrix of the computed basis:
$\gamma_i = \|\mathbf{v}_{i+1}\|^2 - 1$ (the paper's $g_{i+1}$). -/
noncomputable def normSqDefect (i : Fin k) : ℝ :=
  ‖WithLp.toLp 2 (L.v ((i : ℕ) + 1))‖ ^ 2 - 1

/-- The **Gram commutator**
$\mathbf{M}_k = \mathbf{T}_k\mathbf{R}_k - \mathbf{R}_k\mathbf{T}_k
- (\mathbf{V}_k^{\mathsf{T}}\beta_k\mathbf{v}_{k+1})\mathbf{e}_{k-1}^{\mathsf{T}}$
(`eq:M-def` of the maintainer's draft; $\mathbf{e}_{k-1}$ the last coordinate vector, indexed
from $0$). -/
noncomputable def gramCommutator : Matrix (Fin k) (Fin k) ℝ :=
  L.tridiagonal * L.gramStrictUpper - L.gramStrictUpper * L.tridiagonal -
    Matrix.vecMulVec (L.basisᵀ *ᵥ (L.β k • L.v (k + 1))) (Pi.single L.lastIndex 1)

/-- The Gram commutator is upper triangular. No printed source; the maintainer's draft,
`lem:gram-commutator`.
Proof: a tridiagonal times a strictly upper triangular matrix is upper triangular, and the last
term lives in the last column; easy. -/
theorem isUpperTriangular_gramCommutator : L.gramCommutator.IsUpperTriangular := by
  sorry

/-- **The skew part of the Gram commutator** is given by the residual and the diagonal defects:
$$\mathbf{M}_k - \mathbf{M}_k^{\mathsf{T}} = \mathbf{V}_k^{\mathsf{T}}\mathbf{F}_k
- \mathbf{F}_k^{\mathsf{T}}\mathbf{V}_k
- (\mathbf{T}_k\mathbf{\Gamma} - \mathbf{\Gamma}\mathbf{T}_k),
\qquad \mathbf{\Gamma} = \operatorname{diag}(\|\mathbf{v}_{i+1}\|^2 - 1)_i \,.$$
No printed source; the maintainer's draft, `eq:generic-commutator`.
Proof: `NLAlib.LanczosRun.H_mul_basis` multiplied by $\mathbf{V}_k^{\mathsf{T}}$ is symmetric on
the left; subtract the transpose and split the Gram matrix; moderate. -/
theorem gramCommutator_sub_transpose :
    L.gramCommutator - L.gramCommutatorᵀ =
      L.basisᵀ * L.residual - L.residualᵀ * L.basis -
        (L.tridiagonal * Matrix.diagonal L.normSqDefect -
          Matrix.diagonal L.normSqDefect * L.tridiagonal) := by
  sorry

/-- **The Gram commutator is small**:
$\|\mathbf{M}_k\|_2 \le 30k^2\varepsilon\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `cor:gram-commutator`, states
$\|\mathbf{M}_k\| \lesssim_k \varepsilon\|\mathbf{A}\|$ (its formalization: $3000k^3$); here the
strict upper part is bounded in the Frobenius norm by that of
`NLAlib.LanczosRun.gramCommutator_sub_transpose`, and the diagonal entry by entry, which saves a
factor $k$. [Paige1976, (22)]; [Paige1980, (2.17)–(2.18)].
Proof: diagonal entries are differences of `NLAlib.LanczosRun.adjacentInner`; the strict upper
part through `NLAlib.LanczosRun.gramCommutator_sub_transpose`,
`NLAlib.frobNorm_mul_le_specNorm_mul_frobNorm` and `NLAlib.LanczosRun.frobNorm_residual_le`;
moderate.
Result: lanczos-gram-commutator -/
theorem specNorm_gramCommutator_le :
    specNorm L.gramCommutator ≤ 30 * k ^ 2 * L.ε * specNorm L.H := by
  sorry

/-- **Paige's loss-of-orthogonality bound**: for a unit eigenpair
$\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$, $\|\mathbf{y}\| = 1$, of the computed tridiagonal
matrix, the Ritz vector $\mathbf{x} = \mathbf{V}_k\mathbf{y}$ satisfies
$$\lvert\mathbf{x}^{\mathsf{T}}(\beta_k\mathbf{v}_{k+1})\rvert\,\lvert y_{k-1}\rvert
\le 30k^2\varepsilon\|\mathbf{H}\|_2$$
($y_{k-1}$ the last entry, indexed from $0$): orthogonality to $\mathbf{v}_{k+1}$ is lost only
along Ritz vectors whose residual estimate $\beta_k\lvert y_{k-1}\rvert$ is small.
No printed source; the maintainer's draft, `thm:paige`, states
$\lvert\mathbf{x}^{\mathsf{T}}\mathbf{v}_{k+1}\rvert\beta_k\lvert\mathbf{e}_k^{\mathsf{T}}
\mathbf{y}\rvert \lesssim_k \varepsilon\|\mathbf{A}\|$ (its formalization: $3000k^3$);
[Paige1980, (3.11)–(3.13)].
Proof: $\mathbf{y}^{\mathsf{T}}(\mathbf{T}_k\mathbf{R}_k - \mathbf{R}_k\mathbf{T}_k)\mathbf{y} = 0$,
so the left side is $\lvert\mathbf{y}^{\mathsf{T}}\mathbf{M}_k\mathbf{y}\rvert$; then
`NLAlib.LanczosRun.specNorm_gramCommutator_le`; easy.
Result: paige-loss-of-orthogonality -/
theorem abs_basis_mulVec_dotProduct_mul_abs_le {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    |(L.basis *ᵥ y) ⬝ᵥ (L.β k • L.v (k + 1))| * |y L.lastIndex| ≤
      30 * k ^ 2 * L.ε * specNorm L.H := by
  sorry

end LanczosRun

end NLAlib
