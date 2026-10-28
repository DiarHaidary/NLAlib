/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.Paige
public import NLAlibScaffold.Krylov.FinitePrecision.Dilation
public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# A backward model for finite-precision Lanczos

The computed tridiagonal matrix of a run `L : NLAlib.LanczosRun n k` is exactly what $k$ steps of
exact Lanczos produce on a symmetric matrix $\tilde{\mathbf{H}}$ of dimension $n(k+1)$ that is
close to $\mathbf{I}_{k+1} \otimes \mathbf{H}$, from a starting vector whose spectral weights
with respect to $\mathbf{I}_{k+1} \otimes \mathbf{H}$ are those of the normalised
$\bar{\mathbf{v}}_1$ with respect to $\mathbf{H}$ (a Greenbaum-type backward model, with a
perturbation of order $k^4\varepsilon\|\mathbf{H}\|_2$).

The construction: normalise the computed vectors (`NLAlib.LanczosRun.normalized`, whose local
errors stay of order $j\varepsilon\|\mathbf{H}\|_2$); dilate them to orthonormal vectors
(`NLAlib.orthonormalDilation`), which satisfy the computed recurrence with the computed
coefficients up to a
residual $\hat{\mathbf{E}}$ (`NLAlib.LanczosRun.dilatedResidual`), controlled through the Gram
commutator of the normalised vectors; remove the residual by the symmetric perturbation
$\boldsymbol{\Delta} = -\hat{\mathbf{E}}\hat{\mathbf{V}}_k^{\mathsf{T}} -
\hat{\mathbf{V}}_k\hat{\mathbf{E}}^{\mathsf{T}}(\mathbf{I} - \hat{\mathbf{V}}_k
\hat{\mathbf{V}}_k^{\mathsf{T}})$.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `sec:backward`, `lem:normalized-errors`, `cor:normalized-commutator`,
`lem:exchange`, `lem:dilated-recurrence`, `thm:greenbaum`; [Greenbaum1989] for the original
model (perturbation of order $\varepsilon^{1/4}$), [Paige2010] for the augmented model of
dimension $n + k$.

## Main definitions

* `NLAlib.LanczosRun.normalizedV`, `NLAlib.LanczosRun.normalized`: the normalised run.
* `NLAlib.LanczosRun.dilatedH`, `NLAlib.LanczosRun.dilatedBasisSucc`,
  `NLAlib.LanczosRun.dilatedBasis`, `NLAlib.LanczosRun.dilatedStart`,
  `NLAlib.LanczosRun.dilatedResidual`: the dilated recurrence.
* `NLAlib.LanczosRun.backwardPerturbation`, `NLAlib.LanczosRun.backwardH`: the backward model.

## Main results

* `NLAlib.LanczosRun.frobNorm_dilatedResidual_le`: the dilated recurrence.
* `NLAlib.LanczosRun.backwardH_mul_dilatedBasis`,
  `NLAlib.LanczosRun.frobNorm_backwardH_sub_dilatedH_le`: the backward model.
* `NLAlib.lanczosState_eq_of_orthonormal_recurrence`,
  `NLAlib.lanczosState_beta_eq_of_orthonormal_recurrence`: an orthonormal three-term recurrence
  is the
  Lanczos recurrence.
* `NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`: exact Lanczos on the model
  computes $\mathbf{T}_k$.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-! ### Exact Lanczos from an orthonormal three-term recurrence -/

/-- **An orthonormal three-term recurrence is the Lanczos recurrence**: if
$\mathbf{u}_0 = \mathbf{0}$, $\mathbf{u}_1, \dots, \mathbf{u}_{k+1}$ are orthonormal,
$\mathbf{A}\mathbf{u}_{j+1} = \beta_j\mathbf{u}_j + \alpha_{j+1}\mathbf{u}_{j+1}
+ \beta_{j+1}\mathbf{u}_{j+2}$ for $j < k$, $\beta_0 = 0$, $\beta_j > 0$ for $1 \le j < k$ and
$\beta_k \ge 0$, then the Lanczos recurrence from $\mathbf{u}_1$ has state
$(\mathbf{u}_j, \mathbf{u}_{j+1}, \beta_j)$ before step $j < k$. No symmetry of $\mathbf{A}$ is
needed. [Saad2011, §6.6] for the exact recurrence.
Proof: induction on $j$ through `NLAlib.lanczosStep`; orthonormality gives the coefficient,
$\beta_{j+1} = \|\beta_{j+1}\mathbf{u}_{j+2}\|$ and the next vector; moderate. -/
theorem lanczosState_eq_of_orthonormal_recurrence {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {u : ℕ → ι → ℝ} {α β : ℕ → ℝ} {k : ℕ} (hu0 : u 0 = 0)
    (horth : ∀ i j, 1 ≤ i → i ≤ k + 1 → 1 ≤ j → j ≤ k + 1 →
      u i ⬝ᵥ u j = if i = j then 1 else 0)
    (hrec : ∀ j < k, A *ᵥ u (j + 1) = β j • u j + α (j + 1) • u (j + 1) + β (j + 1) • u (j + 2))
    (hβ0 : β 0 = 0) (hβ : ∀ j ≤ k, 0 ≤ β j) (hβpos : ∀ j, 1 ≤ j → j < k → 0 < β j) :
    ∀ j < k, lanczosState A (u 1) j = ⟨u j, u (j + 1), β j⟩ := by
  sorry

/-- Under the hypotheses of `NLAlib.lanczosState_eq_of_orthonormal_recurrence` the coefficient of
the Lanczos state after $k$ steps is $\beta_k$: with $\mathbf{u}_0 = \mathbf{0}$,
$\mathbf{u}_1, \dots, \mathbf{u}_{k+1}$ orthonormal, $\mathbf{A}\mathbf{u}_{j+1} =
\beta_j\mathbf{u}_j + \alpha_{j+1}\mathbf{u}_{j+1} + \beta_{j+1}\mathbf{u}_{j+2}$ for $j < k$,
$\beta_0 = 0$, $\beta_j > 0$ for $1 \le j < k$ and $\beta_k \ge 0$.
Proof: the last step of the induction; easy. -/
theorem lanczosState_beta_eq_of_orthonormal_recurrence {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {u : ℕ → ι → ℝ} {α β : ℕ → ℝ} {k : ℕ} (hu0 : u 0 = 0)
    (horth : ∀ i j, 1 ≤ i → i ≤ k + 1 → 1 ≤ j → j ≤ k + 1 →
      u i ⬝ᵥ u j = if i = j then 1 else 0)
    (hrec : ∀ j < k, A *ᵥ u (j + 1) = β j • u j + α (j + 1) • u (j + 1) + β (j + 1) • u (j + 2))
    (hβ0 : β 0 = 0) (hβ : ∀ j ≤ k, 0 ≤ β j) (hβpos : ∀ j, 1 ≤ j → j < k → 0 < β j) :
    (lanczosState A (u 1) k).beta = β k := by
  sorry

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-! ### The normalised run -/

/-- The **normalised Lanczos vectors** $\bar{\mathbf{v}}_j = \mathbf{v}_j/\|\mathbf{v}_j\|$
($\bar{\mathbf{v}}_0 = \mathbf{0}$); at a terminal last step ($\beta_k = 0$) the vector
$\bar{\mathbf{v}}_{k+1}$, which does not enter the recurrence, is taken to be
$\bar{\mathbf{v}}_1$. -/
noncomputable def normalizedV (j : ℕ) : Fin n → ℝ :=
  if j = k + 1 ∧ L.β k = 0 then ‖WithLp.toLp 2 (L.v 1)‖⁻¹ • L.v 1
  else ‖WithLp.toLp 2 (L.v j)‖⁻¹ • L.v j

/-- The **normalised run**: the computed coefficients with the normalised vectors. -/
noncomputable def normalized : LanczosData n k where
  H := L.H
  v := L.normalizedV
  α := L.α
  β := L.β
  transpose_H := L.transpose_H
  k_pos := L.k_pos
  v_zero := by
    have h : ¬(0 = k + 1 ∧ L.β k = 0) := fun h => by omega
    simp only [normalizedV, if_neg h, L.v_zero, smul_zero]
  β_zero := L.β_zero

/-- The normalised vectors $\bar{\mathbf{v}}_1, \dots, \bar{\mathbf{v}}_{k+1}$ are unit vectors.
Proof: $\|\mathbf{v}_j\|^2 \ge 1 - \varepsilon > 0$; easy. -/
theorem norm_normalizedV {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k + 1) :
    ‖WithLp.toLp 2 (L.normalizedV j)‖ = 1 := by
  sorry

/-- **Normalised local errors**: the normalised vectors satisfy the computed recurrence up to
$\|\bar{\mathbf{f}}_j\| \le 12(j + 1)\varepsilon\|\mathbf{H}\|_2$, $j < k$.
No printed source; the maintainer's draft, `lem:normalized-errors`, states
$\lesssim_k \varepsilon\|\mathbf{A}\|$.
Proof: $\bar{\mathbf{f}}_j - \mathbf{f}_j/\|\mathbf{v}_{j+1}\|$ is two terms
$\beta(\mathbf{v}/\|\mathbf{v}_{j+1}\| - \bar{\mathbf{v}})$, each at most $2\varepsilon\beta$ since
the norms are within $\varepsilon$ of $1$ in square; easy. -/
theorem norm_normalized_recurrenceError_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.normalized.recurrenceError j)‖ ≤ 12 * (j + 1) * L.ε * specNorm L.H := by
  sorry

/-- **Normalised local orthogonality**:
$\lvert\bar p_j\rvert \le 8(j + 1)\varepsilon\|\mathbf{H}\|_2$, $j < k$. No printed source; the
maintainer's draft, `lem:normalized-errors`.
Proof: $\bar p_j = p_j/(\|\mathbf{v}_{j+1}\|\|\mathbf{v}_{j+2}\|)$, or $0$ at a terminal step;
easy. -/
theorem abs_normalized_adjacentInner_le {j : ℕ} (hj : j < k) :
    |L.normalized.adjacentInner j| ≤ 8 * (j + 1) * L.ε * specNorm L.H := by
  sorry

/-- **The normalised Gram commutator is small**:
$\|\bar{\mathbf{M}}_k\|_2 \le 40k^2\varepsilon\|\mathbf{H}\|_2$. No printed source; the
maintainer's draft, `cor:normalized-commutator`.
Proof: `NLAlib.LanczosData.specNorm_gramCommutator_le` with no diagonal defects; easy. -/
theorem specNorm_normalized_gramCommutator_le :
    specNorm L.normalized.gramCommutator ≤ 40 * k ^ 2 * L.ε * specNorm L.H := by
  sorry

/-! ### The dilated recurrence -/

/-- The **dilated matrix** $\hat{\mathbf{H}} = \mathbf{I}_{k+1} \otimes \mathbf{H}$, block
diagonal with $k + 1$ copies of $\mathbf{H}$. -/
def dilatedH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  Matrix.blockDiagonal fun _ => L.H

/-- The **dilated vectors** $\hat{\mathbf{V}}_{k+1}$: the orthonormal dilation of the normalised
vectors $\bar{\mathbf{v}}_1, \dots, \bar{\mathbf{v}}_{k+1}$. -/
noncomputable def dilatedBasisSucc : Matrix (Fin n × Fin (k + 1)) (Fin (k + 1)) ℝ :=
  orthonormalDilation L.normalized.basisSucc

/-- The first $k$ dilated vectors $\hat{\mathbf{V}}_k$. -/
noncomputable def dilatedBasis : Matrix (Fin n × Fin (k + 1)) (Fin k) ℝ :=
  L.dilatedBasisSucc.submatrix id Fin.castSucc

/-- The **dilated starting vector** $(\bar{\mathbf{v}}_1, \mathbf{0}, \dots, \mathbf{0})$. -/
noncomputable def dilatedStart : Fin n × Fin (k + 1) → ℝ :=
  fun p => if (p.2 : ℕ) = 0 then L.normalizedV 1 p.1 else 0

/-- The tridiagonal matrix with the extra row, $\underline{\mathbf{T}}_k$
(`NLAlib.LanczosData.tridiagonalSucc` of the run). -/
def tridiagonalSucc : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  L.toLanczosData.tridiagonalSucc

/-- The **residual of the dilated recurrence**
$\hat{\mathbf{E}} = \hat{\mathbf{H}}\hat{\mathbf{V}}_k - \hat{\mathbf{V}}_{k+1}
\underline{\mathbf{T}}_k$. -/
noncomputable def dilatedResidual : Matrix (Fin n × Fin (k + 1)) (Fin k) ℝ :=
  L.dilatedH * L.dilatedBasis - L.dilatedBasisSucc * L.tridiagonalSucc

/-- **The dilated vectors are orthonormal**. No printed source; the maintainer's draft,
`lem:dilation`.
Proof: `NLAlib.hasOrthonormalCols_orthonormalDilation` and
`NLAlib.LanczosRun.norm_normalizedV`; easy. -/
theorem hasOrthonormalCols_dilatedBasisSucc : HasOrthonormalCols L.dilatedBasisSucc := by
  sorry

/-- The first dilated vector is the dilated starting vector. No printed source; the maintainer's
draft, `lem:dilation`.
Proof: `NLAlib.orthonormalDilation_apply_of_val_eq_zero`; easy. -/
theorem dilatedBasisSucc_col_zero : L.dilatedBasisSucc.col 0 = L.dilatedStart := by
  sorry

/-- **The dilated recurrence** (the exchange rule and the dilated residual): the orthonormal
dilated vectors satisfy the computed recurrence with the computed coefficients up to
$$\|\hat{\mathbf{E}}\|_{\mathsf{F}} =
\|\hat{\mathbf{H}}\hat{\mathbf{V}}_k - \hat{\mathbf{V}}_{k+1}\underline{\mathbf{T}}_k\|_{\mathsf{F}}
\le 1000k^4\varepsilon\|\mathbf{H}\|_2 \,.$$
No printed source; the maintainer's draft, `lem:exchange` and `lem:dilated-recurrence`, state
$\lesssim_k \varepsilon\|\mathbf{A}\|$ (its formalization: $240000k^6$ in the spectral norm).
Proof: block $r$ of $\hat{\mathbf{E}}$ is $\bar{\mathbf{F}}_k(\mathbf{C}\mathbf{K}^r)_k
+ \bar{\mathbf{V}}_{k+1}(\mathbf{Y}_r - \mathbf{Y}_{r+1})$ with $\mathbf{Y}_r =
\underline{\mathbf{T}}_k\mathbf{K}_k^r - \mathbf{K}^r\underline{\mathbf{T}}_k$,
$\mathbf{Y}_{r+1} = \mathbf{Y}_r\mathbf{K}_k + \mathbf{K}^r\mathbf{Y}_1$ and
$\mathbf{Y}_1 = \mathbf{C}(\underline{\mathbf{T}}_k\mathbf{R}_k
- \mathbf{R}\underline{\mathbf{T}}_k)
\mathbf{C}_k$; hard.
Result: lanczos-dilated-recurrence -/
theorem frobNorm_dilatedResidual_le :
    frobNorm L.dilatedResidual ≤ 1000 * k ^ 4 * L.ε * specNorm L.H := by
  sorry

/-! ### The backward model -/

/-- The **backward perturbation**
$\boldsymbol{\Delta} = -\hat{\mathbf{E}}\hat{\mathbf{V}}_k^{\mathsf{T}} -
\hat{\mathbf{V}}_k\hat{\mathbf{E}}^{\mathsf{T}}(\mathbf{I} - \hat{\mathbf{V}}_k
\hat{\mathbf{V}}_k^{\mathsf{T}})$. -/
noncomputable def backwardPerturbation : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  -(L.dilatedResidual * L.dilatedBasisᵀ) -
    L.dilatedBasis * L.dilatedResidualᵀ * (1 - L.dilatedBasis * L.dilatedBasisᵀ)

/-- The **backward model** $\tilde{\mathbf{H}} = \mathbf{I}_{k+1} \otimes \mathbf{H} +
\boldsymbol{\Delta}$. -/
noncomputable def backwardH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  L.dilatedH + L.backwardPerturbation

/-- The backward model is symmetric.
Proof: $\hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{E}} = \hat{\mathbf{V}}_k^{\mathsf{T}}
\hat{\mathbf{H}}\hat{\mathbf{V}}_k - \mathbf{T}_k$ is symmetric; easy. -/
theorem transpose_backwardH : L.backwardHᵀ = L.backwardH := by
  sorry

/-- **The backward model satisfies the computed recurrence exactly**:
$\tilde{\mathbf{H}}\hat{\mathbf{V}}_k = \hat{\mathbf{V}}_{k+1}\underline{\mathbf{T}}_k$ with
$\hat{\mathbf{V}}_{k+1}$ orthonormal. No printed source; the maintainer's draft, `thm:greenbaum`.
Proof: $\boldsymbol{\Delta}\hat{\mathbf{V}}_k = -\hat{\mathbf{E}}$ since
$\hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{V}}_k = \mathbf{I}$; easy. -/
theorem backwardH_mul_dilatedBasis :
    L.backwardH * L.dilatedBasis = L.dilatedBasisSucc * L.tridiagonalSucc := by
  sorry

/-- **Greenbaum-type backward model for finite-precision Lanczos**: the symmetric backward model
$\tilde{\mathbf{H}}$ is close to $\mathbf{I}_{k+1} \otimes \mathbf{H}$,
$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}}
\le 2000k^4\varepsilon\|\mathbf{H}\|_2 \,,$$
and it satisfies the computed recurrence exactly with orthonormal vectors
(`NLAlib.LanczosRun.backwardH_mul_dilatedBasis`), so exact Lanczos on it from the dilated
starting vector computes $\mathbf{T}_k$ and $\beta_k$
(`NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`).
No printed source; the maintainer's draft, `thm:greenbaum`, states
$\|\boldsymbol{\Delta}\| \lesssim_k \varepsilon\|\mathbf{A}\|$ (its formalization:
$480000k^6$ in the spectral norm); the Frobenius norm here is at least the spectral norm.
[Greenbaum1989] has a perturbation of order $\varepsilon^{1/4}$.
Proof: $\|\hat{\mathbf{E}}\hat{\mathbf{V}}_k^{\mathsf{T}}\|_{\mathsf{F}} \le
\|\hat{\mathbf{E}}\|_{\mathsf{F}}$ and the projector has norm at most $1$; then
`NLAlib.LanczosRun.frobNorm_dilatedResidual_le`; easy.
Result: greenbaum-backward-model -/
theorem frobNorm_backwardH_sub_dilatedH_le :
    frobNorm (L.backwardH - L.dilatedH) ≤ 2000 * k ^ 4 * L.ε * specNorm L.H := by
  sorry

/-- **Exact Lanczos on the backward model computes the computed tridiagonal matrix**: $k$ steps
of the Lanczos recurrence on $\tilde{\mathbf{H}}$ from
$(\bar{\mathbf{v}}_1, \mathbf{0}, \dots, \mathbf{0})$ give $\mathbf{T}_k$.
No printed source; the maintainer's draft, `thm:greenbaum`.
Proof: `NLAlib.lanczosState_eq_of_orthonormal_recurrence` with the columns of
$\hat{\mathbf{V}}_{k+1}$; easy. -/
theorem lanczosTridiagonal_backwardH_dilatedStart :
    lanczosTridiagonal L.backwardH L.dilatedStart k = L.tridiagonal := by
  sorry

/-- Exact Lanczos on the backward model computes the dilated vectors:
`lanczosMatrix` of $\tilde{\mathbf{H}}$ from the dilated start is $\hat{\mathbf{V}}_k$.
Proof: as `NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`; easy. -/
theorem lanczosMatrix_backwardH_dilatedStart :
    lanczosMatrix L.backwardH L.dilatedStart k = L.dilatedBasis := by
  sorry

/-- Exact Lanczos on the backward model computes the last coefficient: $\beta_k$ is the
coefficient of the state after $k$ steps.
Proof: as `NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`; easy. -/
theorem lanczosState_backwardH_dilatedStart_beta :
    (lanczosState L.backwardH L.dilatedStart k).beta = L.β k := by
  sorry

end LanczosRun

end NLAlib
