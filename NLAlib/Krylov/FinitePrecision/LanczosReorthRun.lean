/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosData
public import NLAlib.Matrix.Perturbation.OrthErr

/-!
# Finite-precision Lanczos runs with full reorthogonalization

`NLAlib.LanczosReorthRun n k` is the data of $k$ computed steps of Lanczos with full
reorthogonalization in Paige's order and the local guarantees that rounded execution supplies:
the local errors of `NLAlib.LanczosRun` for the product and the two updates, the stored norm
$\nu_j$ of $\mathbf{z}_j$, the orthogonalization guarantee `NLAlib.IsOrthErr` of
$\mathbf{z}_j$ against $\mathbf{v}_1, \dots, \mathbf{v}_j$ (parameters $\eta_0$,
$\varepsilon_1$, $\varepsilon_2$, $\varepsilon_3$), the normalization, and strict
$\tau$-admissibility $\tau\nu_j < \beta_j$ of every step (the stopping criterion of
[Paige1970] in contract form). It is not a `NLAlib.LanczosRun`: the reorthogonalization
correction is absolute, not relative to $\|\mathbf{w}_j\|$. Indices as in `NLAlib.LanczosRun`:
$\mathbf{v}_0 = \mathbf{0}$, steps $j + 1$ for $j < k$, coefficient $h_{j+1, i}$ of
$\mathbf{z}_{j+1}$ against $\mathbf{v}_{i+1}$ for $i \le j$. Design:
`docs/design/Krylov-LanczosReorth.md` §3.1.

## Main definitions

* `NLAlib.LanczosReorthRun`: the run.
* `NLAlib.LanczosReorthRun.basisOf`: the first $m$ vectors as a matrix.
* `NLAlib.LanczosReorthRun.toLanczosData`: the underlying three-term data.
* `NLAlib.LanczosReorthRun.orthLevel`, `NLAlib.LanczosReorthRun.recLevel`: the per-column
  orthogonality level $\mu$ and the recurrence level $\mu + \varepsilon + \varepsilon_2$.
* `NLAlib.LanczosReorthRun.backwardRadius`, `NLAlib.LanczosReorthRun.colSeq`: the backward
  radius and the columns of a basis as a sequence.
* `NLAlib.reorthSteps`: the admissible prefix read off computed outputs.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- The first $m$ vectors $\mathbf{v}_1, \dots, \mathbf{v}_m$ of a sequence as the columns of an
$n \times m$ matrix. -/
def LanczosReorthRun.basisOf {n : ℕ} (v : ℕ → Fin n → ℝ) (m : ℕ) : Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun i c => v ((c : ℕ) + 1) i

/-- **A finite-precision Lanczos run with full reorthogonalization**, $k \ge 1$ steps. -/
structure LanczosReorthRun (n k : ℕ) where
  /-- The matrix. -/
  H : Matrix (Fin n) (Fin n) ℝ
  /-- The Lanczos vectors $\mathbf{v}_j$. -/
  v : ℕ → Fin n → ℝ
  /-- The products $\mathbf{u}_j$. -/
  u : ℕ → Fin n → ℝ
  /-- The vectors $\mathbf{w}_j$. -/
  w : ℕ → Fin n → ℝ
  /-- The vectors $\mathbf{z}_j$ before orthogonalization. -/
  z : ℕ → Fin n → ℝ
  /-- The vectors $\mathbf{z}_j'$ after orthogonalization. -/
  z' : ℕ → Fin n → ℝ
  /-- The diagonal coefficients $\alpha_j$. -/
  α : ℕ → ℝ
  /-- The off-diagonal coefficients $\beta_j$. -/
  β : ℕ → ℝ
  /-- The stored norms $\nu_j$ of $\mathbf{z}_j$. -/
  ν : ℕ → ℝ
  /-- The reorthogonalization coefficients $h_{j,i}$ (discarded by the program). -/
  h : ℕ → ℕ → ℝ
  /-- The error of the product. -/
  eu : ℕ → Fin n → ℝ
  /-- The error of the first update. -/
  ew : ℕ → Fin n → ℝ
  /-- The error of the second update. -/
  ez : ℕ → Fin n → ℝ
  /-- The error of the inner product. -/
  eα : ℕ → ℝ
  /-- The error of the normalization. -/
  δ : ℕ → Fin n → ℝ
  /-- The scalar accuracy parameter. -/
  ε : ℝ
  /-- The admissibility threshold. -/
  τ : ℝ
  /-- The orthogonality precondition of the scheme. -/
  η₀ : ℝ
  /-- The output-relative orthogonality parameter of the scheme. -/
  ε₁ : ℝ
  /-- The residual parameter of the scheme. -/
  ε₂ : ℝ
  /-- The input-relative orthogonality parameter of the scheme. -/
  ε₃ : ℝ
  /-- The matrix is symmetric. -/
  transpose_H : Hᵀ = H
  /-- The scalar accuracy parameter is nonnegative. -/
  ε_nonneg : 0 ≤ ε
  /-- Local accuracy. -/
  ε_le : ε ≤ 1 / 100
  /-- The scheme parameters are nonnegative. -/
  ε₁_nonneg : 0 ≤ ε₁
  /-- The scheme parameters are nonnegative. -/
  ε₂_nonneg : 0 ≤ ε₂
  /-- The scheme parameters are nonnegative. -/
  ε₃_nonneg : 0 ≤ ε₃
  /-- At least one step. -/
  k_pos : 0 < k
  /-- $\mathbf{v}_0 = \mathbf{0}$. -/
  v_zero : v 0 = 0
  /-- $\beta_0 = 0$. -/
  β_zero : β 0 = 0
  /-- The computed product. -/
  u_eq : ∀ j < k, u (j + 1) = H *ᵥ v (j + 1) + eu (j + 1)
  /-- The product error. -/
  norm_eu_le : ∀ j < k,
    ‖WithLp.toLp 2 (eu (j + 1))‖ ≤ ε * specNorm H * ‖WithLp.toLp 2 (v (j + 1))‖
  /-- The first update. -/
  w_eq : ∀ j < k, w (j + 1) = u (j + 1) - β j • v j + ew (j + 1)
  /-- The first update error. -/
  norm_ew_le : ∀ j < k, ‖WithLp.toLp 2 (ew (j + 1))‖ ≤
    ε * (‖WithLp.toLp 2 (u (j + 1))‖ + |β j| * ‖WithLp.toLp 2 (v j)‖)
  /-- The inner product. -/
  α_eq : ∀ j < k, α (j + 1) = v (j + 1) ⬝ᵥ w (j + 1) + eα (j + 1)
  /-- The inner product error. -/
  abs_eα_le : ∀ j < k,
    |eα (j + 1)| ≤ ε * ‖WithLp.toLp 2 (v (j + 1))‖ * ‖WithLp.toLp 2 (w (j + 1))‖
  /-- The second update. -/
  z_eq : ∀ j < k, z (j + 1) = w (j + 1) - α (j + 1) • v (j + 1) + ez (j + 1)
  /-- The second update error. -/
  norm_ez_le : ∀ j < k, ‖WithLp.toLp 2 (ez (j + 1))‖ ≤
    ε * (‖WithLp.toLp 2 (w (j + 1))‖ + |α (j + 1)| * ‖WithLp.toLp 2 (v (j + 1))‖)
  /-- The stored norm before orthogonalization. -/
  abs_ν_sub_le : ∀ j < k, |ν (j + 1) - ‖WithLp.toLp 2 (z (j + 1))‖| ≤
    ε * ‖WithLp.toLp 2 (z (j + 1))‖
  /-- The orthogonalization guarantee against $\mathbf{v}_1, \dots, \mathbf{v}_{j+1}$. -/
  orth_eq : ∀ j < k, IsOrthErr η₀ ε₁ ε₂ ε₃ (LanczosReorthRun.basisOf v (j + 1)) (z (j + 1))
    (fun i => h (j + 1) i) (z' (j + 1))
  /-- The computed norm after orthogonalization. -/
  abs_β_sub_le : ∀ j < k, |β (j + 1) - ‖WithLp.toLp 2 (z' (j + 1))‖| ≤
    ε * ‖WithLp.toLp 2 (z' (j + 1))‖
  /-- The normalization. -/
  smul_v_eq : ∀ j < k, β (j + 1) • v (j + 2) = z' (j + 1) + δ (j + 1)
  /-- The normalization error. -/
  norm_δ_le : ∀ j < k, ‖WithLp.toLp 2 (δ (j + 1))‖ ≤ ε * ‖WithLp.toLp 2 (z' (j + 1))‖
  /-- Nearly unit Lanczos vectors, the next one included. -/
  abs_norm_v_sq_sub_one_le : ∀ j, 1 ≤ j → j ≤ k + 1 → |‖WithLp.toLp 2 (v j)‖ ^ 2 - 1| ≤ ε
  /-- Strict $\tau$-admissibility of every step (so $\beta_j > 0$). -/
  admissible : ∀ j < k, τ * ν (j + 1) < β (j + 1)
  /-- The threshold is positive. -/
  τ_pos : 0 < τ

namespace LanczosReorthRun

variable {n k : ℕ} (L : LanczosReorthRun n k)

/-- The underlying symmetric three-term data (forgetting the local errors). -/
def toLanczosData : LanczosData n k where
  H := L.H
  v := L.v
  α := L.α
  β := L.β
  transpose_H := L.transpose_H
  k_pos := L.k_pos
  v_zero := L.v_zero
  β_zero := L.β_zero

/-- **The per-column orthogonality level** $\mu = 2(\varepsilon_1 + \varepsilon_3/\tau +
\varepsilon)$: a bound for $\|\mathbf{V}_j^{\mathsf{T}}\mathbf{v}_{j+1}\|$ and
$|\|\mathbf{v}_{j+1}\|^2 - 1|$ on an admissible step. -/
noncomputable def orthLevel : ℝ :=
  2 * (L.ε₁ + L.ε₃ / L.τ + L.ε)

/-- **The recurrence level** $\mu + \varepsilon + \varepsilon_2$, the size (relative to
$\|\mathbf{H}\|_2$) of one column of the residual of the three-term relation. -/
noncomputable def recLevel : ℝ :=
  L.orthLevel + L.ε + L.ε₂

/-- **The backward radius** $100(k+1)\,(\mu + \varepsilon + \varepsilon_2)\,\|\mathbf{H}\|_2$, the
bound on the symmetric backward perturbation of the run. -/
noncomputable def backwardRadius : ℝ :=
  100 * ((k : ℝ) + 1) * L.recLevel * specNorm L.H

/-- The columns of an $n \times (k + 1)$ matrix as a sequence indexed from $1$
($\mathbf{u}_0 = \mathbf{0}$, $\mathbf{u}_j$ column $j - 1$ for $1 \le j \le k + 1$, zero beyond),
in the indexing of `NLAlib.lanczosState_eq_of_orthonormal_recurrence`. -/
def colSeq (U : Matrix (Fin n) (Fin (k + 1)) ℝ) (j : ℕ) : Fin n → ℝ :=
  fun i => if h : 1 ≤ j ∧ j ≤ k + 1 then U i ⟨j - 1, by omega⟩ else 0

end LanczosReorthRun

/-- **The admissible prefix** read off computed outputs: the number of leading steps
$j = 1, 2, \dots$ (at most $q$) with $\tau\nu_j < \beta_j$, the coefficients indexed as the
program stores them ($\nu_j$ at `nu[j-1]`, $\beta_j$ at `beta[j]`). -/
noncomputable def reorthSteps (τ : ℝ) (ν β : ℕ → ℝ) (q : ℕ) : ℕ :=
  ((List.range q).takeWhile fun j => τ * ν j < β (j + 1)).length

end NLAlib
