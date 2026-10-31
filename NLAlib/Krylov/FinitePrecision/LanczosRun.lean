/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Spectral

/-!
# A Lanczos run with bounded local errors

`NLAlib.LanczosRun n k` is $k$ steps of the symmetric Lanczos recurrence in Paige's ordering A(1)
with a local error in each of its five operations, each bounded relative to its operands by one
accuracy parameter $\varepsilon$, and nearly unit Lanczos vectors:
$$\mathbf{u}_j = \mathbf{H}\mathbf{v}_j + \mathbf{e}^u_j,\quad
\mathbf{w}_j = \mathbf{u}_j - \beta_{j-1}\mathbf{v}_{j-1} + \mathbf{e}^w_j,\quad
\alpha_j = \mathbf{v}_j^{\mathsf{T}}\mathbf{w}_j + e^\alpha_j,\quad
\mathbf{z}_j = \mathbf{w}_j - \alpha_j\mathbf{v}_j + \mathbf{e}^z_j,\quad
\beta_j\mathbf{v}_{j+1} = \mathbf{z}_j + \boldsymbol{\delta}_j .$$
It is the interface between the rounding-error analysis of the Lanczos program in the standard
model of floating-point arithmetic, which constructs one from a run of the program, and the
stability analysis (local errors, Paige's theorem, the Greenbaum backward model), which never
mentions the model of computation.
Indices as in the paper: $\mathbf{v}_0 = \mathbf{0}$, $\beta_0 = 0$, steps $j = 1, \dots, k$.


## Main definitions

* `NLAlib.LanczosRun`: a run of $k$ steps with accuracy parameter $\varepsilon$.
* `NLAlib.LanczosRun.ofLE`: the same run with a larger accuracy parameter.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-- **A Lanczos run with bounded local errors** [Chen, `sec:model`, Assumptions
`ass:arithmetic`, `ass:normalization`, `ass:small-eps`]: $k \ge 1$ steps of the recurrence in
Paige's ordering A(1) for a real symmetric $\mathbf{H}$, each operation exact up to an error
bounded by $\varepsilon$ times its operands, the Lanczos vectors nearly unit
($\lvert\|\mathbf{v}_j\|^2 - 1\rvert \le \varepsilon$), $\beta_j > 0$ before the last step,
$\beta_k \ge 0$ (the last step may be terminal), and $k\varepsilon \le 1/100$.
Algorithm: lanczos (run model) -/
structure LanczosRun (n k : ℕ) where
  /-- The matrix. -/
  H : Matrix (Fin n) (Fin n) ℝ
  /-- The Lanczos vectors $\mathbf{v}_j$. -/
  v : ℕ → Fin n → ℝ
  /-- The products $\mathbf{u}_j$. -/
  u : ℕ → Fin n → ℝ
  /-- The vectors $\mathbf{w}_j$. -/
  w : ℕ → Fin n → ℝ
  /-- The unnormalised next vectors $\mathbf{z}_j$. -/
  z : ℕ → Fin n → ℝ
  /-- The diagonal coefficients $\alpha_j$. -/
  α : ℕ → ℝ
  /-- The off-diagonal coefficients $\beta_j$. -/
  β : ℕ → ℝ
  /-- The error of the product. -/
  eu : ℕ → Fin n → ℝ
  /-- The error of the first update. -/
  ew : ℕ → Fin n → ℝ
  /-- The error of the second update. -/
  ez : ℕ → Fin n → ℝ
  /-- The error of the inner product. -/
  eα : ℕ → ℝ
  /-- The error of the normalisation. -/
  δ : ℕ → Fin n → ℝ
  /-- The accuracy parameter. -/
  ε : ℝ
  /-- The matrix is symmetric. -/
  transpose_H : Hᵀ = H
  /-- The accuracy parameter is nonnegative. -/
  ε_nonneg : 0 ≤ ε
  /-- At least one step. -/
  k_pos : 0 < k
  /-- Small accuracy parameter (`ass:small-eps`). -/
  k_mul_ε_le : (k : ℝ) * ε ≤ 1 / 100
  /-- $\mathbf{v}_0 = \mathbf{0}$. -/
  v_zero : v 0 = 0
  /-- $\beta_0 = 0$. -/
  β_zero : β 0 = 0
  /-- The computed product (`eq:local-u`). -/
  u_eq : ∀ j < k, u (j + 1) = H *ᵥ v (j + 1) + eu (j + 1)
  /-- The product error (`ass:arithmetic`). -/
  norm_eu_le : ∀ j < k,
    ‖WithLp.toLp 2 (eu (j + 1))‖ ≤ ε * specNorm H * ‖WithLp.toLp 2 (v (j + 1))‖
  /-- The first update (`eq:local-w`). -/
  w_eq : ∀ j < k, w (j + 1) = u (j + 1) - β j • v j + ew (j + 1)
  /-- The first update error. -/
  norm_ew_le : ∀ j < k, ‖WithLp.toLp 2 (ew (j + 1))‖ ≤
    ε * (‖WithLp.toLp 2 (u (j + 1))‖ + |β j| * ‖WithLp.toLp 2 (v j)‖)
  /-- The inner product (`eq:local-alpha`). -/
  α_eq : ∀ j < k, α (j + 1) = v (j + 1) ⬝ᵥ w (j + 1) + eα (j + 1)
  /-- The inner product error. -/
  abs_eα_le : ∀ j < k,
    |eα (j + 1)| ≤ ε * ‖WithLp.toLp 2 (v (j + 1))‖ * ‖WithLp.toLp 2 (w (j + 1))‖
  /-- The second update (`eq:local-z`). -/
  z_eq : ∀ j < k, z (j + 1) = w (j + 1) - α (j + 1) • v (j + 1) + ez (j + 1)
  /-- The second update error. -/
  norm_ez_le : ∀ j < k, ‖WithLp.toLp 2 (ez (j + 1))‖ ≤
    ε * (‖WithLp.toLp 2 (w (j + 1))‖ + |α (j + 1)| * ‖WithLp.toLp 2 (v (j + 1))‖)
  /-- The normalisation (`eq:local-normalize`). -/
  smul_v_eq : ∀ j < k, β (j + 1) • v (j + 2) = z (j + 1) + δ (j + 1)
  /-- The normalisation error (`ass:normalization`). -/
  norm_δ_le : ∀ j < k, ‖WithLp.toLp 2 (δ (j + 1))‖ ≤ ε * ‖WithLp.toLp 2 (z (j + 1))‖
  /-- Nearly unit Lanczos vectors (`eq:local-unit`). -/
  abs_norm_v_sq_sub_one_le : ∀ j, 1 ≤ j → j ≤ k → |‖WithLp.toLp 2 (v j)‖ ^ 2 - 1| ≤ ε
  /-- The next vector is nearly unit when the last step is not terminal. -/
  abs_norm_v_succ_sq_sub_one_le : β k ≠ 0 → |‖WithLp.toLp 2 (v (k + 1))‖ ^ 2 - 1| ≤ ε
  /-- The coefficients $\beta_j$ are nonnegative. -/
  β_nonneg : ∀ j ≤ k, 0 ≤ β j
  /-- No breakdown before the last step. -/
  β_pos : ∀ j, 1 ≤ j → j < k → 0 < β j

namespace LanczosRun

variable {n k : ℕ}

/-- **A run with a larger accuracy parameter**: a run with parameter $\varepsilon$ is one with
any $\varepsilon' \ge \varepsilon$ such that $k\varepsilon' \le 1/100$; every field but the
parameter is unchanged. For callers whose $\varepsilon$ differs from the one a construction
produces (a coarser oracle contract, a uniform constant). No printed source. -/
noncomputable def ofLE (L : LanczosRun n k) {ε' : ℝ} (hε : L.ε ≤ ε')
    (h : (k : ℝ) * ε' ≤ 1 / 100) : LanczosRun n k :=
  { L with
    ε := ε'
    ε_nonneg := L.ε_nonneg.trans hε
    k_mul_ε_le := h
    norm_eu_le := fun j hj => (L.norm_eu_le j hj).trans <| mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hε (specNorm_nonneg _)) (norm_nonneg _)
    norm_ew_le := fun j hj => (L.norm_ew_le j hj).trans <|
      mul_le_mul_of_nonneg_right hε (by positivity)
    abs_eα_le := fun j hj => (L.abs_eα_le j hj).trans <| mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hε (norm_nonneg _)) (norm_nonneg _)
    norm_ez_le := fun j hj => (L.norm_ez_le j hj).trans <|
      mul_le_mul_of_nonneg_right hε (by positivity)
    norm_δ_le := fun j hj => (L.norm_δ_le j hj).trans <|
      mul_le_mul_of_nonneg_right hε (norm_nonneg _)
    abs_norm_v_sq_sub_one_le := fun j h1 h2 => (L.abs_norm_v_sq_sub_one_le j h1 h2).trans hε
    abs_norm_v_succ_sq_sub_one_le := fun hk => (L.abs_norm_v_succ_sq_sub_one_le hk).trans hε }

/-- The run `NLAlib.LanczosRun.ofLE` has parameter $\varepsilon'$. -/
@[simp] theorem ε_ofLE (L : LanczosRun n k) {ε' : ℝ} (hε : L.ε ≤ ε')
    (h : (k : ℝ) * ε' ≤ 1 / 100) : (L.ofLE hε h).ε = ε' := rfl

end LanczosRun

end NLAlib
