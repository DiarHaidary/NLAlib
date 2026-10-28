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
  ext i j
  simp only [Matrix.transpose_apply, tridiagonal, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [if_neg hij, if_neg (Ne.symm hij)]
    split_ifs <;> first | rfl | omega

/-- The computed tridiagonal matrix is tridiagonal. -/
theorem isTridiagonal_tridiagonal : IsTridiagonal L.tridiagonal := by
  intro i j hij
  simp only [tridiagonal, Matrix.of_apply]
  have hne : i ≠ j := fun h => by subst h; omega
  rw [if_neg hne]
  split_ifs <;> first | rfl | omega

/-- The product $\mathbf{V}_k\mathbf{T}_k$ entry by entry: column $j$ is
$\beta_j\mathbf{v}_j + \alpha_{j+1}\mathbf{v}_{j+1} + \beta_{j+1}\mathbf{v}_{j+2}$, the last
term only for $j + 1 < k$. -/
theorem basis_mul_tridiagonal_apply (i : Fin n) (j : Fin k) :
    (L.basis * L.tridiagonal) i j = L.β j * L.v j i + L.α ((j : ℕ) + 1) * L.v ((j : ℕ) + 1) i +
      if (j : ℕ) + 1 < k then L.β ((j : ℕ) + 1) * L.v ((j : ℕ) + 2) i else 0 := by
  obtain ⟨j, hj⟩ := j
  simp only [Matrix.mul_apply, basis, tridiagonal, Matrix.of_apply]
  have hterm : ∀ l : Fin k, L.v ((l : ℕ) + 1) i *
      (if l = ⟨j, hj⟩ then L.α ((l : ℕ) + 1) else if (l : ℕ) = j + 1 then L.β l
        else if j = (l : ℕ) + 1 then L.β j else 0) =
      (fun m : ℕ => (if m = j then L.α (j + 1) * L.v (j + 1) i else 0) +
        (if m = j + 1 then L.β (j + 1) * L.v (j + 2) i else 0) +
        (if m + 1 = j then L.β j * L.v j i else 0)) l := by
    intro l
    obtain ⟨l, hl⟩ := l
    simp only [Fin.mk.injEq]
    split_ifs <;> first | (exfalso; omega) | (subst_vars; ring)
  rw [Finset.sum_congr rfl fun l _ => hterm l, Fin.sum_univ_eq_sum_range
    (fun m : ℕ => (if m = j then L.α (j + 1) * L.v (j + 1) i else 0) +
      (if m = j + 1 then L.β (j + 1) * L.v (j + 2) i else 0) +
      (if m + 1 = j then L.β j * L.v j i else 0)) k]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range k) j,
    Finset.sum_ite_eq' (Finset.range k) (j + 1)]
  rw [if_pos (Finset.mem_range.2 hj)]
  have h3 : ∑ m ∈ Finset.range k, (if m + 1 = j then L.β j * L.v j i else 0) =
      L.β j * L.v j i := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [L.β_zero]
    · rw [Finset.sum_eq_single (j - 1)]
      · rw [if_pos (by omega)]
      · intro m _ hm
        rw [if_neg (by omega)]
      · intro hm
        exact absurd (Finset.mem_range.2 (by omega)) hm
  rw [h3]
  simp only [Finset.mem_range]
  ring

/-- **The perturbed Lanczos recurrence**: the computed basis satisfies
$$\mathbf{H}\mathbf{V}_k = \mathbf{V}_k\mathbf{T}_k
+ (\beta_k\mathbf{v}_{k+1})\mathbf{e}_{k-1}^{\mathsf{T}} + \mathbf{F}_k$$
($\mathbf{e}_{k-1}$ the last coordinate vector, indexed from $0$), an identity of the
definitions. No printed source; the maintainer's draft, `eq:governing`, writes it as
$\mathbf{V}_{k+1}\underline{\mathbf{T}}_k + \mathbf{F}_k$. -/
theorem H_mul_basis :
    L.H * L.basis = L.basis * L.tridiagonal +
      Matrix.vecMulVec (L.β k • L.v (k + 1)) (Pi.single L.lastIndex 1) + L.residual := by
  ext i j
  have hHV : (L.H * L.basis) i j = (L.H *ᵥ L.v ((j : ℕ) + 1)) i := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, basis, Matrix.of_apply]
  rw [Matrix.add_apply, Matrix.add_apply, hHV, L.basis_mul_tridiagonal_apply]
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, residual, Matrix.of_apply,
    recurrenceError, Pi.sub_apply]
  have hlast : j = L.lastIndex ↔ (j : ℕ) + 1 = k := by
    rw [Fin.ext_iff]
    simp only [lastIndex]
    have := L.k_pos
    omega
  by_cases hj : (j : ℕ) + 1 < k
  · rw [if_pos hj, Pi.single_eq_of_ne (fun h => by rw [hlast] at h; omega)]
    ring
  · have hj' : (j : ℕ) + 1 = k := by omega
    rw [if_neg hj, Pi.single_apply, if_pos (hlast.2 hj')]
    have hv : L.v ((j : ℕ) + 2) = L.v (k + 1) := congrArg L.v (by omega)
    have hβ : L.β ((j : ℕ) + 1) = L.β k := congrArg L.β hj'
    rw [hv, hβ]
    ring

/-- **The residual of the perturbed recurrence is small**:
$\|\mathbf{F}_k\|_{\mathsf{F}} \le 6k\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, proof of `cor:gram-commutator`, uses
$\|\mathbf{F}_k\| \le \sqrt{k}\max_j\|\mathbf{f}_j\|$ (its formalization: $700k^2$). -/
theorem frobNorm_residual_le :
    frobNorm L.residual ≤ 6 * k * Real.sqrt k * L.ε * specNorm L.H := by
  have hε0 := L.ε_nonneg
  have hH := specNorm_nonneg L.H
  have hcol : ∀ j : Fin k, ‖WithLp.toLp 2 (L.residual.col j)‖ ≤ 6 * k * L.ε * specNorm L.H := by
    intro j
    have hjk : ((j : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast j.2
    refine (L.norm_recurrenceError_le j.2).trans ?_
    gcongr
  have hsq : frobNorm L.residual ^ 2 ≤ (6 * k * Real.sqrt k * L.ε * specNorm L.H) ^ 2 := by
    rw [frobNorm_sq_eq_sum_col]
    calc ∑ j, ‖WithLp.toLp 2 (L.residual.col j)‖ ^ 2
        ≤ ∑ _j : Fin k, (6 * k * L.ε * specNorm L.H) ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hcol j) 2
      _ = (6 * k * Real.sqrt k * L.ε * specNorm L.H) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hs : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt (Nat.cast_nonneg k)
          calc (k : ℝ) * (6 * k * L.ε * specNorm L.H) ^ 2
              = Real.sqrt (k : ℝ) ^ 2 * (6 * k * L.ε * specNorm L.H) ^ 2 := by rw [hs]
            _ = _ := by ring
  exact (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).1 hsq

/-- **The residual of the perturbed recurrence is small** in the spectral norm:
$\|\mathbf{F}_k\|_2 \le 6k\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, proof of `cor:gram-commutator`. -/
theorem specNorm_residual_le :
    specNorm L.residual ≤ 6 * k * Real.sqrt k * L.ε * specNorm L.H :=
  (specNorm_le_frobNorm _).trans L.frobNorm_residual_le

/-- The last computed vector, scaled: $\|\beta_k\mathbf{v}_{k+1}\| \le
\sqrt{1 + \varepsilon}\,\beta_k$ ($\mathbf{v}_{k+1}$ is nearly unit when $\beta_k \neq 0$). -/
theorem norm_β_smul_v_le : ‖WithLp.toLp 2 (L.β k • L.v (k + 1))‖ ≤ Real.sqrt (1 + L.ε) * L.β k := by
  have hβ := L.β_nonneg k le_rfl
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ, mul_comm]
  rcases hβ.eq_or_lt with h | h
  · rw [← h, mul_zero, mul_zero]
  · gcongr
    apply Real.le_sqrt_of_sq_le
    have := (abs_le.mp (L.abs_norm_v_succ_sq_sub_one_le h.ne')).2
    linarith

/-- **The Ritz residual identity**: for an eigenpair $\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$
of the computed tridiagonal matrix, the Ritz vector $\mathbf{x} = \mathbf{V}_k\mathbf{y}$
satisfies
$$(\mathbf{H} - \theta\mathbf{I})\mathbf{x} = y_{k-1}\,(\beta_k\mathbf{v}_{k+1})
+ \mathbf{F}_k\mathbf{y}$$
($y_{k-1}$ the last entry, indexed from $0$). No printed source; the maintainer's draft,
`eq:ritz-residual-identity`. -/
theorem H_mulVec_basis_mulVec_sub_smul {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) :
    L.H *ᵥ (L.basis *ᵥ y) - θ • (L.basis *ᵥ y) =
      y L.lastIndex • (L.β k • L.v (k + 1)) + L.residual *ᵥ y := by
  have h := congrArg (fun M => M *ᵥ y) L.H_mul_basis
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul,
    Matrix.vecMulVec_mulVec, single_one_dotProduct, op_smul_eq_smul] at h
  rw [h]
  abel

/-- **The Ritz residual bound for finite-precision Lanczos**: for a unit eigenpair
$\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$, $\|\mathbf{y}\| = 1$, of the computed tridiagonal
matrix, the Ritz vector $\mathbf{x} = \mathbf{V}_k\mathbf{y}$ satisfies
$$\|\mathbf{H}\mathbf{x} - \theta\mathbf{x}\|
\le \sqrt{1 + \varepsilon}\,\beta_k\lvert y_{k-1}\rvert
+ 6k\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2 \,.$$
No printed source; the maintainer's draft, `eq:ritz-residual-bound`, with
$\|\mathbf{F}_k\|$ for the last term and both sides divided by $\|\mathbf{x}\|$.
Result: lanczos-ritz-residual -/
theorem norm_H_mulVec_basis_mulVec_sub_smul_le {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    ‖WithLp.toLp 2 (L.H *ᵥ (L.basis *ᵥ y) - θ • (L.basis *ᵥ y))‖ ≤
      Real.sqrt (1 + L.ε) * L.β k * |y L.lastIndex| +
        6 * k * Real.sqrt k * L.ε * specNorm L.H := by
  rw [L.H_mulVec_basis_mulVec_sub_smul hy, WithLp.toLp_add]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, mul_comm]
    gcongr
    exact L.norm_β_smul_v_le
  · refine (norm_toLp_mulVec_le _ _).trans ?_
    rw [hy1, mul_one]
    exact L.specNorm_residual_le

end LanczosRun

end NLAlib
