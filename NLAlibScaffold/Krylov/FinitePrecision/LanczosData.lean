/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Hessenberg
public import NLAlib.Matrix.Norms.Compare

/-!
# Perturbed symmetric three-term recurrences

`NLAlib.LanczosData n k` is the data of $k$ steps of a symmetric three-term recurrence: a real
symmetric $\mathbf{H}$, vectors $\mathbf{v}_0 = \mathbf{0}, \mathbf{v}_1, \dots,
\mathbf{v}_{k+1}$ and coefficients $\alpha_j$, $\beta_j$ with $\beta_0 = 0$, and no relation
between them. Every such datum satisfies the perturbed recurrence
$\mathbf{H}\mathbf{V}_k = \mathbf{V}_k\mathbf{T}_k
+ \beta_k\mathbf{v}_{k+1}\mathbf{e}_{k-1}^{\mathsf{T}} + \mathbf{F}_k$ with its residual
$\mathbf{F}_k$ by definition, and the Gram matrix of its vectors satisfies Paige's commutator
identity. The finite-precision analysis applies these identities
twice: to a computed run (`NLAlib.LanczosRun.toLanczosData`) and to its normalised vectors.

Indices from $0$: column $j$ of the basis is $\mathbf{v}_{j+1}$, step $j$ reads $\mathbf{v}_{j+1}$.
No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `eq:governing`, `lem:gram-commutator`.

## Main definitions

* `NLAlib.LanczosData`, `NLAlib.LanczosData.basis`, `NLAlib.LanczosData.basisSucc`,
  `NLAlib.LanczosData.tridiagonal`, `NLAlib.LanczosData.tridiagonalSucc`,
  `NLAlib.LanczosData.residual`, `NLAlib.LanczosData.gramCommutator`.

## Main results

* `NLAlib.LanczosData.H_mul_basis`, `NLAlib.LanczosData.H_mul_basis_eq_basisSucc_mul`: the
  perturbed recurrence.
* `NLAlib.LanczosData.gramCommutator_sub_transpose`,
  `NLAlib.LanczosData.specNorm_gramCommutator_le`: the Gram commutator.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-- **The strict upper part of an upper triangular matrix is controlled by its skew part**:
for $\mathbf{M}$ upper triangular, the Frobenius norm of $\mathbf{M}$ minus its diagonal is at most
$\|\mathbf{M} - \mathbf{M}^{\mathsf{T}}\|_{\mathsf{F}}$ (its entries above the diagonal are
those of $\mathbf{M} - \mathbf{M}^{\mathsf{T}}$). -/
theorem _root_.Matrix.IsUpperTriangular.frobNorm_sub_diagonal_le {ι : Type*} [Fintype ι]
    [LinearOrder ι] {M : Matrix ι ι ℝ} (hM : M.IsUpperTriangular) :
    frobNorm (M - Matrix.diagonal fun i => M i i) ≤ frobNorm (M - Mᵀ) := by
  have hsq : frobNorm (M - Matrix.diagonal fun i => M i i) ^ 2 ≤ frobNorm (M - Mᵀ) ^ 2 := by
    rw [frobNorm_sq_eq_sum_sq, frobNorm_sq_eq_sum_sq]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    simp only [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_neg h.ne, hM h]
    · simp
    · rw [if_neg h.ne', hM h]
      nlinarith [sq_nonneg (M j i)]
  exact (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1 hsq

/-- A square matrix with entries bounded by $c$ has Frobenius norm at most $\lvert n\rvert c$. -/
theorem frobNorm_le_card_mul_of_forall_abs_le {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i j, |M i j| ≤ c) : frobNorm M ≤ Fintype.card ι * c := by
  have hsq : frobNorm M ^ 2 ≤ (Fintype.card ι * c) ^ 2 := by
    rw [frobNorm_sq_eq_sum_sq]
    calc ∑ i, ∑ j, M i j ^ 2 ≤ ∑ _i : ι, ∑ _j : ι, c ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
      _ = (Fintype.card ι * c) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  exact (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).1 hsq

/-- The data of $k$ steps of a **symmetric three-term recurrence**: a real symmetric matrix,
vectors $\mathbf{v}_j$ with $\mathbf{v}_0 = \mathbf{0}$ and coefficients $\alpha_j$, $\beta_j$
with $\beta_0 = 0$, $k \ge 1$. No relation between vectors and coefficients is assumed; the
residual of the recurrence (`NLAlib.LanczosData.recurrenceError`) measures it. -/
structure LanczosData (n k : ℕ) where
  /-- The matrix. -/
  H : Matrix (Fin n) (Fin n) ℝ
  /-- The vectors. -/
  v : ℕ → Fin n → ℝ
  /-- The diagonal coefficients. -/
  α : ℕ → ℝ
  /-- The off-diagonal coefficients. -/
  β : ℕ → ℝ
  /-- The matrix is symmetric. -/
  transpose_H : Hᵀ = H
  /-- At least one step. -/
  k_pos : 0 < k
  /-- $\mathbf{v}_0 = \mathbf{0}$. -/
  v_zero : v 0 = 0
  /-- $\beta_0 = 0$. -/
  β_zero : β 0 = 0

namespace LanczosData

variable {n k : ℕ} (D : LanczosData n k)

/-- The **residual of the three-term recurrence** at step $j$ (0-based):
$\mathbf{f}_j = \mathbf{H}\mathbf{v}_{j+1} - \beta_j\mathbf{v}_j - \alpha_{j+1}\mathbf{v}_{j+1}
- \beta_{j+1}\mathbf{v}_{j+2}$, the paper's $\mathbf{f}_{j+1}$. At a terminal last step
$\beta_k = 0$ and $\mathbf{v}_{k+1}$ does not enter. -/
noncomputable def recurrenceError (j : ℕ) : Fin n → ℝ :=
  D.H *ᵥ D.v (j + 1) - D.β j • D.v j - D.α (j + 1) • D.v (j + 1) - D.β (j + 1) • D.v (j + 2)

/-- The **inner product of consecutive Lanczos vectors** at step $j$ (0-based):
$\mathbf{v}_{j+1}^{\mathsf{T}}(\beta_{j+1}\mathbf{v}_{j+2})$, the paper's $p_{j+1}$. -/
noncomputable def adjacentInner (j : ℕ) : ℝ :=
  D.v (j + 1) ⬝ᵥ (D.β (j + 1) • D.v (j + 2))

/-- The **computed Lanczos basis** $\mathbf{V}_k$: column $j$ is $\mathbf{v}_{j+1}$. -/
def basis : Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun i j => D.v ((j : ℕ) + 1) i

/-- The **computed tridiagonal matrix** $\mathbf{T}_k$, indexed from $0$:
$\alpha_{i+1}$ at $(i, i)$, and $\beta_i$ at $(i, i - 1)$ and $(i - 1, i)$. -/
def tridiagonal : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if i = j then D.α ((i : ℕ) + 1)
    else if (i : ℕ) = j + 1 then D.β i
    else if (j : ℕ) = i + 1 then D.β j
    else 0

/-- The **residual matrix** $\mathbf{F}_k$ of the recurrence: column $j$ is
`NLAlib.LanczosData.recurrenceError D j`. -/
noncomputable def residual : Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun i j => D.recurrenceError j i

/-- The index $k - 1$ of the last column, as an element of `Fin k` (a run has $k \ge 1$). -/
def lastIndex : Fin k :=
  ⟨k - 1, Nat.sub_one_lt_of_lt D.k_pos⟩

/-- The computed tridiagonal matrix is symmetric. -/
theorem transpose_tridiagonal : D.tridiagonalᵀ = D.tridiagonal := by
  ext i j
  simp only [Matrix.transpose_apply, tridiagonal, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [if_neg hij, if_neg (Ne.symm hij)]
    split_ifs <;> first | rfl | omega

/-- The computed tridiagonal matrix is tridiagonal. -/
theorem isTridiagonal_tridiagonal : IsTridiagonal D.tridiagonal := by
  intro i j hij
  simp only [tridiagonal, Matrix.of_apply]
  have hne : i ≠ j := fun h => by subst h; omega
  rw [if_neg hne]
  split_ifs <;> first | rfl | omega

/-- The product $\mathbf{V}_k\mathbf{T}_k$ entry by entry: column $j$ is
$\beta_j\mathbf{v}_j + \alpha_{j+1}\mathbf{v}_{j+1} + \beta_{j+1}\mathbf{v}_{j+2}$, the last
term only for $j + 1 < k$. -/
theorem basis_mul_tridiagonal_apply (i : Fin n) (j : Fin k) :
    (D.basis * D.tridiagonal) i j = D.β j * D.v j i + D.α ((j : ℕ) + 1) * D.v ((j : ℕ) + 1) i +
      if (j : ℕ) + 1 < k then D.β ((j : ℕ) + 1) * D.v ((j : ℕ) + 2) i else 0 := by
  obtain ⟨j, hj⟩ := j
  simp only [Matrix.mul_apply, basis, tridiagonal, Matrix.of_apply]
  have hterm : ∀ l : Fin k, D.v ((l : ℕ) + 1) i *
      (if l = ⟨j, hj⟩ then D.α ((l : ℕ) + 1) else if (l : ℕ) = j + 1 then D.β l
        else if j = (l : ℕ) + 1 then D.β j else 0) =
      (fun m : ℕ => (if m = j then D.α (j + 1) * D.v (j + 1) i else 0) +
        (if m = j + 1 then D.β (j + 1) * D.v (j + 2) i else 0) +
        (if m + 1 = j then D.β j * D.v j i else 0)) l := by
    intro l
    obtain ⟨l, hl⟩ := l
    simp only [Fin.mk.injEq]
    split_ifs <;> first | (exfalso; omega) | (subst_vars; ring)
  rw [Finset.sum_congr rfl fun l _ => hterm l, Fin.sum_univ_eq_sum_range
    (fun m : ℕ => (if m = j then D.α (j + 1) * D.v (j + 1) i else 0) +
      (if m = j + 1 then D.β (j + 1) * D.v (j + 2) i else 0) +
      (if m + 1 = j then D.β j * D.v j i else 0)) k]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range k) j,
    Finset.sum_ite_eq' (Finset.range k) (j + 1)]
  rw [if_pos (Finset.mem_range.2 hj)]
  have h3 : ∑ m ∈ Finset.range k, (if m + 1 = j then D.β j * D.v j i else 0) =
      D.β j * D.v j i := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [D.β_zero]
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
    D.H * D.basis = D.basis * D.tridiagonal +
      Matrix.vecMulVec (D.β k • D.v (k + 1)) (Pi.single D.lastIndex 1) + D.residual := by
  ext i j
  have hHV : (D.H * D.basis) i j = (D.H *ᵥ D.v ((j : ℕ) + 1)) i := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, basis, Matrix.of_apply]
  rw [Matrix.add_apply, Matrix.add_apply, hHV, D.basis_mul_tridiagonal_apply]
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, residual, Matrix.of_apply,
    recurrenceError, Pi.sub_apply]
  have hlast : j = D.lastIndex ↔ (j : ℕ) + 1 = k := by
    rw [Fin.ext_iff]
    simp only [lastIndex]
    have := D.k_pos
    omega
  by_cases hj : (j : ℕ) + 1 < k
  · rw [if_pos hj, Pi.single_eq_of_ne (fun h => by rw [hlast] at h; omega)]
    ring
  · have hj' : (j : ℕ) + 1 = k := by omega
    rw [if_neg hj, Pi.single_apply, if_pos (hlast.2 hj')]
    have hv : D.v ((j : ℕ) + 2) = D.v (k + 1) := congrArg D.v (by omega)
    have hβ : D.β ((j : ℕ) + 1) = D.β k := congrArg D.β hj'
    rw [hv, hβ]
    ring

/-- The basis with the next vector, $\mathbf{V}_{k+1} = [\mathbf{v}_1, \dots, \mathbf{v}_{k+1}]$:
column $j \le k$ is $\mathbf{v}_{j+1}$. -/
def basisSucc : Matrix (Fin n) (Fin (k + 1)) ℝ :=
  Matrix.of fun i j => D.v ((j : ℕ) + 1) i

/-- The tridiagonal matrix with the extra row $\beta_k\mathbf{e}_{k-1}^{\mathsf{T}}$,
$\underline{\mathbf{T}}_k \in \mathbb{R}^{(k+1) \times k}$, indexed from $0$. -/
def tridiagonalSucc : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) = j then D.α ((i : ℕ) + 1)
    else if (i : ℕ) = j + 1 then D.β i
    else if (j : ℕ) = i + 1 then D.β j
    else 0

/-- The first $k$ rows of $\underline{\mathbf{T}}_k$ are $\mathbf{T}_k$. -/
theorem tridiagonalSucc_castSucc (i j : Fin k) :
    D.tridiagonalSucc (Fin.castSucc i) j = D.tridiagonal i j := by
  simp only [tridiagonalSucc, tridiagonal, Matrix.of_apply, Fin.val_castSucc, Fin.ext_iff]

/-- The last row of $\underline{\mathbf{T}}_k$ is $\beta_k\mathbf{e}_{k-1}^{\mathsf{T}}$. -/
theorem tridiagonalSucc_last (j : Fin k) :
    D.tridiagonalSucc (Fin.last k) j = if k = (j : ℕ) + 1 then D.β k else 0 := by
  obtain ⟨j, hj⟩ := j
  simp only [tridiagonalSucc, Matrix.of_apply, Fin.val_last]
  rw [if_neg (by omega)]
  by_cases h : k = j + 1
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg (by omega)]

/-- Columns of $\mathbf{Q}\underline{\mathbf{T}}_k$ for any $\mathbf{Q}$ with $k + 1$ columns
$\mathbf{u}_1, \dots, \mathbf{u}_{k+1}$: column $j$ is
$\beta_j\mathbf{u}_j + \alpha_{j+1}\mathbf{u}_{j+1} + \beta_{j+1}\mathbf{u}_{j+2}$. -/
theorem mul_tridiagonalSucc_apply {ι : Type*} (Q : Matrix ι (Fin (k + 1)) ℝ) (u : ℕ → ι → ℝ)
    (hu : ∀ (m : ℕ) (hm : m < k + 1) (p : ι), Q p ⟨m, hm⟩ = u (m + 1) p) (p : ι) (j : Fin k) :
    (Q * D.tridiagonalSucc) p j =
      D.β j * u j p + D.α ((j : ℕ) + 1) * u ((j : ℕ) + 1) p +
        D.β ((j : ℕ) + 1) * u ((j : ℕ) + 2) p := by
  obtain ⟨j, hj⟩ := j
  simp only [Matrix.mul_apply, tridiagonalSucc, Matrix.of_apply]
  have hterm : ∀ l : Fin (k + 1), Q p l *
      (if (l : ℕ) = j then D.α ((l : ℕ) + 1) else if (l : ℕ) = j + 1 then D.β l
        else if j = (l : ℕ) + 1 then D.β j else 0) =
      (fun m : ℕ => (if m = j then D.α (j + 1) * u (j + 1) p else 0) +
        (if m = j + 1 then D.β (j + 1) * u (j + 2) p else 0) +
        (if m + 1 = j then D.β j * u j p else 0)) l := by
    intro l
    obtain ⟨l, hl⟩ := l
    rw [hu l hl p]
    simp only
    split_ifs <;> first | (exfalso; omega) | (subst_vars; ring)
  rw [Finset.sum_congr rfl fun l _ => hterm l, Fin.sum_univ_eq_sum_range
    (fun m : ℕ => (if m = j then D.α (j + 1) * u (j + 1) p else 0) +
      (if m = j + 1 then D.β (j + 1) * u (j + 2) p else 0) +
      (if m + 1 = j then D.β j * u j p else 0)) (k + 1)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (k + 1)) j,
    Finset.sum_ite_eq' (Finset.range (k + 1)) (j + 1), if_pos (Finset.mem_range.2 (by omega)),
    if_pos (Finset.mem_range.2 (by omega))]
  have h3 : ∑ m ∈ Finset.range (k + 1), (if m + 1 = j then D.β j * u j p else 0) =
      D.β j * u j p := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [D.β_zero]
    · rw [Finset.sum_eq_single (j - 1)]
      · rw [if_pos (by omega)]
      · intro m _ hm
        rw [if_neg (by omega)]
      · intro hm
        exact absurd (Finset.mem_range.2 (by omega)) hm
  rw [h3]
  ring

/-- $\mathbf{V}_{k+1}\underline{\mathbf{T}}_k = \mathbf{V}_k\mathbf{T}_k
+ (\beta_k\mathbf{v}_{k+1})\mathbf{e}_{k-1}^{\mathsf{T}}$. -/
theorem basisSucc_mul_tridiagonalSucc :
    D.basisSucc * D.tridiagonalSucc = D.basis * D.tridiagonal +
      Matrix.vecMulVec (D.β k • D.v (k + 1)) (Pi.single D.lastIndex 1) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp only [basisSucc, basis, tridiagonalSucc, tridiagonal, Matrix.of_apply,
      Fin.val_castSucc, Fin.ext_iff]
  · obtain ⟨j, hj⟩ := j
    simp only [basisSucc, tridiagonalSucc, Matrix.of_apply, Fin.val_last,
      Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, lastIndex,
      Fin.mk.injEq]
    by_cases h : k = j + 1
    · rw [if_neg (by omega), if_pos h, if_pos (by omega)]
      ring
    · rw [if_neg (by omega), if_neg h, if_neg (by omega), if_neg (by omega)]
      ring

/-- **The perturbed recurrence with the extended tridiagonal matrix**:
$\mathbf{H}\mathbf{V}_k = \mathbf{V}_{k+1}\underline{\mathbf{T}}_k + \mathbf{F}_k$.
No printed source; the maintainer's draft, `eq:governing`. -/
theorem H_mul_basis_eq_basisSucc_mul :
    D.H * D.basis = D.basisSucc * D.tridiagonalSucc + D.residual := by
  rw [D.basisSucc_mul_tridiagonalSucc, D.H_mul_basis]

/-- **The Ritz residual identity**: for an eigenpair $\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$
of the computed tridiagonal matrix, the Ritz vector $\mathbf{x} = \mathbf{V}_k\mathbf{y}$
satisfies
$$(\mathbf{H} - \theta\mathbf{I})\mathbf{x} = y_{k-1}\,(\beta_k\mathbf{v}_{k+1})
+ \mathbf{F}_k\mathbf{y}$$
($y_{k-1}$ the last entry, indexed from $0$). No printed source; the maintainer's draft,
`eq:ritz-residual-identity`. -/
theorem H_mulVec_basis_mulVec_sub_smul {y : Fin k → ℝ} {θ : ℝ}
    (hy : D.tridiagonal *ᵥ y = θ • y) :
    D.H *ᵥ (D.basis *ᵥ y) - θ • (D.basis *ᵥ y) =
      y D.lastIndex • (D.β k • D.v (k + 1)) + D.residual *ᵥ y := by
  have h := congrArg (fun M => M *ᵥ y) D.H_mul_basis
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul,
    Matrix.vecMulVec_mulVec, single_one_dotProduct, op_smul_eq_smul] at h
  rw [h]
  abel

/-- The **strict upper triangle of the Gram matrix** of the computed basis:
$(\mathbf{R}_k)_{i,j} = \mathbf{v}_{i+1}^{\mathsf{T}}\mathbf{v}_{j+1}$ for $i < j$, and $0$
otherwise. -/
def gramStrictUpper : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => if i < j then D.v ((i : ℕ) + 1) ⬝ᵥ D.v ((j : ℕ) + 1) else 0

/-- The **diagonal defects** of the Gram matrix of the computed basis:
$\gamma_i = \|\mathbf{v}_{i+1}\|^2 - 1$ (the paper's $g_{i+1}$). -/
noncomputable def normSqDefect (i : Fin k) : ℝ :=
  ‖WithLp.toLp 2 (D.v ((i : ℕ) + 1))‖ ^ 2 - 1

/-- The **Gram commutator**
$\mathbf{M}_k = \mathbf{T}_k\mathbf{R}_k - \mathbf{R}_k\mathbf{T}_k
- (\mathbf{V}_k^{\mathsf{T}}\beta_k\mathbf{v}_{k+1})\mathbf{e}_{k-1}^{\mathsf{T}}$
(`eq:M-def` of the maintainer's draft; $\mathbf{e}_{k-1}$ the last coordinate vector, indexed
from $0$). -/
noncomputable def gramCommutator : Matrix (Fin k) (Fin k) ℝ :=
  D.tridiagonal * D.gramStrictUpper - D.gramStrictUpper * D.tridiagonal -
    Matrix.vecMulVec (D.basisᵀ *ᵥ (D.β k • D.v (k + 1))) (Pi.single D.lastIndex 1)

/-- The Gram commutator is upper triangular. No printed source; the maintainer's draft,
`lem:gram-commutator`. -/
theorem isUpperTriangular_gramCommutator : D.gramCommutator.IsUpperTriangular := by
  intro i j hji
  simp only [id] at hji
  have hT := D.isTridiagonal_tridiagonal
  have hji' : (j : ℕ) < i := hji
  simp only [gramCommutator, Matrix.sub_apply, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have h1 : ∑ l, D.tridiagonal i l * D.gramStrictUpper l j = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hlj : l < j
    · have hl : (l : ℕ) < j := hlj
      rw [hT i l (Or.inr (by omega)), zero_mul]
    · simp only [gramStrictUpper, Matrix.of_apply, if_neg hlj, mul_zero]
  have h2 : ∑ l, D.gramStrictUpper i l * D.tridiagonal l j = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hil : i < l
    · have hl : (i : ℕ) < l := hil
      rw [hT l j (Or.inr (by omega)), mul_zero]
    · simp only [gramStrictUpper, Matrix.of_apply, if_neg hil, zero_mul]
  have h3 : (Pi.single D.lastIndex (1 : ℝ) : Fin k → ℝ) j = 0 := by
    refine Pi.single_eq_of_ne (fun h => ?_) _
    have : (j : ℕ) = k - 1 := by rw [h]; rfl
    omega
  rw [h1, h2, h3]
  ring

/-- The diagonal entries of the Gram commutator are differences of inner products of consecutive
vectors: $(\mathbf{M}_k)_{i,i} = \beta_i\mathbf{v}_i^{\mathsf{T}}\mathbf{v}_{i+1}
- \mathbf{v}_{i+1}^{\mathsf{T}}(\beta_{i+1}\mathbf{v}_{i+2})$. -/
theorem gramCommutator_apply_self (i : Fin k) :
    D.gramCommutator i i =
      D.β i * (D.v i ⬝ᵥ D.v ((i : ℕ) + 1)) - D.adjacentInner i := by
  obtain ⟨i, hi⟩ := i
  simp only [gramCommutator, Matrix.sub_apply, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have hTR : ∑ l : Fin k, D.tridiagonal ⟨i, hi⟩ l * D.gramStrictUpper l ⟨i, hi⟩ =
      D.β i * (D.v i ⬝ᵥ D.v (i + 1)) := by
    have hterm : ∀ l : Fin k, D.tridiagonal ⟨i, hi⟩ l * D.gramStrictUpper l ⟨i, hi⟩ =
        (fun m : ℕ => if m + 1 = i then D.β i * (D.v i ⬝ᵥ D.v (i + 1)) else 0) l := by
      intro l
      obtain ⟨l, hl⟩ := l
      simp only [tridiagonal, gramStrictUpper, Matrix.of_apply, Fin.mk.injEq, Fin.mk_lt_mk]
      split_ifs <;> first | (exfalso; omega) | (subst_vars; ring)
    rw [Finset.sum_congr rfl fun l _ => hterm l, Fin.sum_univ_eq_sum_range
      (fun m : ℕ => if m + 1 = i then D.β i * (D.v i ⬝ᵥ D.v (i + 1)) else 0) k]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [D.β_zero]
    · rw [Finset.sum_eq_single (i - 1)]
      · rw [if_pos (by omega)]
      · intro m _ hm
        rw [if_neg (by omega)]
      · intro hm
        exact absurd (Finset.mem_range.2 (by omega)) hm
  have hRT : ∑ l : Fin k, D.gramStrictUpper ⟨i, hi⟩ l * D.tridiagonal l ⟨i, hi⟩ =
      if i + 1 < k then D.β (i + 1) * (D.v (i + 1) ⬝ᵥ D.v (i + 2)) else 0 := by
    have hterm : ∀ l : Fin k, D.gramStrictUpper ⟨i, hi⟩ l * D.tridiagonal l ⟨i, hi⟩ =
        (fun m : ℕ => if m = i + 1 then D.β (i + 1) * (D.v (i + 1) ⬝ᵥ D.v (i + 2)) else 0) l := by
      intro l
      obtain ⟨l, hl⟩ := l
      simp only [tridiagonal, gramStrictUpper, Matrix.of_apply, Fin.mk.injEq, Fin.mk_lt_mk]
      split_ifs <;> first | (exfalso; omega) | (subst_vars; ring)
    rw [Finset.sum_congr rfl fun l _ => hterm l, Fin.sum_univ_eq_sum_range
      (fun m : ℕ => if m = i + 1 then D.β (i + 1) * (D.v (i + 1) ⬝ᵥ D.v (i + 2)) else 0) k,
      Finset.sum_ite_eq' (Finset.range k) (i + 1)]
    simp only [Finset.mem_range]
  have hP : (D.basisᵀ *ᵥ (D.β k • D.v (k + 1))) ⟨i, hi⟩ = D.v (i + 1) ⬝ᵥ (D.β k • D.v (k + 1)) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, basis, Matrix.of_apply]
  rw [hTR, hRT, hP, adjacentInner]
  by_cases h : i + 1 < k
  · rw [if_pos h, Pi.single_eq_of_ne (fun h' => by
      have : i = k - 1 := congrArg Fin.val h'
      omega)]
    simp only [dotProduct_smul, smul_eq_mul, mul_zero, sub_zero]
  · have hk : i + 1 = k := by omega
    have hlast : (⟨i, hi⟩ : Fin k) = D.lastIndex := Fin.ext (by simp only [lastIndex]; omega)
    rw [if_neg h, hlast, Pi.single_eq_same]
    have hv : D.v (i + 2) = D.v (k + 1) := congrArg D.v (by omega)
    have hβ : D.β (i + 1) = D.β k := congrArg D.β hk
    rw [hv, hβ]
    ring

/-- **The skew part of the Gram commutator** is given by the residual and the diagonal defects:
$$\mathbf{M}_k - \mathbf{M}_k^{\mathsf{T}} = \mathbf{V}_k^{\mathsf{T}}\mathbf{F}_k
- \mathbf{F}_k^{\mathsf{T}}\mathbf{V}_k
- (\mathbf{T}_k\mathbf{\Gamma} - \mathbf{\Gamma}\mathbf{T}_k),
\qquad \mathbf{\Gamma} = \operatorname{diag}(\|\mathbf{v}_{i+1}\|^2 - 1)_i \,.$$
No printed source; the maintainer's draft, `eq:generic-commutator`. -/
theorem gramCommutator_sub_transpose :
    D.gramCommutator - D.gramCommutatorᵀ =
      D.basisᵀ * D.residual - D.residualᵀ * D.basis -
        (D.tridiagonal * Matrix.diagonal D.normSqDefect -
          Matrix.diagonal D.normSqDefect * D.tridiagonal) := by
  set V := D.basis
  set T := D.tridiagonal
  set R := D.gramStrictUpper
  set P := Matrix.vecMulVec (D.basisᵀ *ᵥ (D.β k • D.v (k + 1))) (Pi.single D.lastIndex (1 : ℝ))
  set Γ := Matrix.diagonal D.normSqDefect
  have hP : Vᵀ * Matrix.vecMulVec (D.β k • D.v (k + 1)) (Pi.single D.lastIndex 1) = P :=
    Matrix.mul_vecMulVec _ _ _
  have hG : Vᵀ * V = 1 + Γ + R + Rᵀ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply, V, R, Γ, basis,
      gramStrictUpper, Matrix.of_apply, Matrix.one_apply, Matrix.diagonal_apply, normSqDefect,
      EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_neg h.ne, if_neg h.ne, if_pos h, if_neg (lt_asymm h)]
      simp only [dotProduct]
      ring
    · simp only [lt_irrefl, ↓reduceIte, dotProduct]
      ring
    · rw [if_neg h.ne', if_neg h.ne', if_neg (lt_asymm h), if_pos h]
      simp only [dotProduct]
      ring_nf
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hT : Tᵀ = T := D.transpose_tridiagonal
  have hX : Vᵀ * (D.H * V) = (1 + Γ + R + Rᵀ) * T + P + Vᵀ * D.residual := by
    rw [D.H_mul_basis, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, hG, hP]
  have hXt : (Vᵀ * (D.H * V))ᵀ = Vᵀ * (D.H * V) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, D.transpose_H,
      Matrix.mul_assoc]
  have hΓ : Γᵀ = Γ := Matrix.diagonal_transpose _
  rw [hX] at hXt
  simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, hT, hΓ,
    Matrix.add_mul, Matrix.one_mul] at hXt
  have hM : D.gramCommutator = T * R - R * T - P := rfl
  rw [hM, Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    hT]
  calc T * R - R * T - P - (Rᵀ * T - T * Rᵀ - Pᵀ)
      = Vᵀ * D.residual - D.residualᵀ * V - (T * Γ - Γ * T) +
          ((T + T * Γ + T * Rᵀ + T * R + Pᵀ + D.residualᵀ * V) -
            (T + Γ * T + R * T + Rᵀ * T + P + Vᵀ * D.residual)) := by abel
    _ = Vᵀ * D.residual - D.residualᵀ * V - (T * Γ - Γ * T) := by
        rw [hXt, sub_self, add_zero]


/-! ### Bounds on the Gram commutator -/

/-- The diagonal entries of the Gram commutator are at most twice a bound on the inner products
of consecutive vectors: if $\lvert p_j\rvert \le a$ for $j < k$, then
$\lvert(\mathbf{M}_k)_{i,i}\rvert \le 2a$. -/
theorem abs_gramCommutator_apply_self_le {a : ℝ} (ha : ∀ j < k, |D.adjacentInner j| ≤ a)
    (i : Fin k) : |D.gramCommutator i i| ≤ 2 * a := by
  rw [D.gramCommutator_apply_self]
  have h2 := ha i i.2
  have h1 : |D.β i * (D.v i ⬝ᵥ D.v ((i : ℕ) + 1))| ≤ a := by
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [h0, D.β_zero, zero_mul, abs_zero]
      exact (abs_nonneg _).trans (ha 0 D.k_pos)
    · have h := ha ((i : ℕ) - 1) (by omega)
      simp only [adjacentInner, show (i : ℕ) - 1 + 1 = i by omega,
        show (i : ℕ) - 1 + 2 = i + 1 by omega, dotProduct_smul, smul_eq_mul] at h
      exact h
  calc |D.β i * (D.v i ⬝ᵥ D.v ((i : ℕ) + 1)) - D.adjacentInner i|
      ≤ |D.β i * (D.v i ⬝ᵥ D.v ((i : ℕ) + 1))| + |D.adjacentInner i| := abs_sub _ _
    _ ≤ 2 * a := by linarith

/-- The commutator of the tridiagonal matrix with the diagonal defects: if $\lvert\beta_j\rvert
\le b$ for $j < k$ and $\lvert\gamma_i\rvert \le g$, then
$\|\mathbf{T}_k\mathbf{\Gamma} - \mathbf{\Gamma}\mathbf{T}_k\|_{\mathsf{F}} \le 2kbg$. -/
theorem frobNorm_tridiagonal_mul_diagonal_sub_diagonal_mul_tridiagonal_le {b g : ℝ}
    (hb : ∀ j < k, |D.β j| ≤ b) (hg : ∀ i, |D.normSqDefect i| ≤ g) :
    frobNorm (D.tridiagonal * Matrix.diagonal D.normSqDefect -
      Matrix.diagonal D.normSqDefect * D.tridiagonal) ≤ k * (b * (2 * g)) := by
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0 D.k_pos)
  have hg0 : 0 ≤ g := (abs_nonneg _).trans (hg ⟨0, D.k_pos⟩)
  have := frobNorm_le_card_mul_of_forall_abs_le (M := D.tridiagonal *
    Matrix.diagonal D.normSqDefect - Matrix.diagonal D.normSqDefect * D.tridiagonal)
    (c := b * (2 * g)) (by positivity) (fun i j => ?_)
  · simpa only [Fintype.card_fin] using this
  rw [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    show D.tridiagonal i j * D.normSqDefect j - D.normSqDefect i * D.tridiagonal i j =
      D.tridiagonal i j * (D.normSqDefect j - D.normSqDefect i) by ring, abs_mul]
  have hgd : |D.normSqDefect j - D.normSqDefect i| ≤ 2 * g := by
    have := abs_sub (D.normSqDefect j) (D.normSqDefect i)
    linarith [hg i, hg j]
  by_cases hij : i = j
  · rw [hij, sub_self, abs_zero, mul_zero]
    positivity
  have hT : |D.tridiagonal i j| ≤ b := by
    simp only [tridiagonal, Matrix.of_apply, if_neg hij]
    split_ifs
    · exact hb i i.2
    · exact hb j j.2
    · rw [abs_zero]
      exact hb0
  exact mul_le_mul hT hgd (abs_nonneg _) hb0

/-- **The Gram commutator is small when the recurrence nearly holds**: if
$\lvert p_j\rvert \le a$, $\lvert\beta_j\rvert \le b$ ($j < k$) and $\lvert\gamma_i\rvert \le g$,
then
$$\|\mathbf{M}_k\|_2 \le 2a + 2\|\mathbf{V}_k\|_{\mathsf{F}}\|\mathbf{F}_k\|_{\mathsf{F}}
+ 2kbg \,.$$
No printed source; the maintainer's draft, `lem:gram-commutator`, bounds every entry and passes
to the Frobenius norm ($2k$ times the maximum); here the strict upper part is bounded at once by
`NLAlib.LanczosData.gramCommutator_sub_transpose`. -/
theorem specNorm_gramCommutator_le {a b g : ℝ} (ha : ∀ j < k, |D.adjacentInner j| ≤ a)
    (hb : ∀ j < k, |D.β j| ≤ b) (hg : ∀ i, |D.normSqDefect i| ≤ g) :
    specNorm D.gramCommutator ≤
      2 * a + 2 * (frobNorm D.basis * frobNorm D.residual) + k * (b * (2 * g)) := by
  have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha 0 D.k_pos)
  set M := D.gramCommutator
  set Dg : Matrix (Fin k) (Fin k) ℝ := Matrix.diagonal fun i => M i i
  have hD : specNorm Dg ≤ 2 * a := by
    refine specNorm_diagonal_le (by positivity) fun i => ?_
    rw [Real.norm_eq_abs]
    exact D.abs_gramCommutator_apply_self_le ha i
  have hVF : frobNorm (D.basisᵀ * D.residual) ≤ frobNorm D.basis * frobNorm D.residual :=
    (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans (by
      rw [specNorm_transpose]
      gcongr
      exact specNorm_le_frobNorm _)
  have hFV : frobNorm (D.residualᵀ * D.basis) ≤ frobNorm D.basis * frobNorm D.residual := by
    rw [← frobNorm_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
    exact hVF
  have hC := D.frobNorm_tridiagonal_mul_diagonal_sub_diagonal_mul_tridiagonal_le hb hg
  have hS : frobNorm (M - Mᵀ) ≤
      2 * (frobNorm D.basis * frobNorm D.residual) + k * (b * (2 * g)) := by
    rw [D.gramCommutator_sub_transpose]
    refine (frobNorm_sub_le _ _).trans ?_
    refine (add_le_add_left (frobNorm_sub_le _ _) _).trans ?_
    linarith
  have hU : specNorm (M - Dg) ≤ 2 * (frobNorm D.basis * frobNorm D.residual) +
      k * (b * (2 * g)) :=
    ((specNorm_le_frobNorm _).trans
      (D.isUpperTriangular_gramCommutator.frobNorm_sub_diagonal_le)).trans hS
  have hMD : M = Dg + (M - Dg) := by abel
  calc specNorm M = specNorm (Dg + (M - Dg)) := by rw [← hMD]
    _ ≤ specNorm Dg + specNorm (M - Dg) := specNorm_add_le _ _
    _ ≤ _ := by linarith

/-- **The Gram commutator in the quadratic form of an eigenvector**: for
$\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$,
$\mathbf{y}^{\mathsf{T}}\mathbf{M}_k\mathbf{y} = -\mathbf{x}^{\mathsf{T}}(\beta_k\mathbf{v}_{k+1})\,
y_{k-1}$ with $\mathbf{x} = \mathbf{V}_k\mathbf{y}$: the commutator
$\mathbf{T}_k\mathbf{R}_k - \mathbf{R}_k\mathbf{T}_k$ vanishes there. -/
theorem dotProduct_gramCommutator_mulVec {y : Fin k → ℝ} {θ : ℝ}
    (hy : D.tridiagonal *ᵥ y = θ • y) :
    y ⬝ᵥ (D.gramCommutator *ᵥ y) =
      -((D.basis *ᵥ y) ⬝ᵥ (D.β k • D.v (k + 1)) * y D.lastIndex) := by
  have h1 : y ⬝ᵥ (D.tridiagonal *ᵥ (D.gramStrictUpper *ᵥ y)) =
      θ * (y ⬝ᵥ (D.gramStrictUpper *ᵥ y)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, D.transpose_tridiagonal, hy,
      smul_dotProduct, smul_eq_mul]
  have h2 : y ⬝ᵥ (D.basisᵀ *ᵥ D.v (k + 1)) = (D.basis *ᵥ y) ⬝ᵥ D.v (k + 1) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [gramCommutator, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, dotProduct_sub, h1, hy,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Matrix.vecMulVec_mulVec,
    single_one_dotProduct, op_smul_eq_smul, h2]
  ring

/-- **Paige's bound from the Gram commutator**: for a unit eigenpair of $\mathbf{T}_k$,
$\lvert\mathbf{x}^{\mathsf{T}}(\beta_k\mathbf{v}_{k+1})\rvert\,\lvert y_{k-1}\rvert
\le \|\mathbf{M}_k\|_2$. -/
theorem abs_basis_mulVec_dotProduct_mul_abs_le {y : Fin k → ℝ} {θ : ℝ}
    (hy : D.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    |(D.basis *ᵥ y) ⬝ᵥ (D.β k • D.v (k + 1))| * |y D.lastIndex| ≤ specNorm D.gramCommutator := by
  have h := norm_star_dotProduct_mulVec_le D.gramCommutator y y
  rw [star_trivial, Real.norm_eq_abs, hy1, one_mul, mul_one,
    D.dotProduct_gramCommutator_mulVec hy, abs_neg, abs_mul] at h
  exact h

end LanczosData

end NLAlib
