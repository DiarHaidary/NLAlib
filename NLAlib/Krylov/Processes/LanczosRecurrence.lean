/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.Lanczos

/-!
# The Lanczos three-term recurrence

The Lanczos algorithm as a total recursion on a state indexed by the step: the state before step
$j$ holds $\mathbf{q}_{j-1}$, $\mathbf{q}_j$ and $\beta_j$, and a step forms
$\mathbf{w} = \mathbf{A}\mathbf{q}_j - \beta_j\mathbf{q}_{j-1} - \alpha_j\mathbf{q}_j$, then
$\beta_{j+1} = \|\mathbf{w}\|$ and $\mathbf{q}_{j+1} = \mathbf{w}/\beta_{j+1}$. Breakdown is a
value: with $0^{-1} = 0$ the vector after $\beta_{j+1} = 0$ is zero and the state stays zero.

The realisation theorems say that for Hermitian $\mathbf{A}$ the recurrence computes the
canonical Lanczos basis `arnoldiMatrix A b q` and its compression, for every $q$ and with no
breakdown hypothesis, because past the grade both the recurrence and the canonical basis are zero.
Breakdown happens exactly at the grade.

## Main definitions

* `NLAlib.LanczosState`, `NLAlib.lanczosAlpha`, `NLAlib.lanczosStep`, `NLAlib.lanczosState`.
* `NLAlib.lanczosMatrix`, `NLAlib.lanczosTridiagonal`: the computed basis and tridiagonal matrix.

## Main results

* `Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix`: the recurrence computes the Lanczos basis.
* `Matrix.IsHermitian.lanczosTridiagonal_eq`: it computes the compression.
* `Matrix.IsHermitian.lanczosState_beta_eq_zero_iff`: breakdown happens exactly at the grade.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The state of the Lanczos recurrence before step $j$: the vectors $\mathbf{q}_{j-1}$,
$\mathbf{q}_j$ and the coefficient $\beta_j$ that couples them. -/
structure LanczosState (𝕜 n : Type*) where
  /-- The previous Lanczos vector $\mathbf{q}_{j-1}$ ($\mathbf{0}$ for $j = 0$). -/
  prev : n → 𝕜
  /-- The current Lanczos vector $\mathbf{q}_j$. -/
  cur : n → 𝕜
  /-- The coefficient $\beta_j = \|\mathbf{w}_{j-1}\|$ ($0$ for $j = 0$). -/
  beta : ℝ

/-- The diagonal coefficient of a Lanczos step,
$\alpha_j = \operatorname{Re}\langle\mathbf{q}_j, \mathbf{A}\mathbf{q}_j - \beta_j
\mathbf{q}_{j-1}\rangle$; in exact arithmetic and for Hermitian $\mathbf{A}$ it is
$\mathbf{q}_j^{\mathsf{H}}\mathbf{A}\mathbf{q}_j$. -/
noncomputable def lanczosAlpha (A : Matrix n n 𝕜) (s : LanczosState 𝕜 n) : ℝ :=
  RCLike.re (star s.cur ⬝ᵥ (A *ᵥ s.cur - (s.beta : 𝕜) • s.prev))

/-- **One Lanczos step** in Paige's order:
$\mathbf{w} = \mathbf{A}\mathbf{q}_j - \beta_j\mathbf{q}_{j-1} - \alpha_j\mathbf{q}_j$,
$\beta_{j+1} = \|\mathbf{w}\|$, $\mathbf{q}_{j+1} = \beta_{j+1}^{-1}\mathbf{w}$. At breakdown,
$\beta_\nu = 0$ at the grade $\nu$, the state is $(\mathbf{q}_{\nu-1}, \mathbf{0}, 0)$, and it is
zero from the following step on. [Paige1972]; [Saad2011, §6.6]. -/
noncomputable def lanczosStep (A : Matrix n n 𝕜) (s : LanczosState 𝕜 n) : LanczosState 𝕜 n :=
  let w := A *ᵥ s.cur - (s.beta : 𝕜) • s.prev - (lanczosAlpha A s : 𝕜) • s.cur
  ⟨s.cur, (‖WithLp.toLp 2 w‖⁻¹ : 𝕜) • w, ‖WithLp.toLp 2 w‖⟩

/-- The **Lanczos recurrence**: the state before step $j$, from
$(\mathbf{0}, \mathbf{b}/\|\mathbf{b}\|, 0)$. [Saad2011, §6.6]. -/
noncomputable def lanczosState (A : Matrix n n 𝕜) (b : n → 𝕜) : ℕ → LanczosState 𝕜 n
  | 0 => ⟨0, (‖WithLp.toLp 2 b‖⁻¹ : 𝕜) • b, 0⟩
  | j + 1 => lanczosStep A (lanczosState A b j)

/-- The basis computed by $q$ steps of the Lanczos recurrence: column $j$ is $\mathbf{q}_j$. -/
noncomputable def lanczosMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) : Matrix n (Fin q) 𝕜 :=
  Matrix.of fun i j => (lanczosState A b j).cur i

/-- The tridiagonal matrix computed by the Lanczos recurrence: $\alpha_0, \dots, \alpha_{q-1}$ on
the diagonal, $\beta_1, \dots, \beta_{q-1}$ beside it. -/
noncomputable def lanczosTridiagonal (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    Matrix (Fin q) (Fin q) 𝕜 :=
  Matrix.of fun i j =>
    if i = j then (lanczosAlpha A (lanczosState A b i) : 𝕜)
    else if (i : ℕ) = j + 1 then ((lanczosState A b i).beta : 𝕜)
    else if (j : ℕ) = i + 1 then ((lanczosState A b j).beta : 𝕜)
    else 0

/-- **The Lanczos recurrence computes the canonical basis**, for Hermitian $\mathbf{A}$ and every
$q$, with no breakdown hypothesis: past the grade both are zero. [Saad2011, §6.6].
Proof: below the grade, by strong induction the computed vectors are orthonormal with
$\mathbf{q}_j \in c_j\mathbf{A}^j\mathbf{b} + \mathcal{K}_j$, $c_j > 0$
(`isGradedKrylovBasis_of_forall_col_mem`), and `IsGradedKrylovBasis.eq_arnoldiMatrix` gives
equality; at the grade $\mathbf{w} = \mathbf{0}$ (`krylovGrade_le_iff`); past it both sides are
zero (a zero `gramSchmidtR` diagonal entry is a zero column, by the diagonal of
`conjTranspose_gramSchmidtQ_mul_self`); `arnoldiMatrix_submatrix_castLE` for nesting. Large,
500 to 700 lines with the next two theorems.
Result: lanczos-recurrence -/
theorem _root_.Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) : lanczosMatrix A b q = arnoldiMatrix A b q := by
  sorry

/-- **The Lanczos recurrence computes the compression**: for Hermitian $\mathbf{A}$ and every
$q$, the computed tridiagonal matrix is $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ for the
canonical basis $\mathbf{Q}$. -/
theorem _root_.Matrix.IsHermitian.lanczosTridiagonal_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (q : ℕ) :
    lanczosTridiagonal A b q = (arnoldiMatrix A b q)ᴴ * A * arnoldiMatrix A b q := by
  sorry

/-- **Lanczos breaks down exactly at the grade**: for Hermitian $\mathbf{A}$,
$\beta_{j+1} = 0$ iff $\nu \le j + 1$. -/
theorem _root_.Matrix.IsHermitian.lanczosState_beta_eq_zero_iff {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (j : ℕ) :
    (lanczosState A b (j + 1)).beta = 0 ↔ krylovGrade A b ≤ j + 1 := by
  sorry

end NLAlib
