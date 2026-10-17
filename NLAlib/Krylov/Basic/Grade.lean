/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import NLAlib.Krylov.Basic.Space

/-!
# The grade of a vector

The grade $\nu$ of $\mathbf{b}$ with respect to $\mathbf{A}$ is the dimension of the largest
Krylov space. The Krylov spaces grow by one dimension per step up to $q = \nu$ and are constant,
and invariant under $\mathbf{A}$, from there on. It is the one breakdown vocabulary of the Krylov
layer: Lanczos and conjugate gradients break down, or terminate, exactly at the grade.

## Main definitions

* `NLAlib.krylovGrade`: the rank of the Krylov matrix with $\lvert n \rvert$ columns.

## Main results

* `NLAlib.rank_krylovMatrix`, `NLAlib.finrank_krylovSpace`: the dimension is $\min(q, \nu)$.
* `NLAlib.krylovMatrix_mulVec_injective_iff`: the Krylov vectors are independent iff $q \le \nu$.
* `NLAlib.krylovGrade_le_iff`: $\nu \le q$ iff $\mathbf{A}^q\mathbf{b} \in \mathcal{K}_q$.
* `NLAlib.mulVec_mem_krylovSpace_of_krylovGrade_le`: invariance from the grade on.
* `NLAlib.mem_krylovSpace_of_krylovGrade_le`: the solution of $\mathbf{A}\mathbf{x} = \mathbf{b}$
  lies in the Krylov space of the grade.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **grade** $\nu$ of $\mathbf{b}$ with respect to $\mathbf{A}$: the dimension of the largest
Krylov space, the rank of $\mathbf{K}_{\lvert n \rvert}(\mathbf{A}, \mathbf{b})$. The Krylov
spaces grow strictly up to $q = \nu$ and are constant from there on. $\nu = 0$ exactly when
$\mathbf{b} = \mathbf{0}$. [Saad2003, §6.2]. -/
noncomputable def krylovGrade (A : Matrix n n 𝕜) (b : n → 𝕜) : ℕ :=
  (krylovMatrix A b (Fintype.card n)).rank

/-- **The Krylov spaces stop growing exactly at the grade**: $\nu \le q$ iff
$\mathbf{A}^q\mathbf{b} \in \mathcal{K}_q$.
Proof: once $\mathbf{A}^q\mathbf{b} \in \mathcal{K}_q$ the space is invariant
(`mulVec_mem_krylovSpace_succ`), so all later spaces equal it; before, each step adds a dimension.
Medium; the core of this file. -/
theorem krylovGrade_le_iff {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ} :
    krylovGrade A b ≤ q ↔ A ^ q *ᵥ b ∈ krylovSpace A b q := by
  sorry

/-- The rank of the Krylov matrix is $\min(q, \nu)$. -/
theorem rank_krylovMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    (krylovMatrix A b q).rank = min q (krylovGrade A b) := by
  sorry

/-- The dimension of $\mathcal{K}_q$ is $\min(q, \nu)$. -/
theorem finrank_krylovSpace (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    Module.finrank 𝕜 (krylovSpace A b q) = min q (krylovGrade A b) := by
  sorry

/-- The grade is at most the dimension. -/
theorem krylovGrade_le_card (A : Matrix n n 𝕜) (b : n → 𝕜) :
    krylovGrade A b ≤ Fintype.card n := by
  sorry

/-- The Krylov vectors $\mathbf{b}, \dots, \mathbf{A}^{q-1}\mathbf{b}$ are linearly independent
exactly up to the grade: the Krylov matrix has full column rank iff $q \le \nu$. -/
theorem krylovMatrix_mulVec_injective_iff {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ} :
    Function.Injective (krylovMatrix A b q).mulVec ↔ q ≤ krylovGrade A b := by
  sorry

/-- From the grade on, the Krylov spaces are constant. -/
theorem krylovSpace_eq_of_krylovGrade_le {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ}
    (h : krylovGrade A b ≤ q) : krylovSpace A b q = krylovSpace A b (krylovGrade A b) := by
  sorry

/-- From the grade on, the Krylov space is invariant under $\mathbf{A}$. -/
theorem mulVec_mem_krylovSpace_of_krylovGrade_le {A : Matrix n n 𝕜} {b x : n → 𝕜} {q : ℕ}
    (h : krylovGrade A b ≤ q) (hx : x ∈ krylovSpace A b q) : A *ᵥ x ∈ krylovSpace A b q := by
  sorry

/-- **The solution lies in the Krylov space of the grade**: for invertible $\mathbf{A}$ and
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\mathbf{x}_\star \in \mathcal{K}_q$ once $\nu \le q$.
[Saad2003, §6.2].
Proof: $\mathbf{A}$ maps the invariant space $\mathcal{K}_q$ injectively, hence onto, itself, and
$\mathbf{b} \in \mathcal{K}_q$. Small. -/
theorem mem_krylovSpace_of_krylovGrade_le {A : Matrix n n 𝕜} (hA : IsUnit A) {b xs : n → 𝕜}
    (hxs : A *ᵥ xs = b) {q : ℕ} (h : krylovGrade A b ≤ q) : xs ∈ krylovSpace A b q := by
  sorry

end NLAlib
