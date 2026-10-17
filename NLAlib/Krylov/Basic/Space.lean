/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Tower

/-!
# Krylov matrices and Krylov spaces

The Krylov matrix $\mathbf{K}_q(\mathbf{A}, \mathbf{b}) =
[\mathbf{b}, \mathbf{A}\mathbf{b}, \dots, \mathbf{A}^{q-1}\mathbf{b}]$ and its column space, the
Krylov space $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$. The space is the column space of a matrix,
so the projector, rank, pseudoinverse and Gram–Schmidt API of the Matrix layer applies to it. Its
vectors are the $p(\mathbf{A})\mathbf{b}$ with $\deg p < q$, for polynomials over $\Bbbk$ or over
any subfield, in particular $\mathbb{R}$, which is how real polynomial bounds reach it.

The index $q$ counts generators: $\mathcal{K}_0 = \{\mathbf{0}\}$, and $q$ matrix-vector products
reach $\mathcal{K}_{q+1}$.

## Main definitions

* `NLAlib.krylovMatrix`: the Krylov matrix, columns indexed by `Fin q`.
* `NLAlib.krylovSpace`: its column space.

## Main results

* `NLAlib.mem_krylovSpace_iff`: the polynomial description over $\Bbbk[X]$.
* `NLAlib.aeval_mulVec_mem_krylovSpace`: membership for polynomials over any subfield.
* `NLAlib.krylovSpace_mono`, `NLAlib.mulVec_mem_krylovSpace_succ`: monotonicity and
  $\mathbf{A}\mathcal{K}_q \subseteq \mathcal{K}_{q+1}$.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **Krylov matrix** $\mathbf{K}_q(\mathbf{A}, \mathbf{b}) =
[\mathbf{b}, \mathbf{A}\mathbf{b}, \dots, \mathbf{A}^{q-1}\mathbf{b}]$: column $j$ is
$\mathbf{A}^j\mathbf{b}$, for $j < q$. For $q = 0$ it has no columns.
[Saad2003, §6.2]. -/
def krylovMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) : Matrix n (Fin q) 𝕜 :=
  Matrix.of fun i j => (A ^ (j : ℕ) *ᵥ b) i

/-- Column $j$ of the Krylov matrix is $\mathbf{A}^j\mathbf{b}$. -/
@[simp]
theorem krylovMatrix_apply (A : Matrix n n 𝕜) (b : n → 𝕜) {q : ℕ} (i : n) (j : Fin q) :
    krylovMatrix A b q i j = (A ^ (j : ℕ) *ᵥ b) i :=
  rfl

/-- The first $q$ columns of a longer Krylov matrix form the shorter one. -/
theorem krylovMatrix_submatrix_castLE (A : Matrix n n 𝕜) (b : n → 𝕜) {q q' : ℕ} (h : q ≤ q') :
    (krylovMatrix A b q').submatrix id (Fin.castLE h) = krylovMatrix A b q :=
  rfl

/-- The **Krylov space** $\mathcal{K}_q(\mathbf{A}, \mathbf{b}) =
\operatorname{span}\{\mathbf{b}, \mathbf{A}\mathbf{b}, \dots, \mathbf{A}^{q-1}\mathbf{b}\}$, the
column space of `krylovMatrix A b q`; $\mathcal{K}_0 = \{\mathbf{0}\}$.
[Saad2003, §6.2]. -/
def krylovSpace (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) : Submodule 𝕜 (n → 𝕜) :=
  LinearMap.range (krylovMatrix A b q).mulVecLin

/-- **The polynomial description of the Krylov space**: $\mathbf{x} \in \mathcal{K}_q$ exactly
when $\mathbf{x} = p(\mathbf{A})\mathbf{b}$ for a polynomial $p \in \Bbbk[X]$ of degree less
than $q$. [Saad2003, §6.2].
Proof: $\mathbf{K}\mathbf{c} = \sum_j c_j\mathbf{A}^j\mathbf{b}$, `Polynomial.aeval_eq_sum_range'`,
`Polynomial.degreeLTEquiv`, `Polynomial.mem_degreeLT`. Small. -/
theorem mem_krylovSpace_iff {A : Matrix n n 𝕜} {b x : n → 𝕜} {q : ℕ} :
    x ∈ krylovSpace A b q ↔ ∃ p : 𝕜[X], p.degree < q ∧ aeval A p *ᵥ b = x := by
  sorry

/-- A polynomial of degree less than $q$ with coefficients in any subfield, in particular a
real polynomial, applied to $\mathbf{b}$ lies in $\mathcal{K}_q$.
Proof: map $p$ to $\Bbbk[X]$ (`Polynomial.aeval_map_algebraMap`, `Polynomial.degree_map_le`) and
`mem_krylovSpace_iff`. Small. -/
theorem aeval_mulVec_mem_krylovSpace {R : Type*} [CommSemiring R] [Algebra R 𝕜]
    (A : Matrix n n 𝕜) (b : n → 𝕜) {q : ℕ} {p : R[X]} (hp : p.degree < q) :
    aeval A p *ᵥ b ∈ krylovSpace A b q := by
  sorry

/-- The Krylov spaces increase with $q$. -/
theorem krylovSpace_mono (A : Matrix n n 𝕜) (b : n → 𝕜) : Monotone (krylovSpace A b) := by
  sorry

/-- The empty Krylov space. -/
@[simp]
theorem krylovSpace_zero (A : Matrix n n 𝕜) (b : n → 𝕜) : krylovSpace A b 0 = ⊥ := by
  sorry

/-- The starting vector lies in every nonempty Krylov space. -/
theorem self_mem_krylovSpace (A : Matrix n n 𝕜) (b : n → 𝕜) {q : ℕ} (hq : 0 < q) :
    b ∈ krylovSpace A b q := by
  sorry

/-- $\mathbf{A}\mathcal{K}_q \subseteq \mathcal{K}_{q+1}$. -/
theorem mulVec_mem_krylovSpace_succ {A : Matrix n n 𝕜} {b x : n → 𝕜} {q : ℕ}
    (hx : x ∈ krylovSpace A b q) : A *ᵥ x ∈ krylovSpace A b (q + 1) := by
  sorry

end NLAlib
