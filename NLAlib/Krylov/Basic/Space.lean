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

* `NLAlib.krylovSpace_eq_span`, `NLAlib.krylovSpace_succ`: the span of the Krylov vectors, one
  generator per step.
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

/-- The Krylov space is the span of the Krylov vectors $\mathbf{A}^j\mathbf{b}$, $j < q$. -/
theorem krylovSpace_eq_span (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    krylovSpace A b q = Submodule.span 𝕜 (Set.range fun j : Fin q => A ^ (j : ℕ) *ᵥ b) := by
  rw [krylovSpace, Matrix.range_mulVecLin]
  rfl

/-- The Krylov vector $\mathbf{A}^j\mathbf{b}$ lies in $\mathcal{K}_q$ for $j < q$. -/
theorem pow_mulVec_mem_krylovSpace (A : Matrix n n 𝕜) (b : n → 𝕜) {q j : ℕ} (hj : j < q) :
    A ^ j *ᵥ b ∈ krylovSpace A b q := by
  rw [krylovSpace_eq_span]
  exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

private lemma aeval_sum_fin_mulVec (A : Matrix n n 𝕜) (b : n → 𝕜) {q : ℕ} (c : Fin q → 𝕜) :
    aeval A (∑ i : Fin q, C (c i) * X ^ (i : ℕ)) *ᵥ b = ∑ i : Fin q, c i • (A ^ (i : ℕ) *ᵥ b) := by
  simp [map_sum, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]

/-- **The polynomial description of the Krylov space**: $\mathbf{x} \in \mathcal{K}_q$ exactly
when $\mathbf{x} = p(\mathbf{A})\mathbf{b}$ for a polynomial $p \in \Bbbk[X]$ of degree less
than $q$. [Saad2003, §6.2].
Port of `NLAlib.mem_krylovSpace_iff` (prototype, real scalars). -/
theorem mem_krylovSpace_iff {A : Matrix n n 𝕜} {b x : n → 𝕜} {q : ℕ} :
    x ∈ krylovSpace A b q ↔ ∃ p : 𝕜[X], p.degree < q ∧ aeval A p *ᵥ b = x := by
  rw [krylovSpace_eq_span]
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hx
    exact ⟨_, degree_sum_fin_lt c, aeval_sum_fin_mulVec A b c⟩
  · rintro ⟨p, hp, rfl⟩
    by_cases hp0 : p = 0
    · subst hp0
      simp
    have hnat : p.natDegree < q := (natDegree_lt_iff_degree_lt hp0).2 hp
    rw [p.as_sum_range' q hnat]
    simp_rw [← C_mul_X_pow_eq_monomial]
    rw [← Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i), aeval_sum_fin_mulVec]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- A polynomial of degree less than $q$ with coefficients in any subfield, in particular a
real polynomial, applied to $\mathbf{b}$ lies in $\mathcal{K}_q$. -/
theorem aeval_mulVec_mem_krylovSpace {R : Type*} [CommSemiring R] [Algebra R 𝕜]
    (A : Matrix n n 𝕜) (b : n → 𝕜) {q : ℕ} {p : R[X]} (hp : p.degree < q) :
    aeval A p *ᵥ b ∈ krylovSpace A b q := by
  rw [← aeval_map_algebraMap 𝕜]
  exact mem_krylovSpace_iff.2 ⟨_, (degree_map_le).trans_lt hp, rfl⟩

/-- The Krylov spaces increase with $q$. -/
theorem krylovSpace_mono (A : Matrix n n 𝕜) (b : n → 𝕜) : Monotone (krylovSpace A b) := by
  intro q q' h
  rw [krylovSpace_eq_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  exact pow_mulVec_mem_krylovSpace A b (j.isLt.trans_le h)

/-- The empty Krylov space. -/
@[simp]
theorem krylovSpace_zero (A : Matrix n n 𝕜) (b : n → 𝕜) : krylovSpace A b 0 = ⊥ := by
  rw [krylovSpace_eq_span, Set.range_eq_empty, Submodule.span_empty]

/-- One step adds one generator: $\mathcal{K}_{q+1} = \mathcal{K}_q +
\operatorname{span}\{\mathbf{A}^q\mathbf{b}\}$.
Port of `NLAlib.krylovSpace_succ` (prototype). -/
theorem krylovSpace_succ (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    krylovSpace A b (q + 1) = krylovSpace A b q ⊔ Submodule.span 𝕜 {A ^ q *ᵥ b} := by
  rw [krylovSpace_eq_span, krylovSpace_eq_span, ← Submodule.span_union]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨i.castSucc, rfl⟩
    · exact ⟨Fin.last q, rfl⟩

/-- The starting vector lies in every nonempty Krylov space. -/
theorem self_mem_krylovSpace (A : Matrix n n 𝕜) (b : n → 𝕜) {q : ℕ} (hq : 0 < q) :
    b ∈ krylovSpace A b q := by
  simpa using pow_mulVec_mem_krylovSpace A b hq

/-- $\mathbf{A}\mathcal{K}_q \subseteq \mathcal{K}_{q+1}$.
Port of `NLAlib.mulVec_mem_krylovSpace_succ` (prototype). -/
theorem mulVec_mem_krylovSpace_succ {A : Matrix n n 𝕜} {b x : n → 𝕜} {q : ℕ}
    (hx : x ∈ krylovSpace A b q) : A *ᵥ x ∈ krylovSpace A b (q + 1) := by
  have hle : krylovSpace A b q ≤ (krylovSpace A b (q + 1)).comap A.mulVecLin := by
    rw [krylovSpace_eq_span A b q]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    change A *ᵥ (A ^ (j : ℕ) *ᵥ b) ∈ krylovSpace A b (q + 1)
    rw [Matrix.mulVec_mulVec, ← pow_succ']
    exact pow_mulVec_mem_krylovSpace A b (Nat.succ_lt_succ j.isLt)
  exact hle hx

end NLAlib
