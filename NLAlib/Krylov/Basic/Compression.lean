/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.Space
public import NLAlib.Matrix.Functions.Polynomial

/-!
# Compressions to a Krylov space

For $\mathbf{Q}$ with orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$ and
the compression $\mathbf{T} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$, polynomials of low
degree pass through the compression:
$\mathbf{Q}^{\mathsf{H}}p(\mathbf{A})\mathbf{b} = p(\mathbf{T})\mathbf{Q}^{\mathsf{H}}\mathbf{b}$
for $\deg p \le q$, and $\mathbf{Q}p(\mathbf{T})\mathbf{Q}^{\mathsf{H}}\mathbf{b} =
p(\mathbf{A})\mathbf{b}$ for $\deg p < q$. Neither needs $\mathbf{A}$ Hermitian. For Hermitian
$\mathbf{A}$ the nodal polynomial of the Ritz values (the eigenvalues of $\mathbf{T}$),
$\pi(z) = \prod_\theta (z - \theta)$, makes $\pi(\mathbf{A})\mathbf{b}$ orthogonal to the
Krylov space: the Ritz polynomial is the orthogonal polynomial of the spectral measure of
$\mathbf{b}$, stated without the measure.

Polynomials have coefficients in any ring `R` acting on `𝕜`, in practice `𝕜` or `ℝ`.

## Main results

* `NLAlib.HasOrthonormalCols.conjTranspose_mulVec_aeval_mulVec_eq`: $\deg p \le q$.
* `NLAlib.HasOrthonormalCols.mulVec_aeval_conjTranspose_mul_mul_mulVec_eq`: exactness,
  $\deg p < q$.
* `NLAlib.HasOrthonormalCols.conjTranspose_mulVec_aeval_nodal_mulVec_eq_zero`: orthogonality of
  the Ritz polynomial.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r]
  [DecidableEq r] {R : Type*} [CommSemiring R] [Algebra R 𝕜]

omit [DecidableEq n] in
/-- A vector in the column space of $\mathbf{Q}$ with orthonormal columns is fixed by
$\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$. -/
private theorem mulVec_conjTranspose_mulVec_of_mem {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {x : n → 𝕜} (hx : x ∈ LinearMap.range Q.mulVecLin) : Q *ᵥ (Qᴴ *ᵥ x) = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [Matrix.mulVecLin_apply, hQ.conjTranspose_mulVec_mulVec]

/-- The Krylov vectors pass through the compression:
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}^j\mathbf{b} =
(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^j\mathbf{Q}^{\mathsf{H}}\mathbf{b}$ for $j \le q$. -/
private theorem conjTranspose_mulVec_pow_mulVec_eq {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) {j : ℕ} (hj : j ≤ q) :
    Qᴴ *ᵥ (A ^ j *ᵥ b) = (Qᴴ * A * Q) ^ j *ᵥ (Qᴴ *ᵥ b) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hmem : A ^ j *ᵥ b ∈ LinearMap.range Q.mulVecLin := by
      rw [hK]
      exact pow_mulVec_mem_krylovSpace A b (by omega)
    rw [pow_succ', ← Matrix.mulVec_mulVec, ← mulVec_conjTranspose_mulVec_of_mem hQ hmem,
      ih (by omega), pow_succ', ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- **Polynomials of degree at most $q$ pass through the compression**: for $\mathbf{Q}$ with
orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$ and $\deg p \le q$,
$\mathbf{Q}^{\mathsf{H}}p(\mathbf{A})\mathbf{b} =
p(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})\,\mathbf{Q}^{\mathsf{H}}\mathbf{b}$, for every
$\mathbf{A}$. [Saad1992, Lemma 3.1]. -/
theorem HasOrthonormalCols.conjTranspose_mulVec_aeval_mulVec_eq {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) {p : R[X]} (hp : p.degree ≤ q) :
    Qᴴ *ᵥ (aeval A p *ᵥ b) = aeval (Qᴴ * A * Q) p *ᵥ (Qᴴ *ᵥ b) := by
  rw [← aeval_map_algebraMap 𝕜, ← aeval_map_algebraMap 𝕜 (Qᴴ * A * Q)]
  set p' := p.map (algebraMap R 𝕜)
  have hp' : p'.natDegree ≤ q := natDegree_le_of_degree_le (degree_map_le.trans hp)
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.sum_mulVec, Matrix.sum_mulVec,
    Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
    conjTranspose_mulVec_pow_mulVec_eq hQ hK
      ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hp')]

/-- **Exactness on polynomials of degree less than $q$**: for $\mathbf{Q}$ with orthonormal
columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$ and $\deg p < q$,
$\mathbf{Q}\,p(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})\,\mathbf{Q}^{\mathsf{H}}\mathbf{b} =
p(\mathbf{A})\mathbf{b}$, for every $\mathbf{A}$. [Saad1992, Lemma 3.1]. -/
theorem HasOrthonormalCols.mulVec_aeval_conjTranspose_mul_mul_mulVec_eq {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) {p : R[X]} (hp : p.degree < q) :
    Q *ᵥ (aeval (Qᴴ * A * Q) p *ᵥ (Qᴴ *ᵥ b)) = aeval A p *ᵥ b := by
  rw [← hQ.conjTranspose_mulVec_aeval_mulVec_eq hK hp.le]
  exact mulVec_conjTranspose_mulVec_of_mem hQ (hK ▸ aeval_mulVec_mem_krylovSpace A b hp)

/-- **The Ritz polynomial is orthogonal to the Krylov space**: for Hermitian $\mathbf{A}$,
$\mathbf{Q}$ with orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$ and a
finite set $s$ of at most $q$ reals containing the spectrum of
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$,
$\mathbf{Q}^{\mathsf{H}}\pi_s(\mathbf{A})\mathbf{b} = \mathbf{0}$ for
$\pi_s(z) = \prod_{\theta \in s}(z - \theta)$. Taking $s$ the set of Ritz values (at most
$\dim\mathcal{K}_q \le q$ of them) gives $\mathbf{b}^{\mathsf{H}}\pi(\mathbf{A})p(\mathbf{A})
\mathbf{b} = 0$ for $\deg p < q$.
[GolubMeurant2010, §4]; [ChenPersson2026, (11)]. -/
theorem HasOrthonormalCols.conjTranspose_mulVec_aeval_nodal_mulVec_eq_zero {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) {s : Finset ℝ}
    (hs : spectrum ℝ (Qᴴ * A * Q) ⊆ ↑s) (hsq : s.card ≤ q) :
    Qᴴ *ᵥ (aeval A (Lagrange.nodal s id) *ᵥ b) = 0 := by
  have hT : (Qᴴ * A * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  rw [hQ.conjTranspose_mulVec_aeval_mulVec_eq hK
      (by rw [Lagrange.degree_nodal]; exact_mod_cast hsq),
    hT.aeval_nodal_eq_zero hs, Matrix.zero_mulVec]

end NLAlib
