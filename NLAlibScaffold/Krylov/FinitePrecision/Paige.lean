/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.Recurrence

/-!
# Paige's loss-of-orthogonality bound

For a run `L : NLAlib.LanczosRun n k`, split the Gram matrix of the computed basis as
$\mathbf{V}_k^{\mathsf{T}}\mathbf{V}_k = \mathbf{I} + \mathbf{R}_k^{\mathsf{T}} + \mathbf{\Gamma}
+ \mathbf{R}_k$ with $\mathbf{R}_k$ strictly upper triangular and $\mathbf{\Gamma}$ diagonal. The
**Gram commutator**
$\mathbf{M}_k = \mathbf{T}_k\mathbf{R}_k - \mathbf{R}_k\mathbf{T}_k
- (\mathbf{V}_k^{\mathsf{T}}\beta_k\mathbf{v}_{k+1})\mathbf{e}_k^{\mathsf{T}}$ is upper triangular
and of size $O(k^2\varepsilon\|\mathbf{H}\|_2)$, although $\mathbf{R}_k$ itself need not be small.
In the quadratic form of an eigenvector of $\mathbf{T}_k$ the commutator vanishes, which gives
Paige's bound: a Ritz vector loses orthogonality to $\mathbf{v}_{k+1}$ only when its scalar
residual estimate $\beta_k\lvert y_k\rvert$ is small, that is, only after it has converged.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `eq:M-def`, `cor:gram-commutator`, `lem:gram-commutator`, `thm:paige`;
[Paige1980, (3.11)–(3.13)] for the bound under Paige's rounding model.

## Main definitions

* `NLAlib.LanczosRun.gramStrictUpper`, `NLAlib.LanczosRun.normSqDefect`: the strict upper
  triangle $\mathbf{R}_k$ and the diagonal defects $\mathbf{\Gamma}$ of the Gram matrix.
* `NLAlib.LanczosRun.gramCommutator`: the Gram commutator $\mathbf{M}_k$.

## Main results

* `NLAlib.LanczosRun.isUpperTriangular_gramCommutator`,
  `NLAlib.LanczosRun.gramCommutator_sub_transpose`,
  `NLAlib.LanczosRun.specNorm_gramCommutator_le`: the Gram commutator.
* `NLAlib.LanczosRun.abs_basis_mulVec_dotProduct_mul_abs_le`: Paige's bound.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

namespace LanczosRun

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
private theorem frobNorm_le_card_mul {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ} {c : ℝ}
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

variable {n k : ℕ} (L : LanczosRun n k)

/-- The **strict upper triangle of the Gram matrix** of the computed basis:
$(\mathbf{R}_k)_{i,j} = \mathbf{v}_{i+1}^{\mathsf{T}}\mathbf{v}_{j+1}$ for $i < j$, and $0$
otherwise. -/
def gramStrictUpper : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => if i < j then L.v ((i : ℕ) + 1) ⬝ᵥ L.v ((j : ℕ) + 1) else 0

/-- The **diagonal defects** of the Gram matrix of the computed basis:
$\gamma_i = \|\mathbf{v}_{i+1}\|^2 - 1$ (the paper's $g_{i+1}$). -/
noncomputable def normSqDefect (i : Fin k) : ℝ :=
  ‖WithLp.toLp 2 (L.v ((i : ℕ) + 1))‖ ^ 2 - 1

/-- The **Gram commutator**
$\mathbf{M}_k = \mathbf{T}_k\mathbf{R}_k - \mathbf{R}_k\mathbf{T}_k
- (\mathbf{V}_k^{\mathsf{T}}\beta_k\mathbf{v}_{k+1})\mathbf{e}_{k-1}^{\mathsf{T}}$
(`eq:M-def` of the maintainer's draft; $\mathbf{e}_{k-1}$ the last coordinate vector, indexed
from $0$). -/
noncomputable def gramCommutator : Matrix (Fin k) (Fin k) ℝ :=
  L.tridiagonal * L.gramStrictUpper - L.gramStrictUpper * L.tridiagonal -
    Matrix.vecMulVec (L.basisᵀ *ᵥ (L.β k • L.v (k + 1))) (Pi.single L.lastIndex 1)

/-- The Gram commutator is upper triangular. No printed source; the maintainer's draft,
`lem:gram-commutator`. -/
theorem isUpperTriangular_gramCommutator : L.gramCommutator.IsUpperTriangular := by
  intro i j hji
  simp only [id] at hji
  have hT := L.isTridiagonal_tridiagonal
  have hji' : (j : ℕ) < i := hji
  simp only [gramCommutator, Matrix.sub_apply, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have h1 : ∑ l, L.tridiagonal i l * L.gramStrictUpper l j = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hlj : l < j
    · have hl : (l : ℕ) < j := hlj
      rw [hT i l (Or.inr (by omega)), zero_mul]
    · simp only [gramStrictUpper, Matrix.of_apply, if_neg hlj, mul_zero]
  have h2 : ∑ l, L.gramStrictUpper i l * L.tridiagonal l j = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hil : i < l
    · have hl : (i : ℕ) < l := hil
      rw [hT l j (Or.inr (by omega)), mul_zero]
    · simp only [gramStrictUpper, Matrix.of_apply, if_neg hil, zero_mul]
  have h3 : (Pi.single L.lastIndex (1 : ℝ) : Fin k → ℝ) j = 0 := by
    refine Pi.single_eq_of_ne (fun h => ?_) _
    have : (j : ℕ) = k - 1 := by rw [h]; rfl
    omega
  rw [h1, h2, h3]
  ring

/-- The diagonal entries of the Gram commutator are differences of inner products of consecutive
vectors: $(\mathbf{M}_k)_{i,i} = \beta_i\mathbf{v}_i^{\mathsf{T}}\mathbf{v}_{i+1}
- \mathbf{v}_{i+1}^{\mathsf{T}}(\beta_{i+1}\mathbf{v}_{i+2})$. -/
theorem gramCommutator_apply_self (i : Fin k) :
    L.gramCommutator i i =
      L.β i * (L.v i ⬝ᵥ L.v ((i : ℕ) + 1)) - L.adjacentInner i := by
  obtain ⟨i, hi⟩ := i
  simp only [gramCommutator, Matrix.sub_apply, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have hTR : ∑ l : Fin k, L.tridiagonal ⟨i, hi⟩ l * L.gramStrictUpper l ⟨i, hi⟩ =
      L.β i * (L.v i ⬝ᵥ L.v (i + 1)) := by
    have hterm : ∀ l : Fin k, L.tridiagonal ⟨i, hi⟩ l * L.gramStrictUpper l ⟨i, hi⟩ =
        (fun m : ℕ => if m + 1 = i then L.β i * (L.v i ⬝ᵥ L.v (i + 1)) else 0) l := by
      intro l
      obtain ⟨l, hl⟩ := l
      simp only [tridiagonal, gramStrictUpper, Matrix.of_apply, Fin.mk.injEq, Fin.mk_lt_mk]
      split_ifs <;> first | (exfalso; omega) | (subst_vars; ring)
    rw [Finset.sum_congr rfl fun l _ => hterm l, Fin.sum_univ_eq_sum_range
      (fun m : ℕ => if m + 1 = i then L.β i * (L.v i ⬝ᵥ L.v (i + 1)) else 0) k]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [L.β_zero]
    · rw [Finset.sum_eq_single (i - 1)]
      · rw [if_pos (by omega)]
      · intro m _ hm
        rw [if_neg (by omega)]
      · intro hm
        exact absurd (Finset.mem_range.2 (by omega)) hm
  have hRT : ∑ l : Fin k, L.gramStrictUpper ⟨i, hi⟩ l * L.tridiagonal l ⟨i, hi⟩ =
      if i + 1 < k then L.β (i + 1) * (L.v (i + 1) ⬝ᵥ L.v (i + 2)) else 0 := by
    have hterm : ∀ l : Fin k, L.gramStrictUpper ⟨i, hi⟩ l * L.tridiagonal l ⟨i, hi⟩ =
        (fun m : ℕ => if m = i + 1 then L.β (i + 1) * (L.v (i + 1) ⬝ᵥ L.v (i + 2)) else 0) l := by
      intro l
      obtain ⟨l, hl⟩ := l
      simp only [tridiagonal, gramStrictUpper, Matrix.of_apply, Fin.mk.injEq, Fin.mk_lt_mk]
      split_ifs <;> first | (exfalso; omega) | (subst_vars; ring)
    rw [Finset.sum_congr rfl fun l _ => hterm l, Fin.sum_univ_eq_sum_range
      (fun m : ℕ => if m = i + 1 then L.β (i + 1) * (L.v (i + 1) ⬝ᵥ L.v (i + 2)) else 0) k,
      Finset.sum_ite_eq' (Finset.range k) (i + 1)]
    simp only [Finset.mem_range]
  have hP : (L.basisᵀ *ᵥ (L.β k • L.v (k + 1))) ⟨i, hi⟩ = L.v (i + 1) ⬝ᵥ (L.β k • L.v (k + 1)) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, basis, Matrix.of_apply]
  rw [hTR, hRT, hP, adjacentInner]
  by_cases h : i + 1 < k
  · rw [if_pos h, Pi.single_eq_of_ne (fun h' => by
      have : i = k - 1 := congrArg Fin.val h'
      omega)]
    simp only [dotProduct_smul, smul_eq_mul, mul_zero, sub_zero]
  · have hk : i + 1 = k := by omega
    have hlast : (⟨i, hi⟩ : Fin k) = L.lastIndex := Fin.ext (by simp only [lastIndex]; omega)
    rw [if_neg h, hlast, Pi.single_eq_same]
    have hv : L.v (i + 2) = L.v (k + 1) := congrArg L.v (by omega)
    have hβ : L.β (i + 1) = L.β k := congrArg L.β hk
    rw [hv, hβ]
    ring

/-- **The skew part of the Gram commutator** is given by the residual and the diagonal defects:
$$\mathbf{M}_k - \mathbf{M}_k^{\mathsf{T}} = \mathbf{V}_k^{\mathsf{T}}\mathbf{F}_k
- \mathbf{F}_k^{\mathsf{T}}\mathbf{V}_k
- (\mathbf{T}_k\mathbf{\Gamma} - \mathbf{\Gamma}\mathbf{T}_k),
\qquad \mathbf{\Gamma} = \operatorname{diag}(\|\mathbf{v}_{i+1}\|^2 - 1)_i \,.$$
No printed source; the maintainer's draft, `eq:generic-commutator`. -/
theorem gramCommutator_sub_transpose :
    L.gramCommutator - L.gramCommutatorᵀ =
      L.basisᵀ * L.residual - L.residualᵀ * L.basis -
        (L.tridiagonal * Matrix.diagonal L.normSqDefect -
          Matrix.diagonal L.normSqDefect * L.tridiagonal) := by
  set V := L.basis
  set T := L.tridiagonal
  set R := L.gramStrictUpper
  set P := Matrix.vecMulVec (L.basisᵀ *ᵥ (L.β k • L.v (k + 1))) (Pi.single L.lastIndex (1 : ℝ))
  set Γ := Matrix.diagonal L.normSqDefect
  have hP : Vᵀ * Matrix.vecMulVec (L.β k • L.v (k + 1)) (Pi.single L.lastIndex 1) = P :=
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
  have hT : Tᵀ = T := L.transpose_tridiagonal
  have hX : Vᵀ * (L.H * V) = (1 + Γ + R + Rᵀ) * T + P + Vᵀ * L.residual := by
    rw [L.H_mul_basis, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, hG, hP]
  have hXt : (Vᵀ * (L.H * V))ᵀ = Vᵀ * (L.H * V) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, L.transpose_H,
      Matrix.mul_assoc]
  have hΓ : Γᵀ = Γ := Matrix.diagonal_transpose _
  rw [hX] at hXt
  simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, hT, hΓ,
    Matrix.add_mul, Matrix.one_mul] at hXt
  have hM : L.gramCommutator = T * R - R * T - P := rfl
  rw [hM, Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    hT]
  calc T * R - R * T - P - (Rᵀ * T - T * Rᵀ - Pᵀ)
      = Vᵀ * L.residual - L.residualᵀ * V - (T * Γ - Γ * T) +
          ((T + T * Γ + T * Rᵀ + T * R + Pᵀ + L.residualᵀ * V) -
            (T + Γ * T + R * T + Rᵀ * T + P + Vᵀ * L.residual)) := by abel
    _ = Vᵀ * L.residual - L.residualᵀ * V - (T * Γ - Γ * T) := by
        rw [hXt, sub_self, add_zero]

/-- **The Gram commutator is small**:
$\|\mathbf{M}_k\|_2 \le 30k^2\varepsilon\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `cor:gram-commutator`, states
$\|\mathbf{M}_k\| \lesssim_k \varepsilon\|\mathbf{A}\|$ (its formalization: $3000k^3$); here the
strict upper part is bounded in the Frobenius norm by that of
`NLAlib.LanczosRun.gramCommutator_sub_transpose`, and the diagonal entry by entry, which saves a
factor $k$. [Paige1976, (22)]; [Paige1980, (2.17)–(2.18)].
Result: lanczos-gram-commutator -/
theorem specNorm_gramCommutator_le :
    specNorm L.gramCommutator ≤ 30 * k ^ 2 * L.ε * specNorm L.H := by
  have hε0 := L.ε_nonneg
  have hε1 := L.ε_le
  have hH := specNorm_nonneg L.H
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.k_pos
  set M := L.gramCommutator
  set D : Matrix (Fin k) (Fin k) ℝ := Matrix.diagonal fun i => M i i
  -- the diagonal
  have hD : specNorm D ≤ 14 * k * L.ε * specNorm L.H := by
    refine specNorm_diagonal_le (by positivity) fun i => ?_
    rw [Real.norm_eq_abs]
    change |L.gramCommutator i i| ≤ _
    rw [L.gramCommutator_apply_self]
    have h2 := L.abs_adjacentInner_le i.2
    have hi : ((i : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast i.2
    have h1 : |L.β i * (L.v i ⬝ᵥ L.v ((i : ℕ) + 1))| ≤ 7 * k * L.ε * specNorm L.H := by
      rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
      · rw [h0, L.β_zero, zero_mul, abs_zero]
        positivity
      · have h := L.abs_adjacentInner_le (j := (i : ℕ) - 1) (by omega)
        rw [adjacentInner, show (i : ℕ) - 1 + 1 = i by omega,
          show (i : ℕ) - 1 + 2 = i + 1 by omega, dotProduct_smul, smul_eq_mul] at h
        refine h.trans ?_
        have : (((i : ℕ) - 1 : ℕ) : ℝ) + 1 ≤ k := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          linarith
        gcongr
    calc |L.β i * (L.v i ⬝ᵥ L.v ((i : ℕ) + 1)) - L.adjacentInner i|
        ≤ |L.β i * (L.v i ⬝ᵥ L.v ((i : ℕ) + 1))| + |L.adjacentInner i| := abs_sub _ _
      _ ≤ 7 * k * L.ε * specNorm L.H + 7 * k * L.ε * specNorm L.H := by
          gcongr
          exact h2.trans (by gcongr)
      _ = 14 * k * L.ε * specNorm L.H := by ring
  -- the Frobenius norm of the computed basis
  have hV : frobNorm L.basis ≤ (1 + L.ε / 2) * Real.sqrt k := by
    have hsq : frobNorm L.basis ^ 2 ≤ ((1 + L.ε / 2) * Real.sqrt k) ^ 2 := by
      rw [frobNorm_sq_eq_sum_col, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
      calc ∑ j, ‖WithLp.toLp 2 (L.basis.col j)‖ ^ 2 ≤ ∑ _j : Fin k, (1 + L.ε / 2) ^ 2 :=
            Finset.sum_le_sum fun j _ =>
              pow_le_pow_left₀ (norm_nonneg _) (L.norm_v_le (j := (j : ℕ) + 1) j.2) 2
        _ = (1 + L.ε / 2) ^ 2 * k := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    exact (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).1 hsq
  have hF := L.frobNorm_residual_le
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg k)
  have hVF : frobNorm (L.basisᵀ * L.residual) ≤ 201 / 200 * 6 * k ^ 2 * L.ε * specNorm L.H := by
    calc frobNorm (L.basisᵀ * L.residual)
        ≤ specNorm L.basisᵀ * frobNorm L.residual := frobNorm_mul_le_specNorm_mul_frobNorm _ _
      _ ≤ frobNorm L.basis * frobNorm L.residual := by
          rw [specNorm_transpose]
          gcongr
          exact specNorm_le_frobNorm _
      _ ≤ ((1 + L.ε / 2) * Real.sqrt k) * (6 * k * Real.sqrt k * L.ε * specNorm L.H) := by
          gcongr
      _ = (1 + L.ε / 2) * 6 * (Real.sqrt k * Real.sqrt k) * k * L.ε * specNorm L.H := by ring
      _ ≤ 201 / 200 * 6 * k ^ 2 * L.ε * specNorm L.H := by
          rw [hsk]
          have : (1 + L.ε / 2) ≤ 201 / 200 := by linarith
          have h0 : 0 ≤ (k : ℝ) * k * L.ε * specNorm L.H := by positivity
          nlinarith
  have hFV : frobNorm (L.residualᵀ * L.basis) ≤ 201 / 200 * 6 * k ^ 2 * L.ε * specNorm L.H := by
    rw [← frobNorm_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
    exact hVF
  have hC : frobNorm (L.tridiagonal * Matrix.diagonal L.normSqDefect -
      Matrix.diagonal L.normSqDefect * L.tridiagonal) ≤ k * (5 / 2 * k * L.ε * specNorm L.H) := by
    have := frobNorm_le_card_mul (M := L.tridiagonal * Matrix.diagonal L.normSqDefect -
      Matrix.diagonal L.normSqDefect * L.tridiagonal) (c := 5 / 2 * k * L.ε * specNorm L.H)
      (by positivity) (fun i j => ?_)
    · simpa only [Fintype.card_fin] using this
    rw [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      show L.tridiagonal i j * L.normSqDefect j - L.normSqDefect i * L.tridiagonal i j =
        L.tridiagonal i j * (L.normSqDefect j - L.normSqDefect i) by ring, abs_mul]
    have hg : ∀ l : Fin k, |L.normSqDefect l| ≤ L.ε := fun l =>
      L.abs_norm_v_sq_sub_one_le ((l : ℕ) + 1) (by omega) l.2
    have hgd : |L.normSqDefect j - L.normSqDefect i| ≤ 2 * L.ε := by
      have := abs_sub (L.normSqDefect j) (L.normSqDefect i)
      linarith [hg i, hg j]
    have hTij : |L.tridiagonal i j| ≤ 5 / 4 * k * specNorm L.H ∨ i = j := by
      by_cases hij : i = j
      · exact Or.inr hij
      left
      have hb : ∀ m : ℕ, m < k → |L.β m| ≤ 5 / 4 * k * specNorm L.H := fun m hm => by
        rw [abs_of_nonneg (L.β_nonneg m hm.le)]
        refine (L.β_le hm.le).trans ?_
        have : (m : ℝ) ≤ k := by exact_mod_cast hm.le
        gcongr
      simp only [tridiagonal, Matrix.of_apply, if_neg hij]
      split_ifs
      · exact hb i i.2
      · exact hb j j.2
      · rw [abs_zero]
        positivity
    rcases hTij with hTij | rfl
    · calc |L.tridiagonal i j| * |L.normSqDefect j - L.normSqDefect i|
          ≤ 5 / 4 * k * specNorm L.H * (2 * L.ε) := by gcongr
        _ = 5 / 2 * k * L.ε * specNorm L.H := by ring
    · rw [sub_self, abs_zero, mul_zero]
      positivity
  have hS : frobNorm (M - Mᵀ) ≤ 15 * k ^ 2 * L.ε * specNorm L.H := by
    rw [L.gramCommutator_sub_transpose]
    refine (frobNorm_sub_le _ _).trans ?_
    refine (add_le_add_left (frobNorm_sub_le _ _) _).trans ?_
    have : k * (5 / 2 * k * L.ε * specNorm L.H) = 5 / 2 * k ^ 2 * L.ε * specNorm L.H := by ring
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (k : ℝ)) hε0) hH]
  have hU : specNorm (M - D) ≤ 15 * k ^ 2 * L.ε * specNorm L.H :=
    ((specNorm_le_frobNorm _).trans
      (L.isUpperTriangular_gramCommutator.frobNorm_sub_diagonal_le)).trans hS
  have hMD : M = D + (M - D) := by abel
  calc specNorm M = specNorm (D + (M - D)) := by rw [← hMD]
    _ ≤ specNorm D + specNorm (M - D) := specNorm_add_le _ _
    _ ≤ 14 * k * L.ε * specNorm L.H + 15 * k ^ 2 * L.ε * specNorm L.H := add_le_add hD hU
    _ ≤ 30 * k ^ 2 * L.ε * specNorm L.H := by
        have h0 : 0 ≤ L.ε * specNorm L.H := by positivity
        nlinarith [mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ k ^ 2 by nlinarith) h0]

/-- **Paige's loss-of-orthogonality bound**: for a unit eigenpair
$\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$, $\|\mathbf{y}\| = 1$, of the computed tridiagonal
matrix, the Ritz vector $\mathbf{x} = \mathbf{V}_k\mathbf{y}$ satisfies
$$\lvert\mathbf{x}^{\mathsf{T}}(\beta_k\mathbf{v}_{k+1})\rvert\,\lvert y_{k-1}\rvert
\le 30k^2\varepsilon\|\mathbf{H}\|_2$$
($y_{k-1}$ the last entry, indexed from $0$): orthogonality to $\mathbf{v}_{k+1}$ is lost only
along Ritz vectors whose residual estimate $\beta_k\lvert y_{k-1}\rvert$ is small.
No printed source; the maintainer's draft, `thm:paige`, states
$\lvert\mathbf{x}^{\mathsf{T}}\mathbf{v}_{k+1}\rvert\beta_k\lvert\mathbf{e}_k^{\mathsf{T}}
\mathbf{y}\rvert \lesssim_k \varepsilon\|\mathbf{A}\|$ (its formalization: $3000k^3$);
[Paige1980, (3.11)–(3.13)].
Result: paige-loss-of-orthogonality -/
theorem abs_basis_mulVec_dotProduct_mul_abs_le {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    |(L.basis *ᵥ y) ⬝ᵥ (L.β k • L.v (k + 1))| * |y L.lastIndex| ≤
      30 * k ^ 2 * L.ε * specNorm L.H := by
  have hq : y ⬝ᵥ (L.gramCommutator *ᵥ y) =
      -((L.basis *ᵥ y) ⬝ᵥ (L.β k • L.v (k + 1)) * y L.lastIndex) := by
    have h1 : y ⬝ᵥ (L.tridiagonal *ᵥ (L.gramStrictUpper *ᵥ y)) =
        θ * (y ⬝ᵥ (L.gramStrictUpper *ᵥ y)) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, L.transpose_tridiagonal, hy,
        smul_dotProduct, smul_eq_mul]
    have h2 : y ⬝ᵥ (L.basisᵀ *ᵥ L.v (k + 1)) = (L.basis *ᵥ y) ⬝ᵥ L.v (k + 1) := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    simp only [gramCommutator, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, dotProduct_sub, h1, hy,
      Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Matrix.vecMulVec_mulVec,
      single_one_dotProduct, op_smul_eq_smul, h2]
    ring
  have hb : |y ⬝ᵥ (L.gramCommutator *ᵥ y)| ≤ specNorm L.gramCommutator := by
    have h := norm_star_dotProduct_mulVec_le L.gramCommutator y y
    rwa [star_trivial, Real.norm_eq_abs, hy1, one_mul, mul_one] at h
  rw [← abs_mul, ← abs_neg, ← hq]
  exact hb.trans L.specNorm_gramCommutator_le

end LanczosRun

end NLAlib
