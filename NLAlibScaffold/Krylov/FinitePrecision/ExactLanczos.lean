/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# Exact Lanczos from an orthonormal three-term recurrence

If orthonormal vectors $\mathbf{u}_1, \dots, \mathbf{u}_{k+1}$ satisfy a three-term recurrence
$\mathbf{A}\mathbf{u}_{j+1} = \beta_j\mathbf{u}_j + \alpha_{j+1}\mathbf{u}_{j+1}
+ \beta_{j+1}\mathbf{u}_{j+2}$ with $\beta_j > 0$ before the last step, then the Lanczos
recurrence `NLAlib.lanczosState` from $\mathbf{u}_1$ reproduces them and the coefficients. Used to
read the backward model of finite-precision Lanczos as exact Lanczos; it belongs with
`NLAlib/Krylov/Processes/LanczosRecurrence.lean`.

## Main results

* `NLAlib.lanczosState_eq_of_orthonormal_recurrence`,
  `NLAlib.lanczosState_beta_eq_of_orthonormal_recurrence`.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-! ### Exact Lanczos from an orthonormal three-term recurrence -/

/-- One step of the Lanczos recurrence on an orthonormal three-term recurrence: from the state
$(\mathbf{u}_j, \mathbf{u}_{j+1}, \beta_j)$ the coefficient is $\alpha_{j+1}$ and the step
produces $\beta_{j+1}$ and the vector $\beta_{j+1}^{-1}(\beta_{j+1}\mathbf{u}_{j+2})$. -/
theorem lanczosStep_of_orthonormal_recurrence {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {u : ℕ → ι → ℝ} {α β : ℕ → ℝ} {k : ℕ}
    (horth : ∀ i j, 1 ≤ i → i ≤ k + 1 → 1 ≤ j → j ≤ k + 1 →
      u i ⬝ᵥ u j = if i = j then 1 else 0)
    (hrec : ∀ j < k, A *ᵥ u (j + 1) = β j • u j + α (j + 1) • u (j + 1) + β (j + 1) • u (j + 2))
    (hβ : ∀ j ≤ k, 0 ≤ β j) {j : ℕ} (hj : j < k) :
    lanczosAlpha A ⟨u j, u (j + 1), β j⟩ = α (j + 1) ∧
      lanczosStep A ⟨u j, u (j + 1), β j⟩ =
        ⟨u (j + 1), (β (j + 1))⁻¹ • (β (j + 1) • u (j + 2)), β (j + 1)⟩ := by
  have h11 := horth (j + 1) (j + 1) (by omega) (by omega) (by omega) (by omega)
  have h12 := horth (j + 1) (j + 2) (by omega) (by omega) (by omega) (by omega)
  rw [if_pos rfl] at h11
  rw [if_neg (by omega)] at h12
  have hα : lanczosAlpha A ⟨u j, u (j + 1), β j⟩ = α (j + 1) := by
    simp only [lanczosAlpha, RCLike.ofReal_real_eq_id, id, star_trivial, RCLike.re_to_real]
    have hrec' : A *ᵥ u (j + 1) - β j • u j = α (j + 1) • u (j + 1) + β (j + 1) • u (j + 2) := by
      rw [hrec j hj]
      abel
    rw [hrec']
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, h11, h12]
    ring
  refine ⟨hα, ?_⟩
  have hw : A *ᵥ u (j + 1) - β j • u j - α (j + 1) • u (j + 1) = β (j + 1) • u (j + 2) := by
    rw [hrec j hj]
    abel
  have hn : ‖WithLp.toLp 2 (u (j + 2))‖ = 1 := by
    have h22 := horth (j + 2) (j + 2) (by omega) (by omega) (by omega) (by omega)
    rw [if_pos rfl, ← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self] at h22
    have := norm_nonneg (WithLp.toLp 2 (u (j + 2)))
    nlinarith
  have hnw : ‖WithLp.toLp 2 (β (j + 1) • u (j + 2))‖ = β (j + 1) := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hβ (j + 1) (by omega)), hn,
      mul_one]
  simp only [lanczosStep, hα, RCLike.ofReal_real_eq_id, id, hw, hnw]

/-- **An orthonormal three-term recurrence is the Lanczos recurrence**: if
$\mathbf{u}_0 = \mathbf{0}$, $\mathbf{u}_1, \dots, \mathbf{u}_{k+1}$ are orthonormal,
$\mathbf{A}\mathbf{u}_{j+1} = \beta_j\mathbf{u}_j + \alpha_{j+1}\mathbf{u}_{j+1}
+ \beta_{j+1}\mathbf{u}_{j+2}$ for $j < k$, $\beta_0 = 0$, $\beta_j > 0$ for $1 \le j < k$ and
$\beta_k \ge 0$, then the Lanczos recurrence from $\mathbf{u}_1$ has state
$(\mathbf{u}_j, \mathbf{u}_{j+1}, \beta_j)$ before step $j < k$. No symmetry of $\mathbf{A}$ is
needed. [Saad2011, §6.6] for the exact recurrence. -/
theorem lanczosState_eq_of_orthonormal_recurrence {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {u : ℕ → ι → ℝ} {α β : ℕ → ℝ} {k : ℕ} (hu0 : u 0 = 0)
    (horth : ∀ i j, 1 ≤ i → i ≤ k + 1 → 1 ≤ j → j ≤ k + 1 →
      u i ⬝ᵥ u j = if i = j then 1 else 0)
    (hrec : ∀ j < k, A *ᵥ u (j + 1) = β j • u j + α (j + 1) • u (j + 1) + β (j + 1) • u (j + 2))
    (hβ0 : β 0 = 0) (hβ : ∀ j ≤ k, 0 ≤ β j) (hβpos : ∀ j, 1 ≤ j → j < k → 0 < β j) :
    ∀ j < k, lanczosState A (u 1) j = ⟨u j, u (j + 1), β j⟩ := by
  intro j hj
  induction j with
  | zero =>
    have h1 := horth 1 1 le_rfl (by omega) le_rfl (by omega)
    rw [if_pos rfl, ← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self] at h1
    have hn : ‖WithLp.toLp 2 (u 1)‖ = 1 := by
      have := norm_nonneg (WithLp.toLp 2 (u 1))
      nlinarith
    simp only [lanczosState, hn, RCLike.ofReal_real_eq_id, id, inv_one, one_smul, hu0, hβ0]
  | succ j ih =>
    rw [show lanczosState A (u 1) (j + 1) = lanczosStep A (lanczosState A (u 1) j) from rfl,
      ih (by omega), (lanczosStep_of_orthonormal_recurrence horth hrec hβ (by omega)).2,
      smul_smul, inv_mul_cancel₀ (hβpos (j + 1) (by omega) hj).ne', one_smul]

/-- Under the hypotheses of `NLAlib.lanczosState_eq_of_orthonormal_recurrence` the coefficient of
the Lanczos state after $k$ steps is $\beta_k$: with $\mathbf{u}_0 = \mathbf{0}$,
$\mathbf{u}_1, \dots, \mathbf{u}_{k+1}$ orthonormal, $\mathbf{A}\mathbf{u}_{j+1} =
\beta_j\mathbf{u}_j + \alpha_{j+1}\mathbf{u}_{j+1} + \beta_{j+1}\mathbf{u}_{j+2}$ for $j < k$,
$\beta_0 = 0$, $\beta_j > 0$ for $1 \le j < k$ and $\beta_k \ge 0$. -/
theorem lanczosState_beta_eq_of_orthonormal_recurrence {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {u : ℕ → ι → ℝ} {α β : ℕ → ℝ} {k : ℕ} (hu0 : u 0 = 0)
    (horth : ∀ i j, 1 ≤ i → i ≤ k + 1 → 1 ≤ j → j ≤ k + 1 →
      u i ⬝ᵥ u j = if i = j then 1 else 0)
    (hrec : ∀ j < k, A *ᵥ u (j + 1) = β j • u j + α (j + 1) • u (j + 1) + β (j + 1) • u (j + 2))
    (hβ0 : β 0 = 0) (hβ : ∀ j ≤ k, 0 ≤ β j) (hβpos : ∀ j, 1 ≤ j → j < k → 0 < β j) :
    (lanczosState A (u 1) k).beta = β k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [hβ0]
    rfl
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [show lanczosState A (u 1) (m + 1) = lanczosStep A (lanczosState A (u 1) m) from rfl,
    lanczosState_eq_of_orthonormal_recurrence hu0 horth hrec hβ0 hβ hβpos m (by omega),
    (lanczosStep_of_orthonormal_recurrence horth hrec hβ (by omega)).2]

end NLAlib
