/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.CGBackward
public import NLAlibScaffold.Krylov.LinearSystems.CGStep

/-!
# The run of the conjugate gradient program in the standard model

A run of `NLAlib.cgProgWith` under `NLAlib.Computation.IsRelErrSem`, for any product `mv` that
meets `NLAlib.LanczosMvSpec`, on a symmetric $\mathbf{A}$ with spectrum in $[a, a']$, $a > 0$,
under the smallness hypothesis $q^3\varepsilon\kappa^2 \le 10^{-5}$, succeeds, and its outputs
are those of computed sequences meeting the clauses of `NLAlib.CGRun` up to the step $k$ where
the computed $\nu_k$ is $0$ (`NLAlib.CGRunFacts`). The loop invariant (`NLAlib.CGLoopInv`) carries
the sequences of the steps taken so far (`NLAlib.CGSeq`, `NLAlib.CGSeq.Valid`); before each
step it is packaged as a `NLAlib.CGRun` of the prefix, whose a priori certificates
(`NLAlib.CGRun.norm_p_sq_le`, `NLAlib.CGRun.specNorm_mul_γ_mul_norm_p_sq_le`) and
`NLAlib.CGRun.norm_r_le_two_mul_norm_p` give $\mathbf{p}_k \ne \mathbf{0}$, so that the computed
curvature is positive (`NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc`) and the division by
it succeeds: the induction over the iterations is interleaved with the analysis of the prefix.
Helper file of `NLAlibScaffold/Krylov/LinearSystems/CGRounding.lean`.

Research branch `research/hscg-fp`. Design: `docs/design/research/Krylov-CGRounding.md` (§1.3).

## Main definitions

* `NLAlib.CGSeq`, `NLAlib.CGSeq.Valid`, `NLAlib.CGSeq.Valid.toCGRun`, `NLAlib.CGSeq.extend`.
* `NLAlib.CGLoopInv`, `NLAlib.CGRunFacts`.

## Main results

* `NLAlib.CGSeq.Valid.pos_curvature`: the next curvature is positive.
* `NLAlib.Computation.IsRelErrSem.exists_cgRunFacts_of_cgProgWith`: the run.
-/

@[expose] public section

open Finset
open scoped Matrix

namespace NLAlib

open Computation Builder

/-- **The computed sequences of a conjugate gradient run**, indexed as `NLAlib.CGRun`. -/
structure CGSeq (n : ℕ) where
  /-- The iterates. -/
  x : ℕ → Fin n → ℝ
  /-- The residuals. -/
  r : ℕ → Fin n → ℝ
  /-- The directions. -/
  p : ℕ → Fin n → ℝ
  /-- The products. -/
  s : ℕ → Fin n → ℝ
  /-- The squared residual norms. -/
  ν : ℕ → ℝ
  /-- The curvatures. -/
  μ : ℕ → ℝ
  /-- The step lengths. -/
  γ : ℕ → ℝ
  /-- The direction coefficients. -/
  δ : ℕ → ℝ
  /-- The product errors. -/
  es : ℕ → Fin n → ℝ
  /-- The relative errors of the squared residual norms. -/
  θ : ℕ → ℝ
  /-- The curvature errors. -/
  eμ : ℕ → ℝ
  /-- The relative errors of the step lengths. -/
  eγ : ℕ → ℝ
  /-- The iterate update errors. -/
  ex : ℕ → Fin n → ℝ
  /-- The residual update errors. -/
  er : ℕ → Fin n → ℝ
  /-- The relative errors of the coefficients. -/
  eδ : ℕ → ℝ
  /-- The direction update errors. -/
  ep : ℕ → Fin n → ℝ

namespace CGSeq

variable {n : ℕ} (T : CGSeq n)

/-- The data of step $j$ of the sequences. -/
def stepData (j : ℕ) : CGStepData n :=
  ⟨T.s j, T.es j, T.μ j, T.eμ j, T.γ j, T.eγ j, T.x (j + 1), T.ex j, T.r (j + 1), T.er j,
    T.ν (j + 1), T.θ (j + 1), T.δ j, T.eδ j, T.p (j + 1), T.ep j⟩

/-- **The sequences of $k$ steps taken**: the start $\mathbf{x}_0 = \mathbf{0}$,
$\mathbf{r}_0 = \mathbf{p}_0 = \mathbf{b}$, $\nu_0$ with its relative error, $\nu_j > 0$ and the
local errors of every step $j < k$. -/
structure Valid (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (ε : ℝ) (k : ℕ) : Prop where
  /-- $\mathbf{x}_0 = \mathbf{0}$. -/
  x_zero : T.x 0 = 0
  /-- $\mathbf{r}_0 = \mathbf{b}$. -/
  r_zero : T.r 0 = b
  /-- $\mathbf{p}_0 = \mathbf{b}$. -/
  p_zero : T.p 0 = b
  /-- The first squared residual norm. -/
  ν_zero : T.ν 0 = ‖WithLp.toLp 2 b‖ ^ 2 * (1 + T.θ 0)
  /-- Its relative error. -/
  abs_θ_zero : |T.θ 0| ≤ ε
  /-- No stop before step $k$. -/
  ν_pos : ∀ j < k, 0 < T.ν j
  /-- The local errors of the steps taken. -/
  step : ∀ j < k, (T.stepData j).IsStep A ε (T.x j) (T.r j) (T.p j) (T.ν j)

variable {T} {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {ε : ℝ} {k : ℕ}

theorem Valid.ν_eq (hv : T.Valid A b ε k) {j : ℕ} (hj : j ≤ k) :
    T.ν j = ‖WithLp.toLp 2 (T.r j)‖ ^ 2 * (1 + T.θ j) := by
  rcases j with _ | j
  · rw [hv.ν_zero, hv.r_zero]
  · exact (hv.step j (by omega)).ν_eq

theorem Valid.abs_θ_le (hv : T.Valid A b ε k) {j : ℕ} (hj : j ≤ k) : |T.θ j| ≤ ε := by
  rcases j with _ | j
  · exact hv.abs_θ_zero
  · exact (hv.step j (by omega)).abs_θ_le

/-- The squared residual norm vanishes only with the residual, for $\varepsilon < 1$. -/
theorem Valid.r_eq_zero_of_ν_eq_zero (hv : T.Valid A b ε k) (hε : ε < 1) {j : ℕ} (hj : j ≤ k)
    (h0 : T.ν j = 0) : T.r j = 0 := by
  have h1 : 0 < 1 + T.θ j := by have := (abs_le.mp (hv.abs_θ_le hj)).1; linarith
  rw [hv.ν_eq hj] at h0
  have h2 : ‖WithLp.toLp 2 (T.r j)‖ = 0 := by
    have := (mul_eq_zero.mp h0).resolve_right h1.ne'
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have h3 := congrArg WithLp.ofLp (norm_eq_zero.mp h2)
  simpa using h3

/-- A nonzero squared residual norm is positive, for $\varepsilon < 1$. -/
theorem Valid.ν_pos_of_ne_zero (hv : T.Valid A b ε k) (hε : ε < 1) {j : ℕ} (hj : j ≤ k)
    (h0 : T.ν j ≠ 0) : 0 < T.ν j := by
  have h1 : 0 < 1 + T.θ j := by have := (abs_le.mp (hv.abs_θ_le hj)).1; linarith
  rw [hv.ν_eq hj] at h0 ⊢
  exact lt_of_le_of_ne (mul_nonneg (sq_nonneg _) h1.le) (Ne.symm h0)

/-- **The sequences of $k \ge 1$ steps as a `NLAlib.CGRun`**. -/
noncomputable def Valid.toCGRun (hv : T.Valid A b ε k) (hA : Aᵀ = A) (hε : 0 ≤ ε) (hk : 0 < k)
    (hkε : (k : ℝ) * ε ≤ 1 / 100) : CGRun n k where
  A := A
  b := b
  x := T.x
  r := T.r
  p := T.p
  s := T.s
  ν := T.ν
  μ := T.μ
  γ := T.γ
  δ := T.δ
  es := T.es
  θ := T.θ
  eμ := T.eμ
  eγ := T.eγ
  ex := T.ex
  er := T.er
  eδ := T.eδ
  ep := T.ep
  ε := ε
  transpose_A := hA
  ε_nonneg := hε
  k_pos := hk
  k_mul_ε_le := hkε
  x_zero := hv.x_zero
  r_zero := hv.r_zero
  p_zero := hv.p_zero
  ν_eq := fun _ hj => hv.ν_eq hj
  abs_θ_le := fun _ hj => hv.abs_θ_le hj
  ν_pos := hv.ν_pos
  s_eq := fun j hj => (hv.step j hj).s_eq
  norm_es_le := fun j hj => (hv.step j hj).norm_es_le
  μ_eq := fun j hj => (hv.step j hj).μ_eq
  abs_eμ_le := fun j hj => (hv.step j hj).abs_eμ_le
  μ_pos := fun j hj => (hv.step j hj).μ_pos
  γ_eq := fun j hj => (hv.step j hj).γ_eq
  abs_eγ_le := fun j hj => (hv.step j hj).abs_eγ_le
  x_succ := fun j hj => (hv.step j hj).x_succ
  norm_ex_le := fun j hj => (hv.step j hj).norm_ex_le
  r_succ := fun j hj => (hv.step j hj).r_succ
  norm_er_le := fun j hj => (hv.step j hj).norm_er_le
  δ_eq := fun j hj => (hv.step j hj).δ_eq
  abs_eδ_le := fun j hj => (hv.step j hj).abs_eδ_le
  p_succ := fun j hj => (hv.step j hj).p_succ
  norm_ep_le := fun j hj => (hv.step j hj).norm_ep_le

variable (T) in
/-- **The sequences extended by one step** $D$ at index $k$. -/
def extend (k : ℕ) (D : CGStepData n) : CGSeq n where
  x := Function.update T.x (k + 1) D.x
  r := Function.update T.r (k + 1) D.r
  p := Function.update T.p (k + 1) D.p
  s := Function.update T.s k D.s
  ν := Function.update T.ν (k + 1) D.ν
  μ := Function.update T.μ k D.μ
  γ := Function.update T.γ k D.γ
  δ := Function.update T.δ k D.δ
  es := Function.update T.es k D.es
  θ := Function.update T.θ (k + 1) D.θ
  eμ := Function.update T.eμ k D.eμ
  eγ := Function.update T.eγ k D.eγ
  ex := Function.update T.ex k D.ex
  er := Function.update T.er k D.er
  eδ := Function.update T.eδ k D.eδ
  ep := Function.update T.ep k D.ep

variable {D : CGStepData n}

theorem extend_stepData_of_lt {j : ℕ} (hj : j < k) :
    (T.extend k D).stepData j = T.stepData j := by
  simp only [stepData, extend, Function.update_of_ne (show j ≠ k by omega),
    Function.update_of_ne (show j + 1 ≠ k + 1 by omega)]

theorem extend_stepData_self : (T.extend k D).stepData k = D := by
  simp only [stepData, extend, Function.update_self]

theorem extend_x_of_le {j : ℕ} (hj : j ≤ k) : (T.extend k D).x j = T.x j :=
  Function.update_of_ne (by omega) _ _

theorem extend_r_of_le {j : ℕ} (hj : j ≤ k) : (T.extend k D).r j = T.r j :=
  Function.update_of_ne (by omega) _ _

theorem extend_p_of_le {j : ℕ} (hj : j ≤ k) : (T.extend k D).p j = T.p j :=
  Function.update_of_ne (by omega) _ _

theorem extend_ν_of_le {j : ℕ} (hj : j ≤ k) : (T.extend k D).ν j = T.ν j :=
  Function.update_of_ne (by omega) _ _

theorem extend_θ_of_le {j : ℕ} (hj : j ≤ k) : (T.extend k D).θ j = T.θ j :=
  Function.update_of_ne (by omega) _ _

theorem extend_γ_of_lt {j : ℕ} (hj : j < k) : (T.extend k D).γ j = T.γ j :=
  Function.update_of_ne (by omega) _ _

theorem extend_δ_of_lt {j : ℕ} (hj : j < k) : (T.extend k D).δ j = T.δ j :=
  Function.update_of_ne (by omega) _ _

/-- **One more step keeps the sequences valid.** -/
theorem Valid.extend (hv : T.Valid A b ε k)
    (hD : D.IsStep A ε (T.x k) (T.r k) (T.p k) (T.ν k)) (hνk : 0 < T.ν k) :
    (T.extend k D).Valid A b ε (k + 1) where
  x_zero := by rw [extend_x_of_le (Nat.zero_le _)]; exact hv.x_zero
  r_zero := by rw [extend_r_of_le (Nat.zero_le _)]; exact hv.r_zero
  p_zero := by rw [extend_p_of_le (Nat.zero_le _)]; exact hv.p_zero
  ν_zero := by
    rw [extend_ν_of_le (Nat.zero_le _)]
    rw [extend_θ_of_le (Nat.zero_le _)]
    exact hv.ν_zero
  abs_θ_zero := by
    rw [extend_θ_of_le (Nat.zero_le _)]
    exact hv.abs_θ_zero
  ν_pos := fun j hj => by
    rw [extend_ν_of_le (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hv.ν_pos j hj
    · exact hνk
  step := fun j hj => by
    rw [extend_x_of_le (by omega), extend_r_of_le (by omega), extend_p_of_le (by omega),
      extend_ν_of_le (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [extend_stepData_of_lt hj]; exact hv.step j hj
    · rw [extend_stepData_self]; exact hD

end CGSeq

/-! ### The next curvature is positive -/

/-- A real symmetric matrix of positive size with spectrum in $[a, a']$ has $a \le a'$. -/
theorem le_of_spectrum_subset_Icc {N : ℕ} (hN : 0 < N) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : Aᵀ = A) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') : a ≤ a' := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA
  have := hs (hH.eigenvalues_mem_spectrum_real ⟨0, hN⟩)
  exact this.1.trans this.2

/-- **The next curvature is positive**: for valid sequences of $k$ steps with $\nu_k \ne 0$,
on a symmetric $\mathbf{A}$ with spectrum in $[a, a']$, $a > 0$, $\kappa = a'/a \ge 1$,
$k^3\varepsilon\kappa^2 \le 10^{-5}$, $k\varepsilon \le 1/100$, $3\varepsilon a' \le a$ and
$20k\varepsilon(1 + 2\kappa + 1.05\kappa) \le 1$, a computed curvature of $\mathbf{p}_k$ in the
standard model is positive. For $k = 0$, $\mathbf{p}_0 = \mathbf{b} \ne \mathbf{0}$; for
$k \ge 1$, the a priori certificates of the prefix run and
`NLAlib.CGRun.norm_r_le_two_mul_norm_p` give $\|\mathbf{r}_k\| \le 2\|\mathbf{p}_k\|$. -/
theorem CGSeq.Valid.pos_curvature {N : ℕ} {T : CGSeq N} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {ε : ℝ} {k : ℕ} (hv : T.Valid A b ε k) (hA : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (hκ : a ≤ a') (hε : 0 ≤ ε)
    (hsmall : (k : ℝ) ^ 3 * ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) (hkε : (k : ℝ) * ε ≤ 1 / 100)
    (h3 : 3 * ε * a' ≤ a) (h20 : 20 * k * ε * (1 + 2 * (a' / a) + 21 / 20 * (a' / a)) ≤ 1)
    (hb : b ≠ 0) (hν : T.ν k ≠ 0) (es : Fin N → ℝ) (eμ : ℝ)
    (hes : ‖WithLp.toLp 2 es‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 (T.p k)‖)
    (heμ : |eμ| ≤ ε * ‖WithLp.toLp 2 (T.p k)‖ * ‖WithLp.toLp 2 (A *ᵥ T.p k + es)‖) :
    0 < T.p k ⬝ᵥ (A *ᵥ T.p k + es) + eμ := by
  refine dotProduct_add_pos_of_spectrum_subset_Icc hA ha hs hε h3 ?_ hes heμ
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [hv.p_zero]; exact hb
  have hε1 : ε < 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  set R := hv.toCGRun hA hε hk hkε
  have hκ1 : 1 ≤ a' / a := (one_le_div ha).mpr hκ
  have hP : ∀ j < k, ‖WithLp.toLp 2 (R.p j)‖ ≤ 2 * (a' / a) * R.ρ j := fun j hj => by
    have h1 := R.norm_p_sq_le ha hs hsmall hj
    have hρ : 0 ≤ R.ρ j := norm_nonneg _
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (two_ne_zero)).mp ?_
    nlinarith [sq_nonneg (R.ρ j)]
  have hK := fun j (hj : j < k) => R.specNorm_mul_γ_mul_norm_p_sq_le ha hs hsmall hj
  have h2 := R.norm_r_le_two_mul_norm_p hP hK h20
  intro hp0
  have hr0 : T.r k ≠ 0 := fun hr => hν (by rw [hv.ν_eq le_rfl, hr]; simp)
  have : R.ρ k ≤ 0 := by
    have hp : ‖WithLp.toLp 2 (R.p k)‖ = 0 := by
      show ‖WithLp.toLp 2 (T.p k)‖ = 0
      rw [hp0]; simp
    linarith
  have hρ0 : R.ρ k = 0 := le_antisymm this (norm_nonneg _)
  have h3 : WithLp.toLp 2 (T.r k) = 0 := norm_eq_zero.mp hρ0
  exact hr0 (by simpa using congrArg WithLp.ofLp h3)

end NLAlib
