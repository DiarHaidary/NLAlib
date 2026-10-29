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

/-! ### The start and the loop -/

section Run

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C) {p : P}
  {u : P → ℝ} {dec : P → K → ℝ}

/-- A cell or a slot outside the blocks of a frame, by arithmetic on the indices. -/
local macro "cg_nb" : tactic => `(tactic| (intro hb; simp only [StoreBlock, IExp.eval_ofNat,
  IExp.eval_const, IExp.eval_zero, IExp.eval_add, IExp.eval_mul, IExp.eval_var] at hb; omega))

/-- **The start of the CG program** in the standard model: `s[3] ← 0`, slot $0$ ←
$\mathbf{0}$, slots $N$ and $3N$ ← $\mathbf{b}$, $\nu_0 = \mathrm{fl}(\mathbf{b}^{\mathsf{T}}
\mathbf{b})$ into `s[0]` and `nu[0]`. -/
theorem exec_cg_init (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hu1 : u p < 1) (st : St P K C)
    {S : Array (P × ℕ)} (hsh : st.store.shape = S) {B W sb Nu Ln : ℕ} {bv : Fin N → ℝ}
    (hb : DecVec st.store p dec B 0 bv) (hBW : B ≠ W) (hBs : B ≠ sb) (hWs : W ≠ sb)
    (hNW : Nu ≠ W) (hNs : Nu ≠ sb) (hSW : S[W]? = some (p, 5 * N)) (hS : S[sb]? = some (p, 7))
    (hSN : S[Nu]? = some (p, Ln)) (hLn : 0 < Ln) :
    ∃ (st' : St P K C) (ν θ : ℝ), (∀ f, exec I (ins (.lit p ⟨sb, 3⟩ 0) >>=
        fun _ => forRange (.const N) (fun i => ins (.lit p ⟨W, IExp.var i⟩ 0)) >>=
        fun _ => copyv p B 0 W (.const N) (.const N) >>=
        fun _ => copyv p B 0 W (3 * IExp.const N) (.const N) >>=
        fun _ => dot p ⟨sb, 0⟩ B 0 B 0 (.const N) >>=
        fun _ => ins (.copy p ⟨Nu, 0⟩ ⟨sb, 0⟩) >>= f).run st = exec I (f ()).run st') ∧
      StoreFrame p st.store st'.store (fun b i => StoreBlock W 0 (5 * N) b i ∨
        StoreBlock sb 0 7 b i ∨ StoreBlock Nu 0 1 b i) ∧
      DecVec st'.store p dec W 0 (0 : Fin N → ℝ) ∧ DecVec st'.store p dec W N bv ∧
      DecVec st'.store p dec W (3 * N) bv ∧ DecCell st'.store p dec sb 0 ν ∧
      DecCell st'.store p dec sb 3 0 ∧ DecCell st'.store p dec Nu 0 ν ∧
      IsRoundingProduct (u p) N θ ∧ ν = ‖WithLp.toLp 2 bv‖ ^ 2 * (1 + θ) := by
  obtain ⟨st₁, h₁, hf₁, h3₁⟩ := exec_lit_zero_decCell I h st hsh ⟨sb, 3⟩ hS (by norm_num)
  obtain ⟨z0, hz0⟩ := h.lit_ok p 0 trivial
  have hdz0 : dec p z0 = 0 := by
    obtain ⟨δ, -, hδ⟩ := h.lit_err p 0 z0 hz0
    simpa using hδ
  obtain ⟨st₂, h₂, hf₂, hc₂⟩ := exec_loop_write I st₁ (p := p) (dec := dec) (Y := W)
    (off := 0) (n := N) (fun _ => 0) (body := fun i => (ins (.lit p ⟨W, IExp.var i⟩ 0)).run)
    fun i hi st' hf => by
      obtain ⟨s', hs'⟩ := exists_write_of_shape ((hf.1.trans hf₁.1).trans hsh) hSW
        (by omega : i < 5 * N) z0
      have hs'' : st'.store.write p W (IExp.eval (IExp.var i)) z0 = some s' := hs'
      exact ⟨_, z0, (exec_seq_instr_lit I (dst := ⟨W, IExp.var i⟩) (t := .skip) (st := st')
        hz0 hs'').trans (exec_skip I _), by rw [zero_add]; exact hs', hdz0⟩
  have hf₁₂ := hf₁.trans hf₂
  have hb₂ : DecVec st₂.store p dec B (IExp.eval 0) bv := hb.frame hf₁₂ fun i hi => by cg_nb
  obtain ⟨st₃, h₃, hf₃, hr₃⟩ := exec_copyv_decVec I st₂ (hf₁₂.1.trans hsh) B 0 W (.const N) hb₂
    hSW (by simp; omega) fun h' => absurd h' hBW
  obtain ⟨st₄, h₄, hf₄, hp₄⟩ := exec_copyv_decVec I st₃ ((hf₁₂.trans hf₃).1.trans hsh) B 0 W
    (3 * IExp.const N) (hb₂.frame hf₃ fun i hi => by cg_nb) hSW (by simp; omega)
    fun h' => absurd h' hBW
  have hf₁₄ := (hf₁₂.trans hf₃).trans hf₄
  obtain ⟨st₅, ν, θ, h₅, hf₅, hν₅, hθ, hν⟩ := exec_dot_self_decCell I h hz hu1 st₄
    (hf₁₄.1.trans hsh) ⟨sb, 0⟩ (X := B) 0 hBs.symm hS (by norm_num)
    ((hb₂.frame hf₃ fun i hi => by cg_nb).frame hf₄ fun i hi => by cg_nb)
  obtain ⟨st₆, h₆, hf₆, hν₆⟩ := exec_copy_decCell I st₅ ((hf₁₄.trans hf₅).1.trans hsh)
    ⟨Nu, 0⟩ ⟨sb, 0⟩ hSN hLn hν₅
  refine ⟨st₆, ν, θ, fun f => ?_, ?_, fun i => ?_,
    (((hr₃.frame hf₄ fun i hi => by cg_nb).frame hf₅ fun i hi => by cg_nb).frame hf₆
      fun i hi => by cg_nb),
    ((hp₄.frame hf₅ fun i hi => by cg_nb).frame hf₆ fun i hi => by cg_nb),
    hν₅.frame hf₆ (by cg_nb),
    (((h3₁.frame hf₂ (by cg_nb)).frame hf₃ (by cg_nb)).frame hf₄ (by cg_nb) |>.frame hf₅
      (by cg_nb)).frame hf₆ (by cg_nb), hν₆, hθ, hν⟩
  · rw [exec_bind_of_exec_eq_some I h₁ (seqShape_ins _),
      exec_bind_of_exec_eq_some I (b := forRange _ _) ((exec_seq_skip I _ _).trans h₂)
        (seqShape_forRange _ _),
      exec_bind_of_exec_eq_some I h₃ (seqShape_copyv _ _ _ _ _ _),
      exec_bind_of_exec_eq_some I h₄ (seqShape_copyv _ _ _ _ _ _),
      exec_bind_of_exec_eq_some I h₅ (seqShape_dot _ _ _ _ _ _ _),
      exec_bind_of_exec_eq_some I h₆ (seqShape_ins _)]
  · refine (hf₁₄.trans (hf₅.trans hf₆)).mono fun b i hb => ?_
    simp only [StoreBlock, IExp.eval_ofNat, IExp.eval_const, IExp.eval_mul] at hb ⊢
    rcases hb with (((hb | hb) | hb) | hb) | hb | hb
    · exact Or.inr (Or.inl ⟨hb.1, by omega, by omega⟩)
    · exact Or.inl ⟨hb.1, by omega, by omega⟩
    · exact Or.inl ⟨hb.1, by omega, by omega⟩
    · exact Or.inl ⟨hb.1, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨hb.1, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨hb.1, by omega, by omega⟩)
  · obtain ⟨w, hw, hd⟩ := (hc₂ i i.2)
    refine ⟨w, ?_, by rw [hd]; rfl⟩
    rw [hf₆.2 W _ (by cg_nb), hf₅.2 W _ (by cg_nb), hf₄.2 W (0 + i) (by cg_nb),
      hf₃.2 W (0 + i) (by cg_nb)]
    exact hw

/-- The region the CG program writes: the five slots, the scalars and the outputs. -/
def cgRegion (W sb G D Nu N q : ℕ) (b i : ℕ) : Prop :=
  StoreBlock W 0 (5 * N) b i ∨ StoreBlock sb 0 7 b i ∨ StoreBlock G 0 q b i ∨
    StoreBlock D 0 q b i ∨ StoreBlock Nu 0 (q + 1) b i

/-- **The loop invariant of the CG program** before iteration $j$: the store is in the frame of
the region of the program, and there are computed sequences of $k \le j$ steps taken
(`NLAlib.CGSeq.Valid`), with $\nu_k = 0$ if $k < j$ (the run stopped), the state of step $k$ in
the slots and scalars, and the outputs written: $\gamma_i, \delta_i$ ($i < k$), $\nu_i$
($i \le k$), and zeros for the skipped iterations $k \le i < j$. -/
def CGLoopInv (p : P) (dec : P → K → ℝ) (s₁ : Store P K) (W sb G D Nu q : ℕ) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (ε : ℝ) (bv : Fin N → ℝ) (j : ℕ) (s : Store P K) : Prop :=
  StoreFrame p s₁ s (cgRegion W sb G D Nu N q) ∧
  ∃ (k : ℕ) (T : CGSeq N), k ≤ j ∧ T.Valid A bv ε k ∧ (k < j → T.ν k = 0) ∧
    DecVec s p dec W 0 (T.x k) ∧ DecVec s p dec W N (T.r k) ∧
    (T.ν k ≠ 0 → DecVec s p dec W (3 * N + N * (k % 2)) (T.p k)) ∧
    DecCell s p dec sb 0 (T.ν k) ∧ DecCell s p dec sb 3 0 ∧
    (∀ i < k, DecCell s p dec G i (T.γ i) ∧ DecCell s p dec D i (T.δ i)) ∧
    (∀ i ≤ k, DecCell s p dec Nu i (T.ν i)) ∧
    ∀ i, k ≤ i → i < j →
      DecCell s p dec G i 0 ∧ DecCell s p dec D i 0 ∧ DecCell s p dec Nu (i + 1) 0

/-- **A skipped iteration** ($\nu_k = 0$) writes three zeros and keeps the invariant. -/
theorem cgLoopInv_skip (h : IsRelErrSem u dec (fun _ _ => True) I.sem) {s₁ : Store P K}
    {S : Array (P × ℕ)} (hS₁ : s₁.shape = S) {W sb G D Nu q N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {ε : ℝ} {bv : Fin N → ℝ} (hSG : S[G]? = some (p, q))
    (hSD : S[D]? = some (p, q)) (hSN : S[Nu]? = some (p, q + 1)) (hGW : G ≠ W) (hGs : G ≠ sb)
    (hDW : D ≠ W) (hDs : D ≠ sb) (hNW : Nu ≠ W) (hNs : Nu ≠ sb) (hGD : G ≠ D) (hGN : G ≠ Nu)
    (hDN : D ≠ Nu) {j : ℕ} (hj : j < q) (st : St P K C)
    (hf : StoreFrame p s₁ st.store (cgRegion W sb G D Nu N q)) {k : ℕ} {T : CGSeq N}
    (hkj : k ≤ j) (hv : T.Valid A bv ε k)
    (hx : DecVec st.store p dec W 0 (T.x k)) (hr : DecVec st.store p dec W N (T.r k))
    (hνc : DecCell st.store p dec sb 0 (T.ν k)) (h3 : DecCell st.store p dec sb 3 0)
    (hout : ∀ i < k, DecCell st.store p dec G i (T.γ i) ∧ DecCell st.store p dec D i (T.δ i))
    (hnu : ∀ i ≤ k, DecCell st.store p dec Nu i (T.ν i))
    (hzo : ∀ i, k ≤ i → i < j → DecCell st.store p dec G i 0 ∧ DecCell st.store p dec D i 0 ∧
      DecCell st.store p dec Nu (i + 1) 0) (hν0 : T.ν k = 0) :
    ∃ st' : St P K C, exec I (ins (.lit p ⟨G, IExp.var j⟩ 0) >>= fun _ =>
        ins (.lit p ⟨D, IExp.var j⟩ 0) >>= fun _ => ins (.lit p ⟨Nu, IExp.var j + 1⟩ 0)).run st =
        some st' ∧ CGLoopInv p dec s₁ W sb G D Nu q A ε bv (j + 1) st'.store := by
  have hsh := hf.1.trans hS₁
  obtain ⟨st₁, h₁, hf₁, hg₁⟩ := exec_lit_zero_decCell I h st hsh ⟨G, IExp.var j⟩ hSG hj
  obtain ⟨st₂, h₂, hf₂, hd₂⟩ := exec_lit_zero_decCell I h st₁ (hf₁.1.trans hsh) ⟨D, IExp.var j⟩
    hSD hj
  obtain ⟨st₃, h₃, hf₃, hn₃⟩ := exec_lit_zero_decCell I h st₂ ((hf₁.trans hf₂).1.trans hsh)
    ⟨Nu, IExp.var j + 1⟩ hSN (by simp; omega)
  replace hf₁ : StoreFrame p st.store st₁.store (StoreBlock G j 1) := hf₁
  replace hf₂ : StoreFrame p st₁.store st₂.store (StoreBlock D j 1) := hf₂
  replace hf₃ : StoreFrame p st₂.store st₃.store (StoreBlock Nu (j + 1) 1) := hf₃
  have hf' := (hf₁.trans hf₂).trans hf₃
  refine ⟨st₃, ?_, (hf.trans hf').mono fun b i hb => ?_, k, T, by omega, hv,
    fun _ => hν0, hx.frame hf' fun i hi => by cg_nb, hr.frame hf' fun i hi => by cg_nb,
    fun h' => absurd hν0 h', hνc.frame hf' (by cg_nb), h3.frame hf' (by cg_nb),
    fun i hi => ⟨(hout i hi).1.frame hf' (by cg_nb), (hout i hi).2.frame hf' (by cg_nb)⟩,
    fun i hi => (hnu i hi).frame hf' (by cg_nb), fun i hki hij => ?_⟩
  · rw [exec_bind_of_exec_eq_some I h₁ (seqShape_ins _),
      exec_bind_of_exec_eq_some I h₂ (seqShape_ins _)]
    exact h₃
  · rcases hb with hb | ((hb | hb) | hb)
    · exact hb
    · exact Or.inr (Or.inr (Or.inl ⟨hb.1, by omega, by have := hb.2.2; omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hb.1, by omega, by have := hb.2.2; omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hb.1, by omega, by have := hb.2.2; omega⟩)))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hij | rfl
    · obtain ⟨a1, a2, a3⟩ := hzo i hki hij
      exact ⟨a1.frame hf' (by cg_nb), a2.frame hf' (by cg_nb), a3.frame hf' (by cg_nb)⟩
    · exact ⟨(hg₁.frame hf₂ (by cg_nb)).frame hf₃ (by cg_nb), hd₂.frame hf₃ (by cg_nb), hn₃⟩

/-- **An iteration that takes a step** ($\nu_j \ne 0$, so $k = j$) keeps the invariant: the
a priori analysis of the prefix makes the curvature positive
(`NLAlib.CGSeq.Valid.pos_curvature`), then one step (`NLAlib.exec_cgStepWith`). -/
theorem cgLoopInv_step (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hu : ((N + 2 : ℕ) : ℝ) * u p < 1)
    {mv : ℕ → IExp ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit} {R : ℕ} {s₀ s₁ : Store P K}
    {A : Matrix (Fin N) (Fin N) ℝ} {c ε : ℝ} (hmv : LanczosMvSpec I mv p dec R s₀ A c)
    (hc : c ≤ ε * specNorm A) (hε : roundingFactor (N + 2) (u p) ≤ ε) (hA : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (hκ : a ≤ a') {q : ℕ}
    (hsm : ∀ m ≤ q, (m : ℝ) ^ 3 * ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hmε : ∀ m ≤ q, (m : ℝ) * ε ≤ 1 / 100) (h3a : 3 * ε * a' ≤ a)
    (h20 : ∀ m ≤ q, 20 * m * ε * (1 + 2 * (a' / a) + 21 / 20 * (a' / a)) ≤ 1)
    {bv : Fin N → ℝ} (hb0 : bv ≠ 0) {S : Array (P × ℕ)} (hS₁ : s₁.shape = S)
    (hR₁ : ∀ i, s₁.read p R i = s₀.read p R i) {W sb G D Nu : ℕ}
    (hSW : S[W]? = some (p, 5 * N)) (hS : S[sb]? = some (p, 7)) (hSG : S[G]? = some (p, q))
    (hSD : S[D]? = some (p, q)) (hSN : S[Nu]? = some (p, q + 1)) (hWs : W ≠ sb) (hGW : G ≠ W)
    (hGs : G ≠ sb) (hDW : D ≠ W) (hDs : D ≠ sb) (hNW : Nu ≠ W) (hNs : Nu ≠ sb) (hGD : G ≠ D)
    (hGN : G ≠ Nu) (hDN : D ≠ Nu) (hRW : R ≠ W) (hRs : R ≠ sb) (hRG : R ≠ G) (hRD : R ≠ D)
    (hRN : R ≠ Nu) {j : ℕ} (hj : j < q) (st : St P K C)
    (hf : StoreFrame p s₁ st.store (cgRegion W sb G D Nu N q)) {T : CGSeq N}
    (hv : T.Valid A bv ε j) (hx : DecVec st.store p dec W 0 (T.x j))
    (hr : DecVec st.store p dec W N (T.r j))
    (hp : DecVec st.store p dec W (3 * N + N * (j % 2)) (T.p j))
    (hνc : DecCell st.store p dec sb 0 (T.ν j)) (h3 : DecCell st.store p dec sb 3 0)
    (hout : ∀ i < j, DecCell st.store p dec G i (T.γ i) ∧ DecCell st.store p dec D i (T.δ i))
    (hnu : ∀ i ≤ j, DecCell st.store p dec Nu i (T.ν i)) (hν0 : T.ν j ≠ 0) :
    ∃ st' : St P K C, exec I (cgStepWith mv p (.const N) W
        (3 * IExp.const N + IExp.const N * (IExp.var j % 2))
        (3 * IExp.const N + IExp.const N * ((IExp.var j + 1) % 2)) sb ⟨G, IExp.var j⟩
        ⟨D, IExp.var j⟩ ⟨Nu, IExp.var j + 1⟩).run st = some st' ∧
      CGLoopInv p dec s₁ W sb G D Nu q A ε bv (j + 1) st'.store := by
  have hsh := hf.1.trans hS₁
  have hR : ∀ i, st.store.read p R i = s₀.read p R i := fun i =>
    (hf.2 R i fun hb => by
      rcases hb with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> contradiction).trans
      (hR₁ i)
  have hε0 : 0 ≤ ε := (roundingFactor_nonneg (h.nonneg trivial) hu).trans hε
  have hε1 : ε < 1 := by have := hmε 1 (by omega); simp at this; linarith
  have hm : (j % 2 = 0 ∧ (j + 1) % 2 = 1) ∨ (j % 2 = 1 ∧ (j + 1) % 2 = 0) := by omega
  have hpc : 3 * N ≤ 3 * N + N * (j % 2) ∧ 3 * N + N * (j % 2) + N ≤ 5 * N := by
    rcases hm with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> omega
  have hpn : 3 * N ≤ 3 * N + N * ((j + 1) % 2) ∧ 3 * N + N * ((j + 1) % 2) + N ≤ 5 * N := by
    rcases hm with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> omega
  have hcn : 3 * N + N * (j % 2) + N ≤ 3 * N + N * ((j + 1) % 2) ∨
      3 * N + N * ((j + 1) % 2) + N ≤ 3 * N + N * (j % 2) := by
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> omega
  have hpc' : 3 * N ≤ (3 * IExp.const N + IExp.const N * (IExp.var j % 2)).eval ∧
      (3 * IExp.const N + IExp.const N * (IExp.var j % 2)).eval + N ≤ 5 * N := hpc
  have hpn' : 3 * N ≤ (3 * IExp.const N + IExp.const N * ((IExp.var j + 1) % 2)).eval ∧
      (3 * IExp.const N + IExp.const N * ((IExp.var j + 1) % 2)).eval + N ≤ 5 * N := hpn
  have hcn' : (3 * IExp.const N + IExp.const N * (IExp.var j % 2)).eval + N ≤
        (3 * IExp.const N + IExp.const N * ((IExp.var j + 1) % 2)).eval ∨
      (3 * IExp.const N + IExp.const N * ((IExp.var j + 1) % 2)).eval + N ≤
        (3 * IExp.const N + IExp.const N * (IExp.var j % 2)).eval := hcn
  have hp'' : DecVec st.store p dec W (3 * IExp.const N + IExp.const N * (IExp.var j % 2)).eval
      (T.p j) := hp
  obtain ⟨st', Dd, he, hf', hx', hr', hp', hν', hg', hd', hn', hD⟩ := exec_cgStepWith I h hz hu
    hmv hc hε st hsh hR (3 * IExp.const N + IExp.const N * (IExp.var j % 2))
    (3 * IExp.const N + IExp.const N * ((IExp.var j + 1) % 2)) ⟨G, IExp.var j⟩ ⟨D, IExp.var j⟩
    ⟨Nu, IExp.var j + 1⟩ hWs hRW hS hSW hSG hj hSD hj hSN (by simp; omega) hGW hGs hDW hDs hNW
    hNs hGD hGN hDN hpc' hpn' hcn' hx hr hp'' hνc hν0
    (hv.pos_curvature hA ha hs hκ hε0 (hsm j hj.le) (hmε j hj.le) h3a (h20 j hj.le) hb0 hν0)
  replace hf' : StoreFrame p st.store st'.store (fun b i => StoreBlock W 0 (3 * N) b i ∨
      StoreBlock W (3 * N + N * ((j + 1) % 2)) N b i ∨ (b = sb ∧ i < 7 ∧ i ≠ 3) ∨
      StoreBlock G j 1 b i ∨ StoreBlock D j 1 b i ∨ StoreBlock Nu (j + 1) 1 b i) := hf'
  have hfr : ∀ b i, b ≠ W → (b = sb → i = 3) → (b = G → i ≠ j) → (b = D → i ≠ j) →
      (b = Nu → i ≠ j + 1) → st'.store.read p b i = st.store.read p b i :=
    fun b i h1 h2 h4 h5 h6 => hf'.2 b i fun hb => by
      rcases hb with hb | hb | ⟨hb, -, hb'⟩ | hb | hb | hb
      · exact h1 hb.1
      · exact h1 hb.1
      · exact hb' (h2 hb)
      · exact h4 hb.1 (by have := hb.2; omega)
      · exact h5 hb.1 (by have := hb.2; omega)
      · exact h6 hb.1 (by have := hb.2; omega)
  have hνj : 0 < T.ν j := hv.ν_pos_of_ne_zero hε1 le_rfl hν0
  refine ⟨st', he, (hf.trans hf').mono fun b i hb => ?_, j + 1, T.extend j Dd, le_rfl,
    hv.extend hD hνj, fun h' => absurd h' (lt_irrefl _), ?_, ?_, fun _ => ?_, ?_,
    ?_, fun i hi => ?_, fun i hi => ?_, fun i hi hi' => absurd hi' (by omega)⟩
  · rcases hb with hb | hb | hb | ⟨rfl, h1, h2⟩ | hb | hb | hb
    · exact hb
    · exact Or.inl ⟨hb.1, by omega, by have := hb.2.2; omega⟩
    · exact Or.inl ⟨hb.1, by omega, by have := hb.2.2; omega⟩
    · exact Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hb.1, by omega, by have := hb.2.2; omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hb.1, by omega, by have := hb.2.2; omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hb.1, by omega, by have := hb.2.2; omega⟩)))
  · change DecVec _ _ _ _ _ (Function.update T.x (j + 1) Dd.x (j + 1))
    rw [Function.update_self]; exact hx'
  · change DecVec _ _ _ _ _ (Function.update T.r (j + 1) Dd.r (j + 1))
    rw [Function.update_self]; exact hr'
  · change DecVec _ _ _ _ _ (Function.update T.p (j + 1) Dd.p (j + 1))
    rw [Function.update_self]; exact hp'
  · change DecCell _ _ _ _ _ (Function.update T.ν (j + 1) Dd.ν (j + 1))
    rw [Function.update_self]; exact hν'
  · obtain ⟨w, hw, hdw⟩ := h3
    exact ⟨w, by rw [hfr sb 3 hWs.symm (fun _ => rfl) (fun h' => absurd h'.symm hGs)
      (fun h' => absurd h'.symm hDs) (fun h' => absurd h'.symm hNs)]; exact hw, hdw⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [CGSeq.extend_γ_of_lt hi, CGSeq.extend_δ_of_lt hi]
      obtain ⟨⟨w₁, hw₁, hd₁⟩, ⟨w₂, hw₂, hd₂⟩⟩ := hout i hi
      refine ⟨⟨w₁, ?_, hd₁⟩, ⟨w₂, ?_, hd₂⟩⟩
      · rw [hfr G i hGW (fun h' => absurd h' hGs) (fun _ => by omega) (fun h' => absurd h' hGD)
          (fun h' => absurd h' hGN)]; exact hw₁
      · rw [hfr D i hDW (fun h' => absurd h' hDs) (fun h' => absurd h'.symm hGD)
          (fun _ => by omega) (fun h' => absurd h' hDN)]; exact hw₂
    · change DecCell _ _ _ _ _ (Function.update T.γ i Dd.γ i) ∧
        DecCell _ _ _ _ _ (Function.update T.δ i Dd.δ i)
      rw [Function.update_self, Function.update_self]; exact ⟨hg', hd'⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_iff.mpr hi) with hi | rfl
    · rw [CGSeq.extend_ν_of_le (Nat.lt_succ_iff.mp hi)]
      obtain ⟨w, hw, hdw⟩ := hnu i (Nat.lt_succ_iff.mp hi)
      refine ⟨w, ?_, hdw⟩
      rw [hfr Nu i hNW (fun h' => absurd h' hNs) (fun h' => absurd h'.symm hGN)
        (fun h' => absurd h'.symm hDN) (fun _ => by omega)]; exact hw
    · change DecCell _ _ _ _ _ (Function.update T.ν (j + 1) Dd.ν (j + 1))
      rw [Function.update_self]; exact hn'

omit [DecidableEq P] [AddMonoid C] in
theorem run_ifThenElse_eq_seq (c : CmpOp) (x y : Cell ℕ ℕ) (t e : Builder P ι ℕ ℕ Unit) :
    (ifThenElse p c x y t e).run = .seq (.ite p c x y t.run e.run) .skip := rfl

/-- **One iteration of the loop keeps the invariant**: the exact test $\nu_k = 0$, then the skip
(`NLAlib.cgLoopInv_skip`) or the step (`NLAlib.cgLoopInv_step`). -/
theorem CGLoopInv.succ (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hu : ((N + 2 : ℕ) : ℝ) * u p < 1)
    {mv : ℕ → IExp ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit} {R : ℕ} {s₀ s₁ : Store P K}
    {A : Matrix (Fin N) (Fin N) ℝ} {c ε : ℝ} (hmv : LanczosMvSpec I mv p dec R s₀ A c)
    (hc : c ≤ ε * specNorm A) (hε : roundingFactor (N + 2) (u p) ≤ ε) (hA : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (hκ : a ≤ a') {q : ℕ}
    (hsm : ∀ m ≤ q, (m : ℝ) ^ 3 * ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hmε : ∀ m ≤ q, (m : ℝ) * ε ≤ 1 / 100) (h3a : 3 * ε * a' ≤ a)
    (h20 : ∀ m ≤ q, 20 * m * ε * (1 + 2 * (a' / a) + 21 / 20 * (a' / a)) ≤ 1)
    {bv : Fin N → ℝ} (hb0 : bv ≠ 0) {S : Array (P × ℕ)} (hS₁ : s₁.shape = S)
    (hR₁ : ∀ i, s₁.read p R i = s₀.read p R i) {W sb G D Nu : ℕ}
    (hSW : S[W]? = some (p, 5 * N)) (hS : S[sb]? = some (p, 7)) (hSG : S[G]? = some (p, q))
    (hSD : S[D]? = some (p, q)) (hSN : S[Nu]? = some (p, q + 1)) (hWs : W ≠ sb) (hGW : G ≠ W)
    (hGs : G ≠ sb) (hDW : D ≠ W) (hDs : D ≠ sb) (hNW : Nu ≠ W) (hNs : Nu ≠ sb) (hGD : G ≠ D)
    (hGN : G ≠ Nu) (hDN : D ≠ Nu) (hRW : R ≠ W) (hRs : R ≠ sb) (hRG : R ≠ G) (hRD : R ≠ D)
    (hRN : R ≠ Nu) {j : ℕ} (hj : j < q) (st : St P K C)
    (hinv : CGLoopInv p dec s₁ W sb G D Nu q A ε bv j st.store) :
    ∃ st' : St P K C, exec I (ifThenElse p .eq ⟨sb, 0⟩ ⟨sb, 3⟩
        (ins (.lit p ⟨G, IExp.var j⟩ 0) >>= fun _ =>
          ins (.lit p ⟨D, IExp.var j⟩ 0) >>= fun _ => ins (.lit p ⟨Nu, IExp.var j + 1⟩ 0))
        (cgStepWith mv p (.const N) W (3 * IExp.const N + IExp.const N * (IExp.var j % 2))
          (3 * IExp.const N + IExp.const N * ((IExp.var j + 1) % 2)) sb ⟨G, IExp.var j⟩
          ⟨D, IExp.var j⟩ ⟨Nu, IExp.var j + 1⟩)).run st = some st' ∧
      CGLoopInv p dec s₁ W sb G D Nu q A ε bv (j + 1) st'.store := by
  obtain ⟨hf, k, T, hkj, hv, hstop, hx, hr, hp, hνc, h3, hout, hnu, hzo⟩ := hinv
  obtain ⟨w0, hw0, hd0⟩ := hνc
  obtain ⟨w3, hw3, hd3⟩ := h3
  have hcmp : cmpStep I p .eq ⟨sb, 0⟩ ⟨sb, 3⟩ st =
      some (decide (T.ν k = 0), { st with cnt := st.cnt + I.charge (.cmp p) }) := by
    simp only [cmpStep]
    rw [show (⟨sb, 0⟩ : Cell ℕ ℕ).idx.eval = 0 from rfl, hw0,
      show (⟨sb, 3⟩ : Cell ℕ ℕ).idx.eval = 3 from rfl, hw3]
    simp [h.cmp_eq, hd0, hd3]
  rw [run_ifThenElse_eq_seq, exec_seq_skip, exec_ite, hcmp, Option.bind_some]
  by_cases hν0 : T.ν k = 0
  · rw [show decide (T.ν k = 0) = true from decide_eq_true hν0, if_pos rfl]
    exact cgLoopInv_skip I h hS₁ hSG hSD hSN hGW hGs hDW hDs hNW hNs hGD hGN hDN hj
      { st with cnt := st.cnt + I.charge (.cmp p) } hf hkj hv hx hr ⟨w0, hw0, hd0⟩
      ⟨w3, hw3, hd3⟩ hout hnu hzo hν0
  · obtain rfl : k = j := by
      by_contra hne
      exact hν0 (hstop (by omega))
    rw [show decide (T.ν k = 0) = false from decide_eq_false hν0, if_neg Bool.false_ne_true]
    exact cgLoopInv_step I h hz hu hmv hc hε hA ha hs hκ hsm hmε h3a h20 hb0 hS₁ hR₁ hSW hS hSG
      hSD hSN hWs hGW hGs hDW hDs hNW hNs hGD hGN hDN hRW hRs hRG hRD hRN hj
      { st with cnt := st.cnt + I.charge (.cmp p) } hf hv hx hr (hp hν0) ⟨w0, hw0, hd0⟩
      ⟨w3, hw3, hd3⟩ hout hnu hν0

/-- **The facts of a run of the CG program on its outputs**, at the store `s`: computed sequences
of $k \ge 1$ steps (`NLAlib.CGSeq.Valid`), $\nu_k = 0$ if $k < q$, the iterate $\mathbf{x}_k$
in `X`, $\gamma_i, \delta_i$ ($i < k$) and $\nu_i$ ($i \le k$) in the outputs, and zeros after
the stop. -/
def CGRunFacts (p : P) (dec : P → K → ℝ) (X G D Nu q : ℕ) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (ε : ℝ) (bv : Fin N → ℝ) (s : Store P K) : Prop :=
  ∃ (k : ℕ) (T : CGSeq N), 0 < k ∧ k ≤ q ∧ T.Valid A bv ε k ∧ (k < q → T.ν k = 0) ∧
    DecVec s p dec X 0 (T.x k) ∧
    (∀ i < k, DecCell s p dec G i (T.γ i) ∧ DecCell s p dec D i (T.δ i)) ∧
    (∀ i ≤ k, DecCell s p dec Nu i (T.ν i)) ∧
    ∀ i, k ≤ i → i < q →
      DecCell s p dec G i 0 ∧ DecCell s p dec D i 0 ∧ DecCell s p dec Nu (i + 1) 0

/-- The sequences at the start: $\mathbf{x}_0 = \mathbf{0}$, $\mathbf{r}_0 = \mathbf{p}_0 =
\mathbf{b}$, $\nu_0$ with relative error $\theta_0$. -/
def CGSeq.start {N : ℕ} (bv : Fin N → ℝ) (ν θ : ℝ) : CGSeq N :=
  ⟨fun _ => 0, fun _ => bv, fun _ => bv, 0, fun _ => ν, 0, 0, 0, 0, fun _ => θ, 0, 0, 0, 0, 0, 0⟩

theorem CGSeq.start_valid {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {bv : Fin N → ℝ} {ε ν θ : ℝ}
    (hν : ν = ‖WithLp.toLp 2 bv‖ ^ 2 * (1 + θ)) (hθ : |θ| ≤ ε) :
    (CGSeq.start bv ν θ).Valid A bv ε 0 :=
  ⟨rfl, rfl, rfl, hν, hθ, fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega)⟩

/-- The CG program after its two allocations: the start, the loop and the copy of the
iterate. -/
theorem exec_cg_inner (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hu : ((N + 2 : ℕ) : ℝ) * u p < 1)
    {mv : ℕ → IExp ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit} {R : ℕ} {s₀ : Store P K}
    {A : Matrix (Fin N) (Fin N) ℝ} {c ε : ℝ} (hmv : LanczosMvSpec I mv p dec R s₀ A c)
    (hc : c ≤ ε * specNorm A) (hε : roundingFactor (N + 2) (u p) ≤ ε) (hA : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (hκ : a ≤ a') {q : ℕ} (hq : 0 < q)
    (hsm : ∀ m ≤ q, (m : ℝ) ^ 3 * ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hmε : ∀ m ≤ q, (m : ℝ) * ε ≤ 1 / 100) (h3a : 3 * ε * a' ≤ a)
    (h20 : ∀ m ≤ q, 20 * m * ε * (1 + 2 * (a' / a) + 21 / 20 * (a' / a)) ≤ 1)
    (st : St P K C) {S : Array (P × ℕ)} (hsh : st.store.shape = S)
    (hR₁ : ∀ i, st.store.read p R i = s₀.read p R i) {B X W sb G D Nu : ℕ} {bv : Fin N → ℝ}
    (hB : DecVec st.store p dec B 0 bv) (hb0 : bv ≠ 0)
    (hSX : S[X]? = some (p, N)) (hSW : S[W]? = some (p, 5 * N)) (hS : S[sb]? = some (p, 7))
    (hSG : S[G]? = some (p, q)) (hSD : S[D]? = some (p, q)) (hSN : S[Nu]? = some (p, q + 1))
    (hBW : B ≠ W) (hBs : B ≠ sb) (hBG : B ≠ G) (hBD : B ≠ D) (hBN : B ≠ Nu) (hWs : W ≠ sb)
    (hXW : X ≠ W) (hXG : X ≠ G) (hXD : X ≠ D) (hXN : X ≠ Nu) (hGW : G ≠ W) (hGs : G ≠ sb)
    (hDW : D ≠ W) (hDs : D ≠ sb) (hNW : Nu ≠ W) (hNs : Nu ≠ sb) (hGD : G ≠ D) (hGN : G ≠ Nu)
    (hDN : D ≠ Nu) (hRW : R ≠ W) (hRs : R ≠ sb) (hRG : R ≠ G) (hRD : R ≠ D) (hRN : R ≠ Nu) :
    ∃ st' : St P K C, exec I (ins (.lit p ⟨sb, 3⟩ 0) >>=
        fun _ => forRange (.const N) (fun i => ins (.lit p ⟨W, IExp.var i⟩ 0)) >>=
        fun _ => copyv p B 0 W (.const N) (.const N) >>=
        fun _ => copyv p B 0 W (3 * IExp.const N) (.const N) >>=
        fun _ => dot p ⟨sb, 0⟩ B 0 B 0 (.const N) >>=
        fun _ => ins (.copy p ⟨Nu, 0⟩ ⟨sb, 0⟩) >>=
        fun _ => (forRange (.const q) fun j => ifThenElse p .eq ⟨sb, 0⟩ ⟨sb, 3⟩
          (ins (.lit p ⟨G, IExp.var j⟩ 0) >>= fun _ =>
            ins (.lit p ⟨D, IExp.var j⟩ 0) >>= fun _ => ins (.lit p ⟨Nu, IExp.var j + 1⟩ 0))
          (cgStepWith mv p (.const N) W (3 * IExp.const N + IExp.const N * (IExp.var j % 2))
            (3 * IExp.const N + IExp.const N * ((IExp.var j + 1) % 2)) sb ⟨G, IExp.var j⟩
            ⟨D, IExp.var j⟩ ⟨Nu, IExp.var j + 1⟩)) >>=
        fun _ => copyv p W 0 X 0 (.const N)).run st = some st' ∧
      st'.store.shape = S ∧ CGRunFacts p dec X G D Nu q A ε bv st'.store := by
  have hε1 : ε < 1 := by have := hmε 1 hq; simp at this; linarith
  have hu1 : u p < 1 := by
    simpa using cast_mul_lt_one_of_le (m := 1) (h.nonneg trivial) (Nat.le_add_left 1 (N + 1)) hu
  obtain ⟨st₁, ν, θ, h₁, hf₁, hx₁, hr₁, hp₁, hν₁, h3₁, hn₁, hθ, hν⟩ := exec_cg_init I h hz hu1 st
    hsh hB hBW hBs hWs hNW hNs hSW hS hSN (Nat.succ_pos q)
  have hθε : |θ| ≤ ε :=
    (hθ.abs_le (cast_mul_lt_one_of_le (h.nonneg trivial) (Nat.le_add_right N 2) hu)).trans
      ((roundingFactor_le_roundingFactor (h.nonneg trivial) (Nat.le_add_right N 2) hu).trans hε)
  have hv₀ := CGSeq.start_valid (A := A) hν hθε
  have hinv₀ : CGLoopInv p dec st.store W sb G D Nu q A ε bv 0 st₁.store := by
    refine ⟨hf₁.mono fun b i hb => ?_, 0, CGSeq.start bv ν θ, le_rfl, hv₀,
      fun h' => absurd h' (lt_irrefl 0), hx₁, hr₁,
      fun _ => by rw [show 3 * N + N * (0 % 2) = 3 * N by simp]; exact hp₁, hν₁, h3₁,
      fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => by obtain rfl : i = 0 := Nat.le_zero.mp hi
                     exact hn₁, fun i h1 h2 => absurd h2 (Nat.not_lt_zero i)⟩
    rcases hb with hb | hb | hb
    · exact Or.inl hb
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hb.1, hb.2.1,
      Nat.lt_of_lt_of_le hb.2.2 (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le q)) 0)⟩)))
  obtain ⟨st₂, h₂, hinv⟩ := exists_exec_loop_eq_some_of_forall I (n := .const q)
    (fun j st' => CGLoopInv p dec st.store W sb G D Nu q A ε bv j st'.store) hinv₀
    fun j hj st' hI => CGLoopInv.succ I h hz hu hmv hc hε hA ha hs hκ hsm hmε h3a h20 hb0 hsh
      hR₁ hSW hS hSG hSD hSN hWs hGW hGs hDW hDs hNW hNs hGD hGN hDN hRW hRs hRG hRD hRN hj
      st' hI
  obtain ⟨hf, k, T, hkq, hv, hstop, hx, -, -, -, -, hout, hnu, hzo⟩ := hinv
  obtain ⟨st₃, h₃, hf₃, hX₃⟩ := exec_copyv_decVec I st₂ (hf.1.trans hsh) W 0 X 0
    (by simpa using hx) hSX (by simp) fun h' => absurd h'.symm hXW
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exfalso
      have h0 := hstop (show 0 < q from hq)
      have := hv.r_eq_zero_of_ν_eq_zero hε1 le_rfl h0
      exact hb0 (by rw [← hv.r_zero]; exact this)
    · exact hk
  refine ⟨st₃, ?_, hf₃.1.trans (hf.1.trans hsh), k, T, hk, hkq, hv, hstop, by simpa using hX₃,
    fun i hi => ⟨(hout i hi).1.frame hf₃ fun hb => hXG hb.1.symm,
      (hout i hi).2.frame hf₃ fun hb => hXD hb.1.symm⟩,
    fun i hi => (hnu i hi).frame hf₃ fun hb => hXN hb.1.symm, fun i h1 h2 => ?_⟩
  · rw [h₁ _, exec_bind_of_exec_eq_some I (b := forRange _ _) ((exec_seq_skip I _ _).trans h₂)
      (seqShape_forRange _ _)]
    exact h₃
  · obtain ⟨a1, a2, a3⟩ := hzo i h1 h2
    exact ⟨a1.frame hf₃ fun hb => hXG hb.1.symm, a2.frame hf₃ fun hb => hXD hb.1.symm,
      a3.frame hf₃ fun hb => hXN hb.1.symm⟩

theorem cgRunFacts_pop {X G D Nu q N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {ε : ℝ}
    {bv : Fin N → ℝ} {s : Store P K} (hX : X + 1 < s.size) (hG : G + 1 < s.size)
    (hD : D + 1 < s.size) (hN : Nu + 1 < s.size) (h' : CGRunFacts p dec X G D Nu q A ε bv s) :
    CGRunFacts p dec X G D Nu q A ε bv s.pop := by
  obtain ⟨k, T, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h'
  have hpop : ∀ {b : ℕ}, b + 1 < s.size → ∀ i v, DecCell s p dec b i v →
      DecCell s.pop p dec b i v :=
    fun hb i v ⟨w, hw, hd⟩ => ⟨w, by rw [Store.read_pop_of_lt (by omega)]; exact hw, hd⟩
  refine ⟨k, T, h1, h2, h3, h4, fun i => hpop hX _ _ (h5 i), fun i hi => ⟨hpop hG _ _ (h6 i hi).1,
    hpop hD _ _ (h6 i hi).2⟩, fun i hi => hpop hN _ _ (h7 i hi), fun i hi hi' =>
    ⟨hpop hG _ _ (h8 i hi hi').1, hpop hD _ _ (h8 i hi hi').2.1, hpop hN _ _ (h8 i hi hi').2.2⟩⟩

/-- **The run of the CG program in the standard model**, for any product meeting
`NLAlib.LanczosMvSpec` (with read-only buffer `R` as in the initial store): under
`NLAlib.Computation.IsRelErrSem` with every value in range and adding zero exactly, with
$(N + 2)u_p < 1$, $\varepsilon \ge \gamma_{N+2}$, the product bound $c \le
\varepsilon\|\mathbf{A}\|_2$, a symmetric $\mathbf{A}$ with spectrum in $[a, a']$, $0 < a \le
a'$, the smallness facts of the a priori analysis for every $m \le q$, a right-hand side
$\mathbf{b} \ne \mathbf{0}$ in buffer `B` and writable outputs `X` ($N$ cells), `G`, `D` ($q$)
and `Nu` ($q + 1$), the run succeeds and its outputs satisfy `NLAlib.CGRunFacts`. -/
theorem _root_.NLAlib.Computation.IsRelErrSem.exists_cgRunFacts_of_cgProgWith
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) {N q : ℕ}
    (hu : ((N + 2 : ℕ) : ℝ) * u p < 1) {mv : ℕ → IExp ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit}
    {R : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {c ε : ℝ} (st : St P K C)
    (hmv : LanczosMvSpec I mv p dec R st.store A c) (hc : c ≤ ε * specNorm A)
    (hε : roundingFactor (N + 2) (u p) ≤ ε) (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ A ⊆ Set.Icc a a') (hκ : a ≤ a') (hq : 0 < q)
    (hsm : ∀ m ≤ q, (m : ℝ) ^ 3 * ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hmε : ∀ m ≤ q, (m : ℝ) * ε ≤ 1 / 100) (h3a : 3 * ε * a' ≤ a)
    (h20 : ∀ m ≤ q, 20 * m * ε * (1 + 2 * (a' / a) + 21 / 20 * (a' / a)) ≤ 1)
    {B X G D Nu : ℕ} {bv : Fin N → ℝ} (hB : DecVec st.store p dec B 0 bv) (hb0 : bv ≠ 0)
    (hBs : B < st.store.size) (hRs : R < st.store.size)
    (hSX : st.store.shape[X]? = some (p, N)) (hSG : st.store.shape[G]? = some (p, q))
    (hSD : st.store.shape[D]? = some (p, q)) (hSN : st.store.shape[Nu]? = some (p, q + 1))
    (hBG : B ≠ G) (hBD : B ≠ D) (hBN : B ≠ Nu) (hXG : X ≠ G) (hXD : X ≠ D) (hXN : X ≠ Nu)
    (hGD : G ≠ D) (hGN : G ≠ Nu) (hDN : D ≠ Nu) (hRG : R ≠ G) (hRD : R ≠ D) (hRN : R ≠ Nu) :
    ∃ st' : St P K C,
      exec I (cgProgWith mv p (.const N) (.const q) B X G D Nu).run st = some st' ∧
      CGRunFacts p dec X G D Nu q A ε bv st'.store := by
  have hlt : ∀ {b n}, st.store.shape[b]? = some (p, n) → b < st.store.size := fun hb' => by
    have := (Array.getElem?_eq_some_iff.mp hb').1
    rwa [Store.size_shape] at this
  have hLX := hlt hSX
  have hLG := hlt hSG
  have hLD := hlt hSD
  have hLN := hlt hSN
  unfold cgProgWith
  rw [run_alloc_bind]
  refine exec_alloc_of I fun st₁ hst₁ => ?_
  simp only [run_alloc_bind]
  refine exec_alloc_of I (p := p) (st := st₁) (len := 7)
    (Q := fun s => CGRunFacts p dec X G D Nu q A ε bv s.pop) fun st₃ hst₃ => ?_
  have hsz₁ : st₁.store.size = st.store.size + 1 := by rw [hst₁]; simp
  have hrd : ∀ b i, b < st.store.size → st₃.store.read p b i = st.store.read p b i :=
    fun b i hb' => by
      rw [hst₃, Store.read_push_of_lt (s := st₁.store) (by omega), hst₁,
        Store.read_push_of_lt hb']
  have hshp : ∀ b, b < st.store.size → st₃.store.shape[b]? = st.store.shape[b]? :=
    fun b hb' => by
      rw [hst₃, Store.getElem?_shape_push_of_lt (s := st₁.store) _ (by omega), hst₁,
        Store.getElem?_shape_push_of_lt _ hb']
  obtain ⟨st₄, h₄, hsh₄, hF⟩ := exec_cg_inner I h hz hu hmv hc hε hA ha hs hκ hq hsm hmε h3a h20
    st₃ rfl (fun i => hrd R i hRs) (W := st.store.size) (sb := st₁.store.size)
    (fun i => by rw [hrd B _ hBs]; exact hB i) hb0
    (by rw [hshp _ hLX]; exact hSX)
    (by rw [hst₃, Store.getElem?_shape_push_of_lt (s := st₁.store) _ (by omega), hst₁,
      Store.getElem?_shape_push_size]; rfl)
    (by rw [hst₃]; exact Store.getElem?_shape_push_size _ _ _)
    (by rw [hshp _ hLG]; exact hSG) (by rw [hshp _ hLD]; exact hSD)
    (by rw [hshp _ hLN]; exact hSN) (by omega) (by omega) hBG hBD hBN (by omega) (by omega)
    hXG hXD hXN (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hGD hGN hDN
    (by omega) (by omega) hRG hRD hRN
  have hsz₄ : st₄.store.size = st.store.size + 2 := by
    rw [← Store.size_shape, hsh₄, Store.size_shape, hst₃]; simp [hsz₁]
  refine ⟨st₄, h₄, cgRunFacts_pop ?_ ?_ ?_ ?_ (cgRunFacts_pop ?_ ?_ ?_ ?_ hF)⟩ <;>
    simp [hsz₄] <;> omega

end Run

end NLAlib
