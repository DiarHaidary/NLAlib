/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.CGRunModel

/-!
# Exact conjugate gradients on the backward model of a computed run

Prefix runs retain the same arithmetic data. Whenever the symmetric backward model is positive
definite, exact CG on that model reproduces the computed step lengths and residual norms.
Its spectral interval therefore controls sums of computed residual ratios, independently of
any accumulated-error hypothesis.

## Main definitions

* `NLAlib.CGRun.take`: the first positive number of steps of a run.

## Main results

* `NLAlib.CGRun.lanczosTridiagonal_backwardH`: the model reproduces the tridiagonal matrix.
* `NLAlib.CGRun.cgAlpha_backwardH_of_posDef`: exact reproduction of step lengths.
* `NLAlib.CGRun.norm_cgState_backwardH_r_of_posDef`: exact reproduction of residual norms.
* `NLAlib.CGRun.sum_ρ_sq_div_ρ_sq_le`: a spectral bound on computed residual-ratio sums.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-- **The first $m$ steps of a run**, $1 \le m \le k$: the same data, every hypothesis
restricted. There is no run of $0$ steps (`NLAlib.CGRun.k_pos`): the step $j = 0$ of the
induction and the iteration $m = 0$ of the bridge are handled directly
($\mathbf{p}_0 = \mathbf{r}_0 = \mathbf{b}$). -/
noncomputable def take (m : ℕ) (hm : 0 < m) (hmk : m ≤ k) : CGRun n m where
  A := C.A
  b := C.b
  x := C.x
  r := C.r
  p := C.p
  s := C.s
  ν := C.ν
  μ := C.μ
  γ := C.γ
  δ := C.δ
  es := C.es
  θ := C.θ
  eμ := C.eμ
  eγ := C.eγ
  ex := C.ex
  er := C.er
  eδ := C.eδ
  ep := C.ep
  ε := C.ε
  transpose_A := C.transpose_A
  ε_nonneg := C.ε_nonneg
  k_pos := hm
  ε_le := C.ε_le
  x_zero := C.x_zero
  r_zero := C.r_zero
  p_zero := C.p_zero
  ν_eq := fun j hj => C.ν_eq j (hj.trans hmk)
  abs_θ_le := fun j hj => C.abs_θ_le j (hj.trans hmk)
  ν_pos := fun j hj => C.ν_pos j (hj.trans_le hmk)
  s_eq := fun j hj => C.s_eq j (hj.trans_le hmk)
  norm_es_le := fun j hj => C.norm_es_le j (hj.trans_le hmk)
  μ_eq := fun j hj => C.μ_eq j (hj.trans_le hmk)
  abs_eμ_le := fun j hj => C.abs_eμ_le j (hj.trans_le hmk)
  μ_pos := fun j hj => C.μ_pos j (hj.trans_le hmk)
  γ_eq := fun j hj => C.γ_eq j (hj.trans_le hmk)
  abs_eγ_le := fun j hj => C.abs_eγ_le j (hj.trans_le hmk)
  x_succ := fun j hj => C.x_succ j (hj.trans_le hmk)
  norm_ex_le := fun j hj => C.norm_ex_le j (hj.trans_le hmk)
  r_succ := fun j hj => C.r_succ j (hj.trans_le hmk)
  norm_er_le := fun j hj => C.norm_er_le j (hj.trans_le hmk)
  δ_eq := fun j hj => C.δ_eq j (hj.trans_le hmk)
  abs_eδ_le := fun j hj => C.abs_eδ_le j (hj.trans_le hmk)
  p_succ := fun j hj => C.p_succ j (hj.trans_le hmk)
  norm_ep_le := fun j hj => C.norm_ep_le j (hj.trans_le hmk)

/-! ### Helpers -/

/-- The initial residual has the norm of the right-hand side. -/
theorem ρ_zero : C.ρ 0 = ‖WithLp.toLp 2 C.b‖ := by
  simp [ρ, C.r_zero]

/-- A successful first step requires a nonzero right-hand side. -/
theorem norm_b_pos : 0 < ‖WithLp.toLp 2 C.b‖ := by
  rw [← C.ρ_zero]
  exact C.ρ_pos C.k_pos

/-- Exact Lanczos does not see a positive scaling of its start. -/
private theorem lanczosState_smul {m : Type*} [Fintype m]
    (H : Matrix m m ℝ) (v : m → ℝ) {c : ℝ} (hc : 0 < c) (j : ℕ) :
    lanczosState H (c • v) j = lanczosState H v j := by
  induction j with
  | zero =>
    simp only [lanczosState]
    congr 1
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
    simp only [RCLike.ofReal_real_eq_id, id]
    rw [mul_inv, mul_right_comm, inv_mul_cancel₀ hc.ne', one_mul]
  | succ j ih => simp only [lanczosState, ih]

private theorem lanczosTridiagonal_smul {m : Type*} [Fintype m]
    (H : Matrix m m ℝ) (v : m → ℝ) {c : ℝ} (hc : 0 < c) (q : ℕ) :
    lanczosTridiagonal H (c • v) q = lanczosTridiagonal H v q := by
  simp only [lanczosTridiagonal, lanczosState_smul H v hc]

private theorem lanczosV_one : C.lanczosV 1 = (‖WithLp.toLp 2 C.b‖⁻¹ : ℝ) • C.b := by
  simp only [lanczosV, one_ne_zero, if_false, Nat.sub_self, pow_zero, one_mul]
  split_ifs <;> simp [ρ, C.r_zero]

private theorem dilatedRhs_eq :
    C.dilatedRhs = ‖WithLp.toLp 2 C.b‖ • C.toNormalizedLanczosData.dilatedStart := by
  funext x
  simp only [dilatedRhs, NormalizedLanczosData.dilatedStart, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · change C.b x.1 = ‖WithLp.toLp 2 C.b‖ * C.lanczosV 1 x.1
    rw [lanczosV_one, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ C.norm_b_pos.ne', one_mul]
  · simp

/-- There is at least one coordinate: $\mathbf{b} \ne \mathbf{0}$. -/
theorem n_pos {n k : ℕ} (C : CGRun n k) : 0 < n := by
  by_contra h
  have h0 : C.b = 0 := funext fun i => absurd i.2 (by omega)
  have := C.norm_b_pos
  rw [h0, WithLp.toLp_zero, norm_zero] at this
  exact lt_irrefl _ this

/-- The backward model is symmetric. -/
theorem isHermitian_backwardH : C.backwardH.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, backwardH,
    NormalizedLanczosData.transpose_backwardH]

/-- The matrix of the run is symmetric. -/
theorem isHermitian : C.A.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, C.transpose_A]

/-- The coordinate type of the dilated model is nonempty. -/
theorem nonempty_index {n k : ℕ} (C : CGRun n k) : Nonempty (Fin n × Fin (k + 1)) :=
  ⟨(⟨0, C.n_pos⟩, 0)⟩

/-! ### Exact CG on a positive definite model (no smallness hypothesis) -/

/-- **Exact Lanczos on the model computes the CG tridiagonal matrix** of the run, from the
dilated right-hand side (no accumulated-error hypothesis). -/
theorem lanczosTridiagonal_backwardH :
    lanczosTridiagonal C.backwardH C.dilatedRhs k = cgTridiagonal C.γ C.ρ k := by
  rw [dilatedRhs_eq, lanczosTridiagonal_smul _ _ C.norm_b_pos, backwardH,
    NormalizedLanczosData.lanczosTridiagonal_backwardH_dilatedStart]
  exact C.tridiagonal_toLanczosData

/-- Exact Lanczos on the model computes the last coefficient of the run. -/
private theorem lanczosState_backwardH_beta :
    (lanczosState C.backwardH C.dilatedRhs k).beta = C.ρ k / (C.γ (k - 1) * C.ρ (k - 1)) := by
  rw [dilatedRhs_eq, lanczosState_smul _ _ C.norm_b_pos, backwardH,
    NormalizedLanczosData.lanczosState_backwardH_dilatedStart_beta]
  change C.lanczosβ k = _
  simp [lanczosβ, C.k_pos.ne']

/-- The dilated right-hand side has the norm of the right-hand side. -/
theorem norm_dilatedRhs : ‖WithLp.toLp 2 C.dilatedRhs‖ = ‖WithLp.toLp 2 C.b‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (0 : Fin (k + 1))]
  · simp [dilatedRhs]
  · intro r _ hr
    have : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h)
    simp [dilatedRhs, this]
  · simp

/-- **Exact CG on a positive definite model computes the computed step lengths**: if the
backward model of the run is positive definite, then for $j < k$ the step length of
`NLAlib.cgState` on $(\tilde{\mathbf{H}}, (\mathbf{b}, \mathbf{0}, \dots))$ from $\mathbf{0}$ is
$\gamma_j$. This form, with positive definiteness as a hypothesis, is the one the a priori
induction uses on the prefix models. -/
theorem cgAlpha_backwardH_of_posDef (hH : C.backwardH.PosDef) {j : ℕ} (hj : j < k) :
    cgAlpha C.backwardH (cgState C.backwardH C.dilatedRhs 0 j) = C.γ j :=
  hH.cgAlpha_cgState_eq_of_lanczosTridiagonal_eq C.lanczosTridiagonal_backwardH
    C.lanczosState_backwardH_beta (fun _ hi => C.γ_pos hi) (fun _ hi => C.ρ_pos hi)
    (C.ρ_zero.trans (by simp [norm_dilatedRhs])) hj

/-- **Exact CG on a positive definite model has the computed residual norms**: if the backward
model is positive definite, $\|\tilde{\mathbf{r}}_j\| = \|\mathbf{r}_j\|$ for $j \le k$. -/
theorem norm_cgState_backwardH_r_of_posDef (hH : C.backwardH.PosDef) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (cgState C.backwardH C.dilatedRhs 0 j).r‖ = C.ρ j :=
  hH.norm_cgState_r_eq_of_lanczosTridiagonal_eq C.lanczosTridiagonal_backwardH
    C.lanczosState_backwardH_beta (fun _ hi => C.γ_pos hi) (fun _ hi => C.ρ_pos hi)
    (C.ρ_zero.trans (by simp [norm_dilatedRhs])) hj

/-- **The residual ratios of the run are bounded by the model's condition number**: if the
spectrum of the backward model lies in $[l, l']$, $l > 0$, then for $j \le k$
$$S_j = \sum_{i \le j}\frac{\|\mathbf{r}_j\|^2}{\|\mathbf{r}_i\|^2} \le \frac{l'}{l} .$$
This is the step (P) of the a priori induction: $S_j$ is what the recursion for
$\pi_j^2 = \|\mathbf{p}_j\|^2/\rho_j^2$ telescopes to. -/
theorem sum_ρ_sq_div_ρ_sq_le {l l' : ℝ} (hl : 0 < l)
    (hH : spectrum ℝ C.backwardH ⊆ Set.Icc l l') {j : ℕ} (hj : j ≤ k) :
    ∑ i ∈ Finset.range (j + 1), C.ρ j ^ 2 / C.ρ i ^ 2 ≤ l' / l := by
  have hPD : C.backwardH.PosDef :=
    C.isHermitian_backwardH.posDef_iff_eigenvalue_pos.mpr fun i hi =>
      hl.trans_le (C.isHermitian_backwardH.spectrum_subset_iff.mp hH i hi).1
  have heq := hPD.norm_cgState_p_sq_eq C.dilatedRhs j
  have hle := hPD.norm_cgState_p_sq_le hl hH C.dilatedRhs j
  have hr : ∀ i ≤ j, ‖WithLp.toLp 2 (cgState C.backwardH C.dilatedRhs 0 i).r‖ = C.ρ i :=
    fun i hi => C.norm_cgState_backwardH_r_of_posDef hPD (hi.trans hj)
  rw [hr j le_rfl] at heq hle
  rw [Finset.sum_congr rfl fun i hi => by rw [hr i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]]
    at heq
  have := C.nonempty_index
  have h0 := C.isHermitian_backwardH.spectrum_subset_iff.mp hH 0 Fintype.card_pos
  have hll' : l ≤ l' := h0.1.trans h0.2
  rcases (norm_nonneg (WithLp.toLp 2 (C.r j))).lt_or_eq with hρ | hρ
  · change 0 < C.ρ j at hρ
    have hρ2 : 0 < C.ρ j ^ 2 := by positivity
    have : ∑ i ∈ Finset.range (j + 1), C.ρ j ^ 2 / C.ρ i ^ 2 =
        ‖WithLp.toLp 2 (cgState C.backwardH C.dilatedRhs 0 j).p‖ ^ 2 / C.ρ j ^ 2 := by
      rw [heq, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [this, div_le_iff₀ hρ2]
    exact hle
  · change 0 = C.ρ j at hρ
    rw [← hρ]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      Finset.sum_const_zero]
    exact div_nonneg (hl.le.trans hll') hl.le

end CGRun

end NLAlib
