/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.CGRun

/-!
# An a priori backward model for finite-precision conjugate gradients

For a conjugate gradient run `C : NLAlib.CGRun n k` on a matrix with spectrum in $[a, a']$,
$a > 0$, $\kappa = a'/a$, under the smallness hypothesis
$$\text{(H)}\qquad k^3\,\varepsilon\,\kappa^2 \le 10^{-5},$$
the run certificates are bounded a priori ($\|\mathbf{p}_j\|^2 \le 3.3\kappa\|\mathbf{r}_j\|^2$,
$\|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2 \le 1.05\kappa\|\mathbf{r}_j\|^2$, $\beta_{j+1},
\delta_j/\gamma_j \le 1.6a'$), and the backward model of the run satisfies
$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{A}\|_{\mathsf{F}} \le
4 \cdot 10^4\,k^3\,\varepsilon\,\kappa\,a' \le a/2 .$$
Exact CG on $(\tilde{\mathbf{H}}, (\mathbf{b}, \mathbf{0}, \dots, \mathbf{0}))$ computes the
computed step lengths $\gamma_j$ exactly and residuals of exactly the computed norms
$\|\mathbf{r}_j\|$; its $\tilde{\mathbf{H}}$-norm error decreases by exactly
$\gamma_j\|\mathbf{r}_j\|^2$ per step, the estimator of [StrakosTichy2002, (4.9)]; and its
squared error at step $k$ is $\|\mathbf{x}_\star\|_{\mathbf{A}}^2 - \sum_{j<k}\gamma_j
\|\mathbf{r}_j\|^2$ up to $2\|\mathbf{b}\|^2c/a^2$, $c$ the model distance.

The proof is one induction on the number of steps (the private theorem
`aprioriCertificates` of this file, by `Nat.rec`) through the backward model of the prefix runs
(`NLAlib.CGRun.take`), built by the a posteriori engine
`NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le_of_certificates` and never by the a priori
theorems below (which are its corollaries): the model of the first $j$ steps is positive
definite with condition number at most $2\kappa + 1$ by P(j); exact CG on it reproduces the run
(`NLAlib.CGRun.cgAlpha_backwardH_of_posDef`, `NLAlib.CGRun.norm_cgState_backwardH_r_of_posDef`, no
smallness hypothesis) and bounds the certificates of step $j$
(`NLAlib.CGRun.sum_ρ_sq_div_ρ_sq_le` from `Matrix.PosDef.norm_cgState_p_sq_eq` and
`Matrix.PosDef.norm_cgState_p_sq_le`; `Matrix.PosDef.norm_cgState_r_succ_sq_div_le`), and Lemmas
A and B close P(j + 1).

Validity range: (H) bounds $k \le (10^{-5}/(\varepsilon\kappa^2))^{1/3}$; in double precision,
$\kappa = 10$, about $k \le 30$ (dense, $N = 10^3$) to $k \le 97$ (oracle, $\varepsilon \approx
Nu$), and vacuous for $\kappa = 10^3$ at practical sizes. The a posteriori model of
`NLAlibScaffold/Krylov/FinitePrecision/CGRun.lean` has no such limit.

Research branch `research/hscg-fp`. Design: `docs/design/research/Krylov-CGRounding.md` (§6–§8).
Constants are unoptimised; see the note.

## Main definitions

* `NLAlib.CGRun.take`: the first $m$ steps of a run.

## Main results

* `NLAlib.CGRun.cgAlpha_backwardH_of_posDef`, `NLAlib.CGRun.norm_cgState_backwardH_r_of_posDef`,
  `NLAlib.CGRun.sum_ρ_sq_div_ρ_sq_le`: exact CG on a positive definite model reproduces the run
  and bounds its residual ratios (no smallness hypothesis; used on the prefix models).

* `NLAlib.CGRun.norm_p_sq_le`, `NLAlib.CGRun.specNorm_mul_γ_mul_norm_p_sq_le`,
  `NLAlib.CGRun.lanczosβ_succ_le`, `NLAlib.CGRun.δ_le`, `NLAlib.CGRun.ρ_le`: a priori
  certificates.
* `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le`: the a priori backward model.
* `NLAlib.CGRun.cgAlpha_backwardH`, `NLAlib.CGRun.norm_cgState_backwardH_r`: exact CG on the
  model reproduces the run.
* `NLAlib.CGRun.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate`,
  `NLAlib.CGRun.abs_quadForm_backwardH_sub_cgIterate_sub_le`: the model's errors in terms of the
  computed coefficients.
* `NLAlib.CGRun.ρ_le_chebyshev`: the computed residual norms converge at the Chebyshev rate of
  $2\kappa + 1$.
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
  k_mul_ε_le := by
    have h : (m : ℝ) ≤ k := by exact_mod_cast hmk
    nlinarith [C.k_mul_ε_le, C.ε_nonneg]
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

/-- The computed residual norms are positive before the last step. -/
private theorem ρ_pos {j : ℕ} (hj : j < k) : 0 < C.ρ j := by
  rcases (norm_nonneg (WithLp.toLp 2 (C.r j))).lt_or_eq with h | h
  · exact h
  · have h1 := C.ν_pos j hj
    rw [C.ν_eq j hj.le, ← h] at h1
    simp at h1

private theorem ρ_zero : C.ρ 0 = ‖WithLp.toLp 2 C.b‖ := by
  simp [ρ, C.r_zero]

private theorem norm_b_pos : 0 < ‖WithLp.toLp 2 C.b‖ := by
  rw [← C.ρ_zero]
  exact C.ρ_pos C.k_pos

/-- Exact Lanczos does not see a positive scaling of its start. -/
private theorem lanczosState_smul {m : Type*} [Fintype m] [DecidableEq m]
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

private theorem lanczosTridiagonal_smul {m : Type*} [Fintype m] [DecidableEq m]
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
private theorem n_pos {n k : ℕ} (C : CGRun n k) : 0 < n := by
  by_contra h
  have h0 : C.b = 0 := funext fun i => absurd i.2 (by omega)
  have := C.norm_b_pos
  rw [h0, WithLp.toLp_zero, norm_zero] at this
  exact lt_irrefl _ this

/-- The Rayleigh bounds of a symmetric matrix with spectrum in $[l, l']$. -/
private theorem quadForm_bounds {m : Type*} [Fintype m] [DecidableEq m] {H : Matrix m m ℝ}
    (hH : H.IsHermitian) {l l' : ℝ} (hs : spectrum ℝ H ⊆ Set.Icc l l') (x : m → ℝ) :
    l * ‖WithLp.toLp 2 x‖ ^ 2 ≤ x ⬝ᵥ (H *ᵥ x) ∧ x ⬝ᵥ (H *ᵥ x) ≤ l' * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos (Fintype.card m) with h0 | hpos
  · have : IsEmpty m := Fintype.card_eq_zero_iff.mp h0
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    simp
  · obtain ⟨c, hc⟩ : ∃ c, c + 1 = Fintype.card m := ⟨Fintype.card m - 1, by omega⟩
    have h1 := hH.eigenvalue_last_mul_le_re_quadForm hc x
    have h2 := hH.re_quadForm_le_eigenvalue_zero_mul x
    simp only [quadForm_def, star_trivial, RCLike.re_to_real] at h1 h2
    have e1 := (hH.spectrum_subset_iff.mp hs c (by omega)).1
    have e2 := (hH.spectrum_subset_iff.mp hs 0 hpos).2
    have hx := sq_nonneg ‖WithLp.toLp 2 x‖
    exact ⟨(mul_le_mul_of_nonneg_right e1 hx).trans h1,
      h2.trans (mul_le_mul_of_nonneg_right e2 hx)⟩

/-- A symmetric matrix with spectrum in $[l, l']$, $l > 0$, is positive definite. -/
private theorem posDef_of_spectrum {m : Type*} [Fintype m] [DecidableEq m] {H : Matrix m m ℝ}
    (hH : H.IsHermitian) {l l' : ℝ} (hl : 0 < l) (hs : spectrum ℝ H ⊆ Set.Icc l l') :
    H.PosDef :=
  hH.posDef_iff_eigenvalue_pos.mpr fun i hi => hl.trans_le (hH.spectrum_subset_iff.mp hs i hi).1

/-- A nonempty spectrum in $[l, l']$ forces $l \le l'$. -/
private theorem le_of_spectrum {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {H : Matrix m m ℝ} (hH : H.IsHermitian) {l l' : ℝ} (hs : spectrum ℝ H ⊆ Set.Icc l l') :
    l ≤ l' :=
  let h := hH.spectrum_subset_iff.mp hs 0 Fintype.card_pos
  h.1.trans h.2

/-- The backward model is symmetric. -/
private theorem isHermitian_backwardH : C.backwardH.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, backwardH,
    NormalizedLanczosData.transpose_backwardH]

/-- The matrix of the run is symmetric. -/
private theorem isHermitian_A : C.A.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, C.transpose_A]

private theorem nonempty_index {n k : ℕ} (C : CGRun n k) : Nonempty (Fin n × Fin (k + 1)) :=
  ⟨(⟨0, C.n_pos⟩, 0)⟩

/-! ### Exact CG on a positive definite model (no smallness hypothesis) -/

/-- **Exact Lanczos on the model computes the CG tridiagonal matrix** of the run, from the
dilated right-hand side (no hypothesis on $\varepsilon$).
Proof: `NLAlib.NormalizedLanczosData.lanczosTridiagonal_backwardH_dilatedStart`,
`NLAlib.CGRun.tridiagonal_toLanczosData`; `NLAlib.lanczosState` is invariant under positive
scaling of its start (a scaling lemma for `NLAlib.lanczosState`, to be added with the proof),
and the dilated right-hand side is $\|\mathbf{b}\|$ times the dilated start. Difficulty: easy. -/
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
private theorem dilatedRhs_norm : ‖WithLp.toLp 2 C.dilatedRhs‖ = ‖WithLp.toLp 2 C.b‖ := by
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
induction uses on the prefix models.
Proof: `Matrix.PosDef.cgAlpha_cgState_eq_of_lanczosTridiagonal_eq` with
`NLAlib.CGRun.lanczosTridiagonal_backwardH`, the last coefficient from
`NLAlib.NormalizedLanczosData.lanczosState_backwardH_dilatedStart_beta` (and the same scaling
lemma), `NLAlib.CGRun.γ_pos`, $\rho_j > 0$ from `C.ν_pos` and `NLAlib.CGRun.ν_eq_zero_iff`,
$\rho_0 = \|\mathbf{b}\|$. Difficulty: easy. -/
theorem cgAlpha_backwardH_of_posDef (hH : C.backwardH.PosDef) {j : ℕ} (hj : j < k) :
    cgAlpha C.backwardH (cgState C.backwardH C.dilatedRhs 0 j) = C.γ j :=
  hH.cgAlpha_cgState_eq_of_lanczosTridiagonal_eq C.k_pos C.lanczosTridiagonal_backwardH
    C.lanczosState_backwardH_beta (fun _ hi => C.γ_pos hi) (fun _ hi => C.ρ_pos hi)
    (C.ρ_zero.trans (by simp [dilatedRhs_norm])) hj

/-- **Exact CG on a positive definite model has the computed residual norms**: if the backward
model is positive definite, $\|\tilde{\mathbf{r}}_j\| = \|\mathbf{r}_j\|$ for $j \le k$.
Proof: `Matrix.PosDef.norm_cgState_r_eq_of_lanczosTridiagonal_eq`, as
`NLAlib.CGRun.cgAlpha_backwardH_of_posDef`. Difficulty: easy. -/
theorem norm_cgState_backwardH_r_of_posDef (hH : C.backwardH.PosDef) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (cgState C.backwardH C.dilatedRhs 0 j).r‖ = C.ρ j :=
  hH.norm_cgState_r_eq_of_lanczosTridiagonal_eq C.k_pos C.lanczosTridiagonal_backwardH
    C.lanczosState_backwardH_beta (fun _ hi => C.γ_pos hi) (fun _ hi => C.ρ_pos hi)
    (C.ρ_zero.trans (by simp [dilatedRhs_norm])) hj

/-- **The residual ratios of the run are bounded by the model's condition number**: if the
spectrum of the backward model lies in $[l, l']$, $l > 0$, then for $j \le k$
$$S_j = \sum_{i \le j}\frac{\|\mathbf{r}_j\|^2}{\|\mathbf{r}_i\|^2} \le \frac{l'}{l} .$$
This is the step (P) of the a priori induction: $S_j$ is what the recursion for
$\pi_j^2 = \|\mathbf{p}_j\|^2/\rho_j^2$ telescopes to.
Proof: `Matrix.PosDef.norm_cgState_p_sq_eq` and `Matrix.PosDef.norm_cgState_p_sq_le` on the model
give $S_j = \|\tilde{\mathbf{p}}_j\|^2/\|\tilde{\mathbf{r}}_j\|^2 \le l'/l$ (for
$\tilde{\mathbf{r}}_j \ne \mathbf{0}$; else both sides of the identity vanish and $S_j = 0$), with
`NLAlib.CGRun.norm_cgState_backwardH_r_of_posDef`; positive definiteness from the spectrum and
`NLAlib.NormalizedLanczosData.transpose_backwardH`. Difficulty: easy. -/
theorem sum_ρ_sq_div_ρ_sq_le {l l' : ℝ} (hl : 0 < l)
    (hH : spectrum ℝ C.backwardH ⊆ Set.Icc l l') {j : ℕ} (hj : j ≤ k) :
    ∑ i ∈ Finset.range (j + 1), C.ρ j ^ 2 / C.ρ i ^ 2 ≤ l' / l := by
  have hPD := posDef_of_spectrum C.isHermitian_backwardH hl hH
  have heq := hPD.norm_cgState_p_sq_eq C.dilatedRhs j
  have hle := hPD.norm_cgState_p_sq_le hl hH C.dilatedRhs j
  have hr : ∀ i ≤ j, ‖WithLp.toLp 2 (cgState C.backwardH C.dilatedRhs 0 i).r‖ = C.ρ i :=
    fun i hi => C.norm_cgState_backwardH_r_of_posDef hPD (hi.trans hj)
  rw [hr j le_rfl] at heq hle
  rw [Finset.sum_congr rfl fun i hi => by rw [hr i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]]
    at heq
  have := C.nonempty_index
  have hll' : l ≤ l' := le_of_spectrum C.isHermitian_backwardH hH
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

/-! ### Helpers for the a priori induction -/

/-- The smallness hypothesis passes to prefixes. -/
private theorem hsmall_take {a a' : ℝ} (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {m : ℕ} (hm : 0 < m) (hmk : m ≤ k) :
    (m : ℝ) ^ 3 * (C.take m hm hmk).ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
  refine le_trans ?_ hsmall
  change (m : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ _
  have : (m : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hmk) 3
  have h0 : 0 ≤ C.ε * (a' / a) ^ 2 := by have := C.ε_nonneg; positivity
  nlinarith



/-- The elementary consequences of the spectral hypothesis and of (H) for a run of $m$ steps:
$a \le a'$, $\kappa \ge 1$, $\|\mathbf{A}\|_2 \le a'$, and the smallness of $m^i\varepsilon\kappa$,
$i \le 2$. -/
private theorem small_facts {n m : ℕ} (D : CGRun n m) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ D.A ⊆ Set.Icc a a')
    (hsmall : (m : ℝ) ^ 3 * D.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    a ≤ a' ∧ 1 ≤ a' / a ∧ specNorm D.A ≤ a' ∧ D.ε ≤ 1 / 10 ^ 5 ∧
      D.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧ (m : ℝ) * D.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧
      (m : ℝ) ^ 2 * D.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧ (m : ℝ) ^ 3 * D.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
  have hn := D.n_pos
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hherm := D.isHermitian_A
  have haa' : a ≤ a' := le_of_spectrum hherm hs
  have hκ : 1 ≤ a' / a := (one_le_div ha).mpr haa'
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast D.k_pos
  have hε := D.ε_nonneg
  have hspec : specNorm D.A ≤ a' := by
    have hc : n - 1 + 1 = Fintype.card (Fin n) := by simp; omega
    rw [hherm.specNorm_eq_max hc]
    have e0 := hherm.spectrum_subset_iff.mp hs 0 (by simp; omega)
    have e1 := hherm.spectrum_subset_iff.mp hs (n - 1) (by simp; omega)
    rw [abs_of_pos (ha.trans_le e0.1), abs_of_pos (ha.trans_le e1.1)]
    exact max_le e0.2 e1.2
  have hκ2 : a' / a ≤ (a' / a) ^ 2 := by nlinarith
  have hm2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hm3 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by nlinarith
  have h3 : (m : ℝ) ^ 3 * D.ε * (a' / a) ≤ 1 / 10 ^ 5 :=
    le_trans (by have := mul_le_mul_of_nonneg_left hκ2 (by positivity : 0 ≤ (m : ℝ) ^ 3 * D.ε)
                 linarith) hsmall
  have h2 : (m : ℝ) ^ 2 * D.ε * (a' / a) ≤ 1 / 10 ^ 5 :=
    le_trans (by have := mul_le_mul_of_nonneg_right hm3 (by positivity : 0 ≤ D.ε * (a' / a))
                 nlinarith) h3
  have h1 : (m : ℝ) * D.ε * (a' / a) ≤ 1 / 10 ^ 5 :=
    le_trans (by have := mul_le_mul_of_nonneg_right hm2 (by positivity : 0 ≤ D.ε * (a' / a))
                 nlinarith) h2
  have h0 : D.ε * (a' / a) ≤ 1 / 10 ^ 5 :=
    le_trans (by have := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ D.ε * (a' / a))
                 nlinarith) h1
  have he : D.ε ≤ 1 / 10 ^ 5 :=
    le_trans (by have := mul_le_mul_of_nonneg_left hκ hε; nlinarith) h0
  exact ⟨haa', hκ, hspec, he, h0, h1, h2, h3⟩

/-- **Exact CG step lengths are at least $1/\lambda_{\max}$**: for positive definite
$\mathbf{H}$ with spectrum in $[l, l']$ and $\mathbf{r}_j \ne \mathbf{0}$, $\gamma_j \ge 1/l'$
(by conjugacy, $\mathbf{p}_j^{\mathsf{T}}\mathbf{H}\mathbf{p}_j \le
\mathbf{r}_j^{\mathsf{T}}\mathbf{H}\mathbf{r}_j$). -/
private theorem one_div_le_cgAlpha {m : Type*} [Fintype m] [DecidableEq m] {H : Matrix m m ℝ}
    (hH : H.PosDef) {l l' : ℝ} (hs : spectrum ℝ H ⊆ Set.Icc l l') (b : m → ℝ)
    (j : ℕ) (hr : (cgState H b 0 j).r ≠ 0) :
    1 / l' ≤ cgAlpha H (cgState H b 0 j) := by
  have hherm := hH.isHermitian
  have hT : Hᵀ = H := by
    have := hherm.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hsymm : ∀ u v : m → ℝ, u ⬝ᵥ (H *ᵥ v) = v ⬝ᵥ (H *ᵥ u) := fun u v => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  set r := (cgState H b 0 j).r
  set p := (cgState H b 0 j).p
  have hrpos : 0 < ‖WithLp.toLp 2 r‖ := by
    rcases (norm_nonneg (WithLp.toLp 2 r)).lt_or_eq with h | h
    · exact h
    · exact absurd (by simpa using h.symm) hr
  -- `‖p‖ ≥ ‖r‖ > 0`
  have hp : p ≠ 0 := by
    intro h0
    have heq := hH.norm_cgState_p_sq_eq b j
    have hsum : (‖WithLp.toLp 2 r‖ ^ 2)⁻¹ ≤
        ∑ i ∈ Finset.range (j + 1), (‖WithLp.toLp 2 (cgState H b 0 i).r‖ ^ 2)⁻¹ :=
      Finset.single_le_sum (f := fun i => (‖WithLp.toLp 2 (cgState H b 0 i).r‖ ^ 2)⁻¹)
        (fun i _ => by positivity) (Finset.self_mem_range_succ j)
    change ‖WithLp.toLp 2 p‖ ^ 2 = ‖WithLp.toLp 2 r‖ ^ 4 * _ at heq
    rw [h0, WithLp.toLp_zero, norm_zero] at heq
    have h4 : 0 < ‖WithLp.toLp 2 r‖ ^ 4 * (‖WithLp.toLp 2 r‖ ^ 2)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ ‖WithLp.toLp 2 r‖ ^ 4)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_eq_mul, pow_eq_zero_iff,
      norm_eq_zero] at heq
    rcases heq with h | h
    · exact hr (by simpa using h)
    · rw [h] at this
      linarith
  have hqp : 0 < p ⬝ᵥ (H *ᵥ p) := by
    have := hH.dotProduct_mulVec_pos hp
    simpa using this
  -- conjugacy: `pᵀHp ≤ rᵀHr`
  have hle : p ⬝ᵥ (H *ᵥ p) ≤ r ⬝ᵥ (H *ᵥ r) := by
    rcases j with _ | j
    · exact le_of_eq rfl
    · obtain ⟨c, hc⟩ : ∃ c : ℝ, p = r + c • (cgState H b 0 j).p := ⟨_, rfl⟩
      set q := (cgState H b 0 j).p
      have hconj : q ⬝ᵥ (H *ᵥ p) = 0 := by
        simpa using hH.star_cgState_p_dotProduct_mulVec_eq_zero (b := b) (x₀ := 0)
          (Nat.lt_succ_self j)
      have hq0 : 0 ≤ q ⬝ᵥ (H *ᵥ q) := by
        have := hH.posSemidef.dotProduct_mulVec_nonneg q
        simpa using this
      have e1 : p ⬝ᵥ (H *ᵥ p) = r ⬝ᵥ (H *ᵥ p) := by
        have : (r + c • q) ⬝ᵥ (H *ᵥ p) = r ⬝ᵥ (H *ᵥ p) := by
          rw [add_dotProduct, smul_dotProduct, hconj, smul_zero, add_zero]
        rwa [← hc] at this
      have e2 : r ⬝ᵥ (H *ᵥ p) = r ⬝ᵥ (H *ᵥ r) + c * (r ⬝ᵥ (H *ᵥ q)) := by
        rw [hc, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
          smul_eq_mul]
      have e3 : q ⬝ᵥ (H *ᵥ r) + c * (q ⬝ᵥ (H *ᵥ q)) = 0 := by
        rw [← hconj, hc, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
          smul_eq_mul]
      have e4 := hsymm r q
      have e5 : c * (q ⬝ᵥ (H *ᵥ r)) = -(c ^ 2 * (q ⬝ᵥ (H *ᵥ q))) := by
        linear_combination c * e3
      rw [e4, e5] at e2
      nlinarith [mul_nonneg (sq_nonneg c) hq0]
  have hrr := (quadForm_bounds hherm hs r).2
  have hl' : 0 < l' := by
    have := hherm
    nlinarith [(quadForm_bounds hherm hs p).2, sq_nonneg ‖WithLp.toLp 2 p‖,
      (quadForm_bounds hherm hs r).1]
  rw [cgAlpha, quadForm_def, star_trivial, RCLike.re_to_real, div_le_div_iff₀ hl' hqp]
  nlinarith

/-- The curvature certificate for any run (the content of
`NLAlib.CGRun.specNorm_mul_γ_mul_norm_p_sq_le`): no model needed. -/
private theorem specNorm_mul_γ_mul_norm_p_sq_le_aux {n m : ℕ} (D : CGRun n m) {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ D.A ⊆ Set.Icc a a')
    (hsmall : (m : ℝ) ^ 3 * D.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j < m) :
    specNorm D.A * D.γ j * ‖WithLp.toLp 2 (D.p j)‖ ^ 2 ≤ 21 / 20 * (a' / a) * D.ρ j ^ 2 := by
  obtain ⟨haa', hκ, hspec, he, hεκ, -⟩ := small_facts D ha hs hsmall
  have hε := D.ε_nonneg
  have hγ := D.γ_pos hj
  set P0 := ‖WithLp.toLp 2 (D.p j)‖ with hP0
  have hρ2 : 0 ≤ D.ρ j ^ 2 := sq_nonneg _
  have hRHS : 0 ≤ 21 / 20 * (a' / a) * D.ρ j ^ 2 := by positivity
  rcases (norm_nonneg (WithLp.toLp 2 (D.p j))).lt_or_eq with hpos | hzero
  swap
  · have : P0 = 0 := hP0.trans hzero.symm
    rw [this]; simpa using hRHS
  rw [← hP0] at hpos
  -- the curvature from below
  have hpAp := (quadForm_bounds D.isHermitian_A hs (D.p j)).1
  have hes := D.norm_es_le j hj
  have hes' : |D.p j ⬝ᵥ D.es j| ≤ D.ε * a' * P0 ^ 2 := by
    refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans ?_
    calc P0 * ‖WithLp.toLp 2 (D.es j)‖ ≤ P0 * (D.ε * specNorm D.A * P0) :=
          mul_le_mul_of_nonneg_left hes hpos.le
      _ ≤ P0 * (D.ε * a' * P0) := by gcongr
      _ = D.ε * a' * P0 ^ 2 := by ring
  have hs_norm : ‖WithLp.toLp 2 (D.s j)‖ ≤ (1 + D.ε) * a' * P0 := by
    rw [D.s_eq j hj, WithLp.toLp_add]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_toLp_mulVec_le D.A (D.p j)
    calc ‖WithLp.toLp 2 (D.A *ᵥ D.p j)‖ + ‖WithLp.toLp 2 (D.es j)‖
        ≤ specNorm D.A * P0 + D.ε * specNorm D.A * P0 := add_le_add h1 hes
      _ ≤ a' * P0 + D.ε * a' * P0 := by gcongr
      _ = (1 + D.ε) * a' * P0 := by ring
  have heμ : |D.eμ j| ≤ D.ε * (1 + D.ε) * a' * P0 ^ 2 := by
    refine (D.abs_eμ_le j hj).trans ?_
    calc D.ε * P0 * ‖WithLp.toLp 2 (D.s j)‖ ≤ D.ε * P0 * ((1 + D.ε) * a' * P0) := by gcongr
      _ = D.ε * (1 + D.ε) * a' * P0 ^ 2 := by ring
  have hεa' : D.ε * a' ≤ a / 10 ^ 5 := by
    have : D.ε * a' = D.ε * (a' / a) * a := by field_simp
    rw [this]
    nlinarith
  have hμ : (1 - 3 / 10 ^ 5) * a * P0 ^ 2 ≤ D.μ j := by
    rw [D.μ_eq j hj, D.s_eq j hj, dotProduct_add]
    have h1 := neg_abs_le (D.p j ⬝ᵥ D.es j)
    have h2 := neg_abs_le (D.eμ j)
    have hP2 : 0 ≤ P0 ^ 2 := sq_nonneg _
    have : D.ε * (1 + D.ε) * a' * P0 ^ 2 ≤ 2 * (D.ε * a') * P0 ^ 2 := by
      have : D.ε * (1 + D.ε) * a' ≤ 2 * (D.ε * a') := by nlinarith
      nlinarith
    nlinarith
  have hμpos : 0 < D.μ j := D.μ_pos j hj
  -- the step length from above
  have hγμ : D.γ j * D.μ j = D.ν j * (1 + D.eγ j) := by
    rw [D.γ_eq j hj]; field_simp
  have hν : D.ν j * (1 + D.eγ j) ≤ (1 + D.ε) ^ 2 * D.ρ j ^ 2 := by
    rw [D.ν_eq j hj.le]
    have h1 := (abs_le.mp (D.abs_θ_le j hj.le)).2
    have h2 := (abs_le.mp (D.abs_eγ_le j hj)).2
    have h3 := (abs_le.mp (D.abs_eγ_le j hj)).1
    have h4 := (abs_le.mp (D.abs_θ_le j hj.le)).1
    change D.ρ j ^ 2 * (1 + D.θ j) * (1 + D.eγ j) ≤ _
    have h5 : 0 ≤ 1 + D.eγ j := by linarith
    have : (1 + D.θ j) * (1 + D.eγ j) ≤ (1 + D.ε) ^ 2 := by nlinarith
    nlinarith
  have hkey : D.γ j * P0 ^ 2 * ((1 - 3 / 10 ^ 5) * a) ≤ (1 + D.ε) ^ 2 * D.ρ j ^ 2 := by
    calc D.γ j * P0 ^ 2 * ((1 - 3 / 10 ^ 5) * a) = D.γ j * ((1 - 3 / 10 ^ 5) * a * P0 ^ 2) := by
          ring
      _ ≤ D.γ j * D.μ j := mul_le_mul_of_nonneg_left hμ hγ.le
      _ ≤ _ := hγμ ▸ hν
  have hA : specNorm D.A * D.γ j * P0 ^ 2 ≤ a' * (D.γ j * P0 ^ 2) := by
    rw [← mul_assoc]; gcongr
  refine hA.trans ?_
  have hc : 0 < (1 - 3 / 10 ^ 5) * a := by positivity
  have hγP : D.γ j * P0 ^ 2 ≤ (1 + D.ε) ^ 2 * D.ρ j ^ 2 / ((1 - 3 / 10 ^ 5) * a) := by
    rw [le_div_iff₀ hc]; exact hkey
  calc a' * (D.γ j * P0 ^ 2) ≤ a' * ((1 + D.ε) ^ 2 * D.ρ j ^ 2 / ((1 - 3 / 10 ^ 5) * a)) := by
        gcongr; linarith
    _ = (a' / a) * ((1 + D.ε) ^ 2 / (1 - 3 / 10 ^ 5)) * D.ρ j ^ 2 := by
        field_simp
    _ ≤ (a' / a) * (21 / 20) * D.ρ j ^ 2 := by
        have hq : (1 + D.ε) ^ 2 / (1 - 3 / 10 ^ 5) ≤ 21 / 20 := by
          rw [div_le_iff₀ (by norm_num)]; nlinarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by positivity)) hρ2
    _ = 21 / 20 * (a' / a) * D.ρ j ^ 2 := by ring

/-- **The model from the a priori certificates**: with $\Pi^2 = 3.3\kappa$, $K = 1.05\kappa$,
$B = 1.6a'$ the a posteriori engine gives $4 \cdot 10^4m^3\varepsilon\kappa a'$. -/
private theorem frobNorm_le_of_apriori {n m : ℕ} (D : CGRun n m) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ D.A ⊆ Set.Icc a a')
    (hsmall : (m : ℝ) ^ 3 * D.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hP : ∀ i < m, ‖WithLp.toLp 2 (D.p i)‖ ^ 2 ≤ 33 / 10 * (a' / a) * D.ρ i ^ 2)
    (hK : ∀ i < m, specNorm D.A * D.γ i * ‖WithLp.toLp 2 (D.p i)‖ ^ 2 ≤
      21 / 20 * (a' / a) * D.ρ i ^ 2)
    (hB : ∀ i, i + 1 < m → D.lanczosβ (i + 1) ≤ 8 / 5 * a' ∧ D.δ i ≤ 8 / 5 * a' * D.γ i) :
    frobNorm (D.backwardH - D.dilatedH) ≤ 40000 * m ^ 3 * D.ε * (a' / a) * a' := by
  obtain ⟨haa', hκ, hspec, -⟩ := small_facts D ha hs hsmall
  set κ := a' / a with hκdef
  have hε := D.ε_nonneg
  have ha' : 0 < a' := ha.trans_le haa'
  set P := Real.sqrt (33 / 10 * κ) with hPdef
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hP2 : P ^ 2 = 33 / 10 * κ := Real.sq_sqrt (by positivity)
  have hP' : ∀ i < m, ‖WithLp.toLp 2 (D.p i)‖ ≤ P * D.ρ i := fun i hi => by
    have hρ : 0 ≤ D.ρ i := norm_nonneg _
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, hP2]
    exact hP i hi
  have h := D.frobNorm_backwardH_sub_dilatedH_le_of_certificates hP' hK hB
  refine h.trans ?_
  have hs0 : 0 ≤ specNorm D.A := specNorm_nonneg _
  have h1P : (1 + P) ^ 2 ≤ 86 / 10 * κ := by nlinarith [sq_nonneg (1 - P)]
  have hPK : 1 + P + 21 / 20 * κ ≤ 42 / 10 * κ := by nlinarith [sq_nonneg (1 - P)]
  have hsP : specNorm D.A * (1 + P) ^ 2 ≤ a' * (86 / 10 * κ) :=
    mul_le_mul hspec h1P (by positivity) ha'.le
  have hBκ : 8 / 5 * a' ≤ 8 / 5 * (κ * a') := by nlinarith
  have hf : 8 * D.ε * (specNorm D.A * (1 + P) ^ 2 + 8 / 5 * a') ≤
      8 * D.ε * (102 / 10 * (κ * a')) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have hp : 16 * (m : ℝ) * D.ε * (specNorm D.A * (1 + P) ^ 2 + 8 / 5 * a' *
      (1 + P + 21 / 20 * κ)) ≤ 16 * (m : ℝ) * D.ε * (1532 / 100 * (κ * a')) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 8 / 5 * a' * (1 + P + 21 / 20 * κ) ≤ 8 / 5 * a' * (42 / 10 * κ) :=
      mul_le_mul_of_nonneg_left hPK (by positivity)
    nlinarith
  unfold normalizedBackwardBound
  have hm3 : 0 ≤ (m : ℝ) ^ 3 := by positivity
  have hm2 : 0 ≤ (m : ℝ) ^ 2 := by positivity
  have := add_le_add (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 102 * (m : ℝ) ^ 3))
    (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 96 * (m : ℝ) ^ 2))
  refine this.trans ?_
  have hE : 0 ≤ (m : ℝ) ^ 3 * (D.ε * (κ * a')) := by positivity
  nlinarith

/-- **Weyl localisation from the a priori model bound**: under (H) the model is within $0.4a$ of
$\mathbf{I} \otimes \mathbf{A}$, so its spectrum is in $[a/2, a' + a/2]$. -/
private theorem spectrum_subset_of_frobNorm_le {n m : ℕ} (D : CGRun n m) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ D.A ⊆ Set.Icc a a')
    (hsmall : (m : ℝ) ^ 3 * D.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hc : frobNorm (D.backwardH - D.dilatedH) ≤ 40000 * m ^ 3 * D.ε * (a' / a) * a') :
    spectrum ℝ D.backwardH ⊆ Set.Icc (a / 2) (a' + a / 2) := by
  have hc' : 40000 * (m : ℝ) ^ 3 * D.ε * (a' / a) * a' ≤ a / 2 := by
    have : 40000 * (m : ℝ) ^ 3 * D.ε * (a' / a) * a' =
        40000 * ((m : ℝ) ^ 3 * D.ε * (a' / a) ^ 2) * a := by
      field_simp
    rw [this]
    nlinarith
  have h := NormalizedLanczosData.spectrum_backwardH_subset_Icc (D := D.toNormalizedLanczosData)
    (a := a) (a' := a') hs (hc.trans hc')
  exact h.trans (Set.Icc_subset_Icc (by linarith) le_rfl)

/-- The direction coefficient against the exact residual ratio, one-sided:
$0 \le \delta_i \le (1 + 4\varepsilon)\rho_{i+1}^2/\rho_i^2$. -/
private theorem δ_bounds {n m : ℕ} (D : CGRun n m) {i : ℕ} (hi : i < m) :
    0 ≤ D.δ i ∧ D.δ i ≤ (1 + 4 * D.ε) * (D.ρ (i + 1) ^ 2 / D.ρ i ^ 2) := by
  have h := abs_le.mp (D.abs_δ_sub_le hi)
  have hq : 0 ≤ D.ρ (i + 1) ^ 2 / D.ρ i ^ 2 := by positivity
  have hε : 4 * D.ε ≤ 1 := by
    have h1 := D.k_mul_ε_le
    have hm : (1 : ℝ) ≤ m := by exact_mod_cast D.k_pos
    nlinarith [D.ε_nonneg]
  constructor <;> nlinarith

/-- **One step of the direction recursion**: with $\lvert\mathbf{p}_i^{\mathsf{T}}
\mathbf{r}_{i+1}\rvert \le t\rho_i^2$, $0 \le t \le 1/10$,
$\|\mathbf{p}_{i+1}\|^2 \le (1 + 3t + 4\varepsilon + 2\varepsilon^2)(\rho_{i+1}^2 +
\delta_i^2\|\mathbf{p}_i\|^2)$. -/
private theorem norm_p_succ_sq_le {n m : ℕ} (D : CGRun n m) {i : ℕ} (hi : i < m) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 10) (hτ : |D.p i ⬝ᵥ D.r (i + 1)| ≤ t * D.ρ i ^ 2) :
    ‖WithLp.toLp 2 (D.p (i + 1))‖ ^ 2 ≤ (1 + 3 * t + 4 * D.ε + 2 * D.ε ^ 2) *
      (D.ρ (i + 1) ^ 2 + D.δ i ^ 2 * ‖WithLp.toLp 2 (D.p i)‖ ^ 2) := by
  obtain ⟨hδ0, hδ⟩ := δ_bounds D hi
  have hε := D.ε_nonneg
  have hε1 : D.ε ≤ 1 / 100 := by
    have h1 := D.k_mul_ε_le
    have hm : (1 : ℝ) ≤ m := by exact_mod_cast D.k_pos
    nlinarith
  set R := D.ρ (i + 1) with hR
  set Q := ‖WithLp.toLp 2 (D.p i)‖ with hQ
  set δ := D.δ i with hδdef
  set τ := D.p i ⬝ᵥ D.r (i + 1) with hτdef
  have hR0 : 0 ≤ R := norm_nonneg _
  have hQ0 : 0 ≤ Q := norm_nonneg _
  set u := R ^ 2 + δ ^ 2 * Q ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  set w := D.r (i + 1) + δ • D.p i with hw
  have hW2 : ‖WithLp.toLp 2 w‖ ^ 2 = R ^ 2 + 2 * δ * τ + δ ^ 2 * Q ^ 2 := by
    rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hR, ρ,
      EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hQ,
      EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hw, hτdef]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (D.r (i + 1)) (D.p i)]
    ring
  -- `δ|τ| ≤ (1 + 4ε) t R²`
  have hδτ : δ * |τ| ≤ (1 + 4 * D.ε) * t * R ^ 2 := by
    rcases (norm_nonneg (WithLp.toLp 2 (D.r i))).lt_or_eq with hρ | hρ
    · change 0 < D.ρ i at hρ
      have hρ2 : 0 < D.ρ i ^ 2 := by positivity
      calc δ * |τ| ≤ ((1 + 4 * D.ε) * (R ^ 2 / D.ρ i ^ 2)) * (t * D.ρ i ^ 2) :=
            mul_le_mul hδ hτ (abs_nonneg _) (by positivity)
        _ = (1 + 4 * D.ε) * t * R ^ 2 := by field_simp
    · change 0 = D.ρ i at hρ
      rw [← hρ] at hτ
      have : |τ| = 0 := le_antisymm (by simpa using hτ) (abs_nonneg _)
      rw [this, mul_zero]; positivity
  have hτl := neg_abs_le τ
  have hτu := le_abs_self τ
  have hW2le : ‖WithLp.toLp 2 w‖ ^ 2 ≤ (1 + 3 * t) * u := by
    rw [hW2]
    have : 2 * δ * τ ≤ 2 * (δ * |τ|) := by nlinarith
    have h5 : 2 * ((1 + 4 * D.ε) * t * R ^ 2) ≤ 3 * t * u := by
      have h6 : 0 ≤ t * R ^ 2 := mul_nonneg ht0 (sq_nonneg R)
      have h7 : 0 ≤ t * (δ ^ 2 * Q ^ 2) := mul_nonneg ht0 (by positivity)
      have h8 : D.ε * (t * R ^ 2) ≤ 1 / 100 * (t * R ^ 2) := mul_le_mul_of_nonneg_right hε1 h6
      rw [hu]
      nlinarith
    nlinarith
  set W := ‖WithLp.toLp 2 w‖ with hWdef
  have hW0 : 0 ≤ W := norm_nonneg _
  set E := ‖WithLp.toLp 2 (D.ep i)‖ with hEdef
  have hE : E ≤ D.ε * (R + δ * Q) := by
    have := D.norm_ep_le i hi
    rwa [abs_of_nonneg hδ0] at this
  have hE0 : 0 ≤ E := norm_nonneg _
  have hZ2 : (R + δ * Q) ^ 2 ≤ 2 * u := by nlinarith [sq_nonneg (R - δ * Q)]
  have hZ0 : 0 ≤ R + δ * Q := by positivity
  have hp : ‖WithLp.toLp 2 (D.p (i + 1))‖ ≤ W + E := by
    rw [D.p_succ i hi, WithLp.toLp_add]
    exact norm_add_le _ _
  have hp2 : ‖WithLp.toLp 2 (D.p (i + 1))‖ ^ 2 ≤ (W + E) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hp 2
  refine hp2.trans ?_
  have h2WE : 2 * W * E ≤ D.ε * (W ^ 2 + (R + δ * Q) ^ 2) := by
    have : W * E ≤ W * (D.ε * (R + δ * Q)) := mul_le_mul_of_nonneg_left hE hW0
    nlinarith [sq_nonneg (W - (R + δ * Q)), mul_nonneg hε (sq_nonneg (W - (R + δ * Q)))]
  have hE2 : E ^ 2 ≤ D.ε ^ 2 * (R + δ * Q) ^ 2 := by
    have := pow_le_pow_left₀ hE0 hE 2
    rwa [mul_pow] at this
  have h3 : D.ε * (W ^ 2 + (R + δ * Q) ^ 2) ≤ D.ε * (4 * u) := by
    apply mul_le_mul_of_nonneg_left _ hε
    nlinarith
  have h4 : D.ε ^ 2 * (R + δ * Q) ^ 2 ≤ D.ε ^ 2 * (2 * u) :=
    mul_le_mul_of_nonneg_left hZ2 (sq_nonneg _)
  have hexp : (W + E) ^ 2 = W ^ 2 + 2 * W * E + E ^ 2 := by ring
  have hrhs : (1 + 3 * t + 4 * D.ε + 2 * D.ε ^ 2) * u =
      (1 + 3 * t) * u + D.ε * (4 * u) + D.ε ^ 2 * (2 * u) := by ring
  rw [hexp, hrhs]
  linarith

/-- A power of a number close to $1$: $(1 + x)^j \le 11/10$ for $0 \le x \le 1$ and
$jx \le 1/11$. -/
private theorem one_add_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {j : ℕ}
    (hjx : (j : ℝ) * x ≤ 1 / 11) : (1 + x) ^ j ≤ 11 / 10 := by
  have h1 : 1 + (j : ℝ) * (-x) ≤ (1 + -x) ^ j := one_add_mul_le_pow (by linarith) j
  have h2 : (10 : ℝ) / 11 ≤ (1 - x) ^ j := by
    rw [sub_eq_add_neg]; linarith
  have h3 : (1 + x) ^ j * (1 - x) ^ j ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h4 : 0 ≤ (1 + x) ^ j := by positivity
  nlinarith

/-- **The unrolled direction recursion**: with $\lvert\mathbf{p}_i^{\mathsf{T}}
\mathbf{r}_{i+1}\rvert \le t\rho_i^2$ for $i < j$,
$\|\mathbf{p}_j\|^2 \le \Lambda^j\rho_j^4\sum_{i \le j}\rho_i^{-2}$,
$\Lambda = (1 + 3t + 4\varepsilon + 2\varepsilon^2)(1 + 4\varepsilon)^2$. -/
private theorem norm_p_sq_le_unroll {n m : ℕ} (D : CGRun n m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 10) {j : ℕ} (hj : j < m)
    (hτ : ∀ i < j, |D.p i ⬝ᵥ D.r (i + 1)| ≤ t * D.ρ i ^ 2) :
    ‖WithLp.toLp 2 (D.p j)‖ ^ 2 ≤ ((1 + 3 * t + 4 * D.ε + 2 * D.ε ^ 2) * (1 + 4 * D.ε) ^ 2) ^ j *
      D.ρ j ^ 4 * ∑ i ∈ Finset.range (j + 1), (D.ρ i ^ 2)⁻¹ := by
  have hε := D.ε_nonneg
  set c₁ := 1 + 3 * t + 4 * D.ε + 2 * D.ε ^ 2 with hc₁
  set Λ := c₁ * (1 + 4 * D.ε) ^ 2 with hΛ
  have hc₁1 : 1 ≤ c₁ := by rw [hc₁]; nlinarith
  have hΛc : c₁ ≤ Λ := by
    rw [hΛ]; nlinarith [sq_nonneg (1 + 4 * D.ε)]
  have hΛ1 : 1 ≤ Λ := hc₁1.trans hΛc
  induction j with
  | zero =>
    have hρ := D.ρ_pos hj
    simp only [pow_zero, one_mul, zero_add, Finset.range_one, Finset.sum_singleton]
    have : ‖WithLp.toLp 2 (D.p 0)‖ = D.ρ 0 := by simp [ρ, D.p_zero, D.r_zero]
    rw [this]
    field_simp
    exact le_rfl
  | succ j ih =>
    have hjm : j < m := Nat.lt_of_succ_lt hj
    have ih' := ih hjm (fun i hi => hτ i (hi.trans (Nat.lt_succ_self j)))
    have hstep := norm_p_succ_sq_le D hjm ht0 ht (hτ j (Nat.lt_succ_self j))
    obtain ⟨hδ0, hδ⟩ := δ_bounds D hjm
    have hρ := D.ρ_pos hjm
    have hR := D.ρ_pos hj
    set R := D.ρ (j + 1)
    set Sj := ∑ i ∈ Finset.range (j + 1), (D.ρ i ^ 2)⁻¹ with hSj
    have hS0 : 0 ≤ Sj := Finset.sum_nonneg fun i _ => by positivity
    have hδ2 : D.δ j ^ 2 ≤ (1 + 4 * D.ε) ^ 2 * (R ^ 2 / D.ρ j ^ 2) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hδ0 hδ 2
    have hQ : D.δ j ^ 2 * ‖WithLp.toLp 2 (D.p j)‖ ^ 2 ≤
        (1 + 4 * D.ε) ^ 2 * Λ ^ j * R ^ 4 * Sj := by
      calc D.δ j ^ 2 * ‖WithLp.toLp 2 (D.p j)‖ ^ 2
          ≤ ((1 + 4 * D.ε) ^ 2 * (R ^ 2 / D.ρ j ^ 2) ^ 2) * (Λ ^ j * D.ρ j ^ 4 * Sj) :=
            mul_le_mul hδ2 ih' (sq_nonneg _) (by positivity)
        _ = (1 + 4 * D.ε) ^ 2 * Λ ^ j * R ^ 4 * Sj := by
            field_simp
    rw [Finset.sum_range_succ, ← hSj]
    refine hstep.trans ?_
    have hR2 : R ^ 2 = R ^ 4 * (R ^ 2)⁻¹ := by field_simp
    have hΛj : c₁ ≤ Λ ^ (j + 1) := hΛc.trans (le_self_pow₀ hΛ1 (Nat.succ_ne_zero j))
    have hR4 : 0 ≤ R ^ 4 * (R ^ 2)⁻¹ := by positivity
    calc c₁ * (R ^ 2 + D.δ j ^ 2 * ‖WithLp.toLp 2 (D.p j)‖ ^ 2)
        ≤ c₁ * (R ^ 4 * (R ^ 2)⁻¹ + (1 + 4 * D.ε) ^ 2 * Λ ^ j * R ^ 4 * Sj) := by
          rw [← hR2]; gcongr
      _ = c₁ * (R ^ 4 * (R ^ 2)⁻¹) + Λ ^ (j + 1) * R ^ 4 * Sj := by
          rw [hΛ, pow_succ]; ring
      _ ≤ Λ ^ (j + 1) * (R ^ 4 * (R ^ 2)⁻¹) + Λ ^ (j + 1) * R ^ 4 * Sj := by
          gcongr
      _ = Λ ^ (j + 1) * R ^ 4 * (Sj + (R ^ 2)⁻¹) := by ring

/-! ### A priori certificates (the induction) -/

/-- $\Lambda^j \le 1.1$ for the growth factor of the unrolled direction recursion. -/
private theorem growth_pow_le {ε t : ℝ} {j : ℕ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 10 ^ 5)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 10) (hjt : (j : ℝ) * t ≤ 21 / 10 ^ 5)
    (hjε : (j : ℝ) * ε ≤ 1 / 10 ^ 5) :
    ((1 + 3 * t + 4 * ε + 2 * ε ^ 2) * (1 + 4 * ε) ^ 2) ^ j ≤ 11 / 10 := by
  set x := (1 + 3 * t + 4 * ε + 2 * ε ^ 2) * (1 + 4 * ε) ^ 2 - 1 with hxdef
  have hexp : x = 3 * t + 12 * ε + 50 * ε ^ 2 + 24 * (t * ε) + 80 * ε ^ 3 + 48 * (t * ε ^ 2) +
      32 * ε ^ 4 := by rw [hxdef]; ring
  have h1 : ε ^ 2 ≤ ε / 10 ^ 5 := by nlinarith
  have h2 : t * ε ≤ ε / 10 := by nlinarith
  have h3 : ε ^ 3 ≤ ε / 10 ^ 5 := by nlinarith [sq_nonneg ε]
  have h4 : t * ε ^ 2 ≤ ε / 10 ^ 5 := by nlinarith [mul_nonneg ht0 hε]
  have h5 : ε ^ 4 ≤ ε / 10 ^ 5 := by nlinarith [pow_nonneg hε 3]
  have hx0 : 0 ≤ x := by rw [hexp]; positivity
  have hx : x ≤ 3 * t + 15 * ε := by rw [hexp]; linarith
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hjx : (j : ℝ) * x ≤ 1 / 11 := by
    have := mul_le_mul_of_nonneg_left hx hj0
    nlinarith
  have := one_add_pow_le hx0 (by linarith) hjx
  rwa [hxdef, add_sub_cancel] at this

/-- The line-search defects at the steps before $j$, from the certificates P(j). -/
private theorem apriori_tau {a a' : ℝ} {j : ℕ} (hjk : j < k)
    (IH : ∀ i < j, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ 33 / 10 * (a' / a) * C.ρ i ^ 2 ∧
      specNorm C.A * C.γ i * ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ 21 / 20 * (a' / a) * C.ρ i ^ 2)
    (hκ : 0 ≤ a' / a) :
    ∀ i < j, |C.p i ⬝ᵥ C.r (i + 1)| ≤ 5 * (j : ℝ) * C.ε *
      (1 + Real.sqrt (33 / 10 * (a' / a)) + 21 / 20 * (a' / a)) * C.ρ i ^ 2 := by
  intro i hi
  have hj0 : 0 < j := by omega
  set P := Real.sqrt (33 / 10 * (a' / a)) with hPdef
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hP2 : P ^ 2 = 33 / 10 * (a' / a) := Real.sq_sqrt (by positivity)
  have hP' : ∀ i < j, ‖WithLp.toLp 2 ((C.take j hj0 hjk.le).p i)‖ ≤
      P * (C.take j hj0 hjk.le).ρ i := fun i hi => by
    have hρ : 0 ≤ C.ρ i := norm_nonneg _
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, hP2]
    exact (IH i hi).1
  have hK' : ∀ i < j, specNorm (C.take j hj0 hjk.le).A * (C.take j hj0 hjk.le).γ i *
      ‖WithLp.toLp 2 ((C.take j hj0 hjk.le).p i)‖ ^ 2 ≤
        21 / 20 * (a' / a) * (C.take j hj0 hjk.le).ρ i ^ 2 := fun i hi => (IH i hi).2
  have h := (C.take j hj0 hjk.le).abs_p_dotProduct_r_succ_le hP' hK' hi
  refine h.trans ?_
  change 5 * ((i : ℝ) + 1) * C.ε * (1 + P + 21 / 20 * (a' / a)) * C.ρ i ^ 2 ≤ _
  have hi1 : (i : ℝ) + 1 ≤ j := by exact_mod_cast hi
  have hq : 0 ≤ C.ε * (1 + P + 21 / 20 * (a' / a)) * C.ρ i ^ 2 := by
    have := C.ε_nonneg; positivity
  have := mul_le_mul_of_nonneg_right hi1 hq
  nlinarith

/-- The residual ratios at step $j$ from the model of the first $j$ steps. -/
private theorem apriori_S {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hjk : j < k)
    (IH : ∀ i < j, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ 33 / 10 * (a' / a) * C.ρ i ^ 2 ∧
      specNorm C.A * C.γ i * ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ 21 / 20 * (a' / a) * C.ρ i ^ 2 ∧
      C.lanczosβ (i + 1) ≤ 8 / 5 * a' ∧ C.δ i ≤ 8 / 5 * a' * C.γ i) :
    ∑ i ∈ Finset.range (j + 1), C.ρ j ^ 2 / C.ρ i ^ 2 ≤ 2 * (a' / a) + 1 := by
  have hκ : 1 ≤ a' / a := (small_facts C ha hs hsmall).2.1
  rcases Nat.eq_zero_or_pos j with h0 | hj0
  · subst h0
    have hρ := C.ρ_pos C.k_pos
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    rw [div_self (by positivity)]
    linarith
  · have hsm := C.hsmall_take hsmall hj0 hjk.le
    have hfrob := frobNorm_le_of_apriori (C.take j hj0 hjk.le) ha hs hsm
      (fun i hi => (IH i hi).1) (fun i hi => (IH i hi).2.1) (fun i hi => (IH i (by omega)).2.2)
    have hspecD := spectrum_subset_of_frobNorm_le (C.take j hj0 hjk.le) ha hs hsm hfrob
    have h := (C.take j hj0 hjk.le).sum_ρ_sq_div_ρ_sq_le (by positivity : 0 < a / 2) hspecD
      (le_refl j)
    have he : (a' + a / 2) / (a / 2) = 2 * (a' / a) + 1 := by field_simp
    rw [he] at h
    exact h

/-- **Step (Π) of the induction**: the direction certificate at step $j$ from P(j). -/

private theorem apriori_Pi {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hjk : j < k)
    (IH : ∀ i < j, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ 33 / 10 * (a' / a) * C.ρ i ^ 2 ∧
      specNorm C.A * C.γ i * ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ 21 / 20 * (a' / a) * C.ρ i ^ 2 ∧
      C.lanczosβ (i + 1) ≤ 8 / 5 * a' ∧ C.δ i ≤ 8 / 5 * a' * C.γ i) :
    ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ 33 / 10 * (a' / a) * C.ρ j ^ 2 := by
  obtain ⟨-, hκ, -, he, -, hk1, hk2, -⟩ := small_facts C ha hs hsmall
  have hε := C.ε_nonneg
  have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk.le
  have hj0R : (0 : ℝ) ≤ j := by positivity
  set P := Real.sqrt (33 / 10 * (a' / a)) with hPdef
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hP2 : P ^ 2 = 33 / 10 * (a' / a) := Real.sq_sqrt (by positivity)
  have hPK : 1 + P + 21 / 20 * (a' / a) ≤ 42 / 10 * (a' / a) := by
    nlinarith [sq_nonneg (1 - P)]
  set t := 5 * (j : ℝ) * C.ε * (1 + P + 21 / 20 * (a' / a)) with ht
  have ht0 : 0 ≤ t := by positivity
  have hjεκ : (j : ℝ) * C.ε * (a' / a) ≤ 1 / 10 ^ 5 := le_trans (by
    have := mul_le_mul_of_nonneg_right hjkR (by positivity : 0 ≤ C.ε * (a' / a))
    nlinarith) hk1
  have hj2 : (j : ℝ) ^ 2 * C.ε * (a' / a) ≤ 1 / 10 ^ 5 := le_trans (by
    have : (j : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ hj0R hjkR 2
    have := mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ C.ε * (a' / a))
    nlinarith) hk2
  have htle : t ≤ 21 * ((j : ℝ) * C.ε * (a' / a)) := by
    have := mul_le_mul_of_nonneg_left hPK (by positivity : 0 ≤ 5 * (j : ℝ) * C.ε)
    nlinarith
  have ht1 : t ≤ 1 / 10 := by nlinarith
  have hjt : (j : ℝ) * t ≤ 21 / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_left htle hj0R
    nlinarith
  have hjε : (j : ℝ) * C.ε ≤ 1 / 10 ^ 5 := le_trans (by
    have := mul_le_mul_of_nonneg_left hκ (by positivity : 0 ≤ (j : ℝ) * C.ε)
    nlinarith) hjεκ
  have hτ : ∀ i < j, |C.p i ⬝ᵥ C.r (i + 1)| ≤ t * C.ρ i ^ 2 :=
    C.apriori_tau hjk (fun i hi => ⟨(IH i hi).1, (IH i hi).2.1⟩) (by positivity)
  have hu := norm_p_sq_le_unroll C ht0 ht1 hjk hτ
  have hS := C.apriori_S ha hs hsmall hjk IH
  have hΛj := growth_pow_le hε he ht0 ht1 hjt hjε
  have hΛ0 : 0 ≤ ((1 + 3 * t + 4 * C.ε + 2 * C.ε ^ 2) * (1 + 4 * C.ε) ^ 2) ^ j := by positivity
  generalize (1 + 3 * t + 4 * C.ε + 2 * C.ε ^ 2) * (1 + 4 * C.ε) ^ 2 = Λ at hu hΛj hΛ0
  have hsum : C.ρ j ^ 4 * ∑ i ∈ Finset.range (j + 1), (C.ρ i ^ 2)⁻¹ =
      C.ρ j ^ 2 * ∑ i ∈ Finset.range (j + 1), C.ρ j ^ 2 / C.ρ i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [mul_assoc, hsum] at hu
  refine hu.trans ?_
  have hρ2 : 0 ≤ C.ρ j ^ 2 := sq_nonneg _
  calc Λ ^ j * (C.ρ j ^ 2 * ∑ i ∈ Finset.range (j + 1), C.ρ j ^ 2 / C.ρ i ^ 2)
      ≤ 11 / 10 * (C.ρ j ^ 2 * (2 * (a' / a) + 1)) :=
        mul_le_mul hΛj (mul_le_mul_of_nonneg_left hS hρ2)
          (mul_nonneg hρ2 (Finset.sum_nonneg fun i _ => div_nonneg hρ2 (sq_nonneg _)))
          (by norm_num)
    _ ≤ 33 / 10 * (a' / a) * C.ρ j ^ 2 := by
        have : 11 / 10 * (2 * (a' / a) + 1) ≤ 33 / 10 * (a' / a) := by linarith
        nlinarith

/-- **Step (B) of the induction**: the coefficient certificates at step $j$ from the model of
the first $j + 1$ steps. -/
private theorem apriori_B {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hjk : j < k)
    (hIH : ∀ i < j + 1, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ 33 / 10 * (a' / a) * C.ρ i ^ 2 ∧
      specNorm C.A * C.γ i * ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ 21 / 20 * (a' / a) * C.ρ i ^ 2)
    (hB : ∀ i < j, C.lanczosβ (i + 1) ≤ 8 / 5 * a' ∧ C.δ i ≤ 8 / 5 * a' * C.γ i) :
    C.lanczosβ (j + 1) ≤ 8 / 5 * a' ∧ C.δ j ≤ 8 / 5 * a' * C.γ j := by
  obtain ⟨haa', -, -, he, -⟩ := small_facts C ha hs hsmall
  have hε := C.ε_nonneg
  have ha' : 0 < a' := ha.trans_le haa'
  set D := C.take (j + 1) (Nat.succ_pos j) hjk
  have hsm := C.hsmall_take hsmall (Nat.succ_pos j) hjk
  have hfrob := frobNorm_le_of_apriori D ha hs hsm (fun i hi => (hIH i hi).1)
    (fun i hi => (hIH i hi).2) (fun i hi => hB i (by omega))
  have hspecD := spectrum_subset_of_frobNorm_le D ha hs hsm hfrob
  have hPD := posDef_of_spectrum D.isHermitian_backwardH (by positivity : 0 < a / 2) hspecD
  have hγ : cgAlpha D.backwardH (cgState D.backwardH D.dilatedRhs 0 j) = C.γ j :=
    D.cgAlpha_backwardH_of_posDef hPD (Nat.lt_succ_self j)
  have hr0 : ‖WithLp.toLp 2 (cgState D.backwardH D.dilatedRhs 0 j).r‖ = C.ρ j :=
    D.norm_cgState_backwardH_r_of_posDef hPD (Nat.le_succ j)
  have hr1 : ‖WithLp.toLp 2 (cgState D.backwardH D.dilatedRhs 0 (j + 1)).r‖ = C.ρ (j + 1) :=
    D.norm_cgState_backwardH_r_of_posDef hPD le_rfl
  have hρ := C.ρ_pos hjk
  have hγpos := C.γ_pos hjk
  have hrne : (cgState D.backwardH D.dilatedRhs 0 j).r ≠ 0 := by
    intro h0; rw [h0, WithLp.toLp_zero, norm_zero] at hr0; linarith
  have hγl := one_div_le_cgAlpha hPD hspecD D.dilatedRhs j hrne
  have hr := hPD.norm_cgState_r_succ_sq_div_le (by positivity : 0 < a / 2) hspecD
    D.dilatedRhs j
  rw [hγ] at hγl hr
  rw [hr0, hr1] at hr
  have hl' : 0 < a' + a / 2 := by positivity
  have hlγ : 1 ≤ (a' + a / 2) * C.γ j := by
    rw [div_le_iff₀ hl'] at hγl; linarith
  obtain ⟨-, hδ⟩ := δ_bounds C hjk
  constructor
  · have hβ : C.lanczosβ (j + 1) = C.ρ (j + 1) / (C.γ j * C.ρ j) := by
      simp [lanczosβ]
    have hρ1 : C.ρ (j + 1) ≤ (a' + a / 2) * C.γ j * C.ρ j := by
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
      calc C.ρ (j + 1) ^ 2 ≤ (a' + a / 2) * C.γ j * C.ρ j ^ 2 := hr
        _ ≤ (a' + a / 2) * C.γ j * C.ρ j ^ 2 * ((a' + a / 2) * C.γ j) :=
            le_mul_of_one_le_right (by positivity) hlγ
        _ = ((a' + a / 2) * C.γ j * C.ρ j) ^ 2 := by ring
    rw [hβ, div_le_iff₀ (by positivity)]
    have hγρ : 0 < C.γ j * C.ρ j := mul_pos hγpos hρ
    have : (a' + a / 2) * C.γ j * C.ρ j ≤ 8 / 5 * a' * (C.γ j * C.ρ j) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) hγρ.le
    linarith
  · calc C.δ j ≤ (1 + 4 * C.ε) * (C.ρ (j + 1) ^ 2 / C.ρ j ^ 2) := hδ
      _ ≤ (1 + 4 * C.ε) * ((a' + a / 2) * C.γ j) := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          exact hr
      _ ≤ 8 / 5 * a' * C.γ j := by
          have h1 : (1 + 4 * C.ε) * (a' + a / 2) ≤ 8 / 5 * a' := by nlinarith
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right h1 hγpos.le

/-- **The a priori induction** P(j), $j \le k$: under (H), for every step $i < j$,
$\|\mathbf{p}_i\|^2 \le 3.3\kappa\rho_i^2$, $\|\mathbf{A}\|_2\gamma_i\|\mathbf{p}_i\|^2 \le
1.05\kappa\rho_i^2$, $\beta_{i+1} \le 1.6a'$ and $\delta_i \le 1.6a'\gamma_i$. The single engine of
the a priori theorems of this file; it uses no a priori theorem.
Proof: `Nat.rec` on $j$; P(0) is vacuous. Step P(j) ⇒ P(j + 1), $j < k$. (Π, K at $j$.) For
$j = 0$ directly: $\mathbf{p}_0 = \mathbf{r}_0$, and $\mu_0 \ge (1 - 2.1\varepsilon\kappa)a
\|\mathbf{p}_0\|^2$ as in `NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc`. For $j \ge 1$: the
model of `C.take j` by `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le_of_certificates` with the
certificates of P(j) ($B$ is needed for $i + 1 < j$ only), so
$c_j \le 4 \cdot 10^4j^3\varepsilon\kappa a' \le 0.4a$ (design note §7 step 1:
$f \le 89\varepsilon\kappa a'$, $p \le 230j\varepsilon\kappa a'$) and its spectrum is in
$[a/2, a' + a/2]$ (`NLAlib.NormalizedLanczosData.spectrum_backwardH_subset_Icc`); then
`NLAlib.CGRun.sum_ρ_sq_div_ρ_sq_le` on `C.take j` at $j$ gives $S_j \le 2\kappa + 1 \le 3\kappa$,
and the recursion $\pi_j^2 \le (1+2\varepsilon)^2[1 + (1+\eta)^2(\rho_j/\rho_{j-1})^2\pi_{j-1}^2 +
2(1+\eta)\lvert\tau_{j-1}\rvert/\rho_{j-1}^2]$ (`NLAlib.CGRun.abs_p_dotProduct_r_succ_le`),
unrolled, gives $\pi_j^2 \le 1.1S_j$; $K$ at $j$ directly. (B at $j$.) The model of
`C.take (j + 1)` (certificates Π, K at $i \le j$, $B$ at $i < j$), reproduction
(`NLAlib.CGRun.cgAlpha_backwardH_of_posDef`, `NLAlib.CGRun.norm_cgState_backwardH_r_of_posDef`),
`Matrix.PosDef.norm_cgState_r_succ_sq_div_le` and `NLAlib.CGRun.abs_δ_sub_le` give
$\delta_j \le 1.04(a' + a/2)\gamma_j$;
$\beta_{j+1}^2 = (\delta_j/\gamma_j)\gamma_j^{-1}(1 + O(\varepsilon))$ with
$\gamma_j^{-1} = \tilde{\mathbf{p}}_j^{\mathsf{T}}\tilde{\mathbf{H}}\tilde{\mathbf{p}}_j/\rho_j^2
\le \lambda_{\max}$ (conjugacy, as in `Matrix.PosDef.norm_cgState_p_sq_le`) gives
$\beta_{j+1} \le 1.6a'$. The
smallness hypothesis of every prefix follows from $j^3 \le k^3$.
Difficulty: hard (the induction of the design). -/
private theorem aprioriCertificates {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j ≤ k) :
    ∀ i < j, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ 33 / 10 * (a' / a) * C.ρ i ^ 2 ∧
      specNorm C.A * C.γ i * ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ 21 / 20 * (a' / a) * C.ρ i ^ 2 ∧
      C.lanczosβ (i + 1) ≤ 8 / 5 * a' ∧ C.δ i ≤ 8 / 5 * a' * C.γ i := by
  induction j with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ j ih =>
    have hjk : j < k := hj
    have IH := ih hjk.le
    have hPi := C.apriori_Pi ha hs hsmall hjk IH
    have hK := specNorm_mul_γ_mul_norm_p_sq_le_aux C ha hs hsmall hjk
    have hIH : ∀ i < j + 1, ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ 33 / 10 * (a' / a) * C.ρ i ^ 2 ∧
        specNorm C.A * C.γ i * ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤
          21 / 20 * (a' / a) * C.ρ i ^ 2 := fun i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact ⟨(IH i hi).1, (IH i hi).2.1⟩
      · subst hi; exact ⟨hPi, hK⟩
    have hB := C.apriori_B ha hs hsmall hjk hIH (fun i hi => (IH i hi).2.2)
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact IH i hi
    · subst hi; exact ⟨hPi, hK, hB⟩

/-- **Directions against residuals, a priori**: under (H), $\|\mathbf{p}_j\|^2 \le
3.3\kappa\|\mathbf{r}_j\|^2$ for $j < k$, $\kappa = a'/a$. [StrakosTichy2002, (9.13)] has
$\|\mathbf{p}_j\|/\|\mathbf{r}_j\| \le 1 + j\kappa^{1/2}$ from an imported monotonicity.
Proof: the private induction `aprioriCertificates` of this file at $j = k$ (the note, §7). Not
through `NLAlib.CGRun.cgAlpha_backwardH` or `NLAlib.CGRun.spectrum_backwardH_subset_Icc`, which
depend on this theorem. Difficulty: easy given the induction. -/
theorem norm_p_sq_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ 33 / 10 * (a' / a) * C.ρ j ^ 2 := by
  sorry

/-- **The curvature certificate, a priori**: under (H),
$\|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2 \le 1.05\kappa\rho_j^2$, $j < k$.
Proof: $\gamma_j = \nu_j/\mu_j(1 + \eta)$ with
$\mu_j \ge (1 - 2.1\varepsilon\kappa)a\|\mathbf{p}_j\|^2$
(as in `NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc`), $\|\mathbf{A}\|_2 \le a'$. No model
needed; also the $K$ part of the private induction `aprioriCertificates`. Difficulty: easy. -/
theorem specNorm_mul_γ_mul_norm_p_sq_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {j : ℕ} (hj : j < k) :
    specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ 21 / 20 * (a' / a) * C.ρ j ^ 2 := by
  sorry

/-- **The off-diagonal coefficients, a priori**: under (H), $\beta_{j+1} =
\rho_{j+1}/(\gamma_j\rho_j) \le 1.6a'$, $j < k$.
Proof: the private induction `aprioriCertificates` of this file at $j = k$; there
$\beta_{j+1} \le 1.04\lambda_{\max}(\tilde{\mathbf{H}}_{j+1}) \le 1.6a'$ for the model of
`C.take (j + 1)`, built by the a posteriori engine. Difficulty: easy given the induction. -/
theorem lanczosβ_succ_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j < k) :
    C.lanczosβ (j + 1) ≤ 8 / 5 * a' := by
  sorry

/-- **The coefficient ratio, a priori**: under (H), $\delta_j \le 1.6a'\gamma_j$, $j < k$.
Proof: the private induction `aprioriCertificates` of this file at $j = k$; there
`Matrix.PosDef.norm_cgState_r_succ_sq_div_le` on the model of `C.take (j + 1)`, which
reproduces $\gamma_j$ and $\rho_j, \rho_{j+1}$ (`NLAlib.CGRun.cgAlpha_backwardH_of_posDef`,
`NLAlib.CGRun.norm_cgState_backwardH_r_of_posDef`), and `NLAlib.CGRun.abs_δ_sub_le`.
Difficulty: easy given the induction. -/
theorem δ_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j < k) :
    C.δ j ≤ 8 / 5 * a' * C.γ j := by
  sorry

/-! ### The backward model -/

/-- **The a priori backward model of finite-precision CG**: for spectrum in $[a, a']$, $a > 0$,
$\kappa = a'/a$, and (H) $k^3\varepsilon\kappa^2 \le 10^{-5}$,
$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{A}\|_{\mathsf{F}} \le
4 \cdot 10^4\,k^3\,\varepsilon\,\kappa\,a' .$$
No printed source. [Greenbaum1989] states the model for perturbed recurrences, with a
perturbation of order $\varepsilon^{1/4}$, and does not bound the perturbation terms of CG in
terms of $\varepsilon$ [MeurantStrakos2006, §5.2]; [GreenbaumLiuChen2021] derive the terms and
check them numerically.
Valid for $k \le (10^{-5}/(\varepsilon\kappa^2))^{1/3}$ only (about $k \le 30$–$100$ in double
precision for $\kappa = 10$; vacuous for $\kappa = 10^3$ at practical sizes); then the bound is
at most $0.4a$.
Proof: `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le_of_certificates` with
$1 + \Pi \le 1 + 1.82\sqrt{\kappa}$, $K \le 1.05\kappa$, $B \le 1.6a'$, $\|\mathbf{A}\|_2 \le a'$
(`NLAlib.CGRun.norm_p_sq_le`, `NLAlib.CGRun.specNorm_mul_γ_mul_norm_p_sq_le`,
`NLAlib.CGRun.lanczosβ_succ_le`, `NLAlib.CGRun.δ_le`):
$f \le 89\varepsilon\kappa a'$, $p \le 16k\varepsilon(8 + 1.6 \cdot 3.9)\kappa a' \le
230k\varepsilon\kappa a'$, and $102 \cdot 89 + 96 \cdot 230 = 31158 \le 4 \cdot 10^4$ (a margin of
$28\%$ for the re-derivation of the constants of Lemmas A and B). Difficulty: easy given the
certificates. -/
theorem frobNorm_backwardH_sub_dilatedH_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    frobNorm (C.backwardH - C.dilatedH) ≤ 40000 * k ^ 3 * C.ε * (a' / a) * a' := by
  sorry

/-- **The model is positive definite with condition number at most $2\kappa + 1$**: under (H)
its spectrum lies in $[a/2, a' + a/2]$.
Proof: `NLAlib.NormalizedLanczosData.spectrum_backwardH_subset_Icc` and
`NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le`, $4 \cdot 10^4k^3\varepsilon\kappa a' =
4 \cdot 10^4(k^3\varepsilon\kappa^2)a \le 0.4a$ by (H). Difficulty: easy. -/
theorem spectrum_backwardH_subset_Icc {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    spectrum ℝ C.backwardH ⊆ Set.Icc (a / 2) (a' + a / 2) := by
  sorry

/-- **Exact CG on the model computes the computed step lengths**: under (H), for $j < k$,
the step length of `NLAlib.cgState` on $(\tilde{\mathbf{H}}, (\mathbf{b}, \mathbf{0}, \dots))$
from $\mathbf{0}$ is $\gamma_j$.
Proof: `NLAlib.CGRun.cgAlpha_backwardH_of_posDef`, positive definiteness from
`NLAlib.CGRun.spectrum_backwardH_subset_Icc`. Difficulty: easy. -/
theorem cgAlpha_backwardH {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j < k) :
    cgAlpha C.backwardH (cgState C.backwardH C.dilatedRhs 0 j) = C.γ j := by
  sorry

/-- **Exact CG on the model has the computed residual norms**: under (H), for $j \le k$,
$\|\tilde{\mathbf{r}}_j\| = \|\mathbf{r}_j\|$.
Proof: `NLAlib.CGRun.norm_cgState_backwardH_r_of_posDef`, as `NLAlib.CGRun.cgAlpha_backwardH`.
Difficulty: easy. -/
theorem norm_cgState_backwardH_r {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (cgState C.backwardH C.dilatedRhs 0 j).r‖ = C.ρ j := by
  sorry

/-- **Residual ratios of the run, a priori**: under (H), $\|\mathbf{r}_j\| \le
\sqrt{3\kappa}\,\|\mathbf{r}_i\|$ for $i \le j \le k$ (the computed residual norms are those of
exact CG on a matrix of condition number at most $2\kappa + 1$). This is [StrakosTichy2002,
(7.20)] with the imported monotonicity replaced by the model.
Proof: `Matrix.PosDef.norm_cgState_r_le` on the model, `NLAlib.CGRun.norm_cgState_backwardH_r`,
$(a' + a/2)/(a/2) \le 3\kappa$. Difficulty: easy. -/
theorem ρ_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ k) :
    C.ρ j ≤ Real.sqrt (3 * (a' / a)) * C.ρ i := by
  sorry

/-- **The computed residual norms converge at the Chebyshev rate** of the widened interval:
under (H), with $\kappa_c = 2\kappa + 1$, for $j \le k$,
$$\|\mathbf{r}_j\| \le 2\sqrt{\kappa_c}\Bigl(\frac{\sqrt{\kappa_c} - 1}{\sqrt{\kappa_c} + 1}\Bigr)^j
\|\mathbf{b}\| .$$
No printed source in this form; the qualitative statement is [Greenbaum1989] with
[MeurantStrakos2006, §5.2]. Valid for $k$ with (H), i.e. $k \lesssim (\varepsilon\kappa^2)^{-1/3}$.
Proof: `Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow` on the model with
spectrum in $[a/2, a' + a/2]$,
$\|\tilde{\mathbf{r}}_j\|^2 \le (a' + a/2)\|\tilde{\mathbf{e}}_j\|^2$,
$\|\tilde{\mathbf{e}}_0\|^2 \le 2\|\mathbf{b}\|^2/a$, and `NLAlib.CGRun.norm_cgState_backwardH_r`.
Difficulty: easy. -/
theorem ρ_le_chebyshev {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j ≤ k) :
    C.ρ j ≤ 2 * Real.sqrt (2 * (a' / a) + 1) *
      ((Real.sqrt (2 * (a' / a) + 1) - 1) / (Real.sqrt (2 * (a' / a) + 1) + 1)) ^ j *
        ‖WithLp.toLp 2 C.b‖ := by
  sorry

/-! ### Errors of exact CG on the model, in the computed quantities -/

/-- **The model's error decrements are the computed estimator**: under (H), for
$\tilde{\mathbf{H}}\tilde{\mathbf{x}}_\star = (\mathbf{b}, \mathbf{0}, \dots)$ and $j + d \le k$,
$$\|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_j\|_{\tilde{\mathbf{H}}}^2 -
\|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_{j+d}\|_{\tilde{\mathbf{H}}}^2 =
\sum_{i=j}^{j+d-1}\gamma_i\|\mathbf{r}_i\|^2,$$
exactly, with the computed $\gamma_i$ and the norms of the computed residuals: the estimator
$\nu_{j,d}$ of [StrakosTichy2002, (4.9), (10.7)] is exact for the model.
Proof: `Matrix.PosDef.re_quadForm_sub_cgIterate_sub_re_quadForm_sub_cgIterate_succ` on the
model, summed, with `NLAlib.CGRun.cgAlpha_backwardH` and `NLAlib.CGRun.norm_cgState_backwardH_r`.
Difficulty: easy. -/
theorem quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n × Fin (k + 1) → ℝ} (hxs : C.backwardH *ᵥ xs = C.dilatedRhs) {j d : ℕ}
    (hjd : j + d ≤ k) :
    quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 j) -
        quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 (j + d)) =
      ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2 := by
  sorry

/-- **The model's error is a Gauss quadrature error of the computed tridiagonal matrix**:
under (H), $\|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_k\|_{\tilde{\mathbf{H}}}^2 =
\|\tilde{\mathbf{x}}_\star\|_{\tilde{\mathbf{H}}}^2 - \sum_{j<k}\gamma_j\|\mathbf{r}_j\|^2$, and
the sum is $\|\mathbf{b}\|^2(\mathbf{T}_k^{-1})_{00}$ for $\mathbf{T}_k$ = `cgTridiagonal C.γ C.ρ k`
(`NLAlib.sq_mul_inv_cgTridiagonal_zero_zero`): the identity
$\|\mathbf{x} - \mathbf{x}_k\|_{\mathbf{A}}^2 = \|\mathbf{r}_0\|^2[(\mathbf{T}_n^{-1})_{11} -
(\mathbf{T}_k^{-1})_{11}]$ of [MeurantStrakos2006, (3.17)] holds for the model with the
computed $\mathbf{T}_k$ and
$\tilde{\mathbf{v}}^{\mathsf{T}}\tilde{\mathbf{H}}^{-1}\tilde{\mathbf{v}}$
in place of $(\mathbf{T}_n^{-1})_{11}$.
Proof: `NLAlib.CGRun.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate` at
$j = 0$, $d = k$. Difficulty: easy. -/
theorem quadForm_backwardH_sub_cgIterate_eq {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n × Fin (k + 1) → ℝ} (hxs : C.backwardH *ᵥ xs = C.dilatedRhs) :
    quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 k) =
      quadForm C.backwardH xs - ∑ j ∈ Finset.range k, C.γ j * C.ρ j ^ 2 := by
  sorry

/-- **The model's initial error is the true one up to the model distance**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $\tilde{\mathbf{H}}\tilde{\mathbf{x}}_\star =
(\mathbf{b}, \mathbf{0}, \dots)$, with $c = 4 \cdot 10^4k^3\varepsilon\kappa a'$,
$$\bigl\lvert\|\tilde{\mathbf{x}}_\star\|_{\tilde{\mathbf{H}}}^2 -
\|\mathbf{x}_\star\|_{\mathbf{A}}^2\bigr\rvert \le 2\|\mathbf{b}\|^2c/a^2 .$$
The start of the model is exactly $\mathbf{b}/\|\mathbf{b}\|$ in the first block
($\mathbf{r}_0 = \mathbf{b}$ is not rounded), so the comparison is with the true problem.
Proof:
$\tilde{\mathbf{b}}^{\mathsf{T}}(\tilde{\mathbf{H}}^{-1} - \hat{\mathbf{H}}^{-1})\tilde{\mathbf{b}}$
and the resolvent identity, $\|\hat{\mathbf{H}}^{-1}\|_2 \le 1/a$,
$\|\tilde{\mathbf{H}}^{-1}\|_2 \le 2/a$, $\|\mathbf{\Delta}\|_2 \le c$. Difficulty: easy. -/
theorem abs_quadForm_backwardH_sub_quadForm_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n × Fin (k + 1) → ℝ} (hxs : C.backwardH *ᵥ xs = C.dilatedRhs) {x : Fin n → ℝ}
    (hx : C.A *ᵥ x = C.b) :
    |quadForm C.backwardH xs - quadForm C.A x| ≤
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (40000 * k ^ 3 * C.ε * (a' / a) * a') / a ^ 2 := by
  sorry

/-- **The model's error at step $k$ in the computed quantities**: under (H),
$$\Bigl\lvert\|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_k\|_{\tilde{\mathbf{H}}}^2 -
\Bigl(\|\mathbf{x}_\star\|_{\mathbf{A}}^2 - \sum_{j<k}\gamma_j\|\mathbf{r}_j\|^2\Bigr)\Bigr\rvert
\le 2\|\mathbf{b}\|^2c/a^2,\qquad c = 4 \cdot 10^4k^3\varepsilon\kappa a' .$$
The computed run's own error $\|\mathbf{x}_\star - \mathbf{x}_k\|_{\mathbf{A}}$ is not covered:
see the note (§9, next round).
Proof: `NLAlib.CGRun.quadForm_backwardH_sub_cgIterate_eq` and
`NLAlib.CGRun.abs_quadForm_backwardH_sub_quadForm_le`. Difficulty: easy. -/
theorem abs_quadForm_backwardH_sub_cgIterate_sub_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n × Fin (k + 1) → ℝ} (hxs : C.backwardH *ᵥ xs = C.dilatedRhs) {x : Fin n → ℝ}
    (hx : C.A *ᵥ x = C.b) :
    |quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 k) -
        (quadForm C.A x - ∑ j ∈ Finset.range k, C.γ j * C.ρ j ^ 2)| ≤
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (40000 * k ^ 3 * C.ε * (a' / a) * a') / a ^ 2 := by
  sorry

end CGRun

end NLAlib
