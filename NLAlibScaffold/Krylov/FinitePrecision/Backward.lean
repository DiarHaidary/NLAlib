/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.Paige
public import NLAlibScaffold.Krylov.FinitePrecision.Dilation
public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# A backward model for finite-precision Lanczos

The computed tridiagonal matrix of a run `L : NLAlib.LanczosRun n k` is exactly what $k$ steps of
exact Lanczos produce on a symmetric matrix $\tilde{\mathbf{H}}$ of dimension $n(k+1)$ that is
close to $\mathbf{I}_{k+1} \otimes \mathbf{H}$, from a starting vector whose spectral weights
with respect to $\mathbf{I}_{k+1} \otimes \mathbf{H}$ are those of the normalised
$\bar{\mathbf{v}}_1$ with respect to $\mathbf{H}$ (a Greenbaum-type backward model, with a
perturbation of order $k^4\varepsilon\|\mathbf{H}\|_2$).

The construction: normalise the computed vectors (`NLAlib.LanczosRun.normalized`, whose local
errors stay of order $j\varepsilon\|\mathbf{H}\|_2$); dilate them to orthonormal vectors
(`NLAlib.orthonormalDilation`), which satisfy the computed recurrence with the computed
coefficients up to a
residual $\hat{\mathbf{E}}$ (`NLAlib.LanczosRun.dilatedResidual`), controlled through the Gram
commutator of the normalised vectors; remove the residual by the symmetric perturbation
$\boldsymbol{\Delta} = -\hat{\mathbf{E}}\hat{\mathbf{V}}_k^{\mathsf{T}} -
\hat{\mathbf{V}}_k\hat{\mathbf{E}}^{\mathsf{T}}(\mathbf{I} - \hat{\mathbf{V}}_k
\hat{\mathbf{V}}_k^{\mathsf{T}})$.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `sec:backward`, `lem:normalized-errors`, `cor:normalized-commutator`,
`lem:exchange`, `lem:dilated-recurrence`, `thm:greenbaum`; [Greenbaum1989] for the original
model (perturbation of order $\varepsilon^{1/4}$), [Paige2010] for the augmented model of
dimension $n + k$.

## Main definitions

* `NLAlib.LanczosRun.normalizedV`, `NLAlib.LanczosRun.normalized`: the normalised run.
* `NLAlib.LanczosRun.dilatedH`, `NLAlib.LanczosRun.dilatedBasisSucc`,
  `NLAlib.LanczosRun.dilatedBasis`, `NLAlib.LanczosRun.dilatedStart`,
  `NLAlib.LanczosRun.dilatedResidual`: the dilated recurrence.
* `NLAlib.LanczosRun.backwardPerturbation`, `NLAlib.LanczosRun.backwardH`: the backward model.

## Main results

* `NLAlib.LanczosRun.frobNorm_dilatedResidual_le`: the dilated recurrence.
* `NLAlib.LanczosRun.backwardH_mul_dilatedBasis`,
  `NLAlib.LanczosRun.frobNorm_backwardH_sub_dilatedH_le`: the backward model.
* `NLAlib.lanczosState_eq_of_orthonormal_recurrence`,
  `NLAlib.lanczosState_beta_eq_of_orthonormal_recurrence`: an orthonormal three-term recurrence
  is the
  Lanczos recurrence.
* `NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`: exact Lanczos on the model
  computes $\mathbf{T}_k$.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-! ### Exact Lanczos from an orthonormal three-term recurrence -/

/-- One step of the Lanczos recurrence on an orthonormal three-term recurrence: from the state
$(\mathbf{u}_j, \mathbf{u}_{j+1}, \beta_j)$ the coefficient is $\alpha_{j+1}$ and the step
produces $\beta_{j+1}$ and the vector $\beta_{j+1}^{-1}(\beta_{j+1}\mathbf{u}_{j+2})$. -/
private theorem lanczosStep_of_orthonormal_recurrence {ι : Type*} [Fintype ι]
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
needed. [Saad2011, §6.6] for the exact recurrence.
Proof: induction on $j$ through `NLAlib.lanczosStep`; orthonormality gives the coefficient,
$\beta_{j+1} = \|\beta_{j+1}\mathbf{u}_{j+2}\|$ and the next vector; moderate. -/
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
$\beta_0 = 0$, $\beta_j > 0$ for $1 \le j < k$ and $\beta_k \ge 0$.
Proof: the last step of the induction; easy. -/
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

/-! ### Leading blocks of upper triangular matrices -/

/-- Dropping the last column of $\mathbf{B}\mathbf{X}$, for $\mathbf{X}$ upper triangular, is
$\mathbf{B}$ without its last column times the leading block of $\mathbf{X}$. -/
private theorem submatrix_castSucc_mul {p : Type*} {m : ℕ} (B : Matrix p (Fin (m + 1)) ℝ)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hX : X.IsUpperTriangular) :
    (B * X).submatrix id Fin.castSucc =
      B.submatrix id Fin.castSucc * X.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [Matrix.submatrix_apply, id, Matrix.mul_apply]
  rw [Fin.sum_univ_castSucc,
    show X (Fin.last m) (Fin.castSucc j) = 0 from hX (Fin.castSucc_lt_last j), mul_zero, add_zero]

/-- The leading block of a product with an upper triangular right factor is the product of the
leading blocks. -/
private theorem submatrix_castSucc_mul_castSucc {m : ℕ}
    (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hY : Y.IsUpperTriangular) :
    (X * Y).submatrix Fin.castSucc Fin.castSucc =
      X.submatrix Fin.castSucc Fin.castSucc * Y.submatrix Fin.castSucc Fin.castSucc := by
  have h := submatrix_castSucc_mul X hY
  ext i j
  have := congrFun (congrFun h (Fin.castSucc i)) j
  simpa only [Matrix.submatrix_apply, id, Matrix.mul_apply] using this

/-- Block $r$ of $(\mathbf{I} \otimes \mathbf{H})\mathbf{M}$ is $\mathbf{H}$ times block $r$ of
$\mathbf{M}$. -/
private theorem submatrix_blockDiagonal_mul {n m : ℕ} {p : Type*}
    (H : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin n × Fin m) p ℝ) (r : Fin m) :
    (Matrix.blockDiagonal (fun _ : Fin m => H) * M).submatrix (fun i => (i, r)) id =
      H * M.submatrix (fun i => (i, r)) id := by
  ext i j
  simp only [Matrix.submatrix_apply, id, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The squared Frobenius norm of a matrix with rows indexed by blocks is the sum over the
blocks. -/
private theorem frobNorm_sq_eq_sum_submatrix {n m : ℕ} {p : Type*} [Fintype p]
    (M : Matrix (Fin n × Fin m) p ℝ) :
    frobNorm M ^ 2 = ∑ r, frobNorm (M.submatrix (fun i => (i, r)) id) ^ 2 := by
  simp only [frobNorm_sq_eq_sum_sq, Fintype.sum_prod_type, Matrix.submatrix_apply, id]
  exact Finset.sum_comm

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-! ### The normalised run -/

/-- The **normalised Lanczos vectors** $\bar{\mathbf{v}}_j = \mathbf{v}_j/\|\mathbf{v}_j\|$
($\bar{\mathbf{v}}_0 = \mathbf{0}$); at a terminal last step ($\beta_k = 0$) the vector
$\bar{\mathbf{v}}_{k+1}$, which does not enter the recurrence, is taken to be
$\bar{\mathbf{v}}_1$. -/
noncomputable def normalizedV (j : ℕ) : Fin n → ℝ :=
  if j = k + 1 ∧ L.β k = 0 then ‖WithLp.toLp 2 (L.v 1)‖⁻¹ • L.v 1
  else ‖WithLp.toLp 2 (L.v j)‖⁻¹ • L.v j

/-- The **normalised run**: the computed coefficients with the normalised vectors. -/
noncomputable def normalized : LanczosData n k where
  H := L.H
  v := L.normalizedV
  α := L.α
  β := L.β
  transpose_H := L.transpose_H
  k_pos := L.k_pos
  v_zero := by
    have h : ¬(0 = k + 1 ∧ L.β k = 0) := fun h => by omega
    simp only [normalizedV, if_neg h, L.v_zero, smul_zero]
  β_zero := L.β_zero

/-- The computed vectors up to step $k$ are nonzero: $\|\mathbf{v}_j\| > 0$ for
$1 \le j \le k$. -/
theorem norm_v_pos {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) : 0 < ‖WithLp.toLp 2 (L.v j)‖ := by
  have h := (abs_le.mp (L.abs_norm_v_sq_sub_one_le j h1 h2)).1
  have hε := L.ε_le
  by_contra h0
  have : ‖WithLp.toLp 2 (L.v j)‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
  rw [this] at h
  linarith

/-- The next vector is nonzero when the last step is not terminal. -/
theorem norm_v_succ_pos (hβ : L.β k ≠ 0) : 0 < ‖WithLp.toLp 2 (L.v (k + 1))‖ := by
  have h := (abs_le.mp (L.abs_norm_v_succ_sq_sub_one_le hβ)).1
  have hε := L.ε_le
  by_contra h0
  have : ‖WithLp.toLp 2 (L.v (k + 1))‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
  rw [this] at h
  linarith

/-- The vector after step $j < k$ is nearly unit when $\beta_{j+1} \neq 0$. -/
theorem abs_norm_v_add_two_sq_sub_one_le {j : ℕ} (hj : j < k) (hβ : L.β (j + 1) ≠ 0) :
    |‖WithLp.toLp 2 (L.v (j + 2))‖ ^ 2 - 1| ≤ L.ε := by
  rcases (show j + 1 < k ∨ j + 1 = k by omega) with h | h
  · exact L.abs_norm_v_sq_sub_one_le (j + 2) (by omega) (by omega)
  · subst h
    exact L.abs_norm_v_succ_sq_sub_one_le hβ

/-- Away from the terminal exception, $\bar{\mathbf{v}}_j = \mathbf{v}_j/\|\mathbf{v}_j\|$. -/
theorem normalizedV_of_le {j : ℕ} (hj : j ≤ k) :
    L.normalizedV j = ‖WithLp.toLp 2 (L.v j)‖⁻¹ • L.v j := by
  rw [normalizedV, if_neg (fun h => by omega)]

/-- $\beta_{j+1}\bar{\mathbf{v}}_{j+2} = \beta_{j+1}\mathbf{v}_{j+2}/\|\mathbf{v}_{j+2}\|$ for every
$j$ (at a terminal step both sides vanish). -/
theorem β_smul_normalizedV (j : ℕ) :
    L.β (j + 1) • L.normalizedV (j + 2) =
      L.β (j + 1) • (‖WithLp.toLp 2 (L.v (j + 2))‖⁻¹ • L.v (j + 2)) := by
  unfold normalizedV
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    rw [show j + 1 = k by omega, h2, zero_smul, zero_smul]
  · rfl

/-- Ratios of nearly unit lengths: if $\lvert a^2 - 1\rvert \le \varepsilon$ and
$\lvert b^2 - 1\rvert \le \varepsilon$ with $a, b \ge 0$ and $\varepsilon \le 1/100$, then
$\lvert b/a - 1\rvert \le 2\varepsilon$ and $a \ge 99/100$. -/
private theorem nearUnit {a b ε : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hε : ε ≤ 1 / 100)
    (ha : |a ^ 2 - 1| ≤ ε) (hb : |b ^ 2 - 1| ≤ ε) : 99 / 100 ≤ a ∧ |b / a - 1| ≤ 2 * ε := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have ha1 : 99 / 100 ≤ a := by nlinarith
  have hb1 : 99 / 100 ≤ b := by nlinarith
  refine ⟨ha1, ?_⟩
  have hapos : 0 < a := by linarith
  rw [show b / a - 1 = (b - a) / a by field_simp, abs_div, abs_of_pos hapos,
    div_le_iff₀ hapos]
  have hab : |b - a| * (a + b) ≤ 2 * ε := by
    rw [← abs_of_pos (show 0 < a + b by linarith), ← abs_mul,
      show (b - a) * (a + b) = (b ^ 2 - 1) - (a ^ 2 - 1) by ring]
    exact (abs_sub _ _).trans (by linarith)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans ha
  nlinarith [abs_nonneg (b - a)]

/-- The normalised vectors $\bar{\mathbf{v}}_1, \dots, \bar{\mathbf{v}}_{k+1}$ are unit vectors.
Proof: $\|\mathbf{v}_j\|^2 \ge 1 - \varepsilon > 0$; easy. -/
theorem norm_normalizedV {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k + 1) :
    ‖WithLp.toLp 2 (L.normalizedV j)‖ = 1 := by
  have hunit : ∀ x : Fin n → ℝ, 0 < ‖WithLp.toLp 2 x‖ →
      ‖WithLp.toLp 2 (‖WithLp.toLp 2 x‖⁻¹ • x)‖ = 1 := fun x hx => by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hx,
      inv_mul_cancel₀ hx.ne']
  unfold normalizedV
  split_ifs with h
  · exact hunit _ (L.norm_v_pos le_rfl L.k_pos)
  · rcases (show j ≤ k ∨ j = k + 1 by omega) with hj | hj
    · exact hunit _ (L.norm_v_pos h1 hj)
    · subst hj
      exact hunit _ (L.norm_v_succ_pos (fun hβ => h ⟨rfl, hβ⟩))

/-- **Normalised local errors**: the normalised vectors satisfy the computed recurrence up to
$\|\bar{\mathbf{f}}_j\| \le 12(j + 1)\varepsilon\|\mathbf{H}\|_2$, $j < k$.
No printed source; the maintainer's draft, `lem:normalized-errors`, states
$\lesssim_k \varepsilon\|\mathbf{A}\|$.
Proof: $\bar{\mathbf{f}}_j - \mathbf{f}_j/\|\mathbf{v}_{j+1}\|$ is two terms
$\beta(\mathbf{v}/\|\mathbf{v}_{j+1}\| - \bar{\mathbf{v}})$, each at most $2\varepsilon\beta$ since
the norms are within $\varepsilon$ of $1$ in square; easy. -/
theorem norm_normalized_recurrenceError_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.normalized.recurrenceError j)‖ ≤ 12 * (j + 1) * L.ε * specNorm L.H := by
  have hε0 := L.ε_nonneg
  have hε1 := L.ε_le
  have hH := specNorm_nonneg L.H
  set d := ‖WithLp.toLp 2 (L.v (j + 1))‖ with hd
  set dj := ‖WithLp.toLp 2 (L.v j)‖ with hdj
  set d2 := ‖WithLp.toLp 2 (L.v (j + 2))‖ with hd2
  have hdsq : |d ^ 2 - 1| ≤ L.ε := L.abs_norm_v_sq_sub_one_le (j + 1) (by omega) (by omega)
  have hd1 : 99 / 100 ≤ d := (nearUnit (norm_nonneg _) (norm_nonneg _) hε1 hdsq hdsq).1
  have hdpos : 0 < d := by linarith
  have heq : L.normalized.recurrenceError j = d⁻¹ • L.recurrenceError j +
      (L.β j * (d⁻¹ - dj⁻¹)) • L.v j + (L.β (j + 1) * (d⁻¹ - d2⁻¹)) • L.v (j + 2) := by
    have h1 := L.normalizedV_of_le (j := j + 1) (by omega)
    have h0 := L.normalizedV_of_le (j := j) (by omega)
    have h2 := L.β_smul_normalizedV j
    simp only [LanczosData.recurrenceError, normalized, recurrenceError, toLanczosData]
    rw [h2, h1, h0, Matrix.mulVec_smul]
    module
  -- each correction term is at most `2 ε β`
  have hterm : ∀ (c : ℝ) (i : ℕ), (i = 0 ∨ |‖WithLp.toLp 2 (L.v i)‖ ^ 2 - 1| ≤ L.ε) →
      (i = 0 → L.v i = 0) →
      ‖WithLp.toLp 2 ((c * (d⁻¹ - ‖WithLp.toLp 2 (L.v i)‖⁻¹)) • L.v i)‖ ≤ |c| * (2 * L.ε) := by
    intro c i hi hi0
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rcases hi with hi | hi
    · rw [hi0 hi, WithLp.toLp_zero, norm_zero, mul_zero]
      positivity
    · set e := ‖WithLp.toLp 2 (L.v i)‖
      obtain ⟨he1, hratio⟩ := nearUnit (norm_nonneg _) (norm_nonneg _) hε1 hi hi
      obtain ⟨-, hr⟩ := nearUnit (norm_nonneg _) (norm_nonneg (WithLp.toLp 2 (L.v i))) hε1 hdsq hi
      have hepos : 0 < e := by linarith
      calc |d⁻¹ - e⁻¹| * e = |e / d - 1| := by
            rw [← abs_of_pos hepos, ← abs_mul, abs_of_pos hepos]
            congr 1
            field_simp
        _ ≤ 2 * L.ε := hr
  have hA : ‖WithLp.toLp 2 ((L.β j * (d⁻¹ - dj⁻¹)) • L.v j)‖ ≤ 5 / 4 * j * specNorm L.H * (2 * L.ε) := by
    refine (hterm (L.β j) j ?_ ?_).trans ?_
    · rcases Nat.eq_zero_or_pos j with h | h
      · exact Or.inl h
      · exact Or.inr (L.abs_norm_v_sq_sub_one_le j h hj.le)
    · intro h; rw [h]; exact L.v_zero
    · rw [abs_of_nonneg (L.β_nonneg j hj.le)]
      gcongr
      exact L.β_le hj.le
  have hB : ‖WithLp.toLp 2 ((L.β (j + 1) * (d⁻¹ - d2⁻¹)) • L.v (j + 2))‖ ≤
      5 / 4 * (j + 1) * specNorm L.H * (2 * L.ε) := by
    by_cases hβ : L.β (j + 1) = 0
    · rw [hβ, zero_mul, zero_smul, WithLp.toLp_zero, norm_zero]
      positivity
    refine (hterm (L.β (j + 1)) (j + 2) (Or.inr (L.abs_norm_v_add_two_sq_sub_one_le hj hβ))
      (fun h => by omega)).trans ?_
    rw [abs_of_nonneg (L.β_nonneg (j + 1) (by omega))]
    gcongr
    have := L.β_le (j := j + 1) (by omega)
    push_cast at this
    exact this
  have hF : ‖WithLp.toLp 2 (d⁻¹ • L.recurrenceError j)‖ ≤ 100 / 99 * (6 * (j + 1) * L.ε * specNorm L.H) := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hdpos]
    gcongr
    · rw [inv_le_comm₀ hdpos (by norm_num)]
      linarith
    · exact L.norm_recurrenceError_le hj
  rw [heq, WithLp.toLp_add, WithLp.toLp_add]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add_left (norm_add_le _ _) _).trans ?_
  have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
  have h0 : 0 ≤ L.ε * specNorm L.H := by positivity
  nlinarith [mul_nonneg hj0 h0]

/-- **Normalised local orthogonality**:
$\lvert\bar p_j\rvert \le 8(j + 1)\varepsilon\|\mathbf{H}\|_2$, $j < k$. No printed source; the
maintainer's draft, `lem:normalized-errors`.
Proof: $\bar p_j = p_j/(\|\mathbf{v}_{j+1}\|\|\mathbf{v}_{j+2}\|)$, or $0$ at a terminal step;
easy. -/
theorem abs_normalized_adjacentInner_le {j : ℕ} (hj : j < k) :
    |L.normalized.adjacentInner j| ≤ 8 * (j + 1) * L.ε * specNorm L.H := by
  have hε1 := L.ε_le
  have hH := specNorm_nonneg L.H
  set d := ‖WithLp.toLp 2 (L.v (j + 1))‖
  set d2 := ‖WithLp.toLp 2 (L.v (j + 2))‖
  have heq : L.normalized.adjacentInner j = d⁻¹ * d2⁻¹ * L.adjacentInner j := by
    have h1 := L.normalizedV_of_le (j := j + 1) (by omega)
    have h2 := L.β_smul_normalizedV j
    simp only [LanczosData.adjacentInner, normalized, adjacentInner, toLanczosData]
    rw [h2, h1, smul_comm (L.β (j + 1)), dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]
    ring
  by_cases hβ : L.β (j + 1) = 0
  · have : L.normalized.adjacentInner j = 0 := by
      simp only [LanczosData.adjacentInner, normalized, hβ, zero_smul, dotProduct_zero]
    rw [this, abs_zero]
    have := L.ε_nonneg
    positivity
  have hdsq : |d ^ 2 - 1| ≤ L.ε := L.abs_norm_v_sq_sub_one_le (j + 1) (by omega) (by omega)
  have hd2sq : |d2 ^ 2 - 1| ≤ L.ε := L.abs_norm_v_add_two_sq_sub_one_le hj hβ
  have hd1 := (nearUnit (norm_nonneg _) (norm_nonneg _) hε1 hdsq hdsq).1
  have hd21 := (nearUnit (norm_nonneg _) (norm_nonneg _) hε1 hd2sq hd2sq).1
  have hp := L.abs_adjacentInner_le hj
  have hinv : d⁻¹ * d2⁻¹ ≤ 100 / 99 * (100 / 99) := by
    have h1 : d⁻¹ ≤ 100 / 99 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h2 : d2⁻¹ ≤ 100 / 99 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    exact mul_le_mul h1 h2 (by positivity) (by norm_num)
  rw [heq, abs_mul, abs_of_pos (by positivity : 0 < d⁻¹ * d2⁻¹)]
  calc d⁻¹ * d2⁻¹ * |L.adjacentInner j|
      ≤ 100 / 99 * (100 / 99) * (7 * (j + 1) * L.ε * specNorm L.H) := by
        gcongr
    _ ≤ 8 * (j + 1) * L.ε * specNorm L.H := by
        have : 0 ≤ (j + 1) * L.ε * specNorm L.H := by have := L.ε_nonneg; positivity
        nlinarith

/-- The normalised residual is small:
$\|\bar{\mathbf{F}}_k\|_{\mathsf{F}} \le 12k\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2$. -/
theorem frobNorm_normalized_residual_le :
    frobNorm L.normalized.residual ≤ 12 * k * Real.sqrt k * L.ε * specNorm L.H := by
  have hε0 := L.ε_nonneg
  have hH := specNorm_nonneg L.H
  have hcol : ∀ j : Fin k, ‖WithLp.toLp 2 (L.normalized.residual.col j)‖ ≤
      12 * k * L.ε * specNorm L.H := by
    intro j
    have hjk : ((j : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast j.2
    refine (L.norm_normalized_recurrenceError_le j.2).trans ?_
    gcongr
  have hsq : frobNorm L.normalized.residual ^ 2 ≤
      (12 * k * Real.sqrt k * L.ε * specNorm L.H) ^ 2 := by
    rw [frobNorm_sq_eq_sum_col]
    calc ∑ j, ‖WithLp.toLp 2 (L.normalized.residual.col j)‖ ^ 2
        ≤ ∑ _j : Fin k, (12 * k * L.ε * specNorm L.H) ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hcol j) 2
      _ = (12 * k * Real.sqrt k * L.ε * specNorm L.H) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            show (12 * k * Real.sqrt k * L.ε * specNorm L.H) ^ 2 =
              (12 * k * L.ε * specNorm L.H) ^ 2 * Real.sqrt k ^ 2 by ring,
            Real.sq_sqrt (Nat.cast_nonneg k)]
          ring
  exact (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).1 hsq

/-- **The normalised Gram commutator is small**:
$\|\bar{\mathbf{M}}_k\|_2 \le 40k^2\varepsilon\|\mathbf{H}\|_2$. No printed source; the
maintainer's draft, `cor:normalized-commutator`.
Proof: `NLAlib.LanczosData.specNorm_gramCommutator_le` with no diagonal defects; easy. -/
theorem specNorm_normalized_gramCommutator_le :
    specNorm L.normalized.gramCommutator ≤ 40 * k ^ 2 * L.ε * specNorm L.H := by
  have hε0 := L.ε_nonneg
  have hH := specNorm_nonneg L.H
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.k_pos
  have ha : ∀ j < k, |L.normalized.adjacentInner j| ≤ 8 * k * L.ε * specNorm L.H :=
    fun j hj => (L.abs_normalized_adjacentInner_le hj).trans (by
      have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
      gcongr)
  have hb : ∀ j < k, |L.normalized.β j| ≤ 5 / 4 * k * specNorm L.H := fun j hj => by
    change |L.β j| ≤ _
    rw [abs_of_nonneg (L.β_nonneg j hj.le)]
    refine (L.β_le hj.le).trans ?_
    have : (j : ℝ) ≤ k := by exact_mod_cast hj.le
    gcongr
  have hg : ∀ i, |L.normalized.normSqDefect i| ≤ 0 := fun i => by
    simp only [LanczosData.normSqDefect, normalized]
    rw [L.norm_normalizedV (by omega) (by omega)]
    norm_num
  have hV : frobNorm L.normalized.basis = Real.sqrt k := by
    rw [← Real.sqrt_sq (frobNorm_nonneg _), frobNorm_sq_eq_sum_col]
    congr 1
    have : ∀ j : Fin k, ‖WithLp.toLp 2 (L.normalized.basis.col j)‖ = 1 := fun j =>
      L.norm_normalizedV (j := (j : ℕ) + 1) (by omega) (by omega)
    simp only [this, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hF := L.frobNorm_normalized_residual_le
  have h := L.normalized.specNorm_gramCommutator_le ha hb hg
  rw [hV, mul_zero, mul_zero, mul_zero, add_zero] at h
  refine h.trans ?_
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg k)
  have h2 : 2 * (Real.sqrt k * frobNorm L.normalized.residual) ≤
      24 * k ^ 2 * L.ε * specNorm L.H := by
    calc 2 * (Real.sqrt k * frobNorm L.normalized.residual)
        ≤ 2 * (Real.sqrt k * (12 * k * Real.sqrt k * L.ε * specNorm L.H)) := by gcongr
      _ = 24 * (Real.sqrt k * Real.sqrt k) * k * L.ε * specNorm L.H := by ring
      _ = 24 * k ^ 2 * L.ε * specNorm L.H := by rw [hsk]; ring
  have h0 : 0 ≤ L.ε * specNorm L.H := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ k ^ 2 by nlinarith) h0]

/-! ### The dilated recurrence -/

/-- The **dilated matrix** $\hat{\mathbf{H}} = \mathbf{I}_{k+1} \otimes \mathbf{H}$, block
diagonal with $k + 1$ copies of $\mathbf{H}$. -/
def dilatedH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  Matrix.blockDiagonal fun _ => L.H

/-- The **dilated vectors** $\hat{\mathbf{V}}_{k+1}$: the orthonormal dilation of the normalised
vectors $\bar{\mathbf{v}}_1, \dots, \bar{\mathbf{v}}_{k+1}$. -/
noncomputable def dilatedBasisSucc : Matrix (Fin n × Fin (k + 1)) (Fin (k + 1)) ℝ :=
  orthonormalDilation L.normalized.basisSucc

/-- The first $k$ dilated vectors $\hat{\mathbf{V}}_k$. -/
noncomputable def dilatedBasis : Matrix (Fin n × Fin (k + 1)) (Fin k) ℝ :=
  L.dilatedBasisSucc.submatrix id Fin.castSucc

/-- The **dilated starting vector** $(\bar{\mathbf{v}}_1, \mathbf{0}, \dots, \mathbf{0})$. -/
noncomputable def dilatedStart : Fin n × Fin (k + 1) → ℝ :=
  fun p => if (p.2 : ℕ) = 0 then L.normalizedV 1 p.1 else 0

/-- The tridiagonal matrix with the extra row, $\underline{\mathbf{T}}_k$
(`NLAlib.LanczosData.tridiagonalSucc` of the run). -/
def tridiagonalSucc : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  L.toLanczosData.tridiagonalSucc

/-- The **residual of the dilated recurrence**
$\hat{\mathbf{E}} = \hat{\mathbf{H}}\hat{\mathbf{V}}_k - \hat{\mathbf{V}}_{k+1}
\underline{\mathbf{T}}_k$. -/
noncomputable def dilatedResidual : Matrix (Fin n × Fin (k + 1)) (Fin k) ℝ :=
  L.dilatedH * L.dilatedBasis - L.dilatedBasisSucc * L.tridiagonalSucc

/-- The normalised vectors have unit length: the Gram matrix of $\bar{\mathbf{V}}_{k+1}$ has unit
diagonal. -/
theorem transpose_basisSucc_mul_self_apply (j : Fin (k + 1)) :
    (L.normalized.basisSuccᵀ * L.normalized.basisSucc) j j = 1 := by
  have h := L.norm_normalizedV (j := (j : ℕ) + 1) (by omega) (by omega)
  have h2 : ‖WithLp.toLp 2 (L.normalizedV ((j : ℕ) + 1))‖ ^ 2 = 1 := by rw [h, one_pow]
  rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self] at h2
  rw [Matrix.mul_apply]
  exact h2

/-- **The dilated vectors are orthonormal**. No printed source; the maintainer's draft,
`lem:dilation`.
Proof: `NLAlib.hasOrthonormalCols_orthonormalDilation` and
`NLAlib.LanczosRun.norm_normalizedV`; easy. -/
theorem hasOrthonormalCols_dilatedBasisSucc : HasOrthonormalCols L.dilatedBasisSucc :=
  hasOrthonormalCols_orthonormalDilation L.transpose_basisSucc_mul_self_apply

/-- The first dilated vector is the dilated starting vector. No printed source; the maintainer's
draft, `lem:dilation`.
Proof: `NLAlib.orthonormalDilation_apply_of_val_eq_zero`; easy. -/
theorem dilatedBasisSucc_col_zero : L.dilatedBasisSucc.col 0 = L.dilatedStart := by
  funext p
  rw [Matrix.col_apply, dilatedBasisSucc, orthonormalDilation_apply_of_val_eq_zero _ rfl]
  simp only [dilatedStart, Fin.ext_iff, Fin.val_zero]
  rfl

private theorem submatrix_sub' {a b c d : Type*} (A B : Matrix a b ℝ) (f : c → a) (g : d → b) :
    (A - B).submatrix f g = A.submatrix f g - B.submatrix f g := rfl

/-- The **exchange defect** $\mathbf{Y}_r = \underline{\mathbf{T}}_k\mathbf{K}_k^r -
\mathbf{K}^r\underline{\mathbf{T}}_k$ of the dilation ($\mathbf{K}_k$ the leading block of
$\mathbf{K}$), which measures how far $\mathbf{K}^r$ is from intertwining
$\underline{\mathbf{T}}_k$ (`lem:exchange` of the maintainer's draft). -/
noncomputable def exchangeDefect (r : ℕ) : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  L.tridiagonalSucc *
      (dilationK L.normalized.basisSucc ^ r).submatrix Fin.castSucc Fin.castSucc -
    dilationK L.normalized.basisSucc ^ r * L.tridiagonalSucc

/-- Block $r$ of the dilated residual:
$\hat{\mathbf{E}}_r = \bar{\mathbf{F}}_k(\mathbf{C}\mathbf{K}^r)_k
+ \bar{\mathbf{V}}_{k+1}(\mathbf{Y}_r - \mathbf{Y}_{r+1})$. -/
theorem dilatedResidual_submatrix (r : Fin (k + 1)) :
    L.dilatedResidual.submatrix (fun i => (i, r)) id =
      L.normalized.residual * (dilationC L.normalized.basisSucc *
          dilationK L.normalized.basisSucc ^ (r : ℕ)).submatrix Fin.castSucc Fin.castSucc +
        L.normalized.basisSucc * (L.exchangeDefect r - L.exchangeDefect (r + 1)) := by
  set W := L.normalized.basisSucc
  set C := dilationC W
  set K := dilationK W
  have hCKr : (C * K ^ (r : ℕ)).IsUpperTriangular :=
    (isUpperTriangular_dilationC W).mul ((isUpperTriangular_dilationK W).pow _)
  have hB : L.dilatedBasis.submatrix (fun i => (i, r)) id =
      (W * (C * K ^ (r : ℕ))).submatrix id Fin.castSucc := by
    ext i j
    simp only [dilatedBasis, dilatedBasisSucc, orthonormalDilation, Matrix.submatrix_apply, id,
      Matrix.of_apply, Matrix.mul_assoc]
    rfl
  have hBs : L.dilatedBasisSucc.submatrix (fun i => (i, r)) id = W * (C * K ^ (r : ℕ)) := by
    ext i j
    simp only [dilatedBasisSucc, orthonormalDilation, Matrix.submatrix_apply, id,
      Matrix.of_apply, Matrix.mul_assoc]
    rfl
  have hW : W.submatrix id Fin.castSucc = L.normalized.basis := by
    ext i j
    rfl
  have hrec := L.normalized.H_mul_basis_eq_basisSucc_mul
  have hT : L.normalized.tridiagonalSucc = L.tridiagonalSucc := rfl
  have hCK : C * K ^ (r : ℕ) = K ^ (r : ℕ) - K ^ ((r : ℕ) + 1) := by
    have : C = 1 - K := by simp only [K, dilationK]; abel
    rw [this, Matrix.sub_mul, Matrix.one_mul, pow_succ']
  have hdil : L.dilatedH = Matrix.blockDiagonal (fun _ : Fin (k + 1) => L.H) := rfl
  rw [dilatedResidual, submatrix_sub', hdil, submatrix_blockDiagonal_mul,
    Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, hB, hBs,
    submatrix_castSucc_mul W hCKr, hW]
  have hH : L.H = L.normalized.H := rfl
  rw [hH, ← Matrix.mul_assoc, hrec, hT]
  simp only [exchangeDefect]
  rw [hCK, submatrix_sub']
  simp only [Matrix.submatrix_id_id, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc]
  abel

/-- The exchange defects satisfy $\mathbf{Y}_{r+1} = \mathbf{Y}_r\mathbf{K}_k +
\mathbf{K}^r\mathbf{Y}_1$. -/
theorem exchangeDefect_succ (r : ℕ) :
    L.exchangeDefect (r + 1) =
      L.exchangeDefect r * (dilationK L.normalized.basisSucc).submatrix Fin.castSucc
          Fin.castSucc +
        dilationK L.normalized.basisSucc ^ r * L.exchangeDefect 1 := by
  set K := dilationK L.normalized.basisSucc
  have hK := isUpperTriangular_dilationK L.normalized.basisSucc
  simp only [exchangeDefect]
  rw [pow_succ, submatrix_castSucc_mul_castSucc _ hK, pow_one]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- $\mathbf{Y}_0 = \mathbf{0}$. -/
theorem exchangeDefect_zero : L.exchangeDefect 0 = 0 := by
  simp only [exchangeDefect, pow_zero, Matrix.one_mul]
  rw [Matrix.submatrix_one _ (Fin.castSucc_injective k), Matrix.mul_one, sub_self]

/-- **The exchange rule**: $\mathbf{Y}_1 = \mathbf{C}(\underline{\mathbf{T}}_k\mathbf{R}_k -
\mathbf{R}\underline{\mathbf{T}}_k)\mathbf{C}_k$. No printed source; the maintainer's draft,
`eq:L-commutator`; [Paige2010, (3.9)]. -/
theorem exchangeDefect_one :
    L.exchangeDefect 1 = dilationC L.normalized.basisSucc *
      (L.tridiagonalSucc * (strictUpperGram L.normalized.basisSucc).submatrix Fin.castSucc
          Fin.castSucc - strictUpperGram L.normalized.basisSucc * L.tridiagonalSucc) *
      (dilationC L.normalized.basisSucc).submatrix Fin.castSucc Fin.castSucc := by
  simp only [exchangeDefect, pow_one]
  set W := L.normalized.basisSucc
  set R := strictUpperGram W
  set C := dilationC W
  set K := dilationK W
  set T := L.tridiagonalSucc
  have hRC : R.submatrix Fin.castSucc Fin.castSucc * C.submatrix Fin.castSucc Fin.castSucc =
      K.submatrix Fin.castSucc Fin.castSucc := by
    rw [← submatrix_castSucc_mul_castSucc _ (isUpperTriangular_dilationC W),
      ← dilationK_eq_strictUpperGram_mul]
  have hCR : C * R = K := (dilationK_eq_dilationC_mul W).symm
  have hC : C = 1 - K := by simp only [K, dilationK]; abel
  have hCk :
      C.submatrix Fin.castSucc Fin.castSucc = 1 - K.submatrix Fin.castSucc Fin.castSucc := by
    rw [hC, submatrix_sub', Matrix.submatrix_one _ (Fin.castSucc_injective k)]
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]
  rw [hRC, ← Matrix.mul_assoc C R, hCR, hCk]
  conv_rhs => rw [hC]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  abel

/-- The commutator of the normalised Gram matrix with $\underline{\mathbf{T}}_k$ is the
normalised Gram commutator with a zero last row:
$\underline{\mathbf{T}}_k\mathbf{R}_k - \mathbf{R}\underline{\mathbf{T}}_k =
\mathbf{J}\bar{\mathbf{M}}_k$, $\mathbf{J}$ the first $k$ columns of $\mathbf{I}_{k+1}$. -/
theorem tridiagonalSucc_mul_sub_eq :
    L.tridiagonalSucc * (strictUpperGram L.normalized.basisSucc).submatrix Fin.castSucc
        Fin.castSucc - strictUpperGram L.normalized.basisSucc * L.tridiagonalSucc =
      (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).submatrix id Fin.castSucc *
        L.normalized.gramCommutator := by
  set D := L.normalized
  have hT : L.tridiagonalSucc = D.tridiagonalSucc := rfl
  have hRc : ∀ a b : Fin k, strictUpperGram D.basisSucc (Fin.castSucc a) (Fin.castSucc b) =
      D.gramStrictUpper a b := fun a b => by
    simp only [strictUpperGram, LanczosData.gramStrictUpper, Matrix.of_apply,
      Fin.castSucc_lt_castSucc_iff, Matrix.mul_apply, Matrix.transpose_apply,
      LanczosData.basisSucc, dotProduct, Fin.val_castSucc]
  have hRlast : ∀ a : Fin k, strictUpperGram D.basisSucc (Fin.castSucc a) (Fin.last k) =
      D.v ((a : ℕ) + 1) ⬝ᵥ D.v (k + 1) := fun a => by
    simp only [strictUpperGram, Matrix.of_apply, if_pos (Fin.castSucc_lt_last a),
      Matrix.mul_apply, Matrix.transpose_apply, LanczosData.basisSucc, dotProduct,
      Fin.val_castSucc, Fin.val_last]
  have hRl : ∀ l, strictUpperGram D.basisSucc (Fin.last k) l = 0 := fun l =>
    strictUpperGram_apply_of_le _ (Fin.le_last l)
  have hlast : ∀ j : Fin k, j = D.lastIndex ↔ k = (j : ℕ) + 1 := fun j => by
    rw [Fin.ext_iff]
    simp only [LanczosData.lastIndex]
    have := D.k_pos
    omega
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · have h1 : ∀ l : Fin k, (Fin.last k = Fin.castSucc l) ↔ False :=
      fun l => ⟨fun h => (Fin.castSucc_lt_last l).ne' h, False.elim⟩
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [hRl, zero_mul, Finset.sum_const_zero, sub_zero, Matrix.submatrix_apply, id,
      Matrix.one_apply, h1, if_false]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hT, D.tridiagonalSucc_last]
    split_ifs with h
    · rw [strictUpperGram_apply_of_le _ (by rw [Fin.le_def]; simp only [Fin.val_castSucc]; omega),
        mul_zero]
    · rw [zero_mul]
  · rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc,
      Matrix.mul_apply]
    simp only [Matrix.submatrix_apply, id, hT, D.tridiagonalSucc_castSucc, D.tridiagonalSucc_last,
      hRc, hRlast, Matrix.one_apply, Fin.castSucc_inj, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [LanczosData.gramCommutator, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.vecMulVec_apply, Pi.single_apply, hlast]
    have hc : (D.basisᵀ *ᵥ (D.β k • D.v (k + 1))) i' = D.β k * (D.v ((i' : ℕ) + 1) ⬝ᵥ D.v (k + 1)) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, LanczosData.basis,
        Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hc]
    by_cases h : k = (j : ℕ) + 1
    · simp only [h, if_true]
      ring
    · simp only [h, if_false]
      ring

/-- The normalised basis with the next vector has Frobenius norm $\sqrt{k + 1}$. -/
theorem frobNorm_normalized_basisSucc :
    frobNorm L.normalized.basisSucc = Real.sqrt (k + 1) := by
  rw [← Real.sqrt_sq (frobNorm_nonneg _), frobNorm_sq_eq_sum_col]
  congr 1
  have : ∀ j : Fin (k + 1), ‖WithLp.toLp 2 (L.normalized.basisSucc.col j)‖ = 1 := fun j =>
    L.norm_normalizedV (j := (j : ℕ) + 1) (by omega) (by omega)
  simp only [this, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- **The exchange rule, bounds**: $\|\mathbf{Y}_1\|_2 \le 160k^2\varepsilon\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `lem:exchange`. -/
theorem specNorm_exchangeDefect_one_le :
    specNorm (L.exchangeDefect 1) ≤ 160 * k ^ 2 * L.ε * specNorm L.H := by
  set W := L.normalized.basisSucc
  have hW := L.transpose_basisSucc_mul_self_apply
  have hC := specNorm_dilationC_le_two hW
  have hCk : specNorm ((dilationC W).submatrix Fin.castSucc Fin.castSucc) ≤ 2 :=
    (specNorm_submatrix_le _ (Fin.castSucc_injective k) (Fin.castSucc_injective k)).trans hC
  have hJ : HasOrthonormalCols ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).submatrix id
      Fin.castSucc) :=
    hasOrthonormalCols_one.submatrix (Equiv.refl _) (Fin.castSucc_injective k)
  have hZ : specNorm (L.tridiagonalSucc * (strictUpperGram W).submatrix Fin.castSucc
      Fin.castSucc - strictUpperGram W * L.tridiagonalSucc) ≤ 40 * k ^ 2 * L.ε * specNorm L.H := by
    rw [L.tridiagonalSucc_mul_sub_eq, hJ.specNorm_mul_left]
    exact L.specNorm_normalized_gramCommutator_le
  rw [L.exchangeDefect_one]
  refine (specNorm_mul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)).trans ?_
  have h0 : 0 ≤ 40 * k ^ 2 * L.ε * specNorm L.H := by
    have := L.ε_nonneg
    have := specNorm_nonneg L.H
    positivity
  calc specNorm (dilationC W) * specNorm (L.tridiagonalSucc *
        (strictUpperGram W).submatrix Fin.castSucc Fin.castSucc -
        strictUpperGram W * L.tridiagonalSucc) *
        specNorm ((dilationC W).submatrix Fin.castSucc Fin.castSucc)
      ≤ 2 * (40 * k ^ 2 * L.ε * specNorm L.H) * 2 := by
        gcongr
    _ = 160 * k ^ 2 * L.ε * specNorm L.H := by ring

/-- The exchange defects grow at most linearly: $\|\mathbf{Y}_r\|_2 \le r\|\mathbf{Y}_1\|_2$. -/
theorem specNorm_exchangeDefect_le (r : ℕ) :
    specNorm (L.exchangeDefect r) ≤ r * specNorm (L.exchangeDefect 1) := by
  have hW := L.transpose_basisSucc_mul_self_apply
  have hK := specNorm_dilationK_le_one hW
  have hKk : specNorm ((dilationK L.normalized.basisSucc).submatrix Fin.castSucc
      Fin.castSucc) ≤ 1 :=
    (specNorm_submatrix_le _ (Fin.castSucc_injective k) (Fin.castSucc_injective k)).trans hK
  have hKr : ∀ r : ℕ, specNorm (dilationK L.normalized.basisSucc ^ r) ≤ 1 := fun r =>
    (specNorm_pow_le _ r).trans (pow_le_one₀ (specNorm_nonneg _) hK)
  induction r with
  | zero => rw [L.exchangeDefect_zero, specNorm_zero]; simp
  | succ r ih =>
    rw [L.exchangeDefect_succ]
    refine (specNorm_add_le _ _).trans ?_
    have h1 : specNorm (L.exchangeDefect r * (dilationK L.normalized.basisSucc).submatrix
        Fin.castSucc Fin.castSucc) ≤ r * specNorm (L.exchangeDefect 1) :=
      (specNorm_mul_le _ _).trans (by
        calc specNorm (L.exchangeDefect r) * _ ≤ r * specNorm (L.exchangeDefect 1) * 1 := by
              gcongr
          _ = _ := mul_one _)
    have h2 : specNorm (dilationK L.normalized.basisSucc ^ r * L.exchangeDefect 1) ≤
        specNorm (L.exchangeDefect 1) :=
      (specNorm_mul_le _ _).trans (by
        calc _ ≤ 1 * specNorm (L.exchangeDefect 1) := by gcongr; exact hKr r
          _ = _ := one_mul _)
    push_cast
    linarith

/-- **The dilated recurrence** (the exchange rule and the dilated residual): the orthonormal
dilated vectors satisfy the computed recurrence with the computed coefficients up to
$$\|\hat{\mathbf{E}}\|_{\mathsf{F}} =
\|\hat{\mathbf{H}}\hat{\mathbf{V}}_k - \hat{\mathbf{V}}_{k+1}\underline{\mathbf{T}}_k\|_{\mathsf{F}}
\le 1000k^4\varepsilon\|\mathbf{H}\|_2 \,.$$
No printed source; the maintainer's draft, `lem:exchange` and `lem:dilated-recurrence`, state
$\lesssim_k \varepsilon\|\mathbf{A}\|$ (its formalization: $240000k^6$ in the spectral norm).
Proof: block $r$ of $\hat{\mathbf{E}}$ is $\bar{\mathbf{F}}_k(\mathbf{C}\mathbf{K}^r)_k
+ \bar{\mathbf{V}}_{k+1}(\mathbf{Y}_r - \mathbf{Y}_{r+1})$ with $\mathbf{Y}_r =
\underline{\mathbf{T}}_k\mathbf{K}_k^r - \mathbf{K}^r\underline{\mathbf{T}}_k$,
$\mathbf{Y}_{r+1} = \mathbf{Y}_r\mathbf{K}_k + \mathbf{K}^r\mathbf{Y}_1$ and
$\mathbf{Y}_1 = \mathbf{C}(\underline{\mathbf{T}}_k\mathbf{R}_k
- \mathbf{R}\underline{\mathbf{T}}_k)
\mathbf{C}_k$; hard.
Result: lanczos-dilated-recurrence -/
theorem frobNorm_dilatedResidual_le :
    frobNorm L.dilatedResidual ≤ 1000 * k ^ 4 * L.ε * specNorm L.H := by
  set W := L.normalized.basisSucc
  have hW := L.transpose_basisSucc_mul_self_apply
  have hε0 := L.ε_nonneg
  have hH := specNorm_nonneg L.H
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.k_pos
  set A := L.ε * specNorm L.H with hA
  have hA0 : 0 ≤ A := by positivity
  have hY1 := L.specNorm_exchangeDefect_one_le
  set c := (24 * k * Real.sqrt k + Real.sqrt (k + 1) * (2 * k + 1) * (160 * k ^ 2)) * A
  have hblock : ∀ r : Fin (k + 1),
      frobNorm (L.dilatedResidual.submatrix (fun i => (i, r)) id) ≤ c := by
    intro r
    have hr : ((r : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp r.2
    have hCK : specNorm ((dilationC W * dilationK W ^ (r : ℕ)).submatrix Fin.castSucc
        Fin.castSucc) ≤ 2 := by
      refine (specNorm_submatrix_le _ (Fin.castSucc_injective k)
        (Fin.castSucc_injective k)).trans ((specNorm_mul_le _ _).trans ?_)
      have h1 := specNorm_dilationC_le_two hW
      have h2 : specNorm (dilationK W ^ (r : ℕ)) ≤ 1 :=
        (specNorm_pow_le _ _).trans (pow_le_one₀ (specNorm_nonneg _)
          (specNorm_dilationK_le_one hW))
      calc _ ≤ 2 * 1 := mul_le_mul h1 h2 (specNorm_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    have hY : specNorm (L.exchangeDefect r - L.exchangeDefect (r + 1)) ≤
        (2 * k + 1) * (160 * k ^ 2 * L.ε * specNorm L.H) := by
      refine (specNorm_sub_le _ _).trans ?_
      have h1 := L.specNorm_exchangeDefect_le r
      have h2 := L.specNorm_exchangeDefect_le (r + 1)
      push_cast at h2
      have hY0 := specNorm_nonneg (L.exchangeDefect 1)
      nlinarith
    rw [L.dilatedResidual_submatrix]
    refine (frobNorm_add_le _ _).trans ?_
    have hF := L.frobNorm_normalized_residual_le
    have e1 := frobNorm_mul_le_frobNorm_mul_specNorm L.normalized.residual
      ((dilationC W * dilationK W ^ (r : ℕ)).submatrix Fin.castSucc Fin.castSucc)
    have e2 := frobNorm_mul_le_frobNorm_mul_specNorm W
      (L.exchangeDefect r - L.exchangeDefect (r + 1))
    rw [L.frobNorm_normalized_basisSucc] at e2
    have hs1 : 0 ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
    calc _ ≤ frobNorm L.normalized.residual * 2 +
          Real.sqrt (k + 1) * ((2 * k + 1) * (160 * k ^ 2 * L.ε * specNorm L.H)) := by
          gcongr
          · exact e1.trans (mul_le_mul_of_nonneg_left hCK (frobNorm_nonneg _))
          · exact e2.trans (mul_le_mul_of_nonneg_left hY hs1)
      _ ≤ 12 * k * Real.sqrt k * L.ε * specNorm L.H * 2 +
          Real.sqrt (k + 1) * ((2 * k + 1) * (160 * k ^ 2 * L.ε * specNorm L.H)) := by gcongr
      _ = c := by simp only [c, hA]; ring
  have hc0 : 0 ≤ c := by positivity
  have hsq : frobNorm L.dilatedResidual ^ 2 ≤ (Real.sqrt (k + 1) * c) ^ 2 := by
    rw [frobNorm_sq_eq_sum_submatrix, mul_pow, Real.sq_sqrt (by positivity)]
    calc ∑ r, frobNorm (L.dilatedResidual.submatrix (fun i => (i, r)) id) ^ 2
        ≤ ∑ _r : Fin (k + 1), c ^ 2 :=
          Finset.sum_le_sum fun r _ => pow_le_pow_left₀ (frobNorm_nonneg _) (hblock r) 2
      _ = (k + 1) * c ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  refine ((sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).1 hsq).trans ?_
  have hsk : Real.sqrt (k + 1) * Real.sqrt (k + 1) = k + 1 := Real.mul_self_sqrt (by positivity)
  have hss : Real.sqrt (k + 1) * Real.sqrt k ≤ 3 / 2 * k := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have : Real.sqrt (k + 1) * c = (24 * k * (Real.sqrt (k + 1) * Real.sqrt k) +
      (Real.sqrt (k + 1) * Real.sqrt (k + 1)) * (2 * k + 1) * (160 * k ^ 2)) * A := by
    simp only [c]; ring
  rw [this, hsk]
  have hpoly : 24 * (k : ℝ) * (3 / 2 * k) + (k + 1) * (2 * k + 1) * (160 * k ^ 2) ≤
      1000 * (k : ℝ) ^ 4 := by
    have h2 : (k : ℝ) ≤ k ^ 2 := by nlinarith
    have h3 : (k : ℝ) ^ 2 ≤ k ^ 3 := by nlinarith
    have h4 : (k : ℝ) ^ 3 ≤ k ^ 4 := by nlinarith
    nlinarith
  calc (24 * k * (Real.sqrt (k + 1) * Real.sqrt k) + (k + 1) * (2 * k + 1) * (160 * k ^ 2)) * A
      ≤ (24 * k * (3 / 2 * k) + (k + 1) * (2 * k + 1) * (160 * k ^ 2)) * A := by gcongr
    _ ≤ 1000 * k ^ 4 * A := by gcongr
    _ = 1000 * k ^ 4 * L.ε * specNorm L.H := by rw [hA]; ring

/-! ### The backward model -/

/-- The **backward perturbation**
$\boldsymbol{\Delta} = -\hat{\mathbf{E}}\hat{\mathbf{V}}_k^{\mathsf{T}} -
\hat{\mathbf{V}}_k\hat{\mathbf{E}}^{\mathsf{T}}(\mathbf{I} - \hat{\mathbf{V}}_k
\hat{\mathbf{V}}_k^{\mathsf{T}})$. -/
noncomputable def backwardPerturbation : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  -(L.dilatedResidual * L.dilatedBasisᵀ) -
    L.dilatedBasis * L.dilatedResidualᵀ * (1 - L.dilatedBasis * L.dilatedBasisᵀ)

/-- The **backward model** $\tilde{\mathbf{H}} = \mathbf{I}_{k+1} \otimes \mathbf{H} +
\boldsymbol{\Delta}$. -/
noncomputable def backwardH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  L.dilatedH + L.backwardPerturbation

/-- The first $k$ dilated vectors are orthonormal. -/
theorem hasOrthonormalCols_dilatedBasis : HasOrthonormalCols L.dilatedBasis :=
  L.hasOrthonormalCols_dilatedBasisSucc.submatrix (Equiv.refl _) (Fin.castSucc_injective k)

/-- $\hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{V}}_{k+1}\underline{\mathbf{T}}_k = \mathbf{T}_k$. -/
theorem transpose_dilatedBasis_mul_dilatedBasisSucc_mul :
    L.dilatedBasisᵀ * (L.dilatedBasisSucc * L.tridiagonalSucc) = L.tridiagonal := by
  have hQ := L.hasOrthonormalCols_dilatedBasisSucc
  have hQQ : L.dilatedBasisSuccᵀ * L.dilatedBasisSucc = 1 := by
    have := hQ.conjTranspose_mul_self
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have h1 : L.dilatedBasisᵀ * L.dilatedBasisSucc =
      (L.dilatedBasisSuccᵀ * L.dilatedBasisSucc).submatrix Fin.castSucc id := by
    rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
    rfl
  rw [← Matrix.mul_assoc, h1, hQQ]
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact L.toLanczosData.tridiagonalSucc_castSucc i j

/-- $\hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{E}}$ is symmetric:
$\hat{\mathbf{E}}^{\mathsf{T}}\hat{\mathbf{V}}_k = \hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{E}}$. -/
theorem transpose_dilatedResidual_mul_dilatedBasis :
    L.dilatedResidualᵀ * L.dilatedBasis = L.dilatedBasisᵀ * L.dilatedResidual := by
  have hH : L.dilatedHᵀ = L.dilatedH := by
    rw [dilatedH, Matrix.blockDiagonal_transpose, L.transpose_H]
  have hX : L.dilatedBasisᵀ * L.dilatedResidual =
      L.dilatedBasisᵀ * L.dilatedH * L.dilatedBasis - L.tridiagonal := by
    rw [dilatedResidual, Matrix.mul_sub, L.transpose_dilatedBasis_mul_dilatedBasisSucc_mul,
      Matrix.mul_assoc]
  rw [← Matrix.transpose_transpose (L.dilatedResidualᵀ * L.dilatedBasis), Matrix.transpose_mul,
    Matrix.transpose_transpose, hX, Matrix.transpose_sub, L.transpose_tridiagonal,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH, Matrix.mul_assoc]

/-- The backward model is symmetric.
Proof: $\hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{E}} = \hat{\mathbf{V}}_k^{\mathsf{T}}
\hat{\mathbf{H}}\hat{\mathbf{V}}_k - \mathbf{T}_k$ is symmetric; easy. -/
theorem transpose_backwardH : L.backwardHᵀ = L.backwardH := by
  set Q := L.dilatedBasis
  set E := L.dilatedResidual
  have hsym := L.transpose_dilatedResidual_mul_dilatedBasis
  have hH : L.dilatedHᵀ = L.dilatedH := by
    rw [dilatedH, Matrix.blockDiagonal_transpose, L.transpose_H]
  rw [backwardH, backwardPerturbation, Matrix.transpose_add, hH]
  congr 1
  simp only [Matrix.transpose_sub, Matrix.transpose_neg, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_one]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Eᵀ Q, hsym, Matrix.mul_assoc]
  abel

/-- **The backward model satisfies the computed recurrence exactly**:
$\tilde{\mathbf{H}}\hat{\mathbf{V}}_k = \hat{\mathbf{V}}_{k+1}\underline{\mathbf{T}}_k$ with
$\hat{\mathbf{V}}_{k+1}$ orthonormal. No printed source; the maintainer's draft, `thm:greenbaum`.
Proof: $\boldsymbol{\Delta}\hat{\mathbf{V}}_k = -\hat{\mathbf{E}}$ since
$\hat{\mathbf{V}}_k^{\mathsf{T}}\hat{\mathbf{V}}_k = \mathbf{I}$; easy. -/
theorem backwardH_mul_dilatedBasis :
    L.backwardH * L.dilatedBasis = L.dilatedBasisSucc * L.tridiagonalSucc := by
  have hQ := L.hasOrthonormalCols_dilatedBasis
  have hQQ : L.dilatedBasisᵀ * L.dilatedBasis = 1 := by
    have := hQ.conjTranspose_mul_self
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [backwardH, backwardPerturbation, Matrix.add_mul, Matrix.sub_mul, Matrix.neg_mul]
  simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hQQ, Matrix.mul_one, sub_self,
    Matrix.mul_zero, sub_zero]
  rw [dilatedResidual]
  abel

/-- **Greenbaum-type backward model for finite-precision Lanczos**: the symmetric backward model
$\tilde{\mathbf{H}}$ is close to $\mathbf{I}_{k+1} \otimes \mathbf{H}$,
$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}}
\le 2000k^4\varepsilon\|\mathbf{H}\|_2 \,,$$
and it satisfies the computed recurrence exactly with orthonormal vectors
(`NLAlib.LanczosRun.backwardH_mul_dilatedBasis`), so exact Lanczos on it from the dilated
starting vector computes $\mathbf{T}_k$ and $\beta_k$
(`NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`).
No printed source; the maintainer's draft, `thm:greenbaum`, states
$\|\boldsymbol{\Delta}\| \lesssim_k \varepsilon\|\mathbf{A}\|$ (its formalization:
$480000k^6$ in the spectral norm); the Frobenius norm here is at least the spectral norm.
[Greenbaum1989] has a perturbation of order $\varepsilon^{1/4}$.
Proof: $\|\hat{\mathbf{E}}\hat{\mathbf{V}}_k^{\mathsf{T}}\|_{\mathsf{F}} \le
\|\hat{\mathbf{E}}\|_{\mathsf{F}}$ and the projector has norm at most $1$; then
`NLAlib.LanczosRun.frobNorm_dilatedResidual_le`; easy.
Result: greenbaum-backward-model -/
theorem frobNorm_backwardH_sub_dilatedH_le :
    frobNorm (L.backwardH - L.dilatedH) ≤ 2000 * k ^ 4 * L.ε * specNorm L.H := by
  have hQ := L.hasOrthonormalCols_dilatedBasis
  have hE := L.frobNorm_dilatedResidual_le
  have hQ1 : specNorm L.dilatedBasis ≤ 1 := hQ.specNorm_le_one
  have hQt : specNorm L.dilatedBasisᵀ ≤ 1 := by rw [specNorm_transpose]; exact hQ1
  have hP := hQ.specNorm_one_sub_mul_transpose_le
  rw [backwardH, add_sub_cancel_left, backwardPerturbation]
  refine (frobNorm_sub_le _ _).trans ?_
  rw [frobNorm_neg]
  have h1 : frobNorm (L.dilatedResidual * L.dilatedBasisᵀ) ≤ frobNorm L.dilatedResidual :=
    (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
      (by simpa using mul_le_mul_of_nonneg_left hQt (frobNorm_nonneg L.dilatedResidual))
  have h2 : frobNorm (L.dilatedBasis * L.dilatedResidualᵀ *
      (1 - L.dilatedBasis * L.dilatedBasisᵀ)) ≤ frobNorm L.dilatedResidual := by
    rw [Matrix.mul_assoc]
    refine (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans ?_
    refine (mul_le_mul hQ1 ((frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
      (mul_le_mul_of_nonneg_left hP (frobNorm_nonneg _))) (frobNorm_nonneg _) zero_le_one).trans ?_
    rw [one_mul, mul_one, frobNorm_transpose]
  linarith

/-- The dilated vectors as a sequence: $\hat{\mathbf{u}}_m$ is column $m - 1$ of
$\hat{\mathbf{V}}_{k+1}$ for $1 \le m \le k + 1$, and $\mathbf{0}$ otherwise. -/
noncomputable def dilatedV (m : ℕ) : Fin n × Fin (k + 1) → ℝ :=
  fun p => if h : 1 ≤ m ∧ m ≤ k + 1 then L.dilatedBasisSucc p ⟨m - 1, by omega⟩ else 0

private theorem dilatedV_succ {m : ℕ} (hm : m < k + 1) (p : Fin n × Fin (k + 1)) :
    L.dilatedBasisSucc p ⟨m, hm⟩ = L.dilatedV (m + 1) p := by
  simp only [dilatedV, dif_pos (show 1 ≤ m + 1 ∧ m + 1 ≤ k + 1 by omega), Nat.add_sub_cancel]

/-- The dilated sequence satisfies the hypotheses of
`NLAlib.lanczosState_eq_of_orthonormal_recurrence` for the backward model. -/
private theorem dilatedV_orthonormal_recurrence :
    L.dilatedV 0 = 0 ∧
    (∀ i j, 1 ≤ i → i ≤ k + 1 → 1 ≤ j → j ≤ k + 1 →
      L.dilatedV i ⬝ᵥ L.dilatedV j = if i = j then 1 else 0) ∧
    (∀ j < k, L.backwardH *ᵥ L.dilatedV (j + 1) = L.β j • L.dilatedV j +
      L.α (j + 1) • L.dilatedV (j + 1) + L.β (j + 1) • L.dilatedV (j + 2)) ∧
    L.dilatedV 1 = L.dilatedStart := by
  have hQ := L.hasOrthonormalCols_dilatedBasisSucc
  have hQQ : L.dilatedBasisSuccᵀ * L.dilatedBasisSucc = 1 := by
    have := hQ.conjTranspose_mul_self
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext p
    simp only [dilatedV, Pi.zero_apply]
    rw [dif_neg (by omega)]
  · intro i j hi1 hi2 hj1 hj2
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have h := congrFun (congrFun hQQ ⟨i, by omega⟩) ⟨j, by omega⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [Matrix.transpose_apply, dilatedV_succ] at h
    rw [dotProduct, h]
    simp only [Fin.mk.injEq, Nat.add_right_cancel_iff]
  · intro j hj
    funext p
    have hl := L.toLanczosData.mul_tridiagonalSucc_apply L.dilatedBasisSucc L.dilatedV
      (fun m hm q => L.dilatedV_succ hm q) p ⟨j, hj⟩
    have hcol : ∀ q, L.dilatedBasis q ⟨j, hj⟩ = L.dilatedV (j + 1) q := fun q =>
      L.dilatedV_succ (by omega) q
    have := congrFun (congrFun L.backwardH_mul_dilatedBasis p) ⟨j, hj⟩
    rw [Matrix.mul_apply, tridiagonalSucc, hl] at this
    simp only [hcol] at this
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact this
  · rw [← L.dilatedBasisSucc_col_zero]
    funext p
    rw [Matrix.col_apply, show (0 : Fin (k + 1)) = ⟨0, by omega⟩ from Fin.ext (by simp),
      L.dilatedV_succ (m := 0) (by omega)]

/-- **Exact Lanczos on the backward model computes the computed tridiagonal matrix**: $k$ steps
of the Lanczos recurrence on $\tilde{\mathbf{H}}$ from
$(\bar{\mathbf{v}}_1, \mathbf{0}, \dots, \mathbf{0})$ give $\mathbf{T}_k$.
No printed source; the maintainer's draft, `thm:greenbaum`.
Proof: `NLAlib.lanczosState_eq_of_orthonormal_recurrence` with the columns of
$\hat{\mathbf{V}}_{k+1}$; easy. -/
theorem lanczosTridiagonal_backwardH_dilatedStart :
    lanczosTridiagonal L.backwardH L.dilatedStart k = L.tridiagonal := by
  obtain ⟨h0, horth, hrec, h1⟩ := L.dilatedV_orthonormal_recurrence
  have hst := lanczosState_eq_of_orthonormal_recurrence h0 horth hrec L.β_zero L.β_nonneg
    L.β_pos
  rw [← h1]
  ext i j
  simp only [lanczosTridiagonal, Matrix.of_apply, hst i i.2, hst j j.2,
    (lanczosStep_of_orthonormal_recurrence horth hrec L.β_nonneg i.2).1,
    RCLike.ofReal_real_eq_id, id]
  rfl

/-- Exact Lanczos on the backward model computes the dilated vectors:
`lanczosMatrix` of $\tilde{\mathbf{H}}$ from the dilated start is $\hat{\mathbf{V}}_k$.
Proof: as `NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`; easy. -/
theorem lanczosMatrix_backwardH_dilatedStart :
    lanczosMatrix L.backwardH L.dilatedStart k = L.dilatedBasis := by
  obtain ⟨h0, horth, hrec, h1⟩ := L.dilatedV_orthonormal_recurrence
  have hst := lanczosState_eq_of_orthonormal_recurrence h0 horth hrec L.β_zero L.β_nonneg
    L.β_pos
  rw [← h1]
  ext p j
  simp only [lanczosMatrix, Matrix.of_apply, hst j j.2]
  exact (L.dilatedV_succ (by omega) p).symm

/-- Exact Lanczos on the backward model computes the last coefficient: $\beta_k$ is the
coefficient of the state after $k$ steps.
Proof: as `NLAlib.LanczosRun.lanczosTridiagonal_backwardH_dilatedStart`; easy. -/
theorem lanczosState_backwardH_dilatedStart_beta :
    (lanczosState L.backwardH L.dilatedStart k).beta = L.β k := by
  obtain ⟨h0, horth, hrec, h1⟩ := L.dilatedV_orthonormal_recurrence
  rw [← h1]
  exact lanczosState_beta_eq_of_orthonormal_recurrence h0 horth hrec L.β_zero L.β_nonneg L.β_pos

end LanczosRun

end NLAlib
