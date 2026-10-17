/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.Lanczos

/-!
# The Lanczos three-term recurrence

The Lanczos algorithm as a total recursion on a state indexed by the step: the state before step
$j$ holds $\mathbf{q}_{j-1}$, $\mathbf{q}_j$ and $\beta_j$, and a step forms
$\mathbf{w} = \mathbf{A}\mathbf{q}_j - \beta_j\mathbf{q}_{j-1} - \alpha_j\mathbf{q}_j$, then
$\beta_{j+1} = \|\mathbf{w}\|$ and $\mathbf{q}_{j+1} = \mathbf{w}/\beta_{j+1}$. Breakdown is a
value: with $0^{-1} = 0$ the vector after $\beta_{j+1} = 0$ is zero and the state stays zero.

The realisation theorems say that for Hermitian $\mathbf{A}$ the recurrence computes the
canonical Lanczos basis `arnoldiMatrix A b q` and its compression, for every $q$ and with no
breakdown hypothesis, because past the grade both the recurrence and the canonical basis are zero.
Breakdown happens exactly at the grade.

## Main definitions

* `NLAlib.LanczosState`, `NLAlib.lanczosAlpha`, `NLAlib.lanczosStep`, `NLAlib.lanczosState`.
* `NLAlib.lanczosMatrix`, `NLAlib.lanczosTridiagonal`: the computed basis and tridiagonal matrix.

## Main results

* `Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix`: the recurrence computes the Lanczos basis.
* `Matrix.IsHermitian.lanczosTridiagonal_eq`: it computes the compression.
* `Matrix.IsHermitian.lanczosState_beta_eq_zero_iff`: breakdown happens exactly at the grade.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The state of the Lanczos recurrence before step $j$: the vectors $\mathbf{q}_{j-1}$,
$\mathbf{q}_j$ and the coefficient $\beta_j$ that couples them. -/
structure LanczosState (𝕜 n : Type*) where
  /-- The previous Lanczos vector $\mathbf{q}_{j-1}$ ($\mathbf{0}$ for $j = 0$). -/
  prev : n → 𝕜
  /-- The current Lanczos vector $\mathbf{q}_j$. -/
  cur : n → 𝕜
  /-- The coefficient $\beta_j = \|\mathbf{w}_{j-1}\|$ ($0$ for $j = 0$). -/
  beta : ℝ

/-- The diagonal coefficient of a Lanczos step,
$\alpha_j = \operatorname{Re}\langle\mathbf{q}_j, \mathbf{A}\mathbf{q}_j - \beta_j
\mathbf{q}_{j-1}\rangle$; in exact arithmetic and for Hermitian $\mathbf{A}$ it is
$\mathbf{q}_j^{\mathsf{H}}\mathbf{A}\mathbf{q}_j$. -/
noncomputable def lanczosAlpha (A : Matrix n n 𝕜) (s : LanczosState 𝕜 n) : ℝ :=
  RCLike.re (star s.cur ⬝ᵥ (A *ᵥ s.cur - (s.beta : 𝕜) • s.prev))

/-- **One Lanczos step** in Paige's order:
$\mathbf{w} = \mathbf{A}\mathbf{q}_j - \beta_j\mathbf{q}_{j-1} - \alpha_j\mathbf{q}_j$,
$\beta_{j+1} = \|\mathbf{w}\|$, $\mathbf{q}_{j+1} = \beta_{j+1}^{-1}\mathbf{w}$. At breakdown,
$\beta_\nu = 0$ at the grade $\nu$, the state is $(\mathbf{q}_{\nu-1}, \mathbf{0}, 0)$, and it is
zero from the following step on. [Paige1972]; [Saad2011, §6.6]. -/
noncomputable def lanczosStep (A : Matrix n n 𝕜) (s : LanczosState 𝕜 n) : LanczosState 𝕜 n :=
  let w := A *ᵥ s.cur - (s.beta : 𝕜) • s.prev - (lanczosAlpha A s : 𝕜) • s.cur
  ⟨s.cur, (‖WithLp.toLp 2 w‖⁻¹ : 𝕜) • w, ‖WithLp.toLp 2 w‖⟩

/-- The **Lanczos recurrence**: the state before step $j$, from
$(\mathbf{0}, \mathbf{b}/\|\mathbf{b}\|, 0)$. [Saad2011, §6.6]. -/
noncomputable def lanczosState (A : Matrix n n 𝕜) (b : n → 𝕜) : ℕ → LanczosState 𝕜 n
  | 0 => ⟨0, (‖WithLp.toLp 2 b‖⁻¹ : 𝕜) • b, 0⟩
  | j + 1 => lanczosStep A (lanczosState A b j)

/-- The basis computed by $q$ steps of the Lanczos recurrence: column $j$ is $\mathbf{q}_j$. -/
noncomputable def lanczosMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) : Matrix n (Fin q) 𝕜 :=
  Matrix.of fun i j => (lanczosState A b j).cur i

/-- The tridiagonal matrix computed by the Lanczos recurrence: $\alpha_0, \dots, \alpha_{q-1}$ on
the diagonal, $\beta_1, \dots, \beta_{q-1}$ beside it. -/
noncomputable def lanczosTridiagonal (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    Matrix (Fin q) (Fin q) 𝕜 :=
  Matrix.of fun i j =>
    if i = j then (lanczosAlpha A (lanczosState A b i) : 𝕜)
    else if (i : ℕ) = j + 1 then ((lanczosState A b i).beta : 𝕜)
    else if (j : ℕ) = i + 1 then ((lanczosState A b j).beta : 𝕜)
    else 0

/-! ### The canonical Lanczos vectors

Column $j$ of `arnoldiMatrix A b q` does not depend on $q > j$; it is the vector `lanczosVec A b j`
below, with $r_j$ = `lanczosR A b j` $\ge 0$ its Gram–Schmidt coefficient. The recurrence is
compared with the state built from these. -/

section Canonical

variable (A : Matrix n n 𝕜) (b : n → 𝕜)

/-- Column $j$ of the canonical basis. -/
private noncomputable def lanczosVec (j : ℕ) : n → 𝕜 :=
  (arnoldiMatrix A b (j + 1)).col (Fin.last j)

/-- The diagonal Gram–Schmidt coefficient
$r_j = \mathbf{q}_j^{\mathsf{H}}\mathbf{A}^j\mathbf{b}$. -/
private noncomputable def lanczosR (j : ℕ) : ℝ :=
  RCLike.re (star (lanczosVec A b j) ⬝ᵥ (A ^ j *ᵥ b))

/-- The canonical value of $\beta_j$: $0$, then $r_j / r_{j-1}$. -/
private noncomputable def lanczosB : ℕ → ℝ
  | 0 => 0
  | j + 1 => lanczosR A b (j + 1) / lanczosR A b j

/-- The canonical value of $\mathbf{q}_{j-1}$: $\mathbf{0}$, then column $j - 1$. -/
private noncomputable def lanczosP : ℕ → n → 𝕜
  | 0 => 0
  | j + 1 => lanczosVec A b j

/-- The canonical state before step $j$. -/
private noncomputable def lanczosC (j : ℕ) : LanczosState 𝕜 n :=
  ⟨lanczosP A b j, lanczosVec A b j, lanczosB A b j⟩

private theorem arnoldiMatrix_col_eq (q : ℕ) (j : Fin q) :
    (arnoldiMatrix A b q).col j = lanczosVec A b j := by
  rw [lanczosVec, ← arnoldiMatrix_submatrix_castLE A b (Nat.succ_le_of_lt j.2)]
  ext i
  simp only [Matrix.col_apply, Matrix.submatrix_apply, id_eq]
  congr 1

/-- Distinct canonical vectors are orthogonal. -/
private theorem star_lanczosVec_dotProduct_of_ne {i k : ℕ} (hik : i ≠ k) :
    star (lanczosVec A b i) ⬝ᵥ lanczosVec A b k = 0 := by
  have h := congrFun (congrFun (conjTranspose_gramSchmidtQ_mul_self
    (krylovMatrix A b (max i k + 1))) ⟨i, by omega⟩) ⟨k, by omega⟩
  rw [conjTranspose_mul_apply, ← arnoldiMatrix, arnoldiMatrix_col_eq, arnoldiMatrix_col_eq,
    Matrix.diagonal_apply_ne _ (fun h => hik (congrArg Fin.val h))] at h
  exact h

private theorem gramSchmidtR_krylovMatrix_apply {q : ℕ} (i j : Fin q) :
    gramSchmidtR (krylovMatrix A b q) i j = star (lanczosVec A b i) ⬝ᵥ (A ^ (j : ℕ) *ᵥ b) := by
  rw [gramSchmidtR, conjTranspose_mul_apply, ← arnoldiMatrix, arnoldiMatrix_col_eq]
  rfl

private theorem coe_lanczosR (j : ℕ) :
    (lanczosR A b j : 𝕜) = star (lanczosVec A b j) ⬝ᵥ (A ^ j *ᵥ b) := by
  have h := gramSchmidtR_apply_self_nonneg (krylovMatrix A b (j + 1)) (Fin.last j)
  rw [gramSchmidtR_krylovMatrix_apply, Fin.val_last] at h
  obtain ⟨x, -, hx⟩ := RCLike.nonneg_iff_exists_ofReal.mp h
  rw [lanczosR, ← hx, RCLike.ofReal_re]

private theorem lanczosR_nonneg (j : ℕ) : 0 ≤ lanczosR A b j := by
  have h := gramSchmidtR_apply_self_nonneg (krylovMatrix A b (j + 1)) (Fin.last j)
  rw [gramSchmidtR_krylovMatrix_apply, Fin.val_last] at h
  exact (RCLike.nonneg_iff.mp h).1

private theorem gramSchmidtR_krylovMatrix_apply_self {q : ℕ} (j : Fin q) :
    gramSchmidtR (krylovMatrix A b q) j j = (lanczosR A b j : 𝕜) := by
  rw [gramSchmidtR_krylovMatrix_apply, coe_lanczosR]

private theorem star_lanczosVec_dotProduct_self {j : ℕ} (hj : lanczosR A b j ≠ 0) :
    star (lanczosVec A b j) ⬝ᵥ lanczosVec A b j = 1 := by
  have h := congrFun (congrFun (conjTranspose_gramSchmidtQ_mul_self
    (krylovMatrix A b (j + 1))) (Fin.last j)) (Fin.last j)
  rw [conjTranspose_mul_apply, ← arnoldiMatrix, arnoldiMatrix_col_eq, Matrix.diagonal_apply_eq,
    gramSchmidtR_krylovMatrix_apply_self, Fin.val_last,
    if_neg (RCLike.ofReal_ne_zero.mpr hj)] at h
  exact h

private theorem norm_lanczosVec {j : ℕ} (h : lanczosR A b j ≠ 0) :
    ‖WithLp.toLp 2 (lanczosVec A b j)‖ = 1 := by
  have h1 := star_lanczosVec_dotProduct_self A b h
  rw [EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, ← RCLike.ofReal_one,
    RCLike.ofReal_inj] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h1

private theorem lanczosVec_eq_zero {j : ℕ} (h : lanczosR A b j = 0) : lanczosVec A b j = 0 := by
  rw [lanczosVec, arnoldiMatrix, gramSchmidtQ_col_eq_zero_iff,
    gramSchmidtR_krylovMatrix_apply_self, Fin.val_last, h, RCLike.ofReal_zero]

private theorem lanczosVec_mem (j : ℕ) : lanczosVec A b j ∈ krylovSpace A b (j + 1) := by
  rw [← range_arnoldiMatrix A b (j + 1)]
  refine ⟨Pi.single (Fin.last j) 1, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  rfl

private theorem lanczosVec_mem_of_lt {j q : ℕ} (h : j < q) :
    lanczosVec A b j ∈ krylovSpace A b q :=
  krylovSpace_mono A b h (lanczosVec_mem A b j)

/-- The classical Gram–Schmidt recursion for the canonical vectors:
$r_j\mathbf{q}_j = \mathbf{A}^j\mathbf{b} - \mathbf{y}$ with $\mathbf{y} \in \mathcal{K}_j$. -/
private theorem exists_lanczosR_smul (j : ℕ) : ∃ y ∈ krylovSpace A b j,
    (lanczosR A b j : 𝕜) • lanczosVec A b j = A ^ j *ᵥ b - y := by
  have h := gramSchmidtR_apply_self_smul_col (krylovMatrix A b (j + 1)) (Fin.last j)
  rw [gramSchmidtR_krylovMatrix_apply_self, Fin.val_last] at h
  refine ⟨_, Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_, h⟩
  rw [← arnoldiMatrix, arnoldiMatrix_col_eq]
  have hk' := Finset.mem_Iio.mp hk
  rw [Fin.lt_def, Fin.val_last] at hk'
  exact lanczosVec_mem_of_lt A b hk'

/-- A canonical vector is orthogonal to the earlier Krylov spaces. -/
private theorem star_lanczosVec_dotProduct_eq_zero {i j : ℕ} (hij : j ≤ i) {x : n → 𝕜}
    (hx : x ∈ krylovSpace A b j) : star (lanczosVec A b i) ⬝ᵥ x = 0 := by
  rw [← range_arnoldiMatrix A b j] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec]
  convert zero_dotProduct c
  ext k
  change star (lanczosVec A b i) ⬝ᵥ (arnoldiMatrix A b j).col k = 0
  rw [arnoldiMatrix_col_eq]
  exact star_lanczosVec_dotProduct_of_ne A b (by omega)

/-- A vector of $\mathcal{K}_q$ orthogonal to the first $q$ canonical vectors is zero. -/
private theorem eq_zero_of_mem_krylovSpace {q : ℕ} {d : n → 𝕜} (hd : d ∈ krylovSpace A b q)
    (h : ∀ i < q, star (lanczosVec A b i) ⬝ᵥ d = 0) : d = 0 := by
  have hd' := hd
  rw [← range_arnoldiMatrix A b q] at hd'
  obtain ⟨c, hc⟩ := hd'
  refine dotProduct_star_self_eq_zero.mp ?_
  rw [show star d ⬝ᵥ d = star d ⬝ᵥ (arnoldiMatrix A b q *ᵥ c) from
    congrArg (star d ⬝ᵥ ·) hc.symm, Matrix.dotProduct_mulVec]
  convert zero_dotProduct c
  ext k
  change star d ⬝ᵥ (arnoldiMatrix A b q).col k = 0
  rw [arnoldiMatrix_col_eq, Matrix.star_dotProduct, h k k.2, star_zero]

/-- $r_j = 0$ exactly from the grade on. -/
private theorem lanczosR_eq_zero_iff {j : ℕ} : lanczosR A b j = 0 ↔ krylovGrade A b ≤ j := by
  obtain ⟨y, hy, hjy⟩ := exists_lanczosR_smul A b j
  rw [krylovGrade_le_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, RCLike.ofReal_zero, zero_smul, eq_comm, sub_eq_zero] at hjy
    exact hjy ▸ hy
  · have h0 := star_lanczosVec_dotProduct_eq_zero A b le_rfl h
    rw [← coe_lanczosR, RCLike.ofReal_eq_zero] at h0
    exact h0

private theorem star_lanczosVec_dotProduct_lanczosP (j : ℕ) :
    star (lanczosVec A b j) ⬝ᵥ lanczosP A b j = 0 := by
  cases j with
  | zero => exact dotProduct_zero _
  | succ j => exact star_lanczosVec_dotProduct_of_ne A b (by omega)

private theorem lanczosP_mem (j : ℕ) : lanczosP A b j ∈ krylovSpace A b (j + 1) := by
  cases j with
  | zero => exact Submodule.zero_mem _
  | succ j => exact lanczosVec_mem_of_lt A b (by omega)

private theorem lanczosB_nonneg (j : ℕ) : 0 ≤ lanczosB A b j := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact div_nonneg (lanczosR_nonneg A b _) (lanczosR_nonneg A b _)

/-- The subdiagonal of the compression: $\mathbf{q}_{j+1}^{\mathsf{H}}\mathbf{A}\mathbf{q}_j =
r_{j+1} / r_j$, for every $\mathbf{A}$. -/
private theorem star_lanczosVec_succ_dotProduct_mulVec (j : ℕ) :
    star (lanczosVec A b (j + 1)) ⬝ᵥ (A *ᵥ lanczosVec A b j) = (lanczosB A b (j + 1) : 𝕜) := by
  rw [lanczosB]
  by_cases hj : lanczosR A b j = 0
  · rw [lanczosVec_eq_zero A b hj, Matrix.mulVec_zero, dotProduct_zero, hj, div_zero,
      RCLike.ofReal_zero]
  obtain ⟨y, hy, hjy⟩ := exists_lanczosR_smul A b j
  have h1 : (lanczosR A b j : 𝕜) • (A *ᵥ lanczosVec A b j) = A ^ (j + 1) *ᵥ b - A *ᵥ y := by
    rw [← Matrix.mulVec_smul, hjy, Matrix.mulVec_sub, Matrix.mulVec_mulVec, pow_succ']
  have h2 := congrArg (star (lanczosVec A b (j + 1)) ⬝ᵥ ·) h1
  simp only [dotProduct_smul, dotProduct_sub, smul_eq_mul] at h2
  rw [star_lanczosVec_dotProduct_eq_zero A b le_rfl (mulVec_mem_krylovSpace_succ hy), sub_zero,
    ← coe_lanczosR] at h2
  have hj' : (lanczosR A b j : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hj
  rw [RCLike.ofReal_div, ← h2, mul_div_cancel_left₀ _ hj']

/-- Entries of the compression below the subdiagonal vanish, for every $\mathbf{A}$. -/
private theorem star_lanczosVec_dotProduct_mulVec_of_lt {i j : ℕ} (h : j + 1 < i) :
    star (lanczosVec A b i) ⬝ᵥ (A *ᵥ lanczosVec A b j) = 0 :=
  star_lanczosVec_dotProduct_eq_zero A b (by omega : j + 1 + 1 ≤ i)
    (mulVec_mem_krylovSpace_succ (lanczosVec_mem A b j))

variable {A}

private theorem star_lanczosVec_dotProduct_mulVec_of_lt' (hA : A.IsHermitian) {i j : ℕ}
    (h : i + 1 < j) : star (lanczosVec A b i) ⬝ᵥ (A *ᵥ lanczosVec A b j) = 0 := by
  rw [hA.star_dotProduct_mulVec_comm, star_lanczosVec_dotProduct_mulVec_of_lt A b h, star_zero]

private theorem star_lanczosVec_dotProduct_mulVec_succ (hA : A.IsHermitian) (j : ℕ) :
    star (lanczosVec A b j) ⬝ᵥ (A *ᵥ lanczosVec A b (j + 1)) = (lanczosB A b (j + 1) : 𝕜) := by
  rw [hA.star_dotProduct_mulVec_comm, star_lanczosVec_succ_dotProduct_mulVec, RCLike.star_def,
    RCLike.conj_ofReal]

/-- The computed $\alpha_j$ is the diagonal entry of the compression. -/
private theorem coe_lanczosAlpha_lanczosC (hA : A.IsHermitian) (j : ℕ) :
    (lanczosAlpha A (lanczosC A b j) : 𝕜) = star (lanczosVec A b j) ⬝ᵥ (A *ᵥ lanczosVec A b j) := by
  have h : lanczosAlpha A (lanczosC A b j) = RCLike.re (quadForm A (lanczosVec A b j)) := by
    rw [lanczosAlpha, lanczosC, dotProduct_sub, dotProduct_smul,
      star_lanczosVec_dotProduct_lanczosP, smul_zero, sub_zero]
    rfl
  rw [h, hA.coe_re_quadForm]
  rfl

omit [DecidableEq n] in
/-- Normalisation of a nonnegative multiple of a vector of norm $1$ (or of $\mathbf{0}$). -/
private theorem norm_smul_and_inv_smul {c : ℝ} (hc : 0 ≤ c) {v : n → 𝕜} (h0 : c = 0 → v = 0)
    (h1 : c ≠ 0 → ‖WithLp.toLp 2 v‖ = 1) :
    ‖WithLp.toLp 2 ((c : 𝕜) • v)‖ = c ∧
      (‖WithLp.toLp 2 ((c : 𝕜) • v)‖⁻¹ : 𝕜) • ((c : 𝕜) • v) = v := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [h0 rfl]
    simp
  · have hn : ‖WithLp.toLp 2 ((c : 𝕜) • v)‖ = c := by
      rw [WithLp.toLp_smul, norm_smul, h1 hc0, mul_one, RCLike.norm_ofReal, abs_of_nonneg hc]
    refine ⟨hn, ?_⟩
    rw [hn, smul_smul, inv_mul_cancel₀ (RCLike.ofReal_ne_zero.mpr hc0), one_smul]

omit [DecidableEq n] in
/-- A Lanczos step, given its three-term vector. -/
private theorem lanczosStep_eq (s : LanczosState 𝕜 n) {u : n → 𝕜}
    (h : A *ᵥ s.cur - (s.beta : 𝕜) • s.prev - (lanczosAlpha A s : 𝕜) • s.cur = u) :
    lanczosStep A s = ⟨s.cur, (‖WithLp.toLp 2 u‖⁻¹ : 𝕜) • u, ‖WithLp.toLp 2 u‖⟩ := by
  rw [← h]
  rfl

/-- Below the grade, the three-term vector of step $j$ is orthogonal to
$\mathbf{q}_0, \dots, \mathbf{q}_j$: Hermitian symmetry removes all but the last two terms of
the Gram–Schmidt sum. -/
private theorem star_lanczosVec_dotProduct_w (hA : A.IsHermitian) {j : ℕ}
    (hj : lanczosR A b j ≠ 0) {i : ℕ} (hi : i ≤ j) :
    star (lanczosVec A b i) ⬝ᵥ (A *ᵥ lanczosVec A b j - (lanczosB A b j : 𝕜) • lanczosP A b j -
      (lanczosAlpha A (lanczosC A b j) : 𝕜) • lanczosVec A b j) = 0 := by
  rw [dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rcases eq_or_lt_of_le hi with rfl | hi
  · rw [← coe_lanczosAlpha_lanczosC b hA, star_lanczosVec_dotProduct_lanczosP,
      star_lanczosVec_dotProduct_self A b hj]
    ring
  cases j with
  | zero => omega
  | succ j =>
    rw [star_lanczosVec_dotProduct_of_ne A b (show i ≠ j + 1 by omega), lanczosP]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [star_lanczosVec_dotProduct_mulVec_of_lt' b hA (show i + 1 < j + 1 by omega),
        star_lanczosVec_dotProduct_of_ne A b (show i ≠ j by omega)]
      ring
    · have hi' : lanczosR A b i ≠ 0 := fun h => by
        have h1 := (lanczosR_eq_zero_iff A b).mp h
        have h2 : ¬ krylovGrade A b ≤ i + 1 := fun h' => hj ((lanczosR_eq_zero_iff A b).mpr h')
        omega
      rw [star_lanczosVec_dotProduct_mulVec_succ b hA, star_lanczosVec_dotProduct_self A b hi']
      ring

/-- The three-term vector $\mathbf{w}$ of step $j$ is $(r_{j+1}/r_j)\,\mathbf{q}_{j+1}$. -/
private theorem lanczosStep_w_eq (hA : A.IsHermitian) (j : ℕ) :
    A *ᵥ lanczosVec A b j - (lanczosB A b j : 𝕜) • lanczosP A b j -
        (lanczosAlpha A (lanczosC A b j) : 𝕜) • lanczosVec A b j =
      (lanczosB A b (j + 1) : 𝕜) • lanczosVec A b (j + 1) := by
  by_cases hj : lanczosR A b j = 0
  · have hB : lanczosB A b j = 0 := by
      cases j with
      | zero => rfl
      | succ j => rw [lanczosB, hj, zero_div]
    rw [lanczosVec_eq_zero A b hj, hB, lanczosB, hj, div_zero]
    simp
  obtain ⟨y, hy, hjy⟩ := exists_lanczosR_smul A b j
  obtain ⟨y', hy', hjy'⟩ := exists_lanczosR_smul A b (j + 1)
  have hrj : (lanczosR A b j : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hj
  have h1 : (lanczosR A b j : 𝕜) • (A *ᵥ lanczosVec A b j) = A ^ (j + 1) *ᵥ b - A *ᵥ y := by
    rw [← Matrix.mulVec_smul, hjy, Matrix.mulVec_sub, Matrix.mulVec_mulVec, pow_succ']
  have hd : (lanczosR A b j : 𝕜) • (A *ᵥ lanczosVec A b j - (lanczosB A b j : 𝕜) •
      lanczosP A b j - (lanczosAlpha A (lanczosC A b j) : 𝕜) • lanczosVec A b j) -
      (lanczosR A b (j + 1) : 𝕜) • lanczosVec A b (j + 1) = 0 := by
    refine eq_zero_of_mem_krylovSpace A b (q := j + 1) ?_ fun i hi => ?_
    · have hdeq : (lanczosR A b j : 𝕜) • (A *ᵥ lanczosVec A b j - (lanczosB A b j : 𝕜) •
          lanczosP A b j - (lanczosAlpha A (lanczosC A b j) : 𝕜) • lanczosVec A b j) -
          (lanczosR A b (j + 1) : 𝕜) • lanczosVec A b (j + 1) =
          y' - A *ᵥ y - (lanczosR A b j : 𝕜) • ((lanczosB A b j : 𝕜) • lanczosP A b j) -
            (lanczosR A b j : 𝕜) • ((lanczosAlpha A (lanczosC A b j) : 𝕜) •
              lanczosVec A b j) := by
        rw [smul_sub, smul_sub, h1, hjy']
        abel
      rw [hdeq]
      exact sub_mem (sub_mem (sub_mem hy' (mulVec_mem_krylovSpace_succ hy))
        (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (lanczosP_mem A b j))))
        (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (lanczosVec_mem A b j)))
    · rw [dotProduct_sub, dotProduct_smul, dotProduct_smul,
        star_lanczosVec_dotProduct_w b hA hj (Nat.lt_succ_iff.mp hi),
        star_lanczosVec_dotProduct_of_ne A b (show i ≠ j + 1 by omega)]
      simp
  rw [sub_eq_zero] at hd
  rw [lanczosB, RCLike.ofReal_div, div_eq_inv_mul, ← smul_smul, ← hd, smul_smul,
    inv_mul_cancel₀ hrj, one_smul]

private theorem lanczosStep_lanczosC (hA : A.IsHermitian) (j : ℕ) :
    lanczosStep A (lanczosC A b j) = lanczosC A b (j + 1) := by
  have hc0 : lanczosB A b (j + 1) = 0 → lanczosVec A b (j + 1) = 0 := by
    intro h
    rw [lanczosB, div_eq_zero_iff] at h
    refine lanczosVec_eq_zero A b ?_
    rcases h with h | h
    · exact h
    · exact (lanczosR_eq_zero_iff A b).mpr
        (((lanczosR_eq_zero_iff A b).mp h).trans (Nat.le_succ j))
  have hc1 : lanczosB A b (j + 1) ≠ 0 → ‖WithLp.toLp 2 (lanczosVec A b (j + 1))‖ = 1 :=
    fun h => norm_lanczosVec A b (div_ne_zero_iff.mp h).1
  obtain ⟨hn, hv⟩ := norm_smul_and_inv_smul (lanczosB_nonneg A b (j + 1)) hc0 hc1
  rw [lanczosStep_eq (lanczosC A b j) (lanczosStep_w_eq b hA j), hv, hn]
  rfl

private theorem lanczosState_eq_lanczosC (hA : A.IsHermitian) (j : ℕ) :
    lanczosState A b j = lanczosC A b j := by
  induction j with
  | zero =>
    have h : lanczosVec A b 0 = (‖WithLp.toLp 2 b‖⁻¹ : 𝕜) • b := by
      rw [lanczosVec, arnoldiMatrix, show Fin.last 0 = ⊥ from rfl,
        gramSchmidtQ_col_bot]
      have hcol : (krylovMatrix A b (0 + 1)).col ⊥ = b := by
        ext i
        simp [show (⊥ : Fin 1) = 0 from rfl]
      rw [hcol]
    rw [lanczosState, lanczosC, h]
    rfl
  | succ j ih => rw [lanczosState, ih, lanczosStep_lanczosC b hA]

end Canonical

/-- **The Lanczos recurrence computes the canonical basis**, for Hermitian $\mathbf{A}$ and every
$q$, with no breakdown hypothesis: past the grade both are zero. [Saad2011, §6.6].
Result: lanczos-recurrence -/
theorem _root_.Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) : lanczosMatrix A b q = arnoldiMatrix A b q := by
  ext i j
  change (lanczosState A b j).cur i = _
  rw [lanczosState_eq_lanczosC b hA]
  exact congrFun (arnoldiMatrix_col_eq A b q j).symm i

/-- **The Lanczos recurrence computes the compression**: for Hermitian $\mathbf{A}$ and every
$q$, the computed tridiagonal matrix is $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ for the
canonical basis $\mathbf{Q}$. -/
theorem _root_.Matrix.IsHermitian.lanczosTridiagonal_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (q : ℕ) :
    lanczosTridiagonal A b q = (arnoldiMatrix A b q)ᴴ * A * arnoldiMatrix A b q := by
  ext i j
  rw [Matrix.mul_assoc, conjTranspose_mul_apply, arnoldiMatrix_col_eq,
    show (A * arnoldiMatrix A b q).col j = A *ᵥ (arnoldiMatrix A b q).col j from rfl,
    arnoldiMatrix_col_eq]
  simp only [lanczosTridiagonal, Matrix.of_apply, lanczosState_eq_lanczosC b hA]
  split_ifs with h1 h2 h3
  · subst h1
    exact coe_lanczosAlpha_lanczosC b hA i
  · rw [h2]
    exact (star_lanczosVec_succ_dotProduct_mulVec A b j).symm
  · rw [h3]
    exact (star_lanczosVec_dotProduct_mulVec_succ b hA i).symm
  · have h1' : (i : ℕ) ≠ j := fun h => h1 (Fin.ext h)
    rcases (show (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i by omega) with h | h
    · exact (star_lanczosVec_dotProduct_mulVec_of_lt' b hA h).symm
    · exact (star_lanczosVec_dotProduct_mulVec_of_lt A b h).symm

/-- **Lanczos breaks down exactly at the grade**: for Hermitian $\mathbf{A}$,
$\beta_{j+1} = 0$ iff $\nu \le j + 1$. -/
theorem _root_.Matrix.IsHermitian.lanczosState_beta_eq_zero_iff {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (j : ℕ) :
    (lanczosState A b (j + 1)).beta = 0 ↔ krylovGrade A b ≤ j + 1 := by
  rw [lanczosState_eq_lanczosC b hA]
  change lanczosR A b (j + 1) / lanczosR A b j = 0 ↔ _
  rw [div_eq_zero_iff, lanczosR_eq_zero_iff, lanczosR_eq_zero_iff]
  omega

end NLAlib
