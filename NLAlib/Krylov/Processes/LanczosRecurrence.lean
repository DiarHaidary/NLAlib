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
* `NLAlib.lanczosState_eq_of_orthonormal_recurrence`,
  `NLAlib.lanczosState_beta_eq_of_orthonormal_recurrence`: an orthonormal three-term recurrence
  is the Lanczos recurrence.
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
zero from the following step on. [Paige1972, §2]; [Saad2011, §6.6]. It is the variant A(2, 7)
there, equations (2) to (5), (7) and (8), for real symmetric $\mathbf{A}$;
[Saad2003, Algorithm 6.15] is the same order. -/
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

The recurrence is compared with the state built from the columns
$\mathbf{q}_j$ = `(arnoldiMatrix A b (j + 1)).col (Fin.last j)` of the canonical basis and their
Gram–Schmidt coefficients $r_j \ge 0$, through the column API of
`NLAlib.Krylov.Processes.Lanczos`. -/

section Canonical

variable (A : Matrix n n 𝕜) (b : n → 𝕜)

/-- The diagonal Gram–Schmidt coefficient $r_j$ as a real number. -/
private noncomputable def lanczosR (j : ℕ) : ℝ :=
  RCLike.re (gramSchmidtR (krylovMatrix A b (j + 1)) (Fin.last j) (Fin.last j))

/-- The canonical value of $\beta_j$: $0$, then $r_j / r_{j-1}$. -/
private noncomputable def lanczosB : ℕ → ℝ
  | 0 => 0
  | j + 1 => lanczosR A b (j + 1) / lanczosR A b j

/-- The canonical value of $\mathbf{q}_{j-1}$: $\mathbf{0}$, then column $j - 1$. -/
private noncomputable def lanczosP : ℕ → n → 𝕜
  | 0 => 0
  | j + 1 => (arnoldiMatrix A b (j + 1)).col (Fin.last j)

/-- The canonical state before step $j$. -/
private noncomputable def lanczosC (j : ℕ) : LanczosState 𝕜 n :=
  ⟨lanczosP A b j, (arnoldiMatrix A b (j + 1)).col (Fin.last j), lanczosB A b j⟩

private theorem coe_lanczosR (j : ℕ) :
    (lanczosR A b j : 𝕜) = gramSchmidtR (krylovMatrix A b (j + 1)) (Fin.last j) (Fin.last j) := by
  obtain ⟨x, -, hx⟩ := RCLike.nonneg_iff_exists_ofReal.mp
    (gramSchmidtR_apply_self_nonneg (krylovMatrix A b (j + 1)) (Fin.last j))
  rw [lanczosR, ← hx, RCLike.ofReal_re]

private theorem coe_lanczosR_eq_star_dotProduct (j : ℕ) :
    (lanczosR A b j : 𝕜) =
      star ((arnoldiMatrix A b (j + 1)).col (Fin.last j)) ⬝ᵥ (A ^ j *ᵥ b) :=
  (coe_lanczosR A b j).trans (gramSchmidtR_krylovMatrix_apply A b (Fin.last j) (Fin.last j))

private theorem lanczosR_nonneg (j : ℕ) : 0 ≤ lanczosR A b j :=
  (RCLike.nonneg_iff.mp (gramSchmidtR_apply_self_nonneg (krylovMatrix A b (j + 1)) (Fin.last j))).1

private theorem lanczosR_eq_zero_iff {j : ℕ} : lanczosR A b j = 0 ↔ krylovGrade A b ≤ j := by
  rw [← RCLike.ofReal_eq_zero (K := 𝕜), coe_lanczosR,
    gramSchmidtR_krylovMatrix_apply_last_eq_zero_iff]

private theorem star_col_dotProduct_self {j : ℕ} (hj : lanczosR A b j ≠ 0) :
    star ((arnoldiMatrix A b (j + 1)).col (Fin.last j)) ⬝ᵥ
      (arnoldiMatrix A b (j + 1)).col (Fin.last j) = 1 := by
  rw [EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq,
    norm_arnoldiMatrix_col_last (not_le.mp fun h => hj ((lanczosR_eq_zero_iff A b).mpr h)),
    one_pow, RCLike.ofReal_one]

/-- A vector of $\mathcal{K}_q$ orthogonal to the first $q$ canonical vectors is zero. -/
private theorem eq_zero_of_mem_krylovSpace {q : ℕ} {d : n → 𝕜} (hd : d ∈ krylovSpace A b q)
    (h : ∀ i < q, star ((arnoldiMatrix A b (i + 1)).col (Fin.last i)) ⬝ᵥ d = 0) : d = 0 := by
  have hd' := hd
  rw [← range_arnoldiMatrix A b q] at hd'
  obtain ⟨c, hc⟩ := hd'
  refine dotProduct_star_self_eq_zero.mp ?_
  have h0 : star d ᵥ* arnoldiMatrix A b q = 0 := by
    funext k
    change star d ⬝ᵥ (arnoldiMatrix A b q).col k = 0
    rw [arnoldiMatrix_col_eq_col_last A b k, Matrix.star_dotProduct, h k k.2, star_zero]
  rw [show star d ⬝ᵥ d = star d ⬝ᵥ (arnoldiMatrix A b q *ᵥ c) from
    congrArg (star d ⬝ᵥ ·) hc.symm, Matrix.dotProduct_mulVec, h0, zero_dotProduct]

private theorem star_col_dotProduct_lanczosP (j : ℕ) :
    star ((arnoldiMatrix A b (j + 1)).col (Fin.last j)) ⬝ᵥ lanczosP A b j = 0 := by
  cases j with
  | zero => exact dotProduct_zero _
  | succ j => exact star_arnoldiMatrix_col_last_dotProduct_of_ne A b (by omega)

private theorem lanczosP_mem (j : ℕ) : lanczosP A b j ∈ krylovSpace A b (j + 1) := by
  cases j with
  | zero => exact Submodule.zero_mem _
  | succ j => exact krylovSpace_mono A b (by omega) (arnoldiMatrix_col_last_mem_krylovSpace A b j)

private theorem lanczosB_nonneg (j : ℕ) : 0 ≤ lanczosB A b j := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact div_nonneg (lanczosR_nonneg A b _) (lanczosR_nonneg A b _)

/-- The subdiagonal of the compression: $\mathbf{q}_{j+1}^{\mathsf{H}}\mathbf{A}\mathbf{q}_j =
r_{j+1} / r_j$, for every $\mathbf{A}$. -/
private theorem star_col_succ_dotProduct_mulVec (j : ℕ) :
    star ((arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1))) ⬝ᵥ
      (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) = (lanczosB A b (j + 1) : 𝕜) := by
  rw [lanczosB]
  by_cases hj : lanczosR A b j = 0
  · rw [arnoldiMatrix_col_last_eq_zero_iff.mpr ((lanczosR_eq_zero_iff A b).mp hj),
      Matrix.mulVec_zero, dotProduct_zero, hj, div_zero, RCLike.ofReal_zero]
  obtain ⟨y, hy, hjy⟩ := exists_gramSchmidtR_smul_arnoldiMatrix_col_last A b j
  rw [← coe_lanczosR] at hjy
  have h1 : (lanczosR A b j : 𝕜) • (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) =
      A ^ (j + 1) *ᵥ b - A *ᵥ y := by
    rw [← Matrix.mulVec_smul, hjy, Matrix.mulVec_sub, Matrix.mulVec_mulVec, pow_succ']
  have h2 := congrArg (star ((arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1))) ⬝ᵥ ·) h1
  simp only [dotProduct_smul, dotProduct_sub, smul_eq_mul] at h2
  rw [star_arnoldiMatrix_col_last_dotProduct_eq_zero_of_mem A b le_rfl
    (mulVec_mem_krylovSpace_succ hy), sub_zero, ← coe_lanczosR_eq_star_dotProduct] at h2
  have hj' : (lanczosR A b j : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hj
  rw [RCLike.ofReal_div, ← h2, mul_div_cancel_left₀ _ hj']

variable {A}

private theorem star_col_dotProduct_mulVec_of_lt' (hA : A.IsHermitian) {i j : ℕ}
    (h : i + 1 < j) :
    star ((arnoldiMatrix A b (i + 1)).col (Fin.last i)) ⬝ᵥ
      (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) = 0 := by
  rw [hA.star_dotProduct_mulVec_comm, star_arnoldiMatrix_col_last_dotProduct_mulVec_of_lt A b h,
    star_zero]

private theorem star_col_dotProduct_mulVec_succ (hA : A.IsHermitian) (j : ℕ) :
    star ((arnoldiMatrix A b (j + 1)).col (Fin.last j)) ⬝ᵥ
      (A *ᵥ (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1))) =
      (lanczosB A b (j + 1) : 𝕜) := by
  rw [hA.star_dotProduct_mulVec_comm, star_col_succ_dotProduct_mulVec, RCLike.star_def,
    RCLike.conj_ofReal]

/-- The computed $\alpha_j$ is the diagonal entry of the compression. -/
private theorem coe_lanczosAlpha_lanczosC (hA : A.IsHermitian) (j : ℕ) :
    (lanczosAlpha A (lanczosC A b j) : 𝕜) =
      star ((arnoldiMatrix A b (j + 1)).col (Fin.last j)) ⬝ᵥ
        (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) := by
  have h : lanczosAlpha A (lanczosC A b j) =
      RCLike.re (quadForm A ((arnoldiMatrix A b (j + 1)).col (Fin.last j))) := by
    rw [lanczosAlpha, lanczosC, dotProduct_sub, dotProduct_smul,
      star_col_dotProduct_lanczosP, smul_zero, sub_zero]
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
private theorem star_col_dotProduct_w (hA : A.IsHermitian) {j : ℕ}
    (hj : lanczosR A b j ≠ 0) {i : ℕ} (hi : i ≤ j) :
    star ((arnoldiMatrix A b (i + 1)).col (Fin.last i)) ⬝ᵥ
      (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j) - (lanczosB A b j : 𝕜) • lanczosP A b j -
        (lanczosAlpha A (lanczosC A b j) : 𝕜) • (arnoldiMatrix A b (j + 1)).col (Fin.last j)) =
      0 := by
  rw [dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rcases eq_or_lt_of_le hi with rfl | hi
  · rw [← coe_lanczosAlpha_lanczosC b hA, star_col_dotProduct_lanczosP,
      star_col_dotProduct_self A b hj]
    ring
  cases j with
  | zero => omega
  | succ j =>
    rw [star_arnoldiMatrix_col_last_dotProduct_of_ne A b (show i ≠ j + 1 by omega), lanczosP]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [star_col_dotProduct_mulVec_of_lt' b hA (show i + 1 < j + 1 by omega),
        star_arnoldiMatrix_col_last_dotProduct_of_ne A b (show i ≠ j by omega)]
      ring
    · have hi' : lanczosR A b i ≠ 0 := fun h => by
        have h1 := (lanczosR_eq_zero_iff A b).mp h
        have h2 : ¬ krylovGrade A b ≤ i + 1 := fun h' => hj ((lanczosR_eq_zero_iff A b).mpr h')
        omega
      rw [star_col_dotProduct_mulVec_succ b hA, star_col_dotProduct_self A b hi']
      ring

/-- The three-term vector $\mathbf{w}$ of step $j$ is $(r_{j+1}/r_j)\,\mathbf{q}_{j+1}$. -/
private theorem lanczosStep_w_eq (hA : A.IsHermitian) (j : ℕ) :
    A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j) - (lanczosB A b j : 𝕜) • lanczosP A b j -
        (lanczosAlpha A (lanczosC A b j) : 𝕜) • (arnoldiMatrix A b (j + 1)).col (Fin.last j) =
      (lanczosB A b (j + 1) : 𝕜) • (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)) := by
  by_cases hj : lanczosR A b j = 0
  · have hB : lanczosB A b j = 0 := by
      cases j with
      | zero => rfl
      | succ j => rw [lanczosB, hj, zero_div]
    rw [arnoldiMatrix_col_last_eq_zero_iff.mpr ((lanczosR_eq_zero_iff A b).mp hj), hB, lanczosB,
      hj, div_zero]
    simp
  obtain ⟨y, hy, hjy⟩ := exists_gramSchmidtR_smul_arnoldiMatrix_col_last A b j
  obtain ⟨y', hy', hjy'⟩ := exists_gramSchmidtR_smul_arnoldiMatrix_col_last A b (j + 1)
  rw [← coe_lanczosR] at hjy hjy'
  have hrj : (lanczosR A b j : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hj
  have h1 : (lanczosR A b j : 𝕜) • (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) =
      A ^ (j + 1) *ᵥ b - A *ᵥ y := by
    rw [← Matrix.mulVec_smul, hjy, Matrix.mulVec_sub, Matrix.mulVec_mulVec, pow_succ']
  have hd : (lanczosR A b j : 𝕜) • (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j) -
      (lanczosB A b j : 𝕜) • lanczosP A b j - (lanczosAlpha A (lanczosC A b j) : 𝕜) •
        (arnoldiMatrix A b (j + 1)).col (Fin.last j)) -
      (lanczosR A b (j + 1) : 𝕜) • (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)) =
        0 := by
    refine eq_zero_of_mem_krylovSpace A b (q := j + 1) ?_ fun i hi => ?_
    · have hdeq : (lanczosR A b j : 𝕜) • (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j) -
          (lanczosB A b j : 𝕜) • lanczosP A b j - (lanczosAlpha A (lanczosC A b j) : 𝕜) •
            (arnoldiMatrix A b (j + 1)).col (Fin.last j)) -
          (lanczosR A b (j + 1) : 𝕜) • (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)) =
          y' - A *ᵥ y - (lanczosR A b j : 𝕜) • ((lanczosB A b j : 𝕜) • lanczosP A b j) -
            (lanczosR A b j : 𝕜) • ((lanczosAlpha A (lanczosC A b j) : 𝕜) •
              (arnoldiMatrix A b (j + 1)).col (Fin.last j)) := by
        rw [smul_sub, smul_sub, h1, hjy']
        abel
      rw [hdeq]
      exact sub_mem (sub_mem (sub_mem hy' (mulVec_mem_krylovSpace_succ hy))
        (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (lanczosP_mem A b j))))
        (Submodule.smul_mem _ _ (Submodule.smul_mem _ _
          (arnoldiMatrix_col_last_mem_krylovSpace A b j)))
    · rw [dotProduct_sub, dotProduct_smul, dotProduct_smul,
        star_col_dotProduct_w b hA hj (Nat.lt_succ_iff.mp hi),
        star_arnoldiMatrix_col_last_dotProduct_of_ne A b (show i ≠ j + 1 by omega)]
      simp
  rw [sub_eq_zero] at hd
  rw [lanczosB, RCLike.ofReal_div, div_eq_inv_mul, ← smul_smul, ← hd, smul_smul,
    inv_mul_cancel₀ hrj, one_smul]

private theorem lanczosStep_lanczosC (hA : A.IsHermitian) (j : ℕ) :
    lanczosStep A (lanczosC A b j) = lanczosC A b (j + 1) := by
  have hc0 : lanczosB A b (j + 1) = 0 →
      (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)) = 0 := by
    intro h
    rw [lanczosB, div_eq_zero_iff] at h
    refine arnoldiMatrix_col_last_eq_zero_iff.mpr ?_
    rcases h with h | h
    · exact (lanczosR_eq_zero_iff A b).mp h
    · exact ((lanczosR_eq_zero_iff A b).mp h).trans (Nat.le_succ j)
  have hc1 : lanczosB A b (j + 1) ≠ 0 →
      ‖WithLp.toLp 2 ((arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)))‖ = 1 :=
    fun h => norm_arnoldiMatrix_col_last (not_le.mp fun h' =>
      (div_ne_zero_iff.mp h).1 ((lanczosR_eq_zero_iff A b).mpr h'))
  obtain ⟨hn, hv⟩ := norm_smul_and_inv_smul (lanczosB_nonneg A b (j + 1)) hc0 hc1
  rw [lanczosStep_eq (lanczosC A b j) (lanczosStep_w_eq b hA j), hv, hn]
  rfl

private theorem lanczosState_eq_lanczosC (hA : A.IsHermitian) (j : ℕ) :
    lanczosState A b j = lanczosC A b j := by
  induction j with
  | zero =>
    have h : (arnoldiMatrix A b (0 + 1)).col (Fin.last 0) = (‖WithLp.toLp 2 b‖⁻¹ : 𝕜) • b := by
      rw [arnoldiMatrix, show Fin.last 0 = ⊥ from rfl, gramSchmidtQ_col_bot]
      have hcol : (krylovMatrix A b (0 + 1)).col ⊥ = b := by
        ext i
        simp [show (⊥ : Fin 1) = 0 from rfl]
      rw [hcol]
    rw [lanczosState, lanczosC, h]
    rfl
  | succ j ih => rw [lanczosState, ih, lanczosStep_lanczosC b hA]

end Canonical

/-- **The Lanczos recurrence computes the canonical basis**, for Hermitian $\mathbf{A}$ and every
$q$, with no breakdown hypothesis: the basis computed by $q$ steps from $\mathbf{b}$ is
$\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q)$; past the grade both are zero.
[Saad2011, §6.6].
Result: lanczos-recurrence -/
theorem _root_.Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) : lanczosMatrix A b q = arnoldiMatrix A b q := by
  ext i j
  change (lanczosState A b j).cur i = _
  rw [lanczosState_eq_lanczosC b hA]
  exact congrFun (arnoldiMatrix_col_eq_col_last A b j).symm i

/-- **The Lanczos recurrence computes the compression**: for Hermitian $\mathbf{A}$ and every
$q$, the tridiagonal matrix computed by $q$ steps from $\mathbf{b}$ is
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ for the canonical basis
$\mathbf{Q} = \mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q)$.
[Saad2003, Theorem 6.19]; there the Arnoldi matrix $\mathbf{H}_m = \mathbf{V}_m^{\mathsf{T}}
\mathbf{A}\mathbf{V}_m$ ([Saad2003, Proposition 6.5]) of a real symmetric $\mathbf{A}$ is the
tridiagonal matrix of the Lanczos algorithm, before the process stops; here every $q$.
Result: lanczos-recurrence -/
theorem _root_.Matrix.IsHermitian.lanczosTridiagonal_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (q : ℕ) :
    lanczosTridiagonal A b q = (arnoldiMatrix A b q)ᴴ * A * arnoldiMatrix A b q := by
  ext i j
  rw [Matrix.mul_assoc, conjTranspose_mul_apply, arnoldiMatrix_col_eq_col_last A b i,
    show (A * arnoldiMatrix A b q).col j = A *ᵥ (arnoldiMatrix A b q).col j from rfl,
    arnoldiMatrix_col_eq_col_last A b j]
  simp only [lanczosTridiagonal, Matrix.of_apply, lanczosState_eq_lanczosC b hA]
  split_ifs with h1 h2 h3
  · subst h1
    exact coe_lanczosAlpha_lanczosC b hA i
  · rw [h2]
    exact (star_col_succ_dotProduct_mulVec A b j).symm
  · rw [h3]
    exact (star_col_dotProduct_mulVec_succ b hA i).symm
  · have h1' : (i : ℕ) ≠ j := fun h => h1 (Fin.ext h)
    rcases (show (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i by omega) with h | h
    · exact (star_col_dotProduct_mulVec_of_lt' b hA h).symm
    · exact (star_arnoldiMatrix_col_last_dotProduct_mulVec_of_lt A b h).symm

/-- **Lanczos breaks down exactly at the grade**: for Hermitian $\mathbf{A}$ and the recurrence
from $\mathbf{b}$, $\beta_{j+1} = 0$ iff $\nu \le j + 1$, $\nu$ the grade of $\mathbf{b}$.
[Saad2003, Proposition 6.6]; stated there for the Arnoldi process, of which Lanczos is the
symmetric case ([Saad2003, Theorem 6.19]), at the first zero coefficient; here the coefficient
stays zero from the grade on.
Result: lanczos-breakdown -/
theorem _root_.Matrix.IsHermitian.lanczosState_beta_eq_zero_iff {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (j : ℕ) :
    (lanczosState A b (j + 1)).beta = 0 ↔ krylovGrade A b ≤ j + 1 := by
  rw [lanczosState_eq_lanczosC b hA]
  change lanczosR A b (j + 1) / lanczosR A b j = 0 ↔ _
  rw [div_eq_zero_iff, lanczosR_eq_zero_iff, lanczosR_eq_zero_iff]
  omega

/-! ### Exact Lanczos from an orthonormal three-term recurrence

Orthonormal vectors that satisfy a three-term recurrence with $\beta_j > 0$ before the last step
are the Lanczos vectors of their first vector, and the coefficients are the Lanczos coefficients.
The finite-precision analysis reads its backward model as exact Lanczos through this. -/

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

/-- If $\mathbf{u}_0 = \mathbf{0}$, $\mathbf{u}_1, \dots, \mathbf{u}_{k+1}$ are orthonormal,
$\mathbf{A}\mathbf{u}_{j+1} = \beta_j\mathbf{u}_j + \alpha_{j+1}\mathbf{u}_{j+1}
+ \beta_{j+1}\mathbf{u}_{j+2}$ for $j < k$, $\beta_0 = 0$, $\beta_j > 0$ for $1 \le j < k$ and
$\beta_k \ge 0$, then the coefficient of the Lanczos state after $k$ steps from $\mathbf{u}_1$
is $\beta_k$. -/
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
