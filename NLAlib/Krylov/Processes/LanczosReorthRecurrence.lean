/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosRecurrence
public import NLAlib.Krylov.Processes.ArnoldiRecurrence

/-!
# The Lanczos recurrence with full reorthogonalization

`NLAlib.lanczosReorthState A b j` is the state before step $j$ of Lanczos with full
reorthogonalization in exact arithmetic: Paige's order
$\mathbf{z}_j = \mathbf{A}\mathbf{q}_j - \beta_j\mathbf{q}_{j-1} - \alpha_j\mathbf{q}_j$ (as
`NLAlib.lanczosStep`), then two classical Gram–Schmidt passes of $\mathbf{z}_j$ against
$\mathbf{q}_0, \dots, \mathbf{q}_j$ (`NLAlib.cgsProject`), then normalization, with
$0^{-1} = 0$ at breakdown. The state also records the norm $\nu_j = \|\mathbf{z}_j\|$ before
orthogonalization, which the program stores. For every square $\mathbf{A}$ the recurrence is
total; for Hermitian $\mathbf{A}$ it is the Lanczos recurrence (the reorthogonalization subtracts
zeros). [Paige1970]. Design: `docs/design/Krylov-LanczosReorth.md` §2.3.

## Main definitions

* `NLAlib.cgsProject`: one exact classical Gram–Schmidt pass.
* `NLAlib.LanczosReorthState`, `NLAlib.lanczosReorthStep`, `NLAlib.lanczosReorthState`,
  `NLAlib.lanczosReorthMatrix`: the recurrence and its basis.

## Main results

* `Matrix.IsHermitian.lanczosReorthState_toLanczosState`,
  `Matrix.IsHermitian.lanczosReorthMatrix_eq`,
  `Matrix.IsHermitian.lanczosReorthState_nu`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- **One exact classical Gram–Schmidt pass** of $\mathbf{w}$ against $\mathbf{q}_0, \dots,
\mathbf{q}_{m-1}$: $\mathbf{w} - \sum_{i<m} (\mathbf{q}_i^{\mathsf{H}}\mathbf{w})\mathbf{q}_i$.
Algorithm: gram-schmidt -/
noncomputable def cgsProject (Q : ℕ → n → 𝕜) (m : ℕ) (w : n → 𝕜) : n → 𝕜 :=
  w - ∑ i ∈ Finset.range m, (star (Q i) ⬝ᵥ w) • Q i

/-- The state of the Lanczos recurrence with full reorthogonalization before step $j$: all
vectors $\mathbf{q}_0, \dots, \mathbf{q}_j$ (zero beyond $j$), the previous and current vectors,
$\beta_j$, and the norm $\nu_j$ of the last vector before orthogonalization ($0$ for $j = 0$).
Algorithm: lanczos-reorth -/
structure LanczosReorthState (𝕜 n : Type*) where
  /-- The vectors $\mathbf{q}_0, \dots, \mathbf{q}_j$, zero beyond $j$. -/
  vecs : ℕ → n → 𝕜
  /-- The previous vector $\mathbf{q}_{j-1}$ ($\mathbf{0}$ for $j = 0$). -/
  prev : n → 𝕜
  /-- The current vector $\mathbf{q}_j$. -/
  cur : n → 𝕜
  /-- The coefficient $\beta_j$. -/
  beta : ℝ
  /-- The norm $\nu_j$ before orthogonalization. -/
  nu : ℝ

/-- The plain Lanczos state underlying a reorthogonalized one. -/
def LanczosReorthState.toLanczosState (s : LanczosReorthState 𝕜 n) : LanczosState 𝕜 n :=
  ⟨s.prev, s.cur, s.beta⟩

/-- **Step $j$ of Lanczos with full reorthogonalization**: Paige's update, two classical
Gram–Schmidt passes against $\mathbf{q}_0, \dots, \mathbf{q}_j$, normalization.
Algorithm: lanczos-reorth -/
noncomputable def lanczosReorthStep (A : Matrix n n 𝕜) (j : ℕ) (s : LanczosReorthState 𝕜 n) :
    LanczosReorthState 𝕜 n :=
  let z := A *ᵥ s.cur - (s.beta : 𝕜) • s.prev - (lanczosAlpha A s.toLanczosState : 𝕜) • s.cur
  let z' := cgsProject s.vecs (j + 1) (cgsProject s.vecs (j + 1) z)
  let c := (‖WithLp.toLp 2 z'‖⁻¹ : 𝕜) • z'
  ⟨Function.update s.vecs (j + 1) c, s.cur, c, ‖WithLp.toLp 2 z'‖, ‖WithLp.toLp 2 z‖⟩

/-- **The Lanczos recurrence with full reorthogonalization**: the state before step $j$, from
$\mathbf{q}_0 = \mathbf{b}/\|\mathbf{b}\|$.
Algorithm: lanczos-reorth -/
noncomputable def lanczosReorthState (A : Matrix n n 𝕜) (b : n → 𝕜) :
    ℕ → LanczosReorthState 𝕜 n
  | 0 =>
    let q₀ := (‖WithLp.toLp 2 b‖⁻¹ : 𝕜) • b
    ⟨Function.update 0 0 q₀, 0, q₀, 0, 0⟩
  | j + 1 => lanczosReorthStep A j (lanczosReorthState A b j)

/-- The basis computed by $q$ steps of the reorthogonalized recurrence: column $j$ is
$\mathbf{q}_j$.
Algorithm: lanczos-reorth -/
noncomputable def lanczosReorthMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    Matrix n (Fin q) 𝕜 :=
  Matrix.of fun i j => (lanczosReorthState A b j).cur i

/-- The current Lanczos vector is the canonical column. -/
private theorem lanczosState_cur_eq_col [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (j : ℕ) :
    (lanczosState A b j).cur = (arnoldiMatrix A b (j + 1)).col (Fin.last j) := by
  funext i
  exact congrFun (congrFun (hA.lanczosMatrix_eq_arnoldiMatrix b (j + 1)) i) (Fin.last j)

/-- Distinct current Lanczos vectors are orthogonal. -/
private theorem star_cur_dotProduct_cur_of_ne {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) {i k : ℕ} (h : i ≠ k) :
    star (lanczosState A b i).cur ⬝ᵥ (lanczosState A b k).cur = 0 := by
  classical
  rw [lanczosState_cur_eq_col hA, lanczosState_cur_eq_col hA]
  exact star_arnoldiMatrix_col_last_dotProduct_of_ne A b h

/-- A current Lanczos vector is $\mathbf{0}$ or a unit vector. -/
private theorem cur_eq_zero_or_star_dotProduct_self {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (k : ℕ) :
    (lanczosState A b k).cur = 0 ∨
      star (lanczosState A b k).cur ⬝ᵥ (lanczosState A b k).cur = 1 := by
  classical
  rw [lanczosState_cur_eq_col hA]
  by_cases h : (arnoldiMatrix A b (k + 1)).col (Fin.last k) = 0
  · exact Or.inl h
  · refine Or.inr ?_
    have hk : k < krylovGrade A b := by
      by_contra hc
      exact h (arnoldiMatrix_col_last_eq_zero_iff.mpr (not_lt.mp hc))
    rw [EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq,
      norm_arnoldiMatrix_col_last hk, one_pow, RCLike.ofReal_one]

/-- The subdiagonal entry of the Lanczos compression. -/
private theorem star_cur_dotProduct_mulVec_cur_succ {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (k : ℕ) :
    star (lanczosState A b k).cur ⬝ᵥ (A *ᵥ (lanczosState A b (k + 1)).cur) =
      ((lanczosState A b (k + 1)).beta : 𝕜) := by
  classical
  have T := congrFun (congrFun (hA.lanczosTridiagonal_eq b (k + 2)) ⟨k, by omega⟩)
    ⟨k + 1, by omega⟩
  rw [Matrix.mul_assoc, conjTranspose_mul_apply] at T
  change _ = star ((arnoldiMatrix A b (k + 2)).col ⟨k, by omega⟩) ⬝ᵥ
    (A *ᵥ (arnoldiMatrix A b (k + 2)).col ⟨k + 1, by omega⟩) at T
  rw [arnoldiMatrix_col_eq_col_last A b (⟨k, by omega⟩ : Fin (k + 2)),
    arnoldiMatrix_col_eq_col_last A b (⟨k + 1, by omega⟩ : Fin (k + 2))] at T
  have hT : lanczosTridiagonal A b (k + 2) ⟨k, by omega⟩ ⟨k + 1, by omega⟩ =
      ((lanczosState A b (k + 1)).beta : 𝕜) := by
    have hk : ¬k = k + 1 + 1 := by omega
    simp [lanczosTridiagonal, Fin.ext_iff, hk]
  rw [hT] at T
  rw [lanczosState_cur_eq_col hA, lanczosState_cur_eq_col hA]
  exact T.symm

/-- Entries of the Lanczos compression above the subdiagonal vanish. -/
private theorem star_cur_dotProduct_mulVec_cur_of_lt {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) {i j : ℕ} (h : i + 1 < j) :
    star (lanczosState A b i).cur ⬝ᵥ (A *ᵥ (lanczosState A b j).cur) = 0 := by
  classical
  rw [lanczosState_cur_eq_col hA, lanczosState_cur_eq_col hA, hA.star_dotProduct_mulVec_comm,
    star_arnoldiMatrix_col_last_dotProduct_mulVec_of_lt A b h, star_zero]

/-- A three-term vector is orthogonal to a unit vector $\mathbf{c}$ with $\mathbf{c}^{\mathsf{H}}
\mathbf{p} = 0$, after the Lanczos coefficient $\alpha = \operatorname{Re}\mathbf{c}^{\mathsf{H}}
(\mathbf{A}\mathbf{c} - \beta\mathbf{p})$ is removed. -/
private theorem star_dotProduct_lanczosW {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c p : n → 𝕜}
    {β : ℝ} (hp : star c ⬝ᵥ p = 0) (hc : c = 0 ∨ star c ⬝ᵥ c = 1) :
    star c ⬝ᵥ (A *ᵥ c - (β : 𝕜) • p -
      (RCLike.re (star c ⬝ᵥ (A *ᵥ c - (β : 𝕜) • p)) : 𝕜) • c) = 0 := by
  have hx : star c ⬝ᵥ (A *ᵥ c - (β : 𝕜) • p) = star c ⬝ᵥ (A *ᵥ c) := by
    rw [dotProduct_sub, dotProduct_smul, hp, smul_zero, sub_zero]
  have hr : (RCLike.re (star c ⬝ᵥ (A *ᵥ c - (β : 𝕜) • p)) : 𝕜) =
      star c ⬝ᵥ (A *ᵥ c - (β : 𝕜) • p) := by
    rw [hx]
    exact hA.coe_re_quadForm c
  rcases hc with rfl | hc1
  · simp
  rw [dotProduct_sub, dotProduct_smul, hc1, smul_eq_mul, mul_one, hr, sub_self]

/-- **The three-term vector of step $j$ is orthogonal to $\mathbf{q}_0, \dots, \mathbf{q}_j$**
(exact arithmetic, Hermitian $\mathbf{A}$). -/
private theorem star_cur_dotProduct_lanczosW {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) {i j : ℕ} (hi : i ≤ j) :
    star (lanczosState A b i).cur ⬝ᵥ (A *ᵥ (lanczosState A b j).cur -
      ((lanczosState A b j).beta : 𝕜) • (lanczosState A b j).prev -
      (lanczosAlpha A (lanczosState A b j) : 𝕜) • (lanczosState A b j).cur) = 0 := by
  classical
  cases j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact star_dotProduct_lanczosW hA (dotProduct_zero _)
      (cur_eq_zero_or_star_dotProduct_self hA b 0)
  | succ k =>
    rcases hi.eq_or_lt with rfl | hlt
    · exact star_dotProduct_lanczosW hA (star_cur_dotProduct_cur_of_ne hA b (by omega))
        (cur_eq_zero_or_star_dotProduct_self hA b (k + 1))
    have hprev : (lanczosState A b (k + 1)).prev = (lanczosState A b k).cur := rfl
    rw [hprev]
    have h2 : star (lanczosState A b k).cur ⬝ᵥ (lanczosState A b (k + 1)).cur = 0 :=
      star_cur_dotProduct_cur_of_ne hA b (by omega)
    have h1 := star_cur_dotProduct_mulVec_cur_succ hA b k
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rcases (show i = k ∨ i + 1 < k + 1 by omega) with h | h
    · rw [h]
      rcases cur_eq_zero_or_star_dotProduct_self hA b k with h3 | h3
      · rw [h3] at h1 ⊢
        simp at h1 ⊢
      · rw [h1, h2, h3]
        simp
    · rw [star_cur_dotProduct_mulVec_cur_of_lt hA b h,
        star_cur_dotProduct_cur_of_ne hA b (show i ≠ k by omega),
        star_cur_dotProduct_cur_of_ne hA b (show i ≠ k + 1 by omega)]
      simp

/-- **Exact full reorthogonalization changes nothing for Hermitian matrices**: for Hermitian
$\mathbf{A}$, every $\mathbf{b}$ and every $j$, the state of the reorthogonalized recurrence
restricts to the Lanczos state, and its stored vectors are the Lanczos vectors
$\mathbf{q}_0, \dots, \mathbf{q}_j$ (zero beyond $j$). No breakdown hypothesis: after breakdown
every vector involved is zero. [Paige1970, §2, (2.1)–(2.7)]; [Parlett1998, §13.1] for the exact
orthogonality.
Result: lanczos-reorth-exact-arithmetic -/
theorem _root_.Matrix.IsHermitian.lanczosReorthState_toLanczosState {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (j : ℕ) :
    (lanczosReorthState A b j).toLanczosState = lanczosState A b j ∧
      ∀ i, (lanczosReorthState A b j).vecs i =
        if i ≤ j then (lanczosState A b i).cur else 0 := by
  induction j with
  | zero =>
    refine ⟨rfl, fun i => ?_⟩
    by_cases hi : i = 0
    · subst hi
      simp [lanczosReorthState, lanczosState]
    · simp [lanczosReorthState, hi]
  | succ j ih =>
    obtain ⟨hs, hv⟩ := ih
    have hcur : (lanczosReorthState A b j).cur = (lanczosState A b j).cur :=
      congrArg LanczosState.cur hs
    have hz : A *ᵥ (lanczosReorthState A b j).cur -
        ((lanczosReorthState A b j).beta : 𝕜) • (lanczosReorthState A b j).prev -
        (lanczosAlpha A (lanczosReorthState A b j).toLanczosState : 𝕜) •
          (lanczosReorthState A b j).cur =
        A *ᵥ (lanczosState A b j).cur -
          ((lanczosState A b j).beta : 𝕜) • (lanczosState A b j).prev -
          (lanczosAlpha A (lanczosState A b j) : 𝕜) • (lanczosState A b j).cur := by
      rw [← hs]
      rfl
    have horth : ∀ i ≤ j, star ((lanczosReorthState A b j).vecs i) ⬝ᵥ
        (A *ᵥ (lanczosState A b j).cur - ((lanczosState A b j).beta : 𝕜) •
          (lanczosState A b j).prev - (lanczosAlpha A (lanczosState A b j) : 𝕜) •
          (lanczosState A b j).cur) = 0 := by
      intro i hi
      rw [hv i, if_pos hi]
      exact star_cur_dotProduct_lanczosW hA b hi
    have hcgs : cgsProject (lanczosReorthState A b j).vecs (j + 1)
        (A *ᵥ (lanczosState A b j).cur - ((lanczosState A b j).beta : 𝕜) •
          (lanczosState A b j).prev - (lanczosAlpha A (lanczosState A b j) : 𝕜) •
          (lanczosState A b j).cur) =
        A *ᵥ (lanczosState A b j).cur - ((lanczosState A b j).beta : 𝕜) •
          (lanczosState A b j).prev - (lanczosAlpha A (lanczosState A b j) : 𝕜) •
          (lanczosState A b j).cur := by
      refine sub_eq_self.mpr (Finset.sum_eq_zero fun i hi => ?_)
      rw [horth i (by have := Finset.mem_range.mp hi; omega), zero_smul]
    refine ⟨?_, fun i => ?_⟩
    · change (lanczosReorthStep A j (lanczosReorthState A b j)).toLanczosState = _
      dsimp only [lanczosReorthStep]
      rw [hz, hcgs, hcgs, hcur]
      rfl
    · change (lanczosReorthStep A j (lanczosReorthState A b j)).vecs i = _
      dsimp only [lanczosReorthStep]
      by_cases hi : i = j + 1
      · subst hi
        rw [Function.update_self, if_pos le_rfl, hz, hcgs, hcgs]
        rfl
      · rw [Function.update_of_ne hi, hv i]
        by_cases hle : i ≤ j
        · rw [if_pos hle, if_pos (by omega)]
        · rw [if_neg hle, if_neg (by omega)]

/-- The reorthogonalized basis is the Lanczos basis for Hermitian $\mathbf{A}$, for every
$\mathbf{b}$ and every number of steps. -/
theorem _root_.Matrix.IsHermitian.lanczosReorthMatrix_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (q : ℕ) : lanczosReorthMatrix A b q = lanczosMatrix A b q := by
  ext i j
  exact congrFun (congrArg LanczosState.cur
    (hA.lanczosReorthState_toLanczosState b (j : ℕ)).1) i

/-- The stored norm before orthogonalization is $\beta$: for Hermitian $\mathbf{A}$,
$\nu_{j+1} = \beta_{j+1}$ in exact arithmetic (nothing is subtracted). -/
theorem _root_.Matrix.IsHermitian.lanczosReorthState_nu {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (j : ℕ) :
    (lanczosReorthState A b (j + 1)).nu = (lanczosReorthState A b (j + 1)).beta := by
  have hs := (hA.lanczosReorthState_toLanczosState b j).1
  have hz : A *ᵥ (lanczosReorthState A b j).cur -
      ((lanczosReorthState A b j).beta : 𝕜) • (lanczosReorthState A b j).prev -
      (lanczosAlpha A (lanczosReorthState A b j).toLanczosState : 𝕜) •
        (lanczosReorthState A b j).cur =
      A *ᵥ (lanczosState A b j).cur - ((lanczosState A b j).beta : 𝕜) •
        (lanczosState A b j).prev - (lanczosAlpha A (lanczosState A b j) : 𝕜) •
        (lanczosState A b j).cur := by
    rw [← hs]
    rfl
  have hb : (lanczosReorthState A b (j + 1)).beta = (lanczosState A b (j + 1)).beta :=
    congrArg LanczosState.beta (hA.lanczosReorthState_toLanczosState b (j + 1)).1
  rw [hb]
  change (lanczosReorthStep A j (lanczosReorthState A b j)).nu =
    (lanczosStep A (lanczosState A b j)).beta
  dsimp only [lanczosReorthStep, lanczosStep]
  rw [hz]

end NLAlib
