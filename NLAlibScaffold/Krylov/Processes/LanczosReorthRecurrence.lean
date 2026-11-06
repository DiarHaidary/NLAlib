/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosReorthRecurrence
public import NLAlib.Krylov.Processes.ArnoldiRecurrence

/-!
# Exact Lanczos with full reorthogonalization is Lanczos for Hermitian matrices (scaffold)

Statements for `NLAlib/Krylov/Processes/LanczosReorthRecurrence.lean` (stage LANCZOS-REORTH,
design note `docs/design/Krylov-LanczosReorth.md` §2.3, ids A2, A3): for Hermitian $\mathbf{A}$
the two Gram–Schmidt passes subtract zero, so the reorthogonalized recurrence computes the
Lanczos states, basis and coefficients, and $\nu_j = \beta_j$; no breakdown hypothesis.

## Main results

* `Matrix.IsHermitian.lanczosReorthState_toLanczosState`,
  `Matrix.IsHermitian.lanczosReorthMatrix_eq`,
  `Matrix.IsHermitian.lanczosReorthState_nu`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

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
    simp [lanczosTridiagonal, Fin.ext_iff]
    intro h
    omega
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

/-- **Exact full reorthogonalization changes nothing for Hermitian matrices** (A2): for Hermitian
$\mathbf{A}$, every $\mathbf{b}$ and every $j$, the state of the reorthogonalized recurrence
restricts to the Lanczos state, and its stored vectors are the Lanczos vectors
$\mathbf{q}_0, \dots, \mathbf{q}_j$ (zero beyond $j$). No breakdown hypothesis: after breakdown
every vector involved is zero. [Paige1970]; [Parlett1998, §13.1] for the exact orthogonality.
Proof: strengthen to the invariant "`vecs i` $=$ `(lanczosState A b i).cur` for $i \le j$, zero
beyond, and the nonzero ones are orthonormal" and induct on $j$. In the step, $\mathbf{z}_j =
\mathbf{A}\mathbf{q}_j - \beta_j\mathbf{q}_{j-1} - \alpha_j\mathbf{q}_j$ is orthogonal to
$\mathbf{q}_0, \dots, \mathbf{q}_j$ in exact arithmetic: by `NLAlib.lanczosStep` it is
$\beta_{j+1}\mathbf{q}_{j+1}$, and the Lanczos vectors are the columns of the canonical basis
(`NLAlib.lanczosState_eq_lanczosC`, `Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix`), whose
distinct columns are orthogonal (`NLAlib.star_arnoldiMatrix_col_last_dotProduct_of_ne`, zero
columns included), so `NLAlib.cgsProject` returns its argument twice
(`Finset.sum_eq_zero`); the normalization is that of `NLAlib.lanczosStep`, and
`Function.update` extends the invariant. M, about 120 lines. -/
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
    have hprev : (lanczosReorthState A b j).prev = (lanczosState A b j).prev :=
      congrArg LanczosState.prev hs
    have hbeta : (lanczosReorthState A b j).beta = (lanczosState A b j).beta :=
      congrArg LanczosState.beta hs
    have hal : lanczosAlpha A (lanczosReorthState A b j).toLanczosState =
        lanczosAlpha A (lanczosState A b j) := by
      rw [hs]
    have hz : A *ᵥ (lanczosReorthState A b j).cur -
        ((lanczosReorthState A b j).beta : 𝕜) • (lanczosReorthState A b j).prev -
        (lanczosAlpha A (lanczosReorthState A b j).toLanczosState : 𝕜) •
          (lanczosReorthState A b j).cur =
        A *ᵥ (lanczosState A b j).cur -
          ((lanczosState A b j).beta : 𝕜) • (lanczosState A b j).prev -
          (lanczosAlpha A (lanczosState A b j) : 𝕜) • (lanczosState A b j).cur := by
      rw [hal, hcur, hbeta, hprev]
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

/-- **The reorthogonalized basis is the Lanczos basis** (A2) for Hermitian $\mathbf{A}$.
Proof: entrywise from `Matrix.IsHermitian.lanczosReorthState_toLanczosState` (the `cur` field),
`NLAlib.lanczosMatrix`, `NLAlib.lanczosReorthMatrix`. S, about 5 lines. -/
theorem _root_.Matrix.IsHermitian.lanczosReorthMatrix_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (q : ℕ) : lanczosReorthMatrix A b q = lanczosMatrix A b q := by
  sorry

/-- **The stored norm before orthogonalization is $\beta$** (A3): for Hermitian $\mathbf{A}$,
$\nu_{j+1} = \beta_{j+1}$ in exact arithmetic (nothing is subtracted).
Proof: unfold `NLAlib.lanczosReorthState` at $j + 1$ and `NLAlib.lanczosReorthStep`; the two
passes return $\mathbf{z}_j$ by the orthogonality in the proof of
`Matrix.IsHermitian.lanczosReorthState_toLanczosState`, so both fields are
$\|\mathbf{z}_j\|$. S, about 15 lines. -/
theorem _root_.Matrix.IsHermitian.lanczosReorthState_nu {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (j : ℕ) :
    (lanczosReorthState A b (j + 1)).nu = (lanczosReorthState A b (j + 1)).beta := by
  sorry

end NLAlib
