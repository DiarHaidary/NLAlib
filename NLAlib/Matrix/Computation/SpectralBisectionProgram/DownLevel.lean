/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Levels
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.DownSlot

/-!
# The downward level of the spectral bisection program

One level of the downward pass of `NLAlib.eighProg` (`NLAlib.eighDownLevel`) takes the arenas from
holding the nodes of depth $d$ to holding those of depth $d + 1$ and the records of depth $d$
(`NLAlib.EighArenas.LevelHolds`, `NLAlib.EighArenas.RecordHolds`), as the node step
`NLAlib.eighStep` of the machine of the interpretation computes them.

## Main results

* `NLAlib.holds_of_exec_eighDownLevel`: what a successful level computes.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP2: the window of a slot lies in the records of depth $d$ (bases, outputs, eigenvalues, kinds,
splits) and the cells of depth $d + 1$; the sizes, node matrices and parameters of depth $d$ are
outside it. -/
private theorem ep2_win_cell {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hk1 : 1 ≤ k) (hk : lo + k ≤ n) (h : el1_win H n d lo k cs b i) :
    ((b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) ∧ H.LevelCell n d b i) ∨
      H.LevelCell n (d + 1) b i := by
  have e1 : 2 * n * (lo + k) ≤ 2 * (n * n) := by
    rw [show 2 * (n * n) = 2 * n * n by ring]; exact Nat.mul_le_mul_left _ hk
  have e2 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
  have e3 : 2 * (n * n) * (d + 1 + 1) = 2 * (n * n) * (d + 1) + 2 * (n * n) := by ring
  have e4 : n * (d + 1) = n * d + n := by ring
  have e5 : n * (d + 1 + 1) = n * (d + 1) + n := by ring
  unfold el1_win at h
  unfold EighArenas.LevelCell
  rcases h with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1⟩ | ⟨hb, j, hj1, hj2, -, hj⟩
  · refine Or.inl ⟨by rcases hb with h | h <;> simp [h],
      Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩⟩
  · exact Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩)
  · exact Or.inl ⟨Or.inr (Or.inr (Or.inl hb)), Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩)⟩
  · refine Or.inl ⟨by rcases hb with h | h <;> simp [h],
      Or.inr (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩)⟩
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl hb), by omega, by omega⟩))

set_option maxHeartbeats 1600000 in
-- The run unfolds the scope, seven instructions, two draw loops and the loop over the slots.
/-- EP2: `NLAlib.holds_of_exec_eighDownLevel` with the finer frame of its proof: of the cells of
depth $d$ only the records (bases, outputs, eigenvalues, kinds, splits) may change. -/
theorem ep2_holds_of_exec_eighDownLevel {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR)
    {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ} {st st' : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hnext : ∀ lo < n, ReadsIdx I.sem st.store p H.Sz (n * (d + 1) + lo) 0)
    (hpos : st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv Su Sg
      H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st = some st') :
    H.LevelHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1) ∧
      H.RecordHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (∀ q b i, b ≠ Su → b ≠ Sg →
        ¬ ((b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) ∧ H.LevelCell n d b i) →
        ¬ H.LevelCell n (d + 1) b i → st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos .uniform = st.pos .uniform + n ∧
      st'.pos .gaussian = st.pos .gaussian + 4 * (n * n) := by
  set M := eighTapeMachine I p mmR qrR with hM
  obtain ⟨hlev1, hlev2, hlev3, hlev4⟩ := hlev
  set tH := st.store.size with htH
  set S0 : Store P K := st.store.push (p, Array.replicate (5 : IExp ℕ).eval none) with hS0
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSzs, hKd, hKp, hLv⟩ := id hH
  obtain ⟨z0, o1, -, hl1, -, -⟩ := id hflag
  have lpar := Store.lt_size_of_read_eq_some hpar.1
  have lc := Store.lt_size_of_read_eq_some (hc.1.trans hl1)
  have lMa := hsz hMa
  have lUa := hsz hUa
  have lQa := hsz hQa
  have lEa := hsz hEa
  have lSz := hsz hSzs
  have lKd := hsz hKd
  have lKp := hsz hKp
  have lLv := hsz hLv
  have dLvc : H.Lv ≠ c := fun h => by simp [EighArenas.handles, h] at hbufs
  have dLvSu : H.Lv ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dLvSg : H.Lv ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzSu : H.Sz ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzSg : H.Sz ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzLv : H.Sz ≠ H.Lv := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaSu : H.Ma ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaSg : H.Ma ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaLv : H.Ma ≠ H.Lv := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparSu : par ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparSg : par ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dparLv : par ≠ H.Lv := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSu : c ≠ Su := fun h => by simp [EighArenas.handles, h] at hbufs
  have dcSg : c ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSuSg : Su ≠ Sg := fun h => by simp [EighArenas.handles, h] at hbufs
  have hpb : par ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hcb : c ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hSub : Su ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hSgb : Sg ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hbufs
  have hLvb : H.Lv ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hnd
  have hwinb : ∀ {lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}, el1_win H n d lo k cs b i →
      b < st.store.size := fun hw => by
    have := el1_win_buf hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  -- the scope
  change exec I (.seq (.alloc p _ _) .skip) st = some st' at h
  obtain ⟨s₂, h₀, e₀⟩ := el1_alloc_inv h
  subst e₀
  clear h
  -- the parameters of depth d + 1
  obtain ⟨v0, S1, hv0, hw0, h⟩ := el1_inv_litIdx h₀
  obtain ⟨a1, b1, v1, S2, ha1, hb1, hv1, hw1, h⟩ := el1_inv_bin h
  obtain ⟨a2, b2, v2, S3, ha2, hb2, hv2, hw2, h⟩ := el1_inv_bin h
  obtain ⟨a3, b3, v3, S4, ha3, hb3, hv3, hw3, h⟩ := el1_inv_bin h
  obtain ⟨a4, b4, v4, S5, ha4, hb4, hv4, hw4, h⟩ := el1_inv_bin h
  obtain ⟨a5, b5, v5, S6, ha5, hb5, hv5, hw5, h⟩ := el1_inv_bin h
  obtain ⟨a6, b6, v6, S7, ha6, hb6, hv6, hw6, h⟩ := el1_inv_bin h
  have hv0' : I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ) = some v0 := hv0
  have hw0' : S0.write p tH 0 v0 = some S1 := hw0
  have hw1' : S1.write p tH 2 v1 = some S2 := hw1
  have hw2' : S2.write p tH 3 v2 = some S3 := hw2
  have hw3' : S3.write p H.Lv (2 * (d + 1)) v3 = some S4 := hw3
  have hw4' : S4.write p tH 1 v4 = some S5 := hw4
  have hw5' : S5.write p tH 3 v5 = some S6 := hw5
  have hw6' : S6.write p H.Lv (2 * (d + 1) + 1) v6 = some S7 := hw6
  have hr0 : ∀ q b i, b < tH → S0.read q b i = st.store.read q b i :=
    fun q b i hb => Store.read_push_of_lt hb
  have dcT : c ≠ tH := by omega
  have dLvT : H.Lv ≠ tH := by omega
  -- the reads of the seven instructions
  have ea1 : S1.read p c 1 = st.store.read p c 1 := by
    rw [Store.read_of_write_eq_some_of_ne hw0' (Or.inl dcT), hr0 _ _ _ lc]
  have ea2 : S2.read p c 2 = st.store.read p c 2 := by
    rw [Store.read_of_write_eq_some_of_ne hw1' (Or.inl dcT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dcT), hr0 _ _ _ lc]
  have eb3 : S3.read p H.Lv (2 * d) = st.store.read p H.Lv (2 * d) := by
    rw [Store.read_of_write_eq_some_of_ne hw2' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dLvT), hr0 _ _ _ lLv]
  have ea4 : S4.read p c 0 = st.store.read p c 0 := by
    rw [Store.read_of_write_eq_some_of_ne hw3' (Or.inl dLvc.symm),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl dcT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl dcT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dcT), hr0 _ _ _ lc]
  have eb4 : S4.read p tH 0 = some v0 := by
    rw [Store.read_of_write_eq_some_of_ne hw3' (Or.inl dLvT.symm),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inr (by omega)),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inr (by omega)),
      Store.read_of_write_eq_some hw0']
  have ea5 : S5.read p c 0 = st.store.read p c 0 := by
    rw [Store.read_of_write_eq_some_of_ne hw4' (Or.inl dcT), ea4]
  have eb6 : S6.read p H.Lv (2 * d + 1) = st.store.read p H.Lv (2 * d + 1) := by
    rw [Store.read_of_write_eq_some_of_ne hw5' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw4' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw3' (Or.inr (by omega)),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl dLvT), hr0 _ _ _ lLv]
  have hb1' : b1 = v0 := Option.some_inj.mp (hb1.symm.trans (Store.read_of_write_eq_some hw0'))
  have hb2' : b2 = v1 := Option.some_inj.mp (hb2.symm.trans (Store.read_of_write_eq_some hw1'))
  have ha3' : a3 = v2 := Option.some_inj.mp (ha3.symm.trans (Store.read_of_write_eq_some hw2'))
  have hb4' : b4 = v0 := Option.some_inj.mp (hb4.symm.trans eb4)
  have hb5' : b5 = v4 := Option.some_inj.mp (hb5.symm.trans (Store.read_of_write_eq_some hw4'))
  have ha6' : a6 = v5 := Option.some_inj.mp (ha6.symm.trans (Store.read_of_write_eq_some hw5'))
  have ha1' : some a1 = I.sem.lit p ((2 : ℕ) : ℚ) := (ha1.symm.trans ea1).trans hc.2.1
  have ha2' : some a2 = some (M.div M.one (M.ofNat 2)) := (ha2.symm.trans ea2).trans hc.2.2.1
  have hb3' : some b3 = some (eighLevelParams M R₀ ε ℓ₀ d).1 := (hb3.symm.trans eb3).trans hlev3
  have ha4' : some a4 = I.sem.lit p 1 := (ha4.symm.trans ea4).trans hc.1
  have ha5' : some a5 = I.sem.lit p 1 := (ha5.symm.trans ea5).trans hc.1
  have hb6' : some b6 = some (eighLevelParams M R₀ ε ℓ₀ d).2 :=
    (hb6.symm.trans eb6).trans hlev4
  subst b1 b2 a3 b4 b5 a6
  -- the machine's values
  have mOne : M.one = a4 := by
    change (I.sem.lit p 1).getD default = a4
    rw [← ha4', Option.getD_some]
  have ea45 : a5 = a4 := Option.some_inj.mp (ha5'.trans ha4'.symm)
  subst a5
  have mTwo : M.ofNat 2 = a1 := by
    change (I.sem.lit p ((2 : ℕ) : ℚ)).getD default = a1
    rw [← ha1', Option.getD_some]
  have mL : M.ofNat (ℓ₀ + d) = v0 := by
    change (I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ)).getD default = v0
    rw [hv0', Option.getD_some]
  have hP1 : (eighLevelParams M R₀ ε ℓ₀ (d + 1)).1 = v3 := by
    change M.mul (M.add (M.div M.one (M.ofNat 2)) (M.div (M.ofNat 2) (M.ofNat (ℓ₀ + d))))
      (eighLevelParams M R₀ ε ℓ₀ d).1 = v3
    rw [← Option.some_inj.mp hb3', ← Option.some_inj.mp ha2', mTwo, mL]
    change (I.sem.bin p .mul ((I.sem.bin p .add a2 ((I.sem.bin p .div a1 v0).getD default)).getD
      default) b3).getD default = v3
    rw [hv1, Option.getD_some, hv2, Option.getD_some, hv3, Option.getD_some]
  have hP2 : (eighLevelParams M R₀ ε ℓ₀ (d + 1)).2 = v6 := by
    change M.mul (M.sub M.one (M.div M.one (M.ofNat (ℓ₀ + d))))
      (eighLevelParams M R₀ ε ℓ₀ d).2 = v6
    rw [← Option.some_inj.mp hb6', mOne, mL]
    change (I.sem.bin p .mul ((I.sem.bin p .sub a4 ((I.sem.bin p .div a4 v0).getD default)).getD
      default) b6).getD default = v6
    rw [hv4, Option.getD_some, hv5, Option.getD_some, hv6, Option.getD_some]
  -- the frame of the seven instructions
  have hr7 : ∀ q b i, b < tH → ¬ (b = H.Lv ∧ (i = 2 * (d + 1) ∨ i = 2 * (d + 1) + 1)) →
      S7.read q b i = st.store.read q b i := by
    intro q b i hb hL
    have hbT : b ≠ tH := by omega
    have hL' : b ≠ H.Lv ∨ (i ≠ 2 * (d + 1) ∧ i ≠ 2 * (d + 1) + 1) := by
      by_cases h' : b = H.Lv
      · exact Or.inr ⟨fun h'' => hL ⟨h', Or.inl h''⟩, fun h'' => hL ⟨h', Or.inr h''⟩⟩
      · exact Or.inl h'
    rw [Store.read_of_write_eq_some_of_ne hw6' (hL'.imp_right And.right),
      Store.read_of_write_eq_some_of_ne hw5' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw4' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw3' (hL'.imp_right And.left),
      Store.read_of_write_eq_some_of_ne hw2' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw1' (Or.inl hbT),
      Store.read_of_write_eq_some_of_ne hw0' (Or.inl hbT), hr0 _ _ _ hb]
  have hL1 : S7.read p H.Lv (2 * (d + 1)) = some v3 := by
    rw [Store.read_of_write_eq_some_of_ne hw6' (Or.inr (by omega)),
      Store.read_of_write_eq_some_of_ne hw5' (Or.inl dLvT),
      Store.read_of_write_eq_some_of_ne hw4' (Or.inl dLvT), Store.read_of_write_eq_some hw3']
  have hL2 : S7.read p H.Lv (2 * (d + 1) + 1) = some v6 := Store.read_of_write_eq_some hw6'
  have hsh7 : S7.shape = S0.shape := by
    rw [Store.shape_of_write_eq_some hw6', Store.shape_of_write_eq_some hw5',
      Store.shape_of_write_eq_some hw4', Store.shape_of_write_eq_some hw3',
      Store.shape_of_write_eq_some hw2', Store.shape_of_write_eq_some hw1',
      Store.shape_of_write_eq_some hw0']
  -- the draws
  obtain ⟨σu, hu, h⟩ := el1_seq h
  obtain ⟨σg, hg, h⟩ := el1_seq h
  obtain ⟨σe, he, h⟩ := el1_seq h
  rw [exec_skip, Option.some_inj] at h
  subst s₂
  obtain ⟨hush, hupos, hurd, hufr⟩ := el1_draw_loop hu
  obtain ⟨hgsh, hgpos, hgrd, hgfr⟩ := el1_draw_loop hg
  have hshg : σg.store.shape = S0.shape := hgsh.trans (hush.trans hsh7)
  have hSuR : ∀ w < n, σg.store.read p Su w = some (I.tape .uniform (n * d + w)) := by
    intro w hw
    rw [hgfr _ _ _ (Or.inl dSuSg), hurd w hw]
    change some (I.tape .uniform (st.pos .uniform + w)) = _
    rw [hpos.1]
  have hSgR : ∀ w < 4 * (n * n), σg.store.read p Sg w =
      some (I.tape .gaussian (4 * (n * n) * d + w)) := by
    intro w hw
    rw [hgrd w hw, hupos]
    simp [hpos.2]
  have hrg : ∀ q b i, b < tH → b ≠ Su → b ≠ Sg →
      ¬ (b = H.Lv ∧ (i = 2 * (d + 1) ∨ i = 2 * (d + 1) + 1)) →
      σg.store.read q b i = st.store.read q b i := fun q b i hb h1 h2 h3 => by
    rw [hgfr _ _ _ (Or.inl h2), hufr _ _ _ (Or.inl h1)]
    exact hr7 q b i hb h3
  have hS0sz : S0.size = tH + 1 := by rw [hS0, Array.size_push, htH]
  have hshape5 : S0.shape[tH]? = some (p, 5) := Store.getElem?_shape_push_size _ _ _
  have hSut : Su = tH → 1 ≤ n → n ≤ 5 := by
    intro hS hn
    obtain ⟨len, hlen, hi⟩ := Store.exists_getElem?_shape_of_read_eq_some (hSuR (n - 1) (by omega))
    rw [hshg, hS, hshape5, Option.some.injEq, Prod.mk.injEq] at hlen
    omega
  have hSgt : Sg = tH → 1 ≤ n → 4 * (n * n) ≤ 5 := by
    intro hS hn
    have hn2 : 0 < 4 * (n * n) := by positivity
    obtain ⟨len, hlen, hi⟩ :=
      Store.exists_getElem?_shape_of_read_eq_some (hSgR (4 * (n * n) - 1) (by omega))
    rw [hshg, hS, hshape5, Option.some.injEq, Prod.mk.injEq] at hlen
    omega
  have hH0 : H.Shaped σg.store p n D :=
    el1_shaped_of_eq (fun b hb => by
      rw [hshg, hS0, Store.getElem?_shape_push_of_lt _ (by
        simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)]) hH
  have htb : tH ∉ H.handles ++ [par, c] := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    omega
  have hnd' : H.handles.Nodup := hnd
  -- nodes of depth d: bounds and uniqueness
  have hbnd : ∀ {a : List Bool} {lo : ℕ} {y : EighNode K},
      eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y) → 1 ≤ y.k →
        1 ≤ n ∧ lo + y.k ≤ n := by
    intro a lo y hl hk
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exfalso
      cases a with
      | nil =>
        simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨-, rfl⟩ := hl
        exact absurd hk (by simp [hn])
      | cons b a =>
        have h0 : n ≤ 1 := by omega
        simp [eighLoc, eighStep, h0] at hl
    · exact ⟨hn, (eighLoc_bounds hn hl).2⟩
  have huniq : ∀ {a a' : List Bool} {lo : ℕ} {y y' : EighNode K}, a.length = d →
      a'.length = d → eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y) →
      eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a' = some (lo, y') → 1 ≤ n → y = y' := by
    intro a a' lo y y' ha ha' hl hl' hn
    by_cases hae : a = a'
    · subst hae
      rw [hl] at hl'
      simp only [Option.some.injEq, Prod.mk.injEq] at hl'
      exact hl'.2
    · have h1 := (eighLoc_bounds hn hl).1
      have h2 := (eighLoc_bounds hn hl').1
      rcases eighLoc_disjoint (ha.trans ha'.symm) hae hl hl' with h | h <;> omega
  -- the loop over the slots
  have hinv := forall_of_exec_loop_eq_some I (fun w (s : St P K C) =>
      s.store.shape = σg.store.shape ∧ s.pos = σg.pos ∧
      (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
          eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
        el1_done H I.sem s.store p M n F d R₀ β lo y) ∧
      ∀ q b i, (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
          eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
          ¬ el1_win H n d lo y.k (el1_childSlot (eighStep M n F R₀ β y.A y.R y.ε y.ℓ
            (eighTapeSample n d lo)) lo) b i) → ¬ (b = tH ∧ i = 4) →
        s.store.read q b i = σg.store.read q b i)
    ⟨rfl, rfl, fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ => rfl⟩ ?_ he
  swap
  · rintro w hw s₁ s₂ ⟨hsh1, hps1, hdn1, hfr1⟩ hex
    change w < n at hw
    have hn1 : 1 ≤ n := by omega
    have hrd1 : ∀ q b i, b ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] → ¬ (b = tH ∧ i = 4) →
        s₁.store.read q b i = σg.store.read q b i :=
      fun q b i hb ht => hfr1 q b i (fun _ _ _ _ => el1_not_win_buf hb) ht
    have hSz1 : ∀ i, i < n * (d + 1) → s₁.store.read p H.Sz i = st.store.read p H.Sz i :=
      fun i hi => (hfr1 _ _ _ (fun _ _ _ _ => el1_not_win_Sz hnd' hi) (fun h => by omega)).trans
        (hrg _ _ _ lSz dSzSu dSzSg fun h => dSzLv h.1)
    have he4 : (n * (d + 1)) = n * d + n := by ring
    by_cases hnode : ∃ (y : EighNode K) (a : List Bool), a.length = d ∧
        eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (w, y)
    · obtain ⟨y, a, ha, hl⟩ := hnode
      obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn1 hl
      obtain ⟨hyR, hyε, hyℓ⟩ := eighLoc_params hl
      rw [ha] at hyR hyε hyℓ
      have hkk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ (by omega)
      have e5 : 2 * n * w + 2 * (n * y.k) ≤ 2 * (n * n) := by
        have := Nat.mul_le_mul_left (2 * n) hkn
        nlinarith
      have e6 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
      obtain ⟨hdone, hfrW, hsh2, hps2⟩ := el1_slot_node hmm hqr p hflag hcmp n ℓ₀ F d D hd hlit htn
        H
        (par := par) (Su := Su) (Sg := Sg) (c := c) (t := tH) (s := s₁) (s' := s₂) (R₀ := R₀)
        (β := β) hk1 hkn hyℓ (el1_shaped_of_eq (fun b _ => by rw [hsh1]) hH0) hbufs htb
        (el1_readsIdx_congr (hSz1 _ (by omega)) (hlev1 a w y ha hl).1)
        (el1_holds_keep (hlev1 a w y ha hl).2 fun i h1 h2 =>
          (hfr1 _ _ _ (fun _ _ _ _ => el1_not_win_Ma hnd' (by omega)) (fun h => by omega)).trans
            (hrg _ _ _ lMa dMaSu dMaSg fun h => dMaLv h.1))
        (by
          rw [hrd1 p H.Lv (2 * d) hLvb (fun h => by omega),
            hrg p H.Lv (2 * d) lLv dLvSu dLvSg (fun h => by omega)]
          exact hlev3.trans (congrArg some hyR.symm))
        (by
          rw [hrd1 p H.Lv (2 * d + 1) hLvb (fun h => by omega),
            hrg p H.Lv (2 * d + 1) lLv dLvSu dLvSg (fun h => by omega)]
          exact hlev4.trans (congrArg some hyε.symm))
        ⟨by rw [hrd1 p par 0 hpb (fun h => by omega),
              hrg p par 0 lpar dparSu dparSg (fun h => dparLv h.1), hpar.1],
          by rw [hrd1 p par 2 hpb (fun h => by omega),
              hrg p par 2 lpar dparSu dparSg (fun h => dparLv h.1), hpar.2]⟩
        (fun hk2 => by
          have hSu4 : Su = tH → w ≠ 4 := fun hS => by have := hSut hS hn1; omega
          exact ⟨(hrd1 _ _ _ hSub fun h => hSu4 h.1 h.2).trans (hSuR w hw), hSu4⟩)
        (fun hk2 => by
          have hSgT : Sg ≠ tH := fun hS => by
            have := hSgt hS hn1
            have : 2 ≤ n := by omega
            nlinarith
          exact ⟨fun w' hw' => (hrd1 _ _ _ hSgb fun h => hSgT h.1).trans (hSgR w' hw'), hSgT⟩)
        ⟨by rw [hrd1 p c 0 hcb (fun h => by omega),
              hrg p c 0 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.1],
          by rw [hrd1 p c 1 hcb (fun h => by omega),
              hrg p c 1 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.1],
          by rw [hrd1 p c 2 hcb (fun h => by omega),
              hrg p c 2 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.2.1],
          by rw [hrd1 p c 3 hcb (fun h => by omega),
              hrg p c 3 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.2.2.1],
          by rw [hrd1 p c 4 hcb (fun h => by omega),
              hrg p c 4 lc dcSu dcSg (fun h => dLvc h.1.symm), hc.2.2.2.2]⟩ hex
      refine ⟨hsh2.trans hsh1, hps2.trans hps1, fun lo y' hlo hn' => ?_,
        fun q b i hall ht4 => ?_⟩
      · obtain ⟨a', ha', hl'⟩ := hn'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
        · have hk1' := (eighLoc_bounds hn1 hl').1
          have hkn' := (eighLoc_bounds hn1 hl').2
          have hdis : lo + y'.k ≤ w := by
            have hae : a' ≠ a := fun h => by
              subst h
              rw [hl] at hl'
              have := (Prod.mk.inj (Option.some_inj.mp hl')).1
              omega
            rcases eighLoc_disjoint (ha'.trans ha.symm) hae hl' hl with h | h <;> omega
          exact el1_done_congr hk1' hkn' (fun b i hwin => hfrW p b i
            (fun hw' => el1_win_disjoint hnd' hk1' hdis hwin hw')
            (fun h => by have := hwinb hwin; omega)) (hdn1 lo y' hlo ⟨a', ha', hl'⟩)
        · rw [← huniq ha ha' hl hl' hn1]
          exact hdone
      · rw [hfrW q b i (hall w y (Nat.lt_succ_self w) ⟨a, ha, hl⟩) ht4]
        exact hfr1 q b i (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4
    · have hSz0 := hlev2 w hw (fun a y ha hl => hnode ⟨y, a, ha, hl⟩)
      obtain ⟨hst, hps2⟩ := el1_slot_skip (s := s₁) (s' := s₂)
        (el1_readsIdx_congr (hSz1 _ (by omega)) hSz0) hex
      refine ⟨by rw [hst]; exact hsh1, hps2.trans hps1, fun lo y' hlo hn' => ?_,
        fun q b i hall ht4 => ?_⟩
      · rw [hst]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
        · exact hdn1 lo y' hlo hn'
        · obtain ⟨a', ha', hl'⟩ := hn'
          exact absurd ⟨y', a', ha', hl'⟩ hnode
      · rw [hst]
        exact hfr1 q b i (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4
  obtain ⟨hshe, hpse, hdne, hfre⟩ := hinv
  -- the pops
  have hSsz : σe.store.size = tH + 1 := by
    rw [Store.size_eq_of_shape_eq (hshe.trans hshg), hS0sz]
  have hpop : ∀ q b i, b < tH → Store.read (Array.pop σe.store) q b i = σe.store.read q b i :=
    fun q b i hb => Store.read_pop_of_lt (by omega)
  have hpopsz : (Array.pop σe.store).size = tH := by simp [Array.size_pop, hSsz]
  have hdoneF : ∀ (a : List Bool) (lo : ℕ) (y : EighNode K), a.length = d →
      eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y) → 1 ≤ y.k →
        el1_done H I.sem (Array.pop σe.store) p M n F d R₀ β lo y := by
    intro a lo y ha hl hk1
    obtain ⟨hn1, hkn⟩ := hbnd hl hk1
    exact el1_done_congr hk1 hkn (fun b i hwin => hpop p b i (hwinb hwin))
      (hdne lo y (by change lo < n; omega) ⟨a, ha, hl⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold EighArenas.LevelHolds
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- the children
      intro a' lo' y' ha' hl'
      obtain ⟨a, b, rfl⟩ : ∃ a b, a' = a ++ [b] := by
        rcases List.eq_nil_or_concat a' with h0 | ⟨L, b, h0⟩
        · subst h0; simp at ha'
        · exact ⟨L, b, by simpa using h0⟩
      have ha : a.length = d := by simpa using ha'
      rw [eighLoc_append_singleton] at hl'
      obtain ⟨⟨lo, y⟩, hl, hl2⟩ := Option.bind_eq_some_iff.mp hl'
      simp only [ha, Nat.zero_add] at hl2
      have hk1 : 1 ≤ y.k := by
        by_contra h0
        have h0' : y.k ≤ 1 := by omega
        simp [eighLoc, eighStep, h0'] at hl2
      exact (hdoneF a lo y ha hl hk1).2 b lo' y' hl2
    · -- the slots that start no node
      intro lo' hlo' hno
      refine el1_readsIdx_congr ?_ (hnext lo' hlo')
      rw [hpop p H.Sz (n * (d + 1) + lo') lSz,
        hfre p H.Sz (n * (d + 1) + lo') ?_ (fun h => by omega),
        hrg p H.Sz (n * (d + 1) + lo') lSz dSzSu dSzSg fun h => dSzLv h.1]
      intro lo y _ ⟨a, ha, hl⟩ hwin
      obtain ⟨j, hj, hij⟩ := el1_win_Sz hnd' hwin
      have hj' : j = lo' := by omega
      subst hj'
      obtain ⟨b, y', hl2⟩ := el1_childSlot_loc hj
      refine hno (a ++ [b]) y' (by simp [ha]) ?_
      rw [eighLoc_append_singleton, hl, Option.bind_some]
      simpa [ha] using hl2
    · rw [hpop p H.Lv (2 * (d + 1)) lLv,
        hfre p H.Lv (2 * (d + 1)) (fun _ _ _ _ => el1_not_win_buf hLvb) (fun h => by omega),
        hgfr p H.Lv (2 * (d + 1)) (Or.inl dLvSg), hufr p H.Lv (2 * (d + 1)) (Or.inl dLvSu), hL1]
      exact congrArg some hP1.symm
    · rw [hpop p H.Lv (2 * (d + 1) + 1) lLv,
        hfre p H.Lv (2 * (d + 1) + 1) (fun _ _ _ _ => el1_not_win_buf hLvb) (fun h => by omega),
        hgfr p H.Lv (2 * (d + 1) + 1) (Or.inl dLvSg), hufr p H.Lv (2 * (d + 1) + 1) (Or.inl dLvSu),
        hL2]
      exact congrArg some hP2.symm
  · -- the records
    unfold EighArenas.RecordHolds
    intro a lo y ha hl hk1
    exact (hdoneF a lo y ha hl hk1).1
  · -- the frame
    intro q b i hbSu hbSg h1 h2
    by_cases hb : b < tH
    · rw [hpop q b i hb, hfre q b i ?_ (fun h => by omega)]
      · exact hrg q b i hb hbSu hbSg fun h => h2 (Or.inr (Or.inr h))
      · intro lo y hlo ⟨a, ha, hl⟩ hwin
        change lo < n at hlo
        have hn1 : 1 ≤ n := by omega
        rcases ep2_win_cell (eighLoc_bounds hn1 hl).1 (eighLoc_bounds hn1 hl).2 hwin with
          h | h
        · exact h1 h
        · exact h2 h
    · rw [Store.read_eq_none_of_size_le (s := Array.pop σe.store) (q := q) (b := b) (i := i)
        (by omega), Store.read_eq_none_of_size_le (s := st.store) (q := q) (b := b) (i := i)
        (by omega)]
  · change Store.shape (Array.pop σe.store) = _
    rw [Store.shape_pop, hshe, hshg, hS0]
    simp [Store.shape]
  · change σe.pos .uniform = _
    rw [hpse, hgpos, hupos]
    simp
  · change σe.pos .gaussian = _
    rw [hpse, hgpos, hupos]
    simp

/-- One level of the downward pass: let the kernels of `I` be the routines `mmR`, `qrR` on
interleaved pairs, the semantics decide flags, with exact integer literals up to $n + 4$ and the
exact floor conversion; $M$ = `NLAlib.eighTapeMachine I p mmR qrR` and the root
$(n, \mathbf{A}, R_0, \varepsilon, \ell_0)$. A successful run of `NLAlib.eighDownLevel` at depth
$d < D$ from a state whose arenas hold the nodes of depth $d$ (`NLAlib.EighArenas.LevelHolds`) and
whose size cells of depth $d + 1$ all read $0$, with the tape positions $nd$ (uniform) and
$4n^2 d$ (Gaussian), the stored $R_0$, $\varepsilon$, $\beta$ in `par` and the constants in `c`
(cells $0$ to $4$: one, $\mathrm{fl}(2)$, $\mathrm{fl}(1/2)$, $-1$, the stored $\sqrt{1/2}$),
ends with the arenas holding the nodes of depth $d + 1$ and the
records of depth $d$ (`NLAlib.EighArenas.RecordHolds`); every cell outside depths $d$ and $d + 1$ of
the arenas and the sample buffers `Su`, `Sg` is unchanged, the store shape too, and the tape
positions advance by $n$ and $4n^2$. No printed source. -/
theorem holds_of_exec_eighDownLevel {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ} {st st' : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hnext : ∀ lo < n, ReadsIdx I.sem st.store p H.Sz (n * (d + 1) + lo) 0)
    (hpos : st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv Su Sg
      H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st = some st') :
    H.LevelHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1) ∧
      H.RecordHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (∀ q b i, b ≠ Su → b ≠ Sg → ¬ H.LevelCell n d b i → ¬ H.LevelCell n (d + 1) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos .uniform = st.pos .uniform + n ∧
      st'.pos .gaussian = st.pos .gaussian + 4 * (n * n) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ep2_holds_of_exec_eighDownLevel hmm hqr p hflag hcmp n ℓ₀ F d
    D hd
    hlit htn H hH hbufs hlev hnext hpos hpar hc h
  exact ⟨h1, h2, fun q b i hSu hSg hd1 hd2 => h3 q b i hSu hSg (fun h => hd1 h.2) hd2, h4, h5, h6⟩

end NLAlib
