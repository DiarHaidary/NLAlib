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


/-! #### Helpers of `NLAlib.holds_of_exec_eighDownLevel` -/

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The window of a slot lies in the records of depth $d$ (bases, outputs, eigenvalues, kinds,
splits) and the cells of depth $d + 1$; the sizes, node matrices and parameters of depth $d$ are
outside it. -/
private theorem levelCell_of_win {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hk1 : 1 ≤ k) (hk : lo + k ≤ n) (h : EighSlotWindow H n d lo k cs b i) :
    ((b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) ∧ H.LevelCell n d b i) ∨
      H.LevelCell n (d + 1) b i := by
  have e1 : 2 * n * (lo + k) ≤ 2 * (n * n) := by
    rw [show 2 * (n * n) = 2 * n * n by ring]; exact Nat.mul_le_mul_left _ hk
  have e2 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
  have e3 : 2 * (n * n) * (d + 1 + 1) = 2 * (n * n) * (d + 1) + 2 * (n * n) := by ring
  have e4 : n * (d + 1) = n * d + n := by ring
  have e5 : n * (d + 1 + 1) = n * (d + 1) + n := by ring
  unfold EighSlotWindow at h
  unfold EighArenas.LevelCell
  rcases h with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1⟩ | ⟨hb, j, hj1, hj2, -, hj⟩
  · refine Or.inl ⟨by rcases hb with h | h <;> simp [h],
      Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩⟩
  · exact Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩)
  · exact Or.inl ⟨Or.inr (Or.inr (Or.inl hb)), Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩)⟩
  · refine Or.inl ⟨by rcases hb with h | h <;> simp [h],
      Or.inr (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩)⟩
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl hb), by omega, by omega⟩))

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The disequalities of the arenas and the buffers `par`, `Su`, `Sg`, `c` that the downward level
uses, from their distinctness. -/
private theorem downLevel_bufs_ne {H : EighArenas} {par Su Sg c : ℕ}
    (h : (H.handles ++ [par, Su, Sg, c]).Nodup) :
    (H.Lv ≠ Su ∧ H.Lv ≠ Sg) ∧ (H.Sz ≠ Su ∧ H.Sz ≠ Sg ∧ H.Sz ≠ H.Lv) ∧
      (H.Ma ≠ Su ∧ H.Ma ≠ Sg ∧ H.Ma ≠ H.Lv) ∧ (par ≠ Su ∧ par ≠ Sg ∧ par ≠ H.Lv) ∧
      (c ≠ Su ∧ c ≠ Sg ∧ c ≠ H.Lv) ∧ Su ≠ Sg := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩ <;>
    intro e <;> simp [EighArenas.handles, e] at h

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The buffers `par`, `Su`, `Sg`, `c` and the window arena are none of the arenas a slot
writes, when the arenas and these buffers are distinct. -/
private theorem not_mem_slotBufs {H : EighArenas} {par Su Sg c x : ℕ}
    (h : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hx : x = par ∨ x = Su ∨ x = Sg ∨ x = c ∨ x = H.Lv) :
    x ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
  intro hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    rcases hm with e | e | e | e | e | e | e <;> simp [EighArenas.handles, e] at h

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A buffer that a slot writes is one of the arenas, so it lies below a bound of all of them. -/
private theorem lt_of_win {H : EighArenas} {tH n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hlt : ∀ x ∈ H.handles, x < tH) (hw : EighSlotWindow H n d lo k cs b i) : b < tH := by
  apply hlt
  have := mem_of_eighSlotWindow hw
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
  tauto

/-- The first four instructions of `NLAlib.eighDownLevel`, inverted: with the scratch buffer `tH`
distinct from `c` and `Lv`, $\mathrm{fl}(2)$ and $\mathrm{fl}(1/2)$ in the cells $1$, $2$ of `c`
and the window of depth $d$ in the cell $2d$ of `Lv`, they leave $\ell_0 + d$ in the cell $0$ of
`tH` and the window of depth $d + 1$ in the cell $2(d + 1)$ of `Lv`, keep the shape and the tape
positions, and change no other cell outside `tH`. -/
private theorem exec_window {p : P} {tH c Lv ℓ₀ d : ℕ} {eL e₁ e₀ : IExp ℕ} {R₀ ε : K}
    {t : Stmt P ι ℕ ℕ} {s s₂ : St P K C}
    (h : exec I (.seq (.instr (.litIdx p ⟨tH, 0⟩ eL))
      (.seq (.instr (.bin p .div ⟨tH, 2⟩ ⟨c, 1⟩ ⟨tH, 0⟩))
      (.seq (.instr (.bin p .add ⟨tH, 3⟩ ⟨c, 2⟩ ⟨tH, 2⟩))
      (.seq (.instr (.bin p .mul ⟨Lv, e₁⟩ ⟨tH, 3⟩ ⟨Lv, e₀⟩)) t)))) s = some s₂)
    (heL : eL.eval = ℓ₀ + d) (he₁ : e₁.eval = 2 * (d + 1)) (he₀ : e₀.eval = 2 * d)
    (hcT : c ≠ tH) (hLvT : Lv ≠ tH)
    (hc1 : s.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ))
    (hc2 : s.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
      (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)))
    (hR : s.store.read p Lv (2 * d) =
      some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1) :
    ∃ σ : St P K C, exec I t σ = some s₂ ∧ σ.pos = s.pos ∧ σ.store.shape = s.store.shape ∧
      σ.store.read p tH 0 = some ((eighTapeMachine I p mmR qrR).ofNat (ℓ₀ + d)) ∧
      σ.store.read p Lv (2 * (d + 1)) =
        some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ (d + 1)).1 ∧
      ∀ q b i, b ≠ tH → (b ≠ Lv ∨ i ≠ 2 * (d + 1)) →
        σ.store.read q b i = s.store.read q b i := by
  set M := eighTapeMachine I p mmR qrR
  obtain ⟨v0, S1, hv0, hw0, h⟩ := exists_of_exec_seq_litIdx h
  obtain ⟨a1, b1, v1, S2, ha1, hb1, hv1, hw1, h⟩ := exists_of_exec_seq_bin h
  obtain ⟨a2, b2, v2, S3, ha2, hb2, hv2, hw2, h⟩ := exists_of_exec_seq_bin h
  obtain ⟨a3, b3, v3, S4, ha3, hb3, hv3, hw3, h⟩ := exists_of_exec_seq_bin h
  rw [heL] at hv0
  change s.store.write p tH 0 v0 = some S1 at hw0
  change S1.read p c 1 = some a1 at ha1
  change S1.read p tH 0 = some b1 at hb1
  change S1.write p tH 2 v1 = some S2 at hw1
  change S2.read p c 2 = some a2 at ha2
  change S2.read p tH 2 = some b2 at hb2
  change S2.write p tH 3 v2 = some S3 at hw2
  change S3.read p tH 3 = some a3 at ha3
  change S3.read p Lv e₀.eval = some b3 at hb3
  change S3.write p Lv e₁.eval v3 = some S4 at hw3
  rw [he₀] at hb3
  rw [he₁] at hw3
  have rd := @Store.read_of_write_eq_some_of_ne P K _
  have eb1 : b1 = v0 := Option.some_inj.mp (hb1.symm.trans (Store.read_of_write_eq_some hw0))
  subst b1
  have eb2 : b2 = v1 := Option.some_inj.mp (hb2.symm.trans (Store.read_of_write_eq_some hw1))
  subst b2
  have ea3 : a3 = v2 := Option.some_inj.mp (ha3.symm.trans (Store.read_of_write_eq_some hw2))
  subst a3
  have ha1' : some a1 = I.sem.lit p ((2 : ℕ) : ℚ) :=
    ha1.symm.trans ((rd hw0 (Or.inl hcT)).trans hc1)
  have ha2' : some a2 = some (M.div M.one (M.ofNat 2)) :=
    ha2.symm.trans ((rd hw1 (Or.inl hcT)).trans ((rd hw0 (Or.inl hcT)).trans hc2))
  have hb3' : some b3 = some (eighLevelParams M R₀ ε ℓ₀ d).1 :=
    hb3.symm.trans ((rd hw2 (Or.inl hLvT)).trans ((rd hw1 (Or.inl hLvT)).trans
      ((rd hw0 (Or.inl hLvT)).trans hR)))
  have mTwo : M.ofNat 2 = a1 := by
    change (I.sem.lit p ((2 : ℕ) : ℚ)).getD default = a1
    rw [← ha1', Option.getD_some]
  have mL : M.ofNat (ℓ₀ + d) = v0 := by
    change (I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ)).getD default = v0
    rw [hv0, Option.getD_some]
  have hP1 : (eighLevelParams M R₀ ε ℓ₀ (d + 1)).1 = v3 := by
    change M.mul (M.add (M.div M.one (M.ofNat 2)) (M.div (M.ofNat 2) (M.ofNat (ℓ₀ + d))))
      (eighLevelParams M R₀ ε ℓ₀ d).1 = v3
    rw [← Option.some_inj.mp hb3', ← Option.some_inj.mp ha2', mTwo, mL]
    change (I.sem.bin p .mul ((I.sem.bin p .add a2 ((I.sem.bin p .div a1 v0).getD default)).getD
      default) b3).getD default = v3
    rw [hv1, Option.getD_some, hv2, Option.getD_some, hv3, Option.getD_some]
  refine ⟨_, h, rfl, ?_, ?_, ?_, fun q b i hb hi => ?_⟩
  · change S4.shape = _
    rw [Store.shape_of_write_eq_some hw3, Store.shape_of_write_eq_some hw2,
      Store.shape_of_write_eq_some hw1, Store.shape_of_write_eq_some hw0]
  · change S4.read p tH 0 = _
    rw [rd hw3 (Or.inl hLvT.symm), rd hw2 (Or.inr (by omega)), rd hw1 (Or.inr (by omega)),
      Store.read_of_write_eq_some hw0, mL]
  · change S4.read p Lv (2 * (d + 1)) = _
    rw [Store.read_of_write_eq_some hw3, hP1]
  · change S4.read q b i = _
    rw [rd hw3 hi, rd hw2 (Or.inl hb), rd hw1 (Or.inl hb), rd hw0 (Or.inl hb)]

/-- The next three instructions of `NLAlib.eighDownLevel`, inverted: with one in the cell $0$ of
`c`, $\ell_0 + d$ in the cell $0$ of `tH` and the tolerance of depth $d$ in the cell $2d + 1$ of
`Lv`, they leave the tolerance of depth $d + 1$ in the cell $2(d + 1) + 1$ of `Lv`, keep the shape
and the tape positions, and change no other cell outside `tH`. -/
private theorem exec_tolerance {p : P} {tH c Lv ℓ₀ d : ℕ} {e₁ e₀ : IExp ℕ} {R₀ ε : K}
    {t : Stmt P ι ℕ ℕ} {s s₂ : St P K C}
    (h : exec I (.seq (.instr (.bin p .div ⟨tH, 1⟩ ⟨c, 0⟩ ⟨tH, 0⟩))
      (.seq (.instr (.bin p .sub ⟨tH, 3⟩ ⟨c, 0⟩ ⟨tH, 1⟩))
      (.seq (.instr (.bin p .mul ⟨Lv, e₁⟩ ⟨tH, 3⟩ ⟨Lv, e₀⟩)) t))) s = some s₂)
    (he₁ : e₁.eval = 2 * (d + 1) + 1) (he₀ : e₀.eval = 2 * d + 1) (hcT : c ≠ tH)
    (hLvT : Lv ≠ tH) (hc0 : s.store.read p c 0 = I.sem.lit p 1)
    (hL : s.store.read p tH 0 = some ((eighTapeMachine I p mmR qrR).ofNat (ℓ₀ + d)))
    (hE : s.store.read p Lv (2 * d + 1) =
      some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).2) :
    ∃ σ : St P K C, exec I t σ = some s₂ ∧ σ.pos = s.pos ∧ σ.store.shape = s.store.shape ∧
      σ.store.read p Lv (2 * (d + 1) + 1) =
        some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ (d + 1)).2 ∧
      ∀ q b i, b ≠ tH → (b ≠ Lv ∨ i ≠ 2 * (d + 1) + 1) →
        σ.store.read q b i = s.store.read q b i := by
  set M := eighTapeMachine I p mmR qrR
  obtain ⟨a4, b4, v4, S5, ha4, hb4, hv4, hw4, h⟩ := exists_of_exec_seq_bin h
  obtain ⟨a5, b5, v5, S6, ha5, hb5, hv5, hw5, h⟩ := exists_of_exec_seq_bin h
  obtain ⟨a6, b6, v6, S7, ha6, hb6, hv6, hw6, h⟩ := exists_of_exec_seq_bin h
  change s.store.read p c 0 = some a4 at ha4
  change s.store.read p tH 0 = some b4 at hb4
  change s.store.write p tH 1 v4 = some S5 at hw4
  change S5.read p c 0 = some a5 at ha5
  change S5.read p tH 1 = some b5 at hb5
  change S5.write p tH 3 v5 = some S6 at hw5
  change S6.read p tH 3 = some a6 at ha6
  change S6.read p Lv e₀.eval = some b6 at hb6
  change S6.write p Lv e₁.eval v6 = some S7 at hw6
  rw [he₀] at hb6
  rw [he₁] at hw6
  have rd := @Store.read_of_write_eq_some_of_ne P K _
  have eb4 : b4 = M.ofNat (ℓ₀ + d) := Option.some_inj.mp (hb4.symm.trans hL)
  subst b4
  have eb5 : b5 = v4 := Option.some_inj.mp (hb5.symm.trans (Store.read_of_write_eq_some hw4))
  subst b5
  have ea6 : a6 = v5 := Option.some_inj.mp (ha6.symm.trans (Store.read_of_write_eq_some hw5))
  subst a6
  have ea5 : a5 = a4 := Option.some_inj.mp (ha5.symm.trans ((rd hw4 (Or.inl hcT)).trans ha4))
  subst a5
  have eb6 : b6 = (eighLevelParams M R₀ ε ℓ₀ d).2 := Option.some_inj.mp
    (hb6.symm.trans ((rd hw5 (Or.inl hLvT)).trans ((rd hw4 (Or.inl hLvT)).trans hE)))
  subst b6
  have mOne : M.one = a4 := by
    change (I.sem.lit p 1).getD default = a4
    rw [← hc0, ha4, Option.getD_some]
  have hP2 : (eighLevelParams M R₀ ε ℓ₀ (d + 1)).2 = v6 := by
    change M.mul (M.sub M.one (M.div M.one (M.ofNat (ℓ₀ + d))))
      (eighLevelParams M R₀ ε ℓ₀ d).2 = v6
    rw [mOne]
    change (I.sem.bin p .mul ((I.sem.bin p .sub a4 ((I.sem.bin p .div a4
      (M.ofNat (ℓ₀ + d))).getD default)).getD default) (eighLevelParams M R₀ ε ℓ₀ d).2).getD
      default = v6
    rw [hv4, Option.getD_some, hv5, Option.getD_some, hv6, Option.getD_some]
  refine ⟨_, h, rfl, ?_, ?_, fun q b i hb hi => ?_⟩
  · change S7.shape = _
    rw [Store.shape_of_write_eq_some hw6, Store.shape_of_write_eq_some hw5,
      Store.shape_of_write_eq_some hw4]
  · change S7.read p Lv (2 * (d + 1) + 1) = _
    rw [Store.read_of_write_eq_some hw6, hP2]
  · change S7.read q b i = _
    rw [rd hw6 hi, rd hw5 (Or.inl hb), rd hw4 (Or.inl hb)]

/-- The instructions and draws of `NLAlib.eighDownLevel` before its slot loop, inverted: with the
scratch buffer `tH` and the constants and parameters of depth $d$ stored, they leave the
parameters of depth $d + 1$ in the cells $2(d + 1)$, $2(d + 1) + 1$ of `Lv` and the $n$ uniform and
$4n^2$ Gaussian draws of depth $d$ in `Su` and `Sg`, advance the tape positions by $n$ and $4n^2$,
keep the shape, and change no other cell outside `tH`. -/
private theorem exec_downLevel_prefix {p : P} {tH c Lv Su Sg n ℓ₀ d : ℕ} {R₀ ε : K}
    {eL e₁ e₀ e₁' e₀' mu mg : IExp ℕ} {t : Stmt P ι ℕ ℕ} {s s₂ : St P K C}
    (h : exec I (.seq (.instr (.litIdx p ⟨tH, 0⟩ eL))
      (.seq (.instr (.bin p .div ⟨tH, 2⟩ ⟨c, 1⟩ ⟨tH, 0⟩))
      (.seq (.instr (.bin p .add ⟨tH, 3⟩ ⟨c, 2⟩ ⟨tH, 2⟩))
      (.seq (.instr (.bin p .mul ⟨Lv, e₁⟩ ⟨tH, 3⟩ ⟨Lv, e₀⟩))
      (.seq (.instr (.bin p .div ⟨tH, 1⟩ ⟨c, 0⟩ ⟨tH, 0⟩))
      (.seq (.instr (.bin p .sub ⟨tH, 3⟩ ⟨c, 0⟩ ⟨tH, 1⟩))
      (.seq (.instr (.bin p .mul ⟨Lv, e₁'⟩ ⟨tH, 3⟩ ⟨Lv, e₀'⟩))
      (.seq (.loop mu fun w => (Builder.ins (ι := ι) (.draw p .uniform ⟨Su, .var w⟩)).run)
      (.seq (.loop mg fun w => (Builder.ins (ι := ι) (.draw p .gaussian ⟨Sg, .var w⟩)).run)
        t))))))))) s = some s₂)
    (heL : eL.eval = ℓ₀ + d) (he₁ : e₁.eval = 2 * (d + 1)) (he₀ : e₀.eval = 2 * d)
    (he₁' : e₁'.eval = 2 * (d + 1) + 1) (he₀' : e₀'.eval = 2 * d + 1) (hmu : mu.eval = n)
    (hmg : mg.eval = 4 * (n * n)) (hcT : c ≠ tH) (hLvT : Lv ≠ tH) (hLvSu : Lv ≠ Su)
    (hLvSg : Lv ≠ Sg) (hSuSg : Su ≠ Sg)
    (hc0 : s.store.read p c 0 = I.sem.lit p 1)
    (hc1 : s.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ))
    (hc2 : s.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
      (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)))
    (hR : s.store.read p Lv (2 * d) =
      some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1)
    (hE : s.store.read p Lv (2 * d + 1) =
      some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).2)
    (hpu : s.pos .uniform = n * d) (hpg : s.pos .gaussian = 4 * (n * n) * d) :
    ∃ σ : St P K C, exec I t σ = some s₂ ∧ σ.store.shape = s.store.shape ∧
      σ.pos .uniform = n * d + n ∧ σ.pos .gaussian = 4 * (n * n) * d + 4 * (n * n) ∧
      (∀ w < n, σ.store.read p Su w = some (I.tape .uniform (n * d + w))) ∧
      (∀ w < 4 * (n * n), σ.store.read p Sg w =
        some (I.tape .gaussian (4 * (n * n) * d + w))) ∧
      σ.store.read p Lv (2 * (d + 1)) =
        some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ (d + 1)).1 ∧
      σ.store.read p Lv (2 * (d + 1) + 1) =
        some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ (d + 1)).2 ∧
      ∀ q b i, b ≠ tH → b ≠ Su → b ≠ Sg →
        ¬ (b = Lv ∧ (i = 2 * (d + 1) ∨ i = 2 * (d + 1) + 1)) →
        σ.store.read q b i = s.store.read q b i := by
  obtain ⟨σ₄, h, hp₄, hsh₄, hL₄, hW₄, hfr₄⟩ := exec_window h heL he₁ he₀ hcT hLvT hc1 hc2 hR
  obtain ⟨σ₇, h, hp₇, hsh₇, hE₇, hfr₇⟩ := exec_tolerance h he₁' he₀' hcT hLvT
    ((hfr₄ _ _ _ hcT (Or.inr (by omega))).trans hc0) hL₄
    ((hfr₄ _ _ _ hLvT (Or.inr (by omega))).trans hE)
  obtain ⟨σu, hu, h⟩ := exists_exec_and_exec_of_exec_seq h
  obtain ⟨σg, hg, h⟩ := exists_exec_and_exec_of_exec_seq h
  obtain ⟨hush, hupos, hurd, hufr⟩ := shape_of_exec_loop_draw hu
  obtain ⟨hgsh, hgpos, hgrd, hgfr⟩ := shape_of_exec_loop_draw hg
  rw [hmu] at hupos hurd hufr
  rw [hmg] at hgpos hgrd hgfr
  have hLv : ∀ i, σg.store.read p Lv i = σ₇.store.read p Lv i := fun i => by
    rw [hgfr _ _ _ (Or.inl hLvSg), hufr _ _ _ (Or.inl hLvSu)]
  refine ⟨σg, h, hgsh.trans (hush.trans (hsh₇.trans hsh₄)), ?_, ?_, fun w hw => ?_,
    fun w hw => ?_, ?_, ?_, fun q b i hb hSu hSg hi => ?_⟩
  · rw [hgpos, hupos, hp₇, hp₄]; simp [hpu]
  · rw [hgpos, hupos, hp₇, hp₄]; simp [hpg]
  · rw [hgfr _ _ _ (Or.inl hSuSg), hurd w hw, hp₇, hp₄, hpu]
  · rw [hgrd w hw, hupos, hp₇, hp₄]; simp [hpg]
  · rw [hLv, hfr₇ _ _ _ hLvT (Or.inr (by omega)), hW₄]
  · rw [hLv, hE₇]
  · have hi' := (not_and_or.mp hi).imp_right not_or.mp
    rw [hgfr _ _ _ (Or.inl hSg), hufr _ _ _ (Or.inl hSu), hfr₇ _ _ _ hb (hi'.imp_right And.right),
      hfr₄ _ _ _ hb (hi'.imp_right And.left)]

/-- The invariant of the slot loop of `NLAlib.eighDownLevel` after the slots below `w`, from the
state `s₀` before the loop: the shape and the tape positions are kept, the slots below `w` that
start a node of depth $d$ are done (`NLAlib.EighSlotDone`), and every cell outside their windows but
the cell $4$ of the scratch buffer `tH` keeps its value. -/
private def DownSlotsInv (I : Interp P ι K C) (mmR : MatMulMap (K × K)) (qrR : QRMap (K × K))
    (p : P) (H : EighArenas) (n F ℓ₀ d tH : ℕ) (R₀ β ε : K) (A : Matrix (Fin n) (Fin n) (K × K))
    (s₀ s : St P K C) (w : ℕ) : Prop :=
  s.store.shape = s₀.store.shape ∧ s.pos = s₀.pos ∧
    (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
        eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
      EighSlotDone H I.sem s.store p (eighTapeMachine I p mmR qrR) n F d R₀ β lo y) ∧
    ∀ q b i, (∀ (lo : ℕ) (y : EighNode K), lo < w → (∃ a : List Bool, a.length = d ∧
        eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) →
        ¬ EighSlotWindow H n d lo y.k (EighChildSlot (eighStep (eighTapeMachine I p mmR qrR) n F R₀
            β
          y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo) b i) →
      ¬ (b = tH ∧ i = 4) → s.store.read q b i = s₀.store.read q b i

/-- A slot of the loop that starts a node of depth $d$ keeps the invariant `DownSlotsInv`: from a
state `s₀` whose arenas hold the nodes of depth $d$, with the parameters `par`, the constants `c`
and the draws of depth $d$ stored, and the scratch buffer `tH` of $5$ cells past all of them. -/
private theorem downSlotsInv_succ_node {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P)
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c tH w : ℕ}
    {s₀ s₁ s₂ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {a : List Bool}
    {y : EighNode K} (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlt : ∀ x ∈ H.handles ++ [par, c], x < tH) (hH : H.Shaped s₀.store p n D)
    (hT5 : s₀.store.shape[tH]? = some (p, 5))
    (hlev : H.LevelHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hpar : s₀.store.read p par 0 = some R₀ ∧ s₀.store.read p par 2 = some β)
    (hc : s₀.store.read p c 0 = I.sem.lit p 1 ∧ s₀.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      s₀.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      s₀.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      s₀.store.read p c 4 = some (I.sem.sqrtHalf p))
    (hSu : ∀ w < n, s₀.store.read p Su w = some (I.tape .uniform (n * d + w)))
    (hSg : ∀ w < 4 * (n * n), s₀.store.read p Sg w =
      some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hw : w < n) (ha : a.length = d)
    (hl : eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (w, y))
    (hinv : DownSlotsInv I mmR qrR p H n F ℓ₀ d tH R₀ β ε A s₀ s₁ w)
    (hex : exec I (eighSlotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
      H.Kp c tH w).run s₁ = some s₂) :
    DownSlotsInv I mmR qrR p H n F ℓ₀ d tH R₀ β ε A s₀ s₂ (w + 1) := by
  obtain ⟨hsh1, hps1, hdn1, hfr1⟩ := hinv
  have hn1 : 1 ≤ n := by omega
  have hnd := hH.1
  have hT : ∀ x ∈ H.handles ++ [par, c], ∀ i, ¬ (x = tH ∧ i = 4) := fun x hx i h => by
    have := hlt x hx; omega
  have hrd1 : ∀ x i, (x = par ∨ x = Su ∨ x = Sg ∨ x = c ∨ x = H.Lv) → ¬ (x = tH ∧ i = 4) →
      s₁.store.read p x i = s₀.store.read p x i := fun x i hx ht =>
    hfr1 p x i (fun _ _ _ _ => not_eighSlotWindow_of_not_mem (not_mem_slotBufs hbufs hx)) ht
  obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn1 hl
  obtain ⟨hyR, hyε, hyℓ⟩ := eighLoc_params hl
  rw [ha] at hyR hyε hyℓ
  have hkk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ (by omega)
  have e5 : 2 * n * w + 2 * (n * y.k) ≤ 2 * (n * n) := by
    have := Nat.mul_le_mul_left (2 * n) hkn
    nlinarith
  have e4 : n * (d + 1) = n * d + n := by ring
  have e6 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
  have hlen : ∀ {x i v}, s₀.store.read p x i = some v → x = tH → i < 5 := fun hr hx => by
    obtain ⟨len, hlen, hi⟩ := Store.exists_getElem?_shape_of_read_eq_some hr
    rw [hx, hT5, Option.some.injEq, Prod.mk.injEq] at hlen
    omega
  have hcT : ∀ i, ¬ (c = tH ∧ i = 4) := hT c (by simp)
  obtain ⟨hdone, hfrW, hsh2, hps2⟩ := holds_of_exec_eighSlotBody hmm hqr p hflag hcmp n ℓ₀ F d D hd
      hlit htn
    H (s := s₁) (s' := s₂) (R₀ := R₀) (β := β) hk1 hkn hyℓ
    (EighArenas.Shaped.of_shape_eq (fun b _ => by rw [hsh1]) hH) hbufs (fun hm => lt_irrefl _ (hlt _
        hm))
    (readsIdx_of_read_eq (hfr1 _ _ _ (fun _ _ _ _ => not_eighSlotWindow_sz hnd (by omega))
      (hT _ (by simp [EighArenas.handles]) _)) (hlev.1 a w y ha hl).1)
    (pairLayout_holds_of_read_eq (hlev.1 a w y ha hl).2 fun i h1 h2 =>
      hfr1 _ _ _ (fun _ _ _ _ => not_eighSlotWindow_ma hnd (by omega))
        (hT _ (by simp [EighArenas.handles]) _))
    ((hrd1 _ _ (by simp) (hT _ (by simp [EighArenas.handles]) _)).trans
      (hlev.2.2.1.trans (congrArg some hyR.symm)))
    ((hrd1 _ _ (by simp) (hT _ (by simp [EighArenas.handles]) _)).trans
      (hlev.2.2.2.trans (congrArg some hyε.symm)))
    ⟨(hrd1 _ _ (by simp) (hT _ (by simp) _)).trans hpar.1,
      (hrd1 _ _ (by simp) (hT _ (by simp) _)).trans hpar.2⟩
    (fun hk2 => by
      have hSu4 : Su = tH → w ≠ 4 := fun hS => by have := hlen (hSu (n - 1) (by omega)) hS; omega
      exact ⟨(hrd1 _ _ (by simp) fun h => hSu4 h.1 h.2).trans (hSu w hw), hSu4⟩)
    (fun hk2 => by
      have hSgT : Sg ≠ tH := fun hS => by
        have h0 : 0 < n * n := Nat.mul_pos hn1 hn1
        have h5 := hlen (hSg (4 * (n * n) - 1) (by omega)) hS
        have h4 : 4 * (n * n) ≤ 5 := by omega
        have : 2 ≤ n := by omega
        nlinarith
      exact ⟨fun w' hw' => (hrd1 _ _ (by simp) fun h => hSgT h.1).trans (hSg w' hw'), hSgT⟩)
    ⟨(hrd1 _ _ (by simp) (hcT 0)).trans hc.1, (hrd1 _ _ (by simp) (hcT 1)).trans hc.2.1,
      (hrd1 _ _ (by simp) (hcT 2)).trans hc.2.2.1, (hrd1 _ _ (by simp) (hcT 3)).trans hc.2.2.2.1,
      (hrd1 _ _ (by simp) (hcT 4)).trans hc.2.2.2.2⟩ hex
  refine ⟨hsh2.trans hsh1, hps2.trans hps1, fun lo y' hlo hn' => ?_, fun q b i hall ht4 => ?_⟩
  · obtain ⟨a', ha', hl'⟩ := hn'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
    · obtain ⟨hk1', hkn'⟩ := eighLoc_bounds hn1 hl'
      have hdis : lo + y'.k ≤ w := by
        have hae : a' ≠ a := by
          rintro rfl
          rw [hl] at hl'
          have := (Prod.mk.inj (Option.some_inj.mp hl')).1
          omega
        rcases eighLoc_disjoint (ha'.trans ha.symm) hae hl' hl with h | h <;> omega
      exact EighSlotDone.of_read_eq hk1' hkn' (fun b i hwin => hfrW p b i
        (fun hw' => false_of_eighSlotWindow_of_eighSlotWindow hnd hk1' hdis hwin hw')
        (fun h => by
          have := lt_of_win (fun x hx => hlt x (List.mem_append_left _ hx)) hwin; omega))
        (hdn1 lo y' hlo ⟨a', ha', hl'⟩)
    · obtain rfl : y = y' := by
        by_cases hae : a = a'
        · subst hae
          rw [hl] at hl'
          exact (Prod.mk.inj (Option.some_inj.mp hl')).2
        · have := (eighLoc_bounds hn1 hl').1
          rcases eighLoc_disjoint (ha.trans ha'.symm) hae hl hl' with h | h <;> omega
      exact hdone
  · rw [hfrW q b i (hall w y (Nat.lt_succ_self w) ⟨a, ha, hl⟩) ht4]
    exact hfr1 q b i (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4

/-- A slot of the loop that starts no node of depth $d$ reads the size $0$, is skipped, and keeps
the invariant `DownSlotsInv`. -/
private theorem downSlotsInv_succ_skip {p : P} {mm qr : ι} {H : EighArenas}
    {n F ℓ₀ d par Su Sg c tH w : ℕ} {s₀ s₁ s₂ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} (hlt : ∀ x ∈ H.handles, x < tH) (hnd : H.handles.Nodup)
    (hlev : H.LevelHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d) (hw : w < n)
    (hno : ¬ ∃ (y : EighNode K) (a : List Bool), a.length = d ∧
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (w, y))
    (hinv : DownSlotsInv I mmR qrR p H n F ℓ₀ d tH R₀ β ε A s₀ s₁ w)
    (hex : exec I (eighSlotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
      H.Kp c tH w).run s₁ = some s₂) :
    DownSlotsInv I mmR qrR p H n F ℓ₀ d tH R₀ β ε A s₀ s₂ (w + 1) := by
  obtain ⟨hsh1, hps1, hdn1, hfr1⟩ := hinv
  have e4 : n * (d + 1) = n * d + n := by ring
  have hSzT : H.Sz < tH := hlt _ (by simp [EighArenas.handles])
  obtain ⟨hst, hps2⟩ := store_eq_of_exec_eighSlotBody (s := s₁) (s' := s₂)
    (readsIdx_of_read_eq (hfr1 _ _ _ (fun _ _ _ _ => not_eighSlotWindow_sz hnd (by omega))
      (fun h => by omega)) (hlev.2.1 w hw fun a y ha hl => hno ⟨y, a, ha, hl⟩)) hex
  refine ⟨by rw [hst]; exact hsh1, hps2.trans hps1, fun lo y' hlo hn' => ?_,
    fun q b i hall ht4 => ?_⟩ <;> rw [hst]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hlo with hlo | rfl
    · exact hdn1 lo y' hlo hn'
    · obtain ⟨a', ha', hl'⟩ := hn'
      exact absurd ⟨y', a', ha', hl'⟩ hno
  · exact hfr1 q b i (fun lo y' hlo hn' => hall lo y' (Nat.lt_succ_of_lt hlo) hn') ht4

/-- The slot loop of `NLAlib.eighDownLevel` ends in the invariant `DownSlotsInv` after all $n$
slots, under the hypotheses of `downSlotsInv_succ_node`. -/
private theorem downSlotsInv_of_exec {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P)
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c tH : ℕ}
    {s₀ s₂ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlt : ∀ x ∈ H.handles ++ [par, c], x < tH) (hH : H.Shaped s₀.store p n D)
    (hT5 : s₀.store.shape[tH]? = some (p, 5))
    (hlev : H.LevelHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hpar : s₀.store.read p par 0 = some R₀ ∧ s₀.store.read p par 2 = some β)
    (hc : s₀.store.read p c 0 = I.sem.lit p 1 ∧ s₀.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      s₀.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      s₀.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      s₀.store.read p c 4 = some (I.sem.sqrtHalf p))
    (hSu : ∀ w < n, s₀.store.read p Su w = some (I.tape .uniform (n * d + w)))
    (hSg : ∀ w < 4 * (n * n), s₀.store.read p Sg w =
      some (I.tape .gaussian (4 * (n * n) * d + w)))
    (he : exec I (.loop (.const n) fun lo => (eighSlotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma
      H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c tH lo).run) s₀ = some s₂) :
    DownSlotsInv I mmR qrR p H n F ℓ₀ d tH R₀ β ε A s₀ s₂ n := by
  refine forall_of_exec_loop_eq_some I (fun w s => DownSlotsInv I mmR qrR p H n F ℓ₀ d tH R₀ β ε A
    s₀ s w) ⟨rfl, rfl, fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ => rfl⟩ ?_ he
  intro w hw s₁ s₂ hinv hex
  change w < n at hw
  by_cases hnode : ∃ (y : EighNode K) (a : List Bool), a.length = d ∧
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (w, y)
  · obtain ⟨y, a, ha, hl⟩ := hnode
    exact downSlotsInv_succ_node hmm hqr p hflag hcmp n ℓ₀ F d D hd hlit htn H hbufs hlt hH hT5
      hlev hpar hc hSu hSg hw ha hl hinv hex
  · exact downSlotsInv_succ_skip (fun x hx => hlt x (List.mem_append_left _ hx)) hH.1 hlev hw
      hnode hinv hex

omit [AddMonoid C] in
/-- After the slot loop, with the scratch buffer popped, the arenas hold the nodes of depth
$d + 1$: from the invariant `DownSlotsInv` at $n$, the size cells of depth $d + 1$ reading $0$
before the level, and the parameters of depth $d + 1$ stored before the loop. -/
private theorem levelHolds_succ_of_downSlots {p : P} {H : EighArenas} {n F ℓ₀ d tH : ℕ}
    {S : Store P K} {s₀ σ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hlt : ∀ x ∈ H.handles, x < tH) (hnd : H.handles.Nodup) (hsz : σ.store.size = tH + 1)
    (hinv : DownSlotsInv I mmR qrR p H n F ℓ₀ d tH R₀ β ε A s₀ σ n)
    (hnext : ∀ lo < n, ReadsIdx I.sem S p H.Sz (n * (d + 1) + lo) 0)
    (hSz : ∀ j, s₀.store.read p H.Sz j = S.read p H.Sz j)
    (hW1 : s₀.store.read p H.Lv (2 * (d + 1)) =
      some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ (d + 1)).1)
    (hW2 : s₀.store.read p H.Lv (2 * (d + 1) + 1) =
      some (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ (d + 1)).2) :
    H.LevelHolds I.sem (Array.pop σ.store) p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1) := by
  obtain ⟨-, -, hdne, hfre⟩ := hinv
  have hpop : ∀ q b i, b < tH → Store.read (Array.pop σ.store) q b i = σ.store.read q b i :=
    fun q b i hb => Store.read_pop_of_lt (by omega)
  have hSzT : H.Sz < tH := hlt _ (by simp [EighArenas.handles])
  have hLvT : H.Lv < tH := hlt _ (by simp [EighArenas.handles])
  have hLvb : H.Lv ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h <;> simp [EighArenas.handles, h] at hnd
  refine ⟨fun a' lo' y' ha' hl' => ?_, fun lo' hlo' hno => ?_, ?_, ?_⟩
  · -- the children
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
    have hkn := (add_k_le_and_of_eighLoc hl).1
    exact (EighSlotDone.of_read_eq hk1 hkn (fun b i hwin => hpop p b i (lt_of_win hlt hwin))
      (hdne lo y (by omega) ⟨a, ha, hl⟩)).2 b lo' y' hl2
  · -- the slots that start no node
    refine readsIdx_of_read_eq ?_ (hnext lo' hlo')
    rw [hpop p H.Sz _ hSzT, hfre p H.Sz _ ?_ (fun h => by omega), hSz]
    intro lo y _ ⟨a, ha, hl⟩ hwin
    obtain ⟨j, hj, hij⟩ := exists_eq_of_eighSlotWindow_sz hnd hwin
    obtain rfl : j = lo' := by omega
    obtain ⟨b, y', hl2⟩ := exists_eighLoc_of_eighChildSlot hj
    refine hno (a ++ [b]) y' (by simp [ha]) ?_
    rw [eighLoc_append_singleton, hl, Option.bind_some]
    simpa [ha] using hl2
  · rw [hpop p H.Lv _ hLvT, hfre p H.Lv _ (fun _ _ _ _ => not_eighSlotWindow_of_not_mem hLvb)
      (fun h => by omega), hW1]
  · rw [hpop p H.Lv _ hLvT, hfre p H.Lv _ (fun _ _ _ _ => not_eighSlotWindow_of_not_mem hLvb)
      (fun h => by omega), hW2]

omit [AddMonoid C] in
/-- After the slot loop, with the scratch buffer popped, the records of depth $d$ hold and every
cell outside the records of depth $d$, the cells of depth $d + 1$ and the sample buffers `Su`,
`Sg` reads as in the store `S` before the level: from the invariant `DownSlotsInv` at $n$ and the
frame `hrg` of the instructions and draws before the loop. -/
private theorem recordHolds_frame_of_downSlots {p : P} {H : EighArenas} {n F ℓ₀ d tH Su Sg : ℕ}
    {S : Store P K} {s₀ σ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hlt : ∀ x ∈ H.handles, x < tH) (hsz : σ.store.size = tH + 1) (hS : S.size = tH)
    (hinv : DownSlotsInv I mmR qrR p H n F ℓ₀ d tH R₀ β ε A s₀ σ n)
    (hrg : ∀ q b i, b < tH → b ≠ Su → b ≠ Sg →
      ¬ (b = H.Lv ∧ (i = 2 * (d + 1) ∨ i = 2 * (d + 1) + 1)) →
      s₀.store.read q b i = S.read q b i) :
    H.RecordHolds I.sem (Array.pop σ.store) p (eighTapeMachine I p mmR qrR) n F R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      ∀ q b i, b ≠ Su → b ≠ Sg →
        ¬ ((b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) ∧ H.LevelCell n d b i) →
        ¬ H.LevelCell n (d + 1) b i → Store.read (Array.pop σ.store) q b i = S.read q b i := by
  obtain ⟨-, -, hdne, hfre⟩ := hinv
  have hpop : ∀ q b i, b < tH → Store.read (Array.pop σ.store) q b i = σ.store.read q b i :=
    fun q b i hb => Store.read_pop_of_lt (by omega)
  refine ⟨fun a lo y ha hl hk1 => ?_, fun q b i hbSu hbSg h1 h2 => ?_⟩
  · have hkn := (add_k_le_and_of_eighLoc hl).1
    exact (EighSlotDone.of_read_eq hk1 hkn (fun b i hwin => hpop p b i (lt_of_win hlt hwin))
      (hdne lo y (by omega) ⟨a, ha, hl⟩)).1
  · by_cases hb : b < tH
    · rw [hpop q b i hb, hfre q b i ?_ (fun h => by omega)]
      · exact hrg q b i hb hbSu hbSg fun h => h2 (Or.inr (Or.inr h))
      · intro lo y hlo ⟨a, ha, hl⟩ hwin
        have hn1 : 1 ≤ n := by omega
        rcases levelCell_of_win (eighLoc_bounds hn1 hl).1 (eighLoc_bounds hn1 hl).2 hwin with
          h | h
        · exact h1 h
        · exact h2 h
    · rw [Store.read_eq_none_of_size_le (s := Array.pop σ.store) (q := q) (b := b) (i := i)
        (by simp [Array.size_pop, hsz]; omega),
        Store.read_eq_none_of_size_le (s := S) (q := q) (b := b) (i := i) (by omega)]

/-- One level of the downward pass, with the finer frame: let the kernels of `I` be the routines
`mmR`, `qrR` on interleaved pairs, the semantics decide flags, with exact integer literals up to
$n + 4$ and the exact floor conversion; $M$ = `NLAlib.eighTapeMachine I p mmR qrR` and the root
$(n, \mathbf{A}, R_0, \varepsilon, \ell_0)$. A successful run of `NLAlib.eighDownLevel` at depth
$d < D$ from a state whose arenas hold the nodes of depth $d$ and whose size cells of depth $d + 1$
all read $0$, with the tape positions $nd$ and $4n^2 d$, the stored $R_0$, $\beta$ in `par` and
the constants in `c`, ends with the arenas holding the nodes of depth $d + 1$ and the records of
depth $d$; of the cells of depth $d$ only the records (bases, outputs, eigenvalues, kinds,
splits) may change, every cell outside depths $d$ and $d + 1$ and the sample buffers `Su`, `Sg`
is unchanged, the store shape too, and the tape positions advance by $n$ and $4n^2$. No printed
source. -/
theorem levelHolds_succ_of_exec_eighDownLevel {mm qr : ι}
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
  obtain ⟨⟨dLvSu, dLvSg⟩, ⟨dSzSu, dSzSg, dSzLv⟩, ⟨dMaSu, dMaSg, dMaLv⟩, ⟨dparSu, dparSg, dparLv⟩,
    ⟨dcSu, dcSg, dcLv⟩, dSuSg⟩ := downLevel_bufs_ne hbufs
  obtain ⟨z0, o1, -, hl1, -, -⟩ := id hflag
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSzs, hKd, hKp, hLv⟩ := id hH
  have lc := Store.lt_size_of_read_eq_some (hc.1.trans hl1)
  have hlt : ∀ x ∈ H.handles ++ [par, c], x < st.store.size := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSzs, hsz hKd, hsz hKp, hsz hLv,
      Store.lt_size_of_read_eq_some hpar.1, lc⟩
  have hlt' : ∀ x ∈ H.handles, x < st.store.size := fun x hx => hlt x (List.mem_append_left _ hx)
  have lLv : H.Lv < st.store.size := hlt' _ (by simp [EighArenas.handles])
  have hr0 : ∀ q b i, b < st.store.size →
      Store.read (st.store.push (p, Array.replicate (5 : IExp ℕ).eval none)) q b i =
        st.store.read q b i := fun q b i hb => Store.read_push_of_lt hb
  change exec I (.seq (.alloc p _ _) .skip) st = some st' at h
  obtain ⟨s₂, h₀, rfl⟩ := exists_exec_of_exec_seq_alloc h
  obtain ⟨σg, h, hshg, hug, hgg, hSuR, hSgR, hW1, hW2, hfrg⟩ := exec_downLevel_prefix
    (n := n) (ℓ₀ := ℓ₀) (d := d) h₀ rfl rfl rfl rfl rfl rfl rfl
    (Nat.ne_of_lt lc) (Nat.ne_of_lt lLv) dLvSu dLvSg dSuSg ((hr0 _ _ _ lc).trans hc.1)
    ((hr0 _ _ _ lc).trans hc.2.1) ((hr0 _ _ _ lc).trans hc.2.2.1)
    ((hr0 _ _ _ lLv).trans hlev.2.2.1) ((hr0 _ _ _ lLv).trans hlev.2.2.2) hpos.1 hpos.2
  obtain ⟨σe, he, h⟩ := exists_exec_and_exec_of_exec_seq h
  rw [exec_skip, Option.some_inj] at h
  subst h
  have hrg : ∀ q b i, b < st.store.size → b ≠ Su → b ≠ Sg →
      ¬ (b = H.Lv ∧ (i = 2 * (d + 1) ∨ i = 2 * (d + 1) + 1)) →
      σg.store.read q b i = st.store.read q b i := fun q b i hb h1 h2 h3 =>
    (hfrg q b i (by omega) h1 h2 h3).trans (hr0 q b i hb)
  have hSz : ∀ j, σg.store.read p H.Sz j = st.store.read p H.Sz j := fun j =>
    hrg _ _ _ (hlt' _ (by simp [EighArenas.handles])) dSzSu dSzSg fun h => dSzLv h.1
  have hcg : ∀ i, σg.store.read p c i = st.store.read p c i := fun i =>
    hrg _ _ _ lc dcSu dcSg fun h => dcLv h.1
  have hparg : ∀ i, σg.store.read p par i = st.store.read p par i := fun i =>
    hrg _ _ _ (Store.lt_size_of_read_eq_some hpar.1) dparSu dparSg fun h => dparLv h.1
  have hlev' : H.LevelHolds I.sem σg.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d :=
    ⟨fun a lo y ha hl => ⟨readsIdx_of_read_eq (hSz _) (hlev.1 a lo y ha hl).1,
        pairLayout_holds_of_read_eq (hlev.1 a lo y ha hl).2 fun i _ _ =>
          hrg _ _ _ (hlt' _ (by simp [EighArenas.handles])) dMaSu dMaSg fun h => dMaLv h.1⟩,
      fun lo hlo hno => readsIdx_of_read_eq (hSz _) (hlev.2.1 lo hlo hno),
      (hrg _ _ _ lLv dLvSu dLvSg (by omega)).trans hlev.2.2.1,
      (hrg _ _ _ lLv dLvSu dLvSg (by omega)).trans hlev.2.2.2⟩
  have hinv := downSlotsInv_of_exec hmm hqr p hflag hcmp n ℓ₀ F d D hd hlit htn H (A := A)
    (ε := ε) hbufs hlt (EighArenas.Shaped.of_shape_eq (fun b hb => by
      rw [hshg]; exact Store.getElem?_shape_push_of_lt _ (hlt' b hb)) hH)
    (by rw [hshg]; exact Store.getElem?_shape_push_size _ _ _) hlev'
    ⟨(hparg 0).trans hpar.1, (hparg 2).trans hpar.2⟩
    ⟨(hcg 0).trans hc.1, (hcg 1).trans hc.2.1, (hcg 2).trans hc.2.2.1, (hcg 3).trans hc.2.2.2.1,
      (hcg 4).trans hc.2.2.2.2⟩ hSuR hSgR he
  have hsze : σe.store.size = st.store.size + 1 := by
    rw [Store.size_eq_of_shape_eq (hinv.1.trans hshg)]; simp
  obtain ⟨hrec, hfr⟩ := recordHolds_frame_of_downSlots hlt' hsze rfl hinv hrg
  refine ⟨levelHolds_succ_of_downSlots hlt' hnd hsze hinv hnext hSz hW1 hW2, hrec, hfr, ?_, ?_, ?_⟩
  · change Store.shape (Array.pop σe.store) = _
    rw [Store.shape_pop, hinv.1, hshg]
    simp [Store.shape]
  · change σe.pos .uniform = _
    rw [hinv.2.1, hug, hpos.1]
  · change σe.pos .gaussian = _
    rw [hinv.2.1, hgg, hpos.2]

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
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := levelHolds_succ_of_exec_eighDownLevel hmm hqr p hflag hcmp n ℓ₀
      F d
    D hd hlit htn H hH hbufs hlev hnext hpos hpar hc h
  exact ⟨h1, h2, fun q b i hSu hSg hd1 hd2 => h3 q b i hSu hSg (fun h => hd1 h.2) hd2, h4, h5, h6⟩

end NLAlib
