/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionClamp
public import NLAlib.Matrix.Computation.SpectralBisectionNode.Setup

/-!
# The node step of the spectral bisection program

The blocks of the node step of `NLAlib.eighProg` compute the matching operations of
`NLAlib.eighStep` on the machine of the semantics (`NLAlib.Computation.ScalarSem.toFloatMachine`,
`NLAlib.eighTapeMachine`). Each value statement is a partial equality: under kernels that are
routines on pairs and a semantics that decides flags, a successful run writes exactly the machine's
value, with no contract on the rounding. The blocks are in the files
`NLAlib/Matrix/Computation/SpectralBisectionNode/*.lean`; this file assembles the branch after the
index binder (one child or a split) and the whole node step.

## Main results

* `NLAlib.holds_of_exec_eighNodeBlock`: the node step computes `NLAlib.eighStep`.
* `NLAlib.holds_of_exec_eighNodeBlock_frame`: the same, with the window it writes.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

-- The branch of a node step unfolds its three loops.
set_option maxHeartbeats 4000000 in
/-- The branch of a node step after the index binder, from a cell that converts to $k_+ \le k$: one
child or a split, with the frame of the node's window. -/
private theorem node_branch_holds_core {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n d lo k : ℕ) (hk : lo + k ≤ n)
    (hk2 : 2 ≤ k) (H : EighArenas) {Sg c t Pp Pm : ℕ} {st st' : St P K C}
    {A Ppv Pmv : Matrix (Fin k) (Fin k) (K × K)} {half w6 : K} {D : ℕ} (hd : d < D)
    (hH : H.Shaped st.store p n D) (s₀ : ℕ) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hlt : ∀ b ∈ H.handles ++ [Sg, c], b < s₀) (hcS : c ∉ H.handles ++ [Sg])
    (hge : s₀ ≤ t ∧ s₀ ≤ Pp ∧ s₀ ≤ Pm) (htPp : t = Pp → False) (htPm : t = Pm → False)
    (htsz : t < st.store.size) (hs₀ : s₀ ≤ st.store.size)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppv) (hPm : pairLayout.Holds st.store p Pm 0 Pmv)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p c 1 = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hsq : st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (ht0 : st.store.read p t 0 = some half)
    (ht1 : st.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg half))
    (ht6 : st.store.read p t 6 = some w6) {kp₀ : ℕ} (hkp₀ : I.sem.toNat p w6 = some kp₀)
    (h : exec I (Builder.bindIdx p ⟨t, 6⟩ (.const k) fun kp => do
        eighWhen (1 - (.const k - .var kp))
          (eighChildBlock p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
            (eighBlockOff (.const n) (.const d + 1) (.const lo)) ⟨t, 0⟩
            ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
            ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 2)
        eighWhen (1 - .var kp)
          (eighChildBlock p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
            (eighBlockOff (.const n) (.const d + 1) (.const lo)) ⟨t, 1⟩
            ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
            ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 3)
        eighWhen (.var kp * (.const k - .var kp))
          (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.var kp) Sg Pp Pm
            H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 1⟩ ⟨t, 0⟩ ⟨t, 1⟩ ⟨c, 4⟩) :
        Builder P ι ℕ ℕ Unit).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let kp := kp₀
    (kp = k → pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift A half) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((2 : ℕ) : ℚ)) ∧
    (kp = 0 → pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift A (M.neg half)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((3 : ℕ) : ℚ)) ∧
    (0 < kp → kp < k →
      let s := eighTapeSample n d lo
      let Qp := deflate M kp Ppv (leadingBlock k (s.2 true))
      let Qm := deflate M (k - kp) Pmv (leadingBlock k (s.2 false))
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) half) ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
          (M.neg half)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
    (∀ q b i, b < s₀ → ¬ nodeWin H n d lo k (if 0 < kp ∧ kp < k then lo + kp else lo) b i →
      st'.store.read q b i = st.store.read q b i) ∧
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M kp
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
  obtain ⟨lMa, lUa, lQa, lEa, lSz, lKd, lKp, lLv, lSg, lc⟩ := hlt
  obtain ⟨gt, gPp, gPm⟩ := hge
  have dMaSz : H.Ma = H.Sz → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaKd : H.Ma = H.Kd → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzKd : H.Sz = H.Kd → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have hn : k ≤ n := by omega
  have hkkn : k * k ≤ n * k := Nat.mul_le_mul_right _ hn
  have hnk : n * k ≤ n * n := Nat.mul_le_mul_left _ hn
  have hbo : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval =
      2 * (n * n) * d + 2 * n * lo := by simp [eighBlockOff]
  have hbo1 : (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.const lo)).eval =
      2 * (n * n) * (d + 1) + 2 * n * lo := by simp [eighBlockOff]
  have hso1 : (eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.const lo)).eval =
      n * (d + 1) + lo := by simp [eighSlotOff]
  have hso : (eighSlotOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval = n * d + lo := by
    simp [eighSlotOff]
  -- the binder
  obtain ⟨v, w, hw, hv, hvk, h⟩ := bindIdx_inv_node h
  replace hvk : v ≤ k := hvk
  have ew : w = w6 := by
    change st.store.read p t 6 = some w at hw
    rw [ht6] at hw; exact (Option.some_inj.mp hw).symm
  subst w
  have hkp : kp = v := by
    change kp₀ = v
    rw [hkp₀] at hv; exact Option.some_inj.mp hv
  refine name_state_node h ?_; clear h; intro σ e1 e2 h; simp only at e1 e2
  beta_reduce at h
  obtain ⟨σa, ha, hra⟩ := when_bind_node h
  obtain ⟨σb, hb, hrb⟩ := when_bind_node hra
  have h' := when_run_node hrb
  clear h hra hrb
  -- the frame of a child block
  have hchild : ∀ (sg : Cell ℕ ℕ) (code : ℕ) {σ₁ σ₂ : St P K C}
      {sv : K}, σ₁.store = st.store → sg.buf = t →
      σ₁.store.read p sg.buf sg.idx.eval = some sv →
      exec I (eighChildBlock (ι := ι) p (.const k) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo)) sg
        ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
        ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ code).run σ₁ = some σ₂ →
      pairLayout.Holds σ₂.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) (M.hermShift A sv) ∧
        σ₂.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
        σ₂.store.read p H.Kd (n * d + lo) = I.sem.lit p ((code : ℕ) : ℚ) ∧
        (∀ j q b i, b < s₀ → ¬ nodeWin H n d lo k j b i →
          σ₂.store.read q b i = st.store.read q b i) ∧
        σ₂.store.shape = st.store.shape ∧ σ₂.pos = σ₁.pos := by
    intro sg code σ₁ σ₂ sv hs hsg hsv hex
    obtain ⟨hM, hsz, hkd, hfr, hsh, hps⟩ := holds_of_exec_eighChildBlock
      (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
      (unif := I.sem.tapeUnif p (I.tape .uniform))
      (normal := I.sem.tapeNormal p (I.tape .gaussian)) p k code (st := σ₁) (st' := σ₂)
      (by rw [hbo, hs]; exact hA) hsv
      (by
        rw [hbo, hbo1]
        simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
          decide_eq_true_eq]
        right; linarith)
      (by simp only [blockDisjoint, hsg, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
          exact Or.inl (Or.inl (by omega)))
      (by simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
          exact Or.inl (Or.inl (fun h => dMaSz h.symm)))
      (by simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
          exact Or.inl (Or.inl (fun h => dMaKd h.symm)))
      (by simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
          exact Or.inl (Or.inl dSzKd)) hex
    rw [hbo1] at hM
    rw [hso1] at hsz
    rw [hso] at hkd
    refine ⟨hM, hsz, hkd, fun j q b i hb hW => ?_, hsh.trans (by rw [hs]), hps⟩
    simp only [nodeWin, not_or, not_and, not_lt] at hW
    obtain ⟨-, hWM, hWS, hWK⟩ := hW
    rw [hfr q b i ?_ ?_ ?_, hs]
    · rw [hbo1]
      refine bd_of_win_node (lo' := 2 * (n * n) * (d + 1) + 2 * n * lo)
        (hi' := 2 * (n * n) * (d + 1) + 2 * n * (lo + k)) (fun h1 => ?_) le_rfl (by linarith)
      by_contra hc; push_neg at hc
      exact absurd (hWM h1 hc.1) (by omega)
    · rw [hso1]
      refine bd_of_win_node (lo' := n * (d + 1) + lo) (hi' := n * (d + 1) + lo + 1)
        (fun h1 => ?_) le_rfl le_rfl
      have := hWS h1
      by_contra hc; push_neg at hc
      omega
    · rw [hso]
      refine bd_of_win_node (lo' := n * d + lo) (hi' := n * d + lo + 1) (fun h1 => ?_) le_rfl le_rfl
      have := hWK (Or.inl h1)
      omega
  have E1 : ∀ x : ℕ, (1 - (1 - (1 - (IExp.const k - IExp.var x)))).eval =
      1 - (1 - (1 - (k - x))) := fun x => rfl
  have E2 : ∀ x : ℕ, (1 - (1 - (1 - IExp.var x))).eval = 1 - (1 - (1 - x)) := fun x => rfl
  have E3 : ∀ x : ℕ, (1 - (1 - IExp.var x * (IExp.const k - IExp.var x))).eval =
      1 - (1 - x * (k - x)) := fun x => rfl
  have hkv : v ≤ k := hvk
  rcases Nat.eq_or_lt_of_le hkv with hkk | hlt'
  · -- one child on the positive side
    have h1 := loop_one_node (by rw [E1]; omega) ha
    have e2' := loop_zero_node (by rw [E2]; omega) hb
    have e3' := loop_zero_node (by rw [E3, hkk, Nat.sub_self, Nat.mul_zero]) h'
    subst e2' e3'
    obtain ⟨hM, hsz, hkd, hfr, hsh, hps⟩ := hchild ⟨t, 0⟩ 2 e1 rfl (by rw [e1]; exact ht0) h1
    refine ⟨fun _ => ⟨hM, hsz, hkd⟩, fun h0 => by omega, fun _ h' => by omega,
      fun q b i hb hW => hfr _ q b i hb hW, hsh, hps.trans e2⟩
  rcases Nat.eq_zero_or_pos (v) with hz | hpos
  · -- one child on the negative side
    have e1' := loop_zero_node (by rw [E1]; omega) ha
    have h2 := loop_one_node (by rw [E2]; omega) hb
    have e3' := loop_zero_node (by rw [E3, hz, Nat.zero_mul]) h'
    subst e1' e3'
    obtain ⟨hM, hsz, hkd, hfr, hsh, hps⟩ := hchild ⟨t, 1⟩ 3 e1 rfl (by rw [e1]; exact ht1) h2
    refine ⟨fun h' => by omega, fun _ => ⟨hM, hsz, hkd⟩, fun h' _ => by omega,
      fun q b i hb hW => hfr _ q b i hb hW, hsh, hps.trans e2⟩
  · -- a split
    have e1' := loop_zero_node (by rw [E1]; omega) ha
    have e2' := loop_zero_node (by rw [E2]; omega) hb
    subst σa; subst σb
    have hprod : 0 < v * (k - v) := Nat.mul_pos hpos (by omega)
    have he3 : (1 - (1 - IExp.var (v) * (IExp.const k - IExp.var (v)))).eval = 1 := by
      rw [E3]; generalize v * (k - v) = m at hprod ⊢; omega
    have h3 := loop_one_node he3 h'
    have hH' : H.Shaped σ.store p n D := by rw [e1]; exact hH
    obtain ⟨⟨q1, q2, q3, q4, q5, q6, q7, q8⟩, hfr, hsh, hps⟩ :=
      holds_of_exec_eighSplitBlock_frame hmm hqr p n d lo k (v) hk hpos hlt'
        (.var (v)) rfl H
        (two := ⟨c, 1⟩) (sg := ⟨t, 0⟩) (nsg := ⟨t, 1⟩) (sq := ⟨c, 4⟩) (σ := half)
        (st := σ) (st' := st') (A := A) (Ppm := Ppv) (Pmm := Pmv) hd hH' hbufs
        (by rw [e1]; exact hA) (by rw [e1]; exact hPp) (by rw [e1]; exact hPm)
        (by rw [e1]; exact hSg) (by rw [e1]; exact htwo)
        (by rw [e1]; exact ht0) (by rw [e1]; exact ht1)
        (by
          intro c' hc'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
          have hcn : c ∉ H.handles ++ [Sg, Pp, Pm] := by
            intro hm
            rw [show H.handles ++ [Sg, Pp, Pm] = (H.handles ++ [Sg]) ++ [Pp, Pm] by simp] at hm
            rcases List.mem_append.mp hm with h | h
            · exact hcS h
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega
          have htn : t ∉ H.handles ++ [Sg, Pp, Pm] := by
            intro hm
            simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
              List.not_mem_nil, or_false] at hm
            rcases hm with h | h | h | h | h | h | h | h | h | h | h <;>
              first | omega | exact htPp h | exact htPm h
          rcases hc' with rfl | rfl | rfl | rfl
          exacts [hcn, htn, htn, hcn])
        (by rw [e1]; exact hsq)
        h3
    refine ⟨fun h' => by omega, fun h' => by omega, fun _ _ => ?_, fun q b i hb hW => ?_,
      hsh.trans (by rw [e1]), hps.trans e2⟩
    · rw [hkp]
      exact ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩
    · rw [if_pos (by rw [hkp]; exact ⟨hpos, hlt'⟩), hkp] at hW
      rw [hfr q b i hW, e1]

-- The clamp, then the branch.
set_option maxHeartbeats 4000000 in
/-- The clamp of the split index and the branch of a node step: one child or a split, with the
frame of the node's window, at $k_+ = \min(k, \lfloor w_6\rfloor_+)$ under exact comparisons,
literals up to $k$ and conversion. -/
private theorem node_branch_holds {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) {dec : P → K → ℝ}
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n d lo k : ℕ) (hlit : IsExactIntLit dec I.sem k) (htn : IsExactToNat dec I.sem)
    (hk : lo + k ≤ n)
    (hk2 : 2 ≤ k) (H : EighArenas) {Sg c t Pp Pm : ℕ} {st st' : St P K C}
    {A Ppv Pmv : Matrix (Fin k) (Fin k) (K × K)} {half w6 : K} {D : ℕ} (hd : d < D)
    (hH : H.Shaped st.store p n D) (s₀ : ℕ) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hlt : ∀ b ∈ H.handles ++ [Sg, c], b < s₀) (hcS : c ∉ H.handles ++ [Sg])
    (hge : s₀ ≤ t ∧ s₀ ≤ Pp ∧ s₀ ≤ Pm) (htPp : t = Pp → False) (htPm : t = Pm → False)
    (htsz : t < st.store.size) (hs₀ : s₀ ≤ st.store.size)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppv) (hPm : pairLayout.Holds st.store p Pm 0 Pmv)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p c 1 = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hsq : st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (ht0 : st.store.read p t 0 = some half)
    (ht1 : st.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg half))
    (ht6 : st.store.read p t 6 = some w6)
    (h : exec I (do
        eighClampBlock p (.const k) ⟨t, 6⟩ ⟨t, 2⟩ ⟨t, 3⟩
        Builder.bindIdx p ⟨t, 6⟩ (.const k) fun kp => do
          eighWhen (1 - (.const k - .var kp))
            (eighChildBlock p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
              (eighBlockOff (.const n) (.const d + 1) (.const lo)) ⟨t, 0⟩
              ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
              ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 2)
          eighWhen (1 - .var kp)
            (eighChildBlock p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
              (eighBlockOff (.const n) (.const d + 1) (.const lo)) ⟨t, 1⟩
              ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
              ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 3)
          eighWhen (.var kp * (.const k - .var kp))
            (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.var kp) Sg Pp
              Pm H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 1⟩ ⟨t, 0⟩ ⟨t, 1⟩ ⟨c, 4⟩) :
        Builder P ι ℕ ℕ Unit).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let kp := min k (M.toNat w6)
    (kp = k → pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift A half) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((2 : ℕ) : ℚ)) ∧
    (kp = 0 → pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift A (M.neg half)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((3 : ℕ) : ℚ)) ∧
    (0 < kp → kp < k →
      let s := eighTapeSample n d lo
      let Qp := deflate M kp Ppv (leadingBlock k (s.2 true))
      let Qm := deflate M (k - kp) Pmv (leadingBlock k (s.2 false))
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) half) ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
          (M.neg half)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
    (∀ q b i, b < s₀ → ¬ nodeWin H n d lo k (if 0 < kp ∧ kp < k then lo + kp else lo) b i →
      st'.store.read q b i = st.store.read q b i) ∧
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M kp
  obtain ⟨σ, hrun, ⟨wc, hwc, hwcn⟩, hfr, hsh, hps, -⟩ :=
    exec_eighClampBlock_bind (I := I) hcmp hlit htn ht6
  rw [hrun] at h
  have rd : ∀ q b i, b ≠ t → σ.store.read q b i = st.store.read q b i :=
    fun q b i hb => hfr q b i fun h => absurd h hb
  have rt : ∀ q i, i < 2 → σ.store.read q t i = st.store.read q t i :=
    fun q i hi => hfr q t i fun _ => ⟨by omega, by omega, by omega⟩
  have lMa : H.Ma < s₀ := hlt _ (by simp [EighArenas.handles])
  have lSg : Sg < s₀ := hlt _ (by simp)
  have lc : c < s₀ := hlt _ (by simp)
  have hH' : H.Shaped σ.store p n D := by unfold EighArenas.Shaped; rw [hsh]; exact hH
  have hM : M.toNat w6 = ⌊dec p w6⌋₊ := by
    change (I.sem.toNat p w6).getD 0 = _
    rw [htn p w6]
    split_ifs with h0
    · rfl
    · exact (Nat.floor_eq_zero.mpr (by linarith [not_le.mp h0])).symm
  have hkp : kp = min k ⌊dec p w6⌋₊ := by change min k (M.toNat w6) = _; rw [hM]
  clear_value kp
  subst hkp
  have C := node_branch_holds_core hmm hqr p n d lo k hk hk2 H (Sg := Sg) (c := c) (st := σ)
    (st' := st') (A := A) (Ppv := Ppv) (Pmv := Pmv) (half := half) hd hH' s₀ hbufs
    hlt hcS hge htPp htPm (by rw [← Store.size_eq_of_shape_eq hsh.symm]; exact htsz)
    (by rw [← Store.size_eq_of_shape_eq hsh.symm]; exact hs₀)
    (fun i j t' => (rd _ _ _ (by omega)).trans (hA i j t'))
    (fun i j t' => (rd _ _ _ (fun h => htPp h.symm)).trans (hPp i j t'))
    (fun i j t' => (rd _ _ _ (fun h => htPm h.symm)).trans (hPm i j t'))
    (fun w hw => (rd _ _ _ (by omega)).trans (hSg w hw))
    ((rd _ _ _ (by omega)).trans htwo) ((rd _ _ _ (by omega)).trans hsq)
    ((rt _ 0 (by omega)).trans ht0) ((rt _ 1 (by omega)).trans ht1) hwc hwcn h
  obtain ⟨c1, c2, c3, cfr, csh, cps⟩ := C
  exact ⟨c1, c2, c3, fun q b i hb hW => (cfr q b i hb hW).trans (rd q b i (by omega)),
    csh.trans hsh, cps.trans hps⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The arenas stay allocated under a push. -/
private theorem shaped_push_node {H : EighArenas} {s : Store P K} {p : P} {n D : ℕ}
    (x : P × Array (Option K)) (hH : H.Shaped s p n D) (hlt : ∀ b ∈ H.handles, b < s.size) :
    H.Shaped (s.push x) p n D := by
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := hH
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hlt
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := hlt
  exact ⟨hnd, by rw [Store.getElem?_shape_push_of_lt _ l1]; exact hMa,
    by rw [Store.getElem?_shape_push_of_lt _ l2]; exact hUa,
    by rw [Store.getElem?_shape_push_of_lt _ l3]; exact hQa,
    by rw [Store.getElem?_shape_push_of_lt _ l4]; exact hEa,
    by rw [Store.getElem?_shape_push_of_lt _ l5]; exact hSz,
    by rw [Store.getElem?_shape_push_of_lt _ l6]; exact hKd,
    by rw [Store.getElem?_shape_push_of_lt _ l7]; exact hKp,
    by rw [Store.getElem?_shape_push_of_lt _ l8]; exact hLv⟩

/-- The handles of a split inside a node step are distinct, and the constants are not among the
arenas and the samples. -/
theorem nodup_scratch_node {H : EighArenas} {par Su Sg c Pp Pm s₀ : ℕ}
    (hb : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlt : ∀ b ∈ H.handles ++ [par, Su, Sg, c], b < s₀) (h1 : s₀ ≤ Pp) (h2 : s₀ ≤ Pm)
    (h3 : Pp ≠ Pm) : (H.handles ++ [Sg, Pp, Pm]).Nodup ∧ c ∉ H.handles ++ [Sg] := by
  have hsub : (H.handles ++ [Sg]).Sublist (H.handles ++ [par, Su, Sg, c]) :=
    List.Sublist.append_left (List.singleton_sublist.mpr (by simp)) _
  have hS := hsub.nodup hb
  refine ⟨?_, ?_⟩
  · rw [show H.handles ++ [Sg, Pp, Pm] = (H.handles ++ [Sg]) ++ [Pp, Pm] by simp]
    refine List.nodup_append.mpr ⟨hS, by simp [h3], fun a ha b hb' => ?_⟩
    have := hlt a (hsub.subset ha)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    omega
  · intro hc
    rw [show H.handles ++ [par, Su, Sg, c] = (H.handles ++ [par, Su, Sg]) ++ [c] by simp] at hb
    have hsub' : (H.handles ++ [Sg]).Sublist (H.handles ++ [par, Su, Sg]) :=
      List.Sublist.append_left (List.singleton_sublist.mpr (by simp)) _
    exact (List.nodup_append.mp hb).2.2 c (hsub'.subset hc) c (by simp) rfl

-- The seven allocations and the branch of a node step.
set_option maxHeartbeats 4000000 in
/-- The node step computes `NLAlib.eighStep`, with the window it writes: under the hypotheses
of `NLAlib.holds_of_exec_eighNodeBlock`, its conclusion with the precise frame: every cell outside
the node's basis block at depth $d$, its matrix block and size cells at depth $d + 1$, and its kind
and split cells at depth $d$ (the window of the slots $[lo, lo + k)$) is unchanged. No printed
source. -/
theorem holds_of_exec_eighNodeBlock_frame {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (hflag : I.sem.DecidesFlags p)
    {dec : P → K → ℝ} (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d lo k : ℕ) (hlit : IsExactIntLit dec I.sem (n + 2)) (htn : IsExactToNat dec I.sem)
    (hk : lo + k ≤ n) (hk2 : 2 ≤ k) (H : EighArenas)
    {par Su Sg c : ℕ} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)} {R R₀ ε β : K}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hR : st.store.read p H.Lv (2 * d) = some R)
    (hRtest : (eighTapeMachine I p mmR qrR).le R ((eighTapeMachine I p mmR qrR).mul ε R₀) = false)
    (hpar : st.store.read p par 2 = some β)
    (hSu : st.store.read p Su lo = some (I.tape .uniform (n * d + lo)))
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
        some st') :
    let M := eighTapeMachine I p mmR qrR
    (match eighStep M n F R₀ β A R ε (ℓ₀ + d) (eighTapeSample n d lo) with
      | .leaf _ _ => False
      | .shift b A' _ =>
        pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) A' ∧
          st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
          st'.store.read p H.Kd (n * d + lo) = I.sem.lit p (((if b then 2 else 3 : ℕ)) : ℚ)
      | .split kp _ Qp Qm Ap Am _ =>
        pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
          pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) Ap ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Am ∧
          st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
          st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
          st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
          st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
      (∀ q b i, ¬ ((b = H.Qa ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧
            i < 2 * (n * n) * d + 2 * n * (lo + k)) ∨
          (b = H.Ma ∧ 2 * (n * n) * (d + 1) + 2 * n * lo ≤ i ∧
            i < 2 * (n * n) * (d + 1) + 2 * n * (lo + k)) ∨
          (b = H.Sz ∧ n * (d + 1) + lo ≤ i ∧ i < n * (d + 1) + lo + k ∧
            (i = n * (d + 1) + lo ∨
              match eighStep M n F R₀ β A R ε (ℓ₀ + d) (eighTapeSample n d lo) with
              | .split kp _ _ _ _ _ _ => i = n * (d + 1) + (lo + kp)
              | _ => False)) ∨
          ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo)) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨-, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := id hH
  obtain ⟨z0, o, -, hl1, -, -⟩ := id hflag
  have hn2 : 0 < 4 * (n * n) := by have : 0 < n := (by omega); positivity
  have lSg := Store.lt_size_of_read_eq_some (hSg 0 hn2)
  have lpar := Store.lt_size_of_read_eq_some hpar
  have lSu := Store.lt_size_of_read_eq_some hSu
  have lc := Store.lt_size_of_read_eq_some (hc.1.trans hl1)
  have hlt : ∀ b ∈ H.handles ++ [par, Su, Sg, c], b < st.store.size := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSz, hsz hKd, hsz hKp, hsz hLv, lpar, lSu,
      lSg, lc]
  have hltH : ∀ b ∈ H.handles, b < st.store.size := fun b hb => hlt b (List.mem_append_left _ hb)
  obtain ⟨hbS, hcS⟩ := nodup_scratch_node (Pp := st.store.size + 5) (Pm := st.store.size + 6)
    hbufs hlt (by omega) (by omega) (by omega)
  -- the allocations
  obtain ⟨s₁, h₁, e₁⟩ := alloc_inv_skip_node h
  obtain ⟨s₂, h₂, e₂⟩ := alloc_inv_node h₁
  obtain ⟨s₃, h₃, e₃⟩ := alloc_inv_node h₂
  obtain ⟨s₄, h₄, e₄⟩ := alloc_inv_node h₃
  obtain ⟨s₅, h₅, e₅⟩ := alloc_inv_node h₄
  obtain ⟨s₆, h₆, e₆⟩ := alloc_inv_node h₅
  obtain ⟨s₇, h₇, e₇⟩ := alloc_inv_node h₆
  clear h h₁ h₂ h₃ h₄ h₅ h₆
  subst e₁ e₂ e₃ e₄ e₅ e₆ e₇
  refine name_state_node h₇ ?_
  clear h₇
  intro σ₇ hσs hσp h₇
  simp only at hσs hσp
  have hrd : ∀ {q : P} {b i : ℕ}, b < st.store.size →
      σ₇.store.read q b i = st.store.read q b i := fun hb => by
    rw [hσs]
    iterate 7 rw [Store.read_push_of_lt (by first | omega | (simp only [Array.size_push]; omega))]
  have hshp : ∀ {b : ℕ}, b < st.store.size → σ₇.store.shape[b]? = st.store.shape[b]? :=
    fun hb => by
      rw [hσs]
      iterate 7 rw [Store.getElem?_shape_push_of_lt _
        (by first | omega | (simp only [Array.size_push]; omega))]
  have hsz₇ : σ₇.store.size = st.store.size + 7 := by rw [hσs]; simp
  have hlt3 : ∀ b ∈ H.handles ++ [par, Su, c], b < st.store.size := fun b hb => by
    rcases List.mem_append.mp hb with hb | hb
    · exact hltH b hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      exacts [lpar, lSu, lc]
  have S := node_setup_holds hmm p hflag n ℓ₀ F d lo k hk H (par := par) (Su := Su) (c := c)
    (A := A) (R := R) (β := β) st.store.size hlt3 _ _ _ _ _ _ _ (by simp <;> omega)
    (by simp [List.nodup_cons] <;> omega) (by rw [hσs]; simp [Store.shape, Array.getElem?_push, Array.getElem_push])
    (fun i j t => (hrd (hsz hMa)).trans (hA i j t)) ((hrd (hsz hLv)).trans hR)
    ((hrd lpar).trans hpar) ((hrd lSu).trans hSu)
    ⟨(hrd lc).trans hc.1, (hrd lc).trans hc.2.1, (hrd lc).trans hc.2.2.1,
      (hrd lc).trans hc.2.2.2.1⟩ _ (h := h₇)
  obtain ⟨σ, hσ, hlo, hsh, hps, ht0, ht1, ht6, hPp, hPm, htwoM⟩ := S
  have hsz' : σ.store.size = st.store.size + 7 := by
    rw [Store.size_eq_of_shape_eq hsh, hsz₇]
  have hH' : H.Shaped σ.store p n D :=
    ⟨hH.1, by rw [hsh, hshp (hsz hMa)]; exact hMa, by rw [hsh, hshp (hsz hUa)]; exact hUa,
      by rw [hsh, hshp (hsz hQa)]; exact hQa, by rw [hsh, hshp (hsz hEa)]; exact hEa,
      by rw [hsh, hshp (hsz hSz)]; exact hSz, by rw [hsh, hshp (hsz hKd)]; exact hKd,
      by rw [hsh, hshp (hsz hKp)]; exact hKp, by rw [hsh, hshp (hsz hLv)]; exact hLv⟩
  have hlt2 : ∀ b ∈ H.handles ++ [Sg, c], b < st.store.size := fun b hb => by
    rcases List.mem_append.mp hb with hb | hb
    · exact hltH b hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      exacts [lSg, lc]
  have Bk := node_branch_holds hmm hqr p hcmp n d lo k (fun q m hm => hlit q m (by omega)) htn hk
    hk2 H (Sg := Sg) (c := c) (st := σ)
    (st' := s₇) (A := A) hd hH' st.store.size
    (nodup_scratch_node hbufs hlt (by simp <;> omega) (by simp <;> omega) (by simp)).1 hlt2 hcS
    (by refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega) (by intro h; simp at h; omega)
    (by intro h; simp at h; omega)
    (by rw [hsz']; simp) (by rw [hsz']; omega)
    (fun i j t => (hlo _ _ _ (hsz hMa)).trans ((hrd (hsz hMa)).trans (hA i j t))) hPp hPm
    (fun w hw => (hlo _ _ _ lSg).trans ((hrd lSg).trans (hSg w hw)))
    ((hlo _ _ _ lc).trans htwoM)
    ((hlo _ _ _ lc).trans ((hrd lc).trans hc.2.2.2.2)) ht0 ht1 ht6 (h := hσ)
  obtain ⟨B1, B2, B3, Bfr, Bsh, Bps⟩ := Bk
  have hs7 : s₇.store.size = st.store.size + 7 := by
    rw [Store.size_eq_of_shape_eq Bsh, hsz']
  have hpop : ∀ {q : P} {b i : ℕ}, b < st.store.size →
      Store.read (Array.pop^[7] s₇.store) q b i = s₇.store.read q b i :=
    fun hb => read_pops_node 7 (by omega)
  refine ⟨?_, fun q b i hW => ?_, ?_, ?_⟩
  · have hRt : M.le R (M.mul ε R₀) = false := hRtest
    unfold eighStep
    dsimp only
    split_ifs with h0 hle h1 h2
    · omega
    · exact absurd hle (by rw [hRt]; decide)
    · obtain ⟨x1, x2, x3⟩ := B1 h1
      exact ⟨fun i j t => (hpop (hsz hMa)).trans (x1 i j t), (hpop (hsz hSz)).trans x2,
        (hpop (hsz hKd)).trans x3⟩
    · obtain ⟨x1, x2, x3⟩ := B2 h2
      exact ⟨fun i j t => (hpop (hsz hMa)).trans (x1 i j t), (hpop (hsz hSz)).trans x2,
        (hpop (hsz hKd)).trans x3⟩
    · obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := 
        B3 (Nat.pos_of_ne_zero h2) (lt_of_le_of_ne (min_le_left _ _) h1)
      exact ⟨fun i j t => (hpop (hsz hQa)).trans (x1 i j t),
        fun i j t => (hpop (hsz hQa)).trans (x2 i j t),
        fun i j t => (hpop (hsz hMa)).trans (x3 i j t),
        fun i j t => (hpop (hsz hMa)).trans (x4 i j t),
        (hpop (hsz hSz)).trans x5, (hpop (hsz hSz)).trans x6, (hpop (hsz hKd)).trans x7,
        (hpop (hsz hKp)).trans x8⟩
  · by_cases hb : b < st.store.size
    · refine (hpop hb).trans ((Bfr q b i hb ?_).trans ((hlo q b i hb).trans (hrd hb)))
      have hRt : M.le R (M.mul ε R₀) = false := hRtest
      intro hN
      apply hW
      unfold nodeWin at hN
      rcases hN with h1 | h1 | ⟨hbS, hi⟩ | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · refine Or.inr (Or.inr (Or.inl ⟨hbS, ?_⟩))
        split_ifs at hi with hc
        · rcases hi with rfl | rfl
          · exact ⟨by omega, by omega, Or.inl rfl⟩
          · refine ⟨by omega, by omega, Or.inr ?_⟩
            unfold eighStep
            dsimp only
            split_ifs with h0 hle h1 h2
            · omega
            · exact absurd hle (by rw [hRt]; decide)
            · exact absurd h1 (Nat.ne_of_lt hc.2)
            · exact absurd h2 (Nat.pos_iff_ne_zero.mp hc.1)
            · rfl
        · rcases hi with rfl | rfl <;> exact ⟨by omega, by omega, Or.inl rfl⟩
      · exact Or.inr (Or.inr (Or.inr h1))
    · have hsz'' : (Array.pop^[7] s₇.store).size = st.store.size := by
        simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Array.size_pop,
          hs7]
        omega
      exact (show Store.read (Array.pop^[7] s₇.store) q b i = none from
        Store.read_eq_none_of_size_le (by omega)).trans
          (Store.read_eq_none_of_size_le (by omega)).symm
  · change Store.shape (Array.pop (Array.pop (Array.pop (Array.pop (Array.pop (Array.pop
      (Array.pop s₇.store))))))) = _
    simp only [Store.shape_pop, Bsh, hsh, hσs]
    simp [Store.shape]
  · exact Bps.trans (hps.trans hσp)

/-- The node step computes `NLAlib.eighStep`: let the kernels of `I` be the routines `mmR`,
`qrR` on interleaved pairs and the semantics decide flags at `p`; let $M$ be the machine of the
interpretation (`NLAlib.eighTapeMachine`). A successful run of `NLAlib.eighNodeBlock` at the slot
$lo$ of depth $d$ for a node of size $k \ge 2$, $lo + k \le n$, whose matrix $\mathbf{A}$ is held at
its block of `Ma`, whose window $R$ is in the cell $2d$ of `Lv`, whose seed is the cell $lo$ of `Su`
(the tape at uniform position $nd + lo$), with the level's Gaussian words in `Sg`, the stored
$\beta$ in cell $2$ of `par` and the constants (the machine's one, $\mathrm{fl}(2)$,
$\mathrm{fl}(1/2)$, $-1$ and the stored $\sqrt{1/2}$, `NLAlib.Computation.ScalarSem.sqrtHalf`) in
cells $0$ to $4$ of `c`, ends with the outcome of `NLAlib.eighStep` at the
node's samples (`NLAlib.eighTapeSample`, depth counter $\ell_0 + d$), when it is not a leaf: for one
child on side $b$, the shifted matrix at the same slot of depth $d + 1$, the size $k$ there, and the
kind $2$ ($b$ true) or $3$; for a split into $k_+$, everything `NLAlib.holds_of_exec_eighSplitBlock`
writes. Every cell outside depths $d$ and $d + 1$ of the arenas (and outside `Su`, `Sg`, `c`, `par`,
which are only read) is unchanged, the store shape and the tape positions too. No printed source. -/
theorem holds_of_exec_eighNodeBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (hflag : I.sem.DecidesFlags p)
    {dec : P → K → ℝ} (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d lo k : ℕ) (hlit : IsExactIntLit dec I.sem (n + 2)) (htn : IsExactToNat dec I.sem)
    (hk : lo + k ≤ n) (hk2 : 2 ≤ k) (H : EighArenas)
    {par Su Sg c : ℕ} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)} {R R₀ ε β : K}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hR : st.store.read p H.Lv (2 * d) = some R)
    (hRtest : (eighTapeMachine I p mmR qrR).le R ((eighTapeMachine I p mmR qrR).mul ε R₀) = false)
    (hpar : st.store.read p par 2 = some β)
    (hSu : st.store.read p Su lo = some (I.tape .uniform (n * d + lo)))
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
        some st') :
    let M := eighTapeMachine I p mmR qrR
    (match eighStep M n F R₀ β A R ε (ℓ₀ + d) (eighTapeSample n d lo) with
      | .leaf _ _ => False
      | .shift b A' _ =>
        pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) A' ∧
          st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
          st'.store.read p H.Kd (n * d + lo) = I.sem.lit p (((if b then 2 else 3 : ℕ)) : ℚ)
      | .split kp _ Qp Qm Ap Am _ =>
        pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
          pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) Ap ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Am ∧
          st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
          st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
          st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
          st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
      (∀ q b i, ¬ H.LevelCell n d b i → ¬ H.LevelCell n (d + 1) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  obtain ⟨hstep, hfr, hsh, hps⟩ := holds_of_exec_eighNodeBlock_frame hmm hqr p hflag hcmp n ℓ₀ F
    d lo k hlit htn hk hk2 H hd hH hbufs hA hR hRtest hpar hSu hSg hc h
  refine ⟨hstep, fun q b i h1 h2 => hfr q b i fun hW => ?_, hsh, hps⟩
  have hlok : n * (lo + k) ≤ n * n := Nat.mul_le_mul_left _ hk
  rcases hW with ⟨rfl, hi1, hi2⟩ | ⟨rfl, hi1, hi2⟩ | ⟨rfl, hi1, hi2, -⟩ | ⟨hb, rfl⟩
  · exact h1 (Or.inl ⟨Or.inr (Or.inr rfl), by linarith [Nat.zero_le (n * lo)],
      by linarith⟩)
  · exact h2 (Or.inl ⟨Or.inl rfl, by linarith [Nat.zero_le (n * lo)], by linarith⟩)
  · exact h2 (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by linarith, by
      rw [Nat.mul_succ]; omega⟩))
  · exact h1 (Or.inr (Or.inl ⟨by rcases hb with rfl | rfl <;> simp, by omega, by
      rw [Nat.mul_succ]; omega⟩))

end NLAlib
