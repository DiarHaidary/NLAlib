/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionNode.SignStep
public import NLAlib.Matrix.Computation.SpectralBisectionNode.SplitSuccess

/-!
# The split block of the spectral bisection node step

A successful run of the split block of the node step of `NLAlib.eighProg` writes the outcome of the
split of `NLAlib.eighStep` on the machine of the semantics: the two children's matrices, sizes and
kinds, and the bases of the deflations; every cell outside the node's window is unchanged.

## Main results

* `NLAlib.holds_of_exec_eighSplitBlock`: what a successful split computes.
* `NLAlib.holds_of_exec_eighSplitBlock_frame`: the same, with the precise frame of the node's
  window.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### The node step -/
/-- A packed complex entry lies in its block. -/
private theorem pair_idx_lt_node {l m : ℕ} (i : Fin l) (j : Fin m) (t : Fin 2) :
    2 * ((i : ℕ) + l * j) + t < 2 * (l * m) := by
  have := i.2; have := j.2; have := t.2
  have : l * ((j : ℕ) + 1) ≤ l * m := Nat.mul_le_mul_left l j.2
  nlinarith

/-- A cell is disjoint from a block inside a window it avoids. -/
theorem bd_of_win_node {b i B off len lo' hi' : ℕ} (h : b = B → i < lo' ∨ hi' ≤ i)
    (h1 : lo' ≤ off) (h2 : off + len ≤ hi') : blockDisjoint (b, i, 1) (B, off, len) = true := by
  unfold blockDisjoint
  by_cases hb : b = B
  · rcases h hb with h | h
    · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl (Or.inr (by omega))
    · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr (by omega)
  · simp [hb]

omit [Inhabited K] in
/-- Name the state of a run. -/
theorem name_state_node {X : Stmt P ι ℕ ℕ} {s s' : St P K C} (h : exec I X s = some s')
    {Q : Prop} (k : ∀ σ : St P K C, σ.store = s.store → σ.pos = s.pos → exec I X σ = some s' → Q) :
    Q := k s rfl rfl h

/-- Seven handles, three below `s₀` and four from `s₀` on, are distinct. -/
private theorem nodup_def_node {a b c s₀ G Y Qf Rf : ℕ} (hab : a = b → False) (hac : a = c → False)
    (hbc : b = c → False) (ha : a < s₀) (hb : b < s₀) (hc : c < s₀) (h4 : [G, Y, Qf, Rf].Nodup)
    (hG : s₀ ≤ G) (hY : s₀ ≤ Y) (hQ : s₀ ≤ Qf) (hR : s₀ ≤ Rf) : [a, b, G, Y, Qf, Rf, c].Nodup := by
  have : a ≠ b := hab; have : a ≠ c := hac; have : b ≠ c := hbc
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h4 ⊢
  omega

/-- Six handles, two below `s₀` and four from `s₀` on, are distinct. -/
private theorem nodup_cmp_node {a b s₀ Qh C1 C2 C3 : ℕ} (hab : a = b → False) (ha : a < s₀)
    (hb : b < s₀) (h4 : [Qh, C1, C2, C3].Nodup) (h1 : s₀ ≤ Qh) (h2 : s₀ ≤ C1) (h3 : s₀ ≤ C2)
    (h5 : s₀ ≤ C3) : [a, b, Qh, C1, C2, C3].Nodup := by
  have : a ≠ b := hab
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h4 ⊢
  omega

/-- A handle below `s₀` is not among four from `s₀` on and another. -/
private theorem notmem5_node {x s₀ G Y Qf Rf c : ℕ} (hx : x < s₀) (hG : s₀ ≤ G) (hY : s₀ ≤ Y)
    (hQ : s₀ ≤ Qf) (hR : s₀ ≤ Rf) (hc : x = c → False) : x ∉ [G, Y, Qf, Rf, c] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨by omega, by omega, by omega, by omega, hc⟩

/-- The index arithmetic of a split inside the window of its node. -/
private theorem split_arith_node {n d lo k kp : ℕ} (hk : lo + k ≤ n) (hkpk : kp < k) :
    2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ 2 * (n * n) * (d + 1) + 2 * n * lo ∧
    2 * (n * n) * (d + 1) + 2 * n * lo + 2 * (kp * kp) ≤
      2 * (n * n) * (d + 1) + 2 * n * (lo + kp) ∧
    2 * (n * n) * (d + 1) + 2 * n * (lo + kp) + 2 * ((k - kp) * (k - kp)) ≤
      2 * (n * n) * (d + 1) + 2 * n * (lo + k) ∧
    2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) ≤ 2 * (n * n) * d + 2 * n * (lo + k) ∧
    2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) + 2 * (k * (k - kp)) ≤
      2 * (n * n) * d + 2 * n * (lo + k) ∧
    2 * (n * n) * (d + 1) + 2 * n * lo ≤ 2 * (n * n) * (d + 1) + 2 * n * (lo + kp) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = kp + r := ⟨k - kp, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have h1 : kp * kp ≤ n * kp := Nat.mul_le_mul_right _ (by omega)
  have h2 : r * r ≤ n * r := Nat.mul_le_mul_right _ (by omega)
  have h3 : (kp + r) * (kp + r) ≤ n * (kp + r) := Nat.mul_le_mul_right _ (by omega)
  have h4 : n * lo + n * (kp + r) ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- The cells a node step at the slot $lo$ of depth $d$ for a node of size $k$ may write in the
arenas. -/
def nodeWin (H : EighArenas) (n d lo k j b i : ℕ) : Prop :=
  (b = H.Qa ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧ i < 2 * (n * n) * d + 2 * n * (lo + k)) ∨
    (b = H.Ma ∧ 2 * (n * n) * (d + 1) + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * (d + 1) + 2 * n * (lo + k)) ∨
    (b = H.Sz ∧ (i = n * (d + 1) + lo ∨ i = n * (d + 1) + j)) ∨
    ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo)

omit [Inhabited K] in
/-- A held block is kept if every read of its words is kept. -/
private theorem holds_keep_node {s s' : Store P K} {p : P} {b off l m : ℕ}
    {Y : Matrix (Fin l) (Fin m) (K × K)} (hY : pairLayout.Holds s p b off Y)
    (h : ∀ i, off ≤ i → i < off + 2 * (l * m) → s'.read p b i = s.read p b i) :
    pairLayout.Holds s' p b off Y :=
  hY.of_forall_read_eq fun i h1 h2 => h i h1 (by
    change i < off + m * l * 2 at h2
    linarith [Nat.mul_comm l m])

-- The split unfolds large index expressions.
set_option maxHeartbeats 4000000 in
/-- The body of a split after its eight allocations: the values of
`NLAlib.holds_of_exec_eighSplitBlock`, and every cell of a buffer below `s₀` outside the cell
`sq` and the node's window is kept. -/
private theorem split_body_holds {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n d lo k kp : ℕ) (hk : lo + k ≤ n)
    (hkp : 0 < kp) (hkpk : kp < k) (kpe : IExp ℕ) (hkpe : kpe.eval = kp) (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ}
    {σ : K} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)} {D : ℕ} (hd : d < D) (s₀ : ℕ)
    (hlt : ∀ b ∈ H.handles ++ [Sg, Pp, Pm, two.buf, sg.buf, nsg.buf, sq.buf], b < s₀)
    (G Y Qf Rf Qh C1 C2 C3 : ℕ) (hge : ∀ X ∈ [G, Y, Qf, Rf, Qh, C1, C2, C3], s₀ ≤ X)
    (hnd : [G, Y, Qf, Rf, Qh, C1, C2, C3].Nodup)
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p two.buf two.idx.eval = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval =
      some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (h : exec I (do
      eighDeflateBlock p mm qr (.const n) (.const k) (kpe) (.const lo) 0 Sg sq Pp G Y Qf Rf
        H.Qa (eighBlockOff (.const n) (.const d) (.const lo))
      eighDeflateBlock p mm qr (.const n) (.const k) (.const k - kpe) (.const lo) 1 Sg sq Pm
        G Y Qf Rf H.Qa (eighBlockOff (.const n) (.const d) (.const lo) +
          2 * (.const k * kpe))
      eighCompressBlock p mm (.const k) (kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo)) two sg Qh C1 C2 C3
      eighCompressBlock p mm (.const k) (.const k - kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg Qh C1 C2 C3
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ (kpe))
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
        (.const k - kpe))
      ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
      ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ (kpe)) :
        Builder P ι ℕ ℕ Unit).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let s := eighTapeSample n d lo
    let Qp := deflate M kp Ppm (leadingBlock k (s.2 true))
    let Qm := deflate M (k - kp) Pmm (leadingBlock k (s.2 false))
    (pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) σ) ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
          (M.neg σ)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
      (∀ q b i, b < s₀ → ¬ nodeWin H n d lo k (lo + kp) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M s Qp Qm
  -- the handles (distinctness kept as implications, out of `omega`'s sight)
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt hge
  obtain ⟨lMa, lUa, lQa, lEa, lSz, lKd, lKp, lLv, lSg, lPp, lPm, ltwo, lsg, lnsg, lsq⟩ := hlt
  obtain ⟨gG, gY, gQf, gRf, gQh, gC1, gC2, gC3⟩ := hge
  have h4a : [G, Y, Qf, Rf].Nodup :=
    (List.nodup_append.mp (show ([G, Y, Qf, Rf] ++ [Qh, C1, C2, C3]).Nodup from hnd)).1
  have h4b : [Qh, C1, C2, C3].Nodup :=
    (List.nodup_append.mp (show ([G, Y, Qf, Rf] ++ [Qh, C1, C2, C3]).Nodup from hnd)).2.1
  have dSgPp : Sg = Pp → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSgPm : Sg = Pm → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSgQa : Sg = H.Qa → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dPpQa : Pp = H.Qa → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dPmQa : Pm = H.Qa → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaQa : H.Ma = H.Qa → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzKd : H.Sz = H.Kd → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzKp : H.Sz = H.Kp → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dKdKp : H.Kd = H.Kp → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dQaSz : H.Qa = H.Sz → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dQaKd : H.Qa = H.Kd → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dQaKp : H.Qa = H.Kp → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaSz : H.Ma = H.Sz → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaKd : H.Ma = H.Kd → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaKp : H.Ma = H.Kp → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have cc : ∀ c ∈ [two, sg, nsg, sq], ∀ b ∈ H.handles ++ [Sg, Pp, Pm], c.buf = b → False :=
    fun c hc b hb h => hcells c hc (h ▸ hb)
  have sqPp : Pp = sq.buf → False := fun h => cc sq (by simp) Pp (by simp) h.symm
  have sqPm : Pm = sq.buf → False := fun h => cc sq (by simp) Pm (by simp) h.symm
  have sqSg : Sg = sq.buf → False := fun h => cc sq (by simp) Sg (by simp) h.symm
  have sqQa : sq.buf = H.Qa → False := cc sq (by simp) H.Qa (by simp [EighArenas.handles])
  have sqMa : H.Ma = sq.buf → False := fun h =>
    cc sq (by simp) H.Ma (by simp [EighArenas.handles]) h.symm
  have twoQa : two.buf = H.Qa → False := cc two (by simp) H.Qa (by simp [EighArenas.handles])
  have sgQa : sg.buf = H.Qa → False := cc sg (by simp) H.Qa (by simp [EighArenas.handles])
  have nsgQa : nsg.buf = H.Qa → False := cc nsg (by simp) H.Qa (by simp [EighArenas.handles])
  have twoMa : two.buf = H.Ma → False := cc two (by simp) H.Ma (by simp [EighArenas.handles])
  have sgMa : sg.buf = H.Ma → False := cc sg (by simp) H.Ma (by simp [EighArenas.handles])
  have nsgMa : nsg.buf = H.Ma → False := cc nsg (by simp) H.Ma (by simp [EighArenas.handles])
  have hkn : k ≤ n := by omega
  have nS4 : ∀ b, b < s₀ → b ∉ [G, Y, Qf, Rf] := fun b hb => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega
  have nC4 : ∀ b, b < s₀ → b ∉ [Qh, C1, C2, C3] := fun b hb => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  -- the stored √(1/2), read from `sq` (written once by `eighProg`)
  refine name_state_node h ?_
  clear h
  intro σ2 hσ2s hσ2p h
  obtain ⟨z2, hz2, hM2⟩ : ∃ z2, st.store.read p two.buf two.idx.eval = some z2 ∧ M.ofNat 2 = z2 :=
    ⟨_, htwo, rfl⟩
  have hf2 : ∀ q b i, σ2.store.read q b i = st.store.read q b i := fun q b i => by rw [hσ2s]
  have hsh2 : σ2.store.shape = st.store.shape := by rw [hσ2s]
  have hb2 : ∀ q b i, b ≠ sq.buf → σ2.store.read q b i = st.store.read q b i :=
    fun q b i _ => hf2 q b i
  have hsq2 : σ2.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p) := (hf2 _ _ _).trans hsq
  -- the first deflation
  rw [exec_eighDeflateBlock_bind_split, exec_eighDeflateBlock_congr_split, hkpe] at h
  obtain ⟨σ3, h3, h⟩ := Option.bind_eq_some_iff.mp h
  have hbo : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval =
      2 * (n * n) * d + 2 * n * lo := by
    simp [eighBlockOff]
  obtain ⟨hQp3, hf3, hsh3, hp3⟩ := holds_of_exec_eighDeflateBlock hmm hqr p n k kp d lo hk
    hkpk.le true (qo := eighBlockOff (.const n) (.const d) (.const lo)) (st := σ2) (st' := σ3)
    (fun i j t => (hb2 _ _ _ sqPp).trans (hPp i j t)) hsq2
    (fun w hw => (hb2 _ _ _ sqSg).trans (hSg w hw))
    (nodup_def_node dSgPp dSgQa dPpQa lSg lPp lQa h4a gG gY gQf gRf)
    (notmem5_node lsq gG gY gQf gRf sqQa) (by exact h3)
  rw [hbo] at hQp3 hf3
  have hk3 : ∀ q b i, s₀ > b → b ≠ H.Qa → σ3.store.read q b i = σ2.store.read q b i :=
    fun q b i h1 h2 => hf3 q b i (nS4 _ (by omega)) (by simp [blockDisjoint, h2])
  -- the second deflation
  rw [exec_eighDeflateBlock_bind_split, exec_eighDeflateBlock_congr_split] at h
  simp only [IExp.eval_sub, IExp.eval_const, hkpe] at h
  obtain ⟨σ4, h4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hQm4, hf4, hsh4, hp4⟩ := holds_of_exec_eighDeflateBlock hmm hqr p n k (k - kp) d lo hk
    (Nat.sub_le _ _) false
    (qo := eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe))
    (st := σ3) (st' := σ4)
    (fun i j t => ((hk3 _ _ _ (by omega) dPmQa).trans (hb2 _ _ _ sqPm)).trans
      (hPm i j t))
    ((hk3 _ _ _ (by omega) sqQa).trans hsq2)
    (fun w hw => ((hk3 _ _ _ (by omega) dSgQa).trans (hb2 _ _ _ sqSg)).trans
      (hSg w hw))
    (nodup_def_node dSgPm dSgQa dPmQa lSg lPm lQa h4a gG gY gQf gRf)
    (notmem5_node lsq gG gY gQf gRf sqQa) (by exact h4)
  simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat, hbo, hkpe] at hQm4 hf4
  have hk4 : ∀ q b i, s₀ > b → b ≠ H.Qa → σ4.store.read q b i = σ3.store.read q b i :=
    fun q b i h1 h2 => hf4 q b i (nS4 _ (by omega)) (by simp [blockDisjoint, h2])
  obtain ⟨F1, F3, F4, F6, F7, F2⟩ := split_arith_node (d := d) hk hkpk
  have hkk : k * k ≤ n * n := Nat.mul_le_mul hkn hkn
  have hkpn : kp * kp ≤ n * kp := Nat.mul_le_mul_right _ (by omega)
  have hkmn : (k - kp) * (k - kp) ≤ n * (k - kp) := Nat.mul_le_mul_right _ (by omega)
  have hkkn : k * k ≤ n * k := Nat.mul_le_mul_right _ hkn
  have hkkp : k * kp + k * (k - kp) = k * k := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hkpk.le]
  have hlok : n * lo + n * k ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  have hQp4 : pairLayout.Holds σ4.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp :=
    holds_keep_node hQp3 fun i _ hi => hf4 p _ i (nS4 _ (by omega)) (by
        simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
          decide_eq_true_eq]
        left; omega)
  have hst4 : ∀ q b i, s₀ > b → b ≠ H.Qa → b ≠ sq.buf →
      σ4.store.read q b i = st.store.read q b i := fun q b i h1 h2 h3 =>
    (hk4 q b i h1 h2).trans ((hk3 q b i h1 h2).trans (hb2 q b i h3))
  have hA4 : pairLayout.Holds σ4.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A :=
    fun i j t => (hst4 _ _ _ (by omega) dMaQa sqMa).trans (hA i j t)
  have hcst4 : ∀ c : Cell ℕ ℕ, c.buf < s₀ → c.buf ≠ H.Qa →
      σ4.store.read p c.buf c.idx.eval = st.store.read p c.buf c.idx.eval :=
    fun c h1 h2 => (hk4 _ _ _ h1 h2).trans ((hk3 _ _ _ h1 h2).trans (hf2 _ _ _))
  have htwo4 := (hcst4 two ltwo twoQa).trans hz2
  have hσ4 := (hcst4 sg lsg sgQa).trans hσ
  have hnσ4 := (hcst4 nsg lnsg nsgQa).trans hnσ
  -- the first compression
  rw [exec_eighCompressBlock_bind_split, exec_eighCompressBlock_congr_split, hkpe] at h
  obtain ⟨σ5, h5, h⟩ := Option.bind_eq_some_iff.mp h
  have hbo1 : (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.const lo)).eval =
      2 * (n * n) * (d + 1) + 2 * n * lo := by
    simp [eighBlockOff]
  have hbo2 : (eighBlockOff (IExp.const n) (IExp.const d + 1)
      (IExp.const lo + kpe)).eval = 2 * (n * n) * (d + 1) + 2 * n * (lo + kp) := by
    simp [eighBlockOff, hkpe]
  obtain ⟨hAp5, hf5, hsh5, hp5⟩ := holds_of_exec_eighCompressBlock
    (toNat := fun x => (I.sem.toNat p x).getD 0) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    hmm p k kp (qo := eighBlockOff (.const n) (.const d) (.const lo))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo)) (st := σ4) (st' := σ5)
    (by rw [hbo]; exact hQp4) (by rw [hbo]; exact hA4) htwo4 hσ4
    (nodup_cmp_node (fun h => dMaQa h.symm) lQa lMa h4b gQh gC1 gC2 gC3)
    ⟨nC4 _ ltwo, nC4 _ lsg⟩
    (by
      rw [hbo, hbo1]
      simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
        decide_eq_true_eq]
      right; linarith)
    ⟨by simp [blockDisjoint, show H.Ma ≠ two.buf from fun h => twoMa h.symm],
      by simp [blockDisjoint, show H.Ma ≠ sg.buf from fun h => sgMa h.symm]⟩ (by exact h5)
  rw [hbo1, ← hM2] at hAp5
  rw [hbo1] at hf5
  have hk5 : ∀ q b i, s₀ > b → b ≠ H.Ma → σ5.store.read q b i = σ4.store.read q b i :=
    fun q b i h1 h2 => hf5 q b i (nC4 _ (by omega)) (by simp [blockDisjoint, h2])
  -- the second compression
  rw [exec_eighCompressBlock_bind_split, exec_eighCompressBlock_congr_split] at h
  simp only [IExp.eval_sub, IExp.eval_const, hkpe] at h
  obtain ⟨σ6, h6, h⟩ := Option.bind_eq_some_iff.mp h
  have hqo2 : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo) +
      2 * (IExp.const k * kpe)).eval = 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) := by
    simp [eighBlockOff, hkpe]
  obtain ⟨hAm6, hf6, hsh6, hp6⟩ := holds_of_exec_eighCompressBlock
    (toNat := fun x => (I.sem.toNat p x).getD 0) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    hmm p k (k - kp)
    (qo := eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) (st := σ5)
    (st' := σ6)
    (by
      rw [hqo2]
      exact fun i j t => (hk5 _ _ _ (by omega) (fun h => dMaQa h.symm)).trans (hQm4 i j t))
    (by
      rw [hbo]
      exact holds_keep_node hA4 fun i _ hi => hf5 p _ i (nC4 _ (by omega)) (by
          simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
            decide_eq_true_eq]
          left; linarith))
    ((hk5 _ _ _ ltwo twoMa).trans htwo4) ((hk5 _ _ _ lnsg nsgMa).trans hnσ4)
    (nodup_cmp_node (fun h => dMaQa h.symm) lQa lMa h4b gQh gC1 gC2 gC3)
    ⟨nC4 _ ltwo, nC4 _ lnsg⟩
    (by
      rw [hbo, hbo2]
      simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
        decide_eq_true_eq]
      right; linarith)
    ⟨by simp [blockDisjoint, show H.Ma ≠ two.buf from fun h => twoMa h.symm],
      by simp [blockDisjoint, show H.Ma ≠ nsg.buf from fun h => nsgMa h.symm]⟩ (by exact h6)
  rw [hbo2, ← hM2] at hAm6
  rw [hbo2] at hf6
  have hk6 : ∀ q b i, s₀ > b → b ≠ H.Ma → σ6.store.read q b i = σ5.store.read q b i :=
    fun q b i h1 h2 => hf6 q b i (nC4 _ (by omega)) (by simp [blockDisjoint, h2])
  -- the records
  rw [hr] at h
  obtain ⟨v7, s7, hv7, hw7, h⟩ := eighSignH_inv_litIdx h
  rw [hr] at h
  obtain ⟨v8, s8, hv8, hw8, h⟩ := eighSignH_inv_litIdx h
  rw [hr] at h
  obtain ⟨v9, s9, hv9, hw9, h⟩ := eighSignH_inv_litIdx h
  change exec I (.seq (.instr _) .skip) _ = some st' at h
  obtain ⟨v10, s10, hv10, hw10, h⟩ := eighSignH_inv_litIdx h
  rw [exec_skip, Option.some_inj] at h
  subst h
  simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat,
    IExp.eval_sub, hkpe] at hv7 hw7 hv8 hw8 hv9 hw9 hv10 hw10
  have hrec : ∀ q b i, b ≠ H.Sz → b ≠ H.Kd → b ≠ H.Kp →
      s10.read q b i = σ6.store.read q b i := fun q b i h1 h2 h3 => by
    rw [Store.read_of_write_eq_some_of_ne hw10 (Or.inl h3),
      Store.read_of_write_eq_some_of_ne hw9 (Or.inl h2),
      Store.read_of_write_eq_some_of_ne hw8 (Or.inl h1),
      Store.read_of_write_eq_some_of_ne hw7 (Or.inl h1)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact fun i j t => (hrec _ _ _ dQaSz dQaKd dQaKp).trans
      ((hk6 _ _ _ (by omega) (fun h => dMaQa h.symm)).trans
        ((hk5 _ _ _ (by omega) (fun h => dMaQa h.symm)).trans (hQp4 i j t)))
  · exact fun i j t => (hrec _ _ _ dQaSz dQaKd dQaKp).trans
      ((hk6 _ _ _ (by omega) (fun h => dMaQa h.symm)).trans
        ((hk5 _ _ _ (by omega) (fun h => dMaQa h.symm)).trans (hQm4 i j t)))
  · refine fun i j t => (hrec _ _ _ dMaSz dMaKd dMaKp).trans ?_
    refine (hf6 _ _ _ (nC4 _ (by omega)) ?_).trans (hAp5 i j t)
    have := pair_idx_lt_node i j t
    simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
      decide_eq_true_eq]
    left
    change _ + (2 * _ + _) + 1 ≤ _
    linarith
  · exact fun i j t => (hrec _ _ _ dMaSz dMaKd dMaKp).trans (hAm6 i j t)
  · rw [Store.read_of_write_eq_some_of_ne hw10 (Or.inl dSzKp),
      Store.read_of_write_eq_some_of_ne hw9 (Or.inl dSzKd),
      Store.read_of_write_eq_some_of_ne hw8 (Or.inr (by omega)),
      Store.read_of_write_eq_some hw7, hv7]
  · rw [Store.read_of_write_eq_some_of_ne hw10 (Or.inl dSzKp),
      Store.read_of_write_eq_some_of_ne hw9 (Or.inl dSzKd),
      Store.read_of_write_eq_some hw8, hv8]
  · rw [Store.read_of_write_eq_some_of_ne hw10 (Or.inl dKdKp),
      Store.read_of_write_eq_some hw9, hv9]
  · rw [Store.read_of_write_eq_some hw10, hv10]
  · intro q b i hb hW
    simp only [nodeWin, not_or, not_and, not_lt] at hW
    obtain ⟨hWQ, hWM, hWS, hWK⟩ := hW
    rw [Store.read_of_write_eq_some_of_ne hw10 ?_, Store.read_of_write_eq_some_of_ne hw9 ?_,
      Store.read_of_write_eq_some_of_ne hw8 ?_, Store.read_of_write_eq_some_of_ne hw7 ?_]
    rotate_left
    · by_cases h1 : b = H.Sz
      · exact Or.inr (fun h2 => by have := hWS h1; omega)
      · exact Or.inl h1
    · by_cases h1 : b = H.Sz
      · exact Or.inr (fun h2 => by have := hWS h1; omega)
      · exact Or.inl h1
    · by_cases h1 : b = H.Kd
      · exact Or.inr (fun h2 => hWK (Or.inl h1) h2)
      · exact Or.inl h1
    · by_cases h1 : b = H.Kp
      · exact Or.inr (fun h2 => hWK (Or.inr h1) h2)
      · exact Or.inl h1
    have hbM : b = H.Ma → i < 2 * (n * n) * (d + 1) + 2 * n * lo ∨
        2 * (n * n) * (d + 1) + 2 * n * (lo + k) ≤ i := fun h1 => by
      by_contra hc
      push_neg at hc
      exact absurd (hWM h1 hc.1) (by omega)
    have hbQ : b = H.Qa → i < 2 * (n * n) * d + 2 * n * lo ∨
        2 * (n * n) * d + 2 * n * (lo + k) ≤ i := fun h1 => by
      by_contra hc
      push_neg at hc
      exact absurd (hWQ h1 hc.1) (by omega)
    rw [hf6 q b i (nC4 b hb) (bd_of_win_node hbM (by linarith) (by linarith)),
      hf5 q b i (nC4 b hb) (bd_of_win_node hbM (by linarith)
        (by linarith [Nat.zero_le ((k - kp) * (k - kp))])),
      hf4 q b i (nS4 b hb) (bd_of_win_node hbQ (by linarith [Nat.zero_le (k * kp)])
        (by linarith)),
      hf3 q b i (nS4 b hb) (bd_of_win_node hbQ (by linarith) (by linarith))]
    exact hf2 q b i
  · rw [Store.shape_of_write_eq_some hw10, Store.shape_of_write_eq_some hw9,
      Store.shape_of_write_eq_some hw8, Store.shape_of_write_eq_some hw7, hsh6, hsh5, hsh4, hsh3]
    exact hsh2
  · exact hp6.trans (hp5.trans (hp4.trans (hp3.trans hσ2p)))

omit [AddMonoid C] [Inhabited K] in
/-- Reads of a store below $m$ pops. -/
theorem read_pops_node : ∀ (m : ℕ) {s : Store P K} {q : P} {b i : ℕ}, b + m < s.size →
    Store.read (Array.pop^[m] s) q b i = s.read q b i
  | 0, _, _, _, _, _ => rfl
  | m + 1, s, q, b, i, h => by
    rw [Function.iterate_succ_apply, read_pops_node m (by simp [Array.size_pop]; omega),
      Store.read_pop_of_lt (by omega)]

omit [AddMonoid C] [Inhabited K] in
/-- Reads of a store below $m$ pushes. -/
private theorem read_pushes_node (x : P × Array (Option K)) : ∀ (m : ℕ) {s : Store P K} {q : P}
    {b i : ℕ}, b < s.size → Store.read ((fun s : Store P K => s.push x)^[m] s) q b i = s.read q b i
  | 0, _, _, _, _, _ => rfl
  | m + 1, s, q, b, i, h => by
    rw [Function.iterate_succ_apply, read_pushes_node x m (by simp; omega),
      Store.read_push_of_lt h]

omit [AddMonoid C] [Inhabited K] in
/-- The size of a store after $m$ pushes. -/
private theorem size_pushes_node (x : P × Array (Option K)) : ∀ (m : ℕ) (s : Store P K),
    ((fun s : Store P K => s.push x)^[m] s).size = s.size + m
  | 0, _ => rfl
  | m + 1, s => by
    rw [Function.iterate_succ_apply, size_pushes_node x m]; simp; omega

omit [AddMonoid C] [Inhabited K] in
/-- The shape of a store after $m$ pushes, below the old size. -/
private theorem shape_pushes_node (x : P × Array (Option K)) : ∀ (m : ℕ) {s : Store P K} {b : ℕ},
    b < s.size → (Store.shape ((fun s : Store P K => s.push x)^[m] s))[b]? = s.shape[b]?
  | 0, _, _, _ => rfl
  | m + 1, s, b, h => by
    rw [Function.iterate_succ_apply, shape_pushes_node x m (by simp; omega),
      Store.getElem?_shape_push_of_lt _ h]

omit [Inhabited K] in
/-- The run of an allocation, inverted. -/
theorem alloc_inv_node {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st st' : St P K C} (h : exec I (.alloc p len body) st = some st') :
    ∃ st₂, exec I (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) } = some st₂ ∧
      { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - len.eval)
          curW := st₂.curW - len.eval * I.width p } = st' := by
  rw [exec_alloc] at h
  exact Option.map_eq_some_iff.mp h

omit [Inhabited K] in
/-- The run of a scoped allocation, inverted. -/
theorem alloc_inv_skip_node {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st st' : St P K C} (h : exec I (.seq (.alloc p len body) .skip) st = some st') :
    ∃ st₂, exec I (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) } = some st₂ ∧
      { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - len.eval)
          curW := st₂.curW - len.eval * I.width p } = st' :=
  alloc_inv_node ((exec_seq_skip I _ st).symm.trans h)

-- The eight allocations of a split.
set_option maxHeartbeats 4000000 in
/-- A split writes the outcome of `NLAlib.eighStep`'s split, with its precise frame: the values
of `NLAlib.holds_of_exec_eighSplitBlock`, and every cell outside the node's window (`nodeWin`)
unchanged; `NLAlib.holds_of_exec_eighSplitBlock` is its coarse form. -/
theorem holds_of_exec_eighSplitBlock_frame {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR) (p : P)
    (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkp : 0 < kp) (hkpk : kp < k) (kpe : IExp ℕ)
    (hkpe : kpe.eval = kp) (H : EighArenas)
    {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {σ : K} {st st' : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p two.buf two.idx.eval = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval =
      some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (h : exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) kpe Sg
      Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp two sg nsg sq).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let s := eighTapeSample n d lo
    let Qp := deflate M kp Ppm (leadingBlock k (s.2 true))
    let Qm := deflate M (k - kp) Pmm (leadingBlock k (s.2 false))
    (pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) σ) ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
          (M.neg σ)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
      (∀ q b i, ¬ nodeWin H n d lo k (lo + kp) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M s Qp Qm
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨-, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := id hH
  have hk0 : 0 < k := by omega
  have hn2 : 0 < 4 * (n * n) := by have : 0 < n := (by omega); positivity
  have lSg := Store.lt_size_of_read_eq_some (hSg 0 hn2)
  have lPp := Store.lt_size_of_read_eq_some (hPp ⟨0, hk0⟩ ⟨0, hk0⟩ ⟨0, two_pos⟩)
  have lPm := Store.lt_size_of_read_eq_some (hPm ⟨0, hk0⟩ ⟨0, hk0⟩ ⟨0, two_pos⟩)
  have ltwo := Store.lt_size_of_read_eq_some htwo
  have lsg := Store.lt_size_of_read_eq_some hσ
  have lnsg := Store.lt_size_of_read_eq_some hnσ
  have lsq := Store.lt_size_of_read_eq_some hsq
  have hlt : ∀ b ∈ H.handles ++ [Sg, Pp, Pm, two.buf, sg.buf, nsg.buf, sq.buf],
      b < st.store.size := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl)
    exacts [hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSz, hsz hKd, hsz hKp, hsz hLv, lSg, lPp,
      lPm, ltwo, lsg, lnsg, lsq]
  set x : P × Array (Option K) := (p, Array.replicate (2 * (IExp.const n * IExp.const n)).eval none)
    with hx
  obtain ⟨s₁, h₁, e₁⟩ := alloc_inv_skip_node h
  obtain ⟨s₂, h₂, e₂⟩ := alloc_inv_node h₁
  obtain ⟨s₃, h₃, e₃⟩ := alloc_inv_node h₂
  obtain ⟨s₄, h₄, e₄⟩ := alloc_inv_node h₃
  obtain ⟨s₅, h₅, e₅⟩ := alloc_inv_node h₄
  obtain ⟨s₆, h₆, e₆⟩ := alloc_inv_node h₅
  obtain ⟨s₇, h₇, e₇⟩ := alloc_inv_node h₆
  obtain ⟨s₈, h₈, e₈⟩ := alloc_inv_node h₇
  clear h h₁ h₂ h₃ h₄ h₅ h₆ h₇
  subst e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
  have key := split_body_holds hmm hqr p n d lo k kp hk hkp hkpk kpe hkpe H hd st.store.size hlt
    _ _ _ _ _ _ _ _ (by simp <;> omega) (by simp [List.nodup_cons] <;> omega) hbufs
    (fun i j t => (read_pushes_node x 8 (hlt _ (by simp [EighArenas.handles]))).trans (hA i j t))
    (fun i j t => (read_pushes_node x 8 lPp).trans (hPp i j t))
    (fun i j t => (read_pushes_node x 8 lPm).trans (hPm i j t))
    (fun w hw => (read_pushes_node x 8 lSg).trans (hSg w hw))
    ((read_pushes_node x 8 ltwo).trans htwo)
    ((read_pushes_node x 8 lsg).trans hσ) ((read_pushes_node x 8 lnsg).trans hnσ) hcells
    ((read_pushes_node x 8 lsq).trans hsq)
    (h := h₈)
  obtain ⟨⟨v1, v2, v3, v4, v5, v6, v7, v8⟩, hfr, hsh, hps⟩ := key
  have hsz8 : s₈.store.size = st.store.size + 8 := by
    rw [Store.size_eq_of_shape_eq hsh]
    exact size_pushes_node x 8 st.store
  have hpop : ∀ {q : P} {b i : ℕ}, b < st.store.size →
      Store.read (Array.pop^[8] s₈.store) q b i = s₈.store.read q b i :=
    fun hb => read_pops_node 8 (by omega)
  have lQa : H.Qa < st.store.size := hsz hQa
  have lMa : H.Ma < st.store.size := hsz hMa
  refine ⟨⟨fun i j t => (hpop lQa).trans (v1 i j t), fun i j t => (hpop lQa).trans (v2 i j t),
    fun i j t => (hpop lMa).trans (v3 i j t), fun i j t => (hpop lMa).trans (v4 i j t),
    (hpop (hsz hSz)).trans v5, (hpop (hsz hSz)).trans v6, (hpop (hsz hKd)).trans v7,
    (hpop (hsz hKp)).trans v8⟩, fun q b i hW => ?_, ?_, hps⟩
  · by_cases hb : b < st.store.size
    · exact (hpop hb).trans ((hfr q b i hb hW).trans (read_pushes_node x 8 hb))
    · have hsz' : (Array.pop^[8] s₈.store).size = st.store.size := by
        simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Array.size_pop,
          hsz8]
        omega
      exact (show Store.read (Array.pop^[8] s₈.store) q b i = none from
        Store.read_eq_none_of_size_le (by omega)).trans
          (Store.read_eq_none_of_size_le (by omega)).symm
  · change Store.shape (Array.pop (Array.pop (Array.pop (Array.pop (Array.pop (Array.pop
      (Array.pop (Array.pop s₈.store)))))))) = _
    simp only [Store.shape_pop, hsh]
    simp [Store.shape, x]

-- The corrected frame lemma is applied to a large run.
set_option maxHeartbeats 1000000 in
/-- A split writes the outcome of `NLAlib.eighStep`'s split: if the kernels of `I` are the
routines `mmR`, `qrR` on interleaved pairs, a successful run of `NLAlib.eighSplitBlock` at the slot
$lo$ of depth $d$ for a node of size $k$ (with $lo + k \le n$) whose matrix $\mathbf{A}$ is held at
its block of `Ma`, with $0 < k_+ < k$, the projectors $\mathbf{P}_\pm$ at offset $0$ of `Pp`, `Pm`,
the level's Gaussian words in `Sg`, and the cells `two`, `sg`, `nsg`, `sq` (outside the arenas,
`Sg`, `Pp` and `Pm`) holding the machine's $\mathrm{fl}(2)$, $\sigma$, $-\sigma$ and the stored
$\sqrt{1/2}$ (`NLAlib.Computation.ScalarSem.sqrtHalf`, computed once by `NLAlib.eighProg`), ends
with: $\mathbf{Q}_+ =$
`NLAlib.deflate M kp Pp G₊` and $\mathbf{Q}_-$ packed at the node's block of `Qa`, the compressions
of `NLAlib.eighStep` at the blocks of the slots $lo$ and $lo + k_+$ of depth $d + 1$ in `Ma`, the
sizes $k_+$ and $k - k_+$ in their cells of `Sz`, the kind $4$ and $k_+$ in the node's cells of `Kd`
and `Kp`; every other cell of the arenas, and every cell outside them, is unchanged ($M$ = `NLAlib.eighTapeMachine I p mmR qrR`, the test matrices those of the node's
samples, `NLAlib.eighTapeSample`). No printed source.
(Design note §8: the hoist of $\sqrt{1/2}$ to `NLAlib.eighProg` made the split read `sq` only,
so the frame has no exemption and needs no distinctness of `sq`.) -/
theorem holds_of_exec_eighSplitBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n d lo k kp : ℕ) (hk : lo + k ≤ n)
    (hkp : 0 < kp) (hkpk : kp < k) (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ}
    {σ : K} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p two.buf two.idx.eval = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval =
      some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (h : exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.const kp) Sg
      Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp two sg nsg sq).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let s := eighTapeSample n d lo
    let Qp := deflate M kp Ppm (leadingBlock k (s.2 true))
    let Qm := deflate M (k - kp) Pmm (leadingBlock k (s.2 false))
    pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) σ) ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
          (M.neg σ)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      (∀ q b i, ¬ H.LevelCell n d b i → ¬ H.LevelCell n (d + 1) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M s Qp Qm
  have key := holds_of_exec_eighSplitBlock_frame (Sg := Sg) (Pp := Pp) (Pm := Pm)
    (two := two) (sg := sg) (nsg := nsg) (sq := sq) (σ := σ) (st := st) (st' := st') (A := A)
    (Ppm := Ppm) (Pmm := Pmm) hmm hqr p n d lo k kp hk hkp hkpk (.const kp) rfl H hd hH
    hbufs hA hPp hPm hSg htwo hσ hnσ hcells hsq h
  refine ⟨key.1.1, key.1.2.1, key.1.2.2.1, key.1.2.2.2.1, key.1.2.2.2.2.1, key.1.2.2.2.2.2.1,
    key.1.2.2.2.2.2.2.1, key.1.2.2.2.2.2.2.2, fun q b i h0 h1' => key.2.1 q b i ?_,
    key.2.2.1, key.2.2.2⟩
  intro hw
  have hnk : n * lo + n * k ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  have e1 : 2 * (n * n) * d + 2 * n * (lo + k) ≤ 2 * (n * n) * (d + 1) := by nlinarith
  have e2 : 2 * (n * n) * (d + 1) + 2 * n * (lo + k) ≤ 2 * (n * n) * (d + 1 + 1) := by nlinarith
  have e3 : n * (d + 1) + lo + k ≤ n * (d + 1 + 1) := by nlinarith
  have e4 : n * d + lo < n * (d + 1) := by nlinarith
  unfold nodeWin at hw
  unfold EighArenas.LevelCell at h0 h1'
  rcases hw with ⟨rfl, a, b'⟩ | ⟨rfl, a, b'⟩ | ⟨rfl, hi⟩ | ⟨hb, rfl⟩
  · exact h0 (Or.inl ⟨Or.inr (Or.inr rfl), by omega, by omega⟩)
  · exact h1' (Or.inl ⟨Or.inl rfl, by omega, by omega⟩)
  · exact h1' (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by rcases hi with rfl | rfl <;> omega,
      by rcases hi with rfl | rfl <;> omega⟩))
  · refine h0 (Or.inr (Or.inl ⟨?_, by omega, by omega⟩))
    rcases hb with hb | hb
    · exact Or.inr (Or.inr (Or.inl hb))
    · exact Or.inr (Or.inr (Or.inr hb))

end NLAlib
