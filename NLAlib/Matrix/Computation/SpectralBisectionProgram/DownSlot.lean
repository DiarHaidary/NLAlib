/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionNode

/-!
# One slot of the downward level of the spectral bisection program

The slot of a node in one level of the downward pass of `NLAlib.eighProg`: the window a slot writes
(its record at depth $d$ and its children at depth $d + 1$), the run of the instructions and loops a
level uses, the equivalence of builders that differ only by the index normal form (a level at an
index variable runs as at the constant of its value), and the slot of a node: its record and its
children are written, and every cell outside its window is kept.

## Main results

* `NLAlib.el1_slot_node`: the slot of a node.
* `NLAlib.el1_Equiv`, `NLAlib.el1_node_congr`, `NLAlib.el1_leaf_congr`: builders with the same index
  normal form.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! #### Helpers of `NLAlib.holds_of_exec_eighDownLevel` -/

omit [Inhabited K] in
/-- EL1: a sequence, inverted. -/
theorem el1_seq {s t : Stmt P ι ℕ ℕ} {st st' : St P K C}
    (h : exec I (.seq s t) st = some st') : ∃ σ, exec I s st = some σ ∧ exec I t σ = some st' :=
  Option.bind_eq_some_iff.mp ((exec_seq I s t st).symm.trans h)

omit [Inhabited K] in
/-- EL1: the run of a scoped allocation, inverted. -/
theorem el1_alloc_inv {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
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
          curW := st₂.curW - len.eval * I.width p } = st' := by
  rw [exec_seq_skip, exec_alloc] at h
  exact Option.map_eq_some_iff.mp h

omit [Inhabited K] in
/-- EL1: an index literal, then the rest, inverted. -/
theorem el1_inv_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.litIdx p dst e)) t) s = some s₂) :
    ∃ v s', I.sem.lit p (e.eval : ℚ) = some v ∧ s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

omit [Inhabited K] in
/-- EL1: a binary operation, then the rest, inverted. -/
theorem el1_inv_bin {p : P} {op : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.bin p op dst x y)) t) s = some s₂) :
    ∃ a c v s', s.store.read p x.buf x.idx.eval = some a ∧
      s.store.read p y.buf y.idx.eval = some c ∧ I.sem.bin p op a c = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.bin p op) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, c, hc, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨a, c, v, s', ha, hc, hv, hw, h⟩

omit [Inhabited K] in
/-- EL1: a successful loop of draws into the cells $w < m$ of one buffer writes the tape values
from the current position, advances the position by $m$ and keeps the shape and every other cell. -/
theorem el1_draw_loop {p : P} {dist : Dist} {m : IExp ℕ} {Y : ℕ} {st st' : St P K C}
    (h : exec I (.loop m fun w => (Builder.ins (ι := ι) (.draw p dist ⟨Y, .var w⟩)).run) st =
      some st') :
    st'.store.shape = st.store.shape ∧
      st'.pos = Function.update st.pos dist (st.pos dist + m.eval) ∧
      (∀ w < m.eval, st'.store.read p Y w = some (I.tape dist (st.pos dist + w))) ∧
      ∀ q b i, (b ≠ Y ∨ m.eval ≤ i) → st'.store.read q b i = st.store.read q b i := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      s.pos = Function.update st.pos dist (st.pos dist + w) ∧
      (∀ w' < w, s.store.read p Y w' = some (I.tape dist (st.pos dist + w'))) ∧
      ∀ q b i, (b ≠ Y ∨ w ≤ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, by simp, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w - s₁ s₂ ⟨hsh, hps, hrd, hfr⟩ hex
  change exec I (.seq (.instr (.draw p dist ⟨Y, .var w⟩)) .skip) s₁ = some s₂ at hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨s', hw', rfl⟩, rfl⟩ := hex
  simp only [IExp.eval_var] at hw'
  have hpd : s₁.pos dist = st.pos dist + w := by rw [hps]; simp
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, ?_, fun w' hw => ?_, fun q b i hb => ?_⟩
  · change Function.update s₁.pos dist (s₁.pos dist + 1) = _
    rw [hpd, hps, Function.update_idem, Nat.add_assoc]
  · change s'.read p Y w' = _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with h | rfl
    · rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega)), hrd w' h]
    · rw [Store.read_of_write_eq_some hw', hpd]
  · change s'.read q b i = _
    have hb' : b ≠ Y ∨ w ≤ i := hb.imp_right fun h => by omega
    rw [Store.read_of_write_eq_some_of_ne hw' ?_, hfr q b i hb']
    rcases hb with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)

omit [Inhabited K] in
/-- EL1: the run of a scoped index binder, inverted. -/
private theorem el1_bindIdx_inv {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {st st' : St P K C}
    (h : exec I (.seq (.bindIdx p x bound body) .skip) st = some st') :
    ∃ v w, st.store.read p x.buf x.idx.eval = some w ∧ I.sem.toNat p w = some v ∧
      v ≤ bound.eval ∧
      exec I (body v) { st with cnt := st.cnt + I.charge (.toNat p) } = some st' := by
  rw [exec_seq_skip, exec_bindIdx] at h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  unfold toNatStep at hr
  obtain ⟨w, hw, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hr
  split_ifs at h with hle
  exact ⟨v, w, hw, hv, hle, h⟩

omit [Inhabited K] in
/-- EL1: the run of a scoped index binder on a stored size within its bound. -/
private theorem el1_bindIdx_of_reads {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {st st' : St P K C} {k : ℕ}
    (hr : ReadsIdx I.sem st.store p x.buf x.idx.eval k) (hk : k ≤ bound.eval)
    (h : exec I (.seq (.bindIdx p x bound body) .skip) st = some st') :
    exec I (body k) { st with cnt := st.cnt + I.charge (.toNat p) } = some st' := by
  obtain ⟨v, w, hw, hv, -, h⟩ := el1_bindIdx_inv h
  unfold ReadsIdx at hr
  rw [hw, Option.bind_some, hv] at hr
  obtain rfl := Option.some_inj.mp hr
  exact h

omit [Inhabited K] in
/-- EL1: a loop of no iteration. -/
private theorem el1_loop_zero {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s s' : St P K C}
    (he : e.eval = 0) (h : exec I (.seq (.loop e b) .skip) s = some s') : s' = s := by
  rw [exec_seq_skip, exec_loop, he] at h
  simp only [List.range_zero, List.foldlM_nil] at h
  exact (Option.some_inj.mp h).symm

omit [Inhabited K] in
/-- EL1: a loop of one iteration. -/
private theorem el1_loop_one {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s s' : St P K C}
    (he : e.eval = 1) (h : exec I (.seq (.loop e b) .skip) s = some s') :
    exec I (b 0) s = some s' := by
  rw [exec_seq_skip, exec_loop, he] at h
  simpa [List.range_one] using h

omit [Inhabited K] in
/-- EL1: a guarded block, then the rest. -/
private theorem el1_when_bind {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit}
    {f : Unit → Builder P ι ℕ ℕ Unit} {st st' : St P K C}
    (h : exec I (eighWhen e b >>= f).run st = some st') :
    ∃ σ, exec I (.seq (.loop (1 - (1 - e)) fun _ => b.run) .skip) st = some σ ∧
      exec I (f ()).run σ = some st' := by
  rw [exec_run_bind I (b := eighWhen e b) (fun _ => rfl)] at h
  exact Option.bind_eq_some_iff.mp h

omit [AddMonoid C] [Inhabited K] in
/-- EL1: a size written as a literal reads back as the size. -/
theorem el1_readsIdx {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {s : Store P K} {p : P} {b i k : ℕ} (hk : k ≤ B)
    (h : s.read p b i = I.sem.lit p ((k : ℕ) : ℚ)) : ReadsIdx I.sem s p b i k := by
  obtain ⟨z, hz, -⟩ := hlit p k hk
  unfold ReadsIdx
  rw [h, hz, Option.bind_some]
  exact hlit.toNat_eq_of_lit_eq_some htn hk hz

omit [AddMonoid C] [Inhabited K] in
/-- EL1: a read of an index transfers along equal reads. -/
theorem el1_readsIdx_congr {sem : ScalarSem P K} {s s' : Store P K} {p : P} {b i k : ℕ}
    (he : s'.read p b i = s.read p b i) (h : ReadsIdx sem s p b i k) : ReadsIdx sem s' p b i k := by
  unfold ReadsIdx at h ⊢
  rw [he]
  exact h

omit [Inhabited K] in
/-- EL1: a held block is kept if every read of its words is kept. -/
theorem el1_holds_keep {s s' : Store P K} {p : P} {b off l m : ℕ}
    {Y : Matrix (Fin l) (Fin m) (K × K)} (hY : pairLayout.Holds s p b off Y)
    (h : ∀ i, off ≤ i → i < off + 2 * (l * m) → s'.read p b i = s.read p b i) :
    pairLayout.Holds s' p b off Y :=
  hY.of_forall_read_eq fun i h1 h2 => h i h1 (by
    change i < off + m * l * 2 at h2
    linarith [Nat.mul_comm l m])

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: two blocks of distinct buffers are disjoint. -/
theorem el1_bd_ne {b b' i i' l l' : ℕ} (h : b ≠ b') :
    blockDisjoint (b, i, l) (b', i', l') = true := by
  simp [blockDisjoint, h]

/-- EL1: the slots of the children of a node step at slot `lo`: none at a leaf, `lo` for one child,
`lo` and `lo + k₊` for a split. -/
def el1_childSlot {F' : Type*} {k : ℕ} (s : EighStep F' k) (lo j : ℕ) : Prop :=
  match s with
  | .leaf _ _ => False
  | .shift _ _ _ => j = lo
  | .split kp _ _ _ _ _ _ => j = lo ∨ j = lo + kp

/-- EL1: the cells the slot `lo` of depth $d$ may write, for a node of size $k$ whose children
start at the slots `cs`. -/
def el1_win (H : EighArenas) (n d lo k : ℕ) (cs : ℕ → Prop) (b i : ℕ) : Prop :=
  ((b = H.Qa ∨ b = H.Ua) ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * d + 2 * n * (lo + k)) ∨
    (b = H.Ma ∧ 2 * (n * n) * (d + 1) + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * (d + 1) + 2 * n * (lo + k)) ∨
    (b = H.Ea ∧ n * d + lo ≤ i ∧ i < n * d + lo + k) ∨
    ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo) ∨
    (b = H.Sz ∧ ∃ j, lo ≤ j ∧ j < lo + k ∧ cs j ∧ i = n * (d + 1) + j)

/-- EL1: the slot `lo` of depth $d$ is done for the node $y$: its record (as
`NLAlib.EighArenas.RecordHolds`) and its children's sizes and matrices are written. -/
def el1_done (H : EighArenas) (sem : ScalarSem P K) (s : Store P K) (p : P)
    (M : FloatMachine K ℕ ℕ) (n F d : ℕ) (R₀ β : K) (lo : ℕ) (y : EighNode K) : Prop :=
  (match eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
      | .leaf U e => ReadsIdx sem s p H.Kd (n * d + lo) 1 ∧
          pairLayout.Holds s p H.Ua (2 * (n * n) * d + 2 * n * lo) U ∧
          ∀ i : Fin y.k, s.read p H.Ea (n * d + lo + i) = some (e i)
      | .shift b _ _ => ReadsIdx sem s p H.Kd (n * d + lo) (if b then 2 else 3)
      | .split kp _ Qp Qm _ _ _ => ReadsIdx sem s p H.Kd (n * d + lo) 4 ∧
          ReadsIdx sem s p H.Kp (n * d + lo) kp ∧
          pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
          pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (y.k * kp)) Qm) ∧
    ∀ (b : Bool) (lo' : ℕ) (y' : EighNode K), eighLoc M n F R₀ β d lo y [b] = some (lo', y') →
      ReadsIdx sem s p H.Sz (n * (d + 1) + lo') y'.k ∧
        pairLayout.Holds s p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo') y'.A

omit [AddMonoid C] [Inhabited K] in
/-- EL1: a split of a node step is proper. -/
private theorem el1_split_lt {M : FloatMachine K ℕ ℕ} {N F : ℕ} {R₀ β R ε : K} {ℓ k : ℕ}
    {A : Matrix (Fin k) (Fin k) (K × K)} {s : EighSample ℕ ℕ N} {kp : ℕ} {h : kp ≤ k}
    {Qp : Matrix (Fin k) (Fin kp) (K × K)} {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {Ap : Matrix (Fin kp) (Fin kp) (K × K)} {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)}
    {σ : K} (hs : eighStep M N F R₀ β A R ε ℓ s = .split kp h Qp Qm Ap Am σ) : 0 < kp ∧ kp < k := by
  unfold eighStep at hs
  dsimp only at hs
  split_ifs at hs <;> (try cases hs) <;> omega

omit [AddMonoid C] [Inhabited K] in
/-- EL1: a slot of a child is reached by a path of one step. -/
theorem el1_childSlot_loc {M : FloatMachine K ℕ ℕ} {n F d lo j : ℕ} {R₀ β : K}
    {y : EighNode K}
    (h : el1_childSlot (eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo j) :
    ∃ (b : Bool) (y' : EighNode K), eighLoc M n F R₀ β d lo y [b] = some (j, y') := by
  revert h
  cases hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e => intro h; exact h.elim
  | shift b A' σ =>
    intro h
    change j = lo at h
    subst h
    exact ⟨b, ⟨y.k, A', (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
      y.ℓ + 1⟩, by simp [eighLoc, hs]⟩
  | split kp hkp Qp Qm Ap Am σ =>
    intro h
    change j = lo ∨ j = lo + kp at h
    rcases h with rfl | rfl
    · exact ⟨true, ⟨kp, Ap, (eighNextParams M y.R y.ε y.ℓ).1,
        (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩, by simp [eighLoc, hs]⟩
    · exact ⟨false, ⟨y.k - kp, Am, (eighNextParams M y.R y.ε y.ℓ).1,
        (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩, by simp [eighLoc, hs]⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: a node window covers the cells a node step writes. -/
theorem el1_win_buf {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (h : el1_win H n d lo k cs b i) : b ∈ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ <;> omega

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: the windows of slots with disjoint ranges are disjoint. -/
theorem el1_win_disjoint {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k lo' k' : ℕ}
    {cs cs' : ℕ → Prop} {b i : ℕ} (hk' : 1 ≤ k') (hlt : lo' + k' ≤ lo)
    (h₁ : el1_win H n d lo' k' cs' b i)
    (h₂ : el1_win H n d lo k cs b i) : False := by
  have e1 : 2 * n * (lo' + k') ≤ 2 * n * lo := Nat.mul_le_mul_left _ hlt
  unfold el1_win at h₁ h₂
  rcases h₁ with ⟨rfl | rfl, h1a, h1b⟩ | ⟨rfl, h1a, h1b⟩ | ⟨rfl, h1a, h1b⟩ | ⟨rfl | rfl, h1a⟩ |
      ⟨rfl, j1, hj1a, hj1b, -, hj1⟩ <;>
    rcases h₂ with ⟨hb2 | hb2, h2a, h2b⟩ | ⟨hb2, h2a, h2b⟩ | ⟨hb2, h2a, h2b⟩ | ⟨hb2 | hb2, h2a⟩ |
      ⟨hb2, j2, hj2a, hj2b, -, hj2⟩ <;>
    first | omega | simp [EighArenas.handles, hb2] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: the window of a slot lies in the cells of depths $d$ and $d + 1$. -/
private theorem el1_win_levelCell {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hk1 : 1 ≤ k) (hk : lo + k ≤ n) (h : el1_win H n d lo k cs b i) :
    H.LevelCell n d b i ∨ H.LevelCell n (d + 1) b i := by
  have e1 : 2 * n * (lo + k) ≤ 2 * (n * n) := by
    rw [show 2 * (n * n) = 2 * n * n by ring]; exact Nat.mul_le_mul_left _ hk
  have e2 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
  have e3 : 2 * (n * n) * (d + 1 + 1) = 2 * (n * n) * (d + 1) + 2 * (n * n) := by ring
  have e4 : n * (d + 1) = n * d + n := by ring
  have e5 : n * (d + 1 + 1) = n * (d + 1) + n := by ring
  unfold el1_win at h
  unfold EighArenas.LevelCell
  rcases h with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1⟩ | ⟨hb, j, hj1, hj2, -, hj⟩
  · exact Or.inl (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩)
  · exact Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩)
  · exact Or.inl (Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl hb), by omega, by omega⟩))

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: a cell of the size arena below depth $d + 1$ is in no window of depth $d$. -/
theorem el1_not_win_Sz {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k : ℕ}
    {cs : ℕ → Prop} {i : ℕ} (hi : i < n * (d + 1)) : ¬ el1_win H n d lo k cs H.Sz i := by
  unfold el1_win
  intro h
  rcases h with ⟨hb | hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb | hb, -⟩ | ⟨-, j, -, -, -, hj⟩
  all_goals first | omega | simp [EighArenas.handles, hb] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: a cell of the node arena below depth $d + 1$ is in no window of depth $d$. -/
theorem el1_not_win_Ma {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k : ℕ}
    {cs : ℕ → Prop} {i : ℕ} (hi : i < 2 * (n * n) * (d + 1)) : ¬ el1_win H n d lo k cs H.Ma i := by
  unfold el1_win
  intro h
  rcases h with ⟨hb | hb, -⟩ | ⟨-, h1, -⟩ | ⟨hb, -⟩ | ⟨hb | hb, -⟩ | ⟨hb, -⟩
  all_goals first | omega | simp [EighArenas.handles, hb] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: a cell of a buffer other than seven arenas is in no window. -/
theorem el1_not_win_buf {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hb : b ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz]) : ¬ el1_win H n d lo k cs b i := by
  exact fun h => hb (el1_win_buf h)

omit [AddMonoid C] [Inhabited K] in
/-- EL1: the done facts of a slot transfer along equal reads of its window. -/
theorem el1_done_congr {H : EighArenas} {sem : ScalarSem P K} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F d : ℕ} {R₀ β : K} {lo : ℕ} {y : EighNode K} (hk1 : 1 ≤ y.k)
    (hk : lo + y.k ≤ n)
    (h : ∀ b i, el1_win H n d lo y.k
      (el1_childSlot (eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo) b i →
        s'.read p b i = s.read p b i)
    (hd : el1_done H sem s p M n F d R₀ β lo y) : el1_done H sem s' p M n F d R₀ β lo y := by
  have hkn : y.k ≤ n := by omega
  have hkk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ hkn
  have e1 : 2 * n * (lo + y.k) = 2 * n * lo + 2 * (n * y.k) := by ring
  obtain ⟨hr, hc⟩ := hd
  unfold el1_done
  cases hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e =>
    simp only [hs] at hr h
    obtain ⟨h1, h2, h3⟩ := hr
    refine ⟨⟨el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩)))))
      h1, el1_holds_keep h2 fun i hi1 hi2 => h _ _ (Or.inl ⟨Or.inr rfl, hi1, by omega⟩),
      fun i => (h _ _ (Or.inr (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)))).trans (h3 i)⟩, ?_⟩
    intro b lo' y' hl
    simp [eighLoc, hs] at hl
  | shift b A' σ =>
    simp only [hs] at hr h
    refine ⟨el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩))))) hr,
      ?_⟩
    intro b' lo' y' hl
    obtain ⟨c1, c2⟩ := hc b' lo' y' hl
    simp only [eighLoc, hs] at hl
    by_cases hb : b' = b
    swap
    · simp [hb] at hl
    simp [hb] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine ⟨el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl,
      by omega, rfl, rfl⟩))))) c1, el1_holds_keep c2 fun i hi1 hi2 => h _ _
      (Or.inr (Or.inl ⟨rfl, hi1, by dsimp only at hi2; omega⟩))⟩
  | split kp hkp Qp Qm Ap Am σ =>
    obtain ⟨hkp0, hkpk⟩ := el1_split_lt hs
    have q1 : y.k * kp + y.k * (y.k - kp) = y.k * y.k := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hkp]
    have q2 : kp * kp ≤ n * y.k := Nat.mul_le_mul (by omega) hkp
    have q3 : (y.k - kp) * (y.k - kp) ≤ n * (y.k - kp) := Nat.mul_le_mul_right _ (by omega)
    have q5 : 2 * n * (lo + kp) = 2 * n * lo + 2 * (n * kp) := by ring
    have q4 : 2 * n * (lo + kp) + 2 * (n * (y.k - kp)) = 2 * n * (lo + y.k) := by
      rw [show lo + y.k = lo + kp + (y.k - kp) by omega]; ring
    simp only [hs] at hr h
    obtain ⟨h1, h2, h3, h4⟩ := hr
    refine ⟨⟨el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩)))))
      h1, el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, rfl⟩))))) h2,
      el1_holds_keep h3 fun i hi1 hi2 => h _ _ (Or.inl ⟨Or.inl rfl, hi1, by omega⟩),
      el1_holds_keep h4 fun i hi1 hi2 => h _ _ (Or.inl ⟨Or.inl rfl, by omega, by omega⟩)⟩, ?_⟩
    intro b' lo' y' hl
    obtain ⟨c1, c2⟩ := hc b' lo' y' hl
    simp only [eighLoc, hs] at hl
    cases b'
    · simp at hl
      obtain ⟨rfl, rfl⟩ := hl
      refine ⟨el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo + kp,
        by omega, by omega, Or.inr rfl, rfl⟩))))) c1, el1_holds_keep c2 fun i hi1 hi2 => h _ _
        (Or.inr (Or.inl ⟨rfl, by omega, by dsimp only at hi2; omega⟩))⟩
    · simp at hl
      obtain ⟨rfl, rfl⟩ := hl
      refine ⟨el1_readsIdx_congr (h _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl,
        by omega, Or.inl rfl, rfl⟩))))) c1, el1_holds_keep c2 fun i hi1 hi2 => h _ _
        (Or.inr (Or.inl ⟨rfl, hi1, by dsimp only at hi2; omega⟩))⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: a size cell in a window is a child slot. -/
theorem el1_win_Sz {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k : ℕ}
    {cs : ℕ → Prop} {i : ℕ} (h : el1_win H n d lo k cs H.Sz i) :
    ∃ j, cs j ∧ i = n * (d + 1) + j := by
  rcases h with ⟨hb | hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb | hb, -⟩ | ⟨-, j, -, -, hj, hi⟩
  all_goals first | exact ⟨j, hj, hi⟩ | (exfalso; simp [EighArenas.handles, hb] at hnd)

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EL1: the cells outside a window of a leaf are outside its blocks. -/
private theorem el1_leaf_bd {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hk : lo + k ≤ n) (hW : ¬ el1_win H n d lo k cs b i) :
    blockDisjoint (b, i, 1) (H.Ua, 2 * (n * n) * d + 2 * n * lo, 2 * (k * k)) = true ∧
      blockDisjoint (b, i, 1) (H.Ea, n * d + lo, k) = true ∧
      blockDisjoint (b, i, 1) (H.Kd, n * d + lo, 1) = true := by
  have hkk : k * k ≤ n * k := Nat.mul_le_mul_right _ (by omega)
  have e1 : 2 * n * (lo + k) = 2 * n * lo + 2 * (n * k) := by ring
  have h1 : ¬ ((b = H.Qa ∨ b = H.Ua) ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * d + 2 * n * (lo + k)) := fun h => hW (Or.inl h)
  have h3 : ¬ (b = H.Ea ∧ n * d + lo ≤ i ∧ i < n * d + lo + k) :=
    fun h => hW (Or.inr (Or.inr (Or.inl h)))
  have h4 : ¬ ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo) :=
    fun h => hW (Or.inr (Or.inr (Or.inr (Or.inl h))))
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_⟩ <;> omega

omit [DecidableEq P] [Inhabited K] in
/-- EL1: the arenas stay allocated under a change of store of the same shape at the arenas. -/
theorem el1_shaped_of_eq {H : EighArenas} {s s' : Store P K} {p : P} {n D : ℕ}
    (h : ∀ b ∈ H.handles, s'.shape[b]? = s.shape[b]?) (hH : H.Shaped s p n D) :
    H.Shaped s' p n D := by
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := hH
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := h
  exact ⟨hnd, l1.trans hMa, l2.trans hUa, l3.trans hQa, l4.trans hEa, l5.trans hSz, l6.trans hKd,
    l7.trans hKp, l8.trans hLv⟩

/-- EL1: the body of the slot loop of `NLAlib.eighDownLevel` at slot `lo`, with the scratch
buffer `t` and the constants in `c`. -/
def el1_slotBody (p : P) (mm qr : ι)
    (n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo : ℕ) : Builder P ι ℕ ℕ Unit :=
  Builder.bindIdx p ⟨Sz, eighSlotOff (.const n) (.const d) (.var lo)⟩ (.const n - .var lo)
    fun k => eighWhen (.var k) do
      eighWhen (1 - (.var k - 1))
        (eighLeafBlock p true (.var k) Ma (eighBlockOff (.const n) (.const d) (.var lo)) Ua
          (eighBlockOff (.const n) (.const d) (.var lo)) Ea
          (eighSlotOff (.const n) (.const d) (.var lo))
          ⟨Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩)
      eighWhen (.var k - 1) do
        ins (.bin p .mul ⟨t, 4⟩ ⟨Lv, 2 * .const d + 1⟩ ⟨par, 0⟩)
        ifThenElse p .le ⟨Lv, 2 * .const d⟩ ⟨t, 4⟩
          (eighLeafBlock p false (.var k) Ma (eighBlockOff (.const n) (.const d) (.var lo)) Ua
            (eighBlockOff (.const n) (.const d) (.var lo)) Ea
            (eighSlotOff (.const n) (.const d) (.var lo))
            ⟨Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩)
          (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.var lo) (.var k)
            par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)

omit [Inhabited K] in
/-- EL1: a slot that starts no node reads the size $0$ and is skipped. -/
theorem el1_slot_skip {p : P} {mm qr : ι}
    {n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo : ℕ} {s s' : St P K C}
    (hSz : ReadsIdx I.sem s.store p Sz (n * d + lo) 0)
    (h : exec I (el1_slotBody p mm qr n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo).run s =
      some s') :
    s'.store = s.store ∧ s'.pos = s.pos := by
  unfold el1_slotBody at h
  have h := el1_bindIdx_of_reads (k := 0) (by exact hSz) (Nat.zero_le _) h
  have e := el1_loop_zero (by change 1 - (1 - 0) = 0; omega) h
  subst e
  exact ⟨rfl, rfl⟩

/-- EL1: two builders run the same under continuations that run the same (used to move index
variables to constants inside a block, piece by piece). -/
def el1_Equiv (I : Interp P ι K C) (X Y : Builder P ι ℕ ℕ Unit) : Prop :=
  ∀ k k' : Unit → Stmt P ι ℕ ℕ, (∀ st, exec I (k ()) st = exec I (k' ()) st) →
    ∀ st, exec I (ContT.run X k) st = exec I (ContT.run Y k') st

omit [Inhabited K] in
private theorem el1E_stmt {S S' : Stmt P ι ℕ ℕ} (h : ∀ st, exec I S st = exec I S' st) :
    el1_Equiv I (Builder.stmt S) (Builder.stmt S') := by
  intro k k' hk st
  change exec I (.seq S (k ())) st = exec I (.seq S' (k' ())) st
  rw [exec_seq, exec_seq, h st]
  congr 1
  funext s
  exact hk s

omit [Inhabited K] in
theorem el1E_ins {i i' : Instr P ℕ ℕ} (h : i.normIdx = i'.normIdx) :
    el1_Equiv I (Builder.ins i) (Builder.ins i') :=
  el1E_stmt fun st => exec_eq_of_normIdx_eq I (by simp only [Stmt.normIdx, h]) st

omit [Inhabited K] in
theorem el1E_kcall {o : ι} {p : P} {dims dims' : List (IExp ℕ)}
    {ins ins' outs outs' : List (ℕ × IExp ℕ)}
    (h : (Stmt.kcall o p dims ins outs).normIdx = (Stmt.kcall o p dims' ins' outs').normIdx) :
    el1_Equiv I (Builder.stmt (.kcall o p dims ins outs))
      (Builder.stmt (.kcall o p dims' ins' outs')) :=
  el1E_stmt fun st => exec_eq_of_normIdx_eq I h st

omit [Inhabited K] in
theorem el1E_pure : el1_Equiv I (pure () : Builder P ι ℕ ℕ Unit) (pure ()) :=
  fun _ _ hk st => hk st

omit [Inhabited K] in
theorem el1E_bind {a a' : Builder P ι ℕ ℕ Unit} {f f' : Unit → Builder P ι ℕ ℕ Unit}
    (ha : el1_Equiv I a a') (hf : el1_Equiv I (f ()) (f' ())) :
    el1_Equiv I (a >>= f) (a' >>= f') := fun k k' hk st =>
  ha (fun u => ContT.run (f u) k) (fun u => ContT.run (f' u) k') (fun st => hf k k' hk st) st

omit [Inhabited K] in
theorem el1E_allocBind {p : P} {len len' : IExp ℕ} {f f' : ℕ → Builder P ι ℕ ℕ Unit}
    (hl : len.eval = len'.eval) (hf : ∀ h, el1_Equiv I (f h) (f' h)) :
    el1_Equiv I (Builder.alloc p len >>= f) (Builder.alloc p len' >>= f') := by
  intro k k' hk st
  change exec I (.alloc p len fun h => ContT.run (f h) k) st =
    exec I (.alloc p len' fun h => ContT.run (f' h) k') st
  rw [exec_alloc, exec_alloc, hl, hf _ k k' hk]

omit [Inhabited K] in
theorem el1E_scope {b b' : Builder P ι ℕ ℕ Unit} (hb : el1_Equiv I b b') :
    el1_Equiv I (Builder.scope b) (Builder.scope b') := by
  intro k k' hk st
  change exec I (.seq b.run (k ())) st = exec I (.seq b'.run (k' ())) st
  rw [exec_seq, exec_seq,
    show exec I b.run st = exec I b'.run st from hb (fun _ => .skip) (fun _ => .skip)
      (fun _ => rfl) st]
  congr 1
  funext s
  exact hk s

omit [Inhabited K] in
theorem el1E_forRange {n n' : IExp ℕ} {body body' : ℕ → Builder P ι ℕ ℕ Unit}
    (hn : n.eval = n'.eval) (hb : ∀ i, el1_Equiv I (body i) (body' i)) :
    el1_Equiv I (Builder.forRange n body) (Builder.forRange n' body') := by
  apply el1E_stmt
  intro st
  rw [exec_loop, exec_loop, hn]
  congr 1
  funext s i
  exact hb i _ _ (fun _ => rfl) s

omit [Inhabited K] in
theorem el1E_bindIdx {p : P} {x x' : Cell ℕ ℕ} {bound bound' : IExp ℕ}
    {body body' : ℕ → Builder P ι ℕ ℕ Unit} (hx : x.normIdx = x'.normIdx)
    (hb : bound.eval = bound'.eval) (h : ∀ i, el1_Equiv I (body i) (body' i)) :
    el1_Equiv I (Builder.bindIdx p x bound body) (Builder.bindIdx p x' bound' body') := by
  apply el1E_stmt
  intro st
  have e1 : toNatStep I p x st = toNatStep I p x' st := by
    rw [show toNatStep I p x st = toNatStep I p x.normIdx st from rfl, hx]
    rfl
  rw [exec_bindIdx, exec_bindIdx, e1, hb]
  congr 1
  funext r
  split_ifs
  · exact h _ _ _ (fun _ => rfl) _
  · rfl

omit [Inhabited K] in
theorem el1E_ite {p : P} {c : CmpOp} {x y x' y' : Cell ℕ ℕ}
    {t e t' e' : Builder P ι ℕ ℕ Unit} (hx : x.normIdx = x'.normIdx) (hy : y.normIdx = y'.normIdx)
    (ht : el1_Equiv I t t') (he : el1_Equiv I e e') :
    el1_Equiv I (Builder.ifThenElse p c x y t e) (Builder.ifThenElse p c x' y' t' e') := by
  apply el1E_stmt
  intro st
  have e1 : cmpStep I p c x y st = cmpStep I p c x' y' st := by
    rw [show cmpStep I p c x y st = cmpStep I p c x.normIdx y.normIdx st from rfl, hx, hy]
    rfl
  rw [exec_ite, exec_ite, e1]
  congr 1
  funext r
  split
  · exact ht _ _ (fun _ => rfl) _
  · exact he _ _ (fun _ => rfl) _

omit [Inhabited K] in
theorem el1E_named {nm nm' : String} {args args' : List (Arg ℕ ℕ)}
    {b b' : Builder P ι ℕ ℕ Unit} (h : el1_Equiv I b b') :
    el1_Equiv I (Builder.named nm args b) (Builder.named nm' args' b') := by
  apply el1E_stmt
  intro st
  rw [exec_named, exec_named]
  exact h _ _ (fun _ => rfl) st

set_option maxHeartbeats 4000000 in
-- The walk goes through every statement of the node step.
omit [Inhabited K] in
/-- EL1: the node step at index variables runs as at the constants of their values. -/
private theorem el1_node_equiv (p : P) (mm qr : ι) (n ℓ₀ F d lo k par Lv Su Sg Ma Qa Sz Kd Kp
    c : ℕ) :
    el1_Equiv I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.var lo)
      (.var k) par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)
    (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩) := by
  unfold eighNodeBlock
  repeat' first
    | rfl
    | exact el1E_pure
    | apply el1E_ins
    | apply el1E_kcall
    | apply el1E_forRange
    | apply el1E_bindIdx
    | apply el1E_ite
    | apply el1E_named
    | apply el1E_scope
    | apply el1E_allocBind
    | apply el1E_bind
    | intro _

omit [Inhabited K] in
/-- EL1: the node step at index variables runs as at the constants of their values. -/
theorem el1_node_congr (p : P) (mm qr : ι) (n ℓ₀ F d lo k par Lv Su Sg Ma Qa Sz Kd Kp
    c : ℕ) (st : St P K C) :
    exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.var lo) (.var k)
      par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
    exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st :=
  el1_node_equiv p mm qr n ℓ₀ F d lo k par Lv Su Sg Ma Qa Sz Kd Kp c (fun _ => .skip)
    (fun _ => .skip) (fun _ => rfl) st

omit [Inhabited K] in
/-- EL1: a leaf at an index variable runs as at the constant of its value. -/
theorem el1_leaf_congr (p : P) (diag : Bool) (k Ma Ua Ea : ℕ) (mo uo eo : IExp ℕ)
    (kd : Cell ℕ ℕ) (st : St P K C) :
    exec I (eighLeafBlock (ι := ι) p diag (.var k) Ma mo Ua uo Ea eo kd).run st =
      exec I (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd).run st := by
  have hE : el1_Equiv I (eighLeafBlock (ι := ι) p diag (.var k) Ma mo Ua uo Ea eo kd)
      (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd) := by
    cases diag <;> unfold eighLeafBlock <;>
    repeat' first
      | rfl
      | exact el1E_pure
      | apply el1E_ins
      | apply el1E_kcall
      | apply el1E_forRange
      | apply el1E_bindIdx
      | apply el1E_ite
      | apply el1E_named
      | apply el1E_scope
      | apply el1E_allocBind
      | apply el1E_bind
      | intro _
  exact hE (fun _ => .skip) (fun _ => .skip) (fun _ => rfl) st

set_option maxHeartbeats 1600000 in
-- The slot unfolds the binder, two guards, the window test and the node step.
/-- EL1: the slot of a node of depth $d$: its record and its children are written, and every cell
outside its window and the scratch cell `t[4]` is kept. -/
theorem el1_slot_node {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P)
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d D : ℕ) (hd : d < D)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {par Su Sg c t lo : ℕ} {s s' : St P K C} {R₀ β : K} {y : EighNode K} (hk1 : 1 ≤ y.k)
    (hkn : lo + y.k ≤ n) (hℓ : y.ℓ = ℓ₀ + d) (hH : H.Shaped s.store p n D)
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup) (ht : t ∉ H.handles ++ [par, c])
    (hSz : ReadsIdx I.sem s.store p H.Sz (n * d + lo) y.k)
    (hA : pairLayout.Holds s.store p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A)
    (hR : s.store.read p H.Lv (2 * d) = some y.R)
    (hε : s.store.read p H.Lv (2 * d + 1) = some y.ε)
    (hpar : s.store.read p par 0 = some R₀ ∧ s.store.read p par 2 = some β)
    (hSu : 2 ≤ y.k → s.store.read p Su lo = some (I.tape .uniform (n * d + lo)) ∧
      (Su = t → lo ≠ 4))
    (hSg : 2 ≤ y.k → (∀ w < 4 * (n * n),
      s.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w))) ∧ Sg ≠ t)
    (hc : s.store.read p c 0 = I.sem.lit p 1 ∧ s.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      s.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      s.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      s.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (el1_slotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
      H.Kp c t lo).run s = some s') :
    el1_done H I.sem s'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β lo y ∧
      (∀ q b i, ¬ el1_win H n d lo y.k (el1_childSlot (eighStep (eighTapeMachine I p mmR qrR) n F
          R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo) b i → ¬ (b = t ∧ i = 4) →
        s'.store.read q b i = s.store.read q b i) ∧
      s'.store.shape = s.store.shape ∧ s'.pos = s.pos := by
  have dUaMa : H.Ua ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hbufs
  have dEaMa : H.Ea ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hbufs
  have dUaEa : H.Ua ≠ H.Ea := fun h => by simp [EighArenas.handles, h] at hbufs
  have dKdMa : H.Kd ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hbufs
  have dKdUa : H.Kd ≠ H.Ua := fun h => by simp [EighArenas.handles, h] at hbufs
  have dKdEa : H.Kd ≠ H.Ea := fun h => by simp [EighArenas.handles, h] at hbufs
  have dtLv : H.Lv ≠ t := fun h => ht (by simp [EighArenas.handles, h])
  have dtMa : H.Ma ≠ t := fun h => ht (by simp [EighArenas.handles, h])
  have dtpar : par ≠ t := fun h => ht (by simp [h])
  have dtc : c ≠ t := fun h => ht (by simp [h])
  -- the binder
  unfold el1_slotBody at h
  have h := el1_bindIdx_of_reads (by exact hSz) (by change y.k ≤ n - lo; omega) h
  have h := el1_loop_one (by change 1 - (1 - y.k) = 1; omega) h
  obtain ⟨σa, ha, hrb⟩ := el1_when_bind h
  rcases Nat.lt_or_ge y.k 2 with hk | hk
  · -- a leaf of size one
    have h1 := el1_loop_one (by change 1 - (1 - (1 - (y.k - 1))) = 1; omega) ha
    have e2 := el1_loop_zero (by change 1 - (1 - (y.k - 1)) = 0; omega) hrb
    subst e2
    have h1' := (el1_leaf_congr p true y.k H.Ma H.Ua H.Ea _ _ _ _ _).symm.trans h1
    obtain ⟨hU, hE, hK, hfr, hsh, hps⟩ := holds_of_exec_eighLeafBlock
      (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
      (unif := I.sem.tapeUnif p (I.tape .uniform))
      (normal := I.sem.tapeNormal p (I.tape .gaussian)) p true y.k (A := y.A) (by exact hA)
      (by exact el1_bd_ne dUaMa) (by exact el1_bd_ne dEaMa) (by exact el1_bd_ne dUaEa)
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨el1_bd_ne dKdMa, el1_bd_ne dKdUa, el1_bd_ne dKdEa⟩) h1'
    have hstep : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
        (eighTapeSample n d lo) = .leaf ((eighTapeMachine I p mmR qrR).identityMat y.k)
          fun i => (y.A i i).1 := by
      rw [eighStep, if_pos (by omega)]
    refine ⟨?_, fun q b i hW _ => ?_, hsh, hps⟩
    · unfold el1_done
      rw [hstep]
      refine ⟨⟨el1_readsIdx (k := 1) hlit htn (by omega) hK, hU,
        fun i => (hE i).trans (by simp)⟩, ?_⟩
      intro b lo' y' hl
      simp [eighLoc, hstep] at hl
    · obtain ⟨b1, b2, b3⟩ := el1_leaf_bd hkn hW
      exact hfr q b i b1 b2 b3
  · -- a node of size at least two: the window test
    have e1 := el1_loop_zero (by change 1 - (1 - (1 - (y.k - 1))) = 0; omega) ha
    subst e1
    have hY := el1_loop_one (by change 1 - (1 - (y.k - 1)) = 1; omega) hrb
    obtain ⟨a, c', v, s₂, ha', hc', hv, hw2, h⟩ := el1_inv_bin hY
    have ea : a = y.ε := Option.some_inj.mp (ha'.symm.trans hε)
    have ec : c' = R₀ := Option.some_inj.mp (hc'.symm.trans hpar.1)
    subst a c'
    have hw2' : s.store.write p t 4 v = some s₂ := hw2
    have hr2 : ∀ q b i, ¬ (b = t ∧ i = 4) → s₂.read q b i = s.store.read q b i :=
      fun q b i hne => Store.read_of_write_eq_some_of_ne hw2' (not_and_or.mp hne)
    have hsh2 : s₂.shape = s.store.shape := Store.shape_of_write_eq_some hw2'
    change exec I (.seq (.ite _ _ _ _ _ _) .skip) _ = some s' at h
    rw [exec_seq_skip, exec_ite] at h
    obtain ⟨⟨r, σc⟩, hcs, h⟩ := Option.bind_eq_some_iff.mp h
    unfold cmpStep at hcs
    obtain ⟨x1, hx1, hcs⟩ := Option.bind_eq_some_iff.mp hcs
    obtain ⟨x2, hx2, hcs⟩ := Option.bind_eq_some_iff.mp hcs
    obtain ⟨r', hr', heq⟩ := Option.map_eq_some_iff.mp hcs
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hrr, hσ⟩ := heq
    subst hσ
    subst r
    have ex1 : x1 = y.R :=
      Option.some_inj.mp (hx1.symm.trans ((hr2 _ _ _ fun h => dtLv h.1).trans hR))
    have ex2 : x2 = v := Option.some_inj.mp (hx2.symm.trans (Store.read_of_write_eq_some hw2'))
    subst x1 x2
    have hcmpM : (eighTapeMachine I p mmR qrR).le y.R
        ((eighTapeMachine I p mmR qrR).mul y.ε R₀) = r' := by
      change (I.sem.cmp p .le y.R ((I.sem.bin p .mul y.ε R₀).getD default)).getD false = r'
      rw [hv, Option.getD_some, hr', Option.getD_some]
    have hA2 : pairLayout.Holds s₂ p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A :=
      el1_holds_keep hA fun i _ _ => hr2 _ _ _ fun h => dtMa h.1
    cases r'
    · -- the node step
      simp only [Bool.false_eq_true, if_false] at h
      have hN := (el1_node_congr p mm qr n ℓ₀ F d lo y.k par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp
        c _).symm.trans h
      obtain ⟨hSu1, hSu2⟩ := hSu hk
      obtain ⟨hSg1, hSg2⟩ := hSg hk
      obtain ⟨hres, hfr, hsh, hps⟩ := holds_of_exec_eighNodeBlock_frame hmm hqr p hflag hcmp n ℓ₀ F
        d lo y.k (fun q m hm => hlit q m (by omega)) htn hkn hk H (A := y.A) (R := y.R) (R₀ := R₀)
        (ε := y.ε) (β := β) (st := { s with store := s₂, cnt := _ }) hd
        (el1_shaped_of_eq (fun b _ => by change s₂.shape[b]? = _; rw [hsh2]) hH) hbufs hA2
        ((hr2 _ _ _ fun h => dtLv h.1).trans hR) hcmpM
        ((hr2 _ _ _ fun h => dtpar h.1).trans hpar.2)
        ((hr2 _ _ _ fun h => hSu2 h.1 h.2).trans hSu1)
        (fun w hw => (hr2 _ _ _ fun h => hSg2 h.1).trans (hSg1 w hw))
        ⟨(hr2 _ _ _ fun h => dtc h.1).trans hc.1, (hr2 _ _ _ fun h => dtc h.1).trans hc.2.1,
          (hr2 _ _ _ fun h => dtc h.1).trans hc.2.2.1,
          (hr2 _ _ _ fun h => dtc h.1).trans hc.2.2.2.1,
          (hr2 _ _ _ fun h => dtc h.1).trans hc.2.2.2.2⟩ hN
      rw [← hℓ] at hres hfr
      have hsh' : s'.store.shape = s.store.shape := hsh.trans hsh2
      cases hs : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
        (eighTapeSample n d lo) with
      | leaf U e =>
        rw [hs] at hres
        exact (hres : False).elim
      | shift b A' σ =>
        rw [hs] at hres hfr
        obtain ⟨x1, x2, x3⟩ := hres
        refine ⟨?_, fun q b' i hW ht4 => ?_, hsh', hps⟩
        · unfold el1_done
          rw [hs]
          refine ⟨el1_readsIdx (k := if b then 2 else 3) hlit htn (by split <;> omega) x3, ?_⟩
          intro b' lo' y' hl
          simp only [eighLoc, hs] at hl
          by_cases hb : b' = b
          swap
          · simp [hb] at hl
          simp [hb] at hl
          obtain ⟨rfl, rfl⟩ := hl
          exact ⟨el1_readsIdx (k := y.k) hlit htn (by omega) x2, x1⟩
        · refine (hfr q b' i fun hN => hW ?_).trans (hr2 q b' i ht4)
          rcases hN with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2, h3⟩ | ⟨h1, rfl⟩
          · exact Or.inl ⟨Or.inl rfl, h1, h2⟩
          · exact Or.inr (Or.inl ⟨rfl, h1, h2⟩)
          · rcases h3 with rfl | h3
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl, by omega, rfl, rfl⟩)))
            · exact (h3 : False).elim
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, rfl⟩)))
      | split kp hkp Qp Qm Ap Am σ =>
        obtain ⟨hkp0, hkpk⟩ := el1_split_lt hs
        rw [hs] at hres hfr
        obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := hres
        refine ⟨?_, fun q b' i hW ht4 => ?_, hsh', hps⟩
        · unfold el1_done
          rw [hs]
          refine ⟨⟨el1_readsIdx (k := 4) hlit htn (by omega) x7,
            el1_readsIdx (k := kp) hlit htn (by omega) x8, x1, x2⟩, ?_⟩
          intro b' lo' y' hl
          simp only [eighLoc, hs] at hl
          cases b'
          · simp at hl
            obtain ⟨rfl, rfl⟩ := hl
            exact ⟨el1_readsIdx (k := y.k - kp) hlit htn (by omega) x6, x4⟩
          · simp at hl
            obtain ⟨rfl, rfl⟩ := hl
            exact ⟨el1_readsIdx (k := kp) hlit htn (by omega) x5, x3⟩
        · refine (hfr q b' i fun hN => hW ?_).trans (hr2 q b' i ht4)
          rcases hN with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2, h3⟩ | ⟨h1, rfl⟩
          · exact Or.inl ⟨Or.inl rfl, h1, h2⟩
          · exact Or.inr (Or.inl ⟨rfl, h1, h2⟩)
          · rcases h3 with rfl | h3
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl, by omega, Or.inl rfl,
                rfl⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo + kp, by omega, by omega, Or.inr rfl,
                h3⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, rfl⟩)))
    · -- a leaf by the window test
      simp only [if_true] at h
      have h1' := (el1_leaf_congr p false y.k H.Ma H.Ua H.Ea _ _ _ _ _).symm.trans h
      obtain ⟨hU, hE, hK, hfr, hsh, hps⟩ := holds_of_exec_eighLeafBlock
        (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
        (unif := I.sem.tapeUnif p (I.tape .uniform))
        (normal := I.sem.tapeNormal p (I.tape .gaussian)) p false y.k (A := y.A) (by exact hA2)
        (by exact el1_bd_ne dUaMa) (by exact el1_bd_ne dEaMa) (by exact el1_bd_ne dUaEa)
        (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨el1_bd_ne dKdMa, el1_bd_ne dKdUa, el1_bd_ne dKdEa⟩) h1'
      have hstep : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
          (eighTapeSample n d lo) = .leaf ((eighTapeMachine I p mmR qrR).identityMat y.k)
            fun _ => (eighTapeMachine I p mmR qrR).zero := by
        rw [eighStep, if_neg (by omega), if_pos hcmpM]
      refine ⟨?_, fun q b i hW ht4 => ?_, hsh.trans hsh2, hps⟩
      · unfold el1_done
        rw [hstep]
        refine ⟨⟨el1_readsIdx (k := 1) hlit htn (by omega) hK, hU,
          fun i => (hE i).trans (by simp; rfl)⟩, ?_⟩
        intro b lo' y' hl
        simp [eighLoc, hstep] at hl
      · obtain ⟨b1, b2, b3⟩ := el1_leaf_bd hkn hW
        exact (hfr q b i b1 b2 b3).trans (hr2 q b i ht4)

end NLAlib
