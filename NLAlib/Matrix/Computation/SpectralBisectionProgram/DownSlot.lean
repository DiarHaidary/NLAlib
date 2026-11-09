/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionNode
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Levels

/-!
# One slot of the downward level of the spectral bisection program

The slot of a node in one level of the downward pass of `NLAlib.eighProg`: the window a slot writes
(its record at depth $d$ and its children at depth $d + 1$), the run of the instructions and loops a
level uses, the equivalence of builders that differ only by the index normal form (a level at an
index variable runs as at the constant of its value), and the slot of a node: its record and its
children are written, and every cell outside its window is kept.

## Main results

* `NLAlib.holds_of_exec_eighSlotBody`: the slot of a node.
* `NLAlib.BuilderEquiv`, `NLAlib.exec_eighNodeBlock_var`, `NLAlib.exec_eighLeafBlock_var`:
  builders with the same index normal form.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! #### Helpers of `NLAlib.holds_of_exec_eighDownLevel` -/

omit [Inhabited K] in
/-- A sequence, inverted. -/
theorem exists_exec_and_exec_of_exec_seq {s t : Stmt P ι ℕ ℕ} {st st' : St P K C}
    (h : exec I (.seq s t) st = some st') : ∃ σ, exec I s st = some σ ∧ exec I t σ = some st' :=
  Option.bind_eq_some_iff.mp ((exec_seq I s t st).symm.trans h)

omit [Inhabited K] in
/-- A successful loop of draws into the cells $w < m$ of one buffer writes the tape values
from the current position, advances the position by $m$ and keeps the shape and every other cell. -/
theorem shape_of_exec_loop_draw {p : P} {dist : Dist} {m : IExp ℕ} {Y : ℕ} {st st' : St P K C}
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
/-- The run of a scoped index binder on a stored size within its bound. -/
private theorem exec_bindIdx_of_readsIdx {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {st st' : St P K C} {k : ℕ}
    (hr : ReadsIdx I.sem st.store p x.buf x.idx.eval k) (hk : k ≤ bound.eval)
    (h : exec I (.seq (.bindIdx p x bound body) .skip) st = some st') :
    exec I (body k) { st with cnt := st.cnt + I.charge (.toNat p) } = some st' := by
  obtain ⟨v, w, hw, hv, -, h⟩ := exists_of_exec_bindIdx h
  unfold ReadsIdx at hr
  rw [hw, Option.bind_some, hv] at hr
  obtain rfl := Option.some_inj.mp hr
  exact h

omit [AddMonoid C] [Inhabited K] in
/-- A size written as a literal reads back as the size. -/
theorem readsIdx_of_read_eq_lit {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {s : Store P K} {p : P} {b i k : ℕ} (hk : k ≤ B)
    (h : s.read p b i = I.sem.lit p ((k : ℕ) : ℚ)) : ReadsIdx I.sem s p b i k := by
  obtain ⟨z, hz, -⟩ := hlit p k hk
  unfold ReadsIdx
  rw [h, hz, Option.bind_some]
  exact hlit.toNat_eq_of_lit_eq_some htn hk hz

omit [AddMonoid C] [Inhabited K] in
/-- A read of an index transfers along equal reads. -/
theorem readsIdx_of_read_eq {sem : ScalarSem P K} {s s' : Store P K} {p : P} {b i k : ℕ}
    (he : s'.read p b i = s.read p b i) (h : ReadsIdx sem s p b i k) : ReadsIdx sem s' p b i k := by
  unfold ReadsIdx at h ⊢
  rw [he]
  exact h

/-- The slots of the children of a node step at slot `lo`: none at a leaf, `lo` for one child,
`lo` and `lo + k₊` for a split. -/
def EighChildSlot {F' : Type*} {k : ℕ} (s : EighStep F' k) (lo j : ℕ) : Prop :=
  match s with
  | .leaf _ _ => False
  | .shift _ _ _ => j = lo
  | .split kp _ _ _ _ _ _ => j = lo ∨ j = lo + kp

/-- The cells the slot `lo` of depth $d$ may write, for a node of size $k$ whose children
start at the slots `cs`. -/
def EighSlotWindow (H : EighArenas) (n d lo k : ℕ) (cs : ℕ → Prop) (b i : ℕ) : Prop :=
  ((b = H.Qa ∨ b = H.Ua) ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * d + 2 * n * (lo + k)) ∨
    (b = H.Ma ∧ 2 * (n * n) * (d + 1) + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * (d + 1) + 2 * n * (lo + k)) ∨
    (b = H.Ea ∧ n * d + lo ≤ i ∧ i < n * d + lo + k) ∨
    ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo) ∨
    (b = H.Sz ∧ ∃ j, lo ≤ j ∧ j < lo + k ∧ cs j ∧ i = n * (d + 1) + j)

/-- The slot `lo` of depth $d$ is done for the node $y$: its record (as
`NLAlib.EighArenas.RecordHolds`) and its children's sizes and matrices are written. -/
def EighSlotDone (H : EighArenas) (sem : ScalarSem P K) (s : Store P K) (p : P)
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

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- Two paths of one length that reach the same slot reach the same node: the nodes of a depth
have disjoint nonempty ranges. -/
theorem eighLoc_eq_of_slot {M : FloatMachine K ℕ ℕ} {N F : ℕ} {R₀ β : K}
    {A : Matrix (Fin N) (Fin N) (K × K)} {ε : K} {ℓ₀ : ℕ} (hN : 1 ≤ N) {a a' : List Bool}
    {lo : ℕ} {y y' : EighNode K} (hlen : a.length = a'.length)
    (h : eighLoc M N F R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
    (h' : eighLoc M N F R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a' = some (lo, y')) : y = y' := by
  by_cases hae : a = a'
  · subst hae
    rw [h] at h'
    exact (Prod.mk.inj (Option.some_inj.mp h')).2
  · have h1 := (eighLoc_bounds hN h).1
    have h2 := (eighLoc_bounds hN h').1
    rcases eighLoc_disjoint hlen hae h h' with h0 | h0 <;> omega

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The range of a node at an earlier slot of the same depth ends before a later node's slot. -/
theorem le_of_eighLoc_lt {M : FloatMachine K ℕ ℕ} {N F : ℕ} {R₀ β : K}
    {A : Matrix (Fin N) (Fin N) (K × K)} {ε : K} {ℓ₀ : ℕ} {a a' : List Bool} {lo lo' : ℕ}
    {y y' : EighNode K} (hlen : a'.length = a.length)
    (h : eighLoc M N F R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
    (h' : eighLoc M N F R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a' = some (lo', y')) (hlt : lo' < lo) :
    lo' + y'.k ≤ lo := by
  have hae : a' ≠ a := by
    rintro rfl
    rw [h] at h'
    have := (Prod.mk.inj (Option.some_inj.mp h')).1
    omega
  rcases eighLoc_disjoint hlen hae h' h with h0 | h0 <;> omega

omit [AddMonoid C] [Inhabited K] in
/-- A split of a node step is proper. -/
private theorem lt_of_eighStep_split {M : FloatMachine K ℕ ℕ} {N F : ℕ} {R₀ β R ε : K} {ℓ k : ℕ}
    {A : Matrix (Fin k) (Fin k) (K × K)} {s : EighSample ℕ ℕ N} {kp : ℕ} {h : kp ≤ k}
    {Qp : Matrix (Fin k) (Fin kp) (K × K)} {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {Ap : Matrix (Fin kp) (Fin kp) (K × K)} {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)}
    {σ : K} (hs : eighStep M N F R₀ β A R ε ℓ s = .split kp h Qp Qm Ap Am σ) : 0 < kp ∧ kp < k := by
  unfold eighStep at hs
  dsimp only at hs
  split_ifs at hs
  cases hs
  omega

omit [AddMonoid C] [Inhabited K] in
/-- A slot of a child is reached by a path of one step. -/
theorem exists_eighLoc_of_eighChildSlot {M : FloatMachine K ℕ ℕ} {n F d lo j : ℕ} {R₀ β : K}
    {y : EighNode K}
    (h : EighChildSlot (eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo j) :
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
/-- A node window covers the cells a node step writes. -/
theorem mem_of_eighSlotWindow {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (h : EighSlotWindow H n d lo k cs b i) : b ∈ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ <;> omega

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The windows of slots with disjoint ranges are disjoint. -/
theorem false_of_eighSlotWindow_of_eighSlotWindow {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k
    lo' k' : ℕ}
    {cs cs' : ℕ → Prop} {b i : ℕ} (hk' : 1 ≤ k') (hlt : lo' + k' ≤ lo)
    (h₁ : EighSlotWindow H n d lo' k' cs' b i)
    (h₂ : EighSlotWindow H n d lo k cs b i) : False := by
  have e1 : 2 * n * (lo' + k') ≤ 2 * n * lo := Nat.mul_le_mul_left _ hlt
  unfold EighSlotWindow at h₁ h₂
  rcases h₁ with ⟨rfl | rfl, h1a, h1b⟩ | ⟨rfl, h1a, h1b⟩ | ⟨rfl, h1a, h1b⟩ | ⟨rfl | rfl, h1a⟩ |
      ⟨rfl, j1, hj1a, hj1b, -, hj1⟩ <;>
    rcases h₂ with ⟨hb2 | hb2, h2a, h2b⟩ | ⟨hb2, h2a, h2b⟩ | ⟨hb2, h2a, h2b⟩ | ⟨hb2 | hb2, h2a⟩ |
      ⟨hb2, j2, hj2a, hj2b, -, hj2⟩ <;>
    first | omega | simp [EighArenas.handles, hb2] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The window of a slot lies in the cells of depths $d$ and $d + 1$. -/
private theorem levelCell_of_eighSlotWindow {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i :
    ℕ}
    (hk1 : 1 ≤ k) (hk : lo + k ≤ n) (h : EighSlotWindow H n d lo k cs b i) :
    H.LevelCell n d b i ∨ H.LevelCell n (d + 1) b i := by
  have e1 : 2 * n * (lo + k) ≤ 2 * (n * n) := by
    rw [show 2 * (n * n) = 2 * n * n by ring]; exact Nat.mul_le_mul_left _ hk
  have e2 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
  have e3 : 2 * (n * n) * (d + 1 + 1) = 2 * (n * n) * (d + 1) + 2 * (n * n) := by ring
  have e4 : n * (d + 1) = n * d + n := by ring
  have e5 : n * (d + 1 + 1) = n * (d + 1) + n := by ring
  unfold EighSlotWindow at h
  unfold EighArenas.LevelCell
  rcases h with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩ | ⟨hb, h1⟩ | ⟨hb, j, hj1, hj2, -, hj⟩
  · exact Or.inl (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩)
  · exact Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩)
  · exact Or.inl (Or.inr (Or.inl ⟨Or.inl hb, by omega, by omega⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl hb), by omega, by omega⟩))

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A cell of the size arena below depth $d + 1$ is in no window of depth $d$. -/
theorem not_eighSlotWindow_sz {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k : ℕ}
    {cs : ℕ → Prop} {i : ℕ} (hi : i < n * (d + 1)) : ¬ EighSlotWindow H n d lo k cs H.Sz i := by
  unfold EighSlotWindow
  intro h
  rcases h with ⟨hb | hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb | hb, -⟩ | ⟨-, j, -, -, -, hj⟩
  all_goals first | omega | simp [EighArenas.handles, hb] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A cell of the node arena below depth $d + 1$ is in no window of depth $d$. -/
theorem not_eighSlotWindow_ma {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k : ℕ}
    {cs : ℕ → Prop} {i : ℕ} (hi : i < 2 * (n * n) * (d + 1)) : ¬ EighSlotWindow H n d lo k cs H.Ma
        i := by
  unfold EighSlotWindow
  intro h
  rcases h with ⟨hb | hb, -⟩ | ⟨-, h1, -⟩ | ⟨hb, -⟩ | ⟨hb | hb, -⟩ | ⟨hb, -⟩
  all_goals first | omega | simp [EighArenas.handles, hb] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A cell of a buffer other than seven arenas is in no window. -/
theorem not_eighSlotWindow_of_not_mem {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hb : b ∉ [H.Qa, H.Ua, H.Ma, H.Ea, H.Kd, H.Kp, H.Sz]) : ¬ EighSlotWindow H n d lo k cs b i :=
  fun h => hb (mem_of_eighSlotWindow h)

omit [AddMonoid C] [Inhabited K] in
/-- The done facts of a slot transfer along equal reads of its window. -/
theorem EighSlotDone.of_read_eq {H : EighArenas} {sem : ScalarSem P K} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F d : ℕ} {R₀ β : K} {lo : ℕ} {y : EighNode K} (hk1 : 1 ≤ y.k)
    (hk : lo + y.k ≤ n)
    (h : ∀ b i, EighSlotWindow H n d lo y.k
      (EighChildSlot (eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo) b i →
        s'.read p b i = s.read p b i)
    (hd : EighSlotDone H sem s p M n F d R₀ β lo y) : EighSlotDone H sem s' p M n F d R₀ β lo y :=
        by
  have hkn : y.k ≤ n := by omega
  have hkk : y.k * y.k ≤ n * y.k := Nat.mul_le_mul_right _ hkn
  have e1 : 2 * n * (lo + y.k) = 2 * n * lo + 2 * (n * y.k) := by ring
  obtain ⟨hr, hc⟩ := hd
  unfold EighSlotDone
  cases hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e =>
    simp only [hs] at hr h
    obtain ⟨h1, h2, h3⟩ := hr
    refine ⟨⟨readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩)))))
      h1, pairLayout_holds_of_read_eq h2 fun i hi1 hi2 => h _ _ (Or.inl ⟨Or.inr rfl, hi1, by
          omega⟩),
      fun i => (h _ _ (Or.inr (Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)))).trans (h3 i)⟩, ?_⟩
    intro b lo' y' hl
    simp [eighLoc, hs] at hl
  | shift b A' σ =>
    simp only [hs] at hr h
    refine ⟨readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩))))) hr,
      ?_⟩
    intro b' lo' y' hl
    obtain ⟨c1, c2⟩ := hc b' lo' y' hl
    simp only [eighLoc, hs] at hl
    split_ifs at hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
    refine ⟨readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl,
      by omega, rfl, rfl⟩))))) c1, pairLayout_holds_of_read_eq c2 fun i hi1 hi2 => h _ _
      (Or.inr (Or.inl ⟨rfl, hi1, by dsimp only at hi2; omega⟩))⟩
  | split kp hkp Qp Qm Ap Am σ =>
    obtain ⟨hkp0, hkpk⟩ := lt_of_eighStep_split hs
    have q1 : y.k * kp + y.k * (y.k - kp) = y.k * y.k := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hkp]
    have q2 : kp * kp ≤ n * y.k := Nat.mul_le_mul (by omega) hkp
    have q3 : (y.k - kp) * (y.k - kp) ≤ n * (y.k - kp) := Nat.mul_le_mul_right _ (by omega)
    have q5 : 2 * n * (lo + kp) = 2 * n * lo + 2 * (n * kp) := by ring
    have q4 : 2 * n * (lo + kp) + 2 * (n * (y.k - kp)) = 2 * n * (lo + y.k) := by
      rw [show lo + y.k = lo + kp + (y.k - kp) by omega]; ring
    simp only [hs] at hr h
    obtain ⟨h1, h2, h3, h4⟩ := hr
    refine ⟨⟨readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩)))))
      h1, readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, rfl⟩))))) h2,
      pairLayout_holds_of_read_eq h3 fun i hi1 hi2 => h _ _ (Or.inl ⟨Or.inl rfl, hi1, by omega⟩),
      pairLayout_holds_of_read_eq h4 fun i hi1 hi2 => h _ _ (Or.inl ⟨Or.inl rfl, by omega, by
          omega⟩)⟩, ?_⟩
    intro b' lo' y' hl
    obtain ⟨c1, c2⟩ := hc b' lo' y' hl
    cases b' <;> simp only [eighLoc, hs, Bool.false_eq_true, if_true, if_false] at hl <;>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
    · refine ⟨readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo + kp,
        by omega, by omega, Or.inr rfl, rfl⟩))))) c1, pairLayout_holds_of_read_eq c2 fun i hi1 hi2
            => h _ _
        (Or.inr (Or.inl ⟨rfl, by omega, by dsimp only at hi2; omega⟩))⟩
    · refine ⟨readsIdx_of_read_eq (h _ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl,
        by omega, Or.inl rfl, rfl⟩))))) c1, pairLayout_holds_of_read_eq c2 fun i hi1 hi2 => h _ _
        (Or.inr (Or.inl ⟨rfl, hi1, by dsimp only at hi2; omega⟩))⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A size cell in a window is a child slot. -/
theorem exists_eq_of_eighSlotWindow_sz {H : EighArenas} (hnd : H.handles.Nodup) {n d lo k : ℕ}
    {cs : ℕ → Prop} {i : ℕ} (h : EighSlotWindow H n d lo k cs H.Sz i) :
    ∃ j, cs j ∧ i = n * (d + 1) + j := by
  rcases h with ⟨hb | hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb | hb, -⟩ | ⟨-, j, -, -, hj, hi⟩
  all_goals first | exact ⟨j, hj, hi⟩ | (exfalso; simp [EighArenas.handles, hb] at hnd)

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The cells outside a window of a leaf are outside its blocks. -/
private theorem bounds_of_eighSlotWindow_leaf {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i :
    ℕ}
    (hk : lo + k ≤ n) (hW : ¬ EighSlotWindow H n d lo k cs b i) :
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
/-- The arenas stay allocated under a change of store of the same shape at the arenas. -/
theorem EighArenas.Shaped.of_shape_eq {H : EighArenas} {s s' : Store P K} {p : P} {n D : ℕ}
    (h : ∀ b ∈ H.handles, s'.shape[b]? = s.shape[b]?) (hH : H.Shaped s p n D) :
    H.Shaped s' p n D := by
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := hH
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := h
  exact ⟨hnd, l1.trans hMa, l2.trans hUa, l3.trans hQa, l4.trans hEa, l5.trans hSz, l6.trans hKd,
    l7.trans hKp, l8.trans hLv⟩

/-- The body of the slot loop of `NLAlib.eighDownLevel` at slot `lo`, with the scratch
buffer `t` and the constants in `c`. -/
def eighSlotBody (p : P) (mm qr : ι)
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
/-- A slot that starts no node reads the size $0$ and is skipped. -/
theorem store_eq_of_exec_eighSlotBody {p : P} {mm qr : ι}
    {n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo : ℕ} {s s' : St P K C}
    (hSz : ReadsIdx I.sem s.store p Sz (n * d + lo) 0)
    (h : exec I (eighSlotBody p mm qr n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c t lo).run s =
      some s') :
    s'.store = s.store ∧ s'.pos = s.pos := by
  unfold eighSlotBody at h
  have h := exec_bindIdx_of_readsIdx (k := 0) (by exact hSz) (Nat.zero_le _) h
  have e := eq_of_exec_loop_of_eval_eq_zero (by change 1 - (1 - 0) = 0; omega) h
  subst e
  exact ⟨rfl, rfl⟩

/-- Two builders run the same under continuations that run the same (used to move index
variables to constants inside a block, piece by piece). -/
def BuilderEquiv (I : Interp P ι K C) (X Y : Builder P ι ℕ ℕ Unit) : Prop :=
  ∀ k k' : Unit → Stmt P ι ℕ ℕ, (∀ st, exec I (k ()) st = exec I (k' ()) st) →
    ∀ st, exec I (ContT.run X k) st = exec I (ContT.run Y k') st

omit [Inhabited K] in
/-- Statements that run the same give builders that run the same. -/
private theorem BuilderEquiv.stmt {S S' : Stmt P ι ℕ ℕ} (h : ∀ st, exec I S st = exec I S' st) :
    BuilderEquiv I (Builder.stmt S) (Builder.stmt S') := by
  intro k k' hk st
  change exec I (.seq S (k ())) st = exec I (.seq S' (k' ())) st
  rw [exec_seq, exec_seq, h st]
  congr 1
  funext s
  exact hk s

omit [Inhabited K] in
/-- Instructions with the same index normal form run the same. -/
theorem BuilderEquiv.ins {i i' : Instr P ℕ ℕ} (h : i.normIdx = i'.normIdx) :
    BuilderEquiv I (Builder.ins i) (Builder.ins i') :=
  BuilderEquiv.stmt fun st => exec_eq_of_normIdx_eq I (by simp only [Stmt.normIdx, h]) st

omit [Inhabited K] in
/-- Kernel calls with the same index normal form run the same. -/
theorem BuilderEquiv.kcall {o : ι} {p : P} {dims dims' : List (IExp ℕ)}
    {ins ins' outs outs' : List (ℕ × IExp ℕ)}
    (h : (Stmt.kcall o p dims ins outs).normIdx = (Stmt.kcall o p dims' ins' outs').normIdx) :
    BuilderEquiv I (Builder.stmt (.kcall o p dims ins outs))
      (Builder.stmt (.kcall o p dims' ins' outs')) :=
  BuilderEquiv.stmt fun st => exec_eq_of_normIdx_eq I h st

omit [Inhabited K] in
/-- The empty builder runs as itself. -/
theorem BuilderEquiv.pure : BuilderEquiv I (pure () : Builder P ι ℕ ℕ Unit) (pure ()) :=
  fun _ _ hk st => hk st

omit [Inhabited K] in
/-- A sequence of builders that run the same runs the same. -/
theorem BuilderEquiv.bind {a a' : Builder P ι ℕ ℕ Unit} {f f' : Unit → Builder P ι ℕ ℕ Unit}
    (ha : BuilderEquiv I a a') (hf : BuilderEquiv I (f ()) (f' ())) :
    BuilderEquiv I (a >>= f) (a' >>= f') := fun k k' hk st =>
  ha (fun u => ContT.run (f u) k) (fun u => ContT.run (f' u) k') (fun st => hf k k' hk st) st

omit [Inhabited K] in
/-- Allocations of the same length, then bodies that run the same, run the same. -/
theorem BuilderEquiv.allocBind {p : P} {len len' : IExp ℕ} {f f' : ℕ → Builder P ι ℕ ℕ Unit}
    (hl : len.eval = len'.eval) (hf : ∀ h, BuilderEquiv I (f h) (f' h)) :
    BuilderEquiv I (Builder.alloc p len >>= f) (Builder.alloc p len' >>= f') := by
  intro k k' hk st
  change exec I (.alloc p len fun h => ContT.run (f h) k) st =
    exec I (.alloc p len' fun h => ContT.run (f' h) k') st
  rw [exec_alloc, exec_alloc, hl, hf _ k k' hk]

omit [Inhabited K] in
/-- Scopes of builders that run the same run the same. -/
theorem BuilderEquiv.scope {b b' : Builder P ι ℕ ℕ Unit} (hb : BuilderEquiv I b b') :
    BuilderEquiv I (Builder.scope b) (Builder.scope b') := by
  intro k k' hk st
  change exec I (.seq b.run (k ())) st = exec I (.seq b'.run (k' ())) st
  rw [exec_seq, exec_seq,
    show exec I b.run st = exec I b'.run st from hb (fun _ => .skip) (fun _ => .skip)
      (fun _ => rfl) st]
  congr 1
  funext s
  exact hk s

omit [Inhabited K] in
/-- Loops of the same length over bodies that run the same run the same. -/
theorem BuilderEquiv.forRange {n n' : IExp ℕ} {body body' : ℕ → Builder P ι ℕ ℕ Unit}
    (hn : n.eval = n'.eval) (hb : ∀ i, BuilderEquiv I (body i) (body' i)) :
    BuilderEquiv I (Builder.forRange n body) (Builder.forRange n' body') := by
  apply BuilderEquiv.stmt
  intro st
  rw [exec_loop, exec_loop, hn]
  congr 1
  funext s i
  exact hb i _ _ (fun _ => rfl) s

omit [Inhabited K] in
/-- Index binders on cells of the same normal form, with bounds of the same value and bodies
that run the same, run the same. -/
theorem BuilderEquiv.bindIdx {p : P} {x x' : Cell ℕ ℕ} {bound bound' : IExp ℕ}
    {body body' : ℕ → Builder P ι ℕ ℕ Unit} (hx : x.normIdx = x'.normIdx)
    (hb : bound.eval = bound'.eval) (h : ∀ i, BuilderEquiv I (body i) (body' i)) :
    BuilderEquiv I (Builder.bindIdx p x bound body) (Builder.bindIdx p x' bound' body') := by
  apply BuilderEquiv.stmt
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
/-- Comparisons of cells of the same normal form, with branches that run the same, run the
same. -/
theorem BuilderEquiv.ite {p : P} {c : CmpOp} {x y x' y' : Cell ℕ ℕ}
    {t e t' e' : Builder P ι ℕ ℕ Unit} (hx : x.normIdx = x'.normIdx) (hy : y.normIdx = y'.normIdx)
    (ht : BuilderEquiv I t t') (he : BuilderEquiv I e e') :
    BuilderEquiv I (Builder.ifThenElse p c x y t e) (Builder.ifThenElse p c x' y' t' e') := by
  apply BuilderEquiv.stmt
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
/-- Named blocks of builders that run the same run the same. -/
theorem BuilderEquiv.named {nm nm' : String} {args args' : List (Arg ℕ ℕ)}
    {b b' : Builder P ι ℕ ℕ Unit} (h : BuilderEquiv I b b') :
    BuilderEquiv I (Builder.named nm args b) (Builder.named nm' args' b') := by
  apply BuilderEquiv.stmt
  intro st
  rw [exec_named, exec_named]
  exact h _ _ (fun _ => rfl) st

omit [Inhabited K] in
/-- The node step at index variables runs as at the constants of their values. -/
private theorem builderEquiv_eighNodeBlock (p : P) (mm qr : ι) (n ℓ₀ F d lo k par Lv Su Sg Ma Qa Sz
    Kd Kp
    c : ℕ) :
    BuilderEquiv I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.var lo)
      (.var k) par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)
    (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩) := by
  -- unfold every block down to the builder primitives, then walk them at reducible transparency
  unfold eighNodeBlock eighChildBlock eighClampBlock eighWhen eighSignBlock newtonSchulzTestBlock
    newtonSchulzStepBlock eighSplitBlock eighDeflateBlock eighCompressBlock
  unfold zhermShift zhermScale zneg ztraceRe zboxTest zhermAvg zcopy zconjTranspose
  unfold zmirror
  repeat' first
    | with_reducible exact BuilderEquiv.pure
    | with_reducible apply BuilderEquiv.ins
    | with_reducible apply BuilderEquiv.kcall
    | with_reducible apply BuilderEquiv.forRange
    | with_reducible apply BuilderEquiv.bindIdx
    | with_reducible apply BuilderEquiv.ite
    | with_reducible apply BuilderEquiv.named
    | with_reducible apply BuilderEquiv.scope
    | with_reducible apply BuilderEquiv.allocBind
    | with_reducible apply BuilderEquiv.bind
    | with_reducible intro _
    | rfl

omit [Inhabited K] in
/-- The node step at index variables runs as at the constants of their values. -/
theorem exec_eighNodeBlock_var (p : P) (mm qr : ι) (n ℓ₀ F d lo k par Lv Su Sg Ma Qa Sz Kd Kp
    c : ℕ) (st : St P K C) :
    exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.var lo) (.var k)
      par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
    exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par Lv Su Sg Ma Qa Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st :=
  builderEquiv_eighNodeBlock p mm qr n ℓ₀ F d lo k par Lv Su Sg Ma Qa Sz Kd Kp c (fun _ => .skip)
    (fun _ => .skip) (fun _ => rfl) st

omit [Inhabited K] in
/-- A leaf at an index variable runs as at the constant of its value. -/
theorem exec_eighLeafBlock_var (p : P) (diag : Bool) (k Ma Ua Ea : ℕ) (mo uo eo : IExp ℕ)
    (kd : Cell ℕ ℕ) (st : St P K C) :
    exec I (eighLeafBlock (ι := ι) p diag (.var k) Ma mo Ua uo Ea eo kd).run st =
      exec I (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd).run st := by
  have hE : BuilderEquiv I (eighLeafBlock (ι := ι) p diag (.var k) Ma mo Ua uo Ea eo kd)
      (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd) := by
    cases diag <;> unfold eighLeafBlock <;>
    repeat' first
      | rfl
      | exact BuilderEquiv.pure
      | apply BuilderEquiv.ins
      | apply BuilderEquiv.kcall
      | apply BuilderEquiv.forRange
      | apply BuilderEquiv.bindIdx
      | apply BuilderEquiv.ite
      | apply BuilderEquiv.named
      | apply BuilderEquiv.scope
      | apply BuilderEquiv.allocBind
      | apply BuilderEquiv.bind
      | intro _
  exact hE (fun _ => .skip) (fun _ => .skip) (fun _ => rfl) st

/-- A leaf of the slot `lo` of depth $d$ (from the size test when `diag`, from the window test
otherwise), whose node step is the leaf of the identity and the diagonal (zeros unless `diag`):
the slot is done, and every cell outside its window is kept, the store shape and the tape
positions too. -/
private theorem done_of_exec_leafBlock {dec : P → K → ℝ} (p : P) (diag : Bool) {n F d lo : ℕ}
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {s s' : St P K C} {R₀ β : K} {y : EighNode K} (hkn : lo + y.k ≤ n)
    (hbufs : H.handles.Nodup)
    (hA : pairLayout.Holds s.store p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A)
    (hstep : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
      (eighTapeSample n d lo) = .leaf ((eighTapeMachine I p mmR qrR).identityMat y.k)
        fun i => if diag then (y.A i i).1 else (eighTapeMachine I p mmR qrR).zero)
    (h : exec I (eighLeafBlock p diag (.var y.k) H.Ma
      (eighBlockOff (.const n) (.const d) (.var lo)) H.Ua
      (eighBlockOff (.const n) (.const d) (.var lo)) H.Ea
      (eighSlotOff (.const n) (.const d) (.var lo))
      ⟨H.Kd, eighSlotOff (.const n) (.const d) (.var lo)⟩).run s = some s') :
    EighSlotDone H I.sem s'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β lo y ∧
      (∀ q b i, ¬ EighSlotWindow H n d lo y.k (EighChildSlot (eighStep (eighTapeMachine I p mmR qrR)
          n F
          R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo) b i →
        s'.store.read q b i = s.store.read q b i) ∧
      s'.store.shape = s.store.shape ∧ s'.pos = s.pos := by
  have dUaMa : H.Ua ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hbufs
  have dEaMa : H.Ea ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hbufs
  have dUaEa : H.Ua ≠ H.Ea := fun h => by simp [EighArenas.handles, h] at hbufs
  have dKdMa : H.Kd ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hbufs
  have dKdUa : H.Kd ≠ H.Ua := fun h => by simp [EighArenas.handles, h] at hbufs
  have dKdEa : H.Kd ≠ H.Ea := fun h => by simp [EighArenas.handles, h] at hbufs
  obtain ⟨hU, hE, hK, hfr, hsh, hps⟩ := holds_of_exec_eighLeafBlock
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform))
    (normal := I.sem.tapeNormal p (I.tape .gaussian)) p diag y.k (A := y.A) (by exact hA)
    (blockDisjoint_of_ne dUaMa) (blockDisjoint_of_ne dEaMa)
        (blockDisjoint_of_ne dUaEa)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨blockDisjoint_of_ne dKdMa, blockDisjoint_of_ne dKdUa,
          blockDisjoint_of_ne dKdEa⟩)
    ((exec_eighLeafBlock_var p diag y.k H.Ma H.Ua H.Ea _ _ _ _ _).symm.trans h)
  refine ⟨?_, fun q b i hW => ?_, hsh, hps⟩
  · unfold EighSlotDone
    rw [hstep]
    refine ⟨⟨readsIdx_of_read_eq_lit (k := 1) hlit htn (by omega) hK, hU, fun i => hE i⟩, ?_⟩
    intro b lo' y' hl
    simp [eighLoc, hstep] at hl
  · obtain ⟨b1, b2, b3⟩ := bounds_of_eighSlotWindow_leaf hkn hW
    exact hfr q b i b1 b2 b3

omit [AddMonoid C] [Inhabited K] in
/-- A slot whose node step is a shift is done once the shifted matrix, its size and the kind are
written. -/
private theorem done_of_shift {dec : P → K → ℝ} {s : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F d lo : ℕ} {R₀ β : K} {H : EighArenas}
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) {y : EighNode K}
    (hkn : lo + y.k ≤ n) {b : Bool} {A' : Matrix (Fin y.k) (Fin y.k) (K × K)} {σ : K}
    (hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) = .shift b A' σ)
    (x1 : pairLayout.Holds s p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) A')
    (x2 : s.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((y.k : ℕ) : ℚ))
    (x3 : s.read p H.Kd (n * d + lo) = I.sem.lit p (((if b then 2 else 3 : ℕ)) : ℚ)) :
    EighSlotDone H I.sem s p M n F d R₀ β lo y := by
  unfold EighSlotDone
  rw [hs]
  refine ⟨readsIdx_of_read_eq_lit hlit htn (by split <;> omega) x3, fun b' lo' y' hl => ?_⟩
  simp only [eighLoc, hs] at hl
  split_ifs at hl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
  exact ⟨readsIdx_of_read_eq_lit (k := y.k) hlit htn (by omega) x2, x1⟩

omit [AddMonoid C] [Inhabited K] in
/-- A slot whose node step is a split is done once the bases, the children's matrices and
sizes, the kind and the split are written. -/
private theorem done_of_split {dec : P → K → ℝ} {s : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F d lo : ℕ} {R₀ β : K} {H : EighArenas}
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) {y : EighNode K}
    (hkn : lo + y.k ≤ n) {kp : ℕ} {hkp : kp ≤ y.k} {Qp : Matrix (Fin y.k) (Fin kp) (K × K)}
    {Qm : Matrix (Fin y.k) (Fin (y.k - kp)) (K × K)} {Ap : Matrix (Fin kp) (Fin kp) (K × K)}
    {Am : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) (K × K)} {σ : K}
    (hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) =
      .split kp hkp Qp Qm Ap Am σ)
    (x1 : pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (x2 : pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (y.k * kp)) Qm)
    (x3 : pairLayout.Holds s p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) Ap)
    (x4 : pairLayout.Holds s p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Am)
    (x5 : s.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ))
    (x6 : s.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((y.k - kp : ℕ) : ℚ))
    (x7 : s.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ))
    (x8 : s.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) :
    EighSlotDone H I.sem s p M n F d R₀ β lo y := by
  unfold EighSlotDone
  rw [hs]
  refine ⟨⟨readsIdx_of_read_eq_lit hlit htn (by omega) x7, readsIdx_of_read_eq_lit hlit htn (by
      omega) x8, x1, x2⟩,
    fun b' lo' y' hl => ?_⟩
  cases b' <;> simp only [eighLoc, hs, Bool.false_eq_true, if_true, if_false] at hl <;>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
  · exact ⟨readsIdx_of_read_eq_lit (k := y.k - kp) hlit htn (by omega) x6, x4⟩
  · exact ⟨readsIdx_of_read_eq_lit (k := kp) hlit htn (by omega) x5, x3⟩

omit [Inhabited K] in
/-- A comparison, then nothing, inverted. -/
private theorem ite_inv {p : P} {c : CmpOp} {x y : Cell ℕ ℕ} {tb eb : Stmt P ι ℕ ℕ}
    {s s' : St P K C} (h : exec I (.seq (.ite p c x y tb eb) .skip) s = some s') :
    ∃ a b r, s.store.read p x.buf x.idx.eval = some a ∧ s.store.read p y.buf y.idx.eval = some b ∧
      I.sem.cmp p c a b = some r ∧
      exec I (if r then tb else eb) { s with cnt := s.cnt + I.charge (.cmp p) } = some s' := by
  rw [exec_seq_skip, exec_ite] at h
  obtain ⟨⟨r, σc⟩, hcs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, ha, hcs⟩ := Option.bind_eq_some_iff.mp hcs
  obtain ⟨b, hb, hcs⟩ := Option.bind_eq_some_iff.mp hcs
  obtain ⟨r', hr', heq⟩ := Option.map_eq_some_iff.mp hcs
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact ⟨a, b, r', ha, hb, hr', by cases r' <;> exact h⟩

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The cells the node step of the slot `lo` may change (as
`NLAlib.holds_of_exec_eighNodeBlock_frame` states them, the second size cell `lo + kp` for a split
of size `kp < k`, `cs` the child slots) lie in the window of the slot. -/
private theorem win_of_nodeBlock {H : EighArenas} {n d lo k : ℕ} {cs : ℕ → Prop} {b i : ℕ}
    (hk1 : 1 ≤ k) {P' : Prop} (hcs : cs lo) (hP : P' → ∃ j, lo < j ∧ j < lo + k ∧ cs j ∧
      i = n * (d + 1) + j)
    (hN : (b = H.Qa ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧
            i < 2 * (n * n) * d + 2 * n * (lo + k)) ∨
          (b = H.Ma ∧ 2 * (n * n) * (d + 1) + 2 * n * lo ≤ i ∧
            i < 2 * (n * n) * (d + 1) + 2 * n * (lo + k)) ∨
          (b = H.Sz ∧ n * (d + 1) + lo ≤ i ∧ i < n * (d + 1) + lo + k ∧
            (i = n * (d + 1) + lo ∨ P')) ∨
          ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo)) :
    EighSlotWindow H n d lo k cs b i := by
  rcases hN with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, -, -, rfl | h3⟩ | ⟨h1, rfl⟩
  · exact Or.inl ⟨Or.inl rfl, h1, h2⟩
  · exact Or.inr (Or.inl ⟨rfl, h1, h2⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, lo, le_rfl, by omega, hcs, rfl⟩)))
  · obtain ⟨j, hj1, hj2, hj, rfl⟩ := hP h3
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, j, hj1.le, hj2, hj, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, rfl⟩)))

/-- The slot of a node of depth $d$: its record and its children are written, and every cell
outside its window and the scratch cell `t[4]` is kept. -/
theorem holds_of_exec_eighSlotBody {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P)
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d D : ℕ)
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
    (h : exec I (eighSlotBody p mm qr n ℓ₀ F d par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd
      H.Kp c t lo).run s = some s') :
    EighSlotDone H I.sem s'.store p (eighTapeMachine I p mmR qrR) n F d R₀ β lo y ∧
      (∀ q b i, ¬ EighSlotWindow H n d lo y.k (EighChildSlot (eighStep (eighTapeMachine I p mmR qrR)
          n F
          R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo)) lo) b i → ¬ (b = t ∧ i = 4) →
        s'.store.read q b i = s.store.read q b i) ∧
      s'.store.shape = s.store.shape ∧ s'.pos = s.pos := by
  have dt : ∀ b ∈ H.handles ++ [par, c], b ≠ t := fun b hb h => ht (h ▸ hb)
  have dtLv := dt H.Lv (by simp [EighArenas.handles])
  have dtMa := dt H.Ma (by simp [EighArenas.handles])
  have dtpar := dt par (by simp)
  have dtc := dt c (by simp)
  -- the binder
  unfold eighSlotBody at h
  have h := exec_bindIdx_of_readsIdx (by exact hSz) (by change y.k ≤ n - lo; omega) h
  have h := exec_loop_one_eq (by change 1 - (1 - y.k) = 1; omega) h
  obtain ⟨σa, ha, hrb⟩ := run_eighWhen_bind h
  rcases Nat.lt_or_ge y.k 2 with hk | hk
  · -- a leaf of size one
    obtain rfl := eq_of_exec_loop_of_eval_eq_zero (by change 1 - (1 - (y.k - 1)) = 0; omega) hrb
    obtain ⟨hd, hfr, hsh, hps⟩ := done_of_exec_leafBlock (F := F) (R₀ := R₀) (β := β) p true
      hlit htn H hkn hH.1 (by exact hA) (by rw [eighStep, if_pos (by omega)]; rfl)
      (exec_loop_one_eq (by change 1 - (1 - (1 - (y.k - 1))) = 1; omega) ha)
    exact ⟨hd, fun q b i hW _ => hfr q b i hW, hsh, hps⟩
  -- a node of size at least two: the window test
  obtain rfl := eq_of_exec_loop_of_eval_eq_zero (by change 1 - (1 - (1 - (y.k - 1))) = 0; omega) ha
  have hY := exec_loop_one_eq (by change 1 - (1 - (y.k - 1)) = 1; omega) hrb
  obtain ⟨a, c', v, s₂, ha', hc', hv, hw2, h⟩ := exists_of_exec_seq_bin hY
  obtain rfl : a = y.ε := Option.some_inj.mp (ha'.symm.trans hε)
  obtain rfl : R₀ = c' := Option.some_inj.mp (hpar.1.symm.trans hc')
  have hw2' : s.store.write p t 4 v = some s₂ := hw2
  have hr2 : ∀ q b i, ¬ (b = t ∧ i = 4) → s₂.read q b i = s.store.read q b i :=
    fun q b i hne => Store.read_of_write_eq_some_of_ne hw2' (not_and_or.mp hne)
  have hr2' : ∀ {b} i, b ≠ t → s₂.read p b i = s.store.read p b i :=
    fun i hb => hr2 _ _ i fun h => hb h.1
  have hsh2 : s₂.shape = s.store.shape := Store.shape_of_write_eq_some hw2'
  change exec I (.seq (.ite _ _ _ _ _ _) .skip) _ = some s' at h
  obtain ⟨x1, x2, r', hx1, hx2, hr', h⟩ := ite_inv h
  obtain rfl : x1 = y.R := Option.some_inj.mp (hx1.symm.trans ((hr2' _ dtLv).trans hR))
  obtain rfl : v = x2 := Option.some_inj.mp ((Store.read_of_write_eq_some hw2').symm.trans hx2)
  have hcmpM : (eighTapeMachine I p mmR qrR).le y.R
      ((eighTapeMachine I p mmR qrR).mul y.ε R₀) = r' := by
    change (I.sem.cmp p .le y.R ((I.sem.bin p .mul y.ε R₀).getD default)).getD false = r'
    rw [hv, Option.getD_some, hr', Option.getD_some]
  have hA2 : pairLayout.Holds s₂ p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A :=
    pairLayout_holds_of_read_eq hA fun i _ _ => hr2' i dtMa
  cases r'
  · -- the node step
    simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨hSu1, hSu2⟩ := hSu hk
    obtain ⟨hSg1, hSg2⟩ := hSg hk
    obtain ⟨hres, hfr, hsh, hps⟩ := holds_of_exec_eighNodeBlock_frame hmm hqr p hflag hcmp n ℓ₀ F
      d lo y.k (fun q m hm => hlit q m (by omega)) htn hkn hk H (A := y.A) (R := y.R) (R₀ := R₀)
      (ε := y.ε) (β := β) (st := { s with store := s₂, cnt := _ })
      (EighArenas.Shaped.of_shape_eq (fun b _ => by change s₂.shape[b]? = _; rw [hsh2]) hH) hbufs
          hA2
      ((hr2' _ dtLv).trans hR) hcmpM ((hr2' _ dtpar).trans hpar.2)
      ((hr2 _ _ _ fun h => hSu2 h.1 h.2).trans hSu1)
      (fun w hw => (hr2' _ hSg2).trans (hSg1 w hw))
      ⟨(hr2' _ dtc).trans hc.1, (hr2' _ dtc).trans hc.2.1, (hr2' _ dtc).trans hc.2.2.1,
        (hr2' _ dtc).trans hc.2.2.2.1, (hr2' _ dtc).trans hc.2.2.2.2⟩
      ((exec_eighNodeBlock_var p mm qr n ℓ₀ F d lo y.k par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp
        c _).symm.trans h)
    rw [← hℓ] at hres hfr
    cases hs : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
      (eighTapeSample n d lo) with
    | leaf U e => rw [hs] at hres; exact hres.elim
    | shift b A' σ =>
      rw [hs] at hres hfr
      obtain ⟨x1, x2, x3⟩ := hres
      exact ⟨done_of_shift hlit htn hkn hs x1 x2 x3, fun q b' i hW ht4 =>
        (hfr q b' i fun hN => hW (win_of_nodeBlock hk1 rfl False.elim hN)).trans
          (hr2 q b' i ht4), hsh.trans hsh2, hps⟩
    | split kp hkp Qp Qm Ap Am σ =>
      obtain ⟨hkp0, hkpk⟩ := lt_of_eighStep_split hs
      rw [hs] at hres hfr
      obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := hres
      exact ⟨done_of_split hlit htn hkn hs x1 x2 x3 x4 x5 x6 x7 x8, fun q b' i hW ht4 =>
        (hfr q b' i fun hN => hW (win_of_nodeBlock hk1 (Or.inl rfl)
          (fun h3 => ⟨lo + kp, by omega, by omega, Or.inr rfl, h3⟩) hN)).trans
          (hr2 q b' i ht4), hsh.trans hsh2, hps⟩
  · -- a leaf by the window test
    simp only [if_true] at h
    obtain ⟨hd, hfr, hsh, hps⟩ := done_of_exec_leafBlock (F := F) (R₀ := R₀) (β := β) p false
      hlit htn H hkn hH.1 (by exact hA2)
      (by rw [eighStep, if_neg (by omega), if_pos hcmpM]; rfl) h
    exact ⟨hd, fun q b i hW ht4 => (hfr q b i hW).trans (hr2 q b i ht4), hsh.trans hsh2, hps⟩

end NLAlib
