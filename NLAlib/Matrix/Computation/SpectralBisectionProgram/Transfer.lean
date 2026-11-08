/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Levels
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.DownSlot

/-!
# The passes of the spectral bisection program at index variables

Facts the refinement of `NLAlib.eighProg` uses to chain its levels: a cell of the arenas lies at one
depth only, the holding predicates of the arenas transfer between stores that agree on their cells,
the instructions of the initialisation keep them, and each level at an index variable runs as at the
constant of its value.

## Main results

* `NLAlib.ep1_down_congr`, `NLAlib.ep1_bottom_congr`, `NLAlib.ep1_up_congr`: the levels at index
  variables.
* `NLAlib.ep1_lev_tr`, `NLAlib.ep1_rec_tr`: the transfer of the holding predicates.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! ### The program -/

/-! #### Helpers of `NLAlib.holds_of_exec_eighProg` -/

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: a cell of the arenas lies at one depth only. -/
theorem ep1_lc_eq {H : EighArenas} (hnd : H.handles.Nodup) {n d e b i : ℕ}
    (h1 : H.LevelCell n d b i) (h2 : H.LevelCell n e b i) : d = e := by
  have hm : ∀ m x y : ℕ, m * x ≤ i → i < m * (x + 1) → m * y ≤ i → i < m * (y + 1) → x = y := by
    intro m x y h1 h2 h3 h4
    by_contra hxy
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · have := Nat.mul_le_mul_left m (show x + 1 ≤ y by omega); omega
    · have := Nat.mul_le_mul_left m (show y + 1 ≤ x by omega); omega
  simp only [EighArenas.handles, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨_, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _⟩, ⟨_, _, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _⟩,
    ⟨_, _⟩, _, -⟩ := hnd
  unfold EighArenas.LevelCell at h1 h2
  rcases h1 with ⟨hb1, a1, a2⟩ | ⟨hb1, a1, a2⟩ | ⟨hb1, a1⟩ <;>
    rcases h2 with ⟨hb2, c1, c2⟩ | ⟨hb2, c1, c2⟩ | ⟨hb2, c1⟩
  · exact hm _ _ _ a1 a2 c1 c2
  · exfalso
    rcases hb1 with h | h | h <;> rcases hb2 with h' | h' | h' | h' <;>
      exact absurd (h.symm.trans h') ‹_›
  · exfalso
    rcases hb1 with h | h | h <;> exact absurd (h.symm.trans hb2) ‹_›
  · exfalso
    rcases hb2 with h' | h' | h' <;> rcases hb1 with h | h | h | h <;>
      first | exact absurd (h.symm.trans h') ‹_› | exact absurd (h'.symm.trans h) ‹_›
  · exact hm _ _ _ a1 a2 c1 c2
  · exfalso
    rcases hb1 with h | h | h | h <;> exact absurd (h.symm.trans hb2) ‹_›
  · exfalso
    rcases hb2 with h | h | h <;> exact absurd (h.symm.trans hb1) ‹_›
  · exfalso
    rcases hb2 with h | h | h | h <;> exact absurd (h.symm.trans hb1) ‹_›
  · omega

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: a block of at most $k^2$ complex words at the slot of a node of size $k$ lies at its
depth. -/
private theorem ep1_blk {n d lo k i : ℕ} (hk : lo + k ≤ n)
    (h1 : 2 * (n * n) * d + 2 * n * lo ≤ i) (h2 : i < 2 * (n * n) * d + 2 * n * lo + 2 * (k * k)) :
    2 * (n * n) * d ≤ i ∧ i < 2 * (n * n) * (d + 1) := by
  have e1 : k * k ≤ n * k := Nat.mul_le_mul_right _ (by omega)
  have e2 : n * lo + n * k ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  constructor <;> nlinarith

omit [AddMonoid C] [Inhabited K] in
/-- EP1: the nodes of depth $d$ transfer to a store that reads the same on the node, size and
window cells of depth $d$. -/
theorem ep1_lev_tr {H : EighArenas} {sem : ScalarSem P K} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F ℓ₀ d : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hn : 1 ≤ n)
    (hs : ∀ q b i, (b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) → H.LevelCell n d b i →
      s'.read q b i = s.read q b i)
    (h : H.LevelHolds sem s p M n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d) :
    H.LevelHolds sem s' p M n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d := by
  have e4 : n * (d + 1) = n * d + n := by ring
  have hSz : ∀ lo k, lo < n → ReadsIdx sem s p H.Sz (n * d + lo) k →
      ReadsIdx sem s' p H.Sz (n * d + lo) k := fun lo k hlo hr =>
    el1_readsIdx_congr (hs p _ _ (Or.inr (Or.inl rfl))
      (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by omega, by omega⟩))) hr
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun a lo y ha hl => ?_, fun lo hlo hno => hSz lo 0 hlo (h2 lo hlo hno), ?_, ?_⟩
  · obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn hl
    obtain ⟨r1, r2⟩ := h1 a lo y ha hl
    exact ⟨hSz lo _ (by omega) r1, el1_holds_keep r2 fun i hi1 hi2 =>
      hs p _ _ (Or.inl rfl) (Or.inl ⟨Or.inl rfl, ep1_blk hkn hi1 hi2⟩)⟩
  · rw [hs p _ _ (Or.inr (Or.inr rfl)) (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩))]; exact h3
  · rw [hs p _ _ (Or.inr (Or.inr rfl)) (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩))]; exact h4

omit [AddMonoid C] [Inhabited K] in
/-- EP1: the records of depth $d$ transfer to a store that reads the same on the output, basis,
eigenvalue, kind and split cells of depth $d$. -/
theorem ep1_rec_tr {H : EighArenas} {sem : ScalarSem P K} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F ℓ₀ d : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hn : 1 ≤ n)
    (hs : ∀ q b i, (b = H.Ua ∨ b = H.Qa ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) →
      H.LevelCell n d b i → s'.read q b i = s.read q b i)
    (h : H.RecordHolds sem s p M n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d) :
    H.RecordHolds sem s' p M n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d := by
  have e4 : n * (d + 1) = n * d + n := by ring
  intro a lo y ha hl hk
  obtain ⟨-, hkn⟩ := eighLoc_bounds hn hl
  have hR : ∀ {b} k, (b = H.Kd ∨ b = H.Kp) → ReadsIdx sem s p b (n * d + lo) k →
      ReadsIdx sem s' p b (n * d + lo) k := fun k hb hr =>
    el1_readsIdx_congr (hs p _ _ (by rcases hb with h | h <;> simp [h])
      (Or.inr (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩))) hr
  have hblk : ∀ {b} {l m : ℕ} {Y : Matrix (Fin l) (Fin m) (K × K)} (off : ℕ),
      (b = H.Ua ∨ b = H.Qa) → off + 2 * (l * m) ≤ 2 * (y.k * y.k) →
      pairLayout.Holds s p b (2 * (n * n) * d + 2 * n * lo + off) Y →
      pairLayout.Holds s' p b (2 * (n * n) * d + 2 * n * lo + off) Y :=
    fun off hb hle hY => el1_holds_keep hY fun i hi1 hi2 =>
      hs p _ _ (by rcases hb with h | h <;> simp [h])
        (Or.inl ⟨by rcases hb with h | h <;> simp [h], ep1_blk hkn (by omega) (by omega)⟩)
  have this := h a lo y ha hl hk
  revert this
  cases eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e =>
    rintro ⟨h1, h2, h3⟩
    refine ⟨hR 1 (Or.inl rfl) h1, ?_, fun i => (hs p _ _ (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inr (Or.inl ⟨Or.inl rfl, by omega, by have := i.isLt; omega⟩))).trans (h3 i)⟩
    simpa using hblk (Y := U) 0 (Or.inl rfl) (by omega) (by simpa using h2)
  | shift b A' σ => exact hR _ (Or.inl rfl)
  | split kp hkp Qp Qm Ap Am σ =>
    rintro ⟨h1, h2, h3, h4⟩
    have e5 : y.k * kp + y.k * (y.k - kp) = y.k * y.k := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hkp]
    have e6 : y.k * kp ≤ y.k * y.k := Nat.mul_le_mul_left _ hkp
    refine ⟨hR 4 (Or.inl rfl) h1, hR kp (Or.inr rfl) h2, ?_, hblk (Y := Qm) _ (Or.inr rfl)
      (by omega) h4⟩
    simpa using hblk (Y := Qp) 0 (Or.inr rfl) (by omega) (by simpa using h3)

omit [AddMonoid C] [Inhabited K] in
/-- EP1: the outputs of depth $d$ transfer to a store that reads the same on the output and
eigenvalue cells of depth $d$. -/
private theorem ep1_out_tr {H : EighArenas} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F ℓ₀ D d : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hn : 1 ≤ n)
    (hs : ∀ q b i, (b = H.Ua ∨ b = H.Ea) → H.LevelCell n d b i → s'.read q b i = s.read q b i)
    (h : H.OutHolds s p M n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d) :
    H.OutHolds s' p M n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d := by
  have e4 : n * (d + 1) = n * d + n := by ring
  intro a lo y ha hl
  obtain ⟨-, hkn⟩ := eighLoc_bounds hn hl
  obtain ⟨h1, h2⟩ := h a lo y ha hl
  exact ⟨el1_holds_keep h1 fun i hi1 hi2 => hs p _ _ (Or.inl rfl)
      (Or.inl ⟨Or.inr (Or.inl rfl), ep1_blk hkn hi1 hi2⟩),
    fun i => (hs p _ _ (Or.inr rfl) (Or.inr (Or.inl ⟨Or.inl rfl, by omega,
      by have := i.isLt; omega⟩))).trans (h2 i)⟩

omit [Inhabited K] in
/-- EP1: the run of an allocation, inverted. -/
theorem ep1_alloc {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {st st' : St P K C}
    (h : exec I (.alloc p len body) st = some st') :
    ∃ (S st₂ : St P K C), S.store = st.store.push (p, Array.replicate len.eval none) ∧
      S.store.shape[st.store.size]? = some (p, len.eval) ∧
      S.pos = st.pos ∧ exec I (body st.store.size) S = some st₂ ∧
      st'.store = Array.pop st₂.store := by
  rw [exec_alloc] at h
  obtain ⟨st₂, h2, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨_, st₂, ?_, ?_, ?_, h2, rfl⟩
  · rfl
  · exact Store.getElem?_shape_push_size _ _ _
  · rfl

omit [Inhabited K] in
/-- EP1: a literal, then the rest, inverted. -/
theorem ep1_inv_lit {p : P} {dst : Cell ℕ ℕ} {q : ℚ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.lit p dst q)) t) s = some s₂) :
    ∃ v W σ, I.sem.lit p q = some v ∧ s.store.write p dst.buf dst.idx.eval v = some W ∧
      σ.store = W ∧ σ.pos = s.pos ∧ exec I t σ = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  refine ⟨v, s', _, hv, hw, ?_, ?_, h⟩ <;> rfl

omit [Inhabited K] in
/-- EP1: an index literal, then the rest, inverted. -/
theorem ep1_inv_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.litIdx p dst e)) t) s = some s₂) :
    ∃ v W σ, I.sem.lit p (e.eval : ℚ) = some v ∧ s.store.write p dst.buf dst.idx.eval v = some W ∧
      σ.store = W ∧ σ.pos = s.pos ∧ exec I t σ = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  refine ⟨v, s', _, hv, hw, ?_, ?_, h⟩ <;> rfl

omit [Inhabited K] in
/-- EP1: a binary operation, then the rest, inverted. -/
theorem ep1_inv_bin {p : P} {op : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.bin p op dst x y)) t) s = some s₂) :
    ∃ a c v W σ, s.store.read p x.buf x.idx.eval = some a ∧
      s.store.read p y.buf y.idx.eval = some c ∧ I.sem.bin p op a c = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some W ∧ σ.store = W ∧ σ.pos = s.pos ∧
      exec I t σ = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, c, hc, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  refine ⟨a, c, v, s', _, ha, hc, hv, hw, ?_, ?_, h⟩ <;> rfl

omit [Inhabited K] in
/-- EP1: a unary operation, then the rest, inverted. -/
theorem ep1_inv_un {p : P} {op : UnOp} {dst x : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.un p op dst x)) t) s = some s₂) :
    ∃ a v W σ, s.store.read p x.buf x.idx.eval = some a ∧ I.sem.un p op a = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some W ∧ σ.store = W ∧ σ.pos = s.pos ∧
      exec I t σ = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  refine ⟨a, v, s', _, ha, hv, hw, ?_, ?_, h⟩ <;> rfl

omit [Inhabited K] in
/-- EP1: a copy, then the rest, inverted. -/
theorem ep1_inv_copy {p : P} {dst src : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.copy p dst src)) t) s = some s₂) :
    ∃ v W σ, s.store.read p src.buf src.idx.eval = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some W ∧ σ.store = W ∧ σ.pos = s.pos ∧
      exec I t σ = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  refine ⟨v, s', _, hv, hw, ?_, ?_, h⟩ <;> rfl

omit [Inhabited K] in
/-- EP1: a successful loop of index literals into the cells $w < m$ of one buffer leaves the
literal in each, every other cell, the shape and the positions unchanged. -/
theorem ep1_litIdx_loop {p : P} {m e : IExp ℕ} {Y : ℕ} {st st' : St P K C}
    (h : exec I (.loop m fun w => (Builder.ins (ι := ι) (.litIdx p ⟨Y, .var w⟩ e)).run) st =
      some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ w < m.eval, st'.store.read p Y w = I.sem.lit p (e.eval : ℚ)) ∧
      ∀ q b i, (b ≠ Y ∨ m.eval ≤ i) → st'.store.read q b i = st.store.read q b i := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      s.pos = st.pos ∧ (∀ w' < w, s.store.read p Y w' = I.sem.lit p (e.eval : ℚ)) ∧
      ∀ q b i, (b ≠ Y ∨ w ≤ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w - s₁ s₂ ⟨hsh, hps, hrd, hfr⟩ hex
  change exec I (.seq (.instr (.litIdx p ⟨Y, .var w⟩ e)) .skip) s₁ = some s₂ at hex
  obtain ⟨v, s', hv, hw', hex⟩ := el1_inv_litIdx hex
  rw [exec_skip, Option.some_inj] at hex
  subst hex
  simp only [IExp.eval_var] at hw'
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hps, fun w' hw => ?_, fun q b i hb => ?_⟩
  · change s'.read p Y w' = _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with h | rfl
    · rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega)), hrd w' h]
    · rw [Store.read_of_write_eq_some hw', hv]
  · change s'.read q b i = _
    rw [Store.read_of_write_eq_some_of_ne hw' ?_, hfr q b i (hb.imp_right fun h => by omega)]
    rcases hb with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)

omit [Inhabited K] in
/-- EP1: a successful loop of copies `Y[w] ← X[w]`, $w < m$, between distinct buffers. -/
theorem ep1_copy_loop {p : P} {m : IExp ℕ} {X Y : ℕ} {st st' : St P K C} (hXY : X ≠ Y)
    (h : exec I (.loop m fun w => (Builder.ins (ι := ι)
      (.copy p ⟨Y, .var w⟩ ⟨X, .var w⟩)).run) st = some st') :
    st'.store.shape = st.store.shape ∧
      (∀ w < m.eval, st'.store.read p Y w = st.store.read p X w) ∧
      ∀ q b i, (b ≠ Y ∨ m.eval ≤ i) → st'.store.read q b i = st.store.read q b i := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      (∀ w' < w, s.store.read p Y w' = st.store.read p X w') ∧
      ∀ q b i, (b ≠ Y ∨ w ≤ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w - s₁ s₂ ⟨hsh, hrd, hfr⟩ hex
  change exec I (.seq (.instr (.copy p ⟨Y, .var w⟩ ⟨X, .var w⟩)) .skip) s₁ = some s₂ at hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
  simp only [IExp.eval_var] at hw' hv
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, fun w' hw => ?_, fun q b i hb => ?_⟩
  · change s'.read p Y w' = _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with h | rfl
    · rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr (by omega)), hrd w' h]
    · rw [Store.read_of_write_eq_some hw', ← hv, hfr _ _ _ (Or.inl hXY)]
  · change s'.read q b i = _
    rw [Store.read_of_write_eq_some_of_ne hw' ?_, hfr q b i (hb.imp_right fun h => by omega)]
    rcases hb with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)

set_option maxHeartbeats 8000000 in
-- The walk goes through every statement of the level, the node step included.
omit [Inhabited K] in
/-- EP1: a level of the downward pass at an index variable runs as at the constant of its
value. -/
theorem ep1_down_congr (p : P) (mm qr : ι)
    (n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c : ℕ) (st : St P K C) :
    exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par Lv Su Sg Ma Ua
      Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
    exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par Lv Su Sg Ma
      Ua Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st := by
  have hE : el1_Equiv I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par Lv
      Su Sg Ma Ua Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)
      (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par Lv Su Sg Ma Ua
      Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩) := by
    unfold eighDownLevel
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

omit [Inhabited K] in
/-- EP1: the spent level at an index expression runs as at the constant of its value. -/
theorem ep1_bottom_congr (p : P) (n D : ℕ) (De : IExp ℕ) (hD : De.eval = D)
    (Ua Ea Sz : ℕ) (st : St P K C) :
    exec I (eighBottomLevel (ι := ι) p (.const n) De Ua Ea Sz).run st =
      exec I (eighBottomLevel (ι := ι) p (.const n) (.const D) Ua Ea Sz).run st := by
  subst hD
  have hE : el1_Equiv I (eighBottomLevel (ι := ι) p (.const n) De Ua Ea Sz)
      (eighBottomLevel (ι := ι) p (.const n) (.const De.eval) Ua Ea Sz) := by
    unfold eighBottomLevel
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
-- The walk goes through every statement of the level.
omit [Inhabited K] in
/-- EP1: a level of the upward pass at an index expression runs as at the constant of its
value. -/
theorem ep1_up_congr (p : P) (mm : ι) (n d : ℕ) (de : IExp ℕ) (hd : de.eval = d)
    (Lv Ua Qa Ea Sz Kd Kp c : ℕ) (st : St P K C) :
    exec I (eighUpLevel p mm (.const n) de Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩).run st =
      exec I (eighUpLevel p mm (.const n) (.const d) Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩).run st := by
  subst hd
  have hE : el1_Equiv I (eighUpLevel p mm (.const n) de Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩)
      (eighUpLevel p mm (.const n) (.const de.eval) Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩) := by
    unfold eighUpLevel
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

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: a cell of a depth lies in one of the arenas. -/
theorem ep1_lc_mem {H : EighArenas} {n e b i : ℕ} (h : H.LevelCell n e b i) :
    b ∈ H.handles := by
  unfold EighArenas.LevelCell at h
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ⟨h | h | h, -⟩ | ⟨h | h | h | h, -⟩ | ⟨h, -⟩ <;> simp [h]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the node, size and window arenas are arenas. -/
theorem ep1_mem3 {H : EighArenas} {b : ℕ} (h : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) :
    b ∈ H.handles := by
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h <;> simp [h]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the record arenas are arenas. -/
theorem ep1_mem5 {H : EighArenas} {b : ℕ}
    (h : b = H.Ua ∨ b = H.Qa ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) : b ∈ H.handles := by
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h | h | h <;> simp [h]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the node, size and window arenas are not record arenas. -/
theorem ep1_disj {H : EighArenas} (hnd : H.handles.Nodup) {b : ℕ}
    (h : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv)
    (h' : b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) : False := by
  rcases h with rfl | rfl | rfl <;> rcases h' with h' | h' | h' | h' | h' <;>
    simp [EighArenas.handles, h'] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- EP1: the node, size and window arenas are not the output or eigenvalue arenas. -/
theorem ep1_disj' {H : EighArenas} (hnd : H.handles.Nodup) {b : ℕ}
    (h : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) (h' : b = H.Ua ∨ b = H.Ea) : False :=
  ep1_disj hnd h (by rcases h' with h' | h' <;> simp [h'])

end NLAlib
