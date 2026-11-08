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

* `NLAlib.exec_eighDownLevel_var`, `NLAlib.exec_eighBottomLevel_of_eval_eq`,
  `NLAlib.exec_eighUpLevel_of_eval_eq`: the levels at index variables.
* `NLAlib.EighArenas.LevelHolds.of_read_eq`, `NLAlib.EighArenas.RecordHolds.of_read_eq`: the
  transfer of the holding predicates.
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
/-- A cell of the arenas lies at one depth only. -/
theorem eq_of_levelCell_of_levelCell {H : EighArenas} (hnd : H.handles.Nodup) {n d e b i : ℕ}
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
/-- A block of at most $k^2$ complex words at the slot of a node of size $k$ lies at its
depth. -/
private theorem lt_of_block_le {n d lo k i : ℕ} (hk : lo + k ≤ n)
    (h1 : 2 * (n * n) * d + 2 * n * lo ≤ i) (h2 : i < 2 * (n * n) * d + 2 * n * lo + 2 * (k * k)) :
    2 * (n * n) * d ≤ i ∧ i < 2 * (n * n) * (d + 1) := by
  have e1 : k * k ≤ n * k := Nat.mul_le_mul_right _ (by omega)
  have e2 : n * lo + n * k ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  constructor <;> nlinarith

omit [AddMonoid C] [Inhabited K] in
/-- The nodes of depth $e$ transfer to a store that reads the same on the node, size and window
cells of depth $e$ and on the size cell $ne$ (the root's when $n = 0$). No printed source. -/
theorem EighArenas.LevelHolds.of_read_eq {H : EighArenas} {s s' : Store P K} {p : P}
    {sem : ScalarSem P K} {M : FloatMachine K ℕ ℕ} {n F ℓ₀ e : ℕ} {R₀ β ε : K}
    {A : Matrix (Fin n) (Fin n) (K × K)}
    (hs : ∀ q b i, (b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) →
      (H.LevelCell n e b i ∨ (b = H.Sz ∧ i = n * e)) → s'.read q b i = s.read q b i)
    (h : H.LevelHolds sem s p M n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ e) :
    H.LevelHolds sem s' p M n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ e := by
  have e4 : n * (e + 1) = n * e + n := by ring
  refine ⟨fun a lo y ha hay => ?_, fun lo hlo hno => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := h.1 a lo y ha hay
    obtain ⟨hb, hb1⟩ := add_k_le_and_of_eighLoc hay
    refine ⟨readsIdx_of_read_eq (hs p _ _ (Or.inr (Or.inl rfl)) ?_) h1,
      pairLayout_holds_of_read_eq h2 fun i h1' h2' => hs p _ _ (Or.inl rfl) ?_⟩
    · by_cases hlo : lo = 0
      · exact Or.inr ⟨rfl, by omega⟩
      · have := hb1 (by omega)
        exact Or.inl (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by omega, by omega⟩))
    · exact Or.inl (Or.inl ⟨Or.inl rfl, lt_of_block_le hb h1' h2'⟩)
  · exact readsIdx_of_read_eq (hs p _ _ (Or.inr (Or.inl rfl))
      (Or.inl (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by omega, by omega⟩)))) (h.2.1 lo hlo hno)
  · rw [hs p _ _ (Or.inr (Or.inr rfl)) (Or.inl (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)))]
    exact h.2.2.1
  · rw [hs p _ _ (Or.inr (Or.inr rfl)) (Or.inl (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩)))]
    exact h.2.2.2

omit [AddMonoid C] [Inhabited K] in
/-- The nodes of depth $d$ of a root of size $n \ge 1$ transfer to a store that reads the same on
the node, size and window cells of depth $d$. No printed source. -/
theorem EighArenas.LevelHolds.of_read_eq_of_one_le {H : EighArenas} {sem : ScalarSem P K}
    {s s' : Store P K} {p : P} {M : FloatMachine K ℕ ℕ} {n F ℓ₀ d : ℕ}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} (hn : 1 ≤ n)
    (hs : ∀ q b i, (b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) → H.LevelCell n d b i →
      s'.read q b i = s.read q b i)
    (h : H.LevelHolds sem s p M n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d) :
    H.LevelHolds sem s' p M n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d := by
  refine EighArenas.LevelHolds.of_read_eq (fun q b i hb hi => hs q b i hb ?_) h
  rcases hi with hi | ⟨rfl, rfl⟩
  · exact hi
  · have : n * (d + 1) = n * d + n := by ring
    exact Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by omega, by omega⟩)

omit [AddMonoid C] [Inhabited K] in
/-- The records of depth $d$ transfer to a store that reads the same on the output, basis,
eigenvalue, kind and split cells of depth $d$. No printed source. -/
theorem EighArenas.RecordHolds.of_read_eq {H : EighArenas} {sem : ScalarSem P K}
    {s s' : Store P K} {p : P} {M : FloatMachine K ℕ ℕ} {n F ℓ₀ d : ℕ}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hs : ∀ q b i, (b = H.Ua ∨ b = H.Qa ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) →
      H.LevelCell n d b i → s'.read q b i = s.read q b i)
    (h : H.RecordHolds sem s p M n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d) :
    H.RecordHolds sem s' p M n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d := by
  have e4 : n * (d + 1) = n * d + n := by ring
  intro a lo y ha hl hk
  have hkn := (add_k_le_and_of_eighLoc hl).1
  have hR : ∀ {b} k, (b = H.Kd ∨ b = H.Kp) → ReadsIdx sem s p b (n * d + lo) k →
      ReadsIdx sem s' p b (n * d + lo) k := fun k hb hr =>
    readsIdx_of_read_eq (hs p _ _ (by rcases hb with h | h <;> simp [h])
      (Or.inr (Or.inl ⟨by rcases hb with h | h <;> simp [h], by omega, by omega⟩))) hr
  have hblk : ∀ {b} {l m : ℕ} {Y : Matrix (Fin l) (Fin m) (K × K)} (off : ℕ),
      (b = H.Ua ∨ b = H.Qa) → off + 2 * (l * m) ≤ 2 * (y.k * y.k) →
      pairLayout.Holds s p b (2 * (n * n) * d + 2 * n * lo + off) Y →
      pairLayout.Holds s' p b (2 * (n * n) * d + 2 * n * lo + off) Y :=
    fun off hb hle hY => pairLayout_holds_of_read_eq hY fun i hi1 hi2 =>
      hs p _ _ (by rcases hb with h | h <;> simp [h])
        (Or.inl ⟨by rcases hb with h | h <;> simp [h], lt_of_block_le hkn (by omega) (by omega)⟩)
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
/-- The outputs of depth $d$ transfer to a store that reads the same on the output and
eigenvalue cells of depth $d$. -/
private theorem EighArenas.OutHolds.of_read_eq {H : EighArenas} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F ℓ₀ D d : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hn : 1 ≤ n)
    (hs : ∀ q b i, (b = H.Ua ∨ b = H.Ea) → H.LevelCell n d b i → s'.read q b i = s.read q b i)
    (h : H.OutHolds s p M n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d) :
    H.OutHolds s' p M n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d := by
  have e4 : n * (d + 1) = n * d + n := by ring
  intro a lo y ha hl
  obtain ⟨-, hkn⟩ := eighLoc_bounds hn hl
  obtain ⟨h1, h2⟩ := h a lo y ha hl
  exact ⟨pairLayout_holds_of_read_eq h1 fun i hi1 hi2 => hs p _ _ (Or.inl rfl)
      (Or.inl ⟨Or.inr (Or.inl rfl), lt_of_block_le hkn hi1 hi2⟩),
    fun i => (hs p _ _ (Or.inr rfl) (Or.inr (Or.inl ⟨Or.inl rfl, by omega,
      by have := i.isLt; omega⟩))).trans (h2 i)⟩

omit [Inhabited K] in
/-- The run of an allocation, inverted. -/
theorem exists_of_exec_alloc {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {st st' : St P K C}
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
/-- A literal, then the rest, inverted. -/
theorem exists_of_exec_seq_lit {p : P} {dst : Cell ℕ ℕ} {q : ℚ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.lit p dst q)) t) s = some s₂) :
    ∃ v s', I.sem.lit p q = some v ∧ s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

omit [Inhabited K] in
/-- A unary operation, then the rest, inverted. -/
theorem exists_of_exec_seq_un {p : P} {op : UnOp} {dst x : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.un p op dst x)) t) s = some s₂) :
    ∃ a v s', s.store.read p x.buf x.idx.eval = some a ∧ I.sem.un p op a = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.un p op) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨a, v, s', ha, hv, hw, h⟩

omit [Inhabited K] in
/-- A copy, then the rest, inverted. -/
theorem exists_of_exec_seq_copy {p : P} {dst src : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.copy p dst src)) t) s = some s₂) :
    ∃ v s', s.store.read p src.buf src.idx.eval = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.copy p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

omit [Inhabited K] in
/-- A successful loop of index literals into the cells $w < m$ of one buffer leaves the
literal in each, every other cell, the shape and the positions unchanged. -/
theorem shape_of_exec_loop_litIdx {p : P} {m e : IExp ℕ} {Y : ℕ} {st st' : St P K C}
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
  obtain ⟨v, s', hv, hw', hex⟩ := exists_of_exec_seq_litIdx hex
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
/-- A successful loop of copies `Y[w] ← X[w]`, $w < m$, between distinct buffers. -/
theorem shape_of_exec_loop_copy {p : P} {m : IExp ℕ} {X Y : ℕ} {st st' : St P K C} (hXY : X ≠ Y)
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

omit [Inhabited K] in
/-- A builder that emits one statement before its continuation runs as itself under continuations
that run the same. -/
private theorem BuilderEquiv.refl_seq {X : Builder P ι ℕ ℕ Unit}
    (hX : ∃ S, ∀ k : Unit → Stmt P ι ℕ ℕ, ContT.run X k = .seq S (k ())) : BuilderEquiv I X X := by
  obtain ⟨S, hX⟩ := hX
  intro k k' hk st
  refine (congrArg (exec I · st) (hX k)).trans
    (Eq.trans ?_ (congrArg (exec I · st) (hX k')).symm)
  rw [exec_seq, exec_seq]
  congr 1
  funext s
  exact hk s

omit [Inhabited K] in
/-- A level of the downward pass at an index variable runs as at the constant of its
value. -/
theorem exec_eighDownLevel_var (p : P) (mm qr : ι)
    (n ℓ₀ F d par Lv Su Sg Ma Ua Qa Ea Sz Kd Kp c : ℕ) (st : St P K C) :
    exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par Lv Su Sg Ma Ua
      Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
    exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par Lv Su Sg Ma
      Ua Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st := by
  -- The whole level has too large a normal form for one `rfl`: walk its statements; the blocks
  -- that do not mention the depth are equal as they stand.
  have hE : BuilderEquiv I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par Lv
      Su Sg Ma Ua Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)
      (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par Lv Su Sg Ma Ua
      Qa Ea Sz Kd Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩) := by
    unfold eighDownLevel
    repeat' first
      | exact BuilderEquiv.pure
      | (with_reducible refine BuilderEquiv.refl_seq ?_); exact ⟨_, fun _ => rfl⟩
      | apply BuilderEquiv.bind
      | apply BuilderEquiv.ins
      | apply BuilderEquiv.kcall
      | apply BuilderEquiv.forRange
      | apply BuilderEquiv.bindIdx
      | apply BuilderEquiv.ite
      | apply BuilderEquiv.named
      | apply BuilderEquiv.scope
      | apply BuilderEquiv.allocBind
      | intro _
      | rfl
  exact hE (fun _ => .skip) (fun _ => .skip) (fun _ => rfl) st

omit [Inhabited K] in
/-- The spent level at an index expression runs as at the constant of its value. -/
theorem exec_eighBottomLevel_of_eval_eq (p : P) (n D : ℕ) (De : IExp ℕ) (hD : De.eval = D)
    (Ua Ea Sz : ℕ) (st : St P K C) :
    exec I (eighBottomLevel (ι := ι) p (.const n) De Ua Ea Sz).run st =
      exec I (eighBottomLevel (ι := ι) p (.const n) (.const D) Ua Ea Sz).run st := by
  subst hD
  exact exec_eq_of_normIdx_eq I (by unfold eighBottomLevel zidentity; rfl) st

omit [Inhabited K] in
/-- A level of the upward pass at an index expression runs as at the constant of its
value. -/
theorem exec_eighUpLevel_of_eval_eq (p : P) (mm : ι) (n d : ℕ) (de : IExp ℕ) (hd : de.eval = d)
    (Lv Ua Qa Ea Sz Kd Kp c : ℕ) (st : St P K C) :
    exec I (eighUpLevel p mm (.const n) de Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩).run st =
      exec I (eighUpLevel p mm (.const n) (.const d) Lv Ua Qa Ea Sz Kd Kp ⟨c, 1⟩).run st := by
  subst hd
  exact exec_eq_of_normIdx_eq I rfl st

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A cell of a depth lies in one of the arenas. -/
theorem mem_handles_of_levelCell {H : EighArenas} {n e b i : ℕ} (h : H.LevelCell n e b i) :
    b ∈ H.handles := by
  unfold EighArenas.LevelCell at h
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ⟨h | h | h, -⟩ | ⟨h | h | h | h, -⟩ | ⟨h, -⟩ <;> simp [h]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The node, size and window arenas are arenas. -/
theorem mem_handles_of_node_arena {H : EighArenas} {b : ℕ} (h : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) :
    b ∈ H.handles := by
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h <;> simp [h]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The record arenas are arenas. -/
theorem mem_handles_of_record_arena {H : EighArenas} {b : ℕ}
    (h : b = H.Ua ∨ b = H.Qa ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) : b ∈ H.handles := by
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with h | h | h | h | h <;> simp [h]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The node, size and window arenas are not record arenas. -/
theorem false_of_node_arena_of_record_arena {H : EighArenas} (hnd : H.handles.Nodup) {b : ℕ}
    (h : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv)
    (h' : b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) : False := by
  rcases h with rfl | rfl | rfl <;> rcases h' with h' | h' | h' | h' | h' <;>
    simp [EighArenas.handles, h'] at hnd

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The node, size and window arenas are not the output or eigenvalue arenas. -/
theorem false_of_node_arena_of_out_arena {H : EighArenas} (hnd : H.handles.Nodup) {b : ℕ}
    (h : b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) (h' : b = H.Ua ∨ b = H.Ea) : False :=
  false_of_node_arena_of_record_arena hnd h (by rcases h' with h' | h' <;> simp [h'])

end NLAlib
