/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exec

/-!
# Successful runs: loop invariants, the unrolled `whileFuel`, inverted instructions

The refinement of a program to a shallow definition reads the value of a *successful* run, so it
needs the invariant of a loop in the direction "the run succeeded, so the invariant holds at the
end", the unrolling of `whileFuel` by one test, and the inversion of a successful scalar
instruction followed by the rest of a program (what it read, computed and wrote).

## Main results

* `NLAlib.Computation.forall_of_exec_loop_eq_some`: the invariant of a successful loop.
* `NLAlib.Computation.exec_whileFuel_of_eval_eq_zero`,
  `NLAlib.Computation.exec_whileFuel_of_eval_eq_succ`: `whileFuel` unrolled.
* `NLAlib.Computation.exists_of_exec_seq_lit`, `NLAlib.Computation.exists_of_exec_seq_litIdx`,
  `NLAlib.Computation.exists_of_exec_seq_bin`, `NLAlib.Computation.exists_of_exec_seq_un`,
  `NLAlib.Computation.exists_of_exec_seq_copy`: a successful instruction, then the rest, inverted.
* `NLAlib.Computation.read_of_exec_loop_lit`: a successful loop of literals into one buffer.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C)

/-- The invariant of a successful loop: if `R 0` holds at the start and, for each index `i`
below the bound, every successful run of the body from a state satisfying `R i` ends in a state
satisfying `R (i + 1)`, then a successful run of the loop ends in a state satisfying `R n`. No
printed source. -/
theorem forall_of_exec_loop_eq_some {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st st' : St P K C} (R : ℕ → St P K C → Prop) (h0 : R 0 st)
    (hstep : ∀ i < n.eval, ∀ st₁ st₂, R i st₁ → exec I (body i) st₁ = some st₂ → R (i + 1) st₂)
    (h : exec I (.loop n body) st = some st') : R n.eval st' := by
  rw [exec_loop] at h
  generalize n.eval = m at hstep h ⊢
  induction m generalizing st' with
  | zero =>
    simp only [List.range_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact h0
  | succ m ih =>
    rw [List.range_succ, List.foldlM_append] at h
    obtain ⟨s, hs, h'⟩ := Option.bind_eq_some_iff.mp h
    have h2 : exec I (body m) s = some st' := by simpa [List.foldlM_cons] using h'
    exact hstep m (Nat.lt_succ_self m) s st' (ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi)) hs) h2

/-- `whileFuel` with no fuel fails: a `whileFuel` loop whose fuel evaluates to $0$ fails (the
test is never found false). No printed source. -/
theorem exec_whileFuel_of_eval_eq_zero {fuel : IExp ℕ} (hf : fuel.eval = 0) (p : P) (c : CmpOp)
    (x y : Cell ℕ ℕ) (body : Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.whileFuel fuel p c x y body) st = none := by
  rw [exec, hf, List.range_zero, List.foldlM_nil]
  simp only [Option.pure_def, Option.bind_some, if_true]

/-- A fold whose step fixes every state with flag `false` leaves such a state unchanged. -/
private theorem foldlM_false_eq {α : Type} (f : α × Bool → ℕ → Option (α × Bool))
    (hf : ∀ s i, f (s, false) i = some (s, false)) (a : α) (l : List ℕ) :
    l.foldlM f (a, false) = some (a, false) := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldlM_cons, hf]; exact ih

/-- `whileFuel` unrolled by one test: with fuel $j + 1$, the loop compares; if the comparison
is true it runs the body and continues with fuel $j$, and otherwise it stops in the charged
state. No printed source. -/
theorem exec_whileFuel_of_eval_eq_succ {fuel : IExp ℕ} {j : ℕ} (hf : fuel.eval = j + 1) (p : P)
    (c : CmpOp) (x y : Cell ℕ ℕ) (body : Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.whileFuel fuel p c x y body) st = (cmpStep I p c x y st).bind fun r =>
      if r.1 then (exec I body r.2).bind (exec I (.whileFuel (.const j) p c x y body))
      else some r.2 := by
  rw [exec, hf, List.range_succ_eq_map, List.foldlM_cons]
  simp only [List.foldlM_map, ↓reduceIte]
  rcases hc : cmpStep I p c x y st with _ | ⟨b, s⟩
  · simp
  · cases b
    · simp only [Option.bind_some, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind]
      rw [foldlM_false_eq]
      · rfl
      · intro s i
        simp
    · simp only [Option.bind_some, ↓reduceIte, Option.bind_eq_bind]
      rcases h : exec I body s with _ | s' <;> simp [exec, IExp.eval_const]

/-! ### Inverted instructions -/

section Inversion

variable {I}

/-- A successful literal, then the rest, inverted: the literal's value, its write to the
destination and the successful run of the rest from the charged state. No printed source. -/
theorem exists_of_exec_seq_lit {p : P} {dst : Cell ℕ ℕ} {q : ℚ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.lit p dst q)) t) s = some s₂) :
    ∃ v s', I.sem.lit p q = some v ∧ s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

/-- A successful index literal, then the rest, inverted: the literal's value, its write to the
destination and the successful run of the rest from the charged state. No printed source. -/
theorem exists_of_exec_seq_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.litIdx p dst e)) t) s = some s₂) :
    ∃ v s', I.sem.lit p (e.eval : ℚ) = some v ∧ s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

/-- A successful binary operation, then the rest, inverted: the two operands read, the value of
the operation, its write to the destination and the successful run of the rest from the charged
state. No printed source. -/
theorem exists_of_exec_seq_bin {p : P} {op : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.bin p op dst x y)) t) s = some s₂) :
    ∃ a c v s', s.store.read p x.buf x.idx.eval = some a ∧
      s.store.read p y.buf y.idx.eval = some c ∧ I.sem.bin p op a c = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.bin p op) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, c, hc, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨a, c, v, s', ha, hc, hv, hw, h⟩

/-- A successful unary operation, then the rest, inverted: the operand read, the value of the
operation, its write to the destination and the successful run of the rest from the charged
state. No printed source. -/
theorem exists_of_exec_seq_un {p : P} {op : UnOp} {dst x : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.un p op dst x)) t) s = some s₂) :
    ∃ a v s', s.store.read p x.buf x.idx.eval = some a ∧ I.sem.un p op a = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.un p op) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨a, v, s', ha, hv, hw, h⟩

/-- A successful copy, then the rest, inverted: the value read at the source, its write to the
destination and the successful run of the rest from the charged state. No printed source. -/
theorem exists_of_exec_seq_copy {p : P} {dst src : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.copy p dst src)) t) s = some s₂) :
    ∃ v s', s.store.read p src.buf src.idx.eval = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.copy p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

/-- A successful loop of literals $c$ into the cells `f w`, $w < m$, of one buffer `Y` keeps the
store shape and the tape positions, leaves the literal's value in every written cell and every
other cell unchanged. No printed source. -/
theorem read_of_exec_loop_lit {p : P} {m : IExp ℕ} {Y : ℕ} {f : ℕ → IExp ℕ} {c : ℚ}
    {st st' : St P K C}
    (h : exec I (.loop m fun w => .seq (.instr (.lit p ⟨Y, f w⟩ c)) .skip) st = some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ w < m.eval, ∃ z, I.sem.lit p c = some z ∧ st'.store.read p Y (f w).eval = some z) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w < m.eval, (f w).eval ≠ i) →
        st'.store.read q b i = st.store.read q b i := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      s.pos = st.pos ∧
      (∀ w' < w, ∃ z, I.sem.lit p c = some z ∧ s.store.read p Y (f w').eval = some z) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w' < w, (f w').eval ≠ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w - s₁ s₂ ⟨hsh, hps, hrd, hfr⟩ hex
  obtain ⟨v, s', hv, hw', hex⟩ := exists_of_exec_seq_lit hex
  rw [exec_skip, Option.some_inj] at hex
  subst hex
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hps, fun w' hw => ?_,
    fun q b i hb => ?_⟩
  · by_cases hww : (f w').eval = (f w).eval
    · exact ⟨v, hv, hww ▸ Store.read_of_write_eq_some hw'⟩
    · have hlt : w' < w := lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) (fun h => hww (h ▸ rfl))
      rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr hww)]
      exact hrd w' hlt
  · rw [Store.read_of_write_eq_some_of_ne hw' ?_]
    · exact hfr q b i (hb.imp_right fun h w' hw => h w' (Nat.lt_succ_of_lt hw))
    · exact hb.imp_right fun h => (h w (Nat.lt_succ_self w)).symm

end Inversion

end NLAlib.Computation
