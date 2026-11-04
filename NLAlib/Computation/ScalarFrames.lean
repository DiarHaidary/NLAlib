/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Model

/-!
# Scalar instruction frames and execution composition

Actual scalar operations expose their store write, exact charge and complete cell frame.
Composition certificates join emitted prefixes to later execution. A generic ROM loading
loop retains its full storage frame and all usage guarantees for arbitrary stored words.

## Main results

* `exec_scalar_bin`, `exec_scalar_un`, `exec_scalar_copy`, `exec_scalar_lit`: scalar frames.
* `ExecutionComposable`, `executionComposable_single`, `ExecutionComposable.bind`: composition.
* `exec_forRange_rom`: actual ROM loading with a complete buffer frame.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P K : Type} [DecidableEq P]

/-- One scalar instruction executes from initialized operands into a writable cell. This
records the actual store write, exact charge and complete frame; the arithmetic premise is
only the interpretation's single primitive operation, not a solver error assumption. -/
theorem exec_scalar_bin {ι C : Type} [AddMonoid C] (I : Interp P ι K C)
    (tag : P) (st : St P K C) (op : BinOp) (dst x y : Cell ℕ ℕ)
    (a b value : K) (hx : st.store.read tag x.buf x.idx.eval = some a)
    (hy : st.store.read tag y.buf y.idx.eval = some b)
    (hv : I.sem.bin tag op a b = some value)
    (hd : ∃ len, st.store.shape[dst.buf]? = some (tag, len) ∧ dst.idx.eval < len) :
    ∃ store, st.store.write tag dst.buf dst.idx.eval value = some store ∧
      exec I (Builder.ins (.bin tag op dst x y)).run st =
        some { st with store := store, cnt := st.cnt + I.charge (.bin tag op) } ∧
      store.shape = st.store.shape ∧ store.read tag dst.buf dst.idx.eval = some value ∧
      ∀ q buf idx, (q ≠ tag ∨ buf ≠ dst.buf ∨ idx ≠ dst.idx.eval) →
        store.read q buf idx = st.store.read q buf idx := by
  obtain ⟨len, hlen, hidx⟩ := hd
  obtain ⟨store, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape value hlen hidx
  refine ⟨store, hw, ?_, Store.shape_of_write_eq_some hw,
    Store.read_of_write_eq_some hw, ?_⟩
  · exact (exec_seq_instr_bin I hx hy hv hw).trans (exec_skip I _)
  · intro q buf idx hne
    rcases hne with hq | hcell
    · exact Store.read_of_write_eq_some_of_ne_tag hw hq
    · exact Store.read_of_write_eq_some_of_ne hw hcell

/-- Unary scalar instructions have the same actual write, charge and full frame contract. -/
theorem exec_scalar_un {ι C : Type} [AddMonoid C] (I : Interp P ι K C)
    (tag : P) (st : St P K C) (op : UnOp) (dst x : Cell ℕ ℕ)
    (a value : K) (hx : st.store.read tag x.buf x.idx.eval = some a)
    (hv : I.sem.un tag op a = some value)
    (hd : ∃ len, st.store.shape[dst.buf]? = some (tag, len) ∧ dst.idx.eval < len) :
    ∃ store, st.store.write tag dst.buf dst.idx.eval value = some store ∧
      exec I (Builder.ins (.un tag op dst x)).run st =
        some { st with store := store, cnt := st.cnt + I.charge (.un tag op) } ∧
      store.shape = st.store.shape ∧ store.read tag dst.buf dst.idx.eval = some value ∧
      ∀ q buf idx, (q ≠ tag ∨ buf ≠ dst.buf ∨ idx ≠ dst.idx.eval) →
        store.read q buf idx = st.store.read q buf idx := by
  obtain ⟨len, hlen, hidx⟩ := hd
  obtain ⟨store, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape value hlen hidx
  refine ⟨store, hw, ?_, Store.shape_of_write_eq_some hw,
    Store.read_of_write_eq_some hw, ?_⟩
  · exact (exec_seq_instr_un I hx hv hw).trans (exec_skip I _)
  · intro q buf idx hne
    rcases hne with hq | hcell
    · exact Store.read_of_write_eq_some_of_ne_tag hw hq
    · exact Store.read_of_write_eq_some_of_ne hw hcell

/-- A scalar copy needs initialized source data but only writable destination capacity. -/
theorem exec_scalar_copy {ι C : Type} [AddMonoid C] (I : Interp P ι K C)
    (tag : P) (st : St P K C) (dst src : Cell ℕ ℕ)
    (value : K) (hx : st.store.read tag src.buf src.idx.eval = some value)
    (hd : ∃ len, st.store.shape[dst.buf]? = some (tag, len) ∧ dst.idx.eval < len) :
    ∃ store, st.store.write tag dst.buf dst.idx.eval value = some store ∧
      exec I (Builder.ins (.copy tag dst src)).run st =
        some { st with store := store, cnt := st.cnt + I.charge (.copy tag) } ∧
      store.shape = st.store.shape ∧ store.read tag dst.buf dst.idx.eval = some value ∧
      ∀ q buf idx, (q ≠ tag ∨ buf ≠ dst.buf ∨ idx ≠ dst.idx.eval) →
        store.read q buf idx = st.store.read q buf idx := by
  obtain ⟨len, hlen, hidx⟩ := hd
  obtain ⟨store, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape value hlen hidx
  refine ⟨store, hw, ?_, Store.shape_of_write_eq_some hw,
    Store.read_of_write_eq_some hw, ?_⟩
  · exact (exec_seq_instr_copy I hx hw).trans (exec_skip I _)
  · intro q buf idx hne
    rcases hne with hq | hcell
    · exact Store.read_of_write_eq_some_of_ne_tag hw hq
    · exact Store.read_of_write_eq_some_of_ne hw hcell

/-- Literal execution retains the actual writable-store witness and exact charge. -/
theorem exec_scalar_lit {ι C : Type} [AddMonoid C] (I : Interp P ι K C)
    (tag : P) (st : St P K C) (dst : Cell ℕ ℕ) (q : ℚ) (value : K)
    (hv : I.sem.lit tag q = some value)
    (hd : ∃ len, st.store.shape[dst.buf]? = some (tag, len) ∧ dst.idx.eval < len) :
    ∃ store, st.store.write tag dst.buf dst.idx.eval value = some store ∧
      exec I (Builder.ins (.lit tag dst q)).run st =
        some { st with store := store, cnt := st.cnt + I.charge (.lit tag) } ∧
      store.shape = st.store.shape ∧ store.read tag dst.buf dst.idx.eval = some value ∧
      ∀ p buf idx, (p ≠ tag ∨ buf ≠ dst.buf ∨ idx ≠ dst.idx.eval) →
        store.read p buf idx = st.store.read p buf idx := by
  obtain ⟨len, hlen, hidx⟩ := hd
  obtain ⟨store, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape value hlen hidx
  refine ⟨store, hw, ?_, Store.shape_of_write_eq_some hw,
    Store.read_of_write_eq_some hw, ?_⟩
  · exact (exec_seq_instr_lit I hv hw).trans (exec_skip I _)
  · intro p buf idx hne
    rcases hne with hp | hcell
    · exact Store.read_of_write_eq_some_of_ne_tag hw hp
    · exact Store.read_of_write_eq_some_of_ne hw hcell

/-- A builder whose emitted prefix composes with later execution. This property applies to
framed instruction/kernel prefixes; it does not presume anything about solver arithmetic. -/
def ExecutionComposable {ι C : Type} [AddMonoid C] (I : Interp P ι K C)
    (b : Builder P ι ℕ ℕ Unit) : Prop :=
  ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C),
    exec I (b >>= f).run st = (exec I b.run st).bind (exec I (f ()).run)

/-- Any builder emitting one statement before its continuation composes with execution. -/
theorem executionComposable_single {ι C : Type} [AddMonoid C] (I : Interp P ι K C)
    {b : Builder P ι ℕ ℕ Unit} {X : Stmt P ι ℕ ℕ}
    (hb : ∀ k, ContT.run b k = .seq X (k ())) : ExecutionComposable I b :=
  fun f st => exec_run_bind I hb f st

/-- Execution composition is closed under concatenation of two certified prefixes. -/
theorem ExecutionComposable.bind {ι C : Type} [AddMonoid C] {I : Interp P ι K C}
    {a b : Builder P ι ℕ ℕ Unit} (ha : ExecutionComposable I a)
    (hb : ExecutionComposable I b) : ExecutionComposable I (a >>= fun _ => b) := by
  intro f st
  change exec I (a >>= fun _ => b >>= f).run st = _
  rw [ha, ha]
  simp only [Option.bind_assoc]
  congr 1
  funext out
  exact hb f out

variable {ι : Type}

/-- A ROM loading loop succeeds whenever its source entries exist and its destination has
room. It preserves every cell in other buffers, all usage fields except the ROM count, and
the destination shape. This holds for any scalar semantics and any carrier of words. -/
theorem exec_forRange_rom (I : Interp P ι K (OpCount P ι)) (tag : P)
    (st : St P K (OpCount P ι)) (n : IExp ℕ) (buf : ℕ) (values : ℕ → K)
    (hshape : st.store.shape[buf]? = some (tag, n.eval))
    (hrom : ∀ i < n.eval, I.rom i = some (values i)) :
    ∃ s', exec I (.loop n fun i => .seq (.rom tag ⟨buf, .var i⟩ (.var i)) .skip) st =
      some { st with store := s', cnt := st.cnt + n.eval • I.charge (.rom tag) } ∧
      s'.shape = st.store.shape ∧
      (∀ i < n.eval, s'.read tag buf i = some (values i)) ∧
      ∀ p b i, b ≠ buf → s'.read p b i = st.store.read p b i := by
  let R (j : ℕ) (out : St P K (OpCount P ι)) : Prop :=
    ∃ s', out = { st with store := s', cnt := st.cnt + j • I.charge (.rom tag) } ∧
      s'.shape = st.store.shape ∧
      (∀ i < j, s'.read tag buf i = some (values i)) ∧
      ∀ p b i, b ≠ buf → s'.read p b i = st.store.read p b i
  have h0 : R 0 st := ⟨st.store, by simp only [zero_nsmul, add_zero],
    rfl, fun i hi => by omega, fun _ _ _ _ => rfl⟩
  have hstep : ∀ j < n.eval, ∀ out, R j out → ∃ out',
      exec I (.seq (.rom tag ⟨buf, .var j⟩ (.var j)) .skip) out = some out' ∧
        R (j + 1) out' := by
    rintro j hj out ⟨s, rfl, hsh, hread, hframe⟩
    have hshape' : s.shape[buf]? = some (tag, n.eval) := by
      rw [hsh]
      exact hshape
    obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape (values j) hshape' hj
    refine ⟨{ st with store := s', cnt := st.cnt + (j + 1) • I.charge (.rom tag) },
      ?_, s', rfl, (Store.shape_of_write_eq_some hs').trans hsh, ?_, ?_⟩
    · simp only [exec, IExp.eval_var, hrom j hj, Option.bind_some, hs',
        Option.map_some, succ_nsmul, add_assoc]
    · intro i hi
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | hij
      · exact Store.read_of_write_eq_some hs'
      · rw [Store.read_of_write_eq_some_of_ne hs' (Or.inr (by omega))]
        exact hread i hij
    · intro p b i hb
      rw [Store.read_of_write_eq_some_of_ne hs' (Or.inl hb)]
      exact hframe p b i hb
  obtain ⟨out, hrun, s', hout, hsh, hread, hframe⟩ :=
    exists_exec_loop_eq_some_of_forall I (n := n) R h0 hstep
  exact ⟨s', hout ▸ hrun, hsh, hread, hframe⟩

end NLAlib.Computation
