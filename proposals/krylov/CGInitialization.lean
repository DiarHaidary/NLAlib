/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Model

/-!
# Initialization lemmas for the proposed CG program

Actual ROM and initialization loops used by the proposed canonical CG tree. These lemmas
state executions of the existing Computation syntax, with exact storage frames and counts;
they introduce no new program or arithmetic interface.

## Main results

* `NLAlib.CGImplementation.exec_forRange_rom`: load the matrix words from ROM.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation

variable {P ι K : Type} [DecidableEq P]

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


end NLAlib.CGImplementation
