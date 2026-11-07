/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlibScaffold.Computation.IndexBinder

/-!
# The clamp of the split index of the spectral bisection program (scaffold)

The node step of `NLAlib.eighProg` clamps $\mathrm{fl}(t + \mathrm{fl}(1/2))$ to $[0, k]$ by
counted instructions (`NLAlib.eighClampBlock`) before its index binder, which fails on a negative
value and above its bound. Under exact comparisons, integer literals up to $k$ and the exact floor
conversion, the clamp writes back a value whose conversion is $\min(k, \lfloor x\rfloor_+)$, and
it always succeeds: the binder always receives a value in range.

## Main results

* `NLAlib.eighClampBlock_bind_run`: the clamp then the rest, as a statement.
* `NLAlib.exec_eighClampBlock_bind`: the run of the clamp, then the rest, is the run of the rest
  from a state whose clamped cell converts to $\min(k, \lfloor x\rfloor_+)$.
-/

@[expose] public section

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] {I : Interp P ι K C}

omit [DecidableEq P] [AddMonoid C] in
/-- The clamp of the cell $6$ of `t` (the literals in its cells $2$, $3$), then the rest, as a
statement. No printed source. -/
theorem eighClampBlock_bind_run (p : P) (k t : ℕ) (f : Unit → Builder P ι ℕ ℕ Unit) :
    (eighClampBlock p (.const k) ⟨t, 6⟩ ⟨t, 2⟩ ⟨t, 3⟩ >>= f).run =
      .seq (.instr (.lit p ⟨t, 2⟩ 0)) (.seq (.instr (.litIdx p ⟨t, 3⟩ (.const k)))
        (.seq (.ite p .le ⟨t, 2⟩ ⟨t, 6⟩
            (.seq (.ite p .le ⟨t, 3⟩ ⟨t, 6⟩ (.seq (.instr (.copy p ⟨t, 6⟩ ⟨t, 3⟩)) .skip) .skip)
              .skip)
            (.seq (.instr (.copy p ⟨t, 6⟩ ⟨t, 2⟩)) .skip))
          (f ()).run)) := rfl

/-- The two literals of the clamp: from a state whose cell $6$ of `t` holds $w$, the literals
$0$ and $k$ are written to the cells $2$ and $3$ of `t`, and the clamp then the rest runs as its
comparisons then the rest. No printed source. -/
private theorem exec_eighClampBlock_lits {p : P} {k t : ℕ} {st : St P K C} {w z0 zk : K}
    (hz0 : I.sem.lit p 0 = some z0) (hzk : I.sem.lit p (k : ℚ) = some zk)
    (hw : st.store.read p t 6 = some w) :
    ∃ s2 : Store P K, s2.shape = st.store.shape ∧ s2.read p t 2 = some z0 ∧
      s2.read p t 3 = some zk ∧ s2.read p t 6 = some w ∧
      (∀ q b i, (b = t → i ≠ 2 ∧ i ≠ 3 ∧ i ≠ 6) → s2.read q b i = st.store.read q b i) ∧
      ∀ f : Unit → Builder P ι ℕ ℕ Unit,
        exec I (eighClampBlock p (.const k) ⟨t, 6⟩ ⟨t, 2⟩ ⟨t, 3⟩ >>= f).run st =
          exec I (.seq (.ite p .le ⟨t, 2⟩ ⟨t, 6⟩
            (.seq (.ite p .le ⟨t, 3⟩ ⟨t, 6⟩ (.seq (.instr (.copy p ⟨t, 6⟩ ⟨t, 3⟩)) .skip) .skip)
              .skip)
            (.seq (.instr (.copy p ⟨t, 6⟩ ⟨t, 2⟩)) .skip))
          (f ()).run)
            { st with store := s2, cnt := st.cnt + I.charge (.lit p) + I.charge (.lit p) } := by
  obtain ⟨m, hshm, h6m⟩ := Store.exists_getElem?_shape_of_read_eq_some hw
  obtain ⟨s1, hs1⟩ := Store.exists_write_eq_some_of_getElem?_shape z0 hshm (i := 2) (by omega)
  have hsh1 : s1.shape = st.store.shape := Store.shape_of_write_eq_some hs1
  obtain ⟨s2, hs2⟩ := Store.exists_write_eq_some_of_getElem?_shape zk (hsh1 ▸ hshm) (i := 3)
    (by omega)
  refine ⟨s2, (Store.shape_of_write_eq_some hs2).trans hsh1, ?_, Store.read_of_write_eq_some hs2,
    ?_, fun q b i hbi => ?_, fun f => ?_⟩
  · rw [Store.read_of_write_eq_some_of_ne hs2 (Or.inr (by decide))]
    exact Store.read_of_write_eq_some hs1
  · rw [Store.read_of_write_eq_some_of_ne hs2 (Or.inr (by decide)),
      Store.read_of_write_eq_some_of_ne hs1 (Or.inr (by decide))]
    exact hw
  · have hne : ∀ j, j = 2 ∨ j = 3 → b ≠ t ∨ i ≠ j := fun j hj => by
      by_cases hb : b = t
      · obtain ⟨h2, h3, -⟩ := hbi hb
        rcases hj with rfl | rfl
        exacts [Or.inr h2, Or.inr h3]
      · exact Or.inl hb
    rw [Store.read_of_write_eq_some_of_ne hs2 (hne 3 (Or.inr rfl)),
      Store.read_of_write_eq_some_of_ne hs1 (hne 2 (Or.inl rfl))]
  · rw [eighClampBlock_bind_run, exec_seq, exec_instr]
    simp only [Instr.run, hz0, Option.bind_some, IExp.eval, hs1, Option.map_some, Instr.kind]
    rw [exec_seq, exec_instr]
    simp only [Instr.run, IExp.eval, hzk, Option.bind_some, hs2, Option.map_some, Instr.kind]

/-- **The run of the clamp of the split index**: with exact comparisons at `p`, exact integer
literals up to $k$ and the exact floor conversion, from a state whose cell $6$ of `t` holds $w$, the
clamp (`NLAlib.eighClampBlock`, literals in the cells $2$ and $3$ of `t`) then the rest runs as the
rest from a state whose cell $6$ of `t` converts to $\min(k, \lfloor w\rfloor_+)$, which differs
from the start only in the cells $2$, $3$, $6$ of `t`, with the same shape, tape positions and
memory. No printed source. -/
theorem exec_eighClampBlock_bind {dec : P → K → ℝ} {p : P}
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    {k : ℕ} (hlit : IsExactIntLit dec I.sem k) (htn : IsExactToNat dec I.sem) {t : ℕ}
    {st : St P K C} {w : K} (hw : st.store.read p t 6 = some w) :
    ∃ σ : St P K C,
      (∀ f : Unit → Builder P ι ℕ ℕ Unit,
        exec I (eighClampBlock p (.const k) ⟨t, 6⟩ ⟨t, 2⟩ ⟨t, 3⟩ >>= f).run st =
          exec I (f ()).run σ) ∧
      (∃ wc, σ.store.read p t 6 = some wc ∧ I.sem.toNat p wc = some (min k ⌊dec p w⌋₊)) ∧
      (∀ q b i, (b = t → i ≠ 2 ∧ i ≠ 3 ∧ i ≠ 6) → σ.store.read q b i = st.store.read q b i) ∧
      σ.store.shape = st.store.shape ∧ σ.pos = st.pos ∧ σ.cur = st.cur ∧ σ.peak = st.peak ∧
      σ.curW = st.curW ∧ σ.peakW = st.peakW := by
  obtain ⟨z0, hz0, hd0⟩ := hlit p 0 (Nat.zero_le _)
  obtain ⟨zk, hzk, hdk⟩ := hlit p k le_rfl
  obtain ⟨s2, hsh2, r2, r3, r6, fr2, hrun2⟩ :=
    exec_eighClampBlock_lits (I := I) (by simpa using hz0) hzk hw
  obtain ⟨m, hshm, h6m⟩ := Store.exists_getElem?_shape_of_read_eq_some hw
  -- the state after the two literals
  let c₂ : C := st.cnt + I.charge (.lit p) + I.charge (.lit p)
  let σ₂ : St P K C := { st with store := s2, cnt := c₂ }
  by_cases h0 : 0 ≤ dec p w
  · by_cases hkw : (k : ℝ) ≤ dec p w
    · -- the cell gets the literal k
      obtain ⟨s3, hs3⟩ := Store.exists_write_eq_some_of_getElem?_shape zk (hsh2 ▸ hshm) (i := 6)
        (by omega)
      let c₃ : C := σ₂.cnt + I.charge (.cmp p) + I.charge (.cmp p) + I.charge (.copy p)
      refine ⟨{ σ₂ with store := s3, cnt := c₃ }, fun f => ?_,
        ⟨zk, Store.read_of_write_eq_some hs3, ?_⟩,
        fun q b i hbi => ?_, (Store.shape_of_write_eq_some hs3).trans hsh2, rfl, rfl, rfl, rfl,
        rfl⟩
      · simp only [hrun2, exec_seq, exec_ite, exec_instr, exec_skip, cmpStep, σ₂, IExp.eval, r2, r3,
          r6, Option.bind_some, Option.map_some, hcmp, hd0, hdk, h0,
          hkw, decide_true, if_true, Nat.cast_zero, Instr.run, hs3, Instr.kind]
        rfl
      · rw [htn p zk, hdk, if_pos (Nat.cast_nonneg k), Nat.floor_natCast,
          min_eq_left (Nat.le_floor hkw)]
      · rw [Store.read_of_write_eq_some_of_ne hs3 ?_]
        · exact fr2 q b i hbi
        · by_cases hb : b = t
          · exact Or.inr (hbi hb).2.2
          · exact Or.inl hb
    · -- the cell is kept
      push Not at hkw
      let c₃ : C := σ₂.cnt + I.charge (.cmp p) + I.charge (.cmp p)
      refine ⟨{ σ₂ with cnt := c₃ }, fun f => ?_,
        ⟨w, r6, ?_⟩, fr2, hsh2, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [hrun2, exec_seq, exec_ite, exec_skip, cmpStep, σ₂, IExp.eval, r2, r3, r6,
          Option.bind_some, Option.map_some, hcmp, hd0, hdk, h0,
          not_le.mpr hkw, decide_true, decide_false, if_true, Bool.false_eq_true, if_false,
          Nat.cast_zero]
        rfl
      · rw [htn p w, if_pos h0, min_eq_right]
        exact (Nat.floor_lt h0).mpr hkw |>.le
  · -- the cell gets the literal 0
    obtain ⟨s3, hs3⟩ := Store.exists_write_eq_some_of_getElem?_shape z0 (hsh2 ▸ hshm) (i := 6)
      (by omega)
    push Not at h0
    let c₃ : C := σ₂.cnt + I.charge (.cmp p) + I.charge (.copy p)
    refine ⟨{ σ₂ with store := s3, cnt := c₃ },
      fun f => ?_, ⟨z0, Store.read_of_write_eq_some hs3, ?_⟩, fun q b i hbi => ?_,
      (Store.shape_of_write_eq_some hs3).trans hsh2, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [hrun2, exec_seq, exec_ite, exec_instr, exec_skip, cmpStep, σ₂, IExp.eval, r2, r6,
        Option.bind_some, Option.map_some, hcmp, hd0,
        not_le.mpr h0, decide_false, Bool.false_eq_true, if_false, Nat.cast_zero, Instr.run, hs3,
        Instr.kind]
      rfl
    · rw [htn p z0, hd0, Nat.cast_zero, if_pos le_rfl, Nat.floor_zero,
        Nat.floor_eq_zero.mpr (by linarith), min_zero]
    · rw [Store.read_of_write_eq_some_of_ne hs3 ?_]
      · exact fr2 q b i hbi
      · by_cases hb : b = t
        · exact Or.inr (hbi hb).2.2
        · exact Or.inl hb

end NLAlib
