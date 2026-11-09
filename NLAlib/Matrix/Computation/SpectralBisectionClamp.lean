/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Contract
public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Computation.StaticCost
public import NLAlib.Computation.RoutineSpec

/-!
# The clamp of the split index of the spectral bisection program

The node step of `NLAlib.eighProg` clamps $\mathrm{fl}(t + \mathrm{fl}(1/2))$ to $[0, k]$ by counted
instructions (`NLAlib.eighClampBlock`) before its index binder, which fails on a negative value and
above its bound. Under exact comparisons, integer literals up to $k$ and the exact floor conversion,
the clamp writes back a value whose conversion is $\min(k, \lfloor x\rfloor_+)$, and it always
succeeds: the binder always receives a value in range.

## Main results

* `NLAlib.eighClampBlock_bind_run`: the clamp then the rest, as a statement.
* `NLAlib.toNat_eighClamp`: the clamped index, as mathematics.
* `NLAlib.spec_eighClampBlock`: the clamp as a routine specification, in every mode.
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

omit [DecidableEq P] [AddMonoid C] in
/-- **The clamped index**, the mathematics of the clamp: under the exact floor conversion, the
conversion of the stored $0$ if $x < 0$, of the stored $k$ if $k \le x$, and of $x$ otherwise, is
$\min(k, \lfloor x\rfloor_+)$, for the decoded value $x$ of $w$. No printed source. -/
theorem toNat_eighClamp {dec : P → K → ℝ} {sem : ScalarSem P K} (htn : IsExactToNat dec sem)
    {p : P} {k : ℕ} {w z0 zk : K} (hd0 : dec p z0 = 0) (hdk : dec p zk = k) :
    sem.toNat p (if dec p z0 ≤ dec p w then (if dec p zk ≤ dec p w then zk else w) else z0) =
      some (min k ⌊dec p w⌋₊) := by
  rw [hd0, hdk]
  split_ifs with h0 hk
  · rw [htn, hdk, if_pos (Nat.cast_nonneg k), Nat.floor_natCast, min_eq_left (Nat.le_floor hk)]
  · rw [htn, if_pos h0, min_eq_right ((Nat.floor_lt h0).mpr (not_le.mp hk)).le]
  · rw [htn, hd0, if_pos le_rfl, Nat.floor_zero, Nat.floor_eq_zero.mpr (by linarith), min_zero]

/-- **The clamp as a routine specification**, in every mode: with exact comparisons at `p`, exact
integer literals up to $k$ and the exact floor conversion, from a state whose cell $6$ of `t` holds
$w$, the clamp (`NLAlib.eighClampBlock`, literals in the cells $2$ and $3$ of `t`) modifies only
the cells $2$, $3$, $6$ of `t`, keeps the tape positions, and leaves in the cell $6$ a word whose
conversion is $\min(k, \lfloor w\rfloor_+)$. No printed source. -/
theorem spec_eighClampBlock (md : Mode) {dec : P → K → ℝ} {p : P}
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    {k : ℕ} (hlit : IsExactIntLit dec I.sem k) (htn : IsExactToNat dec I.sem) {t : ℕ} (w : K) :
    RoutineSpec md I (fun st => st.store.read p t 6 = some w)
      (eighClampBlock p (.const k) ⟨t, 6⟩ ⟨t, 2⟩ ⟨t, 3⟩) [(t, 2, 1), (t, 3, 1), (t, 6, 1)]
      fun st st' => (∃ wc, st'.store.read p t 6 = some wc ∧
        I.sem.toNat p wc = some (min k ⌊dec p w⌋₊)) ∧ PosKept st st' := by
  obtain ⟨z0, hz0, hd0⟩ := hlit p 0 (Nat.zero_le _)
  obtain ⟨zk, hzk, hdk⟩ := hlit p k le_rfl
  refine ⟨by exec_composable, fun st hst => ?_⟩
  obtain ⟨m, hshm, h6m⟩ := Store.exists_getElem?_shape_of_read_eq_some hst
  have hW (i : ℕ) (hi : i ≤ 6) (s : Store P K) (hs : s.shape = st.store.shape) :
      md.Needs (Writable s p t i 1) := Mode.needs_of (writable_of_shape_eq hs hshm (by omega)) md
  refine (RoutineSpec.ins (spec_lit (p := p) (dst := ⟨t, 2⟩) (q := 0) (v := z0)
    (by simpa using hz0))).wp_bind
    (hW 2 (by omega) _ rfl) fun st₁ hm₁ ⟨h2, _, hp₁⟩ => ?_
  refine (RoutineSpec.ins (spec_litIdx (p := p) (dst := ⟨t, 3⟩) (e := .const k) hzk)).wp_bind
    (hW 3 (by omega) _ hm₁.1) fun st₂ hm₂ ⟨h3, _, hp₂⟩ => ?_
  have h6 := (readsOnly_read p t 6 (some w)).of_modifies hst (hm₁.trans hm₂) (by fp_omega)
  have h2' := (readsOnly_read p t 2 (some z0)).of_modifies h2 hm₂ (by fp_omega)
  refine (RoutineSpec.ifThenElse (r := decide (dec p z0 ≤ dec p w)) (fp := [(t, 6, 1)])
    (RoutineSpec.ifThenElse (r := decide (dec p zk ≤ dec p w))
      (RoutineSpec.ins (spec_copy (x := ⟨t, 3⟩) (dst := ⟨t, 6⟩) (a := zk)))
      (RoutineSpec.pure (pre := fun _ => True))
      (pre := fun st => st.store.read p t 3 = some zk ∧ st.store.read p t 6 = some w ∧
        st.store.shape = st₂.store.shape) (fun _ h => ⟨zk, w, h.1, h.2.1, hcmp _ _⟩)
      (fun _ h _ => ⟨h.1, hW 6 le_rfl _ (h.2.2.trans hm₂.1 |>.trans hm₁.1)⟩) fun _ _ _ => trivial)
    (RoutineSpec.ins (spec_copy (x := ⟨t, 2⟩) (dst := ⟨t, 6⟩) (a := z0)))
    (fun _ h => ⟨z0, w, h.1, h.2.2.1, hcmp _ _⟩) (fun _ h _ => ⟨h.2.1, h.2.2.1, h.2.2.2⟩)
    fun _ h _ => ⟨h.1, hW 6 le_rfl _ (h.2.2.2.trans hm₂.1 |>.trans hm₁.1)⟩).wp_run
    (pre := fun st => st.store.read p t 2 = some z0 ∧ st.store.read p t 3 = some zk ∧
      st.store.read p t 6 = some w ∧ st.store.shape = st₂.store.shape) ⟨h2', h3, h6, rfl⟩
    fun st₃ hm₃ h => ?_
  have key : (st₃.store.read p t 6 = some (if dec p z0 ≤ dec p w then
      (if dec p zk ≤ dec p w then zk else w) else z0)) ∧ st₃.pos = st₂.pos := by
    by_cases h0 : dec p z0 ≤ dec p w
    · obtain ⟨hT, hE⟩ := h.1 (decide_eq_true h0)
      by_cases hk : dec p zk ≤ dec p w
      · rw [if_pos h0, if_pos hk]
        exact ⟨(hT (decide_eq_true hk)).1, (hT (decide_eq_true hk)).2.2⟩
      · rw [if_pos h0, if_neg hk, hE (decide_eq_false hk)]
        exact ⟨h6, rfl⟩
    · rw [if_neg h0]
      exact ⟨(h.2 (decide_eq_false h0)).1, (h.2 (decide_eq_false h0)).2.2⟩
  exact ⟨(hm₁.trans hm₂ |>.trans hm₃).mono (by simp), ⟨_, key.1,
    toNat_eighClamp htn (by simpa using hd0) hdk⟩, key.2.trans (hp₂.trans hp₁)⟩

/-- The run of the clamp of the split index: with exact comparisons at `p`, exact integer
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
  have h := spec_eighClampBlock (t := t) .total hcmp hlit htn w
  obtain ⟨σ, hrun, hm, ⟨hv, hpos⟩, hcur, hpeak, hcurW, hpeakW⟩ := (h.spec.and_liberal
    (Triple.seq_mem (triple_instr_mem _) (Triple.seq_mem (triple_instr_mem _) (Triple.seq_mem
      (Triple.ite_mem (Triple.seq_mem (Triple.ite_mem (Triple.seq_mem (triple_instr_mem _)
        triple_skip_mem) triple_skip_mem) triple_skip_mem)
        (Triple.seq_mem (triple_instr_mem _) triple_skip_mem)) triple_skip_mem)))).exists_exec hw
  refine ⟨σ, fun f => by rw [h.composable f st, hrun, Option.bind_some], hv, fun q b i hbi =>
    hm.2 q b i fun x hx => ?_, hm.1, hpos, hcur, hpeak, hcurW, hpeakW⟩
  refine blockDisjoint_iff.mpr ?_
  by_cases hb : b = t
  · have := hbi hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> dsimp only <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact Or.inl hb

end NLAlib
