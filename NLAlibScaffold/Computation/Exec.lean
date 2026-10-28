/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exec

/-!
# Costs of a straight-line run do not depend on the value semantics

A statement is **straight-line** (`NLAlib.Computation.Stmt.StraightLine`) when it has no
conditional (`ite`) and no loop on a comparison (`whileFuel`): its control flow is fixed by its
syntax. The tape positions, counts and memory of a successful run of a straight-line statement
(`NLAlib.Computation.St.usage`) are then a function of the syntax, the charge and the widths only,
not of the value semantics, the tapes, the oracles or the stored values
(`NLAlib.Computation.usage_eq_of_exec_eq_some_of_straightLine`). So a floating-point analysis
of a straight-line kernel takes its counts and memory from the exact specification of the kernel,
and becomes a `NLAlib.Computation.RunsWithin` statement. To move into
`NLAlib/Computation/Exec.lean` when proved. Design: `docs/design/Computation-Rounding.md` (R5).

## Main definitions

* `NLAlib.Computation.Stmt.StraightLine`: no `ite` and no `whileFuel`.
* `NLAlib.Computation.St.usage`: the tape positions, counts and memory of a state.

## Main results

* `NLAlib.Computation.usage_eq_of_exec_eq_some_of_straightLine`: two successful runs of a
  straight-line statement, under interpretations with the same charge and widths, from states
  with the same usage and store shape, end with the same usage.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι VB VI : Type}

/-- A statement is **straight-line** if it has no conditional (`ite`) and no loop on a comparison
(`whileFuel`), in any loop or allocation body: which instructions it runs is fixed by its syntax
and its index values, not by the stored values. -/
def Stmt.StraightLine : Stmt P ι VB VI → Prop
  | .skip => True
  | .seq s t => s.StraightLine ∧ t.StraightLine
  | .instr _ => True
  | .apply .. => True
  | .rom .. => True
  | .alloc _ _ body => ∀ b, (body b).StraightLine
  | .loop _ body => ∀ i, (body i).StraightLine
  | .whileFuel .. => False
  | .ite .. => False
  | .named _ _ body => body.StraightLine

/-- The **usage** of a state: the tape positions, the counts, and the current and peak memory,
in cells per tag and in bits; the state without its store. -/
def St.usage {K C : Type} (st : St P K C) : (Dist → ℕ) × C × (P → ℕ) × (P → ℕ) × ℕ × ℕ :=
  (st.pos, st.cnt, st.cur, st.peak, st.curW, st.peakW)

variable [DecidableEq P] {K K' C : Type} [AddMonoid C]

/-- Two runs of one scalar instruction from the same tape positions end at the same tape
positions, whatever the value semantics, the tapes and the stores. -/
private theorem Instr.snd_run_eq {i : Instr P ℕ ℕ} {sem : ScalarSem P K} {sem' : ScalarSem P K'}
    {tape : Dist → ℕ → K} {tape' : Dist → ℕ → K'} {s : Store P K} {s' : Store P K'}
    {pos : Dist → ℕ} {r : Store P K × (Dist → ℕ)} {r' : Store P K' × (Dist → ℕ)}
    (h : i.run sem tape s pos = some r) (h' : i.run sem' tape' s' pos = some r') :
    r.2 = r'.2 := by
  cases i <;> simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h h' <;>
    grind

/-- Two folds whose steps keep a relation between their states keep it. -/
private theorem foldlM_rel {α σ σ' : Type} (R : σ → σ' → Prop) {f : σ → α → Option σ}
    {g : σ' → α → Option σ'}
    (hfg : ∀ x a a' b b', R a a' → f a x = some b → g a' x = some b' → R b b') :
    ∀ {l : List α} {a b : σ} {a' b' : σ'}, R a a' → l.foldlM f a = some b →
      l.foldlM g a' = some b' → R b b'
  | [], _, _, _, _, hR, h, h' => by cases h; cases h'; exact hR
  | x :: l, _, _, _, _, hR, h, h' => by
    rw [List.foldlM_cons] at h h'
    obtain ⟨c, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c', h1', h2'⟩ := Option.bind_eq_some_iff.mp h'
    exact foldlM_rel R hfg (hfg x _ _ _ _ hR h1 h1') h2 h2'

/-- The induction behind `NLAlib.Computation.usage_eq_of_exec_eq_some_of_straightLine`: the
shape of the store and the usage are carried together. -/
private theorem shape_usage_eq_of_exec (I : Interp P ι K C) (I' : Interp P ι K' C)
    (hc : I.charge = I'.charge) (hw : I.width = I'.width) :
    ∀ (s : Stmt P ι ℕ ℕ), s.StraightLine → ∀ {st₀ st₁ : St P K C} {st₀' st₁' : St P K' C},
      st₀.store.shape = st₀'.store.shape → st₀.usage = st₀'.usage →
      exec I s st₀ = some st₁ → exec I' s st₀' = some st₁' →
      st₁.store.shape = st₁'.store.shape ∧ st₁.usage = st₁'.usage
  | .skip, _, _, _, _, _, hsh, hu, h, h' => by
    rw [exec_skip] at h h'; cases h; cases h'; exact ⟨hsh, hu⟩
  | .seq s t, hst, _, _, _, _, hsh, hu, h, h' => by
    rw [exec_seq] at h h'
    obtain ⟨st₂, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨st₂', h1', h2'⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨hsh₂, hu₂⟩ := shape_usage_eq_of_exec I I' hc hw s hst.1 hsh hu h1 h1'
    exact shape_usage_eq_of_exec I I' hc hw t hst.2 hsh₂ hu₂ h2 h2'
  | .instr i, _, st₀, _, st₀', _, hsh, hu, h, h' => by
    simp only [St.usage, Prod.mk.injEq] at hu
    obtain ⟨hpos, hcnt, hcur, hpeak, hcurW, hpeakW⟩ := hu
    rw [exec_instr] at h h'
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h'
    rw [hpos] at hr
    refine ⟨(Instr.shape_of_run_eq_some hr).trans
      (hsh.trans (Instr.shape_of_run_eq_some hr').symm), ?_⟩
    simp only [St.usage, Prod.mk.injEq]
    exact ⟨Instr.snd_run_eq hr hr', by rw [hcnt, hc], hcur, hpeak, hcurW, hpeakW⟩
  | .apply o p dst dOff src sOff cols, _, st₀, _, st₀', _, hsh, hu, h, h' => by
    simp only [St.usage, Prod.mk.injEq] at hu
    obtain ⟨hpos, hcnt, hcur, hpeak, hcurW, hpeakW⟩ := hu
    rw [exec] at h h'
    split_ifs at h h'
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h h'
    obtain ⟨_, -, _, -, s, hs, rfl⟩ := h
    obtain ⟨_, -, _, -, s', hs', rfl⟩ := h'
    refine ⟨(Store.shape_of_writeBlock_eq_some hs).trans
      (hsh.trans (Store.shape_of_writeBlock_eq_some hs').symm), ?_⟩
    simp only [St.usage, Prod.mk.injEq]
    exact ⟨hpos, by rw [hcnt, hc], hcur, hpeak, hcurW, hpeakW⟩
  | .rom p dst i, _, st₀, _, st₀', _, hsh, hu, h, h' => by
    simp only [St.usage, Prod.mk.injEq] at hu
    obtain ⟨hpos, hcnt, hcur, hpeak, hcurW, hpeakW⟩ := hu
    rw [exec] at h h'
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h h'
    obtain ⟨_, -, s, hs, rfl⟩ := h
    obtain ⟨_, -, s', hs', rfl⟩ := h'
    refine ⟨(Store.shape_of_write_eq_some hs).trans
      (hsh.trans (Store.shape_of_write_eq_some hs').symm), ?_⟩
    simp only [St.usage, Prod.mk.injEq]
    exact ⟨hpos, by rw [hcnt, hc], hcur, hpeak, hcurW, hpeakW⟩
  | .alloc p len body, hst, st₀, _, st₀', _, hsh, hu, h, h' => by
    simp only [St.usage, Prod.mk.injEq] at hu
    obtain ⟨hpos, hcnt, hcur, hpeak, hcurW, hpeakW⟩ := hu
    rw [exec_alloc] at h h'
    obtain ⟨st₂, h2, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨st₂', h2', rfl⟩ := Option.map_eq_some_iff.mp h'
    have hsize : st₀.store.size = st₀'.store.size := by
      simpa [Store.shape] using congrArg Array.size hsh
    rw [hsize] at h2
    obtain ⟨hsh₂, hu₂⟩ := shape_usage_eq_of_exec I I' hc hw (body st₀'.store.size)
      (hst _) (by simp only [Store.shape, Array.map_push, Array.size_replicate] at hsh ⊢; rw [hsh])
      (by simp only [St.usage, Prod.mk.injEq]
          exact ⟨hpos, hcnt, by rw [hcur], by rw [hpeak, hcur], by rw [hcurW, hw],
            by rw [hpeakW, hcurW, hw]⟩) h2 h2'
    simp only [St.usage, Prod.mk.injEq] at hu₂
    obtain ⟨hpos₂, hcnt₂, hcur₂, hpeak₂, hcurW₂, hpeakW₂⟩ := hu₂
    refine ⟨by simp only [Store.shape_pop, hsh₂], ?_⟩
    simp only [St.usage, Prod.mk.injEq]
    exact ⟨hpos₂, hcnt₂, by rw [hcur₂], hpeak₂, by rw [hcurW₂, hw], hpeakW₂⟩
  | .loop n body, hst, _, _, _, _, hsh, hu, h, h' => by
    rw [exec_loop] at h h'
    exact foldlM_rel (fun (a : St P K C) (a' : St P K' C) =>
        a.store.shape = a'.store.shape ∧ a.usage = a'.usage)
      (fun i _ _ _ _ hR hb hb' => shape_usage_eq_of_exec I I' hc hw (body i) (hst i) hR.1 hR.2
        hb hb') ⟨hsh, hu⟩ h h'
  | .whileFuel .., hst, _, _, _, _, _, _, _, _ => hst.elim
  | .ite .., hst, _, _, _, _, _, _, _, _ => hst.elim
  | .named _ _ body, hst, _, _, _, _, hsh, hu, h, h' => by
    rw [exec_named] at h h'
    exact shape_usage_eq_of_exec I I' hc hw body hst hsh hu h h'

/-- **The costs of a straight-line run do not depend on the value semantics**: for interpretations
`I` and `I'` (over any carriers) with the same charge and the same widths, and a straight-line
statement $s$, if the runs of $s$ under `I` from $\mathit{st}_0$ and under `I'` from
$\mathit{st}'_0$ both succeed, and the two start states have the same usage and the same store
shape, then the two end states have the same usage: the same tape positions, counts, and current
and peak memory. The value semantics, tapes, oracles, read-only data and stored values may
differ. No printed source. -/
theorem usage_eq_of_exec_eq_some_of_straightLine (I : Interp P ι K C) (I' : Interp P ι K' C)
    (hc : I.charge = I'.charge) (hw : I.width = I'.width) {s : Stmt P ι ℕ ℕ}
    (hs : s.StraightLine) {st₀ st₁ : St P K C} {st₀' st₁' : St P K' C}
    (hshape : st₀.store.shape = st₀'.store.shape) (husage : st₀.usage = st₀'.usage)
    (h : exec I s st₀ = some st₁) (h' : exec I' s st₀' = some st₁') :
    st₁.usage = st₁'.usage :=
  (shape_usage_eq_of_exec I I' hc hw s hs hshape husage h h').2

end NLAlib.Computation
