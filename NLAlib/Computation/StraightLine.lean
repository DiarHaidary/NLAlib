/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineSpec

/-!
# Straight-line scalar blocks

A block of scalar instructions without loops or branches (the rotation of two complex entries,
the norm of a pair) is specified once, as a list of scalar operations
(`NLAlib.Computation.ScalarOp`) and the function that evaluates the list on the stored words
(`NLAlib.Computation.evalOps`), instead of instruction by instruction. A run of
`NLAlib.Computation.scalarBlock` modifies the cells it writes, each of which then holds a word,
counts one charge per operation and keeps the tape positions; the word function of the store
(`NLAlib.Computation.storeFn`: the word of each cell, `default` for a cell without one) after the
run is the evaluation of the list on the word function before it. Aliasing of cells is exactly
the `Function.update` of the evaluation, so the rule has no distinctness side goal, and every
index enters only through its value, so one specification serves a block at index variables and
at constants.

In the liberal mode the rule has no precondition. The total mode needs every cell the block reads
to hold a word when it is read (`NLAlib.Computation.OpsDefined`: present in the store, or written
earlier by the block, so temporaries need no initialisation), every operation to succeed along the
evaluation (`NLAlib.Computation.OpsOk`) and every cell it writes writable.

## Main definitions

* `NLAlib.Computation.ScalarOp`: a literal, an index literal, a binary or unary operation, or a
  copy, on cells.
* `NLAlib.Computation.scalarBlock`: the builder of a list of scalar operations.
* `NLAlib.Computation.storeFn`, `NLAlib.Computation.evalOps`: the word function of a store and
  the evaluation of a list on a word function.
* `NLAlib.Computation.OpsDefined`, `NLAlib.Computation.OpsOk`: the cells read hold words, and every
  operation succeeds.
* `NLAlib.Computation.WordTotal`: addition, subtraction, multiplication and negation never fail.

## Main results

* `NLAlib.Computation.spec_scalarBlock`: the routine specification of a list, in every mode.
* `NLAlib.Computation.opsOk_of_plain`, `NLAlib.Computation.IsRelErrSem.wordTotal`: success of the
  operations that cannot fail under total word arithmetic, which the standard model gives with
  every value in range.
-/

@[expose] public section

namespace NLAlib.Computation

/-- **A scalar operation on cells**: a literal, an index literal, a binary or unary operation, or
a copy; the scalar instructions of one tag that a straight-line block is made of. -/
inductive ScalarOp (VB VI : Type) where
  /-- Write the rational literal `q`. -/
  | lit (dst : Cell VB VI) (q : ℚ)
  /-- Write the value of the index expression `e`, as a literal. -/
  | litIdx (dst : Cell VB VI) (e : IExp VI)
  /-- A binary operation. -/
  | bin (op : BinOp) (dst x y : Cell VB VI)
  /-- A unary operation. -/
  | un (op : UnOp) (dst x : Cell VB VI)
  /-- A copy. -/
  | copy (dst src : Cell VB VI)

section Build

variable {P ι VB VI : Type}

/-- The instruction of a scalar operation at tag `p`. -/
def ScalarOp.toInstr (p : P) : ScalarOp VB VI → Instr P VB VI
  | .lit dst q => .lit p dst q
  | .litIdx dst e => .litIdx p dst e
  | .bin op dst x y => .bin p op dst x y
  | .un op dst x => .un p op dst x
  | .copy dst src => .copy p dst src

/-- **A straight-line block**: the instructions of a list of scalar operations at tag `p`, in
order. -/
def scalarBlock (p : P) (ops : List (ScalarOp VB VI)) : Builder P ι VB VI Unit :=
  ops.foldr (fun o r => Builder.ins (o.toInstr p) >>= fun _ => r) (pure ())

/-- The block of no operation is the empty builder. -/
@[simp] theorem scalarBlock_nil (p : P) :
    scalarBlock (ι := ι) (VB := VB) (VI := VI) p [] = pure () :=
  rfl

/-- A block is its first instruction, then the rest. -/
@[simp] theorem scalarBlock_cons (p : P) (o : ScalarOp VB VI) (os : List (ScalarOp VB VI)) :
    scalarBlock (ι := ι) p (o :: os) = Builder.ins (o.toInstr p) >>= fun _ => scalarBlock p os :=
  rfl

end Build

section Eval

variable {P K : Type}

/-- A cell of a store: the buffer handle and the index in it. -/
abbrev Loc : Type := ℕ × ℕ

/-- The location of a closed cell: its buffer and the value of its index. -/
def Cell.loc (c : Cell ℕ ℕ) : Loc := (c.buf, c.idx.eval)

/-- The location of a cell is its buffer and the value of its index. -/
@[simp] theorem Cell.loc_mk (b : ℕ) (e : IExp ℕ) : Cell.loc ⟨b, e⟩ = (b, e.eval) := rfl

/-- The cell a scalar operation writes. -/
def ScalarOp.dst : ScalarOp ℕ ℕ → Loc
  | .lit d _ => d.loc
  | .litIdx d _ => d.loc
  | .bin _ d _ _ => d.loc
  | .un _ d _ => d.loc
  | .copy d _ => d.loc

/-- The cells a scalar operation reads. -/
def ScalarOp.srcs : ScalarOp ℕ ℕ → List Loc
  | .lit _ _ => []
  | .litIdx _ _ => []
  | .bin _ _ x y => [x.loc, y.loc]
  | .un _ _ x => [x.loc]
  | .copy _ s => [s.loc]

/-- The cells written by a list of operations. -/
def dstLocs (ops : List (ScalarOp ℕ ℕ)) : List Loc := ops.map ScalarOp.dst

/-- The cells read by a list of operations. -/
def srcLocs (ops : List (ScalarOp ℕ ℕ)) : List Loc := ops.flatMap ScalarOp.srcs

/-- The footprint of a list of operations: one one-cell block per operation, at the cell it
writes (the form of `NLAlib.Computation.cellBlocks`). -/
def opsFootprint (ops : List (ScalarOp ℕ ℕ)) : List (ℕ × ℕ × ℕ) :=
  ops.map fun o => (o.dst.1, o.dst.2, 1)

/-- **The cells read are defined**: every cell an operation reads satisfies `D` when it is read,
where `D` starts as the given predicate (the cells that hold a word) and grows by each cell
written. A temporary written before it is read needs nothing of the store. -/
def OpsDefined : List (ScalarOp ℕ ℕ) → (Loc → Prop) → Prop
  | [], _ => True
  | o :: os, D => (∀ l ∈ o.srcs, D l) ∧ OpsDefined os fun l => l = o.dst ∨ D l

variable [Inhabited K]

/-- **The word function of a store** at tag `p`: the word of each cell, `default` where the cell
holds none. -/
def storeFn [DecidableEq P] (p : P) (s : Store P K) : Loc → K :=
  fun l => (s.read p l.1 l.2).getD default

/-- The word one scalar operation writes, on a word function: the result, `default` if the
operation fails (which only a failed run sees). -/
def ScalarOp.value (sem : ScalarSem P K) (p : P) (g : Loc → K) : ScalarOp ℕ ℕ → K
  | .lit _ q => (sem.lit p q).getD default
  | .litIdx _ e => (sem.lit p (e.eval : ℚ)).getD default
  | .bin op _ x y => (sem.bin p op (g x.loc) (g y.loc)).getD default
  | .un op _ x => (sem.un p op (g x.loc)).getD default
  | .copy _ s => g s.loc

/-- One scalar operation on a word function: the written cell gets the operation's word. -/
def ScalarOp.step (sem : ScalarSem P K) (p : P) (g : Loc → K) (o : ScalarOp ℕ ℕ) : Loc → K :=
  Function.update g o.dst (o.value sem p g)

/-- **The evaluation** of a list of operations on a word function. -/
def evalOps (sem : ScalarSem P K) (p : P) : List (ScalarOp ℕ ℕ) → (Loc → K) → Loc → K
  | [], g => g
  | o :: os, g => evalOps sem p os (o.step sem p g)

/-- An operation succeeds on a word function. -/
def ScalarOp.Ok (sem : ScalarSem P K) (p : P) (g : Loc → K) : ScalarOp ℕ ℕ → Prop
  | .lit _ q => ∃ v, sem.lit p q = some v
  | .litIdx _ e => ∃ v, sem.lit p (e.eval : ℚ) = some v
  | .bin op _ x y => ∃ v, sem.bin p op (g x.loc) (g y.loc) = some v
  | .un op _ x => ∃ v, sem.un p op (g x.loc) = some v
  | .copy _ _ => True

/-- **Every operation of a list succeeds** along its evaluation. -/
def OpsOk (sem : ScalarSem P K) (p : P) : List (ScalarOp ℕ ℕ) → (Loc → K) → Prop
  | [], _ => True
  | o :: os, g => o.Ok sem p g ∧ OpsOk sem p os (o.step sem p g)

/-- The evaluation of no operation. -/
@[simp] theorem evalOps_nil (sem : ScalarSem P K) (p : P) (g : Loc → K) :
    evalOps sem p [] g = g := rfl

/-- The evaluation of a list is its first step, then the rest. -/
@[simp] theorem evalOps_cons (sem : ScalarSem P K) (p : P) (o : ScalarOp ℕ ℕ)
    (os : List (ScalarOp ℕ ℕ)) (g : Loc → K) :
    evalOps sem p (o :: os) g = evalOps sem p os (o.step sem p g) := rfl

/-- The evaluation of two lists in sequence. -/
theorem evalOps_append (sem : ScalarSem P K) (p : P) (os ot : List (ScalarOp ℕ ℕ))
    (g : Loc → K) : evalOps sem p (os ++ ot) g = evalOps sem p ot (evalOps sem p os g) := by
  induction os generalizing g with
  | nil => rfl
  | cons o os ih => exact ih _

/-- The evaluation keeps every cell the list does not write. -/
theorem evalOps_of_not_mem (sem : ScalarSem P K) (p : P) {ops : List (ScalarOp ℕ ℕ)}
    {l : Loc} (hl : l ∉ dstLocs ops) (g : Loc → K) : evalOps sem p ops g l = g l := by
  induction ops generalizing g with
  | nil => rfl
  | cons o os ih =>
    simp only [dstLocs, List.map_cons, List.mem_cons, not_or] at hl
    rw [evalOps_cons, ih hl.2, ScalarOp.step, Function.update_of_ne hl.1]

/-- Success of two lists in sequence. -/
theorem opsOk_append (sem : ScalarSem P K) (p : P) (os ot : List (ScalarOp ℕ ℕ))
    (g : Loc → K) : OpsOk sem p (os ++ ot) g ↔
      OpsOk sem p os g ∧ OpsOk sem p ot (evalOps sem p os g) := by
  induction os generalizing g with
  | nil => simp [OpsOk]
  | cons o os ih => simp only [List.cons_append, OpsOk, ih, evalOps_cons, and_assoc]

omit [Inhabited K] in
/-- Defined cells are monotone in the predicate. -/
theorem OpsDefined.mono {ops : List (ScalarOp ℕ ℕ)} {D D' : Loc → Prop}
    (h : OpsDefined ops D) (hD : ∀ l, D l → D' l) : OpsDefined ops D' := by
  induction ops generalizing D D' with
  | nil => trivial
  | cons o os ih =>
    exact ⟨fun l hl => hD l (h.1 l hl), ih h.2 fun l => Or.imp_right (hD l)⟩

omit [Inhabited K] in
/-- The cells read are defined if all of them satisfy the predicate at the start. -/
theorem opsDefined_of_forall {ops : List (ScalarOp ℕ ℕ)} {D : Loc → Prop}
    (h : ∀ l ∈ srcLocs ops, D l) : OpsDefined ops D := by
  induction ops generalizing D with
  | nil => trivial
  | cons o os ih =>
    refine ⟨fun l hl => h l (List.mem_flatMap.mpr ⟨o, List.mem_cons_self, hl⟩),
      ih fun l hl => Or.inr (h l ?_)⟩
    exact List.mem_flatMap.mpr ((List.mem_flatMap.mp hl).imp fun _ h => ⟨.tail _ h.1, h.2⟩)

end Eval

section Run

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}

omit [AddMonoid C] in
/-- A cell that holds a word holds the word of the word function. -/
theorem storeFn_of_read {p : P} {s : Store P K} {b i : ℕ} {v : K}
    (h : s.read p b i = some v) : storeFn p s (b, i) = v := by
  simp [storeFn, h]

omit [AddMonoid C] in
/-- A cell that holds a word reads the word of the word function. -/
theorem read_eq_some_storeFn {p : P} {s : Store P K} {l : Loc}
    (h : ∃ v, s.read p l.1 l.2 = some v) : s.read p l.1 l.2 = some (storeFn p s l) := by
  obtain ⟨v, hv⟩ := h
  rw [storeFn_of_read hv, hv]

omit [AddMonoid C] in
/-- The word function of a store after a write is updated at the written cell. -/
theorem storeFn_eq_update_of_write {p : P} {s s' : Store P K} {b i : ℕ} {v : K}
    (h : s.write p b i v = some s') :
    storeFn p s' = Function.update (storeFn p s) (b, i) v := by
  funext l
  by_cases hl : l = (b, i)
  · subst hl
    simp [storeFn, Store.read_of_write_eq_some h]
  · rw [Function.update_of_ne hl]
    have : l.1 ≠ b ∨ l.2 ≠ i := by
      by_contra hc
      exact hl (Prod.ext (not_not.mp (not_or.mp hc).1) (not_not.mp (not_or.mp hc).2))
    simp only [storeFn, Store.read_of_write_eq_some_of_ne h this]

omit [AddMonoid C] in
/-- The run of one operation: a successful run writes the operation's word on the word
function of the start into the cell it writes and keeps the tape positions. -/
theorem ScalarOp.write_of_run_eq_some {p : P} {o : ScalarOp ℕ ℕ} {s s' : Store P K}
    {pos pos' : Dist → ℕ} (h : (o.toInstr p).run I.sem I.tape s pos = some (s', pos')) :
    s.write p o.dst.1 o.dst.2 (o.value I.sem p (storeFn p s)) = some s' ∧ pos' = pos := by
  have tail : ∀ {v : K}, (s.write p o.dst.1 o.dst.2 v).map (fun s'' => (s'', pos)) =
      some (s', pos') → s.write p o.dst.1 o.dst.2 v = some s' ∧ pos' = pos := fun hm => by
    obtain ⟨s'', hw', he⟩ := Option.map_eq_some_iff.mp hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨hw', rfl⟩
  cases o with
  | lit d q | litIdx d q =>
    obtain ⟨v, hv, hw⟩ := Option.bind_eq_some_iff.mp h
    simpa [ScalarOp.value, hv] using tail hw
  | bin op d x y =>
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, hw⟩ := Option.bind_eq_some_iff.mp h
    simpa [ScalarOp.value, Cell.loc, storeFn_of_read ha, storeFn_of_read hb, hv] using tail hw
  | un op d x =>
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, hv, hw⟩ := Option.bind_eq_some_iff.mp h
    simpa [ScalarOp.value, Cell.loc, storeFn_of_read ha, hv] using tail hw
  | copy d x =>
    obtain ⟨a, ha, hw⟩ := Option.bind_eq_some_iff.mp h
    simpa [ScalarOp.value, Cell.loc, storeFn_of_read ha] using tail hw

omit [AddMonoid C] in
/-- One operation succeeds when the cells it reads hold words, it succeeds on the word
function and the cell it writes is writable. -/
theorem ScalarOp.exists_run_eq_some {p : P} {o : ScalarOp ℕ ℕ} {s : Store P K} (pos : Dist → ℕ)
    (hsrc : ∀ l ∈ o.srcs, ∃ v, s.read p l.1 l.2 = some v) (hok : o.Ok I.sem p (storeFn p s))
    (hw : Writable s p o.dst.1 o.dst.2 1) :
    ∃ r, (o.toInstr p).run I.sem I.tape s pos = some r := by
  obtain ⟨len, hl, hlt⟩ := hw 0 Nat.one_pos
  have hwr : ∀ v, ∃ s', s.write p o.dst.1 o.dst.2 v = some s' := fun v =>
    Store.exists_write_eq_some_of_getElem?_shape v hl (by omega)
  have rd : ∀ c : Cell ℕ ℕ, c.loc ∈ o.srcs → s.read p c.buf c.idx.eval = some (storeFn p s c.loc) :=
    fun c hc => read_eq_some_storeFn (hsrc c.loc hc)
  cases o with
  | lit d q | litIdx d q =>
    obtain ⟨v, hv⟩ := hok
    obtain ⟨s', hs'⟩ := hwr v
    simp only [ScalarOp.dst, Cell.loc] at hs'
    exact ⟨(s', pos), by simp only [ScalarOp.toInstr, Instr.run, hv, Option.bind_some, hs',
      Option.map_some]⟩
  | bin op d x y =>
    obtain ⟨v, hv⟩ := hok
    obtain ⟨s', hs'⟩ := hwr v
    simp only [ScalarOp.dst, Cell.loc] at hs'
    exact ⟨(s', pos), by simp only [ScalarOp.toInstr, Instr.run, rd x (by simp [ScalarOp.srcs]),
      rd y (by simp [ScalarOp.srcs]), Option.bind_some, hv, hs', Option.map_some]⟩
  | un op d x =>
    obtain ⟨v, hv⟩ := hok
    obtain ⟨s', hs'⟩ := hwr v
    simp only [ScalarOp.dst, Cell.loc] at hs'
    exact ⟨(s', pos), by simp only [ScalarOp.toInstr, Instr.run, rd x (by simp [ScalarOp.srcs]),
      Option.bind_some, hv, hs', Option.map_some]⟩
  | copy d x =>
    obtain ⟨s', hs'⟩ := hwr (storeFn p s x.loc)
    simp only [ScalarOp.dst, Cell.loc] at hs'
    exact ⟨(s', pos), by simp only [ScalarOp.toInstr, Instr.run, rd x (by simp [ScalarOp.srcs]),
      Option.bind_some, Cell.loc, hs', Option.map_some]⟩

omit [Inhabited K] in
/-- A straight-line block composes with what follows. -/
theorem executionComposable_scalarBlock (p : P) (ops : List (ScalarOp ℕ ℕ)) :
    ExecutionComposable I (scalarBlock (ι := ι) p ops) := by
  induction ops with
  | nil => exact (routineSpec_pure (m := .liberal) (pre := fun _ => True) (fp := [])).composable
  | cons o os ih => exact (executionComposable_ins _).bind ih

omit [AddMonoid C] [Inhabited K] in
/-- Two different cells form disjoint one-cell blocks. -/
theorem blockDisjoint_cell_of_ne {l d : Loc} (h : l ≠ d) :
    blockDisjoint (l.1, l.2, 1) (d.1, d.2, 1) = true := by
  rw [blockDisjoint_iff]
  by_cases h1 : l.1 = d.1
  · have h2 : l.2 ≠ d.2 := fun h2 => h (Prod.ext h1 h2)
    dsimp only
    omega
  · exact Or.inl h1

omit [AddMonoid C] [Inhabited K] in
/-- A cell that a list of operations does not write is unchanged by a modification of its
footprint. -/
theorem read_eq_of_modifies_ops {p : P} {ops : List (ScalarOp ℕ ℕ)} {s s' : Store P K}
    (hm : Modifies (opsFootprint ops) s s') {l : Loc} (hl : l ∉ dstLocs ops) :
    s'.read p l.1 l.2 = s.read p l.1 l.2 := by
  refine hm.2 p l.1 l.2 fun x hx => ?_
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
  exact blockDisjoint_cell_of_ne fun h => hl (List.mem_map.mpr ⟨o, ho, h.symm⟩)

/-- A successful run of a straight-line block: it modifies the cells it writes, each of
which then holds its word, the word function afterwards is the evaluation of the list on the
word function before, the count rises by one charge per operation and the tape positions are
kept. -/
private theorem post_of_exec_scalarBlock {p : P} {ops : List (ScalarOp ℕ ℕ)} {st st' : St P K C}
    (h : exec I (scalarBlock (ι := ι) p ops).run st = some st') :
    Modifies (opsFootprint ops) st.store st'.store ∧
      (∀ l ∈ dstLocs ops, st'.store.read p l.1 l.2 = some (storeFn p st'.store l)) ∧
      storeFn p st'.store = evalOps I.sem p ops (storeFn p st.store) ∧
      Costs (ops.map fun o => I.charge (o.toInstr p).kind).sum st st' ∧ PosKept st st' := by
  induction ops generalizing st with
  | nil =>
    cases h
    exact ⟨.refl _ _, by simp [dstLocs], rfl, (Costs.refl _), rfl⟩
  | cons o os ih =>
    change (exec I (.instr (o.toInstr p)) st).bind (exec I (scalarBlock p os).run) = _ at h
    obtain ⟨st₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
    rw [exec_instr] at h₁
    obtain ⟨⟨s₁, pos₁⟩, hr, rfl⟩ := Option.map_eq_some_iff.mp h₁
    obtain ⟨hw, rfl⟩ := ScalarOp.write_of_run_eq_some hr
    obtain ⟨hm, hdst, hfn, hc, hpos⟩ := ih h
    refine ⟨(Modifies.of_write hw).trans hm, fun l hl => ?_, ?_, ?_, hpos⟩
    · by_cases hin : l ∈ dstLocs os
      · exact hdst l hin
      · rcases List.mem_cons.mp hl with rfl | hl
        · rw [read_eq_of_modifies_ops hm hin, Store.read_of_write_eq_some hw]
          simp [storeFn, read_eq_of_modifies_ops hm hin, Store.read_of_write_eq_some hw]
        · exact absurd hl hin
    · rw [hfn, storeFn_eq_update_of_write hw]
      rfl
    · simpa [Costs, add_assoc] using hc

/-- A straight-line block succeeds when every cell it reads holds a word when read, every
operation succeeds along the evaluation and every cell it writes is writable. -/
theorem exists_exec_scalarBlock {p : P} {ops : List (ScalarOp ℕ ℕ)} {st : St P K C}
    (hdef : OpsDefined ops fun l => ∃ v, st.store.read p l.1 l.2 = some v)
    (hok : OpsOk I.sem p ops (storeFn p st.store))
    (hw : WritableBlocks st.store p (opsFootprint ops)) :
    ∃ st', exec I (scalarBlock (ι := ι) p ops).run st = some st' := by
  induction ops generalizing st with
  | nil => exact ⟨st, rfl⟩
  | cons o os ih =>
    obtain ⟨⟨s₁, pos₁⟩, hr⟩ := ScalarOp.exists_run_eq_some st.pos hdef.1 hok.1
      (hw _ List.mem_cons_self)
    obtain ⟨hw₁, rfl⟩ := ScalarOp.write_of_run_eq_some hr
    have hm := Modifies.of_write hw₁
    have hdef₁ : OpsDefined os fun l => ∃ v, s₁.read p l.1 l.2 = some v := by
      refine hdef.2.mono fun l hl => ?_
      rcases hl with rfl | ⟨v, hv⟩
      · exact ⟨_, Store.read_of_write_eq_some hw₁⟩
      · by_cases hld : l = o.dst
        · exact ⟨_, hld ▸ Store.read_of_write_eq_some hw₁⟩
        · exact ⟨v, (hm.2 p l.1 l.2 fun x hx => by
            rw [List.mem_singleton.mp hx]; exact blockDisjoint_cell_of_ne hld).trans hv⟩
    have hok₁ : OpsOk I.sem p os (storeFn p s₁) := by
      rw [storeFn_eq_update_of_write hw₁]
      exact hok.2
    obtain ⟨st', h'⟩ := ih
      (st := { st with store := s₁, cnt := st.cnt + I.charge (o.toInstr p).kind }) hdef₁ hok₁
      fun x hx => (hw x (.tail _ hx)).of_modifies hm
    refine ⟨st', ?_⟩
    change (exec I (.instr (o.toInstr p)) st).bind (exec I (scalarBlock p os).run) = _
    rw [exec_instr, hr]
    exact h'

/-- **A straight-line block** as a routine specification, in every mode: the block modifies the
cells it writes (`NLAlib.Computation.opsFootprint`), each of which then holds the word of the
evaluation of the list on the word function before (`NLAlib.Computation.evalOps`,
`NLAlib.Computation.storeFn`), the word function afterwards is that evaluation, the count rises by
one charge per operation and the tape positions are kept. The liberal mode needs nothing; the
total mode needs every cell the block reads to hold a word when it is read
(`NLAlib.Computation.OpsDefined`), every operation to succeed along the evaluation
(`NLAlib.Computation.OpsOk`) and every cell it writes writable. Every index enters through its
value only. -/
theorem spec_scalarBlock (m : Mode) (p : P) (ops : List (ScalarOp ℕ ℕ)) :
    RoutineSpec m I (fun st => m.Needs ((OpsDefined ops fun l => ∃ v, st.store.read p l.1 l.2 =
        some v) ∧ OpsOk I.sem p ops (storeFn p st.store) ∧
        WritableBlocks st.store p (opsFootprint ops)))
      (scalarBlock (ι := ι) p ops) (opsFootprint ops) fun st st' =>
        (∀ l ∈ dstLocs ops,
          st'.store.read p l.1 l.2 = some (evalOps I.sem p ops (storeFn p st.store) l)) ∧
        storeFn p st'.store = evalOps I.sem p ops (storeFn p st.store) ∧
        Costs (ops.map fun o => I.charge (o.toInstr p).kind).sum st st' ∧ PosKept st st' := by
  refine ⟨executionComposable_scalarBlock p ops, Triple.of_exec (fun st hst =>
    hst.mono fun h => exists_exec_scalarBlock h.1 h.2.1 h.2.2) fun st st' _ h => ?_⟩
  obtain ⟨hm, hdst, hfn, hc, hpos⟩ := post_of_exec_scalarBlock h
  exact ⟨hm, fun l hl => hfn ▸ hdst l hl, hfn, hc, hpos⟩

end Run

/-! ### Total word arithmetic -/

section Total

variable {P K : Type}

/-- **Total word arithmetic** at tag `p`: addition, subtraction, multiplication and negation never
fail. The standard model with every value in range gives it
(`NLAlib.Computation.IsRelErrSem.wordTotal`). -/
structure WordTotal (sem : ScalarSem P K) (p : P) : Prop where
  /-- Addition succeeds. -/
  add : ∀ x y, ∃ v, sem.bin p .add x y = some v
  /-- Subtraction succeeds. -/
  sub : ∀ x y, ∃ v, sem.bin p .sub x y = some v
  /-- Multiplication succeeds. -/
  mul : ∀ x y, ∃ v, sem.bin p .mul x y = some v
  /-- Negation succeeds. -/
  neg : ∀ x, ∃ v, sem.un p .neg x = some v

/-- The standard model with every value in range is total on addition, subtraction,
multiplication and negation. -/
theorem IsRelErrSem.wordTotal {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    {sem : ScalarSem P K} (h : IsRelErrSem u dec safe sem) {p : P} (hs : ∀ x, safe p x) :
    WordTotal sem p where
  add x y := h.bin_ok p .add x y (by simp [BinOp.IsArith]) (by simp) (hs _)
  sub x y := h.bin_ok p .sub x y (by simp [BinOp.IsArith]) (by simp) (hs _)
  mul x y := h.bin_ok p .mul x y (by simp [BinOp.IsArith]) (by simp) (hs _)
  neg x := (h.neg p x).imp fun _ h => h.1

/-- The operations that cannot fail under total word arithmetic: additions, subtractions,
multiplications, negations and copies. -/
def ScalarOp.IsPlain : ScalarOp ℕ ℕ → Prop
  | .bin op _ _ _ => op = .add ∨ op = .sub ∨ op = .mul
  | .un op _ _ => op = .neg
  | .copy _ _ => True
  | _ => False

variable [Inhabited K]

/-- Plain operations succeed under total word arithmetic, on every word function. -/
theorem opsOk_of_plain {sem : ScalarSem P K} {p : P} (h : WordTotal sem p)
    {ops : List (ScalarOp ℕ ℕ)} (hops : ∀ o ∈ ops, o.IsPlain) (g : Loc → K) :
    OpsOk sem p ops g := by
  induction ops generalizing g with
  | nil => trivial
  | cons o os ih =>
    refine ⟨?_, ih (fun o' ho' => hops o' (.tail _ ho')) _⟩
    have ho := hops o List.mem_cons_self
    cases o with
    | bin op d x y =>
      rcases ho with rfl | rfl | rfl
      · exact h.add _ _
      · exact h.sub _ _
      · exact h.mul _ _
    | un op d x =>
      obtain rfl := ho
      exact h.neg _
    | copy d s => trivial
    | lit | litIdx => exact absurd ho id

end Total

end NLAlib.Computation
