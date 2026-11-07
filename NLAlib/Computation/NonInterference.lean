/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Compile
public import NLAlib.Computation.FirstOrder

/-!
# Non-interference: a run depends on the data only through its queries

The run of a statement reads four parts of an interpretation that carry data: the oracles, the
kernels, the tapes and the read-only data. Each is read at one place of
`NLAlib.Computation.exec`: an oracle call reads the oracle on the block it read from the store, a
kernel call reads the kernel on the blocks it read, a draw reads the tape of its distribution at
the current position, and a read-only read reads the data at its index. These are the **queries**
of the run (`NLAlib.Computation.Query`), and `NLAlib.Computation.Stmt.queries` collects them along
the run: a sequence adds the queries of its second part from the state after the first, a loop
and a `whileFuel` loop add those of each iteration from the state it starts in, and an index
binder those of its body at the clamped value it binds. Every other field of an interpretation
(the value semantics, the charge, the oracle heights, the widths, the kernel shapes and the size
of the read-only data) is its shape (`NLAlib.Computation.Interp.SameShape`).

The theorem (`NLAlib.Computation.exec_eq_of_agreeOn`): two interpretations of the same shape that
give the same answers on every query the run under the first makes give the same run, so the
same final state, store, tape positions, counts and memory, or the same failure. It holds for
every constructor, kernel calls and index binders included, and for every distribution of the
tape, `Dist.uniform` included. The first-order and program forms follow by the bridge
`NLAlib.Computation.FStmt.exec_eq_exec_toStmt`; with the size of the read-only data in the shape,
so does running within a budget. The no-query end of the theorem, for the oracle, is
`NLAlib.Computation.exec_eq_of_exec_eq_some_of_cnt_load_le`, which this file generalises to runs
that make queries, and to the kernels, the tapes and the read-only data.

Design:
`docs/design/Computation-Hardening.md` (§1.1, GEN).

## Main definitions

* `NLAlib.Computation.Query`: a query of a run.
* `NLAlib.Computation.Interp.AgreeOn`, `NLAlib.Computation.Interp.SameShape`: the same answers on
  a set of queries, and the same data-free part.
* `NLAlib.Computation.Stmt.queries`, `NLAlib.Computation.FStmt.queries`,
  `NLAlib.Computation.Prog.queries`: the queries of a run.

## Main results

* `NLAlib.Computation.exec_eq_of_agreeOn`: non-interference for statements.
* `NLAlib.Computation.FStmt.exec_eq_of_agreeOn`, `NLAlib.Computation.Prog.exec_eq_of_agreeOn`:
  for first-order statements and programs.
* `NLAlib.Computation.Prog.runsWithin_iff_of_agreeOn`: running within a budget.
-/

@[expose] public section

namespace NLAlib.Computation

/-! ### Queries -/

/-- A query a run makes of the parts of an interpretation that carry data. -/
inductive Query (ι K : Type) where
  /-- An oracle call: oracle `o` on the block `X` of `cols` columns read from the store. -/
  | oracle (o : ι) (cols : ℕ) (X : Array K)
  /-- A kernel call: kernel `o` at the dimensions `ds` on the blocks `xs` read from the store. -/
  | kernel (o : ι) (ds : List ℕ) (xs : List (Array K))
  /-- A draw: the tape of `d` at position `i`. -/
  | draw (d : Dist) (i : ℕ)
  /-- A read-only read: entry `i` of the read-only data. -/
  | rom (i : ℕ)

section Interp

variable {P ι K C : Type}

/-- Two interpretations **agree on the queries** `S`: `I'` answers every oracle, kernel, tape and
read-only query in `S` as `I` does. -/
def Interp.AgreeOn (I I' : Interp P ι K C) (S : Set (Query ι K)) : Prop :=
  (∀ o c X, .oracle o c X ∈ S → I'.oracle o c X = I.oracle o c X) ∧
  (∀ o ds xs, .kernel o ds xs ∈ S → I'.kernel o ds xs = I.kernel o ds xs) ∧
  (∀ d i, .draw d i ∈ S → I'.tape d i = I.tape d i) ∧
  (∀ i, .rom i ∈ S → I'.rom i = I.rom i)

/-- Two interpretations have **the same shape**: the same value semantics, charge, oracle
heights, widths, kernel shapes and size of the read-only data; they may differ in the oracles,
the kernels, the tapes and the read-only data. -/
structure Interp.SameShape (I I' : Interp P ι K C) : Prop where
  /-- The same value semantics. -/
  sem : I'.sem = I.sem
  /-- The same charge. -/
  charge : I'.charge = I.charge
  /-- The same oracle heights. -/
  height : I'.height = I.height
  /-- The same widths. -/
  width : I'.width = I.width
  /-- The same kernel shapes. -/
  kshape : I'.kshape = I.kshape
  /-- The same size of the read-only data (read by the memory clause of a budget, not by the
  run). -/
  romSize : I'.romSize = I.romSize

/-- Agreement on a set of queries is agreement on every subset. -/
theorem Interp.AgreeOn.mono {I I' : Interp P ι K C} {S T : Set (Query ι K)} (h : I.AgreeOn I' S)
    (hT : T ⊆ S) : I.AgreeOn I' T :=
  ⟨fun o c X hq => h.1 o c X (hT hq), fun o ds xs hq => h.2.1 o ds xs (hT hq),
    fun d i hq => h.2.2.1 d i (hT hq), fun i hq => h.2.2.2 i (hT hq)⟩

/-- Agreement on a union is agreement on both parts. -/
theorem Interp.agreeOn_union {I I' : Interp P ι K C} {S T : Set (Query ι K)} :
    I.AgreeOn I' (S ∪ T) ↔ I.AgreeOn I' S ∧ I.AgreeOn I' T :=
  ⟨fun h => ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩, fun h =>
    ⟨fun o c X hq => hq.elim (h.1.1 o c X) (h.2.1 o c X),
      fun o ds xs hq => hq.elim (h.1.2.1 o ds xs) (h.2.2.1 o ds xs),
      fun d i hq => hq.elim (h.1.2.2.1 d i) (h.2.2.2.1 d i),
      fun i hq => hq.elim (h.1.2.2.2 i) (h.2.2.2.2 i)⟩⟩

end Interp

/-- The queries of a fold of partial steps: the queries `q a x` of each step from the state `a` it
starts in, as long as the steps succeed. -/
def foldlMQueries {σ α Q : Type} (f : σ → α → Option σ) (q : σ → α → Set Q) :
    List α → σ → Set Q
  | [], _ => ∅
  | x :: l, a => q a x ∪ (f a x).elim ∅ (foldlMQueries f q l)

/-- Two folds of partial steps agree if their steps agree wherever a predicate, inherited by
subsets, holds of the queries of the step; and the predicate holds of the queries of the
fold. -/
theorem foldlM_eq_of_foldlMQueries {σ α Q : Type} {f f' : σ → α → Option σ} {q : σ → α → Set Q}
    {R : Set Q → Prop} (hR : ∀ {S T}, R S → T ⊆ S → R T)
    (hf : ∀ a x, R (q a x) → f' a x = f a x) :
    ∀ (l : List α) (a : σ), R (foldlMQueries f q l a) → l.foldlM f' a = l.foldlM f a
  | [], _, _ => rfl
  | x :: l, a, h => by
    rw [List.foldlM_cons, List.foldlM_cons, hf a x (hR h Set.subset_union_left)]
    rcases hfa : f a x with _ | b
    · rfl
    · refine foldlM_eq_of_foldlMQueries hR hf l b (hR h ?_)
      change _ ⊆ q a x ∪ (f a x).elim ∅ (foldlMQueries f q l)
      rw [hfa]
      exact Set.subset_union_right

section Exec

variable {P ι K C : Type} [DecidableEq P]

/-- The queries of one instruction at the tape positions `pos`: a draw from `d` queries the tape
of `d` at `pos d`; no other instruction queries anything. -/
def Instr.queries {ι K : Type} : Instr P ℕ ℕ → (Dist → ℕ) → Set (Query ι K)
  | .draw _ d _, pos => {.draw d (pos d)}
  | _, _ => ∅

/-- The blocks a kernel call reads: `NLAlib.Computation.Interp.kcallStore` up to the call of the
kernel, `none` if the call fails before it. -/
def Interp.kcallReads (I : Interp P ι K C) (o : ι) (p : P) (ds : List ℕ)
    (ins outs : List (ℕ × ℕ)) (s : Store P K) : Option (List (Array K)) :=
  if ins.length = (I.kshape o ds).1.length ∧ outs.length = (I.kshape o ds).2.length ∧
      (kcallBlocks outs (I.kshape o ds).2).Pairwise (fun x y => blockDisjoint x y = true) ∧
      ∀ x ∈ kcallBlocks outs (I.kshape o ds).2, ∀ y ∈ kcallBlocks ins (I.kshape o ds).1,
        blockDisjoint x y = true then
    s.readBlocks p (kcallBlocks ins (I.kshape o ds).1)
  else none

/-- A kernel call is its reads, then the kernel on the blocks read, then the writes. -/
theorem Interp.kcallStore_eq_bind_kcallReads (I : Interp P ι K C) (o : ι) (p : P) (ds : List ℕ)
    (ins outs : List (ℕ × ℕ)) (s : Store P K) :
    I.kcallStore o p ds ins outs s = (I.kcallReads o p ds ins outs s).bind fun xs =>
      (I.kernel o ds xs).bind fun ys =>
        s.writeBlocks p (kcallBlocks outs (I.kshape o ds).2) ys := by
  unfold Interp.kcallStore Interp.kcallReads
  split_ifs <;> rfl

variable [AddMonoid C] (I : Interp P ι K C)

/-- **The queries of the run** of `s` from `st` under `I`, along `NLAlib.Computation.exec`: a
draw queries the tape at the current position, an oracle call the oracle on the block it read, a
kernel call the kernel on the blocks it read, a read-only read the data at its index. A sequence
adds the queries of its second part from the state after the first, an allocation, a named
kernel and a conditional those of the body or branch run, a loop and a `whileFuel` loop those of
each iteration from the state it starts in, and an index binder those of its body at the clamped
value. -/
def Stmt.queries : Stmt P ι ℕ ℕ → St P K C → Set (Query ι K)
  | .skip, _ => ∅
  | .seq s t, st => s.queries st ∪ (exec I s st).elim ∅ t.queries
  | .instr i, st => i.queries st.pos
  | .apply o p dst dOff src sOff cols, st =>
      if dst ≠ src ∨ dOff.eval + I.height o * cols.eval ≤ sOff.eval ∨
          sOff.eval + I.height o * cols.eval ≤ dOff.eval then
        (st.store.readBlock p src sOff.eval (I.height o * cols.eval)).elim ∅ fun X =>
          {.oracle o cols.eval X}
      else ∅
  | .rom _ _ i, _ => {.rom i.eval}
  | .alloc p len body, st =>
      (body st.store.size).queries { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) }
  | .loop n body, st =>
      foldlMQueries (fun st i => exec I (body i) st) (fun st i => (body i).queries st)
        (List.range n.eval) st
  | .whileFuel fuel p c x y body, st =>
      foldlMQueries (fun (s : St P K C × Bool) _ =>
          if s.2 then (cmpStep I p c x y s.1).bind fun r =>
            if r.1 then (exec I body r.2).map fun st' => (st', true) else some (r.2, false)
          else some s)
        (fun s _ => if s.2 then (cmpStep I p c x y s.1).elim ∅ fun r =>
            if r.1 then body.queries r.2 else ∅
          else ∅)
        (List.range fuel.eval) (st, true)
  | .ite p c x y t e, st => (cmpStep I p c x y st).elim ∅ fun r =>
      if r.1 then t.queries r.2 else e.queries r.2
  | .named _ _ body, st => body.queries st
  | .kcall o p dims ins outs, st =>
      (I.kcallReads o p (dims.map IExp.eval) (ins.map fun x => (x.1, x.2.eval))
        (outs.map fun x => (x.1, x.2.eval)) st.store).elim ∅ fun xs =>
          {.kernel o (dims.map IExp.eval) xs}
  | .bindIdx p x bound body, st => (toNatStep I p x st).elim ∅ fun r =>
      (body (min r.1 bound.eval)).queries r.2

/-! ### Non-interference -/

variable {I} {I' : Interp P ι K C}

omit [DecidableEq P] [AddMonoid C] in
/-- An instruction runs the same under two tapes that agree at the position it draws from. -/
theorem Instr.run_eq_of_agreeOn [DecidableEq P] (hI : I.SameShape I') (i : Instr P ℕ ℕ)
    (s : Store P K) (pos : Dist → ℕ) (h : I.AgreeOn I' (i.queries pos)) :
    i.run I'.sem I'.tape s pos = i.run I.sem I.tape s pos := by
  rw [hI.sem]
  cases i with
  | draw p d dst => simp only [Instr.run, h.2.2.1 d (pos d) rfl]
  | _ => rfl

omit [DecidableEq P] in
/-- A comparison runs the same under interpretations of the same shape. -/
theorem cmpStep_eq_of_sameShape [DecidableEq P] (hI : I.SameShape I') (p : P) (c : CmpOp)
    (x y : Cell ℕ ℕ) (st : St P K C) : cmpStep I' p c x y st = cmpStep I p c x y st := by
  simp only [cmpStep, hI.sem, hI.charge]

omit [DecidableEq P] in
/-- A conversion to an index runs the same under interpretations of the same shape. -/
theorem toNatStep_eq_of_sameShape [DecidableEq P] (hI : I.SameShape I') (p : P) (x : Cell ℕ ℕ)
    (st : St P K C) : toNatStep I' p x st = toNatStep I p x st := by
  simp only [toNatStep, hI.sem, hI.charge]

omit [AddMonoid C] in
/-- A kernel call runs the same under interpretations of the same shape whose kernels agree on
the blocks it reads. -/
theorem Interp.kcallStore_eq_of_agreeOn (hI : I.SameShape I') (o : ι) (p : P) (ds : List ℕ)
    (ins outs : List (ℕ × ℕ)) (s : Store P K)
    (h : I.AgreeOn I' ((I.kcallReads o p ds ins outs s).elim ∅ fun xs => {.kernel o ds xs})) :
    I'.kcallStore o p ds ins outs s = I.kcallStore o p ds ins outs s := by
  have hr : I'.kcallReads o p ds ins outs s = I.kcallReads o p ds ins outs s := by
    simp only [Interp.kcallReads, hI.kshape]
  rw [Interp.kcallStore_eq_bind_kcallReads, Interp.kcallStore_eq_bind_kcallReads, hr, hI.kshape]
  rcases hxs : I.kcallReads o p ds ins outs s with _ | xs
  · rfl
  · rw [hxs] at h
    simp only [Option.bind_some, h.2.1 o ds xs rfl]

/-- Non-interference: two interpretations of the same shape (the same value semantics,
charge, oracle heights, widths, kernel shapes and size of the read-only data) that answer every
query of the run of `s` from `st` under the first in the same way give the same run: the same
final state (store, tape positions, counts and memory) or the same failure. The oracles, kernels,
tapes and read-only data enter the run only through its queries. It generalises
`NLAlib.Computation.exec_eq_of_exec_eq_some_of_cnt_load_le`, the case of a run with no oracle
query. No printed source. -/
theorem exec_eq_of_agreeOn (hI : I.SameShape I') :
    ∀ (s : Stmt P ι ℕ ℕ) (st : St P K C), I.AgreeOn I' (s.queries I st) →
      exec I' s st = exec I s st
  | .skip, _, _ => rfl
  | .seq s t, st, h => by
    rw [Stmt.queries, Interp.agreeOn_union] at h
    rw [exec_seq, exec_seq, exec_eq_of_agreeOn hI s st h.1]
    rcases hs : exec I s st with _ | st₁
    · rfl
    · rw [hs] at h
      exact exec_eq_of_agreeOn hI t st₁ h.2
  | .instr i, st, h => by
    rw [exec_instr, exec_instr, Instr.run_eq_of_agreeOn hI i _ _ h, hI.charge]
  | .apply o p dst dOff src sOff cols, st, h => by
    rw [Stmt.queries] at h
    rw [exec, exec, hI.height, hI.charge]
    split_ifs at h ⊢ with hd
    · rcases hX : st.store.readBlock p src sOff.eval (I.height o * cols.eval) with _ | X
      · rfl
      · rw [hX] at h
        simp only [Option.bind_some, h.1 o cols.eval X rfl]
    · rfl
  | .rom p dst i, st, h => by
    rw [exec, exec, h.2.2.2 i.eval rfl, hI.charge]
  | .alloc p len body, st, h => by
    rw [exec_alloc, exec_alloc, hI.width]
    exact congrArg _ (exec_eq_of_agreeOn hI (body st.store.size) _ h)
  | .loop n body, st, h => by
    rw [exec_loop, exec_loop]
    exact foldlM_eq_of_foldlMQueries (fun h hT => Interp.AgreeOn.mono h hT)
      (fun a i ha => exec_eq_of_agreeOn hI (body i) a ha) _ st h
  | .whileFuel fuel p c x y body, st, h => by
    rw [exec, exec]
    rw [foldlM_eq_of_foldlMQueries (fun h hT => Interp.AgreeOn.mono h hT) (fun a _ ha => ?_) _ _
      h]
    split_ifs at ha ⊢
    · rw [cmpStep_eq_of_sameShape hI]
      rcases hr : cmpStep I p c x y a.1 with _ | r
      · rfl
      · rw [hr] at ha
        simp only [Option.elim_some] at ha
        simp only [Option.bind_some]
        split_ifs at ha ⊢
        · rw [exec_eq_of_agreeOn hI body r.2 ha]
        · rfl
    · rfl
  | .ite p c x y t e, st, h => by
    rw [Stmt.queries] at h
    rw [exec_ite, exec_ite, cmpStep_eq_of_sameShape hI]
    rcases hr : cmpStep I p c x y st with _ | r
    · rfl
    · rw [hr] at h
      simp only [Option.elim_some] at h
      simp only [Option.bind_some]
      split_ifs at h ⊢
      · exact exec_eq_of_agreeOn hI t r.2 h
      · exact exec_eq_of_agreeOn hI e r.2 h
  | .named _ _ body, st, h => by
    rw [exec_named, exec_named]
    exact exec_eq_of_agreeOn hI body st h
  | .kcall o p dims ins outs, st, h => by
    rw [exec, exec, Interp.kcallStore_eq_of_agreeOn hI _ _ _ _ _ _ h, hI.charge]
  | .bindIdx p x bound body, st, h => by
    rw [Stmt.queries] at h
    rw [exec_bindIdx, exec_bindIdx, toNatStep_eq_of_sameShape hI]
    rcases hr : toNatStep I p x st with _ | r
    · rfl
    · rw [hr] at h
      exact exec_eq_of_agreeOn hI (body (min r.1 bound.eval)) r.2 h

end Exec

/-! ### First-order statements and programs -/

section FirstOrder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C)

/-- The queries of the run of a first-order statement in the environment of handles `ρB` and of
index values `ρI`: those of the run of its instantiation. -/
def FStmt.queries {nb ni : ℕ} (s : FStmt P ι nb ni) (ρB : Fin nb → ℕ) (ρI : Fin ni → ℕ)
    (st : St P K C) : Set (Query ι K) :=
  (s.toStmt ρB fun v => .const (ρI v)).queries I st

/-- The queries of the run of a program at the sizes $N$ and $n$. -/
def Prog.queries {r b : ℕ} (prog : Prog P ι r b) (N : ℕ) (n : Fin r → ℕ) (st : St P K C) :
    Set (Query ι K) :=
  FStmt.queries I prog (fun j => (j : ℕ)) (Fin.cons N n) st

variable {I} {I' : Interp P ι K C}

/-- Non-interference for first-order statements: two interpretations of the same shape that
agree on the queries of the run of `s` under the first give the same run. No printed source. -/
theorem FStmt.exec_eq_of_agreeOn (hI : I.SameShape I') {nb ni : ℕ} (s : FStmt P ι nb ni)
    (ρB : Fin nb → ℕ) (ρI : Fin ni → ℕ) (st : St P K C) (h : I.AgreeOn I' (s.queries I ρB ρI st)) :
    s.exec I' ρB ρI st = s.exec I ρB ρI st := by
  have e := fun J : Interp P ι K C => FStmt.exec_eq_exec_toStmt J s ρB (fun v => .const (ρI v)) st
  simp only [IExp.eval_const] at e
  rw [e I', e I]
  exact Computation.exec_eq_of_agreeOn hI _ st h

/-- Non-interference for programs: two interpretations of the same shape that agree on the
queries of the run of a program under the first give the same run. No printed source. -/
theorem Prog.exec_eq_of_agreeOn (hI : I.SameShape I') {r b : ℕ} (prog : Prog P ι r b) (N : ℕ)
    (n : Fin r → ℕ) (st : St P K C) (h : I.AgreeOn I' (prog.queries I N n st)) :
    prog.exec I' N n st = prog.exec I N n st :=
  FStmt.exec_eq_of_agreeOn hI prog _ _ st h

/-- A program runs within a budget under one of two interpretations of the same shape that agree
on its queries if and only if it does under the other. No printed source. -/
theorem Prog.runsWithin_iff_of_agreeOn [Preorder C] (hI : I.SameShape I') {r b : ℕ}
    (prog : Prog P ι r b) (N : ℕ) (n : Fin r → ℕ) (st₀ : St P K C) (c : C) (m : P → ℕ)
    (Q : St P K C → Prop) (h : I.AgreeOn I' (prog.queries I N n st₀)) :
    prog.RunsWithin I' N n st₀ c m Q ↔ prog.RunsWithin I N n st₀ c m Q := by
  simp only [Prog.RunsWithin, Prog.exec_eq_of_agreeOn hI prog N n st₀ h, hI.romSize]

end FirstOrder

end NLAlib.Computation
