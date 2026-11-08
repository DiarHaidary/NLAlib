/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineFrames
public import NLAlib.Computation.IndexBinder
public import NLAlib.Computation.Loops
public import NLAlib.Computation.Contract
public import NLAlib.Computation.StaticCost
public import NLAlib.Computation.ExecCharge
public import NLAlib.Computation.MatvecRoutine

/-!
# A program logic for runs (scaffold)

Statements for a new `NLAlib/Computation/ProgramLogic.lean` (stage PROG-LOGIC, design note
`docs/design/Computation-ProgramLogic.md`, ids PL1–PL69). The run `NLAlib.Computation.exec` is
deterministic, so its weakest precondition is a definition, not an inductive judgement:
`NLAlib.Computation.Wp m I s Q st` says the run of `s` from `st` ends in a state satisfying `Q`
(mode `total`: it succeeds; mode `liberal`: if it succeeds). A triple
(`NLAlib.Computation.Triple`) relates the start and final states, so frames, counts and the
size of the store are stated against the start state, and a routine specification
(`NLAlib.Computation.Spec`) adds the blocks it may modify (`NLAlib.Computation.Modifies`). The
rules are proved once from the run equations of `NLAlib/Computation/Exec.lean`; a program proof
applies them statement by statement, each step naming the next state.

## Main definitions

* `NLAlib.Computation.Modifies`, `NLAlib.Computation.ReadsOnly`: footprints and read sets.
* `NLAlib.Computation.Mode`, `NLAlib.Computation.Wp`, `NLAlib.Computation.Triple`: the logic.
* `NLAlib.Computation.Spec`, `NLAlib.Computation.RoutineSpec`: routine specifications.
* `NLAlib.Computation.Costs`: an exact count, threaded additively.
* `NLAlib.Computation.IsRoutineSem`: the arithmetic assumptions of a routine, in one record.

## Main results

* `NLAlib.Computation.wp_seq`, `NLAlib.Computation.wp_alloc`, `NLAlib.Computation.wp_ite`,
  `NLAlib.Computation.wp_bindIdx_of_read`, `NLAlib.Computation.wp_kcall`: the statement rules.
* `NLAlib.Computation.Triple.loop`, `NLAlib.Computation.Triple.whileFuel`: invariant rules.
* `NLAlib.Computation.Spec.seq`, `NLAlib.Computation.Spec.frame`,
  `NLAlib.Computation.Spec.alloc`: composition, the frame rule, scoped scratch.
* `NLAlib.Computation.RoutineSpec.wp_bind`: the call rule.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P]

/-! ### Footprints and read sets -/

section Footprint

/-- **`s'` differs from `s` only in the blocks `fp`** (`(handle, offset, length)`): the two stores
have the same shape and every cell disjoint from every block of `fp` reads the same at every
tag. The cell form `blockDisjoint (b, i, 1) x` is the frame form of the kernel contracts. -/
def Modifies (fp : List (ℕ × ℕ × ℕ)) (s s' : Store P K) : Prop :=
  s'.shape = s.shape ∧
    ∀ q b i, (∀ x ∈ fp, blockDisjoint (b, i, 1) x = true) → s'.read q b i = s.read q b i

/-- **A store predicate that reads only the blocks `rs`**: it survives any store that has the
same shape on the buffers of `rs` and reads the same on every cell of `rs`, at every tag. The
block analogue of `NLAlib.Computation.IsFramed`, which reads whole buffers. -/
def ReadsOnly (F : Store P K → Prop) (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ s s', F s → (∀ x ∈ rs, s'.shape[x.1]? = s.shape[x.1]?) →
    (∀ q, ∀ x ∈ rs, ∀ j < x.2.2, s'.read q x.1 (x.2.1 + j) = s.read q x.1 (x.2.1 + j)) → F s'

/-- Every block of `rs` is disjoint from every block of `fp`; with
`NLAlib.Computation.blockDisjoint_iff` the goal is linear arithmetic. -/
def BlocksDisjoint (rs fp : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ x ∈ rs, ∀ y ∈ fp, blockDisjoint x y = true

/-- A store modifies nothing of itself. -/
theorem Modifies.refl (fp : List (ℕ × ℕ × ℕ)) (s : Store P K) : Modifies fp s s := by
  sorry

/-- Footprints in sequence add. -/
theorem Modifies.trans {fp₁ fp₂ : List (ℕ × ℕ × ℕ)} {s s₁ s₂ : Store P K}
    (h₁ : Modifies fp₁ s s₁) (h₂ : Modifies fp₂ s₁ s₂) : Modifies (fp₁ ++ fp₂) s s₂ := by
  sorry

/-- A footprint may be enlarged. -/
theorem Modifies.mono {fp fp' : List (ℕ × ℕ × ℕ)} {s s' : Store P K} (h : Modifies fp s s')
    (hfp : ∀ x ∈ fp, x ∈ fp') : Modifies fp' s s' := by
  sorry

/-- Block writes modify their blocks. -/
theorem Modifies.of_writeBlocks {p : P} {bs : List (ℕ × ℕ × ℕ)} {ys : List (Array K)}
    {s s' : Store P K} (h : s.writeBlocks p bs ys = some s') : Modifies bs s s' := by
  sorry

/-- A block write modifies its block. -/
theorem Modifies.of_writeBlock {p : P} {b o : ℕ} {y : Array K} {s s' : Store P K}
    (h : s.writeBlock p b o y = some s') : Modifies [(b, o, y.size)] s s' := by
  sorry

/-- A kernel call modifies its output blocks. -/
theorem Modifies.of_kcallStore {C : Type} {I : Interp P ι K C} {o : ι} {p : P} {ds : List ℕ}
    {ins outs : List (ℕ × ℕ)} {s s' : Store P K} (h : I.kcallStore o p ds ins outs s = some s') :
    Modifies (kcallBlocks outs (I.kshape o ds).2) s s' := by
  sorry

/-- Scratch on top: a run from the store with a buffer pushed, popped at the end, modifies in
the original store only the blocks it modified below the top. -/
theorem Modifies.pop {fp : List (ℕ × ℕ × ℕ)} {s s' : Store P K} {y : P × Array (Option K)}
    (h : Modifies fp (s.push y) s') : Modifies fp s s'.pop := by
  sorry

/-- **The frame of a read set**: a predicate that reads only `rs` survives a change confined to
blocks disjoint from `rs`. -/
theorem ReadsOnly.of_modifies {F : Store P K → Prop} {rs fp : List (ℕ × ℕ × ℕ)}
    {s s' : Store P K} (hF : ReadsOnly F rs) (h : F s) (hm : Modifies fp s s')
    (hd : BlocksDisjoint rs fp) : F s' := by
  sorry

/-- A conjunction reads the union of the read sets. -/
theorem ReadsOnly.and {F G : Store P K → Prop} {rs ts : List (ℕ × ℕ × ℕ)} (hF : ReadsOnly F rs)
    (hG : ReadsOnly G ts) : ReadsOnly (fun s => F s ∧ G s) (rs ++ ts) := by
  sorry

/-- A read set may be enlarged. -/
theorem ReadsOnly.mono {F : Store P K → Prop} {rs ts : List (ℕ × ℕ × ℕ)} (hF : ReadsOnly F rs)
    (h : ∀ x ∈ rs, x ∈ ts) : ReadsOnly F ts := by
  sorry

/-- A predicate reading only buffers below the top survives pushing a buffer. -/
theorem ReadsOnly.push {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} {s : Store P K}
    (hF : ReadsOnly F rs) (h : F s) (hrs : ∀ x ∈ rs, x.1 < s.size) (y : P × Array (Option K)) :
    F (s.push y) := by
  sorry

/-- A predicate reading only buffers below the top survives popping the top buffer. -/
theorem ReadsOnly.pop {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} {s : Store P K}
    (hF : ReadsOnly F rs) (h : F s) (hrs : ∀ x ∈ rs, x.1 + 1 < s.size) : F s.pop := by
  sorry

/-- One stored cell reads only itself. -/
theorem readsOnly_read (q : P) (b i : ℕ) (v : Option K) :
    ReadsOnly (fun s : Store P K => s.read q b i = v) [(b, i, 1)] := by
  sorry

/-- A writable block reads only itself (its shape). -/
theorem readsOnly_writable (p : P) (b off n : ℕ) :
    ReadsOnly (fun s : Store P K => Writable s p b off n) [(b, off, n)] := by
  sorry

/-- A decoded vector reads only its block. -/
theorem readsOnly_readsDecoded {N : ℕ} (dec : P → K → ℝ) (p : P) (b off : ℕ) (x : Fin N → ℝ) :
    ReadsOnly (fun s : Store P K => ReadsDecoded s dec p b off x) [(b, off, N)] := by
  sorry

/-- A decoded matrix reads only its block. -/
theorem readsOnly_holdsDecoded {N k : ℕ} (dec : P → K → ℝ) (p : P) (b off : ℕ)
    (M : Matrix (Fin N) (Fin k) ℝ) :
    ReadsOnly (fun s : Store P K => HoldsDecoded s dec p b off M) [(b, off, N * k)] := by
  sorry

/-- A buffer-framed precondition survives a change confined to other buffers. -/
theorem IsFramed.of_modifies {pre : Store P K → Prop} {ro : List ℕ} {fp : List (ℕ × ℕ × ℕ)}
    {s s' : Store P K} (hf : IsFramed pre ro) (h : pre s) (hm : Modifies fp s s')
    (hro : ∀ x ∈ fp, x.1 ∉ ro) : pre s' := by
  sorry

end Footprint

/-! ### Modes, weakest preconditions and triples -/

/-- **The mode of a judgement**: `total` asserts that the run succeeds, `liberal` only constrains
a successful run (Dijkstra's weakest liberal precondition). -/
inductive Mode where
  /-- The run succeeds and its final state satisfies the postcondition. -/
  | total
  /-- If the run succeeds, its final state satisfies the postcondition. -/
  | liberal

/-- What a mode needs of the arithmetic: the total mode needs `A`, the liberal mode nothing. A
specification proved for every mode `m` under `m.Needs A` gives, at `liberal`, the refinement
without `A` and, at `total`, success under `A`, from one proof. -/
def Mode.Needs : Mode → Prop → Prop
  | .total, A => A
  | .liberal, _ => True

/-- The outcome `o` of a step satisfies `Q` in mode `m`. -/
def Mode.Sat {α : Type} : Mode → (α → Prop) → Option α → Prop
  | .total, Q, o => ∃ x, o = some x ∧ Q x
  | .liberal, Q, o => ∀ x, o = some x → Q x

/-- A satisfied outcome satisfies a weaker predicate. -/
theorem Mode.Sat.mono {α : Type} {m : Mode} {Q Q' : α → Prop} {o : Option α}
    (h : m.Sat Q o) (hQ : ∀ x, Q x → Q' x) : m.Sat Q' o := by
  sorry

/-- A successful outcome satisfies `Q` iff its value does. -/
theorem Mode.sat_some {α : Type} {m : Mode} {Q : α → Prop} {x : α} :
    m.Sat Q (some x) ↔ Q x := by
  sorry

/-- An outcome in sequence: the bind of the outcome monad. -/
theorem Mode.sat_bind {α β : Type} {m : Mode} {Q : β → Prop} {o : Option α}
    {f : α → Option β} : m.Sat Q (o.bind f) ↔ m.Sat (fun x => m.Sat Q (f x)) o := by
  sorry

/-- An outcome mapped. -/
theorem Mode.sat_map {α β : Type} {m : Mode} {Q : β → Prop} {o : Option α} {f : α → β} :
    m.Sat Q (o.map f) ↔ m.Sat (fun x => Q (f x)) o := by
  sorry

/-- A requirement of the total mode holds in the liberal mode. -/
theorem Mode.needs_liberal (A : Prop) : Mode.liberal.Needs A := trivial

/-- A requirement that holds holds in every mode. -/
theorem Mode.needs_of {A : Prop} (h : A) (m : Mode) : m.Needs A := by
  cases m
  · exact h
  · trivial

/-- **The arithmetic assumptions of a routine**, in one record: the standard model at unit
roundoff `u` with decoding `dec` and safe set `safe`, and exact index arithmetic (integer
literals up to `B`, the conversion to an index the floor). The comparison and literal facts a
routine needs are projections of it. -/
structure IsRoutineSem (u : P → ℝ) (dec : P → K → ℝ) (safe : P → ℝ → Prop) (B : ℕ)
    (sem : ScalarSem P K) : Prop where
  /-- The standard model of rounding. -/
  relErr : IsRelErrSem u dec safe sem
  /-- Exact index arithmetic. -/
  index : IsIndexExactSem dec B sem

variable [AddMonoid C]

/-- A state with its count raised by `c`: the state after a charged step that writes nothing. -/
def St.addCnt (st : St P K C) (c : C) : St P K C := { st with cnt := st.cnt + c }

/-- **The weakest precondition** of `s` for `Q` in mode `m`: the run of `s` from `st` under `I`
ends (`total`: succeeds and ends; `liberal`: if it succeeds, ends) in a state satisfying `Q`. -/
def Wp (m : Mode) (I : Interp P ι K C) (s : Stmt P ι ℕ ℕ) (Q : St P K C → Prop)
    (st : St P K C) : Prop :=
  m.Sat Q (exec I s st)

/-- **A triple** in mode `m`: from every state satisfying `pre`, the run of `s` ends in a state
related to the start by `post`. -/
def Triple (m : Mode) (I : Interp P ι K C) (pre : St P K C → Prop) (s : Stmt P ι ℕ ℕ)
    (post : St P K C → St P K C → Prop) : Prop :=
  ∀ st, pre st → Wp m I s (post st) st

section Core

variable {m : Mode} {I : Interp P ι K C} {s t : Stmt P ι ℕ ℕ} {Q Q' : St P K C → Prop}
  {st : St P K C}

/-- The weakest precondition is monotone in the postcondition. -/
theorem wp_mono (h : Wp m I s Q st) (hQ : ∀ st', Q st' → Q' st') : Wp m I s Q' st := by
  sorry

/-- **The application rule**: a triple gives the weakest precondition of any postcondition its
own implies, at a state satisfying its precondition. -/
theorem Triple.wp_of {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    (h : Triple m I pre s post) (hpre : pre st) (hQ : ∀ st', post st st' → Q st') :
    Wp m I s Q st := by
  sorry

/-- **The rule of consequence.** -/
theorem Triple.conseq {pre pre' : St P K C → Prop} {post post' : St P K C → St P K C → Prop}
    (h : Triple m I pre s post) (hpre : ∀ st, pre' st → pre st)
    (hpost : ∀ st st', pre' st → post st st' → post' st st') : Triple m I pre' s post' := by
  sorry

/-- A total triple is a liberal one. -/
theorem Triple.liberal {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    (h : Triple .total I pre s post) : Triple .liberal I pre s post := by
  sorry

/-- A liberal triple and success give a total triple (the run is deterministic). -/
theorem Triple.total_of_liberal {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    (h : Triple .liberal I pre s post) (hs : ∀ st, pre st → ∃ st', exec I s st = some st') :
    Triple .total I pre s post := by
  sorry

/-- A total triple: the run succeeds. -/
theorem Triple.exists_exec {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    (h : Triple .total I pre s post) (hpre : pre st) :
    ∃ st', exec I s st = some st' ∧ post st st' := by
  sorry

/-- A liberal triple: what a successful run satisfies. -/
theorem Triple.holds_of_exec {pre : St P K C → Prop} {post : St P K C → St P K C → Prop}
    {st' : St P K C} (h : Triple .liberal I pre s post) (hpre : pre st)
    (hrun : exec I s st = some st') : post st st' := by
  sorry

/-! #### Statement rules -/

/-- `skip`. -/
theorem wp_skip : Wp m I .skip Q st ↔ Q st := by
  sorry

/-- **Sequence**: the weakest precondition of `t` is the postcondition of `s`. -/
theorem wp_seq : Wp m I (.seq s t) Q st ↔ Wp m I s (Wp m I t Q) st := by
  sorry

/-- A scalar instruction. -/
theorem wp_instr (i : Instr P ℕ ℕ) :
    Wp m I (.instr i) Q st ↔
      m.Sat (fun r => Q ({ st with store := r.1, pos := r.2, cnt := st.cnt + I.charge i.kind }))
        (i.run I.sem I.tape st.store st.pos) := by
  sorry

/-- **Allocation**: the body runs from the state with the fresh buffer at handle
`st.store.size`, and the postcondition is read after its release. -/
theorem wp_alloc (p : P) (len : IExp ℕ) (body : ℕ → Stmt P ι ℕ ℕ) :
    Wp m I (.alloc p len body) Q st ↔
      Wp m I (body st.store.size) (fun st₂ => Q (st₂.release p len.eval (I.width p)))
        (st.allocate p len.eval (I.width p)) := by
  sorry

/-- **A conditional**, from the comparison step. -/
theorem wp_ite (p : P) (c : CmpOp) (x y : Cell ℕ ℕ) :
    Wp m I (.ite p c x y s t) Q st ↔
      m.Sat (fun r => if r.1 then Wp m I s Q r.2 else Wp m I t Q r.2) (cmpStep I p c x y st) := by
  sorry

/-- A conditional on stored values: with the cells read and compared, the branch taken. -/
theorem wp_ite_of_read {p : P} {c : CmpOp} {x y : Cell ℕ ℕ} {a b : K} {r : Bool}
    (hx : st.store.read p x.buf x.idx.eval = some a)
    (hy : st.store.read p y.buf y.idx.eval = some b) (hr : I.sem.cmp p c a b = some r) :
    Wp m I (.ite p c x y s t) Q st ↔
      if r then Wp m I s Q (st.addCnt (I.charge (.cmp p)))
      else Wp m I t Q (st.addCnt (I.charge (.cmp p))) := by
  sorry

/-- **An index binder** on a stored value: the body runs at every converted value $k$ with the
fact $k \le \mathit{bound}$; the total mode needs the bound. -/
theorem wp_bindIdx_of_read {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {v : K} (hx : st.store.read p x.buf x.idx.eval = some v)
    (h : m.Sat (fun k => m.Needs (k ≤ bound.eval) ∧
      (k ≤ bound.eval → Wp m I (body k) Q (st.addCnt (I.charge (.toNat p)))))
      (I.sem.toNat p v)) :
    Wp m I (.bindIdx p x bound body) Q st := by
  sorry

/-- **A kernel call**: the black box's store, charged once. -/
theorem wp_kcall (o : ι) (p : P) (dims : List (IExp ℕ)) (ins outs : List (ℕ × IExp ℕ)) :
    Wp m I (.kcall o p dims ins outs) Q st ↔
      m.Sat (fun s => Q ({ st with store := s } |>.addCnt
          (I.charge (.kcall p o (dims.map IExp.eval)))))
        (I.kcallStore o p (dims.map IExp.eval) (ins.map fun x => (x.1, x.2.eval))
          (outs.map fun x => (x.1, x.2.eval)) st.store) := by
  sorry

/-- A named kernel runs as its body (the label is transparent to the logic). -/
theorem wp_named (name : String) (args : List (Arg ℕ ℕ)) :
    Wp m I (.named name args s) Q st ↔ Wp m I s Q st := by
  sorry

/-! #### Composite rules -/

/-- **Sequence of triples**: the first routine's output feeds the second (`hmid`), and the
composite postcondition names the intermediate state. -/
theorem Triple.seq {pre pre₂ : St P K C → Prop} {mid post : St P K C → St P K C → Prop}
    (h₁ : Triple m I pre s mid) (h₂ : Triple m I pre₂ t post)
    (hmid : ∀ st st₁, pre st → mid st st₁ → pre₂ st₁) :
    Triple m I pre (.seq s t) fun st st₂ => ∃ st₁, mid st st₁ ∧ post st₁ st₂ := by
  sorry

/-- **A loop with an invariant**: `Inv st₀ k` holds of the state after `k` iterations from
`st₀`, and the body keeps it. -/
theorem Triple.loop {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {pre : St P K C → Prop}
    (Inv : St P K C → ℕ → St P K C → Prop) (h0 : ∀ st, pre st → Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ k < n.eval,
      Triple m I (Inv st₀ k) (body k) fun _ st' => Inv st₀ (k + 1) st') :
    Triple m I pre (.loop n body) fun st₀ st' => Inv st₀ n.eval st' := by
  sorry

/-- **A fueled loop with an invariant**: `Inv st₀ j` holds of the state before the $j$-th test;
a test that holds runs the body to `Inv st₀ (j + 1)`, and in the total mode leaves fuel for the
next test. The final state is the state of a failed test. -/
theorem Triple.whileFuel {fuel : IExp ℕ} {p : P} {c : CmpOp} {x y : Cell ℕ ℕ}
    {body : Stmt P ι ℕ ℕ} {pre : St P K C → Prop} (Inv : St P K C → ℕ → St P K C → Prop)
    (h0 : ∀ st, pre st → m.Needs (0 < fuel.eval) ∧ Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ j st, Inv st₀ j st →
      m.Sat (fun r => r.1 = true → m.Needs (j + 1 < fuel.eval) ∧
        Wp m I body (Inv st₀ (j + 1)) r.2) (cmpStep I p c x y st)) :
    Triple m I pre (.whileFuel fuel p c x y body) fun st₀ st' =>
      ∃ j stj, Inv st₀ j stj ∧ cmpStep I p c x y stj = some (false, st') := by
  sorry

/-- **Scoped scratch**: a body that runs from the state with the fresh buffer at the relative
handle `b` (the size of the store, fixed by the precondition) gives the allocation, its
postcondition read after the release. -/
theorem Triple.alloc {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {b : ℕ}
    {pre pre' : St P K C → Prop} {post post' : St P K C → St P K C → Prop}
    (h : Triple m I pre' (body b) post') (hb : ∀ st, pre st → st.store.size = b)
    (hpre : ∀ st, pre st → pre' (st.allocate p len.eval (I.width p)))
    (hpost : ∀ st st₂, pre st → post' (st.allocate p len.eval (I.width p)) st₂ →
      post st (st₂.release p len.eval (I.width p))) :
    Triple m I pre (.alloc p len body) post := by
  sorry

end Core

/-! ### Builders -/

section Builder

variable {m : Mode} {I : Interp P ι K C} {Q : St P K C → Prop} {st : St P K C}

/-- **A builder in sequence**: a composable prefix, then the rest. -/
theorem wp_run_bind {x : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit}
    (hx : ExecutionComposable I x) :
    Wp m I (x >>= f).run Q st ↔ Wp m I x.run (Wp m I (f ()).run Q) st := by
  sorry

/-- **An allocation in a builder**: the rest of the block runs on the fresh handle. -/
theorem wp_run_allocBind {p : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} :
    Wp m I (Builder.alloc p len >>= f).run Q st ↔
      Wp m I (f st.store.size).run (fun st₂ => Q (st₂.release p len.eval (I.width p)))
        (st.allocate p len.eval (I.width p)) := by
  sorry

/-- The empty builder. -/
theorem wp_run_pure : Wp m I (pure () : Builder P ι ℕ ℕ Unit).run Q st ↔ Q st := by
  sorry

/-- A statement is a composable prefix. -/
theorem executionComposable_stmt (s : Stmt P ι ℕ ℕ) :
    ExecutionComposable I (Builder.stmt s) := by
  sorry

/-- A scalar instruction is a composable prefix. -/
theorem executionComposable_ins (i : Instr P ℕ ℕ) :
    ExecutionComposable I (Builder.ins (ι := ι) i) := by
  sorry

/-- A scope is a composable prefix. -/
theorem executionComposable_scope (x : Builder P ι ℕ ℕ Unit) :
    ExecutionComposable I (Builder.scope x) := by
  sorry

/-- A named kernel is a composable prefix. -/
theorem executionComposable_named (name : String) (args : List (Arg ℕ ℕ))
    (x : Builder P ι ℕ ℕ Unit) : ExecutionComposable I (Builder.named name args x) := by
  sorry

/-- A loop is a composable prefix. -/
theorem executionComposable_forRange (n : IExp ℕ) (body : ℕ → Builder P ι ℕ ℕ Unit) :
    ExecutionComposable I (Builder.forRange n body) := by
  sorry

/-- A conditional is a composable prefix. -/
theorem executionComposable_ifThenElse (p : P) (c : CmpOp) (x y : Cell ℕ ℕ)
    (t e : Builder P ι ℕ ℕ Unit) : ExecutionComposable I (Builder.ifThenElse p c x y t e) := by
  sorry

/-- An index binder is a composable prefix. -/
theorem executionComposable_bindIdx (p : P) (x : Cell ℕ ℕ) (bound : IExp ℕ)
    (body : ℕ → Builder P ι ℕ ℕ Unit) :
    ExecutionComposable I (Builder.bindIdx p x bound body) := by
  sorry

end Builder

/-! ### Routine specifications -/

section Spec

/-- **A routine specification**: a triple whose postcondition also bounds what the run modifies
to the blocks `fp`. Inputs, outputs and scratch are blocks of the footprint or of the
precondition's read sets, so frames and disjointness are linear arithmetic on their offsets. -/
def Spec (m : Mode) (I : Interp P ι K C) (pre : St P K C → Prop) (s : Stmt P ι ℕ ℕ)
    (fp : List (ℕ × ℕ × ℕ)) (post : St P K C → St P K C → Prop) : Prop :=
  Triple m I pre s fun st st' => Modifies fp st.store st'.store ∧ post st st'

/-- **A specified routine**: a builder that composes with what follows and whose run meets a
specification. The analogue of `NLAlib.Computation.IsBlockRoutine` with a postcondition. -/
structure RoutineSpec (m : Mode) (I : Interp P ι K C) (pre : St P K C → Prop)
    (r : Builder P ι ℕ ℕ Unit) (fp : List (ℕ × ℕ × ℕ)) (post : St P K C → St P K C → Prop) :
    Prop where
  /-- The routine composes with the following program. -/
  composable : ExecutionComposable I r
  /-- Its run meets the specification. -/
  spec : Spec m I pre r.run fp post

variable {m : Mode} {I : Interp P ι K C} {s t : Stmt P ι ℕ ℕ} {st : St P K C}
  {pre pre₂ : St P K C → Prop} {post post₂ : St P K C → St P K C → Prop}
  {fp fp₂ : List (ℕ × ℕ × ℕ)}

/-- Consequence for specifications, with a larger footprint. -/
theorem Spec.conseq {pre' : St P K C → Prop} {post' : St P K C → St P K C → Prop}
    {fp' : List (ℕ × ℕ × ℕ)} (h : Spec m I pre s fp post) (hpre : ∀ st, pre' st → pre st)
    (hfp : ∀ x ∈ fp, x ∈ fp') (hpost : ∀ st st', pre' st → post st st' → post' st st') :
    Spec m I pre' s fp' post' := by
  sorry

/-- **Sequence of specifications**: footprints add, the first output feeds the second. -/
theorem Spec.seq (h₁ : Spec m I pre s fp post) (h₂ : Spec m I pre₂ t fp₂ post₂)
    (hmid : ∀ st st₁, pre st → Modifies fp st.store st₁.store → post st st₁ → pre₂ st₁) :
    Spec m I pre (.seq s t) (fp ++ fp₂) fun st st₂ => ∃ st₁, post st st₁ ∧ post₂ st₁ st₂ := by
  sorry

/-- **The frame rule**: a predicate reading only blocks disjoint from the footprint is kept. -/
theorem Spec.frame {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} (h : Spec m I pre s fp post)
    (hF : ReadsOnly F rs) (hd : BlocksDisjoint rs fp) :
    Spec m I (fun st => pre st ∧ F st.store) s fp fun st st' => post st st' ∧ F st'.store := by
  sorry

omit [AddMonoid C] in
/-- The frame of one step of a proof: what a specified step keeps. -/
theorem ReadsOnly.of_spec_post {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} {st' : St P K C}
    (hF : ReadsOnly F rs) (h : F st.store) (hm : Modifies fp st.store st'.store)
    (hd : BlocksDisjoint rs fp) : F st'.store :=
  hF.of_modifies h hm hd

/-- **A conditional of specifications** on a comparison whose outcome `r` the precondition
fixes. -/
theorem Spec.ite {p : P} {c : CmpOp} {x y : Cell ℕ ℕ} {r : Bool}
    {preT preE : St P K C → Prop} {postT postE : St P K C → St P K C → Prop}
    (ht : Spec m I preT s fp postT) (he : Spec m I preE t fp postE)
    (hcmp : ∀ st, pre st → ∃ a b, st.store.read p x.buf x.idx.eval = some a ∧
      st.store.read p y.buf y.idx.eval = some b ∧ I.sem.cmp p c a b = some r)
    (hT : ∀ st, pre st → r = true → preT (st.addCnt (I.charge (.cmp p))))
    (hE : ∀ st, pre st → r = false → preE (st.addCnt (I.charge (.cmp p)))) :
    Spec m I pre (.ite p c x y s t) fp fun st st' =>
      (r = true → postT (st.addCnt (I.charge (.cmp p))) st') ∧
        (r = false → postE (st.addCnt (I.charge (.cmp p))) st') := by
  sorry

/-- **A loop of specifications** with an invariant and one footprint for every iteration. -/
theorem Spec.loop {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    (Inv : St P K C → ℕ → St P K C → Prop) (h0 : ∀ st, pre st → Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ k < n.eval,
      Spec m I (Inv st₀ k) (body k) fp fun _ st' => Inv st₀ (k + 1) st') :
    Spec m I pre (.loop n body) fp fun st₀ st' => Inv st₀ n.eval st' := by
  sorry

/-- **Scoped scratch for specifications**: the body may modify the fresh buffer at the relative
handle `b`; the allocation's footprint is the body's below it. -/
theorem Spec.alloc {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {b : ℕ}
    {pre' : St P K C → Prop} {post' : St P K C → St P K C → Prop}
    (h : Spec m I pre' (body b) (fp ++ [(b, 0, len.eval)]) post')
    (hb : ∀ st, pre st → st.store.size = b)
    (hpre : ∀ st, pre st → pre' (st.allocate p len.eval (I.width p)))
    (hpost : ∀ st st₂, pre st → post' (st.allocate p len.eval (I.width p)) st₂ →
      post st (st₂.release p len.eval (I.width p))) :
    Spec m I pre (.alloc p len body) fp post := by
  sorry

/-- **The call rule**: a specified routine followed by the rest of a builder, without unfolding
the routine; the rest starts from a named state with the routine's effect as hypotheses. -/
theorem RoutineSpec.wp_bind {r : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit}
    {Q : St P K C → Prop} (h : RoutineSpec m I pre r fp post) (hpre : pre st)
    (hk : ∀ st', Modifies fp st.store st'.store → post st st' → Wp m I (f ()).run Q st') :
    Wp m I (r >>= f).run Q st := by
  sorry

/-- The call rule for the last routine of a block. -/
theorem RoutineSpec.wp_run {r : Builder P ι ℕ ℕ Unit} {Q : St P K C → Prop}
    (h : RoutineSpec m I pre r fp post) (hpre : pre st)
    (hk : ∀ st', Modifies fp st.store st'.store → post st st' → Q st') :
    Wp m I r.run Q st := by
  sorry

/-- Two specified routines in sequence form one. -/
theorem RoutineSpec.bind {r₁ r₂ : Builder P ι ℕ ℕ Unit} (h₁ : RoutineSpec m I pre r₁ fp post)
    (h₂ : RoutineSpec m I pre₂ r₂ fp₂ post₂)
    (hmid : ∀ st st₁, pre st → Modifies fp st.store st₁.store → post st st₁ → pre₂ st₁) :
    RoutineSpec m I pre (r₁ >>= fun _ => r₂) (fp ++ fp₂)
      fun st st₂ => ∃ st₁, post st st₁ ∧ post₂ st₁ st₂ := by
  sorry

/-- A scope around a specified routine is specified alike. -/
theorem RoutineSpec.scope {r : Builder P ι ℕ ℕ Unit} (h : Spec m I pre r.run fp post) :
    RoutineSpec m I pre (Builder.scope r) fp post := by
  sorry

/-- **A specification from a liberal one and success**, each from its own proof. -/
theorem Spec.total_of_liberal (h : Spec .liberal I pre s fp post)
    (hs : ∀ st, pre st → ∃ st', exec I s st = some st') : Spec .total I pre s fp post :=
  Triple.total_of_liberal h hs

end Spec

/-! ### Counts -/

section Costs

/-- **An exact count**: the final count is the start count plus `c`. Counts thread additively
(`NLAlib.Computation.Costs.trans`) in any additive monoid, and `c` may be a term in the charge
`I.charge`, so one count lemma serves every charge. -/
def Costs (c : C) (st st' : St P K C) : Prop := st'.cnt = st.cnt + c

omit [DecidableEq P] in
/-- No step, no count. -/
theorem Costs.refl (st : St P K C) : Costs 0 st st := by
  sorry

omit [DecidableEq P] in
/-- Counts in sequence add. -/
theorem Costs.trans {c₁ c₂ : C} {st st₁ st₂ : St P K C} (h₁ : Costs c₁ st st₁)
    (h₂ : Costs c₂ st₁ st₂) : Costs (c₁ + c₂) st st₂ := by
  sorry

omit [DecidableEq P] in
/-- A charged step that writes nothing. -/
theorem Costs.addCnt (st : St P K C) (c : C) : Costs c st (st.addCnt c) := by
  sorry

omit [DecidableEq P] in
/-- The counts of a loop add over its iterations. -/
theorem Costs.list_sum {n : ℕ} {c : ℕ → C} {f : ℕ → St P K C}
    (h : ∀ k < n, Costs (c k) (f k) (f (k + 1))) :
    Costs ((List.range n).map c).sum (f 0) (f n) := by
  sorry

/-- **A specification under another charge**: the store, the tape positions and the memory of a
run do not depend on the charge, so a total specification whose pre- and postcondition ignore
the count holds under every charge. -/
theorem Spec.withCharge {I : Interp P ι K C} {pre : St P K C → Prop} {s : Stmt P ι ℕ ℕ}
    {fp : List (ℕ × ℕ × ℕ)} {post : St P K C → St P K C → Prop} (ch : OpKind P ι → C)
    (h : Spec .total I pre s fp post) (hpre : ∀ st c, pre st → pre { st with cnt := c })
    (hpost : ∀ st st' c c', post st st' → post { st with cnt := c } { st' with cnt := c' }) :
    Spec .total { I with charge := ch } pre s fp post := by
  sorry

end Costs

/-! ### Certificates as specifications -/

section Certificates

variable {I : Interp P ι K C}

/-- **A footprint certificate is a specification**: from a state satisfying `pre` with writable
outputs, the routine succeeds and modifies only its output blocks. -/
theorem IsBlockRoutine.routineSpec {tag : P} {pre : Store P K → Prop}
    {outs : List (ℕ × ℕ × ℕ)} {r : Builder P ι ℕ ℕ Unit} (h : IsBlockRoutine I tag pre outs r) :
    RoutineSpec .total I (fun st => pre st.store ∧ WritableBlocks st.store tag outs) r outs
      fun _ _ => True := by
  sorry

/-- **A certified matrix-vector routine is a specification**, for each decoded input $x$: it
modifies only the destination block, which then decodes to $y$ with
$\lVert \mathbf{A}x - y \rVert_2 \le c \lVert x \rVert_2$. -/
theorem IsMatvecRoutine.routineSpec {dec : P → K → ℝ} {tag : P} {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {c : ℝ} {pre : Store P K → Prop} {src dst : ℕ}
    {sOff dOff : IExp ℕ} {r : Builder P ι ℕ ℕ Unit}
    (h : IsMatvecRoutine I dec tag A c pre src dst sOff dOff r) (x : Fin N → ℝ) :
    RoutineSpec .total I (fun st => pre st.store ∧ ReadsDecoded st.store dec tag src sOff.eval x ∧
        Writable st.store tag dst dOff.eval N) r [(dst, dOff.eval, N)] fun _ st' =>
      ∃ y : Fin N → ℝ, ReadsDecoded st'.store dec tag dst dOff.eval y ∧
        ‖WithLp.toLp 2 (Matrix.mulVec A x - y)‖ ≤ c * ‖WithLp.toLp 2 x‖ := by
  sorry

end Certificates

/-! ### Budgets -/

/-- **A total triple of a compiled program runs within its static budget**: success from the
triple, the counts and the workspace from the fixed first-order tree
(`NLAlib.Computation.Prog.runsWithin_staticCost_of_exec_eq_some`). -/
theorem Triple.prog_runsWithin {I : Interp P ι K (OpCount P ι)} {r b : ℕ} (prog : Prog P ι r b)
    (N : ℕ) (n : Fin r → ℕ) {pre : St P K (OpCount P ι) → Prop}
    {post : St P K (OpCount P ι) → St P K (OpCount P ι) → Prop}
    (h : Triple .total I pre (prog.toStmt N n) post) {st : St P K (OpCount P ι)} (hpre : pre st)
    (hsize : st.store.size = b) :
    prog.RunsWithin I N n st (prog.staticCost I.charge I.width N n).count
      (fun p => max (st.peak p) (st.cur p +
        (prog.staticCost I.charge I.width N n).cells p) + I.romSize p) (post st) := by
  sorry

/-! ### Tactics -/

/-- Footprint side goals: membership in, disjointness of and arithmetic on concrete block lists,
closed by `omega` after unfolding `NLAlib.Computation.BlocksDisjoint` and
`NLAlib.Computation.blockDisjoint_iff`. -/
macro "fp_omega" : tactic => `(tactic| (
  try simp only [BlocksDisjoint, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.forall_mem_cons, blockDisjoint_iff, ne_eq] at *
  omega))

/-- One step of a program proof: split a sequence, apply the triple `h` to its first statement
and leave its precondition and the continuation from the named next state; footprint side
goals closed by `assumption` or `fp_omega` are removed, the others stay in order (precondition,
continuation). -/
syntax "spec_step " term : tactic

macro_rules
  | `(tactic| spec_step $h) => `(tactic| (
      first | rw [wp_seq] | skip
      refine Triple.wp_of $h ?_ ?_ <;> try (first | assumption | fp_omega)))

/-- One call of a specified routine in a builder: `NLAlib.Computation.RoutineSpec.wp_bind`, with
side goals closed by `assumption` or `fp_omega` removed, as for `spec_step`. -/
syntax "spec_call " term : tactic

macro_rules
  | `(tactic| spec_call $h) => `(tactic| (
      first | refine RoutineSpec.wp_bind $h ?_ ?_ | refine RoutineSpec.wp_run $h ?_ ?_
      all_goals try (first | assumption | fp_omega)))

end NLAlib.Computation
