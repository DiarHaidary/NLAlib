/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.ProgramLogic

/-!
# Routine specifications

The specification layer of the program logic of `NLAlib/Computation/ProgramLogic.lean` (design
note `docs/design/Computation-ProgramLogic.md`): a routine specification
(`NLAlib.Computation.Spec`) is a triple whose postcondition also bounds what the run modifies
(`NLAlib.Computation.Modifies`); a specified routine (`NLAlib.Computation.RoutineSpec`) is a
builder that composes with what follows and meets one. The rules compose specifications
(sequence, the frame rule, conditionals, loops, scoped scratch, the call rule), the instruction
specifications fix what one instruction writes, and the certificates of
`NLAlib/Computation/RoutineFrames.lean` and `NLAlib/Computation/MatvecRoutine.lean` are
specifications. A program proof is a sequence of calls (`spec_call`), each naming the next state.

## Main definitions

* `NLAlib.Computation.Spec`, `NLAlib.Computation.RoutineSpec`: routine specifications.
* `NLAlib.Computation.Costs`, `NLAlib.Computation.CostsLe`: an exact count and a weighted count
  bound, threaded additively.

## Main results

* `NLAlib.Computation.Spec.seq`, `NLAlib.Computation.Spec.frame`,
  `NLAlib.Computation.Spec.alloc`: composition, the frame rule, scoped scratch.
* `NLAlib.Computation.RoutineSpec.wp_bind`: the call rule;
  `NLAlib.Computation.RoutineSpec.wp_bind_keep`: with a kept frame.
* `NLAlib.Computation.Spec.allocBind`, `NLAlib.Computation.Spec.loopFp`,
  `NLAlib.Computation.Spec.bindIdx_of_read`, `NLAlib.Computation.RoutineSpec.bindIdx_of_read`:
  allocation by named states, loops with per-iteration footprints, index binders.
* `NLAlib.Computation.spec_lit`, `NLAlib.Computation.spec_bin`, `NLAlib.Computation.spec_draw`:
  instruction specifications.
* `NLAlib.Computation.IsBlockRoutine.routineSpec`, `NLAlib.Computation.IsMatvecRoutine.routineSpec`:
  certificates as specifications.
* `NLAlib.Computation.Triple.prog_runsWithin`: the static budget of a compiled program.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

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
    Spec m I pre' s fp' post' :=
  Triple.conseq h hpre fun st st' hst hp => ⟨hp.1.mono hfp, hpost st st' hst hp.2⟩

/-- A specification's postcondition may also state its footprint. -/
theorem Spec.with_modifies (h : Spec m I pre s fp post) :
    Spec m I pre s fp fun st st' => Modifies fp st.store st'.store ∧ post st st' :=
  Triple.conseq h (fun _ h => h) fun _ _ _ hp => ⟨hp.1, hp.1, hp.2⟩

/-- **Sequence of specifications**: footprints add, the first output feeds the second. -/
theorem Spec.seq (h₁ : Spec m I pre s fp post) (h₂ : Spec m I pre₂ t fp₂ post₂)
    (hmid : ∀ st st₁, pre st → Modifies fp st.store st₁.store → post st st₁ → pre₂ st₁) :
    Spec m I pre (.seq s t) (fp ++ fp₂) fun st st₂ => ∃ st₁, post st st₁ ∧ post₂ st₁ st₂ :=
  Triple.conseq (Triple.seq h₁ h₂ fun st st₁ hst hp => hmid st st₁ hst hp.1 hp.2) (fun _ h => h)
    fun _ _ _ ⟨st₁, ⟨hm₁, hp₁⟩, hm₂, hp₂⟩ => ⟨hm₁.trans hm₂, st₁, hp₁, hp₂⟩

omit [AddMonoid C] in
/-- A block of one buffer is disjoint from every block of other buffers. -/
theorem blocksDisjoint_singleton_of_fst_ne {x : ℕ × ℕ × ℕ} {fp : List (ℕ × ℕ × ℕ)}
    (h : ∀ y ∈ fp, x.1 ≠ y.1) : BlocksDisjoint [x] fp := fun x' hx y hy => by
  rw [List.mem_singleton.mp hx]
  exact blockDisjoint_of_fst_ne (h y hy)

/-- **The frame rule**: a predicate reading only blocks disjoint from the footprint is kept. -/
theorem Spec.frame {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} (h : Spec m I pre s fp post)
    (hF : ReadsOnly F rs) (hd : BlocksDisjoint rs fp) :
    Spec m I (fun st => pre st ∧ F st.store) s fp fun st st' => post st st' ∧ F st'.store :=
  fun st hst => wp_mono (h st hst.1) fun _ hp => ⟨hp.1, hp.2, hF.of_modifies hst.2 hp.1 hd⟩

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
  intro st hst
  obtain ⟨a, b, hx, hy, hr⟩ := hcmp st hst
  rw [wp_ite_of_read hx hy hr]
  cases r
  · exact wp_mono (he _ (hE st hst rfl)) fun _ hp =>
      ⟨hp.1, fun h => absurd h (by simp), fun _ => hp.2⟩
  · exact wp_mono (ht _ (hT st hst rfl)) fun _ hp =>
      ⟨hp.1, fun _ => hp.2, fun h => absurd h (by simp)⟩

/-- **A loop of specifications** with an invariant and one footprint for every iteration. -/
theorem Spec.loop {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    (Inv : St P K C → ℕ → St P K C → Prop) (h0 : ∀ st, pre st → Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ k < n.eval,
      Spec m I (Inv st₀ k) (body k) fp fun _ st' => Inv st₀ (k + 1) st') :
    Spec m I pre (.loop n body) fp fun st₀ st' => Inv st₀ n.eval st' := by
  refine Triple.conseq (Triple.loop (fun st₀ k st => Inv st₀ k st ∧ Modifies fp st₀.store st.store)
    (fun st hst => ⟨h0 st hst, Modifies.refl _ _⟩) fun st₀ hst k hk => ?_) (fun _ h => h)
    fun _ _ _ hp => ⟨hp.2, hp.1⟩
  exact fun st hp => wp_mono (hstep st₀ hst k hk st hp.1) fun _ hq =>
    ⟨hq.2, (hp.2.trans hq.1).mono fun x hx => by
      rcases List.mem_append.mp hx with hx | hx <;> exact hx⟩

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
  refine Triple.alloc h hb hpre fun st st₂ hst hp => ⟨?_, hpost st st₂ hst hp.2⟩
  have hm := hp.1
  rw [← hb st hst] at hm
  exact Modifies.pop_top hm

/-- **The call rule**: a specified routine followed by the rest of a builder, without unfolding
the routine; the rest starts from a named state with the routine's effect as hypotheses. -/
theorem RoutineSpec.wp_bind {r : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit}
    {Q : St P K C → Prop} (h : RoutineSpec m I pre r fp post) (hpre : pre st)
    (hk : ∀ st', Modifies fp st.store st'.store → post st st' → Wp m I (f ()).run Q st') :
    Wp m I (r >>= f).run Q st := by
  rw [wp_run_bind h.composable]
  exact h.spec.wp_of hpre fun st' hp => hk st' hp.1 hp.2

/-- The call rule for the last routine of a block. -/
theorem RoutineSpec.wp_run {r : Builder P ι ℕ ℕ Unit} {Q : St P K C → Prop}
    (h : RoutineSpec m I pre r fp post) (hpre : pre st)
    (hk : ∀ st', Modifies fp st.store st'.store → post st st' → Q st') :
    Wp m I r.run Q st :=
  h.spec.wp_of hpre fun st' hp => hk st' hp.1 hp.2

/-- **The call rule with a kept frame**: as `NLAlib.Computation.RoutineSpec.wp_bind`, and a store
predicate `F` that reads only blocks disjoint from the routine's footprint is handed to the rest
of the block. One read-set side goal (`fp_omega`) per call, for every fact the bundle `F`
carries (`NLAlib.Computation.CellsHold`, `NLAlib.Computation.ReadsOnly.and`). -/
theorem RoutineSpec.wp_bind_keep {r : Builder P ι ℕ ℕ Unit} {f : Unit → Builder P ι ℕ ℕ Unit}
    {Q : St P K C → Prop} {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)}
    (h : RoutineSpec m I pre r fp post) (hF : ReadsOnly F rs) (hd : BlocksDisjoint rs fp)
    (hpre : pre st) (hFst : F st.store)
    (hk : ∀ st', Modifies fp st.store st'.store → post st st' → F st'.store →
      Wp m I (f ()).run Q st') :
    Wp m I (r >>= f).run Q st :=
  h.wp_bind hpre fun st' hm hp => hk st' hm hp (hF.of_modifies hFst hm hd)

/-- The call rule with a kept frame, for the last routine of a block. -/
theorem RoutineSpec.wp_run_keep {r : Builder P ι ℕ ℕ Unit} {Q : St P K C → Prop}
    {F : Store P K → Prop} {rs : List (ℕ × ℕ × ℕ)} (h : RoutineSpec m I pre r fp post)
    (hF : ReadsOnly F rs) (hd : BlocksDisjoint rs fp) (hpre : pre st) (hFst : F st.store)
    (hk : ∀ st', Modifies fp st.store st'.store → post st st' → F st'.store → Q st') :
    Wp m I r.run Q st :=
  h.wp_run hpre fun st' hm hp => hk st' hm hp (hF.of_modifies hFst hm hd)

/-- Two specified routines in sequence form one. -/
theorem RoutineSpec.bind {r₁ r₂ : Builder P ι ℕ ℕ Unit} (h₁ : RoutineSpec m I pre r₁ fp post)
    (h₂ : RoutineSpec m I pre₂ r₂ fp₂ post₂)
    (hmid : ∀ st st₁, pre st → Modifies fp st.store st₁.store → post st st₁ → pre₂ st₁) :
    RoutineSpec m I pre (r₁ >>= fun _ => r₂) (fp ++ fp₂)
      fun st st₂ => ∃ st₁, post st st₁ ∧ post₂ st₁ st₂ := by
  refine ⟨h₁.composable.bind h₂.composable, fun st hst => ?_⟩
  refine h₁.wp_bind hst fun st₁ hm₁ hp₁ => ?_
  exact h₂.spec.wp_of (hmid st st₁ hst hm₁ hp₁) fun st₂ hp₂ => ⟨hm₁.trans hp₂.1, st₁, hp₁, hp₂.2⟩

/-- A scope around a specified routine is specified alike. -/
theorem RoutineSpec.scope {r : Builder P ι ℕ ℕ Unit} (h : Spec m I pre r.run fp post) :
    RoutineSpec m I pre (Builder.scope r) fp post :=
  ⟨executionComposable_scope r, fun st hst => (wp_seq).mpr <|
    wp_mono (h st hst) fun _ hp => (wp_skip).mpr hp⟩

/-- A named kernel around a specified run is specified alike. -/
theorem RoutineSpec.named {x : Builder P ι ℕ ℕ Unit} (name : String) (args : List (Arg ℕ ℕ))
    (h : Spec m I pre x.run fp post) : RoutineSpec m I pre (Builder.named name args x) fp post :=
  ⟨executionComposable_named name args x, fun st hst => (wp_seq).mpr <|
    (wp_named name args).mpr <| wp_mono (h st hst) fun _ hp => (wp_skip).mpr hp⟩

/-- **A triple from the two lemmas of a run**: what every successful run satisfies, and, in the
total mode, success. The adapter of an existing pair of a refinement and a success lemma. -/
theorem Triple.of_exec {post : St P K C → St P K C → Prop}
    (hrun : ∀ st, pre st → m.Needs (∃ st', exec I s st = some st'))
    (hpost : ∀ st st', pre st → exec I s st = some st' → post st st') : Triple m I pre s post := by
  intro st hst
  cases m
  · obtain ⟨st', h⟩ := hrun st hst
    exact ⟨st', h, hpost st st' hst h⟩
  · exact fun st' h => hpost st st' hst h

/-- **A specification from a liberal one and success**, each from its own proof. -/
theorem Spec.total_of_liberal (h : Spec .liberal I pre s fp post)
    (hs : ∀ st, pre st → ∃ st', exec I s st = some st') : Spec .total I pre s fp post :=
  Triple.total_of_liberal h hs

/-- **A statement step as a routine**: the call rule applies to `Builder.stmt s` (a kernel call
in a builder) with the specification of `s`. -/
theorem RoutineSpec.stmt (h : Spec m I pre s fp post) :
    RoutineSpec m I pre (Builder.stmt s) fp post :=
  ⟨executionComposable_stmt s, fun st hst => (wp_seq).mpr <|
    wp_mono (h st hst) fun _ hp => (wp_skip).mpr hp⟩

/-- A scalar instruction step as a routine. -/
theorem RoutineSpec.ins {i : Instr P ℕ ℕ} (h : Spec m I pre (.instr i) fp post) :
    RoutineSpec m I pre (Builder.ins i) fp post :=
  RoutineSpec.stmt h

/-- **Transport across run equivalence**: a specified routine specifies every composable builder
whose run runs the same (index normal forms, `Builder` rewrites). -/
theorem RoutineSpec.congr {r r' : Builder P ι ℕ ℕ Unit} (h : RoutineSpec m I pre r fp post)
    (hc : ExecutionComposable I r') (he : ∀ st, exec I r'.run st = exec I r.run st) :
    RoutineSpec m I pre r' fp post := by
  refine ⟨hc, fun st hst => ?_⟩
  have := h.spec st hst
  rw [Wp, he]
  exact this

/-- A specification transported to a statement of the same index normal form
(`NLAlib.Computation.exec_eq_of_normIdx_eq`). -/
theorem Spec.of_normIdx_eq {s' : Stmt P ι ℕ ℕ} (h : Spec m I pre s fp post)
    (hn : s'.normIdx = s.normIdx) : Spec m I pre s' fp post := by
  intro st hst
  have := h st hst
  rw [Wp, exec_eq_of_normIdx_eq I hn]
  exact this

/-- **An allocation in a builder, by named states**: the rest of the block, specified at the
relative handle `b` from the allocated state `st₁` (an equation, not a pushed term), gives the
block's specification; its footprint below the fresh buffer is the body's. -/
theorem Spec.allocBind {p : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} {b : ℕ}
    {pre' : St P K C → Prop} {post' : St P K C → St P K C → Prop}
    (h : Spec m I pre' (f b).run (fp ++ [(b, 0, len.eval)]) post')
    (hb : ∀ st, pre st → st.store.size = b)
    (hpre : ∀ st st₁, pre st → st₁ = st.allocate p len.eval (I.width p) → pre' st₁)
    (hpost : ∀ st st₁ st₂, pre st → st₁ = st.allocate p len.eval (I.width p) → post' st₁ st₂ →
      post st (st₂.release p len.eval (I.width p))) :
    Spec m I pre (Builder.alloc p len >>= f).run fp post :=
  Spec.alloc (body := fun b => (f b).run) h hb (fun st hst => hpre st _ hst rfl)
    fun st st₂ hst hp => hpost st _ st₂ hst rfl hp

/-- **An allocation in a builder, by named states, with the rest specified from the allocated
state**: the rest of the block is specified from every state `st.allocate …` with `pre st`, its
postcondition for every such `st` read after the release; no other obligation. -/
theorem Spec.allocBind_named {p : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} {b : ℕ}
    (hb : ∀ st, pre st → st.store.size = b)
    (h : Spec m I (fun s => ∃ st, pre st ∧ s = st.allocate p len.eval (I.width p)) (f b).run
      (fp ++ [(b, 0, len.eval)]) fun s s' => ∀ st, pre st →
        s = st.allocate p len.eval (I.width p) → post st (s'.release p len.eval (I.width p))) :
    Spec m I pre (Builder.alloc p len >>= f).run fp post :=
  Spec.allocBind h hb (fun st _ hst e => ⟨st, hst, e⟩) fun st _ _ hst e hp => hp st hst e

/-- **The $j$-th of a chain of allocations, by named states**: from a state that is $j$
allocations after a state satisfying `pre` (whose store has $b$ buffers), an allocation of
`len` cells gets the handle $b + j$, so the rest of the block, specified $j + 1$ allocations
after, gives the block's specification $j$ allocations after, with one fresh block fewer in the
footprint and one release fewer in the postcondition. -/
theorem spec_allocBind_iterate {p : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit} {b : ℕ} (j : ℕ)
    (hb : ∀ st, pre st → st.store.size = b)
    (h : Spec m I (fun s => ∃ st, pre st ∧ s = (·.allocate p len.eval (I.width p))^[j + 1] st)
      (f (b + j)).run (fp ++ (List.range (j + 1)).map fun i => (b + i, 0, len.eval))
      fun s s' => ∀ st, pre st → s = (·.allocate p len.eval (I.width p))^[j + 1] st →
        post st ((·.release p len.eval (I.width p))^[j + 1] s')) :
    Spec m I (fun s => ∃ st, pre st ∧ s = (·.allocate p len.eval (I.width p))^[j] st)
      (Builder.alloc p len >>= f).run (fp ++ (List.range j).map fun i => (b + i, 0, len.eval))
      fun s s' => ∀ st, pre st → s = (·.allocate p len.eval (I.width p))^[j] st →
        post st ((·.release p len.eval (I.width p))^[j] s') := by
  have hsz : ∀ i st, pre st → ((·.allocate p len.eval (I.width p))^[i] st).store.size = b + i := by
    intro i st hst
    induction i with
    | zero => exact hb st hst
    | succ i ih => rw [Function.iterate_succ_apply', St.size_allocate, ih, Nat.add_assoc]
  rw [List.range_succ, List.map_append, List.map_singleton, ← List.append_assoc] at h
  refine Spec.allocBind h (fun _ ⟨st, hst, e⟩ => e ▸ hsz j st hst)
    (fun _ _ ⟨st, hst, e⟩ e₁ => ⟨st, hst, by rw [e₁, e, Function.iterate_succ_apply']⟩)
    fun _ _ s₂ ⟨st₀, hst₀, e⟩ e₁ hp st hst e' => ?_
  rw [← Function.iterate_succ_apply]
  exact hp st hst (by rw [e₁, e', Function.iterate_succ_apply'])

/-- **A loop with per-iteration footprints**: iteration `k` may modify the blocks `fp k` (which
may depend on ghost sizes read before the loop); the loop modifies their union. -/
theorem Spec.loopFp {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} (fp : ℕ → List (ℕ × ℕ × ℕ))
    (Inv : St P K C → ℕ → St P K C → Prop) (h0 : ∀ st, pre st → Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ k < n.eval,
      Spec m I (Inv st₀ k) (body k) (fp k) fun _ st' => Inv st₀ (k + 1) st') :
    Spec m I pre (.loop n body) ((List.range n.eval).flatMap fp)
      fun st₀ st' => Inv st₀ n.eval st' := by
  refine Triple.conseq (Triple.loop (fun st₀ k st => Inv st₀ k st ∧
      Modifies ((List.range k).flatMap fp) st₀.store st.store)
    (fun st hst => ⟨h0 st hst, Modifies.refl _ _⟩) fun st₀ hst k hk => ?_) (fun _ h => h)
    fun _ _ _ hp => ⟨hp.2, hp.1⟩
  refine fun st hp => wp_mono (hstep st₀ hst k hk st hp.1) fun _ hq => ⟨hq.2, ?_⟩
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
  exact hp.2.trans hq.1

/-- A loop in a builder, with per-iteration footprints. -/
theorem RoutineSpec.forRange {n : IExp ℕ} {body : ℕ → Builder P ι ℕ ℕ Unit}
    (fp : ℕ → List (ℕ × ℕ × ℕ)) (Inv : St P K C → ℕ → St P K C → Prop)
    (h0 : ∀ st, pre st → Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ k < n.eval,
      Spec m I (Inv st₀ k) (body k).run (fp k) fun _ st' => Inv st₀ (k + 1) st') :
    RoutineSpec m I pre (Builder.forRange n body) ((List.range n.eval).flatMap fp)
      fun st₀ st' => Inv st₀ n.eval st' :=
  RoutineSpec.stmt (s := .loop n fun i => (body i).run) (Spec.loopFp fp Inv h0 hstep)

/-- A loop in a builder with one footprint for every iteration: the iterations modify the blocks
`fp`, which the loop then modifies. -/
theorem RoutineSpec.forRange_const {n : IExp ℕ} {body : ℕ → Builder P ι ℕ ℕ Unit}
    (fp : List (ℕ × ℕ × ℕ)) (Inv : St P K C → ℕ → St P K C → Prop)
    (h0 : ∀ st, pre st → Inv st 0 st)
    (hstep : ∀ st₀, pre st₀ → ∀ k < n.eval,
      Spec m I (Inv st₀ k) (body k).run fp fun _ st' => Inv st₀ (k + 1) st') :
    RoutineSpec m I pre (Builder.forRange n body) fp fun st₀ st' => Inv st₀ n.eval st' :=
  RoutineSpec.stmt (s := .loop n fun i => (body i).run) (Spec.loop Inv h0 hstep)

/-- **An index binder of specifications**: the precondition fixes the stored value `v`, which
converts to `k`; the body is specified at `k` with the fact `k ≤ bound` and may have a footprint
depending on `k`; the binder's postcondition records `k ≤ bound`, which the total mode needs. -/
theorem Spec.bindIdx_of_read {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {v : K} {k : ℕ} {pre' : St P K C → Prop} {post' : St P K C → St P K C → Prop}
    (hx : ∀ st, pre st → st.store.read p x.buf x.idx.eval = some v)
    (hk : I.sem.toNat p v = some k) (hbound : m.Needs (k ≤ bound.eval))
    (h : k ≤ bound.eval → Spec m I pre' (body k) fp post')
    (hpre : ∀ st, pre st → pre' (st.addCnt (I.charge (.toNat p)))) :
    Spec m I pre (.bindIdx p x bound body) fp
      fun st st' => k ≤ bound.eval ∧ post' (st.addCnt (I.charge (.toNat p))) st' := by
  intro st hst
  refine wp_bindIdx_of_read (hx st hst) ?_
  rw [hk, Mode.sat_some]
  exact ⟨hbound, fun hkb => wp_mono (h hkb _ (hpre st hst)) fun _ hp => ⟨hp.1, hkb, hp.2⟩⟩

/-- **An index binder in a builder**, of specifications: `NLAlib.Computation.Spec.bindIdx_of_read`
for `NLAlib.Computation.Builder.bindIdx`, the body a builder specified at the converted value
$k$ with the fact $k \le$ `bound`. -/
theorem RoutineSpec.bindIdx_of_read {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ}
    {body : ℕ → Builder P ι ℕ ℕ Unit} {v : K} {k : ℕ} {pre' : St P K C → Prop}
    {post' : St P K C → St P K C → Prop}
    (hx : ∀ st, pre st → st.store.read p x.buf x.idx.eval = some v)
    (hk : I.sem.toNat p v = some k) (hbound : m.Needs (k ≤ bound.eval))
    (h : k ≤ bound.eval → Spec m I pre' (body k).run fp post')
    (hpre : ∀ st, pre st → pre' (st.addCnt (I.charge (.toNat p)))) :
    RoutineSpec m I pre (Builder.bindIdx p x bound body) fp
      fun st st' => k ≤ bound.eval ∧ post' (st.addCnt (I.charge (.toNat p))) st' :=
  ⟨executionComposable_bindIdx p x bound body,
    (RoutineSpec.stmt (s := .bindIdx p x bound fun i => (body i).run)
      (Spec.bindIdx_of_read hx hk hbound h hpre)).spec⟩

/-- **A two-armed conditional of specifications** (the branch not fixed by the precondition):
the postcondition is that of the arm taken. -/
theorem Spec.ite_cases {p : P} {c : CmpOp} {x y : Cell ℕ ℕ}
    {preT preE : St P K C → Prop} {postT postE : St P K C → St P K C → Prop}
    (ht : Spec m I preT s fp postT) (he : Spec m I preE t fp postE)
    (hcmp : ∀ st, pre st → m.Needs (∃ a b r, st.store.read p x.buf x.idx.eval = some a ∧
      st.store.read p y.buf y.idx.eval = some b ∧ I.sem.cmp p c a b = some r))
    (hT : ∀ st, pre st → preT (st.addCnt (I.charge (.cmp p))))
    (hE : ∀ st, pre st → preE (st.addCnt (I.charge (.cmp p)))) :
    Spec m I pre (.ite p c x y s t) fp fun st st' =>
      postT (st.addCnt (I.charge (.cmp p))) st' ∨ postE (st.addCnt (I.charge (.cmp p))) st' := by
  intro st hst
  rw [wp_ite]
  have hsat : m.Sat (fun r : Bool × St P K C => r.2 = st.addCnt (I.charge (.cmp p)))
      (cmpStep I p c x y st) := by
    have hrun : ∀ r, cmpStep I p c x y st = some r → r.2 = st.addCnt (I.charge (.cmp p)) := by
      intro r hr
      simp only [cmpStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨_, _, _, _, _, _, rfl⟩ := hr
      rfl
    cases m
    · obtain ⟨a, b, r, hx, hy, hr⟩ := hcmp st hst
      have he : cmpStep I p c x y st = some (r, st.addCnt (I.charge (.cmp p))) := by
        simp only [cmpStep, hx, hy, hr, Option.bind_some, Option.map_some]
        rfl
      exact ⟨_, he, rfl⟩
    · exact hrun
  refine hsat.mono fun r h₁ => ?_
  obtain ⟨r, st₁⟩ := r
  dsimp only at h₁ ⊢
  subst h₁
  cases r
  · exact wp_mono (he _ (hE st hst)) fun _ hp => ⟨hp.1, Or.inr hp.2⟩
  · exact wp_mono (ht _ (hT st hst)) fun _ hp => ⟨hp.1, Or.inl hp.2⟩

end Spec


/-! ### Counts -/

section Costs

/-- **An exact count**: the final count is the start count plus `c`. Counts thread additively
(`NLAlib.Computation.Costs.trans`) in any additive monoid, and `c` may be a term in the charge
`I.charge`, so one count lemma serves every charge. -/
def Costs (c : C) (st st' : St P K C) : Prop := st'.cnt = st.cnt + c

omit [DecidableEq P] in
/-- No step, no count. -/
theorem Costs.refl (st : St P K C) : Costs 0 st st :=
  (add_zero _).symm

omit [DecidableEq P] in
/-- Counts in sequence add. -/
theorem Costs.trans {c₁ c₂ : C} {st st₁ st₂ : St P K C} (h₁ : Costs c₁ st st₁)
    (h₂ : Costs c₂ st₁ st₂) : Costs (c₁ + c₂) st st₂ := by
  rw [Costs, h₂, h₁, add_assoc]

omit [DecidableEq P] in
/-- A charged step that writes nothing. -/
theorem Costs.addCnt (st : St P K C) (c : C) : Costs c st (st.addCnt c) :=
  rfl

omit [DecidableEq P] in
/-- The counts of a loop add over its iterations. -/
theorem Costs.list_sum {n : ℕ} {c : ℕ → C} {f : ℕ → St P K C}
    (h : ∀ k < n, Costs (c k) (f k) (f (k + 1))) :
    Costs ((List.range n).map c).sum (f 0) (f n) := by
  induction n with
  | zero => exact Costs.refl _
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    exact (ih fun k hk => h k (by omega)).trans (h n (by omega))

/-- **A specification under another charge**, in every mode: success, the store, the tape
positions and the memory of a run do not depend on the charge, so a specification whose
postcondition ignores the count holds under every charge (the run starts from the same state). -/
theorem Spec.withCharge {m : Mode} {I : Interp P ι K C} {pre : St P K C → Prop}
    {s : Stmt P ι ℕ ℕ} {fp : List (ℕ × ℕ × ℕ)} {post : St P K C → St P K C → Prop}
    (ch : OpKind P ι → C) (h : Spec m I pre s fp post)
    (hpost : ∀ st st' c c', post st st' → post { st with cnt := c } { st' with cnt := c' }) :
    Spec m { I with charge := ch } pre s fp post := by
  intro st hst
  cases m
  · obtain ⟨st', hrun, hm, hp⟩ := h st hst
    obtain ⟨c₁, hrun'⟩ := exists_exec_withCharge_eq_some I ch _ hrun st.cnt
    exact ⟨_, hrun', hm, hpost st st' st.cnt c₁ hp⟩
  · intro st' hrun
    obtain ⟨c₁, hrun'⟩ := exists_exec_withCharge_eq_some { I with charge := ch } I.charge _ hrun
      st.cnt
    obtain ⟨hm, hp⟩ := h st hst _ hrun'
    exact ⟨hm, hpost st { st' with cnt := c₁ } st.cnt st'.cnt hp⟩

omit [DecidableEq P] in
/-- **A weighted count bound**: the weight `w` (additive, such as `Finsupp.weight` of a kernel
weight) of the final count exceeds that of the start count by at most `c`. The form of the EP7
weighted kernel count; data-dependent through a supremum over an index binder's values. -/
def CostsLe (w : C →+ ℕ) (c : ℕ) (st st' : St P K C) : Prop := w st'.cnt ≤ w st.cnt + c

omit [DecidableEq P] in
/-- Weighted bounds in sequence add. -/
theorem CostsLe.trans {w : C →+ ℕ} {c₁ c₂ : ℕ} {st st₁ st₂ : St P K C}
    (h₁ : CostsLe w c₁ st st₁) (h₂ : CostsLe w c₂ st₁ st₂) : CostsLe w (c₁ + c₂) st st₂ := by
  unfold CostsLe at *
  omega

omit [DecidableEq P] in
/-- A weighted bound may be raised. -/
theorem CostsLe.mono {w : C →+ ℕ} {c c' : ℕ} {st st' : St P K C} (h : CostsLe w c st st')
    (hc : c ≤ c') : CostsLe w c' st st' := by
  unfold CostsLe at *
  omega

omit [DecidableEq P] in
/-- An exact count gives its weight as a bound. -/
theorem CostsLe.of_costs {w : C →+ ℕ} {c : C} {st st' : St P K C} (h : Costs c st st') :
    CostsLe w (w c) st st' := by
  rw [CostsLe, h, map_add]

omit [DecidableEq P] in
/-- Weighted bounds of a loop add over its iterations. -/
theorem CostsLe.list_sum {w : C →+ ℕ} {n : ℕ} {c : ℕ → ℕ} {f : ℕ → St P K C}
    (h : ∀ k < n, CostsLe w (c k) (f k) (f (k + 1))) :
    CostsLe w ((List.range n).map c).sum (f 0) (f n) := by
  induction n with
  | zero => exact le_add_right le_rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ← add_zero (_ + _)]
    rw [add_zero]
    exact (ih fun k hk => h k (by omega)).trans (h n (by omega))

end Costs

/-! ### Instructions -/

section Instructions

variable {m : Mode} {I : Interp P ι K C} {p : P} {dst x y : Cell ℕ ℕ}

omit [AddMonoid C] in
/-- A scalar write of a writable cell succeeds in the total mode. -/
theorem Mode.sat_write {s : Store P K} {b i : ℕ} {v : K} {Q : Store P K → Prop}
    (hW : m.Needs (Writable s p b i 1)) (hQ : ∀ s', s.write p b i v = some s' → Q s') :
    m.Sat Q (s.write p b i v) := by
  cases m
  · obtain ⟨len, hl, hlt⟩ := hW 0 Nat.one_pos
    obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape v hl (by omega)
    exact ⟨s', hs', hQ s' hs'⟩
  · exact hQ

/-- **A literal** writes its value into the destination cell, charges one literal and keeps the
tape positions; the total mode needs the cell writable. -/
theorem spec_lit {q : ℚ} {v : K} (hv : I.sem.lit p q = some v) :
    Spec m I (fun st => m.Needs (Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.lit p dst q)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some v ∧ Costs (I.charge (.lit p)) st st' ∧
          PosKept st st' := by
  intro st hst
  simp only [Wp, exec_instr, Mode.sat_map, Instr.run, hv, Option.bind_some]
  exact Mode.sat_write hst fun s' hs' =>
    ⟨Modifies.of_write hs', Store.read_of_write_eq_some hs', rfl, rfl⟩

/-- **An index literal**: the value of an index expression as a literal. -/
theorem spec_litIdx {e : IExp ℕ} {v : K} (hv : I.sem.lit p (e.eval : ℚ) = some v) :
    Spec m I (fun st => m.Needs (Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.litIdx p dst e)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some v ∧ Costs (I.charge (.lit p)) st st' ∧
          PosKept st st' := by
  intro st hst
  simp only [Wp, exec_instr, Mode.sat_map, Instr.run, hv, Option.bind_some]
  exact Mode.sat_write hst fun s' hs' =>
    ⟨Modifies.of_write hs', Store.read_of_write_eq_some hs', rfl, rfl⟩

/-- **An index literal**, read back as the semantics' literal: the destination cell then reads
`I.sem.lit p e.eval` (in every mode, without naming its value); the total mode needs the literal
to succeed and the cell writable. -/
theorem spec_litIdx_read {e : IExp ℕ} :
    Spec m I (fun st => m.Needs ((∃ v, I.sem.lit p (e.eval : ℚ) = some v) ∧
        Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.litIdx p dst e)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = I.sem.lit p (e.eval : ℚ) ∧ PosKept st st' := by
  intro st hst
  rw [Wp, exec_instr, Mode.sat_map, Instr.run, Mode.sat_bind]
  have key : ∀ v, I.sem.lit p (e.eval : ℚ) = some v → m.Sat (fun r => Modifies
      [(dst.buf, dst.idx.eval, 1)] st.store r.1 ∧ r.1.read p dst.buf dst.idx.eval =
        I.sem.lit p (e.eval : ℚ) ∧ r.2 = st.pos)
      ((st.store.write p dst.buf dst.idx.eval v).map fun s' => (s', st.pos)) := fun v hv => by
    rw [Mode.sat_map]
    exact Mode.sat_write (hst.mono (·.2)) fun s' hs' =>
      ⟨Modifies.of_write hs', (Store.read_of_write_eq_some hs').trans hv.symm, rfl⟩
  cases m
  · obtain ⟨v, hv⟩ := hst.1
    exact ⟨v, hv, key v hv⟩
  · exact key

/-- **An index literal**, read back as the stored literal: the destination cell then holds the
semantics' literal of the index (with `default` if it failed, which only a failed run sees); the
total mode needs the literal to succeed and the cell writable. -/
theorem spec_litIdx_getD [Inhabited K] {e : IExp ℕ} :
    Spec m I (fun st => m.Needs ((∃ v, I.sem.lit p (e.eval : ℚ) = some v) ∧
        Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.litIdx p dst e)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some ((I.sem.lit p (e.eval : ℚ)).getD default) ∧
          PosKept st st' := by
  intro st hst
  rw [Wp, exec_instr, Mode.sat_map, Instr.run, Mode.sat_bind]
  have key : ∀ v, I.sem.lit p (e.eval : ℚ) = some v → m.Sat (fun r => Modifies
      [(dst.buf, dst.idx.eval, 1)] st.store r.1 ∧ r.1.read p dst.buf dst.idx.eval =
        some ((I.sem.lit p (e.eval : ℚ)).getD default) ∧ r.2 = st.pos)
      ((st.store.write p dst.buf dst.idx.eval v).map fun s' => (s', st.pos)) := fun v hv => by
    rw [Mode.sat_map]
    exact Mode.sat_write (hst.mono (·.2)) fun s' hs' =>
      ⟨Modifies.of_write hs', by rw [Store.read_of_write_eq_some hs', hv]; rfl, rfl⟩
  cases m
  · obtain ⟨v, hv⟩ := hst.1
    exact ⟨v, hv, key v hv⟩
  · exact key

/-- **A literal**, read back as the stored literal (with `default` if it failed, which only a
failed run sees); the total mode needs the literal to succeed and the cell writable. -/
theorem spec_lit_getD [Inhabited K] {q : ℚ} :
    Spec m I (fun st => m.Needs ((∃ v, I.sem.lit p q = some v) ∧
        Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.lit p dst q)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some ((I.sem.lit p q).getD default) ∧
          PosKept st st' := by
  intro st hst
  rw [Wp, exec_instr, Mode.sat_map, Instr.run, Mode.sat_bind]
  have key : ∀ v, I.sem.lit p q = some v → m.Sat (fun r => Modifies
      [(dst.buf, dst.idx.eval, 1)] st.store r.1 ∧ r.1.read p dst.buf dst.idx.eval =
        some ((I.sem.lit p q).getD default) ∧ r.2 = st.pos)
      ((st.store.write p dst.buf dst.idx.eval v).map fun s' => (s', st.pos)) := fun v hv => by
    rw [Mode.sat_map]
    exact Mode.sat_write (hst.mono (·.2)) fun s' hs' =>
      ⟨Modifies.of_write hs', by rw [Store.read_of_write_eq_some hs', hv]; rfl, rfl⟩
  cases m
  · obtain ⟨v, hv⟩ := hst.1
    exact ⟨v, hv, key v hv⟩
  · exact key

/-- **A binary operation**, read back as the stored result (with `default` if it failed, which
only a failed run sees); the total mode needs the operation to succeed and the cell writable. -/
theorem spec_bin_getD [Inhabited K] {op : BinOp} {a b : K} :
    Spec m I (fun st => st.store.read p x.buf x.idx.eval = some a ∧
        st.store.read p y.buf y.idx.eval = some b ∧
        m.Needs ((∃ v, I.sem.bin p op a b = some v) ∧ Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.bin p op dst x y)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some ((I.sem.bin p op a b).getD default) ∧
          PosKept st st' := by
  intro st ⟨hx, hy, hst⟩
  rw [Wp, exec_instr, Mode.sat_map, Instr.run]
  simp only [hx, hy, Option.bind_some]
  rw [Mode.sat_bind]
  have key : ∀ v, I.sem.bin p op a b = some v → m.Sat (fun r => Modifies
      [(dst.buf, dst.idx.eval, 1)] st.store r.1 ∧ r.1.read p dst.buf dst.idx.eval =
        some ((I.sem.bin p op a b).getD default) ∧ r.2 = st.pos)
      ((st.store.write p dst.buf dst.idx.eval v).map fun s' => (s', st.pos)) := fun v hv => by
    rw [Mode.sat_map]
    exact Mode.sat_write (hst.mono (·.2)) fun s' hs' =>
      ⟨Modifies.of_write hs', by rw [Store.read_of_write_eq_some hs', hv]; rfl, rfl⟩
  cases m
  · obtain ⟨v, hv⟩ := hst.1
    exact ⟨v, hv, key v hv⟩
  · exact key

/-- **A unary operation**, read back as the stored result (with `default` if it failed, which
only a failed run sees); the total mode needs the operation to succeed and the cell writable. -/
theorem spec_un_getD [Inhabited K] {op : UnOp} {a : K} :
    Spec m I (fun st => st.store.read p x.buf x.idx.eval = some a ∧
        m.Needs ((∃ v, I.sem.un p op a = some v) ∧ Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.un p op dst x)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some ((I.sem.un p op a).getD default) ∧
          PosKept st st' := by
  intro st ⟨hx, hst⟩
  rw [Wp, exec_instr, Mode.sat_map, Instr.run]
  simp only [hx, Option.bind_some]
  rw [Mode.sat_bind]
  have key : ∀ v, I.sem.un p op a = some v → m.Sat (fun r => Modifies
      [(dst.buf, dst.idx.eval, 1)] st.store r.1 ∧ r.1.read p dst.buf dst.idx.eval =
        some ((I.sem.un p op a).getD default) ∧ r.2 = st.pos)
      ((st.store.write p dst.buf dst.idx.eval v).map fun s' => (s', st.pos)) := fun v hv => by
    rw [Mode.sat_map]
    exact Mode.sat_write (hst.mono (·.2)) fun s' hs' =>
      ⟨Modifies.of_write hs', by rw [Store.read_of_write_eq_some hs', hv]; rfl, rfl⟩
  cases m
  · obtain ⟨v, hv⟩ := hst.1
    exact ⟨v, hv, key v hv⟩
  · exact key

/-- **A literal**, read back without naming its value: the destination cell then holds the
semantics' literal, which exists (in every mode); the total mode needs the literal to succeed and
the cell writable. -/
theorem spec_lit_read {q : ℚ} :
    Spec m I (fun st => m.Needs ((∃ v, I.sem.lit p q = some v) ∧
        Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.lit p dst q)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        (∃ v, I.sem.lit p q = some v ∧ st'.store.read p dst.buf dst.idx.eval = some v) ∧
          PosKept st st' := by
  intro st hst
  rw [Wp, exec_instr, Mode.sat_map, Instr.run, Mode.sat_bind]
  have key : ∀ v, I.sem.lit p q = some v → m.Sat (fun r => Modifies
      [(dst.buf, dst.idx.eval, 1)] st.store r.1 ∧ (∃ v, I.sem.lit p q = some v ∧
        r.1.read p dst.buf dst.idx.eval = some v) ∧ r.2 = st.pos)
      ((st.store.write p dst.buf dst.idx.eval v).map fun s' => (s', st.pos)) := fun v hv => by
    rw [Mode.sat_map]
    exact Mode.sat_write (hst.mono (·.2)) fun s' hs' =>
      ⟨Modifies.of_write hs', ⟨v, hv, Store.read_of_write_eq_some hs'⟩, rfl⟩
  cases m
  · obtain ⟨v, hv⟩ := hst.1
    exact ⟨v, hv, key v hv⟩
  · exact key

/-- **A binary operation** on two stored values. -/
theorem spec_bin {op : BinOp} {a b v : K} (hv : I.sem.bin p op a b = some v) :
    Spec m I (fun st => st.store.read p x.buf x.idx.eval = some a ∧
        st.store.read p y.buf y.idx.eval = some b ∧
        m.Needs (Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.bin p op dst x y)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some v ∧ Costs (I.charge (.bin p op)) st st' ∧
          PosKept st st' := by
  intro st hst
  simp only [Wp, exec_instr, Mode.sat_map, Instr.run, hst.1, hst.2.1, hv, Option.bind_some]
  exact Mode.sat_write hst.2.2 fun s' hs' =>
    ⟨Modifies.of_write hs', Store.read_of_write_eq_some hs', rfl, rfl⟩

/-- **A unary operation** on a stored value. -/
theorem spec_un {op : UnOp} {a v : K} (hv : I.sem.un p op a = some v) :
    Spec m I (fun st => st.store.read p x.buf x.idx.eval = some a ∧
        m.Needs (Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.un p op dst x)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some v ∧ Costs (I.charge (.un p op)) st st' ∧
          PosKept st st' := by
  intro st hst
  simp only [Wp, exec_instr, Mode.sat_map, Instr.run, hst.1, hv, Option.bind_some]
  exact Mode.sat_write hst.2 fun s' hs' =>
    ⟨Modifies.of_write hs', Store.read_of_write_eq_some hs', rfl, rfl⟩

/-- **A copy** of a stored value. -/
theorem spec_copy {a : K} :
    Spec m I (fun st => st.store.read p x.buf x.idx.eval = some a ∧
        m.Needs (Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.copy p dst x)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some a ∧ Costs (I.charge (.copy p)) st st' ∧
          PosKept st st' := by
  intro st hst
  simp only [Wp, exec_instr, Mode.sat_map, Instr.run, hst.1, Option.bind_some]
  exact Mode.sat_write hst.2 fun s' hs' =>
    ⟨Modifies.of_write hs', Store.read_of_write_eq_some hs', rfl, rfl⟩

/-- **A draw** writes the next tape value of its distribution and advances that position. -/
theorem spec_draw {d : Dist} :
    Spec m I (fun st => m.Needs (Writable st.store p dst.buf dst.idx.eval 1))
      (.instr (.draw p d dst)) [(dst.buf, dst.idx.eval, 1)] fun st st' =>
        st'.store.read p dst.buf dst.idx.eval = some (I.tape d (st.pos d)) ∧
          Costs (I.charge (.draw p d)) st st' ∧
          st'.pos = Function.update st.pos d (st.pos d + 1) := by
  intro st hst
  rw [Wp, exec_instr, Mode.sat_map, Instr.run, Mode.sat_map]
  exact Mode.sat_write hst fun s' hs' =>
    ⟨Modifies.of_write hs', Store.read_of_write_eq_some hs', rfl, rfl⟩

/-- **A loop of draws** into consecutive cells (`NLAlib.Computation.exec_forRange_draw`): the
block holds the next `n` tape values and the position advances by `n`. -/
theorem spec_forRange_draw (d : Dist) (X off : ℕ) (n : IExp ℕ) (idx : ℕ → IExp ℕ)
    (hidx : ∀ i, (idx i).eval = off + i) :
    RoutineSpec m I (fun st => m.Needs (Writable st.store p X off n.eval))
      (Builder.forRange n fun i => Builder.ins (.draw p d ⟨X, idx i⟩)) [(X, off, n.eval)]
      fun st st' => (∀ i < n.eval, st'.store.read p X (off + i) = some (I.tape d (st.pos d + i))) ∧
        Costs (n.eval • I.charge (.draw p d)) st st' ∧
        st'.pos = Function.update st.pos d (st.pos d + n.eval) := by
  let Inv : St P K C → ℕ → St P K C → Prop := fun st₀ k st =>
    Modifies [(X, off, k)] st₀.store st.store ∧
      (∀ i < k, st.store.read p X (off + i) = some (I.tape d (st₀.pos d + i))) ∧
      Costs (k • I.charge (.draw p d)) st₀ st ∧
      st.pos = Function.update st₀.pos d (st₀.pos d + k)
  refine RoutineSpec.stmt (s := .loop n fun i => (Builder.ins (.draw p d ⟨X, idx i⟩)).run)
    (Triple.conseq (Triple.loop Inv (fun st _ => ⟨?_, fun i hi => absurd hi (by omega),
      by simp [Costs], by simp⟩) fun st₀ hst k hk st hinv => ?_) (fun _ h => h)
      fun _ _ _ h => ⟨h.1, h.2⟩)
  · exact ⟨rfl, fun _ _ _ _ => rfl⟩
  obtain ⟨hm, hrd, hcost, hpos⟩ := hinv
  refine (wp_seq).mpr ((wp_instr _).mpr ?_)
  simp only [Instr.run, Mode.sat_map]
  refine Mode.sat_write (hst.mono fun hW i hi => ?_) fun s' hs' => (wp_skip).mpr ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨len, hl, hlt⟩ := hW k hk
    exact ⟨len, by rw [hm.1]; exact hl, by rw [hidx]; omega⟩
  · refine (hm.trans (Modifies.of_write hs')).of_cells fun b i hb x hx => ?_
    have := blockDisjoint_iff.mp (hb _ List.mem_cons_self)
    rw [hidx] at hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rw [blockDisjoint_iff] <;> dsimp only at this ⊢ <;> omega
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Store.read_of_write_eq_some_of_ne hs' (Or.inr (by rw [hidx]; omega))]
      exact hrd i hi
    · rw [hidx] at hs'
      rw [Store.read_of_write_eq_some hs', hpos, Function.update_self]
  · change st.cnt + I.charge (.draw p d) = st₀.cnt + (k + 1) • I.charge (.draw p d)
    rw [hcost, succ_nsmul, add_assoc]
  · change Function.update st.pos d (st.pos d + 1) = _
    rw [hpos, Function.update_self, Function.update_idem, Nat.add_assoc]

/-! #### Frames of runs: liberal, from every state -/

/-- A copy modifies only its destination cell and keeps the tape positions. -/
theorem spec_copy_frame :
    Spec .liberal I (fun _ => True) (.instr (.copy p dst x)) [(dst.buf, dst.idx.eval, 1)]
      fun st st' => PosKept st st' := by
  intro st _ st' h
  rw [exec_instr, Instr.run] at h
  obtain ⟨⟨s', _⟩, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨_, -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨s'', hw, he⟩ := Option.map_eq_some_iff.mp hr
  cases he
  exact ⟨Modifies.of_write hw, rfl⟩

/-- A unary operation modifies only its destination cell and keeps the tape positions. -/
theorem spec_un_frame {op : UnOp} :
    Spec .liberal I (fun _ => True) (.instr (.un p op dst x)) [(dst.buf, dst.idx.eval, 1)]
      fun st st' => PosKept st st' := by
  intro st _ st' h
  rw [exec_instr, Instr.run] at h
  obtain ⟨⟨s', _⟩, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨_, -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨_, -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨s'', hw, he⟩ := Option.map_eq_some_iff.mp hr
  cases he
  exact ⟨Modifies.of_write hw, rfl⟩

/-- A binary operation modifies only its destination cell and keeps the tape positions. -/
theorem spec_bin_frame {op : BinOp} :
    Spec .liberal I (fun _ => True) (.instr (.bin p op dst x y)) [(dst.buf, dst.idx.eval, 1)]
      fun st st' => PosKept st st' := by
  intro st _ st' h
  rw [exec_instr, Instr.run] at h
  obtain ⟨⟨s', _⟩, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨_, -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨_, -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨_, -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨s'', hw, he⟩ := Option.map_eq_some_iff.mp hr
  cases he
  exact ⟨Modifies.of_write hw, rfl⟩

/-- A literal modifies only its destination cell and keeps the tape positions. -/
theorem spec_lit_frame {q : ℚ} :
    Spec .liberal I (fun _ => True) (.instr (.lit p dst q)) [(dst.buf, dst.idx.eval, 1)]
      fun st st' => PosKept st st' := by
  intro st _ st' h
  rw [exec_instr, Instr.run] at h
  obtain ⟨⟨s', _⟩, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨_, -, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨s'', hw, he⟩ := Option.map_eq_some_iff.mp hr
  cases he
  exact ⟨Modifies.of_write hw, rfl⟩

/-- A named kernel runs as its body, so it meets its body's specification. -/
theorem Spec.named {pre : St P K C → Prop} {s : Stmt P ι ℕ ℕ} {fp : List (ℕ × ℕ × ℕ)}
    {post : St P K C → St P K C → Prop} (name : String) (args : List (Arg ℕ ℕ))
    (h : Spec m I pre s fp post) : Spec m I pre (.named name args s) fp post :=
  fun st hst => (wp_named name args).mpr (h st hst)

/-- `skip` modifies nothing and keeps the tape positions. -/
theorem spec_skip_frame {fp : List (ℕ × ℕ × ℕ)} :
    Spec .liberal I (fun _ => True) .skip fp fun st st' => PosKept st st' :=
  fun _ _ => (wp_skip).mpr ⟨Modifies.refl _ _, rfl⟩

/-- Frames in sequence: two runs that modify only `fp` and keep the tape positions. -/
theorem Spec.seq_frame {fp : List (ℕ × ℕ × ℕ)} {s t : Stmt P ι ℕ ℕ}
    (hs : Spec .liberal I (fun _ => True) s fp fun st st' => PosKept st st')
    (ht : Spec .liberal I (fun _ => True) t fp fun st st' => PosKept st st') :
    Spec .liberal I (fun _ => True) (.seq s t) fp fun st st' => PosKept st st' :=
  (Spec.seq hs ht fun _ _ _ _ _ => trivial).conseq (fun _ h => h)
    (fun _ hx => (List.mem_append.mp hx).elim id id) fun _ _ _ ⟨_, h₁, h₂⟩ => h₂.trans h₁

/-- A loop of frames is a frame. -/
theorem Spec.loop_frame {fp : List (ℕ × ℕ × ℕ)} {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    (h : ∀ k < n.eval, Spec .liberal I (fun _ => True) (body k) fp fun st st' => PosKept st st') :
    Spec .liberal I (fun _ => True) (.loop n body) fp fun st st' => PosKept st st' :=
  Spec.loop (fun st₀ _ st => PosKept st₀ st) (fun _ _ => rfl) fun _ _ k hk =>
    (h k hk).conseq (fun _ _ => trivial) (fun _ h => h) fun _ _ hst hp => hp.trans hst

/-- A kernel call modifies only its output blocks and keeps the tape positions. -/
theorem spec_kcall_frame {o : ι} {dims : List (IExp ℕ)} {ins outs : List (ℕ × IExp ℕ)} :
    Spec .liberal I (fun _ => True) (.kcall o p dims ins outs)
      (kcallBlocks (outs.map fun x => (x.1, x.2.eval)) (I.kshape o (dims.map IExp.eval)).2)
      fun st st' => PosKept st st' := by
  intro st _ st' h
  rw [exec_kcall] at h
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨Modifies.of_kcallStore hs, rfl⟩

omit [AddMonoid C] in
/-- A footprint may be replaced by one whose blocks contain its blocks. -/
theorem Modifies.of_sub {fp fp' : List (ℕ × ℕ × ℕ)} {s s' : Store P K} (h : Modifies fp s s')
    (hsub : ∀ x ∈ fp, ∃ y ∈ fp', x.1 = y.1 ∧ y.2.1 ≤ x.2.1 ∧ x.2.1 + x.2.2 ≤ y.2.1 + y.2.2) :
    Modifies fp' s s' :=
  h.of_cells fun b i hb x hx => by
    obtain ⟨y, hy, h1, h2, h3⟩ := hsub x hx
    have := blockDisjoint_iff.mp (hb y hy)
    rw [blockDisjoint_iff]
    dsimp only at this ⊢
    omega

/-- A specification whose blocks lie in blocks of `fp'` has the footprint `fp'`. -/
theorem Spec.sub {pre : St P K C → Prop} {s : Stmt P ι ℕ ℕ} {fp fp' : List (ℕ × ℕ × ℕ)}
    {post : St P K C → St P K C → Prop} (h : Spec m I pre s fp post)
    (hsub : ∀ x ∈ fp, ∃ y ∈ fp', x.1 = y.1 ∧ y.2.1 ≤ x.2.1 ∧ x.2.1 + x.2.2 ≤ y.2.1 + y.2.2) :
    Spec m I pre s fp' post :=
  Triple.conseq h (fun _ h => h) fun _ _ _ hp => ⟨hp.1.of_sub hsub, hp.2⟩

/-- A frame whose blocks lie in blocks of `fp` is a frame of `fp`. -/
theorem Spec.frame_of_sub {fp fp' : List (ℕ × ℕ × ℕ)} {s : Stmt P ι ℕ ℕ}
    (h : Spec .liberal I (fun _ => True) s fp fun st st' => PosKept st st')
    (hsub : ∀ x ∈ fp, ∃ y ∈ fp', x.1 = y.1 ∧ y.2.1 ≤ x.2.1 ∧ x.2.1 + x.2.2 ≤ y.2.1 + y.2.2) :
    Spec .liberal I (fun _ => True) s fp' fun st st' => PosKept st st' :=
  Triple.conseq h (fun _ h => h) fun _ _ _ hp => ⟨hp.1.of_sub hsub, hp.2⟩

/-- A frame of one cell is a frame of every block containing it. -/
theorem Spec.frame_of_mem {fp : List (ℕ × ℕ × ℕ)} {s : Stmt P ι ℕ ℕ} {b i o N : ℕ}
    (h : Spec .liberal I (fun _ => True) s [(b, i, 1)] fun st st' => PosKept st st')
    (hi : o ≤ i ∧ i < o + N) (hfp : (b, o, N) ∈ fp) :
    Spec .liberal I (fun _ => True) s fp fun st st' => PosKept st st' :=
  Triple.conseq h (fun _ h => h) fun _ _ _ hp => ⟨hp.1.of_cells fun b' i' hb x hx => by
    rw [List.mem_singleton.mp hx]
    have := blockDisjoint_iff.mp (hb _ hfp)
    rw [blockDisjoint_iff]
    dsimp only at this ⊢
    omega, hp.2⟩

omit [DecidableEq P] [AddMonoid C] in
/-- A block inside a writable block is writable. -/
theorem Writable.of_le {s : Store P K} {b off n off' n' : ℕ} (h : Writable s p b off n)
    (h₁ : off ≤ off') (h₂ : off' + n' ≤ off + n) : Writable s p b off' n' := fun i hi => by
  obtain ⟨len, hl, hlt⟩ := h (off' - off + i) (by omega)
  exact ⟨len, hl, by omega⟩

omit [DecidableEq P] [AddMonoid C] in
/-- A writable nonempty block lies in a buffer of the store. -/
theorem Writable.exists_len {s : Store P K} {b off N : ℕ} (h : Writable s p b off N)
    (hN : 0 < N) : ∃ len, s.shape[b]? = some (p, len) ∧ off + N ≤ len := by
  obtain ⟨len, hl, hlt⟩ := h (N - 1) (by omega)
  exact ⟨len, hl, by omega⟩

/-- **A loop of literal writes into a block**: iteration $i$ writes the literal $q$ into a cell
of the block `(Y, off, N)`; the loop modifies only that block and keeps the tape positions, and in
the total mode succeeds given the literal and the block writable. -/
theorem spec_forRange_lit_frame {q : ℚ} {n : IExp ℕ} {idx : ℕ → IExp ℕ} {Y off N : ℕ}
    (hidx : ∀ i < n.eval, off ≤ (idx i).eval ∧ (idx i).eval < off + N) :
    RoutineSpec m I (fun st => m.Needs ((∃ v, I.sem.lit p q = some v) ∧
        Writable st.store p Y off N))
      (Builder.forRange n fun i => Builder.ins (.lit p ⟨Y, idx i⟩ q)) [(Y, off, N)]
      fun st st' => PosKept st st' := by
  refine RoutineSpec.stmt (s := .loop n fun i => (Builder.ins (.lit p ⟨Y, idx i⟩ q)).run)
    ((Spec.loop (fun st₀ _ st => st.pos = st₀.pos ∧ st.store.shape = st₀.store.shape)
      (fun _ _ => ⟨rfl, rfl⟩) fun st₀ hst₀ k hk => ?_).conseq (fun _ h => h) (fun _ h => h)
      fun _ _ _ h => h.1)
  refine (((RoutineSpec.ins (spec_lit_read (m := m) (p := p) (dst := ⟨Y, idx k⟩)
    (q := q))).spec.sub (fp' := [(Y, off, N)]) fun x hx =>
      ⟨_, List.mem_cons_self, ?_⟩).with_modifies
    ).conseq (fun st h => hst₀.mono fun ⟨hv, hw⟩ => ⟨hv, fun i hi => ?_⟩) (fun _ h => h)
      fun st st' h hp => ⟨hp.2.2.trans h.1, hp.1.1.trans h.2⟩
  · rw [List.mem_singleton.mp hx]
    exact ⟨rfl, (hidx k hk).1, by have := (hidx k hk).2; dsimp only; omega⟩
  · obtain ⟨len, hl, hlt⟩ := hw ((idx k).eval - off) (by have := hidx k hk; omega)
    exact ⟨len, by rw [h.2]; exact hl, by have := hidx k hk; dsimp only; omega⟩

/-! #### Conditionals, the empty builder, memory, and facts added to a specification -/

/-- **A conditional in a builder**, on a comparison whose outcome `r` the precondition fixes: the
arms are specified routines with one footprint. -/
theorem RoutineSpec.ifThenElse {c : CmpOp} {r : Bool} {tb eb : Builder P ι ℕ ℕ Unit}
    {pre preT preE : St P K C → Prop} {fp : List (ℕ × ℕ × ℕ)}
    {postT postE : St P K C → St P K C → Prop} (ht : RoutineSpec m I preT tb fp postT)
    (he : RoutineSpec m I preE eb fp postE)
    (hcmp : ∀ st, pre st → ∃ a b, st.store.read p x.buf x.idx.eval = some a ∧
      st.store.read p y.buf y.idx.eval = some b ∧ I.sem.cmp p c a b = some r)
    (hT : ∀ st, pre st → r = true → preT (st.addCnt (I.charge (.cmp p))))
    (hE : ∀ st, pre st → r = false → preE (st.addCnt (I.charge (.cmp p)))) :
    RoutineSpec m I pre (Builder.ifThenElse p c x y tb eb) fp fun st st' =>
      (r = true → postT (st.addCnt (I.charge (.cmp p))) st') ∧
        (r = false → postE (st.addCnt (I.charge (.cmp p))) st') :=
  RoutineSpec.stmt (s := .ite p c x y tb.run eb.run) (Spec.ite ht.spec he.spec hcmp hT hE)

/-- The empty builder modifies nothing and ends where it starts. -/
theorem routineSpec_pure {pre : St P K C → Prop} {fp : List (ℕ × ℕ × ℕ)} :
    RoutineSpec m I pre (pure () : Builder P ι ℕ ℕ Unit) fp fun st st' => st' = st :=
  ⟨fun f st => by
    change exec I (f ()).run st = (exec I .skip st).bind (exec I (f ()).run)
    rw [exec_skip, Option.bind_some],
    fun _ _ => (wp_skip).mpr ⟨Modifies.refl _ _, rfl⟩⟩

/-- An instruction keeps the current and peak memory. -/
theorem triple_instr_mem (i : Instr P ℕ ℕ) :
    Triple .liberal I (fun _ => True) (.instr i) fun st st' =>
      st'.cur = st.cur ∧ st'.peak = st.peak ∧ st'.curW = st.curW ∧ st'.peakW = st.peakW := by
  intro st _ st' h
  rw [exec_instr] at h
  obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `skip` keeps the current and peak memory. -/
theorem triple_skip_mem :
    Triple .liberal I (fun _ => True) .skip fun st st' =>
      st'.cur = st.cur ∧ st'.peak = st.peak ∧ st'.curW = st.curW ∧ st'.peakW = st.peakW :=
  fun _ _ => (wp_skip).mpr ⟨rfl, rfl, rfl, rfl⟩

/-- Runs in sequence that keep the current and peak memory keep it. -/
theorem Triple.seq_mem {s t : Stmt P ι ℕ ℕ}
    (hs : Triple .liberal I (fun _ => True) s fun st st' =>
      st'.cur = st.cur ∧ st'.peak = st.peak ∧ st'.curW = st.curW ∧ st'.peakW = st.peakW)
    (ht : Triple .liberal I (fun _ => True) t fun st st' =>
      st'.cur = st.cur ∧ st'.peak = st.peak ∧ st'.curW = st.curW ∧ st'.peakW = st.peakW) :
    Triple .liberal I (fun _ => True) (.seq s t) fun st st' =>
      st'.cur = st.cur ∧ st'.peak = st.peak ∧ st'.curW = st.curW ∧ st'.peakW = st.peakW :=
  (Triple.seq hs ht fun _ _ _ _ => trivial).conseq (fun _ h => h)
    fun _ _ _ ⟨_, h₁, h₂⟩ => ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
      h₂.2.2.2.trans h₁.2.2.2⟩

/-- A conditional whose arms keep the current and peak memory keeps it. -/
theorem Triple.ite_mem {c : CmpOp} {s t : Stmt P ι ℕ ℕ}
    (hs : Triple .liberal I (fun _ => True) s fun st st' =>
      st'.cur = st.cur ∧ st'.peak = st.peak ∧ st'.curW = st.curW ∧ st'.peakW = st.peakW)
    (ht : Triple .liberal I (fun _ => True) t fun st st' =>
      st'.cur = st.cur ∧ st'.peak = st.peak ∧ st'.curW = st.curW ∧ st'.peakW = st.peakW) :
    Triple .liberal I (fun _ => True) (.ite p c x y s t) fun st st' =>
      st'.cur = st.cur ∧ st'.peak = st.peak ∧ st'.curW = st.curW ∧ st'.peakW = st.peakW := by
  intro st _
  rw [wp_ite]
  intro ⟨b, st₁⟩ h
  obtain rfl : st₁ = { st with cnt := st.cnt + I.charge (.cmp p) } := snd_of_cmpStep_eq_some h
  cases b
  · exact wp_mono (ht _ trivial) fun _ h => h
  · exact wp_mono (hs _ trivial) fun _ h => h

/-- **A specification with a liberal fact of every run added**: what every successful run of `s`
satisfies (a frame, a kept memory) joins the postcondition, in every mode. -/
theorem Spec.and_liberal {pre : St P K C → Prop} {s : Stmt P ι ℕ ℕ} {fp : List (ℕ × ℕ × ℕ)}
    {post R : St P K C → St P K C → Prop} (h : Spec m I pre s fp post)
    (hR : Triple .liberal I (fun _ => True) s R) :
    Spec m I pre s fp fun st st' => post st st' ∧ R st st' := by
  intro st hst
  cases m
  · obtain ⟨st', hr, hm, hp⟩ := h st hst
    exact ⟨st', hr, hm, hp, hR st trivial st' hr⟩
  · exact fun st' hr => ⟨(h st hst st' hr).1, (h st hst st' hr).2, hR st trivial st' hr⟩

/-- A specified routine with a liberal fact of every run added to its postcondition. -/
theorem RoutineSpec.and_liberal {pre : St P K C → Prop} {r : Builder P ι ℕ ℕ Unit}
    {fp : List (ℕ × ℕ × ℕ)} {post R : St P K C → St P K C → Prop}
    (h : RoutineSpec m I pre r fp post) (hR : Triple .liberal I (fun _ => True) r.run R) :
    RoutineSpec m I pre r fp fun st st' => post st st' ∧ R st st' :=
  ⟨h.composable, h.spec.and_liberal hR⟩

/-- Consequence for specified routines, with a larger footprint. -/
theorem RoutineSpec.conseq {pre pre' : St P K C → Prop} {r : Builder P ι ℕ ℕ Unit}
    {fp fp' : List (ℕ × ℕ × ℕ)} {post post' : St P K C → St P K C → Prop}
    (h : RoutineSpec m I pre r fp post) (hpre : ∀ st, pre' st → pre st)
    (hfp : ∀ x ∈ fp, x ∈ fp') (hpost : ∀ st st', pre' st → post st st' → post' st st') :
    RoutineSpec m I pre' r fp' post' :=
  ⟨h.composable, h.spec.conseq hpre hfp hpost⟩

end Instructions

omit [DecidableEq P] [AddMonoid C] in
/-- The standard model on a range implies it on every smaller range. -/
theorem IsRelErrSem.mono_safe {u : P → ℝ} {dec : P → K → ℝ} {safe safe' : P → ℝ → Prop}
    {sem : ScalarSem P K} (h : IsRelErrSem u dec safe sem) (hs : ∀ p x, safe' p x → safe p x) :
    IsRelErrSem u dec safe' sem :=
  { h with
    bin_ok := fun p b x y hb hd hx => h.bin_ok p b x y hb hd (hs _ _ hx)
    lit_ok := fun p q hq => h.lit_ok p q (hs _ _ hq)
    convert_ok := fun p q x hx => h.convert_ok p q x (hs _ _ hx) }

/-! ### Certificates as specifications -/

section Certificates

variable {I : Interp P ι K C}

/-- **A footprint certificate is a specification**: from a state satisfying `pre` with writable
outputs, the routine succeeds and modifies only its output blocks. -/
theorem IsBlockRoutine.routineSpec {tag : P} {pre : Store P K → Prop}
    {outs : List (ℕ × ℕ × ℕ)} {r : Builder P ι ℕ ℕ Unit} (h : IsBlockRoutine I tag pre outs r) :
    RoutineSpec .total I (fun st => pre st.store ∧ WritableBlocks st.store tag outs) r outs
      fun _ _ => True := by
  refine ⟨h.composable, fun st hst => ?_⟩
  obtain ⟨out, ys, hr, hw⟩ := h.run st hst.1 hst.2
  exact ⟨out, hr, Modifies.of_writeBlocks hw, trivial⟩

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
  refine ⟨h.composable, fun st hst => ?_⟩
  obtain ⟨out, W, hr, hw, he⟩ := h.run st x hst.1 hst.2.1 hst.2.2
  have hm := Modifies.of_writeBlock hw
  rw [Array.size_ofFn] at hm
  refine ⟨out, hr, hm, fun i => dec tag (W i), fun i => ⟨W i, ?_, rfl⟩, he⟩
  rw [Store.read_of_writeBlock_eq_some_of_lt hw (by rw [Array.size_ofFn]; exact i.2)]
  simp

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
  obtain ⟨st', hrun, hp⟩ := h.exists_exec hpre
  rw [← Prog.exec_eq_exec_toStmt] at hrun
  obtain ⟨hs, _, h₁, h₂, h₃, rfl⟩ :=
    Prog.runsWithin_staticCost_of_exec_eq_some I prog N n hsize hrun
  exact ⟨hs, _, h₁, h₂, h₃, hp⟩

/-! ### Tactics -/

/-- Footprint side goals: membership in, disjointness of, distinctness of and arithmetic on
concrete block lists. `fp_omega [h₁, …]` adds the facts `hᵢ` (layout bounds such as
`Nat.mul_le_mul hr hk`), unfolds `NLAlib.Computation.BlocksDisjoint`,
`NLAlib.Computation.matBlock`, `List.Nodup` and `NLAlib.Computation.blockDisjoint_iff` in the
goal and those facts only (never the whole context), normalises products with `ring_nf` (so
`r * k` and `k * r` are one atom), clears the rest of the context (so `omega` stays fast in the
large contexts of program proofs) and closes with `omega`. **Every hypothesis the goal needs must
be passed** (`fp_omega [Nat.mul_le_mul hr hk, hlen]`, not `fp_omega [Nat.mul_le_mul hr hk]` with
`hlen` in the context). -/
syntax (name := fpOmega) "fp_omega" (" [" term,* "]")? : tactic

/-- The closing step of `fp_omega` on the goal and the named facts. -/
syntax (name := fpClose) "fp_close" (ppSpace colGt ident)* : tactic

macro_rules
  | `(tactic| fp_close $names*) => `(tactic| (
      (try simp only [BlocksDisjoint, matBlock, cellBlocks, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append,
        List.nodup_cons, List.nodup_nil, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false, and_true, not_or, forall_eq_or_imp, forall_eq, List.forall_mem_cons,
        blockDisjoint_iff, ne_eq, not_false_eq_true, IExp.eval_const, IExp.eval_ofNat,
        imp_false] at $names* ⊢)
      (try ring_nf (config := { ifUnchanged := .silent }) at $names* ⊢)
      (try clear * - $names*)
      omega))

macro_rules
  | `(tactic| fp_omega) => `(tactic| fp_close)
  | `(tactic| fp_omega [$hs,*]) => do
      let mut names : Array (Lean.TSyntax `ident) := #[]
      for _ in hs.getElems do
        names := names.push (Lean.mkIdent (Lean.Name.mkSimple s!"fp_fact{names.size}"))
      let mut tac ← `(tactic| fp_close $names*)
      for (h, nm) in (hs.getElems.zip names).reverse do
        tac ← `(tactic| (have $nm := $h; $tac:tactic))
      return tac

/-- The composability of a builder made of statements, scalar instructions, loops, conditionals,
index binders, scopes and named kernels in sequence: `NLAlib.Computation.ExecutionComposable.bind`
and the `executionComposable_` lemmas. -/
syntax (name := execComposable) "exec_composable" : tactic

macro_rules
  | `(tactic| exec_composable) => `(tactic| repeat' (first
      | exact executionComposable_stmt _ | exact executionComposable_ins _
      | exact executionComposable_named _ _ _ | exact executionComposable_forRange _ _
      | exact executionComposable_scope _ | exact executionComposable_ifThenElse _ _ _ _ _ _
      | exact executionComposable_bindIdx _ _ _ _ | refine ExecutionComposable.bind ?_ ?_))

/-- The read set of a conjunction of stored facts: `ReadsOnly F ?rs` for `F` built by `∧` from
cell reads, bundles of cells (`NLAlib.Computation.CellsHold`), blocks of cells with a property
each (`NLAlib.Computation.readsOnly_forall_read`), writable blocks and decoded vectors and
matrices, by `NLAlib.Computation.ReadsOnly.and`. -/
syntax (name := readsOnlyTac) "reads_only" : tactic

macro_rules
  | `(tactic| reads_only) => `(tactic| repeat' (first
      | exact readsOnly_cellsHold _ | exact readsOnly_read _ _ _ _
      | exact readsOnly_writable _ _ _ _ | exact readsOnly_readsDecoded _ _ _ _ _
      | exact readsOnly_holdsDecoded _ _ _ _ _ | exact readsOnly_forall_read _ _ _ _
      | refine ReadsOnly.and ?_ ?_))

/-- One step of a program proof: split a sequence, apply the triple `h` to its first statement
and leave its precondition and the continuation from the named next state; footprint side
goals closed by `assumption` or `fp_omega` are removed, the others stay in order (precondition,
continuation). -/
syntax (name := specStep) "spec_step " term : tactic

macro_rules
  | `(tactic| spec_step $h) => `(tactic| (
      first | rw [wp_seq] | skip
      (refine Triple.wp_of $h ?_ ?_) <;> try (first | assumption | fp_omega)))

/-- One call of a specified routine in a builder: `NLAlib.Computation.RoutineSpec.wp_run` for the
last call of a block, else `NLAlib.Computation.RoutineSpec.wp_bind`, with
side goals closed by `assumption` or `fp_omega` removed, as for `spec_step`. -/
syntax (name := specCall) "spec_call " term : tactic

macro_rules
  | `(tactic| spec_call $h) => `(tactic| (
      first
        | (refine RoutineSpec.wp_run $h ?_ ?_) <;> try (first | assumption | fp_omega)
        | (refine RoutineSpec.wp_bind $h ?_ ?_) <;> try (first | assumption | fp_omega)))

/-! ### Loops writing consecutive cells -/

section CellLoops

variable {m : Mode} {I : Interp P ι K C} {p : P}

/-- **A loop of copies into consecutive cells**: iteration $i$ copies the cell `sidx i` of `X`
(outside the destination block) into the cell $\mathit{off} + i$ of `Y`; the block then holds the
source values $a_i$, nothing else changes and the tape positions are kept; the total mode needs
the block writable. -/
theorem spec_forRange_copy {n : IExp ℕ} {Y off X : ℕ} {didx sidx : ℕ → IExp ℕ} (a : ℕ → K)
    (hd : ∀ i, (didx i).eval = off + i)
    (hs : ∀ i < n.eval, blockDisjoint (X, (sidx i).eval, 1) (Y, off, n.eval) = true) :
    RoutineSpec m I (fun st => (∀ i < n.eval, st.store.read p X (sidx i).eval = some (a i)) ∧
        m.Needs (Writable st.store p Y off n.eval))
      (Builder.forRange n fun i => Builder.ins (.copy p ⟨Y, didx i⟩ ⟨X, sidx i⟩)) [(Y, off, n.eval)]
      fun st st' => (∀ i < n.eval, st'.store.read p Y (off + i) = some (a i)) ∧ PosKept st st' := by
  refine RoutineSpec.stmt (s := .loop n fun i => (Builder.ins (.copy p ⟨Y, didx i⟩
    ⟨X, sidx i⟩)).run) ((Spec.loop (fun st₀ j st => st.pos = st₀.pos ∧
      Modifies [(Y, off, n.eval)] st₀.store st.store ∧
      ∀ i < j, st.store.read p Y (off + i) = some (a i)) (fun _ _ => ⟨rfl, .refl _ _, by simp⟩)
      fun st₀ hst₀ k hk => ?_).conseq (fun _ h => h) (fun _ h => h) fun _ _ _ h => ⟨h.2.2, h.1⟩)
  refine (((RoutineSpec.ins (spec_copy (m := m) (p := p) (dst := ⟨Y, didx k⟩) (x := ⟨X, sidx k⟩)
    (a := a k))).spec.with_modifies.sub (fp' := [(Y, off, n.eval)])
      fun x hx => ?_).conseq (fun st h => ⟨(readsOnly_read _ _ _ _).of_modifies
      (hst₀.1 k hk) h.2.1 (by fp_omega [hs k hk]), hst₀.2.mono fun hw => ?_⟩) (fun _ h => h)
      fun st st' h hp => ⟨hp.2.2.2.trans h.1, (h.2.1.trans (hp.1.of_sub
        (fp' := [(Y, off, n.eval)]) fun x hx => ?_)).mono (by simp), ?_⟩)
  · rw [List.mem_singleton.mp hx, hd]
    exact ⟨_, List.mem_cons_self, rfl, by dsimp only; omega, by dsimp only; omega⟩
  · intro i hi
    obtain ⟨len, hl, hlt⟩ := hw k hk
    exact ⟨len, by rw [h.2.1.1]; exact hl, by rw [hd]; omega⟩
  · rw [List.mem_singleton.mp hx, hd]
    exact ⟨_, List.mem_cons_self, rfl, by dsimp only; omega, by dsimp only; omega⟩
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ((readsOnly_read _ _ _ _).of_modifies (h.2.2 i hi) hp.1
        (by rw [hd]; fp_omega [hi])).trans rfl
    · rw [← hd]; exact hp.2.1

/-- **A loop of literal writes into consecutive cells**: iteration $i$ writes the literal $q$
into the cell $\mathit{off} + i$ of `Y`; the block then holds the literal, nothing else changes
and the tape positions are kept; the total mode needs the literal and the block writable. -/
theorem spec_forRange_lit {q : ℚ} {n : IExp ℕ} {Y off : ℕ} {didx : ℕ → IExp ℕ}
    (hd : ∀ i, (didx i).eval = off + i) :
    RoutineSpec m I (fun st => m.Needs ((∃ v, I.sem.lit p q = some v) ∧
        Writable st.store p Y off n.eval))
      (Builder.forRange n fun i => Builder.ins (.lit p ⟨Y, didx i⟩ q)) [(Y, off, n.eval)]
      fun st st' => (∀ i < n.eval, ∃ v, I.sem.lit p q = some v ∧
        st'.store.read p Y (off + i) = some v) ∧ PosKept st st' := by
  refine RoutineSpec.stmt (s := .loop n fun i => (Builder.ins (.lit p ⟨Y, didx i⟩ q)).run)
    ((Spec.loop (fun st₀ j st => st.pos = st₀.pos ∧
      Modifies [(Y, off, n.eval)] st₀.store st.store ∧
      ∀ i < j, ∃ v, I.sem.lit p q = some v ∧ st.store.read p Y (off + i) = some v)
      (fun _ _ => ⟨rfl, .refl _ _, by simp⟩)
      fun st₀ hst₀ k hk => ?_).conseq (fun _ h => h) (fun _ h => h) fun _ _ _ h => ⟨h.2.2, h.1⟩)
  refine (((RoutineSpec.ins (spec_lit_read (m := m) (p := p) (dst := ⟨Y, didx k⟩)
    (q := q))).spec.with_modifies.sub (fp' := [(Y, off, n.eval)])
      fun x hx => ?_).conseq (fun st h => hst₀.mono fun hw => ⟨hw.1, ?_⟩)
      (fun _ h => h) fun st st' h hp => ⟨hp.2.2.trans h.1, (h.2.1.trans (hp.1.of_sub
        (fp' := [(Y, off, n.eval)]) fun x hx => ?_)).mono (by simp),
        ?_⟩)
  · rw [List.mem_singleton.mp hx, hd]
    exact ⟨_, List.mem_cons_self, rfl, by dsimp only; omega, by dsimp only; omega⟩
  · intro i hi
    obtain ⟨len, hl, hlt⟩ := hw.2 k hk
    exact ⟨len, by rw [h.2.1.1]; exact hl, by rw [hd]; omega⟩
  · rw [List.mem_singleton.mp hx, hd]
    exact ⟨_, List.mem_cons_self, rfl, by dsimp only; omega, by dsimp only; omega⟩
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · obtain ⟨v, hv, hr⟩ := h.2.2 i hi
      exact ⟨v, hv, ((readsOnly_read _ _ _ _).of_modifies hr hp.1
        (by rw [hd]; fp_omega [hi])).trans rfl⟩
    · obtain ⟨v, hv, hr⟩ := hp.2.1
      exact ⟨v, hv, by rw [← hd]; exact hr⟩

end CellLoops

end NLAlib.Computation
