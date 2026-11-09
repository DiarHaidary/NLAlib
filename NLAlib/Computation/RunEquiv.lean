/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.StraightLine

/-!
# Builders that run the same: index transport

A specification proved for a builder at one index expression applies to a builder that differs
only in index expressions of the same values: a loop body at the index variable `.var k` against
a specification at the constant `.const k`, or `2 * k + 1` against `1 + 2 * k`.
`NLAlib.Computation.RunEquiv I X Y` says that the two builders run the same under continuations
that run the same. It is built by congruence rules, one per builder form, whose index hypotheses
are equalities of values (`n.eval = n'.eval`, `NLAlib.Computation.Cell.normIdx` of one cell), so
the proof walks the program once and no step compares whole statements: the tactic `run_equiv`
applies the rules and closes each value equality by `rfl`. The transport is
`NLAlib.Computation.RoutineSpec.of_runEquiv`.

The default pattern makes transport unnecessary: state a block's specification for every index
expression, with hypotheses and conclusions about its value only (`(xo : IExp ℕ)` and `xo.eval`),
so that it applies at `.var k` and `.const k` alike (`NLAlib.Computation.spec_scalarBlock` is of
this form). Comparing two whole statements by `rfl` on their index normal forms
(`NLAlib.Computation.exec_eq_of_normIdx_eq`) can exhaust the kernel on a large block.

## Main definitions

* `NLAlib.Computation.RunEquiv`: builders that run the same under continuations that run the
  same.

## Main results

* `NLAlib.Computation.RunEquiv.ins`, `NLAlib.Computation.RunEquiv.forRange`,
  `NLAlib.Computation.RunEquiv.allocBind`, `NLAlib.Computation.RunEquiv.bindIdx`,
  `NLAlib.Computation.RunEquiv.ifThenElse`, `NLAlib.Computation.RunEquiv.scalarBlock`: the
  congruence rules.
* `NLAlib.Computation.RoutineSpec.of_runEquiv`: a specification transported along it.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] {I : Interp P ι K C}

/-- **Builders that run the same**: under any two continuations that run the same from every
state, the two builders run the same from every state. -/
def RunEquiv (I : Interp P ι K C) (X Y : Builder P ι ℕ ℕ Unit) : Prop :=
  ∀ k k' : Unit → Stmt P ι ℕ ℕ, (∀ st, exec I (k ()) st = exec I (k' ()) st) →
    ∀ st, exec I (ContT.run X k) st = exec I (ContT.run Y k') st

/-- Builders that run the same have runs that run the same. -/
theorem RunEquiv.exec_run_eq {X Y : Builder P ι ℕ ℕ Unit} (h : RunEquiv I X Y) (st : St P K C) :
    exec I X.run st = exec I Y.run st :=
  h _ _ (fun _ => rfl) st

/-- Running the same is symmetric. -/
theorem RunEquiv.symm {X Y : Builder P ι ℕ ℕ Unit} (h : RunEquiv I X Y) : RunEquiv I Y X :=
  fun k k' hk st => (h k' k (fun st => (hk st).symm) st).symm

/-- Statements that run the same give builders that run the same. -/
theorem RunEquiv.stmt {S S' : Stmt P ι ℕ ℕ} (h : ∀ st, exec I S st = exec I S' st) :
    RunEquiv I (Builder.stmt S) (Builder.stmt S') := by
  intro k k' hk st
  change exec I (.seq S (k ())) st = exec I (.seq S' (k' ())) st
  rw [exec_seq, exec_seq, h st]
  congr 1
  funext s
  exact hk s

/-- Two cells with the same buffer and index values have the same normal form. -/
theorem Cell.normIdx_eq_of_eval_eq {c c' : Cell ℕ ℕ} (hb : c.buf = c'.buf)
    (h : c.idx.eval = c'.idx.eval) : c.normIdx = c'.normIdx := by
  rw [Cell.normIdx, Cell.normIdx, hb, h]

/-- Instructions with the same index normal form run the same (`rfl` for an index variable
against its value; `NLAlib.Computation.Cell.normIdx_eq_of_eval_eq` for values equal by
arithmetic). -/
theorem RunEquiv.ins {i i' : Instr P ℕ ℕ} (h : i.normIdx = i'.normIdx) :
    RunEquiv I (Builder.ins i) (Builder.ins i') :=
  RunEquiv.stmt fun st => exec_eq_of_normIdx_eq I (by simp only [Stmt.normIdx, h]) st

/-- Kernel calls with dimensions and offsets of the same values run the same. -/
theorem RunEquiv.kcall {o : ι} {p : P} {dims dims' : List (IExp ℕ)}
    {ins ins' outs outs' : List (ℕ × IExp ℕ)} (hd : dims.map IExp.eval = dims'.map IExp.eval)
    (hi : ins.map (fun x => (x.1, x.2.eval)) = ins'.map fun x => (x.1, x.2.eval))
    (ho : outs.map (fun x => (x.1, x.2.eval)) = outs'.map fun x => (x.1, x.2.eval)) :
    RunEquiv I (Builder.stmt (.kcall o p dims ins outs))
      (Builder.stmt (.kcall o p dims' ins' outs')) :=
  RunEquiv.stmt fun st => by rw [exec_kcall, exec_kcall, hd, hi, ho]

/-- The empty builder runs as itself. -/
theorem RunEquiv.pure : RunEquiv I (pure () : Builder P ι ℕ ℕ Unit) (pure ()) :=
  fun _ _ hk st => hk st

/-- Builders in sequence that run the same run the same. -/
theorem RunEquiv.bind {a a' : Builder P ι ℕ ℕ Unit} {f f' : Unit → Builder P ι ℕ ℕ Unit}
    (ha : RunEquiv I a a') (hf : RunEquiv I (f ()) (f' ())) :
    RunEquiv I (a >>= f) (a' >>= f') := fun k k' hk st =>
  ha (fun u => ContT.run (f u) k) (fun u => ContT.run (f' u) k') (fun st => hf k k' hk st) st

/-- Allocations of lengths of the same value, then bodies that run the same, run the same. -/
theorem RunEquiv.allocBind {p : P} {len len' : IExp ℕ} {f f' : ℕ → Builder P ι ℕ ℕ Unit}
    (hl : len.eval = len'.eval) (hf : ∀ h, RunEquiv I (f h) (f' h)) :
    RunEquiv I (Builder.alloc p len >>= f) (Builder.alloc p len' >>= f') := by
  intro k k' hk st
  change exec I (.alloc p len fun h => ContT.run (f h) k) st =
    exec I (.alloc p len' fun h => ContT.run (f' h) k') st
  rw [exec_alloc, exec_alloc, hl, hf _ k k' hk]

/-- Scopes of builders that run the same run the same. -/
theorem RunEquiv.scope {b b' : Builder P ι ℕ ℕ Unit} (hb : RunEquiv I b b') :
    RunEquiv I (Builder.scope b) (Builder.scope b') :=
  RunEquiv.stmt hb.exec_run_eq

/-- Loops of lengths of the same value over bodies that run the same run the same. -/
theorem RunEquiv.forRange {n n' : IExp ℕ} {body body' : ℕ → Builder P ι ℕ ℕ Unit}
    (hn : n.eval = n'.eval) (hb : ∀ i, RunEquiv I (body i) (body' i)) :
    RunEquiv I (Builder.forRange n body) (Builder.forRange n' body') := by
  refine RunEquiv.stmt fun st => ?_
  rw [exec_loop, exec_loop, hn]
  congr 1
  funext s i
  exact (hb i).exec_run_eq s

/-- Index binders on cells of the same normal form, with bounds of the same value and bodies that
run the same, run the same. -/
theorem RunEquiv.bindIdx {p : P} {x x' : Cell ℕ ℕ} {bound bound' : IExp ℕ}
    {body body' : ℕ → Builder P ι ℕ ℕ Unit} (hx : x.normIdx = x'.normIdx)
    (hb : bound.eval = bound'.eval) (h : ∀ i, RunEquiv I (body i) (body' i)) :
    RunEquiv I (Builder.bindIdx p x bound body) (Builder.bindIdx p x' bound' body') := by
  refine RunEquiv.stmt fun st => ?_
  have e : toNatStep I p x st = toNatStep I p x' st := by
    rw [show toNatStep I p x st = toNatStep I p x.normIdx st from rfl, hx]
    rfl
  rw [exec_bindIdx, exec_bindIdx, e, hb]
  congr 1
  funext r
  split_ifs
  · exact (h _).exec_run_eq _
  · rfl

/-- Conditionals on cells of the same normal forms, with arms that run the same, run the same. -/
theorem RunEquiv.ifThenElse {p : P} {c : CmpOp} {x y x' y' : Cell ℕ ℕ}
    {t e t' e' : Builder P ι ℕ ℕ Unit} (hx : x.normIdx = x'.normIdx)
    (hy : y.normIdx = y'.normIdx) (ht : RunEquiv I t t') (he : RunEquiv I e e') :
    RunEquiv I (Builder.ifThenElse p c x y t e) (Builder.ifThenElse p c x' y' t' e') := by
  refine RunEquiv.stmt fun st => ?_
  have e₁ : cmpStep I p c x y st = cmpStep I p c x' y' st := by
    rw [show cmpStep I p c x y st = cmpStep I p c x.normIdx y.normIdx st from rfl, hx, hy]
    rfl
  rw [exec_ite, exec_ite, e₁]
  congr 1
  funext r
  split
  · exact ht.exec_run_eq _
  · exact he.exec_run_eq _

/-- Named kernels over builders that run the same run the same. -/
theorem RunEquiv.named {nm nm' : String} {args args' : List (Arg ℕ ℕ)}
    {b b' : Builder P ι ℕ ℕ Unit} (h : RunEquiv I b b') :
    RunEquiv I (Builder.named nm args b) (Builder.named nm' args' b') :=
  RunEquiv.stmt fun st => by rw [exec_named, exec_named, h.exec_run_eq]

/-- Straight-line blocks whose instructions have the same index normal forms run the same. -/
theorem RunEquiv.scalarBlock {p : P} {ops ops' : List (ScalarOp ℕ ℕ)}
    (h : ops.map (fun o => (o.toInstr p).normIdx) = ops'.map fun o => (o.toInstr p).normIdx) :
    RunEquiv I (scalarBlock p ops) (scalarBlock p ops') := by
  induction ops generalizing ops' with
  | nil =>
    obtain rfl := List.map_eq_nil_iff.mp h.symm
    exact RunEquiv.pure
  | cons o os ih =>
    cases ops' with
    | nil => simp at h
    | cons o' os' =>
      simp only [List.map_cons, List.cons.injEq] at h
      exact RunEquiv.bind (RunEquiv.ins h.1) (ih h.2)

/-- **Transport of a specified routine** to a builder that runs the same: the specification of
`r` holds of every builder `r'` with `NLAlib.Computation.RunEquiv I r' r` (a block at index
variables, specified at constants). -/
theorem RoutineSpec.of_runEquiv {m : Mode} {pre : St P K C → Prop} {r r' : Builder P ι ℕ ℕ Unit}
    {fp : List (ℕ × ℕ × ℕ)} {post : St P K C → St P K C → Prop}
    (h : RoutineSpec m I pre r fp post) (he : RunEquiv I r' r) :
    RoutineSpec m I pre r' fp post := by
  refine ⟨fun f st => ?_, fun st hst => ?_⟩
  · change exec I (ContT.run r' fun u => (f u).run) st = _
    rw [he _ _ (fun _ => rfl) st, he.exec_run_eq]
    exact h.composable f st
  · have := h.spec st hst
    rwa [Wp, ← he.exec_run_eq] at this

/-- Builders that run the same, from the builder forms: `NLAlib.Computation.RunEquiv.bind`,
`NLAlib.Computation.RunEquiv.ins` and the other congruence rules, applied at reducible
transparency, with every equation of index values or normal forms closed by `rfl`; what `rfl`
does not close (values equal by arithmetic) is left as a goal. Unfold the program's own
definitions first. -/
syntax (name := runEquivTac) "run_equiv" : tactic

macro_rules
  | `(tactic| run_equiv) => `(tactic| repeat' (first
      | with_reducible exact RunEquiv.pure
      | with_reducible apply RunEquiv.ins
      | with_reducible apply RunEquiv.kcall
      | with_reducible apply RunEquiv.forRange
      | with_reducible apply RunEquiv.bindIdx
      | with_reducible apply RunEquiv.ifThenElse
      | with_reducible apply RunEquiv.named
      | with_reducible apply RunEquiv.scope
      | with_reducible apply RunEquiv.allocBind
      | with_reducible apply RunEquiv.scalarBlock
      | with_reducible apply RunEquiv.bind
      | intro _
      | rfl))

end NLAlib.Computation
