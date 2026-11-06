/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exec

/-!
# Runs of loops: invariants of successful runs and the unrolled `whileFuel` (scaffold)

Statements for stage COMPDYN S1d (design note `docs/design/Computation-SignDeflatePrograms.md`,
§3): the refinement of a program to a shallow definition reads the value of a *successful* run,
so it needs the invariant of a loop in the direction "the run succeeded, so the invariant holds at
the end", and the unrolling of `whileFuel` by one test. `NLAlib/Computation/Exec.lean` is at the
size limit, so these go into a new file `NLAlib/Computation/Loops.lean` when proved.

## Main results

* `NLAlib.Computation.forall_of_exec_loop_eq_some`: the invariant of a successful loop.
* `NLAlib.Computation.exec_whileFuel_of_eval_eq_zero`,
  `NLAlib.Computation.exec_whileFuel_of_eval_eq_succ`: `whileFuel` unrolled.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C)

/-- **The invariant of a successful loop**: if `R 0` holds at the start and, for each index `i`
below the bound, every successful run of the body from a state satisfying `R i` ends in a state
satisfying `R (i + 1)`, then a successful run of the loop ends in a state satisfying `R n`. No
printed source.
Proof: `rw [exec_loop] at h`; `generalize n.eval = m at hstep h`; induction on `m` with
`List.range_succ`, `List.foldlM_append` and `Option.bind_eq_some_iff` (the converse of
`NLAlib.Computation.exists_exec_loop_eq_some_of_forall`). S, about 12 lines. -/
theorem forall_of_exec_loop_eq_some {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st st' : St P K C} (R : ℕ → St P K C → Prop) (h0 : R 0 st)
    (hstep : ∀ i < n.eval, ∀ st₁ st₂, R i st₁ → exec I (body i) st₁ = some st₂ → R (i + 1) st₂)
    (h : exec I (.loop n body) st = some st') : R n.eval st' := by
  rw [exec_loop] at h
  generalize n.eval = m at hstep h ⊢
  induction m generalizing st' with
  | zero =>
    simp only [List.range_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact h0
  | succ m ih =>
    rw [List.range_succ, List.foldlM_append] at h
    obtain ⟨s, hs, h'⟩ := Option.bind_eq_some_iff.mp h
    have h2 : exec I (body m) s = some st' := by simpa [List.foldlM_cons] using h'
    exact hstep m (Nat.lt_succ_self m) s st' (ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi)) hs) h2

/-- **`whileFuel` with no fuel fails**: a `whileFuel` loop whose fuel evaluates to $0$ fails (the
test is never found false). No printed source.
Proof: `rw [exec, hf]`; `List.range_zero`, `List.foldlM_nil`, then `if_pos rfl`. S, 2 lines. -/
theorem exec_whileFuel_of_eval_eq_zero {fuel : IExp ℕ} (hf : fuel.eval = 0) (p : P) (c : CmpOp)
    (x y : Cell ℕ ℕ) (body : Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.whileFuel fuel p c x y body) st = none := by
  rw [exec, hf, List.range_zero, List.foldlM_nil]
  simp only [Option.pure_def, Option.bind_some, if_true]

/-- **`whileFuel` unrolled by one test**: with fuel $j + 1$, the loop compares; if the comparison
is true it runs the body and continues with fuel $j$, and otherwise it stops in the charged
state. No printed source.
Proof: `rw [exec, hf, List.range_succ_eq_map, List.foldlM_cons]`; the step function ignores its
index, so `List.foldlM_map` turns the rest into the fold over `List.range j`; when the comparison
is false the rest is the identity on `(_, false)` (induction on the list, a private lemma), and
when it is true it is the run of `.whileFuel (.const j) …` (`IExp.eval_const`), by cases on
`exec I body r.2`. M, about 25 lines. -/
theorem exec_whileFuel_of_eval_eq_succ {fuel : IExp ℕ} {j : ℕ} (hf : fuel.eval = j + 1) (p : P)
    (c : CmpOp) (x y : Cell ℕ ℕ) (body : Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.whileFuel fuel p c x y body) st = (cmpStep I p c x y st).bind fun r =>
      if r.1 then (exec I body r.2).bind (exec I (.whileFuel (.const j) p c x y body))
      else some r.2 := by
  sorry

end NLAlib.Computation
