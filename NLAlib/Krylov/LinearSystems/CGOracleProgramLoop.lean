/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGOracleProgramExecution

/-!
# Exact guarded oracle CG loop

One actual oracle application replaces the dense product phase. The scalar guards, vector
updates, cached residual and SPD continuation are shared with the stored implementation.

## Main results

* `NLAlib.CGOracleImplementation.exec_exact_loop`: exact guarded oracle trajectory.
-/

@[expose] public section

namespace NLAlib.CGOracleImplementation

open Computation Computation.Builder CGImplementation
open scoped Matrix

variable {P ι : Type} [DecidableEq P]

private theorem composable_curvature (I : Interp P ι ℝ (OpCount P ι))
    (tag : P) (o : ι) (N : ℕ) : ExecutionComposable I (do
      stmt (.apply o tag 6 0 3 0 1)
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)) :=
  (executionComposable_single I (b := stmt (.apply o tag 6 0 3 0 1)) (fun _ => rfl)).bind
    (executionComposable_single I (b := dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)) (fun _ => rfl))

/-- The active oracle step computes its actual curvature, then executes the shared guarded
body or records rejection. A nonzero residual is required only to justify the division. -/
theorem exec_exact_active_step (tag : P) (o : ι) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ)
    (st : St P ℝ (OpCount P ι)) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (h : StoreContext tag (fun _ x => x) N A b v (v.r ⬝ᵥ v.r) 0 1 st.store false)
    (hr : v.r ⬝ᵥ v.r ≠ 0) :
    let μ := v.p ⬝ᵥ (A *ᵥ v.p)
    let next := if 0 < μ then cgStep A v else v
    ∃ out, exec (exactInterp (fun _ => A) ξ) (do
      stmt (.apply o tag 6 0 3 0 1)
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)
      ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
      ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      forRange (.const N) fun i => do
        ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩)) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b next (next.r ⬝ᵥ next.r)
        (if 0 < μ then if next.r ⬝ᵥ next.r = 0 then 1 else 0 else -1) 1 out.store false ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW := by
  let I : Interp P ι ℝ (OpCount P ι) := exactInterp (fun _ => A) ξ
  obtain ⟨mid, ecurv, hctx, hs, hμ, hp, hc, hw⟩ :=
    exec_exact_curvature tag o N A ξ st b v (v.r ⬝ᵥ v.r) 0 h
  obtain ⟨out, erun, hctx', hp', hc', hw', _, _, _⟩ :=
    CGImplementation.exec_exact_curvature_guard I rfl (fun _ => rfl) tag mid N A b v
      hctx hμ hr hs
  refine ⟨out, ?_, hctx', hp'.trans hp, hc'.trans hc, hw'.trans hw⟩
  change exec I ((do
    stmt (.apply o tag 6 0 3 0 1)
    dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)) >>= fun _ =>
      ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
      ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      forRange (.const N) fun i => do
        ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))).run st = some out
  rw [composable_curvature I tag o N, ecurv, Option.bind_some]
  exact erun

/-- The actual outer status guard skips all arithmetic after a stop, and otherwise executes
one oracle step. The store invariant needs no matrix-definiteness assumption. -/
theorem exec_exact_guarded_step (tag : P) (o : ι) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ)
    (st : St P ℝ (OpCount P ι)) (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (status : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v (v.r ⬝ᵥ v.r) status 1 st.store false)
    (hr : status = 0 → v.r ⬝ᵥ v.r ≠ 0) :
    let μ := v.p ⬝ᵥ (A *ᵥ v.p)
    let next := if status = 0 then if 0 < μ then cgStep A v else v else v
    ∃ out, exec (exactInterp (fun _ => A) ξ) (ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
      (do
      stmt (.apply o tag 6 0 3 0 1)
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)
      ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
      ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      forRange (.const N) fun i => do
        ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) (pure ()) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b next (next.r ⬝ᵥ next.r)
        (if status = 0 then if 0 < μ then if next.r ⬝ᵥ next.r = 0 then 1 else 0
          else -1 else status) 1 out.store false ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW := by
  classical
  dsimp only
  let I : Interp P ι ℝ (OpCount P ι) := exactInterp (fun _ => A) ξ
  have hz : st.store.read tag 7 6 = some 0 := by
    obtain ⟨word, hw, rfl⟩ := h.zero
    exact hw
  have hstatus : st.store.read tag 4 0 = some status := by
    obtain ⟨word, hw, rfl⟩ := h.statusValue
    exact hw
  have hcmp : cmpStep I tag .eq ⟨4, 0⟩ ⟨7, 6⟩ st =
      some (decide (status = 0), { st with cnt := st.cnt + I.charge (.cmp tag) }) := by
    simp only [cmpStep, IExp.eval_ofNat, hstatus, hz, Option.bind_some,
      show I.sem.cmp tag .eq status 0 = some (decide (status = 0)) from rfl, Option.map_some]
  let mid := { st with cnt := st.cnt + I.charge (.cmp tag) }
  by_cases hactive : status = 0
  · have hctx : StoreContext tag (fun _ x => x) N A b v (v.r ⬝ᵥ v.r) 0 1 mid.store false := by
      simpa only [hactive] using h
    obtain ⟨out, erun, hctx', hp, hc, hw⟩ :=
      exec_exact_active_step tag o N A ξ mid b v hctx (hr hactive)
    refine ⟨out, ?_, ?_, hp, hc, hw⟩
    · change exec I (.seq (.ite tag .eq ⟨4, 0⟩ ⟨7, 6⟩ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp, Option.bind_some]
      simpa only [hactive, decide_true, Bool.true_eq, ↓reduceIte] using erun
    · simpa only [if_pos hactive] using hctx'
  · refine ⟨mid, ?_, ?_, rfl, rfl, rfl⟩
    · change exec I (.seq (.ite tag .eq ⟨4, 0⟩ ⟨7, 6⟩ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp, Option.bind_some]
      simpa only [hactive, decide_false, Bool.false_eq_true, ↓reduceIte, Builder.run_pure]
        using exec_skip I mid
    · simpa only [if_neg hactive] using h

/-- The oracle step preserves unconditional safe statuses and conditional SPD recurrence
correspondence, including the terminal zero continuation. -/
theorem exec_exact_step (tag : P) (o : ι) (N j : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ)
    (st : St P ℝ (OpCount P ι)) (b : Fin N → ℝ)
    (h : LoopInvariant tag N A b j st.store false) :
    ∃ out, exec (exactInterp (fun _ => A) ξ) (ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
      (do
      stmt (.apply o tag 6 0 3 0 1)
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)
      ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
      ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      forRange (.const N) fun i => do
        ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) (pure ()) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      LoopInvariant tag N A b (j + 1) out.store false ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW := by
  obtain ⟨v, status, hctx, hstatus, hactive, hexact⟩ := h
  obtain ⟨out, erun, hctx', hp, hc, hw⟩ :=
    exec_exact_guarded_step tag o N A ξ st b v status hctx
      (fun hs hz => hactive hs (dotProduct_self_eq_zero.mp hz))
  exact ⟨out, erun, ⟨_, _, hctx', guarded_next_invariants hstatus hactive hexact⟩, hp, hc, hw⟩

/-- Every requested oracle loop executes, with exact SPD vector correspondence and safe
status for every real matrix. Zero input and zero dimension are included. -/
theorem exec_exact_loop (tag : P) (o : ι) (N q : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ)
    (st : St P ℝ (OpCount P ι)) (b : Fin N → ℝ)
    (h : StoreContext tag (fun _ x => x) N A b ⟨0, b, b⟩ (b ⬝ᵥ b)
      (if b = 0 then 1 else 0) 1 st.store false) :
    ∃ out, exec (exactInterp (fun _ => A) ξ) (forRange (.const q) fun _ =>
      (ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
      (do
      stmt (.apply o tag 6 0 3 0 1)
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)
      ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
      ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      forRange (.const N) fun i => do
        ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) (pure ()) : Builder P ι ℕ ℕ Unit)).run st = some out ∧
      LoopInvariant tag N A b q out.store false ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW := by
  let I : Interp P ι ℝ (OpCount P ι) := exactInterp (fun _ => A) ξ
  let R (j : ℕ) (out : St P ℝ (OpCount P ι)) :=
    LoopInvariant tag N A b j out.store false ∧ out.pos = st.pos ∧
      out.cur = st.cur ∧ out.curW = st.curW
  have h0 : R 0 st := ⟨loopInvariant_initial_of_storeContext tag N A b _ false h, rfl, rfl, rfl⟩
  have hstep (j : ℕ) (_hj : j < q) (mid : St P ℝ (OpCount P ι)) (hm : R j mid) :=
    (exec_exact_step tag o N j A ξ mid b hm.1).imp fun _ hout =>
      And.intro hout.1 (And.intro hout.2.1 (And.intro (hout.2.2.1.trans hm.2.1)
        (And.intro (hout.2.2.2.1.trans hm.2.2.1) (hout.2.2.2.2.trans hm.2.2.2))))
  obtain ⟨out, erun, hout⟩ := exists_exec_loop_eq_some_of_forall I (n := .const q) R h0 hstep
  refine ⟨out, ?_, hout⟩
  change exec I (.seq (.loop (.const q) _) .skip) st = _
  rw [exec_seq_skip]
  exact erun

end NLAlib.CGOracleImplementation
