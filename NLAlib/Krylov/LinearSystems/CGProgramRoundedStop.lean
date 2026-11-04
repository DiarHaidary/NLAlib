/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramRoundedStep

/-!
# Actual rounded CG cache and stop operations

The new residual dot is copied into the cache only after the direction quotient and update.
The actual decoded zero comparison then writes the stored positive flag. The flag is the
rounded literal-one decoding; this module does not identify it with exact real one.

## Main results

* `NLAlib.CGImplementation.exec_rounded_cache_and_stop`: actual final copy and stop guard.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation
open scoped Matrix

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {u : P → ℝ} {dec : P → K → ℝ}

/-- The actual cache copy preserves the computed word without introducing arithmetic error.
It updates the decoded cache after the direction has consumed its old value. -/
theorem exec_rounded_cache_copy (I : Interp P ι K C) (tag : P) (st : St P K C) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (ν νnext status flag : ℝ) (h : StoreContext tag dec N A b v ν status flag st.store)
    (hnext : ∃ w, st.store.read tag 7 1 = some w ∧ dec tag w = νnext) :
    ∃ out, exec I (Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)).run st = some out ∧
      StoreContext tag dec N A b v νnext status flag out.store ∧
      ∀ q buf idx, (q ≠ tag ∨ buf ≠ 7 ∨ idx ≠ 0) →
        out.store.read q buf idx = st.store.read q buf idx := by
  obtain ⟨word, hnext, hdec⟩ := hnext
  obtain ⟨store, _, hrun, hshape, hread, hf⟩ := exec_scalar_copy I tag st
    ⟨7, 0⟩ ⟨7, 1⟩ word hnext ⟨9, by simp [h.shape, workspaceShape], by norm_num⟩
  refine ⟨{ st with store := store, cnt := st.cnt + I.charge (.copy tag) }, hrun, ?_, hf⟩
  apply h.replace_registers hshape
  · intro buf idx hcell _
    exact hf tag buf idx (Or.inr hcell)
  · exact ⟨word, hread, hdec⟩
  · obtain ⟨w, hw, hdec⟩ := h.statusValue
    exact ⟨w, (hf tag 4 0 (Or.inr (Or.inl (by norm_num)))).trans hw, hdec⟩

/-- The actual decoded zero comparison records the stored positive flag precisely when
the new cache is zero. Other vector, scalar and input buffers retain their actual words. -/
theorem exec_rounded_stop_guard (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (ν status flag : ℝ) (h : StoreContext tag dec N A b v ν status flag st.store) :
    ∃ out, exec I (Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
      (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())).run st = some out ∧
      StoreContext tag dec N A b v ν (if ν = 0 then flag else status) flag out.store ∧
      ∀ q buf idx, buf ≠ 4 → out.store.read q buf idx = st.store.read q buf idx := by
  classical
  obtain ⟨wν, hν, hνdec⟩ := h.squaredResidual
  obtain ⟨zero, hz, hzdec⟩ := h.zero
  obtain ⟨positive, hp, hpdec⟩ := h.positive
  have hcmpsem : I.sem.cmp tag .eq wν zero = some (if ν = 0 then true else false) := by
    by_cases hνzero : ν = 0 <;> simpa [hνdec, hzdec, hνzero] using hsem.cmp_eq tag wν zero
  have hcmp : cmpStep I tag .eq ⟨7, 0⟩ ⟨7, 6⟩ st =
      some ((if ν = 0 then true else false), { st with cnt := st.cnt + I.charge (.cmp tag) }) := by
    simp only [cmpStep, IExp.eval_ofNat, hν, hz, Option.bind_some, hcmpsem, Option.map_some]
  let mid : St P K C := { st with cnt := st.cnt + I.charge (.cmp tag) }
  by_cases hzero : ν = 0
  · obtain ⟨store, _, hrun, hshape, hread, hf⟩ := exec_scalar_copy I tag mid
      ⟨4, 0⟩ ⟨7, 7⟩ positive hp
      ⟨1, by simp [mid, h.shape, workspaceShape], by norm_num⟩
    refine ⟨{ mid with store := store, cnt := mid.cnt + I.charge (.copy tag) }, ?_, ?_, ?_⟩
    · change exec I (.seq (.ite tag .eq ⟨7, 0⟩ ⟨7, 6⟩ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp, Option.bind_some]
      simpa only [hzero, decide_true, Bool.true_eq, ↓reduceIte] using hrun
    · rw [if_pos hzero]
      apply h.replace_registers hshape
      · intro buf idx _ hcell
        exact hf tag buf idx (Or.inr hcell)
      · exact ⟨wν, (hf tag 7 0 (Or.inr (Or.inl (by norm_num)))).trans hν, hνdec⟩
      · exact ⟨positive, hread, hpdec⟩
    · intro q buf idx hb
      exact hf q buf idx (Or.inr (Or.inl hb))
  · refine ⟨mid, ?_, ?_, fun _ _ _ _ => rfl⟩
    · change exec I (.seq (.ite tag .eq ⟨7, 0⟩ ⟨7, 6⟩ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp, Option.bind_some]
      simpa only [hzero, decide_false, Bool.false_eq_true, ↓reduceIte, Builder.run_pure]
        using exec_skip I mid
    · simpa only [if_neg hzero] using h

/-- The canonical final copy and guard execute with the newly computed residual word.
The iterate, residual and direction are retained, including a zero terminal next state. -/
theorem exec_rounded_cache_and_stop (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (ν νnext status flag : ℝ) (h : StoreContext tag dec N A b v ν status flag st.store)
    (hnext : ∃ w, st.store.read tag 7 1 = some w ∧ dec tag w = νnext) :
    ∃ out, exec I (do
      Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()) : Builder P ι ℕ ℕ Unit).run st =
      some out ∧ StoreContext tag dec N A b v νnext
        (if νnext = 0 then flag else status) flag out.store ∧
      ∀ idx, idx ≠ 0 → out.store.read tag 7 idx = st.store.read tag 7 idx := by
  obtain ⟨mid, hrun, hctx, hcopyframe⟩ := exec_rounded_cache_copy I tag st N A b v
    ν νnext status flag h hnext
  obtain ⟨out, hout, hctx', hstopframe⟩ := exec_rounded_stop_guard I tag hsem mid N A b v
    νnext status flag hctx
  refine ⟨out, ?_, hctx', ?_⟩
  · rw [exec_run_bind I (b := Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩))
      (fun _ => rfl), hrun, Option.bind_some]
    exact hout
  · intro idx hi
    exact (hstopframe tag 7 idx (by norm_num)).trans
      (hcopyframe tag 7 idx (Or.inr (Or.inr hi)))

end NLAlib.CGImplementation
