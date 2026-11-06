/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exec

/-!
# Scoped allocation states and execution

The two state updates below are exactly the allocation and release records in `exec_alloc`.
They expose the same bookkeeping for arbitrary word carriers, charges and cell widths, so
exact and rounded execution proofs can share their outer scope argument.

## Main results

* `NLAlib.Computation.exec_alloc_of_exec_eq_some`: a checked body execution lifts through its
  actual allocation and release, retaining all counters and both memory ledgers.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Push an uninitialized buffer and update the actual cell and bit memory ledgers. -/
def St.allocate (st : St P K C) (tag : P) (len width : ℕ) : St P K C :=
  { st with
    store := st.store.push (tag, Array.replicate len none)
    cur := Function.update st.cur tag (st.cur tag + len)
    peak := Function.update st.peak tag (max (st.peak tag) (st.cur tag + len))
    curW := st.curW + len * width
    peakW := max st.peakW (st.curW + len * width) }

/-- Pop the scoped buffer and subtract its cell and bit capacity, preserving peak usage. -/
def St.release (st : St P K C) (tag : P) (len width : ℕ) : St P K C :=
  { st with
    store := st.store.pop
    cur := Function.update st.cur tag (st.cur tag - len)
    curW := st.curW - len * width }

omit [AddMonoid C] in
/-- Allocating a buffer appends exactly its tag and capacity to the store shape. -/
theorem St.shape_allocate (st : St P K C) (tag : P) (len width : ℕ) :
    (st.allocate tag len width).store.shape = st.store.shape.push (tag, len) := by
  simp only [St.allocate, Store.shape, Array.map_push, Array.size_replicate]

omit [AddMonoid C] in
/-- Allocation preserves every read in an existing buffer, independently of word width
and of the new buffer's tag and capacity. -/
theorem St.read_allocate_of_lt (st : St P K C) (tag : P) (len width : ℕ)
    (p : P) (buf idx : ℕ) (hbuf : buf < st.store.size) :
    (st.allocate tag len width).store.read p buf idx = st.store.read p buf idx :=
  Store.read_push_of_lt hbuf

/-- An actual body execution lifts through the corresponding allocation and scope release.
No scalar correctness, zero-width, initialization or numerical output premise is needed. -/
theorem exec_alloc_of_exec_eq_some (I : Interp P ι K C) (tag : P) (len : IExp ℕ)
    (body : ℕ → Stmt P ι ℕ ℕ) (st out : St P K C)
    (h : exec I (body st.store.size) (st.allocate tag len.eval (I.width tag)) = some out) :
    exec I (.alloc tag len body) st = some (out.release tag len.eval (I.width tag)) := by
  rw [exec_alloc]
  change (exec I (body st.store.size) (st.allocate tag len.eval (I.width tag))).map
    (fun next => next.release tag len.eval (I.width tag)) = _
  rw [h]
  rfl

end NLAlib.Computation
