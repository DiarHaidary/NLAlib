/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Allocation
public import NLAlib.Krylov.Processes.LanczosProgramTree

/-!
# Scoped Lanczos workspace under arbitrary arithmetic

The stored and oracle programs share three scoped allocations after their six declared
buffers. This wrapper retains actual scalar semantics and memory widths. Matrix capacity is
the stored dimension product or zero; no numerical correctness or initialized-state premise
is required beyond execution of the actual workspace body.

## Main results

* `NLAlib.LanczosImplementation.exec_scope_of_exec_eq_some`: execute and release the workspace.
* `NLAlib.LanczosImplementation.read_releaseWorkspace`: preserve declared output reads.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Release the two scalar registers, work vector and matrix slot, retaining usage peaks. -/
def releaseWorkspace (tag : P) (matrixLen N width : ℕ) (out : St P K C) : St P K C :=
  ((out.release tag 2 width).release tag N width).release tag matrixLen width

/-- A successful body at the actual Lanczos workspace handles executes within all three
canonical allocations and scope cleanup, with arbitrary words, arithmetic and widths. -/
theorem exec_scope_of_exec_eq_some (I : Interp P ι K C) (tag : P)
    (matrixLen : IExp ℕ) (N : ℕ) (st out : St P K C) (hsize : st.store.size = 6)
    (body : ℕ → ℕ → ℕ → Builder P ι ℕ ℕ Unit)
    (h : exec I (body 6 7 8).run
      (((st.allocate tag matrixLen.eval (I.width tag)).allocate tag N (I.width tag)).allocate
        tag 2 (I.width tag)) = some out) :
    exec I (scope do
      let A ← alloc tag matrixLen
      let work ← alloc tag (.const N)
      let scalars ← alloc tag 2
      body A work scalars).run st =
      some (releaseWorkspace tag matrixLen.eval N (I.width tag) out) := by
  change exec I (.seq (.alloc tag matrixLen fun A =>
    .alloc tag (.const N) fun work => .alloc tag 2 fun scalars => (body A work scalars).run)
      .skip) st = _
  rw [exec_seq_skip]
  apply exec_alloc_of_exec_eq_some
  apply exec_alloc_of_exec_eq_some
  apply exec_alloc_of_exec_eq_some
  simpa only [St.allocate, Array.size_push, hsize, Nat.reduceAdd, IExp.eval_const,
    IExp.eval_ofNat] using h

omit [AddMonoid C] in
/-- Releasing the workspace preserves every read in the six declared Lanczos buffers. -/
theorem read_releaseWorkspace (tag : P) (matrixLen N width : ℕ) (out : St P K C)
    (hsize : out.store.size = 9) (p : P) (buf i : ℕ) (hbuf : buf < 6) :
    (releaseWorkspace tag matrixLen N width out).store.read p buf i =
      out.store.read p buf i := by
  change Store.read out.store.pop.pop.pop p buf i = _
  rw [Store.read_pop_of_lt (by simp only [Array.size_pop, hsize]; omega),
    Store.read_pop_of_lt (by simp only [Array.size_pop, hsize]; omega),
    Store.read_pop_of_lt (by rw [hsize]; omega)]

omit [AddMonoid C] in
/-- The three releases leave exactly the six declared Lanczos buffer capacities. -/
theorem shape_releaseWorkspace (tag : P) (matrixLen N q width : ℕ) (out : St P K C)
    (hshape : out.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, matrixLen), (tag, N), (tag, 2)]) :
    (releaseWorkspace tag matrixLen N width out).store.shape =
      #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N)] := by
  change Store.shape out.store.pop.pop.pop = _
  rw [Store.shape_pop, Store.shape_pop, Store.shape_pop, hshape]
  rfl

end NLAlib.LanczosImplementation
