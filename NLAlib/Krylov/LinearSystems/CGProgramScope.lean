/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Allocation
public import NLAlib.Krylov.LinearSystems.CGProgramTree

/-!
# Outer CG scope under arbitrary arithmetic

The actual three scoped allocations are independent of scalar arithmetic. This execution
wrapper is shared by the stored and oracle variants: the matrix allocation expression is
the stored dimension product or zero, respectively. It retains the actual memory widths.

## Main results

* `NLAlib.CGImplementation.exec_scope_of_exec_eq_some`: lift a workspace body execution
  through all three actual allocations and releases.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P]

/-- The five declared CG buffers, with the input words initialized and all outputs unwritten.
Both stored-entry and oracle backends use this same initial state. -/
def declaredState [Zero C] (tag : P) (N : ℕ) (b : Fin N → K) : St P K C :=
  inputState tag [(Array.ofFn b).map some, Array.replicate N none,
    Array.replicate N none, Array.replicate N none, Array.replicate 1 none]

variable [AddMonoid C]

/-- Release the scalar, product and matrix slots of either CG backend, preserving usage peaks. -/
def releaseWorkspace (tag : P) (matrixLen N width : ℕ) (out : St P K C) : St P K C :=
  ((out.release tag 9 width).release tag N width).release tag matrixLen width

/-- For a five-buffer declared state, execute the checked CG workspace body at its actual
handles, then release all three scoped buffers. Matrix capacity may be zero for oracle access;
the stored program uses the literal index expression for the dimension product. -/
theorem exec_scope_of_exec_eq_some (I : Interp P ι K C) (tag : P)
    (matrixLen : IExp ℕ) (N : ℕ) (st out : St P K C) (hsize : st.store.size = 5)
    (body : ℕ → ℕ → ℕ → Builder P ι ℕ ℕ Unit)
    (h : exec I (body 5 6 7).run
      (((st.allocate tag matrixLen.eval (I.width tag)).allocate tag N (I.width tag)).allocate
        tag 9 (I.width tag)) = some out) :
    exec I (scope do
      let A ← alloc tag matrixLen
      let s ← alloc tag (.const N)
      let scalars ← alloc tag 9
      body A s scalars).run st =
      some (releaseWorkspace tag matrixLen.eval N (I.width tag) out) := by
  change exec I (.seq (.alloc tag matrixLen fun A =>
    .alloc tag (.const N) fun s => .alloc tag 9 fun scalars => (body A s scalars).run)
      .skip) st = _
  rw [exec_seq_skip]
  apply exec_alloc_of_exec_eq_some
  apply exec_alloc_of_exec_eq_some
  apply exec_alloc_of_exec_eq_some
  simpa only [St.allocate, Array.size_push, hsize, Nat.reduceAdd, IExp.eval_const,
    IExp.eval_ofNat] using h

omit [AddMonoid C] in
/-- Releasing the three workspace slots preserves every read in the five declared buffers. -/
theorem read_releaseWorkspace (tag : P) (matrixLen N width : ℕ) (out : St P K C)
    (hsize : out.store.size = 8) (p : P) (buf i : ℕ) (hbuf : buf < 5) :
    (releaseWorkspace tag matrixLen N width out).store.read p buf i =
      out.store.read p buf i := by
  change Store.read out.store.pop.pop.pop p buf i = _
  rw [Store.read_pop_of_lt (by simp only [Array.size_pop, hsize]; omega),
    Store.read_pop_of_lt (by simp only [Array.size_pop, hsize]; omega),
    Store.read_pop_of_lt (by rw [hsize]; omega)]

omit [AddMonoid C] in
/-- The released workspace has exactly the declared input, three vectors and status buffer. -/
theorem shape_releaseWorkspace (tag : P) (matrixLen N width : ℕ) (out : St P K C)
    (hshape : out.store.shape = #[(tag, N), (tag, N), (tag, N), (tag, N), (tag, 1),
      (tag, matrixLen), (tag, N), (tag, 9)]) :
    (releaseWorkspace tag matrixLen N width out).store.shape =
      #[(tag, N), (tag, N), (tag, N), (tag, N), (tag, 1)] := by
  change Store.shape out.store.pop.pop.pop = _
  rw [Store.shape_pop, Store.shape_pop, Store.shape_pop, hshape]
  rfl

end NLAlib.CGImplementation
