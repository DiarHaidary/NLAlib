/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exact
public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# Stored state of the concrete Lanczos program

The fixed nine-buffer layout retains the input, loaded matrix, completed basis and
coefficient prefixes, input norm, previous vector and persistent comparison zero. The state
is an execution invariant proved from the actual program, not an outer target premise.

## Main definitions

* `NLAlib.LanczosImplementation.workspaceShape`: dense or reserved-empty workspace layout.
* `NLAlib.LanczosImplementation.State`: exact stored recurrence-prefix invariant.
* `NLAlib.LanczosImplementation.stepCount`: approved componentwise per-step budget.

## Main results

The invariant is initialized in `LanczosProgramInitialization.lean` and advanced by the
actual Paige-order kernels in `LanczosProgramStep.lean`.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation

variable {P ι : Type} [DecidableEq P]

/-- The six declared Lanczos buffers, with input words initialized and outputs unwritten.
Stored-entry and oracle execution share this initial layout and zero resource counters. -/
def declaredState {K C : Type} [Zero C] (tag : P) (N q : ℕ) (b : Fin N → K) : St P K C :=
  inputState tag [(Array.ofFn b).map some, Array.replicate (N * (q + 1)) none,
    Array.replicate q none, Array.replicate (q + 1) none, Array.replicate 1 none,
    Array.replicate N none]

/-- The fixed nine-buffer Lanczos layout. Matrix-free execution reserves an empty slot 6;
the default stored-matrix specialization retains the original dense matrix capacity. -/
def workspaceShape (tag : P) (N q : ℕ) (storedMatrix : Bool := true) : Array (P × ℕ) :=
  #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N),
    (tag, if storedMatrix then N * N else 0), (tag, N), (tag, 2)]

/-- The exact stored state after initialization and the first `j` concrete Lanczos steps.
The nine buffers are the six declared buffers followed by loaded matrix, work vector and
two scalar scratch cells. Matrix-free execution reserves the matrix slot empty.
The stored-matrix parameter defaults to true, preserving the dense invariant.
Only the negative scratch cell and work vector are unconstrained.
This is an induction invariant proved from execution, not an extra target premise. -/
structure State (tag : P) (N q j : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (st : St P ℝ (OpCount P ι)) (storedMatrix : Bool := true) : Prop where
  /-- Exact shape of the declared and scoped workspace buffers. -/
  shape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
    (tag, 1), (tag, N), (tag, if storedMatrix then N * N else 0), (tag, N), (tag, 2)]
  /-- The declared input is retained. -/
  input : ∀ i : Fin N, st.store.read tag 0 i = some (b i)
  /-- Stored execution has loaded the matrix column-major; matrix-free execution uses no slot. -/
  matrix : if storedMatrix then Holds st.store tag 6 0 A else True
  /-- Every computed basis column agrees with its exact recurrence state. -/
  basis : ∀ c ≤ j, ∀ i : Fin N,
    st.store.read tag 1 (N * c + i) = some ((lanczosState A b c).cur i)
  /-- Every completed diagonal coefficient agrees with the recurrence. -/
  alpha : ∀ c < j,
    st.store.read tag 2 c = some (lanczosAlpha A (lanczosState A b c))
  /-- The initial and all completed off-diagonal coefficients agree with the recurrence. -/
  beta : ∀ c ≤ j, st.store.read tag 3 c = some ((lanczosState A b c).beta)
  /-- The actual input norm has its exact arithmetic value. -/
  inputNorm : st.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖
  /-- The previous-vector buffer holds the previous exact state vector. -/
  prev : ∀ i : Fin N, st.store.read tag 5 i = some ((lanczosState A b j).prev i)
  /-- The persistent comparison scalar remains exact zero. -/
  zero : st.store.read tag 8 0 = some 0

/-- At the final iteration, releasing the three scoped workspace buffers preserves all
six declared outputs. The statement applies to stored and matrix-free workspace layouts. -/
theorem State.holds_pop_pop_pop {tag : P} {N q : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {st : St P ℝ (OpCount P ι)} {storedMatrix : Bool}
    (h : State tag N q q A b st storedMatrix) :
    Holds st.store.pop.pop.pop tag 0 0 (fun i (_ : Fin 1) => b i) ∧
    Holds st.store.pop.pop.pop tag 1 0 (lanczosMatrix A b (q + 1)) ∧
    Holds st.store.pop.pop.pop tag 2 0
      (fun (j : Fin q) (_ : Fin 1) => lanczosAlpha A (lanczosState A b j)) ∧
    Holds st.store.pop.pop.pop tag 3 0
      (fun (j : Fin (q + 1)) (_ : Fin 1) => (lanczosState A b j).beta) ∧
    Store.read st.store.pop.pop.pop tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
    Holds st.store.pop.pop.pop tag 5 0
      (fun i (_ : Fin 1) => (lanczosState A b q).prev i) := by
  have hs : st.store.size = 9 := by
    simpa [Store.shape] using congrArg Array.size h.shape
  have hf (p : P) (k i : ℕ) (hk : k < 6) :
      Store.read st.store.pop.pop.pop p k i = st.store.read p k i := by
    rw [Store.read_pop_of_lt (by simp only [Array.size_pop]; omega),
      Store.read_pop_of_lt (by simp only [Array.size_pop]; omega)]
    exact Store.read_pop_of_lt (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [hf tag 0 _ (by omega)]
    simpa using h.input i
  · intro i j
    rw [hf tag 1 _ (by omega)]
    simpa only [lanczosMatrix, Matrix.of_apply, zero_add, Nat.add_comm] using
      h.basis j (Nat.le_of_lt_succ j.isLt) i
  · intro i j
    rw [hf tag 2 _ (by omega)]
    simpa using h.alpha i i.isLt
  · intro i j
    rw [hf tag 3 _ (by omega)]
    simpa using h.beta i (Nat.le_of_lt_succ i.isLt)
  · exact (hf tag 4 0 (by omega)).trans h.inputNorm
  · intro i j
    rw [hf tag 5 _ (by omega)]
    simpa using h.prev i

/-- Componentwise upper counts of one concrete Paige step, including both alternatives of
the guarded next-column normalization. ROM loading and initialization are counted separately. -/
noncomputable def stepCount {P ι : Type} (tag : P) (N : ℕ) : OpCount P ι :=
  Finsupp.single (.bin tag .mul) (N ^ 2 + 4 * N) +
  Finsupp.single (.bin tag .add) (N ^ 2 + 4 * N) +
  Finsupp.single (.un tag .conj) (2 * N) +
  Finsupp.single (.bin tag .div) N + Finsupp.single (.un tag .sqrt) 1 +
  Finsupp.single (.un tag .neg) 2 + Finsupp.single (.lit tag) (2 * N + 2) +
  Finsupp.single (.cmp tag) 1 + Finsupp.single (.copy tag) (2 * N)

end NLAlib.LanczosImplementation
