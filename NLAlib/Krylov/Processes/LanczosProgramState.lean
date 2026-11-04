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

/-- The exact stored state after initialization and the first `j` concrete Lanczos steps.
The nine buffers are the six declared buffers followed by loaded matrix, work vector and
two scalar scratch cells. Only the negative scratch cell and work vector are unconstrained.
This is an induction invariant proved from execution, not an extra target premise. -/
structure State (tag : P) (N q j : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (st : St P ℝ (OpCount P ι)) : Prop where
  /-- Exact shape of the declared and scoped workspace buffers. -/
  shape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
    (tag, 1), (tag, N), (tag, N * N), (tag, N), (tag, 2)]
  /-- The declared input is retained. -/
  input : ∀ i : Fin N, st.store.read tag 0 i = some (b i)
  /-- The ROM matrix has been loaded column-major. -/
  matrix : Holds st.store tag 6 0 A
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
