/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGTargets

/-!
# Count algebra for the approved CG target

Per-step increments of the approved count formula. These are bookkeeping identities,
not new program definitions or independently chosen cost guarantees.

## Main results

* `NLAlib.cgCount_succ`: one more permitted active step adds the fixed per-step budget.
-/

@[expose] public section

namespace NLAlib

open Computation

/-- The per-step budget of the approved stored CG implementation, including both guards,
the successful body and a possible terminal-status copy. Early stopping lowers counts. -/
noncomputable def CGImplementation.stepCount {P ι : Type} (tag : P) (N : ℕ) : OpCount P ι :=
  Finsupp.single (.bin tag .mul) (N ^ 2 + 5 * N) +
  Finsupp.single (.bin tag .add) (N ^ 2 + 5 * N) +
  Finsupp.single (.un tag .conj) (2 * N) +
  Finsupp.single (.bin tag .div) 2 + Finsupp.single (.un tag .neg) 1 +
  Finsupp.single (.lit tag) (N + 2) + Finsupp.single (.cmp tag) 3 +
  Finsupp.single (.copy tag) 2

/-- The approved CG budget consists of its initialization and one increment per permitted
step. This identity holds for zero dimension and zero step count too. -/
theorem cgCount_succ {P ι : Type} (tag : P) (N q : ℕ) :
    cgCount (ι := ι) tag N (q + 1) = cgCount tag N q + CGImplementation.stepCount tag N := by
  classical
  unfold cgCount CGImplementation.stepCount
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Finsupp.single_add]
  abel

/-- The approved CG count splits into initialization and the permitted loop increments. -/
theorem cgCount_decompose {P ι : Type} (tag : P) (N q : ℕ) :
    cgCount (ι := ι) tag N 0 + q • CGImplementation.stepCount tag N = cgCount tag N q := by
  induction q with
  | zero => simp only [zero_nsmul, add_zero]
  | succ q ih => rw [succ_nsmul, ← add_assoc, ih, cgCount_succ]

end NLAlib
