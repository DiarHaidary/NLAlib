/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosTargets
public import NLAlib.Krylov.Processes.LanczosProgramStep

/-!
# Count algebra for the stored Lanczos target

These identities collect the counts obtained from actual ROM loading, initialization and
Paige-step execution into the approved `lanczosCount` formula.

## Main results

* `lanczosCount_succ`: one more iteration adds the approved componentwise step budget.
* `add_nsmul_eq_lanczosCount`: ROM, initialization and all step counts give the full budget.
-/

@[expose] public section

namespace NLAlib

open Computation LanczosImplementation

/-- The actual initializer's componentwise upper budget: literal scalar/previous-vector setup,
input norm, then guarded copy/division or zero fill. Matrix ROM loading is counted separately. -/
noncomputable def LanczosImplementation.initializationCount {P ι : Type}
    (tag : P) (N : ℕ) : OpCount P ι :=
  (N + 2) • Finsupp.single (.lit tag) 1 +
    (N • (Finsupp.single (.un tag .conj) 1 + Finsupp.single (.bin tag .mul) 1 +
      Finsupp.single (.bin tag .add) 1) + Finsupp.single (.lit tag) 1 +
        Finsupp.single (.un tag .sqrt) 1) +
    (Finsupp.single (.cmp tag) 1 + N •
      (Finsupp.single (.lit tag) 1 + Finsupp.single (.copy tag) 1 +
        Finsupp.single (.bin tag .div) 1))

/-- The approved collected budget adds one fixed Paige-step increment per iteration. -/
theorem lanczosCount_succ {P ι : Type} (tag : P) (N q : ℕ) :
    lanczosCount (ι := ι) tag N (q + 1) = lanczosCount tag N q + stepCount tag N := by
  classical
  unfold lanczosCount stepCount
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Finsupp.single_add]
  abel

/-- At zero iterations the budget is exactly ROM loading, the scalar and previous-vector
literal prefix, the actual input norm, and guarded first-column normalization. -/
theorem lanczosCount_zero {P ι : Type} (tag : P) (N : ℕ) :
    lanczosCount (ι := ι) tag N 0 =
      Finsupp.single (.rom tag) (N * N) + initializationCount tag N := by
  classical
  simp only [lanczosCount, initializationCount, Nat.zero_mul, Nat.mul_zero, Nat.zero_add,
    Finsupp.single_zero, add_zero, nsmul_add,
    Finsupp.smul_single, smul_eq_mul, mul_one, Nat.pow_two,
    show 2 * N + 3 = N + N + (2 + 1) by omega, Finsupp.single_add]
  abel

/-- The approved budget is exactly the compositional upper bound from ROM loading,
initialization in its actual order, and the proved inline iteration loop. -/
theorem add_nsmul_eq_lanczosCount {P ι : Type} (tag : P) (N q : ℕ) :
    Finsupp.single (.rom tag) (N * N) + initializationCount tag N +
        q • stepCount (ι := ι) tag N =
      lanczosCount tag N q := by
  induction q with
  | zero => simpa only [zero_nsmul, add_zero] using (lanczosCount_zero tag N).symm
  | succ q ih => rw [succ_nsmul, ← add_assoc, ih, lanczosCount_succ]

end NLAlib
