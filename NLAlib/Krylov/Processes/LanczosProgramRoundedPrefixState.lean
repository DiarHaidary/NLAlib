/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramRoundedState
public import NLAlib.Krylov.Processes.LanczosProgramRounding
public import NLAlib.Krylov.FinitePrecision.LanczosRun

/-!
# The active prefix and the stored zero continuation

A positive-length existing LanczosRun describes the steps through the first zero next
coefficient. The decoded context describes every requested stored column, including actual
zero continuation. This bookkeeping proposition does not assume future execution.

## Main definitions

* `NLAlib.LanczosImplementation.RoundedPrefix`: active run and full decoded output prefix.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

/-- A decoded prefix is either the initialized zero-step or zero-input trajectory, or an
existing positive-length run with zero functions beyond its active range. A terminal next
vector is zero as a consequence of the actual guarded normalization. Every written column
is retained in the context, while the run length stops at the first zero coefficient. -/
def RoundedPrefix {P K : Type} [DecidableEq P] (tag : P) (dec : P → K → ℝ)
    (N q j : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b v1 : Fin N → ℝ)
    (ε s : ℝ) (store : Computation.Store P K) : Prop :=
  ((j = 0 ∨ b = 0) ∧
    StoreContext tag dec N q j A b (Function.update (0 : ℕ → Fin N → ℝ) 1 v1)
      (fun _ => 0) (fun _ => 0) s store) ∨
  ∃ (m : ℕ) (R : LanczosRun N m), m ≤ j ∧ R.H = A ∧ R.ε = ε ∧ R.v 1 = v1 ∧
    StoreContext tag dec N q j A b R.v R.α R.β s store ∧
    (∀ i, m + 1 < i → R.v i = 0) ∧
    (∀ i, m < i → R.α i = 0 ∧ R.β i = 0) ∧
    (R.β m = 0 → R.v (m + 1) = 0) ∧ (m < j → R.β m = 0)

end NLAlib.LanczosImplementation
