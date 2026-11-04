/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGRecurrence
public import NLAlib.Krylov.LinearSystems.CGProgramTree

/-!
# CG as a program: the approved target

The exact stored-entry target approved by the maintainer on 2026-11-04. It fixes the
registered tree, declared inputs, all promised output cells, guarded control flow and the
componentwise count and ROM-inclusive memory bounds. Its statement has no outer mathematical
input restriction or prover-chosen postcondition. The proof is in `CGProgram.lean`.
Design: `docs/design/Krylov-Implementation-Integration.md`.

## Main definitions

* `NLAlib.cgCount`: the approved componentwise upper count formula.
* `NLAlib.StoredEntriesConjugateGradient`: the exact target of the registered implementation.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation

/-- Componentwise operation upper bounds for the canonical program, including initialization,
all requested loop guards, and the maximal number of active steps. Early termination and
nonpositive-curvature rejection can lower individual counts. No square root, oracle call,
conversion or random draw is charged. -/
noncomputable def cgCount {P ι : Type} (tag : P) (N q : ℕ) : OpCount P ι :=
  Finsupp.single (.rom tag) (N ^ 2) +
  Finsupp.single (.bin tag .mul) (N + q * (N ^ 2 + 5 * N)) +
  Finsupp.single (.bin tag .add) (N + q * (N ^ 2 + 5 * N)) +
  Finsupp.single (.un tag .conj) (N + 2 * q * N) +
  Finsupp.single (.bin tag .div) (2 * q) +
  Finsupp.single (.un tag .neg) (q + 1) +
  Finsupp.single (.lit tag) (N + 3 + q * (N + 2)) +
  Finsupp.single (.cmp tag) (1 + 3 * q) +
  Finsupp.single (.copy tag) (2 * N + 2 * q + 2)

/-- The approved exact target of the registered program.
Every real ROM matrix and right-hand
side gives a successful guarded run with one of three statuses. For an SPD ROM matrix, the
three output vectors equal the exact CG state after the requested budget, padded after zero
termination. Counts are componentwise upper bounds and cell memory includes the read-only
matrix, loaded matrix, inputs, outputs and scratch. The statement and its compiled tree are
registered in `docs/targets.toml`. -/
def StoredEntriesConjugateGradient : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (tag : P),
    StoredEntries (𝕜 := ℝ) tag (cgProg.compiled (ι := ι) tag)
      (fun _ _ => True) (fun N _ => Fin N → ℝ)
      (fun N _ b => ![(Array.ofFn b).map some, Array.replicate N none,
        Array.replicate N none, Array.replicate N none, Array.replicate 1 none])
      (fun N _ => N ^ 2) (fun N q => cgCount tag N (q 0))
      (fun N _ p => if p = tag then 2 * N ^ 2 + 5 * N + 11 else 0)
      (fun N q b vals _ st =>
        let A : Matrix (Fin N) (Fin N) ℝ := fun i j => vals (i + N * j)
        ∃ status : ℝ, st.store.read tag 4 0 = some status ∧
          (status = 0 ∨ status = 1 ∨ status = -1) ∧
          Holds st.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
          (A.PosDef →
            Holds st.store tag 1 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).x i) ∧
            Holds st.store tag 2 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).r i) ∧
            Holds st.store tag 3 0 (fun i (_ : Fin 1) => (cgState A b 0 (q 0)).p i) ∧
            (status = 1 ↔ (cgState A b 0 (q 0)).r = 0) ∧ status ≠ -1))

end NLAlib
