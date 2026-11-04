/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosRecurrence
public import NLAlib.Krylov.Processes.LanczosProgramTree

/-!
# Lanczos as a program: the approved target

The exact stored-entry target approved by the maintainer on 2026-11-04. It fixes the
registered tree, declared inputs, all promised output cells, guarded control flow and the
componentwise count and ROM-inclusive memory bounds. Its statement has no outer mathematical
input restriction or prover-chosen postcondition. The proof is in `LanczosProgram.lean`.
Design: `docs/design/Krylov-Implementation-Integration.md`.

## Main definitions

* `NLAlib.lanczosCount`: the approved componentwise upper count formula.
* `NLAlib.StoredEntriesLanczos`: the exact target of the registered implementation.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation

/-- Componentwise upper operation counts for the concrete implementation. Early zero branches
replace copying and division by literal-zero writes. Each component is bounded separately,
so the bound includes both alternatives without asserting that both execute. -/
noncomputable def lanczosCount {P ι : Type} (tag : P) (N q : ℕ) : OpCount P ι :=
  Finsupp.single (.rom tag) (N ^ 2) +
  Finsupp.single (.bin tag .mul) (N + q * (N ^ 2 + 4 * N)) +
  Finsupp.single (.bin tag .add) (N + q * (N ^ 2 + 4 * N)) +
  Finsupp.single (.un tag .conj) (N + 2 * q * N) +
  Finsupp.single (.bin tag .div) (N * (q + 1)) +
  Finsupp.single (.un tag .sqrt) (q + 1) +
  Finsupp.single (.un tag .neg) (2 * q) +
  Finsupp.single (.lit tag) (2 * N + 3 + q * (2 * N + 2)) +
  Finsupp.single (.cmp tag) (q + 1) +
  Finsupp.single (.copy tag) (N + 2 * q * N)

/-- The approved exact target of the registered program:
for every real ROM matrix and input, the concrete
compiled program succeeds within the stated counts and memory, and its actual output buffers
hold every basis column and recurrence coefficient, the input norm, and the final previous
vector of `lanczosState`. No symmetry, nonzero-input or nonbreakdown premise is imposed. -/
def StoredEntriesLanczos : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (tag : P),
    StoredEntries (𝕜 := ℝ) tag (lanczosProg.compiled (ι := ι) tag)
      (fun _ _ => True) (fun N _ => Fin N → ℝ)
      (fun N q b => ![(Array.ofFn b).map some, Array.replicate (N * (q 0 + 1)) none,
        Array.replicate (q 0) none, Array.replicate (q 0 + 1) none,
        Array.replicate 1 none, Array.replicate N none])
      (fun N _ => N ^ 2) (fun N q => lanczosCount tag N (q 0))
      (fun N q p => if p = tag then 2 * N ^ 2 + N * (q 0 + 4) + 2 * q 0 + 5 else 0)
      (fun N q b vals _ st =>
        let A : Matrix (Fin N) (Fin N) ℝ := fun i j => vals (i + N * j)
        Holds st.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
        Holds st.store tag 1 0 (lanczosMatrix A b (q 0 + 1)) ∧
        Holds st.store tag 2 0
          (fun (j : Fin (q 0)) (_ : Fin 1) => lanczosAlpha A (lanczosState A b j)) ∧
        Holds st.store tag 3 0
          (fun (j : Fin (q 0 + 1)) (_ : Fin 1) => (lanczosState A b j).beta) ∧
        st.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
        Holds st.store tag 5 0 (fun i (_ : Fin 1) => (lanczosState A b (q 0)).prev i))

end NLAlib
