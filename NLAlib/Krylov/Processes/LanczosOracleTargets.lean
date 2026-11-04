/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosOracleProgramTree
public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# Approved matrix-free Lanczos target

The approved target fixes the actual oracle tree, retained input and every output buffer,
componentwise counts, and peak cells. It includes zero dimensions, zero inputs, zero requested
steps and terminal zero continuation, for every real matrix without a symmetry assumption.
Oracle backend storage and arithmetic remain outside this access model.
Design: `docs/design/Lanczos-Matrix-Free-Program.md`.

## Main definitions

* `NLAlib.lanczosOracleCount`: approved componentwise count budget.
* `NLAlib.MatrixFreeLanczos`: the approved exact matrix-free target.

## Main results

The target is realized in `LanczosOracleProgram.lean`.
-/

@[expose] public section

namespace NLAlib

open Computation

/-- Proposed operation counts for q oracle Paige steps, including both alternatives of
componentwise guarded normalization. Each call charges one load and one column matvec. -/
noncomputable def lanczosOracleCount {P ι : Type} (tag : P) (o : ι) (N q : ℕ) : OpCount P ι :=
  Finsupp.single (.load tag o) q + Finsupp.single (.matvec tag o) q +
  Finsupp.single (.bin tag .mul) (N + 4 * q * N) +
  Finsupp.single (.bin tag .add) (N + 4 * q * N) +
  Finsupp.single (.un tag .conj) (N + 2 * q * N) +
  Finsupp.single (.bin tag .div) (N * (q + 1)) +
  Finsupp.single (.un tag .sqrt) (q + 1) +
  Finsupp.single (.un tag .neg) (2 * q) +
  Finsupp.single (.lit tag) (2 * N + 3 + q * (N + 2)) +
  Finsupp.single (.cmp tag) (q + 1) +
  Finsupp.single (.copy tag) (N + 2 * q * N)

/-- Proposed matrix-free target for all real matrices and inputs: the actual compiled tree
retains the input and computes every Lanczos basis column, alpha/beta coefficient, the input
norm and final previous vector within the displayed counts and linear workspace. Zero input,
zero dimension, zero requested steps and zero continuation are included. Oracle backend
storage and arithmetic are outside the model; loads and one-column matvecs are counted. -/
def MatrixFreeLanczos : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (tag : P) (o : ι),
    MatrixFree (𝕜 := ℝ) tag (lanczosOracleProg.compiled tag o)
      (fun _ _ => True) (fun N _ => Fin N → ℝ)
      (fun N q b => ![(Array.ofFn b).map some, Array.replicate (N * (q 0 + 1)) none,
        Array.replicate (q 0) none, Array.replicate (q 0 + 1) none,
        Array.replicate 1 none, Array.replicate N none])
      (fun N q => lanczosOracleCount tag o N (q 0))
      (fun N q p => if p = tag then N * (q 0 + 4) + 2 * q 0 + 5 else 0)
      (fun _ q b A _ st =>
        Holds st.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
        Holds st.store tag 1 0 (lanczosMatrix A b (q 0 + 1)) ∧
        Holds st.store tag 2 0
          (fun (j : Fin (q 0)) (_ : Fin 1) => lanczosAlpha A (lanczosState A b j)) ∧
        Holds st.store tag 3 0
          (fun (j : Fin (q 0 + 1)) (_ : Fin 1) => (lanczosState A b j).beta) ∧
        st.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
        Holds st.store tag 5 0 (fun i (_ : Fin 1) => (lanczosState A b (q 0)).prev i))

end NLAlib
